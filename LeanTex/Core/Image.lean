import LeanTex.Core.Diag
import LeanTex.Core.Dim
import LeanTex.Core.Flate
import LeanTex.Core.PdfRead

namespace LeanTex.Core.Image

open LeanTex.Core.Dim

/-! # External images

Two pure halves. `probe` reads a file's header into a `Source` — every fact
the embedding decision can read cheaply: dimensions, density, sample
layout, the palette, a colour key, an embedded profile, an orientation tag,
and the compressed payload as a slice of the input, never a decoded
surface. `plan` is a pure match from a `Source` and the `PlanParams` a
declaration projects onto images to the `Plan` the PDF writer embeds: the
colour space, filter, and alpha as three sums, the stream bytes, and a
`losses` ledger naming every `Source` fact the plan does not carry
(`plan_losses_accounts` — the planner never drops a fact wordlessly).
Reading the file is the driver's effect; everything here is total over a
`ByteArray` — a truncated or foreign file yields an error value, never a
crash and never a wrong number. Opaque and indexed PNGs pass their IDAT
through untouched (`plan_passthrough_exact`); a PNG with an alpha channel
inflates once and deinterleaves its filtered rows into a colour stream and
a soft-mask stream — never its pixels — since a PDF image holds exactly
its colour space's samples and carries opacity as a separate `/SMask`
image. A `tRNS` chunk on the pass-through types becomes the exact
colour-key `/Mask`, or a refusal where no single range can carry it.
Interlaced and 16-bit-alpha PNGs, CMYK JPEGs, and the formats no PDF
filter decodes (WebP, AVIF, JPEG XL) are refused with a reason that names
them. `decode` is `plan PlanParams.default ∘ probe`. -/

/-- Both specs can leave the physical size undeclared — PNG's pHYs is
optional and "the physical size of each pixel is unknown" without it
(ISO/IEC 15948 §11.3.5.3), JFIF density unit 0 declares aspect ratio only
(ISO/IEC 10918-5 §5). The engine then adopts 72 pixels per inch, pdfTeX's
`\pdfimageresolution` default, so one pixel is one point. -/
def defaultDpi : Nat := 72

/-- What the signature says a file is. The last four are recognised so the
refusal can name them — no PDF filter decodes WebP, AVIF, or JPEG XL (ISO
32000-2 Table 6), and a JPEG 2000 codestream passes through only under a
permitting declaration, a later slice's arm. -/
inductive Format where
  | png
  | jpeg
  /-- A selected PDF page, embedded as a form XObject: vector stays vector. -/
  | pdf
  | webp
  | avif
  | jxl
  /-- JPEG 2000: a JP2 container or a raw J2K codestream. -/
  | jpx
  deriving Repr, BEq, Inhabited

/-- The name a refusal shows the reader: the one constant
`plan_refuses_named` is stated over. -/
def Format.name : Format → String
  | .png => "PNG"
  | .jpeg => "JPEG"
  | .pdf => "PDF"
  | .webp => "WebP"
  | .avif => "AVIF"
  | .jxl => "JPEG XL"
  | .jpx => "JPEG 2000"

/-- The colour interpretation a PNG declares: what `colorKeyRanges` judges
a `tRNS` chunk against. -/
inductive Space where
  | gray
  | rgb
  /-- PNG colour type 3: samples index the PLTE palette. -/
  | indexed
  deriving Repr, BEq, Inhabited

/-- Samples per pixel, for `/DecodeParms /Colors`. -/
def Space.components : Space → Nat
  | .gray => 1
  | .rgb => 3
  | .indexed => 1

/-- The `/ColorSpace` a plan declares (ISO 32000-2 §8.6). `iccBased` is
produced only under `IccPolicy.carry` and carries the profile as zlib
bytes for a `/FlateDecode` stream; its alternate is the device space of
`n` components. The writer's `/ICCBased` emission is a later slice's —
until then the arm writes the alternate, and the default policy never
plans it (`plan_losses_accounts`). -/
inductive ColorSpaceDecl where
  | gray
  | rgb
  /-- `[/Indexed /DeviceRGB hival <palette>]`: the PLTE payload, RGB triples. -/
  | indexed (palette : ByteArray)
  | iccBased (n : Nat) (profile : ByteArray)
  deriving BEq, Inhabited

/-- Samples per pixel, for `/DecodeParms /Colors`. -/
def ColorSpaceDecl.components : ColorSpaceDecl → Nat
  | .gray => 1
  | .rgb => 3
  | .indexed _ => 1
  | .iccBased n _ => n

/-- The `/Filter` a plan declares. `flatePredictor` is a PNG-predicted zlib
stream — a pass-through IDAT, or the colour plane deinterleaved from an
alpha PNG's filtered rows and deflated again — legal as `/FlateDecode`
with Predictor 15 declared (ISO 32000-2 §7.4.4.4); `dct` is a whole JPEG
file. -/
inductive FilterDecl where
  | flatePredictor
  | dct
  deriving Repr, BEq, Inhabited

/-- How a plan carries transparency, or that it has none. -/
inductive Alpha where
  | opaque
  /-- Colour-key masking (ISO 32000-2 §8.9.6.4): the `/Mask` ranges, two
  per component in sample units at the plan's bit depth, a pixel inside
  every range not painted — a PNG `tRNS` chunk mapped exactly
  (`colorKeyRanges`). -/
  | colorKey (ranges : Array Nat)
  /-- An alpha channel as its own zlib-compressed gray plane under the
  source rows' own filters: the PDF soft mask, Predictor 15 declared, at
  `bpc` bits per sample. -/
  | soft (plane : ByteArray) (bpc : Nat)
  deriving BEq, Inhabited

/-- A `Source` fact the plan does not carry: the ledger the driver turns
into diagnostics, one per entry. -/
inductive PlanLoss where
  /-- An embedded colour profile (PNG `iCCP`, JPEG `APP2`) dropped; the
  page reads the samples as device colour. -/
  | iccDropped
  /-- An Exif orientation other than 1 dropped; the page shows the stored
  orientation. -/
  | orientationDropped
  deriving Repr, DecidableEq, Inhabited

/-- What the PDF writer embeds and placement reads. `data` is the stream
the writer embeds as-is: a PNG's concatenated IDAT zlib stream, a JPEG's
whole file, or the recoded colour plane of an alpha PNG. -/
structure Plan where
  pxW : Nat
  pxH : Nat
  dpiX : Nat := defaultDpi
  dpiY : Nat := defaultDpi
  bitDepth : Nat := 8
  color : ColorSpaceDecl := .rgb
  filter : FilterDecl := .flatePredictor
  data : ByteArray := ByteArray.empty
  alpha : Alpha := .opaque
  /-- Did the plan do real work — inflate, split, recompress? The driver's
  cache gate, declared by the planner (`recodes_iff`), never peeked from
  the bytes. -/
  recoded : Bool := false
  losses : Array PlanLoss := #[]
  /-- The Exif orientation the source declared, 1–8; carried for the
  rotation arm a later slice adds, dropped meanwhile (`.orientationDropped`). -/
  orientation : Nat := 1
  /-- A PDF page read as a form XObject: the box, the content, and the
  copied resource graph. The `wf` witness rides with it —
  `PdfRead.resources_closed` — so the writer never meets a dangling
  reference. -/
  form : Option { f : PdfRead.Form // f.wf } := none
  deriving Inhabited

/-- Intrinsic physical width: pixels over density, in sp — and for a PDF
page, its box, exact to the sp (the `form_bbox_exact` half of the story:
the intrinsic size *is* the page box). -/
def Plan.width (i : Plan) : Sp :=
  match i.form with
  | some f => f.val.w
  | none => (i.pxW : Int) * 72 * spPerPt / max i.dpiX 1

def Plan.height (i : Plan) : Sp :=
  match i.form with
  | some f => f.val.h
  | none => (i.pxH : Int) * 72 * spPerPt / max i.dpiY 1

/-- At the default density one pixel is one point: the convention is not
just a comment, it is what `Plan.width` computes. -/
theorem width_at_default_dpi (px : Nat) :
    Plan.width { pxW := px, pxH := px } = Dim.pt px := by
  show ((px : Int) * 72 * 65536) / (((72 : Nat) : Int)) = (px : Int) * 65536
  omega

-- Byte readers, all bounds-checked: the parsers below must be total over
-- arbitrary input.

private def u8? (b : ByteArray) (i : Nat) : Option Nat :=
  (b[i]?).map (·.toNat)

private def u16be? (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u8? b i) * 256 + (← u8? b (i + 1))

private def u32be? (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u16be? b i) * 65536 + (← u16be? b (i + 2))

private def u16le? (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u8? b i) + (← u8? b (i + 1)) * 256

private def u24le? (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u16le? b i) + (← u8? b (i + 2)) * 65536

private def u32le? (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u16le? b i) + (← u16le? b (i + 2)) * 65536

/-- A 16-bit read in the byte order a TIFF header declares (`le`). -/
private def u16? (le : Bool) (b : ByteArray) (i : Nat) : Option Nat :=
  if le then u16le? b i else u16be? b i

private def u32? (le : Bool) (b : ByteArray) (i : Nat) : Option Nat :=
  if le then u32le? b i else u32be? b i

private def sliceEq (b : ByteArray) (i : Nat) (pat : List Nat) : Bool :=
  pat.zipIdx.all fun (v, k) => u8? b (i + k) == some v

/-- Pixels-per-metre to pixels-per-inch, rounded: 1 in = 25.4 mm exactly. -/
private def ppmToDpi (ppm : Nat) : Nat := (ppm * 254 + 5000) / 10000

/-! ## PNG

Signature, then chunks of `length type data crc`. IHDR carries the
dimensions and sample layout, pHYs the density, PLTE the palette, IDAT the
zlib stream (possibly split across chunks). Greyscale (0), truecolour (2),
and indexed (3) samples pass through to a PDF `/FlateDecode` image XObject
with the PNG predictor declared — their scanlines are pure sample runs after
the per-row filter byte, which is exactly what the predictor describes. An
alpha channel (types 4 and 6, 8-bit) interleaves samples a PDF colour space
cannot hold: ISO 32000-2 §8.9.5 gives an image exactly `/Colors` samples per
pixel, and per-pixel opacity is a separate gray image named by `/SMask`
(§11.6.5.3). So those inflate and deinterleave — the filtered residuals as
they stand, each row's filter byte kept, never the pixels — into two
predicted planes that deflate again (`splitPredictedAlpha`). Adam7
interlacing and 16-bit alpha are refused with the reason. -/

private def pngSig : List Nat := [137, 80, 78, 71, 13, 10, 26, 10]

/-! ### Channel projection commutes with the row filters

The five row filters predict each byte from the byte `bpp` to its left, the
byte above, and the byte above-left (ISO/IEC 15948 §9.2; a PDF reader's
Predictor 15 undoes the same five, ISO 32000-2 §7.4.4.4). Keeping `k` of a
`chs`-sample pixel's samples sends byte `j` of a projected run to byte
`j / k * chs + sel (j % k)` of the source run, and that map carries
neighbours to neighbours: one projected pixel back is one source pixel back.
So the filtered residuals deinterleave as they stand, and the two planes
unfilter to the two projections of the source pixels — `splitPredictedAlpha_exact`.
Stated over the artifact's encoding, not the IR: what a PDF reader
reconstructs from the two streams the writer emits is a fact of the
artifact, with no IR value behind it. -/

/-- Source byte of byte `j` of a projected run of pixels. -/
@[inline] def embPlane (chs k : Nat) (sel : Nat → Nat) (j : Nat) : Nat :=
  j / k * chs + sel (j % k)

/-- Keep `k` samples of every `chs`-sample pixel, chosen by `sel`. -/
@[specialize] def project (px : ByteArray) (chs k : Nat) (sel : Nat → Nat) : ByteArray :=
  Flate.build (px.size / chs * k) fun out => px[embPlane chs k sel out.size]?.getD 0

/-- Split decoded pixels into the colour plane and the alpha plane:
`chs` is 4 (RGBA) or 2 (grey + alpha), the alpha always last. The semantic
route — what the fast path is proved to equal, and the tests' oracle; the
engine itself never reconstructs the pixels. -/
def splitAlpha (px : ByteArray) (chs : Nat) : ByteArray × ByteArray :=
  (project px chs (chs - 1) id, project px chs 1 fun _ => chs - 1)

/-- Source byte of byte `j` of a projected *predicted* stream: rows of
`1 + W * k` bytes, each opening with the filter byte its source row (of
`1 + W * chs` bytes) opens with. -/
@[inline] def embPred (W chs k : Nat) (sel : Nat → Nat) (j : Nat) : Nat :=
  let r := j / (1 + W * k)
  let t := j % (1 + W * k)
  if t = 0 then r * (1 + W * chs) else r * (1 + W * chs) + 1 + embPlane chs k sel (t - 1)

/-- Project a predicted stream of `pxH` rows, `W` pixels of `chs` samples
each, onto `k` samples per pixel — one read and one write per output byte. -/
@[specialize] def projectPred (raw : ByteArray) (pxH W chs k : Nat) (sel : Nat → Nat) :
    ByteArray :=
  Flate.build (pxH * (1 + W * k)) fun out => raw[embPred W chs k sel out.size]?.getD 0

/-- The inflated IDAT of an alpha PNG (`chs` 4 or 2) as two predicted
planes, colour and alpha, each row's filter byte preserved — what the PDF
writer deflates and declares Predictor 15 on. -/
def splitPredictedAlpha (raw : ByteArray) (pxH W chs : Nat) : ByteArray × ByteArray :=
  (projectPred raw pxH W chs (chs - 1) id, projectPred raw pxH W chs 1 fun _ => chs - 1)

theorem getElem?_project (px : ByteArray) (chs k : Nat) (sel : Nat → Nat) (j : Nat)
    (hj : j < px.size / chs * k) :
    (project px chs k sel)[j]? = some (px[embPlane chs k sel j]?.getD 0) := by
  rw [project, Flate.getElem?_build _ _ j hj, Flate.size_build]

theorem projectPred_filter (raw : ByteArray) (pxH W chs k : Nat) (sel : Nat → Nat)
    (r : Nat) (hr : r < pxH) :
    (projectPred raw pxH W chs k sel)[r * (1 + W * k)]? =
      some (raw[r * (1 + W * chs)]?.getD 0) := by
  have hL : 0 < 1 + W * k := by omega
  rw [projectPred, Flate.getElem?_build _ _ _ (Nat.mul_lt_mul_of_pos_right hr hL),
    Flate.size_build, embPred]
  simp [Nat.mul_div_cancel _ hL, Nat.mul_mod_left]

theorem projectPred_sample (raw : ByteArray) (pxH W chs k : Nat) (sel : Nat → Nat)
    (r i : Nat) (hr : r < pxH) (hi : i < W * k) :
    (projectPred raw pxH W chs k sel)[r * (1 + W * k) + 1 + i]? =
      some (raw[r * (1 + W * chs) + 1 + embPlane chs k sel i]?.getD 0) := by
  have hL : 0 < 1 + W * k := by omega
  have hlt : r * (1 + W * k) + 1 + i < pxH * (1 + W * k) := by
    have : (r + 1) * (1 + W * k) ≤ pxH * (1 + W * k) := Nat.mul_le_mul_right _ hr
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  rw [projectPred, Flate.getElem?_build _ _ _ hlt, Flate.size_build, embPred]
  have hq : (r * (1 + W * k) + 1 + i) / (1 + W * k) = r := by
    rw [Nat.add_assoc, Nat.mul_comm r, Nat.mul_add_div hL, Nat.div_eq_of_lt (by omega)]
    rfl
  have hm : (r * (1 + W * k) + 1 + i) % (1 + W * k) = 1 + i := by
    rw [Nat.add_assoc, Nat.mul_comm r, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  simp [hq, hm]

/-- Projection is an embedding of pixel runs: byte `j` of the projection is
`j / (W * k)` rows down and `embPlane (j % (W * k))` into the source row —
and that offset stays inside the row. -/
theorem embPlane_row (chs k W : Nat) (sel : Nat → Nat) (hk : 0 < k)
    (hsel : ∀ c < k, sel c < chs) (hW : 0 < W) (j : Nat) :
    embPlane chs k sel j = j / (W * k) * (W * chs) + embPlane chs k sel (j % (W * k)) ∧
    embPlane chs k sel (j % (W * k)) < W * chs := by
  have hWk : 0 < W * k := Nat.mul_pos hW hk
  have hi := Nat.mod_lt j hWk
  have hdiv : j % (W * k) / k < W := (Nat.div_lt_iff_lt_mul hk).mpr hi
  have hs := hsel (j % (W * k) % k) (Nat.mod_lt _ hk)
  constructor
  · have hj := Nat.div_add_mod j (W * k)
    conv => lhs; rw [← hj]
    unfold embPlane
    rw [show W * k * (j / (W * k)) = k * (W * (j / (W * k))) by ac_rfl,
      Nat.mul_add_div hk, Nat.mul_add_mod, Nat.add_mul]
    ac_rfl
  · unfold embPlane
    have : (j % (W * k) / k + 1) * chs ≤ W * chs := Nat.mul_le_mul_right _ hdiv
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- One projected pixel back is one source pixel back: subtracting `m`
projected pixels from `j` subtracts `m` source pixels from its source byte. -/
theorem embPlane_sub (chs k : Nat) (sel : Nat → Nat) (hk : 0 < k) (j m : Nat)
    (h : k * m ≤ j) :
    embPlane chs k sel (j - k * m) = embPlane chs k sel j - m * chs ∧
    m * chs ≤ embPlane chs k sel j := by
  have hq : m ≤ j / k := (Nat.le_div_iff_mul_le hk).mpr (by rw [Nat.mul_comm]; exact h)
  have hmc : m * chs ≤ j / k * chs := Nat.mul_le_mul_right _ hq
  unfold embPlane
  rw [Nat.sub_mul_div_of_le _ _ _ h, Nat.sub_mul_mod h, Nat.sub_mul]
  omega

/-- A projected byte has a left neighbour exactly when its source byte does. -/
theorem embPlane_ge_iff (chs k : Nat) (sel : Nat → Nat) (hk : 0 < k)
    (hsel : ∀ c < k, sel c < chs) (j : Nat) :
    chs ≤ embPlane chs k sel j ↔ k ≤ j := by
  constructor
  · intro h
    rcases Nat.lt_or_ge j k with hlt | hge
    · unfold embPlane at h
      rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, Nat.zero_mul, Nat.zero_add] at h
      exact absurd (hsel j hlt) (Nat.not_lt.mpr h)
    · exact hge
  · intro h
    have := (embPlane_sub chs k sel hk j 1 (by omega)).2
    rwa [Nat.one_mul] at this

/-- The heart of `splitPredictedAlpha_exact`: byte `j` of the unfiltered
projected plane is byte `embPlane j` of the unfiltered source plane, by
strong induction along the plane — each byte's three neighbours are earlier
bytes whose sources are the source byte's three neighbours (`embPlane_sub`),
and the residual and filter byte are the same bytes (`projectPred_sample`,
`projectPred_filter`). -/
theorem unfilterByte_project (raw : ByteArray) (pxH W chs k : Nat) (sel : Nat → Nat)
    (hk : 0 < k) (hsel : ∀ c < k, sel c < chs) (hW : 0 < W) :
    ∀ j, j < pxH * (W * k) →
      Flate.unfilterByte (projectPred raw pxH W chs k sel) (W * k) k
          (Flate.build j (Flate.unfilterByte (projectPred raw pxH W chs k sel) (W * k) k)) =
        Flate.unfilterByte raw (W * chs) chs
          (Flate.build (embPlane chs k sel j) (Flate.unfilterByte raw (W * chs) chs)) := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    have hWk : 0 < W * k := Nat.mul_pos hW hk
    have hchs : 0 < chs := Nat.lt_of_le_of_lt (Nat.zero_le _) (hsel 0 hk)
    have hWc : 0 < W * chs := Nat.mul_pos hW hchs
    obtain ⟨hrow, hsmall⟩ := embPlane_row chs k W sel hk hsel hW j
    have hr : j / (W * k) < pxH := (Nat.div_lt_iff_lt_mul hWk).mpr hj
    have hi := Nat.mod_lt j hWk
    -- The source byte's row and column.
    have hJr : embPlane chs k sel j / (W * chs) = j / (W * k) := by
      rw [hrow, Nat.mul_comm (j / (W * k)), Nat.mul_add_div hWc, Nat.div_eq_of_lt hsmall]
      rfl
    have hJi : embPlane chs k sel j % (W * chs) = embPlane chs k sel (j % (W * k)) := by
      rw [hrow, Nat.mul_comm (j / (W * k)), Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsmall]
    -- Neighbours: one pixel left, one row up, both.
    have hleft := embPlane_sub chs k sel hk j 1
    have hup := embPlane_sub chs k sel hk j W
    have hboth := embPlane_sub chs k sel hk j (W + 1)
    have hcond := embPlane_ge_iff chs k sel hk hsel (j % (W * k))
    have hmodle := Nat.mod_le j (W * k)
    -- Each neighbour read, when it happens, is an earlier byte of the same
    -- plane, and the induction hypothesis carries it across.
    have hread : ∀ m, k * m ≤ j → m * chs ≤ embPlane chs k sel j →
        (Flate.build j (Flate.unfilterByte (projectPred raw pxH W chs k sel) (W * k) k))[j - k * m]?
          = (Flate.build (embPlane chs k sel j)
              (Flate.unfilterByte raw (W * chs) chs))[embPlane chs k sel j - m * chs]? := by
      intro m hm hmc
      by_cases hm0 : m = 0
      · subst hm0
        simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_mul]
        rw [getElem?_neg _ _ (by rw [Flate.size_build]; omega),
          getElem?_neg _ _ (by rw [Flate.size_build]; omega)]
      · have hmk : 0 < k * m := Nat.mul_pos hk (Nat.pos_of_ne_zero hm0)
        have hmc0 : 0 < m * chs := Nat.mul_pos (Nat.pos_of_ne_zero hm0) hchs
        rw [Flate.getElem?_build _ _ _ (by omega),
          Flate.getElem?_build _ _ _ (by omega),
          ih (j - k * m) (by omega) (by omega), (embPlane_sub chs k sel hk j m hm).1]
    have h1 : k ≤ j % (W * k) ↔ chs ≤ embPlane chs k sel (j % (W * k)) := hcond.symm
    have h2 : W * k ≤ j ↔ W * chs ≤ embPlane chs k sel j := by
      constructor
      · intro h
        exact (hup (by rw [Nat.mul_comm]; exact h)).2
      · intro h
        rcases Nat.lt_or_ge j (W * k) with hlt | hge
        · rw [Nat.div_eq_of_lt hlt, Nat.zero_mul, Nat.zero_add] at hrow
          omega
        · exact hge
    -- The three neighbour terms, in the shape the unfolded byte reads them.
    have hL : (if k ≤ j % (W * k) then
          ((Flate.build j (Flate.unfilterByte (projectPred raw pxH W chs k sel) (W * k) k))[j - k]?.getD
            0).toNat else 0) =
        (if chs ≤ embPlane chs k sel (j % (W * k)) then
          ((Flate.build (embPlane chs k sel j) (Flate.unfilterByte raw (W * chs) chs))[embPlane chs k sel j
            - chs]?.getD 0).toNat else 0) := by
      by_cases hl : k ≤ j % (W * k)
      · have hkj : k * 1 ≤ j := by rw [Nat.mul_one]; omega
        have := hread 1 hkj (hleft hkj).2
        rw [Nat.mul_one, Nat.one_mul] at this
        rw [ite_eq_left hl, ite_eq_left (h1.mp hl), this]
      · rw [ite_eq_right hl, ite_eq_right (fun h => hl (h1.mpr h))]
    have hU : (if W * k ≤ j then
          ((Flate.build j (Flate.unfilterByte (projectPred raw pxH W chs k sel) (W * k) k))[j - W * k]?.getD
            0).toNat else 0) =
        (if W * chs ≤ embPlane chs k sel j then
          ((Flate.build (embPlane chs k sel j) (Flate.unfilterByte raw (W * chs) chs))[embPlane chs k sel j
            - W * chs]?.getD 0).toNat else 0) := by
      by_cases hu : W * k ≤ j
      · have hkW : k * W ≤ j := by rw [Nat.mul_comm]; exact hu
        have := hread W hkW (hup hkW).2
        rw [Nat.mul_comm k W] at this
        rw [ite_eq_left hu, ite_eq_left (h2.mp hu), this]
      · rw [ite_eq_right hu, ite_eq_right (fun h => hu (h2.mpr h))]
    have hUL : (if W * k ≤ j ∧ k ≤ j % (W * k) then
          ((Flate.build j (Flate.unfilterByte (projectPred raw pxH W chs k sel) (W * k) k))[j - W * k
            - k]?.getD 0).toNat else 0) =
        (if W * chs ≤ embPlane chs k sel j ∧ chs ≤ embPlane chs k sel (j % (W * k)) then
          ((Flate.build (embPlane chs k sel j) (Flate.unfilterByte raw (W * chs) chs))[embPlane chs k sel j
            - W * chs - chs]?.getD 0).toNat else 0) := by
      by_cases hb : W * k ≤ j ∧ k ≤ j % (W * k)
      · have hkW1 : k * (W + 1) ≤ j := by
          have hj' := Nat.div_add_mod j (W * k)
          have hq1 : 1 ≤ j / (W * k) := (Nat.le_div_iff_mul_le hWk).mpr (by omega)
          have : W * k ≤ W * k * (j / (W * k)) := Nat.le_mul_of_pos_right _ hq1
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm k W]
          omega
        have := hread (W + 1) hkW1 (hboth hkW1).2
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm k W, Nat.add_mul, Nat.one_mul, ← Nat.sub_sub,
          ← Nat.sub_sub] at this
        rw [ite_eq_left hb, ite_eq_left ⟨h2.mp hb.1, h1.mp hb.2⟩, this]
      · rw [ite_eq_right hb, ite_eq_right (fun h => hb ⟨h2.mpr h.1, h1.mpr h.2⟩)]
    rw [Flate.unfilterByte, Flate.unfilterByte]
    simp only [Flate.size_build, hJr, hJi, projectPred_filter raw pxH W chs k sel _ hr,
      projectPred_sample raw pxH W chs k sel _ _ hr hi, Option.getD_some]
    rw [hL, hU, hUL]

/-- Deinterleaving the *filtered* residuals is exact: unfiltering the colour
and alpha planes `splitPredictedAlpha` writes yields exactly the colour and
alpha projections (`splitAlpha`) of unfiltering the original — for every
predicted stream the engine's unfilter accepts, at every width and height,
under every mix of the five row filters. The PDF reader's Predictor 15
reconstructs what the pixel route would have shipped, and the engine never
materializes the pixels. Stated over the artifact's encoding, not the IR
(see the section note). -/
theorem splitPredictedAlpha_exact (raw : ByteArray) (pxH W chs : Nat) (h2 : 2 ≤ chs)
    (hW : 0 < W) (px : ByteArray)
    (h : Flate.pngUnfilter raw pxH (W * chs) chs = .ok px) :
    Flate.pngUnfilter (splitPredictedAlpha raw pxH W chs).1 pxH (W * (chs - 1)) (chs - 1) =
        .ok (splitAlpha px chs).1 ∧
      Flate.pngUnfilter (splitPredictedAlpha raw pxH W chs).2 pxH W 1 =
        .ok (splitAlpha px chs).2 := by
  have hchs : 0 < chs := by omega
  -- What the hypothesis says: the source stream is long enough, its filter
  -- bytes are legal, and `px` is its plane.
  unfold Flate.pngUnfilter at h
  split at h
  · exact absurd h (by simp)
  split at h
  · next _ hft =>
    have hpx : px = Flate.unfilterAll raw pxH (W * chs) chs := (Except.ok.inj h).symm
    subst hpx
    -- One projection at a time, both instances of the same fact.
    have core : ∀ k (sel : Nat → Nat), 0 < k → (∀ c < k, sel c < chs) →
        Flate.pngUnfilter (projectPred raw pxH W chs k sel) pxH (W * k) k =
          .ok (project (Flate.unfilterAll raw pxH (W * chs) chs) chs k sel) := by
      intro k sel hk hsel
      unfold Flate.pngUnfilter
      have hsz : (projectPred raw pxH W chs k sel).size = pxH * (1 + W * k) := by
        rw [projectPred, Flate.size_build]
      have hall : ∀ r < pxH, ((projectPred raw pxH W chs k sel)[r * (1 + W * k)]?.getD 0).toNat
          ≤ 4 := by
        intro r hr
        rw [projectPred_filter raw pxH W chs k sel r hr, Option.getD_some]
        exact hft r hr
      have hdiv : pxH * (W * chs) / chs = pxH * W := by
        rw [← Nat.mul_assoc]; exact Nat.mul_div_cancel _ hchs
      simp only [hsz, Nat.lt_irrefl, ↓reduceIte]
      rw [ite_eq_left hall]
      congr 1
      apply Flate.ext_of_getElem?
      · rw [Flate.unfilterAll, Flate.size_build, project, Flate.size_build, Flate.unfilterAll,
          Flate.size_build, hdiv, Nat.mul_assoc]
      · intro j hj
        rw [Flate.unfilterAll, Flate.size_build] at hj
        rw [Flate.unfilterAll, Flate.getElem?_build _ _ j hj,
          unfilterByte_project raw pxH W chs k sel hk hsel hW j hj,
          getElem?_project _ _ _ _ _ (by
            rw [Flate.unfilterAll, Flate.size_build, hdiv, Nat.mul_assoc]; exact hj),
          Flate.unfilterAll, Flate.getElem?_build _ _ _ (by
            rw [(embPlane_row chs k W sel hk hsel hW j).1]
            have hr : j / (W * k) < pxH := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hW hk)).mpr hj
            have : (j / (W * k) + 1) * (W * chs) ≤ pxH * (W * chs) := Nat.mul_le_mul_right _ hr
            rw [Nat.add_mul, Nat.one_mul] at this
            have := (embPlane_row chs k W sel hk hsel hW j).2
            omega),
          Option.getD_some]
    refine ⟨?_, ?_⟩
    · exact core (chs - 1) id (by omega) (fun c hc => by simp only [id]; omega)
    · have := core 1 (fun _ => chs - 1) Nat.one_pos (fun _ _ => by omega)
      rwa [Nat.mul_one] at this
  · exact absurd h (by simp)

/-! ### Colour-key transparency

A `tRNS` chunk on the pass-through colour types names transparency a PDF
expresses without touching the samples: colour-key masking (ISO 32000-2
§8.9.6.4), `/Mask [min₁ max₁ … minₙ maxₙ]` over the image's `n` components
in sample units, a pixel whose every component falls inside its range not
painted. Greyscale and truecolour tRNS name one fully transparent sample
value (ISO/IEC 15948 §11.3.2.1), so the ranges are degenerate and the
mapping exact. An indexed tRNS gives each palette entry an alpha; with
`n = 1` the mask is a single index interval, so the mapping is exact when
the transparent entries form one interval and every other entry is
opaque — and anything else, a fractional alpha or two separated runs, is
refused rather than approximated (a soft mask is the exact form; it is
not this slice's). Entries past the chunk's length are opaque (§11.3.2.1),
which the interval never reaches. -/

/-- Sample `i` of a tRNS payload of two-byte big-endian samples. -/
def trnsSample (trns : ByteArray) (i : Nat) : Nat :=
  (trns[2 * i]?.getD 0).toNat * 256 + (trns[2 * i + 1]?.getD 0).toNat

/-- Palette entry `i`'s alpha as the tRNS chunk states it. -/
def trnsEntry (trns : ByteArray) (i : Nat) : Nat := (trns[i]?.getD 0).toNat

/-- Where a left-to-right scan of an indexed tRNS stands: no transparent
entry yet, inside the transparent run that opened at `lo`, or past the
run `[lo, hi]`. -/
inductive KeyState where
  | before
  | inside (lo : Nat)
  | after (lo hi : Nat)
  deriving Repr, BEq

def partialAlphaMsg : String :=
  "indexed PNG with partial transparency (tRNS alpha entries other than 0 and 255, or \
separated transparent entries) is not supported; re-export with a full alpha channel or \
flatten it"

/-- One entry: opaque keeps or closes the run, transparent opens or
continues it, and a second run or a fractional value is the refusal. -/
def keyStep (st : KeyState) (i a : Nat) : Except String KeyState :=
  if a = 255 then
    match st with
    | .before => .ok .before
    | .inside lo => .ok (.after lo (i - 1))
    | .after lo hi => .ok (.after lo hi)
  else if a = 0 then
    match st with
    | .before => .ok (.inside i)
    | .inside lo => .ok (.inside lo)
    | .after _ _ => .error partialAlphaMsg
  else .error partialAlphaMsg

/-- The scan state after the first `n` entries. -/
def keyScan (trns : ByteArray) : Nat → Except String KeyState
  | 0 => .ok .before
  | n + 1 =>
    match keyScan trns n with
    | .ok st => keyStep st n (trnsEntry trns n)
    | .error e => .error e

/-- The mask an indexed scan ends in: nothing, or the one interval. -/
def indexedKey (trns : ByteArray) : Except String (Array Nat) :=
  match keyScan trns trns.size with
  | .ok .before => .ok #[]
  | .ok (.inside lo) => .ok #[lo, trns.size - 1]
  | .ok (.after lo hi) => .ok #[lo, hi]
  | .error e => .error e

/-- The `/Mask` ranges a tRNS chunk denotes for an image of `space` at
`bitDepth` over `palette`, or the refusal: a malformed length, a sample
past the bit depth, more entries than the palette or the depth allows,
or indexed transparency no single interval can express. -/
def colorKeyRanges (space : Space) (bitDepth : Nat) (trns palette : ByteArray) :
    Except String (Array Nat) :=
  match space with
  | .gray =>
    if trns.size ≠ 2 then .error "corrupt PNG: a greyscale tRNS chunk must hold one 2-byte sample"
    else if 2 ^ bitDepth ≤ trnsSample trns 0 then
      .error s!"corrupt PNG: tRNS sample exceeds the {bitDepth}-bit range"
    else .ok #[trnsSample trns 0, trnsSample trns 0]
  | .rgb =>
    if trns.size ≠ 6 then
      .error "corrupt PNG: a truecolour tRNS chunk must hold three 2-byte samples"
    else if 2 ^ bitDepth ≤ trnsSample trns 0 ∨ 2 ^ bitDepth ≤ trnsSample trns 1 ∨
        2 ^ bitDepth ≤ trnsSample trns 2 then
      .error s!"corrupt PNG: tRNS sample exceeds the {bitDepth}-bit range"
    else .ok #[trnsSample trns 0, trnsSample trns 0, trnsSample trns 1, trnsSample trns 1,
      trnsSample trns 2, trnsSample trns 2]
  | .indexed =>
    if palette.size / 3 < trns.size then .error "corrupt PNG: tRNS has more entries than the palette"
    else if 2 ^ bitDepth < trns.size then
      .error "corrupt PNG: tRNS has more entries than the bit depth allows"
    else indexedKey trns

/-- Greyscale tRNS is exact: one sample, in range, is the degenerate range
`[v v]`. -/
theorem colorKeyRanges_gray_exact (bitDepth : Nat) (trns palette : ByteArray)
    (hsz : trns.size = 2) (hv : trnsSample trns 0 < 2 ^ bitDepth) :
    colorKeyRanges .gray bitDepth trns palette = .ok #[trnsSample trns 0, trnsSample trns 0] := by
  simp [colorKeyRanges, hsz, Nat.not_le.mpr hv]

/-- Truecolour tRNS is exact: three samples, in range, are the three
degenerate ranges. -/
theorem colorKeyRanges_rgb_exact (bitDepth : Nat) (trns palette : ByteArray)
    (hsz : trns.size = 6) (h0 : trnsSample trns 0 < 2 ^ bitDepth)
    (h1 : trnsSample trns 1 < 2 ^ bitDepth) (h2 : trnsSample trns 2 < 2 ^ bitDepth) :
    colorKeyRanges .rgb bitDepth trns palette =
      .ok #[trnsSample trns 0, trnsSample trns 0, trnsSample trns 1, trnsSample trns 1,
        trnsSample trns 2, trnsSample trns 2] := by
  simp [colorKeyRanges, hsz, Nat.not_le.mpr h0, Nat.not_le.mpr h1, Nat.not_le.mpr h2]

/-- Is entry `i` inside the transparent run a scan state describes? -/
def KeyState.keyed : KeyState → Nat → Bool
  | .before, _ => false
  | .inside lo, i => lo ≤ i
  | .after lo hi, i => lo ≤ i && i ≤ hi

/-- The run a state describes lies within the entries read. -/
def KeyState.wf : KeyState → Nat → Prop
  | .before, _ => True
  | .inside lo, n => lo < n
  | .after lo hi, n => lo ≤ hi ∧ hi < n

/-- The scan invariant: a state reached after `n` entries is well formed,
and every entry read is 0 exactly inside the run it describes and 255
everywhere else — so a scan that completes has read only 0 and 255, and
the run is the whole truth about the zeros. -/
theorem keyScan_spec (trns : ByteArray) :
    ∀ (n : Nat) (st : KeyState), keyScan trns n = .ok st →
      st.wf n ∧ ∀ i < n, trnsEntry trns i = if st.keyed i then 0 else 255 := by
  intro n
  induction n with
  | zero =>
    intro st h
    simp only [keyScan, Except.ok.injEq] at h
    subst h
    exact ⟨trivial, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro st' h
    simp only [keyScan] at h
    split at h
    · next st hst =>
      obtain ⟨hwf, hent⟩ := ih st hst
      -- The new entry decides the step; each arm extends the invariant by
      -- one index.
      have hstep : ∀ i < n + 1, i < n ∨ i = n := fun i hi => by omega
      unfold keyStep at h
      split at h
      · next ha =>
        cases st with
        | before =>
          simp only [Except.ok.injEq] at h
          subst h
          refine ⟨trivial, fun i hi => ?_⟩
          rcases hstep i hi with hlt | heq
          · exact hent i hlt
          · rw [heq]; simp [KeyState.keyed, ha]
        | inside lo =>
          simp only [Except.ok.injEq] at h
          subst h
          simp only [KeyState.wf] at hwf
          refine ⟨⟨by omega, by omega⟩, fun i hi => ?_⟩
          rcases hstep i hi with hlt | heq
          · rw [hent i hlt]
            simp [KeyState.keyed, show i ≤ n - 1 by omega]
          · rw [heq]
            simp [KeyState.keyed, ha, show ¬ n ≤ n - 1 by omega]
        | after lo hi =>
          simp only [Except.ok.injEq] at h
          subst h
          simp only [KeyState.wf] at hwf
          refine ⟨⟨hwf.1, by omega⟩, fun i hi' => ?_⟩
          rcases hstep i hi' with hlt | heq
          · exact hent i hlt
          · rw [heq]
            simp [KeyState.keyed, ha, show ¬ n ≤ hi by omega]
      · next ha =>
        split at h
        · next ha0 =>
          cases st with
          | before =>
            simp only [Except.ok.injEq] at h
            subst h
            refine ⟨Nat.lt_succ_self n, fun i hi => ?_⟩
            rcases hstep i hi with hlt | heq
            · rw [hent i hlt]
              simp [KeyState.keyed, show ¬ n ≤ i by omega]
            · rw [heq]; simp [KeyState.keyed, ha0]
          | inside lo =>
            simp only [Except.ok.injEq] at h
            subst h
            simp only [KeyState.wf] at hwf
            refine ⟨show lo < n + 1 by omega, fun i hi => ?_⟩
            rcases hstep i hi with hlt | heq
            · exact hent i hlt
            · rw [heq]
              simp [KeyState.keyed, ha0, show lo ≤ n by omega]
          | after lo hi => exact absurd h (by simp)
        · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **The interval is the whole truth about the transparent entries.** An
indexed tRNS that maps to `/Mask [lo hi]` has entry `i` transparent
exactly when `lo ≤ i ≤ hi` — over every index, the entries past the chunk
being opaque by the PNG rule. -/
theorem colorKeyRanges_indexed_covers (bitDepth : Nat) (trns palette : ByteArray) (lo hi : Nat)
    (h : colorKeyRanges .indexed bitDepth trns palette = .ok #[lo, hi]) :
    ∀ i, (i < trns.size ∧ trnsEntry trns i = 0) ↔ (lo ≤ i ∧ i ≤ hi) := by
  simp only [colorKeyRanges] at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  next hpal hdepth =>
  unfold indexedKey at h
  split at h
  · exact absurd h (by simp)
  · next a hscan =>
    obtain ⟨hwf, hent⟩ := keyScan_spec trns trns.size _ hscan
    simp only [KeyState.wf] at hwf
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i
    constructor
    · rintro ⟨hi, hz⟩
      rw [hent i hi] at hz
      by_cases hle : lo ≤ i
      · exact ⟨hle, by omega⟩
      · simp [KeyState.keyed, hle] at hz
    · rintro ⟨hlo, hhi⟩
      have hi : i < trns.size := by omega
      refine ⟨hi, ?_⟩
      rw [hent i hi]
      simp [KeyState.keyed, hlo]
  · next a b hscan =>
    obtain ⟨hwf, hent⟩ := keyScan_spec trns trns.size _ hscan
    simp only [KeyState.wf] at hwf
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i
    constructor
    · rintro ⟨hi', hz⟩
      rw [hent i hi'] at hz
      by_cases h1 : lo ≤ i
      · by_cases h2 : i ≤ hi
        · exact ⟨h1, h2⟩
        · simp [KeyState.keyed, h2] at hz
      · simp [KeyState.keyed, h1] at hz
    · rintro ⟨hlo, hhi⟩
      have hi : i < trns.size := by omega
      refine ⟨hi, ?_⟩
      rw [hent i hi]
      simp [KeyState.keyed, hlo, hhi]
  · exact absurd h (by simp)

/-- Every emitted range value is a legal sample at the bit depth: the
`/Mask` array the dictionary writes is in range for its
`/BitsPerComponent`. -/
theorem colorKeyRanges_between (space : Space) (bitDepth : Nat) (trns palette : ByteArray)
    (ks : Array Nat) (h : colorKeyRanges space bitDepth trns palette = .ok ks) :
    ∀ v ∈ ks, v < 2 ^ bitDepth := by
  cases space with
  | gray =>
    simp only [colorKeyRanges] at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    next hv =>
    simp only [Except.ok.injEq] at h
    subst h
    intro v hv'
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl <;> omega
  | rgb =>
    simp only [colorKeyRanges] at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    next hv =>
    simp only [Except.ok.injEq] at h
    subst h
    intro v hv'
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | indexed =>
    simp only [colorKeyRanges] at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    next hpal hdepth =>
    unfold indexedKey at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      intro v hv
      simp at hv
    · next lo hscan =>
      have hwf := (keyScan_spec trns trns.size _ hscan).1
      simp only [KeyState.wf] at hwf
      simp only [Except.ok.injEq] at h
      subst h
      intro v hv
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> omega
    · next lo hi hscan =>
      have hwf := (keyScan_spec trns trns.size _ hscan).1
      simp only [KeyState.wf] at hwf
      simp only [Except.ok.injEq] at h
      subst h
      intro v hv
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> omega
    · exact absurd h (by simp)

/-- **An empty mask is paid for.** For every tRNS shape, the mapping
returns no ranges only for an indexed chunk whose every entry is opaque —
there was no transparency to carry. Greyscale and truecolour tRNS never
map to an empty mask: they are exact or refused. -/
theorem colorKeyRanges_accounts (space : Space) (bitDepth : Nat) (trns palette : ByteArray)
    (h : colorKeyRanges space bitDepth trns palette = .ok #[]) :
    space = .indexed ∧ ∀ i < trns.size, trnsEntry trns i = 255 := by
  cases space with
  | gray =>
    simp only [colorKeyRanges] at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    exact absurd h (by simp)
  | rgb =>
    simp only [colorKeyRanges] at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    exact absurd h (by simp)
  | indexed =>
    refine ⟨rfl, ?_⟩
    simp only [colorKeyRanges] at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    unfold indexedKey at h
    split at h
    · next hscan =>
      have hent := (keyScan_spec trns trns.size _ hscan).2
      intro i hi
      rw [hent i hi]
      rfl
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **Lossy transparency is refused, never dropped.** An indexed tRNS
carrying any alpha other than 0 or 255 maps to no ranges at all: the
result is an error the driver names. -/
theorem colorKeyRanges_partial_accounts (bitDepth : Nat) (trns palette : ByteArray)
    (hpartial : ∃ i < trns.size, trnsEntry trns i ≠ 0 ∧ trnsEntry trns i ≠ 255) :
    ∃ e, colorKeyRanges .indexed bitDepth trns palette = .error e := by
  obtain ⟨i, hi, hz, ho⟩ := hpartial
  match hres : colorKeyRanges .indexed bitDepth trns palette with
  | .error e => exact ⟨e, rfl⟩
  | .ok ks =>
    exfalso
    simp only [colorKeyRanges] at hres
    split at hres
    · exact absurd hres (by simp)
    split at hres
    · exact absurd hres (by simp)
    unfold indexedKey at hres
    have hscan : ∃ st, keyScan trns trns.size = .ok st := by
      split at hres
      · next hs => exact ⟨_, hs⟩
      · next hs => exact ⟨_, hs⟩
      · next hs => exact ⟨_, hs⟩
      · exact absurd hres (by simp)
    obtain ⟨st, hst⟩ := hscan
    have hent := (keyScan_spec trns trns.size st hst).2 i hi
    split at hent
    · exact hz hent
    · exact ho hent

/-! ## The source: what a header says

`Source` is every fact the embedding decision can read from a file's
header, format by format, plus the compressed payload as a slice of the
input. Nothing here is a decision: a `Source` may describe an interlaced
PNG, a CMYK JPEG, or a WebP file — `plan` is where each is embedded or
refused by name. `probe` is the one loop over the bytes; its totality is
the fuzz oracle's claim (`scripts/img-fuzz.lean`), not a theorem, and the
theorems live on `plan`, the pure match after it. -/

structure Source where
  format : Format
  pxW : Nat
  pxH : Nat
  dpiX : Nat := defaultDpi
  dpiY : Nat := defaultDpi
  /-- PNG bit depth; a JPEG's sample precision. -/
  bitDepth : Nat := 8
  /-- PNG colour type (0, 2, 3, 4, 6); a JPEG's component count (1, 3, 4). -/
  colorType : Nat := 2
  /-- PNG Adam7 interlacing declared. -/
  interlace : Bool := false
  /-- PNG PLTE payload, RGB triples. -/
  palette : ByteArray := ByteArray.empty
  /-- PNG tRNS payload, verbatim; `none` when the chunk is absent (an empty
  chunk is a present, all-opaque one). -/
  trns : Option ByteArray := none
  /-- An embedded colour profile: a PNG iCCP's compressed bytes (zlib,
  `iccIsZlib`), or a JPEG's APP2 `ICC_PROFILE` segments concatenated in
  sequence order (raw). Empty when none. -/
  icc : ByteArray := ByteArray.empty
  iccIsZlib : Bool := false
  /-- PNG sRGB chunk: the rendering intent. -/
  srgbIntent : Option Nat := none
  /-- PNG gAMA: gamma × 100000. -/
  gamma : Option Nat := none
  /-- PNG cHRM: the eight chromaticity values × 100000. -/
  chrm : Option (Array Nat) := none
  /-- Exif orientation (tag 0x0112), 1–8; 1 when undeclared. -/
  orientation : Nat := 1
  /-- JPEG APP14 Adobe segment: the colour transform flag. -/
  adobeTransform : Option Nat := none
  /-- The stream a pass-through plan embeds: a PNG's concatenated IDAT, a
  JPEG's whole file. Empty for a PDF page. -/
  payload : ByteArray := ByteArray.empty
  /-- A PDF's page 1 as a form XObject, with its closure witness. -/
  form : Option { f : PdfRead.Form // f.wf } := none
  deriving Inhabited

/-- The PNG colour type table (ISO/IEC 15948 §11.2.2): the sample
interpretation and, for the alpha types, the channel count that must
really decode. The one place the type numbers are spelled — `plan` and
`Plan.recodes` both read it, which is what ties the cache gate to the
planner (`recodes_iff`). -/
def pngSpace : Nat → Option (Space × Option Nat)
  | 0 => some (.gray, none)
  | 2 => some (.rgb, none)
  | 3 => some (.indexed, none)
  | 4 => some (.gray, some 2)
  | 6 => some (.rgb, some 4)
  | _ => none

/-- A PNG header into a `Source`: signature, IHDR first, then chunks of
`length type data crc` — pHYs, PLTE, tRNS, iCCP, sRGB, gAMA, cHRM read,
IDAT concatenated, IEND ends the walk. Structural corruption is refused
here (a lying length, a chunk out of order, a colour type the spec has
no row for); what the spec allows but the engine does not embed
(interlace, a 16-bit alpha) is a fact on the `Source` for `plan` to
refuse by name. -/
def probePng (b : ByteArray) : Except String Source := do
  unless sliceEq b 0 pngSig do
    throw "not a PNG file (bad signature)"
  -- IHDR must be first (ISO/IEC 15948 §5.6).
  unless u32be? b 8 == some 13 && sliceEq b 12 [73, 72, 68, 82] do
    throw "corrupt PNG: IHDR is not the first chunk"
  let some pxW := u32be? b 16 | throw "truncated PNG: no IHDR width"
  let some pxH := u32be? b 20 | throw "truncated PNG: no IHDR height"
  let some bitDepth := u8? b 24 | throw "truncated PNG: no IHDR bit depth"
  let some colorType := u8? b 25 | throw "truncated PNG: no IHDR colour type"
  let some interlace := u8? b 28 | throw "truncated PNG: no IHDR interlace flag"
  if pxW == 0 || pxH == 0 then
    throw "corrupt PNG: zero width or height"
  let some (space, alpha) := pngSpace colorType
    | throw s!"corrupt PNG: colour type {colorType}"
  unless [1, 2, 4, 8, 16].contains bitDepth do
    throw s!"corrupt PNG: bit depth {bitDepth}"
  if space == .rgb && alpha.isNone && bitDepth < 8 then
    throw s!"corrupt PNG: truecolour at bit depth {bitDepth}"
  if alpha.isSome && bitDepth < 8 then
    throw s!"corrupt PNG: an alpha channel at bit depth {bitDepth}"
  -- Walk the chunks. `i` advances by at least 12 per step, so the loop over
  -- `b.size` iterations covers every well-formed file; a lying length that
  -- points past the end is caught by the bounds-checked reads.
  let mut dpiX := defaultDpi
  let mut dpiY := defaultDpi
  let mut palette := ByteArray.empty
  let mut trns : Option ByteArray := none
  let mut icc := ByteArray.empty
  let mut srgbIntent : Option Nat := none
  let mut gamma : Option Nat := none
  let mut chrm : Option (Array Nat) := none
  let mut idat := ByteArray.empty
  let mut sawEnd := false
  let mut i := 8
  for _ in [0:b.size] do
    let some len := u32be? b i | break
    let some t0 := u8? b (i + 4) | break
    if i + 12 + len > b.size then
      throw "truncated PNG: a chunk overruns the file"
    -- Chunk types compared byte-wise; the reads are in bounds by the check.
    if t0 == 112 && sliceEq b (i + 4) [112, 72, 89, 115] then  -- pHYs
      if len == 9 then
        let some px := u32be? b (i + 8) | break
        let some py := u32be? b (i + 12) | break
        let some unit := u8? b (i + 16) | break
        -- Unit 1 is the metre; unit 0 declares aspect ratio only, and the
        -- physical size stays unknown (the default density).
        if unit == 1 && px > 0 && py > 0 then
          dpiX := max 1 (ppmToDpi px)
          dpiY := max 1 (ppmToDpi py)
    else if t0 == 80 && sliceEq b (i + 4) [80, 76, 84, 69] then  -- PLTE
      palette := b.extract (i + 8) (i + 8 + len)
    else if t0 == 116 && sliceEq b (i + 4) [116, 82, 78, 83] then  -- tRNS
      -- One chunk, after PLTE and before IDAT, never on an alpha type
      -- (ISO/IEC 15948 §5.6, §11.3.2.1): the transparency it names is
      -- carried exactly or refused, so the walk keeps the payload and
      -- `colorKeyRanges` judges it once the geometry is known.
      if trns.isSome then
        throw "corrupt PNG: more than one tRNS chunk"
      if !idat.isEmpty then
        throw "corrupt PNG: tRNS after the image data"
      if alpha.isSome then
        throw "corrupt PNG: tRNS is not allowed with an alpha channel"
      if space == .indexed && palette.isEmpty then
        throw "corrupt PNG: tRNS before PLTE"
      trns := some (b.extract (i + 8) (i + 8 + len))
    else if t0 == 105 && sliceEq b (i + 4) [105, 67, 67, 80] then  -- iCCP
      -- Profile name (1–79 bytes, null-terminated), compression method
      -- (0 = zlib, the only one defined), then the compressed profile
      -- (ISO/IEC 15948 §11.3.3.3).
      if !icc.isEmpty then
        throw "corrupt PNG: more than one iCCP chunk"
      let mut nameEnd := i + 8
      for _ in [0:80] do
        if u8? b nameEnd == some 0 || nameEnd ≥ i + 8 + len then break
        nameEnd := nameEnd + 1
      if u8? b nameEnd != some 0 || nameEnd == i + 8 then
        throw "corrupt PNG: iCCP chunk without a profile name"
      if u8? b (nameEnd + 1) != some 0 then
        throw "corrupt PNG: iCCP chunk with an unknown compression method"
      icc := b.extract (nameEnd + 2) (i + 8 + len)
    else if t0 == 115 && sliceEq b (i + 4) [115, 82, 71, 66] then  -- sRGB
      if len == 1 then srgbIntent := u8? b (i + 8)
    else if t0 == 103 && sliceEq b (i + 4) [103, 65, 77, 65] then  -- gAMA
      if len == 4 then gamma := u32be? b (i + 8)
    else if t0 == 99 && sliceEq b (i + 4) [99, 72, 82, 77] then  -- cHRM
      if len == 32 then
        let mut vals : Array Nat := #[]
        for k in [0:8] do
          if let some v := u32be? b (i + 8 + 4 * k) then vals := vals.push v
        if vals.size == 8 then chrm := some vals
    else if t0 == 73 && sliceEq b (i + 4) [73, 68, 65, 84] then  -- IDAT
      idat := idat ++ b.extract (i + 8) (i + 8 + len)
    else if t0 == 73 && sliceEq b (i + 4) [73, 69, 78, 68] then  -- IEND
      sawEnd := true
      break
    i := i + 12 + len
  unless sawEnd do
    throw "truncated PNG: no IEND chunk"
  if idat.isEmpty then
    throw "corrupt PNG: no image data (IDAT)"
  if space == .indexed && (palette.isEmpty || palette.size % 3 != 0) then
    throw "corrupt PNG: indexed colour without a usable PLTE"
  return { format := .png, pxW, pxH, dpiX, dpiY, bitDepth, colorType,
           interlace := interlace != 0, palette, trns, icc, iccIsZlib := true,
           srgbIntent, gamma, chrm, payload := idat }

/-! ## JPEG

A marker stream: `FF xx`, most segments carrying a big-endian length that
includes its own two bytes. `SOFn` carries the dimensions (ISO/IEC 10918-1
§B.2.2), the JFIF `APP0` the density, an `APP1` Exif block the orientation
(tag 0x0112 in IFD0, CIPA DC-008), `APP2 ICC_PROFILE` segments the colour
profile in numbered pieces (ICC.1 Annex B.4), `APP14 Adobe` the colour
transform flag. The entropy-coded data after `SOS` never contains a bare
`FF xx` marker except via `FF 00` stuffing and the restart markers, so the
header walk stops there — the dimensions must have appeared first for the
file to be an image at all. -/

/-- Is this marker byte an SOFn frame header? DHT (C4), JPG (C8) and DAC
(CC) share the Cx block and are not. -/
private def isSof (m : Nat) : Bool :=
  0xC0 ≤ m && m ≤ 0xCF && m != 0xC4 && m != 0xC8 && m != 0xCC

/-- The Exif orientation an APP1 segment at `t` (the TIFF header) states:
byte order, the 42, IFD0's offset, then its entries — tag, type, count,
value — read for tag 0x0112 as a SHORT. Only a value in 1–8 counts;
anything else, or no tag, is the default orientation. Every read stays
inside `end_`, the segment's end. -/
private def exifOrientation (b : ByteArray) (t end_ : Nat) : Nat := Id.run do
  let le := u8? b t == some 0x49 && u8? b (t + 1) == some 0x49
  let be := u8? b t == some 0x4D && u8? b (t + 1) == some 0x4D
  unless le || be do return 1
  unless u16? le b (t + 2) == some 42 do return 1
  let some ifd := u32? le b (t + 4) | return 1
  let some count := u16? le b (t + ifd) | return 1
  for k in [0:count] do
    let e := t + ifd + 2 + 12 * k
    if e + 12 > end_ then return 1
    if u16? le b e == some 0x0112 && u16? le b (e + 2) == some 3 then
      let some v := u16? le b (e + 8) | return 1
      return if 1 ≤ v && v ≤ 8 then v else 1
  return 1

def probeJpeg (b : ByteArray) : Except String Source := do
  unless sliceEq b 0 [0xFF, 0xD8] do
    throw "not a JPEG file (no SOI marker)"
  let mut i := 2
  let mut dpiX := defaultDpi
  let mut dpiY := defaultDpi
  let mut dims : Option (Nat × Nat × Nat × Nat) := none
  let mut orientation := 1
  let mut adobeTransform : Option Nat := none
  -- ICC pieces by sequence number (1-based), the count from the first
  -- piece seen: concatenated in sequence order whatever the file order.
  let mut iccPieces : Array ByteArray := #[]
  for _ in [0:b.size] do
    -- Fill bytes: any number of FFs may precede a marker.
    unless u8? b i == some 0xFF do
      throw "corrupt JPEG: expected a marker"
    let mut j := i + 1
    for _ in [0:b.size] do
      if u8? b j == some 0xFF then j := j + 1 else break
    let some m := u8? b j | throw "truncated JPEG: file ends inside a marker"
    if m == 0xD8 || (0xD0 ≤ m && m ≤ 0xD7) || m == 0x01 then
      -- Standalone markers carry no length.
      i := j + 1
      continue
    if m == 0xD9 || m == 0xDA then
      -- EOI, or the scan begins: the header is over.
      break
    let some len := u16be? b (j + 1) | throw "truncated JPEG: marker without a length"
    if len < 2 || j + 1 + len > b.size then
      throw "truncated JPEG: a segment overruns the file"
    if isSof m then
      let some precision := u8? b (j + 3) | throw "truncated JPEG: SOF too short"
      let some pxH := u16be? b (j + 4) | throw "truncated JPEG: SOF too short"
      let some pxW := u16be? b (j + 6) | throw "truncated JPEG: SOF too short"
      let some ncomp := u8? b (j + 8) | throw "truncated JPEG: SOF too short"
      dims := some (pxW, pxH, precision, ncomp)
    else if m == 0xE0 && sliceEq b (j + 3) [0x4A, 0x46, 0x49, 0x46, 0] then
      -- JFIF APP0: version(2) units(1) Xdensity(2) Ydensity(2).
      let some unit := u8? b (j + 10) | throw "truncated JPEG: APP0 too short"
      let some dx := u16be? b (j + 11) | throw "truncated JPEG: APP0 too short"
      let some dy := u16be? b (j + 13) | throw "truncated JPEG: APP0 too short"
      if dx > 0 && dy > 0 then
        if unit == 1 then
          dpiX := dx
          dpiY := dy
        else if unit == 2 then  -- dots per centimetre
          dpiX := max 1 ((dx * 254 + 50) / 100)
          dpiY := max 1 ((dy * 254 + 50) / 100)
    else if m == 0xE1 && sliceEq b (j + 3) [0x45, 0x78, 0x69, 0x66, 0, 0] then
      -- APP1 Exif: "Exif\0\0" then the TIFF header.
      orientation := exifOrientation b (j + 9) (j + 1 + len)
    else if m == 0xE2 && sliceEq b (j + 3)
        [0x49, 0x43, 0x43, 0x5F, 0x50, 0x52, 0x4F, 0x46, 0x49, 0x4C, 0x45, 0] then
      -- APP2 "ICC_PROFILE\0" seq(1) count(1) data.
      let some seq := u8? b (j + 15) | throw "truncated JPEG: APP2 too short"
      let some count := u8? b (j + 16) | throw "truncated JPEG: APP2 too short"
      if iccPieces.isEmpty then
        iccPieces := Array.replicate count ByteArray.empty
      if 1 ≤ seq then
        iccPieces := iccPieces.setIfInBounds (seq - 1) (b.extract (j + 17) (j + 1 + len))
    else if m == 0xEE && sliceEq b (j + 3) [0x41, 0x64, 0x6F, 0x62, 0x65] && len ≥ 12 then
      -- APP14 "Adobe": version(2) flags0(2) flags1(2) transform(1).
      adobeTransform := u8? b (j + 14)
    i := j + 1 + len
  let some (pxW, pxH, precision, ncomp) := dims
    | throw "corrupt JPEG: no frame header (SOFn) before the scan"
  if pxW == 0 || pxH == 0 then
    throw "corrupt JPEG: zero width or height"
  unless ncomp == 1 || ncomp == 3 || ncomp == 4 do
    throw s!"corrupt JPEG: {ncomp} components"
  let mut icc := ByteArray.empty
  for piece in iccPieces do
    icc := icc ++ piece
  return { format := .jpeg, pxW, pxH, dpiX, dpiY, bitDepth := precision, colorType := ncomp,
           icc, orientation, adobeTransform, payload := b }

/-! ## The formats no PDF filter decodes

Recognised by signature, their dimensions read from the container so a
later HTML-only path can size an `<img>`, and refused for the PDF by name
(`plan_refuses_named`). Nothing here decodes a pixel. -/

/-- WebP (RIFF `WEBP`): a `VP8 ` key frame's 14-bit dimensions, a `VP8L`
header's packed 14-bit dimensions plus one, or a `VP8X` canvas's 24-bit
dimensions plus one. -/
def probeWebp (b : ByteArray) : Except String Source := do
  unless sliceEq b 0 [0x52, 0x49, 0x46, 0x46] && sliceEq b 8 [0x57, 0x45, 0x42, 0x50] do
    throw "not a WebP file (no RIFF WEBP header)"
  let dims : Option (Nat × Nat) :=
    if sliceEq b 12 [0x56, 0x50, 0x38, 0x20] then  -- "VP8 "
      if sliceEq b 23 [0x9D, 0x01, 0x2A] then do
        return ((← u16le? b 26) % 16384, (← u16le? b 28) % 16384)
      else none
    else if sliceEq b 12 [0x56, 0x50, 0x38, 0x4C] then  -- "VP8L"
      if u8? b 20 == some 0x2F then do
        let bits ← u32le? b 21
        return (bits % 16384 + 1, bits / 16384 % 16384 + 1)
      else none
    else if sliceEq b 12 [0x56, 0x50, 0x38, 0x58] then do  -- "VP8X"
      return ((← u24le? b 24) + 1, (← u24le? b 27) + 1)
    else none
  let some (pxW, pxH) := dims | throw "truncated WebP file: no readable image header"
  return { format := .webp, pxW, pxH }

/-- Find a four-byte box or chunk tag in the first `limit` bytes. -/
private def findTag (b : ByteArray) (tag : List Nat) (limit : Nat) : Option Nat := Id.run do
  for i in [0:min b.size limit] do
    if sliceEq b i tag then return some i
  return none

/-- The bytes a header scan reads before giving up: the boxes that carry
dimensions sit inside the first few kilobytes of every container; the
bound keeps the probe a header walk on a large file. -/
private def headerScanLimit : Nat := 65536

/-- AVIF (ISOBMFF, `ftyp` brand `avif`/`avis`): dimensions from the `ispe`
item property — version/flags, then width and height as u32. -/
def probeAvif (b : ByteArray) : Except String Source := do
  unless sliceEq b 4 [0x66, 0x74, 0x79, 0x70] &&
      (sliceEq b 8 [0x61, 0x76, 0x69, 0x66] || sliceEq b 8 [0x61, 0x76, 0x69, 0x73]) do
    throw "not an AVIF file (no ftyp avif brand)"
  let some i := findTag b [0x69, 0x73, 0x70, 0x65] headerScanLimit
    | throw "truncated AVIF file: no image spatial extents (ispe)"
  let some pxW := u32be? b (i + 8) | throw "truncated AVIF file: ispe too short"
  let some pxH := u32be? b (i + 12) | throw "truncated AVIF file: ispe too short"
  return { format := .avif, pxW, pxH }

/-- Bit `k` of a little-endian bit stream starting at byte `off`
(ISO/IEC 18181-1 reads its headers LSB first). -/
private def bitAt (b : ByteArray) (off k : Nat) : Option Nat := do
  return (← u8? b (off + k / 8)) / 2 ^ (k % 8) % 2

/-- `n` bits from bit position `k`, LSB first. -/
private def bitsAt (b : ByteArray) (off k n : Nat) : Option Nat := Id.run do
  let mut v := 0
  for j in [0:n] do
    let some bit := bitAt b off (k + j) | return none
    v := v + bit * 2 ^ j
  return some v

/-- A JPEG XL `SizeHeader` at byte `off`: `small` picks 5-bit multiples of
eight, else a `U32` with selectors for 9, 13, 18, or 30 bits (each plus
one); a 3-bit aspect ratio replaces the width when non-zero (the table is
the codec's `FixedAspectRatios`). Returns width and height. -/
private def jxlSize (b : ByteArray) (off : Nat) : Option (Nat × Nat) := do
  let small ← bitAt b off 0
  -- (value, bits consumed) for one U32.
  let u32At (k : Nat) : Option (Nat × Nat) := do
    let sel ← bitsAt b off k 2
    let n := match sel with | 0 => 9 | 1 => 13 | 2 => 18 | _ => 30
    let v ← bitsAt b off (k + 2) n
    return (v + 1, 2 + n)
  let (h, k) ← (if small == 1 then (bitsAt b off 1 5).map fun y => ((y + 1) * 8, 6)
    else (u32At 1).map fun (v, n) => (v, 1 + n) : Option (Nat × Nat))
  let ratio ← bitsAt b off k 3
  let w ← (match ratio with
    | 0 => if small == 1 then (bitsAt b off (k + 3) 5).map fun x => (x + 1) * 8
           else (u32At (k + 3)).map (·.1)
    | 1 => some h
    | 2 => some (h * 12 / 10)
    | 3 => some (h * 4 / 3)
    | 4 => some (h * 3 / 2)
    | 5 => some (h * 16 / 9)
    | 6 => some (h * 5 / 4)
    | _ => some (h * 2) : Option Nat)
  return (w, h)

/-- JPEG XL: a bare codestream (`FF 0A`) or the ISOBMFF container (the
`JXL ` signature box), whose codestream sits in a `jxlc` box or begins in
the first `jxlp` box after its 4-byte index. -/
def probeJxl (b : ByteArray) : Except String Source := do
  let codestream : Option Nat :=
    if sliceEq b 0 [0xFF, 0x0A] then some 0
    else if sliceEq b 0 [0, 0, 0, 0x0C, 0x4A, 0x58, 0x4C, 0x20, 0x0D, 0x0A, 0x87, 0x0A] then
      match findTag b [0x6A, 0x78, 0x6C, 0x63] headerScanLimit with  -- jxlc
      | some i => some (i + 4)
      | none => (findTag b [0x6A, 0x78, 0x6C, 0x70] headerScanLimit).map (· + 8)  -- jxlp
    else none
  let some cs := codestream | throw "not a JPEG XL file (no signature)"
  unless sliceEq b cs [0xFF, 0x0A] do
    throw "truncated JPEG XL file: no codestream header"
  let some (pxW, pxH) := jxlSize b (cs + 2) | throw "truncated JPEG XL file: size header cut"
  return { format := .jxl, pxW, pxH }

/-- JPEG 2000: a JP2 container (signature box, dimensions from `ihdr` —
height then width) or a raw J2K codestream (`SOC SIZ`, dimensions
`Xsiz − XOsiz` by `Ysiz − YOsiz`, ISO/IEC 15444-1 Annex A.5.1). -/
def probeJpx (b : ByteArray) : Except String Source := do
  if sliceEq b 0 [0, 0, 0, 0x0C, 0x6A, 0x50, 0x20, 0x20, 0x0D, 0x0A, 0x87, 0x0A] then
    let some i := findTag b [0x69, 0x68, 0x64, 0x72] headerScanLimit
      | throw "truncated JPEG 2000 file: no image header box (ihdr)"
    let some pxH := u32be? b (i + 4) | throw "truncated JPEG 2000 file: ihdr too short"
    let some pxW := u32be? b (i + 8) | throw "truncated JPEG 2000 file: ihdr too short"
    return { format := .jpx, pxW, pxH }
  else if sliceEq b 0 [0xFF, 0x4F, 0xFF, 0x51] then
    let some xsiz := u32be? b 8 | throw "truncated JPEG 2000 codestream: SIZ too short"
    let some ysiz := u32be? b 12 | throw "truncated JPEG 2000 codestream: SIZ too short"
    let some xo := u32be? b 16 | throw "truncated JPEG 2000 codestream: SIZ too short"
    let some yo := u32be? b 20 | throw "truncated JPEG 2000 codestream: SIZ too short"
    return { format := .jpx, pxW := xsiz - xo, pxH := ysiz - yo }
  else throw "not a JPEG 2000 file (no signature)"

/-- A PDF page's geometry and resource closure, shared by default and
explicit page selection. The pixel fields round to whole points; placement
reads the form's box exactly. -/
def probePdf (b : ByteArray) (page : PdfRead.PageSelection := .first) :
    Except String Source := do
  let f ← PdfRead.readForm b page
  return { format := .pdf
           pxW := (max 0 f.val.w / spPerPt).toNat
           pxH := (max 0 f.val.h / spPerPt).toNat
           form := some f }

/-- Read any asset's header, told apart by signature: PNG, JPEG, a PDF
whose page 1 reads as a form XObject, and the recognised-but-unembeddable
containers. Total over every input — the fuzz oracle's claim, not a
theorem: the loops are bounded by the file and every read is checked. -/
def probe (b : ByteArray) : Except String Source :=
  if sliceEq b 0 pngSig then probePng b
  else if sliceEq b 0 [0xFF, 0xD8] then probeJpeg b
  else if sliceEq b 0 [0x25, 0x50, 0x44, 0x46] then probePdf b
  else if sliceEq b 0 [0x52, 0x49, 0x46, 0x46] && sliceEq b 8 [0x57, 0x45, 0x42, 0x50] then
    probeWebp b
  else if sliceEq b 4 [0x66, 0x74, 0x79, 0x70] &&
      (sliceEq b 8 [0x61, 0x76, 0x69, 0x66] || sliceEq b 8 [0x61, 0x76, 0x69, 0x73]) then
    probeAvif b
  else if sliceEq b 0 [0xFF, 0x0A] ||
      sliceEq b 0 [0, 0, 0, 0x0C, 0x4A, 0x58, 0x4C, 0x20, 0x0D, 0x0A, 0x87, 0x0A] then
    probeJxl b
  else if sliceEq b 0 [0, 0, 0, 0x0C, 0x6A, 0x50, 0x20, 0x20, 0x0D, 0x0A, 0x87, 0x0A] ||
      sliceEq b 0 [0xFF, 0x4F, 0xFF, 0x51] then
    probeJpx b
  else .error "not a PNG, JPEG, or PDF file (unrecognised signature)"

/-- PDFs resolve the requested physical page. Raster readers discard the
page value, including zero and out-of-range ordinals: `luatex.def`'s
`Gread@png` clears `Gin@page`, and `Gread@jpg` aliases it. The ordinary
probe still owns format validation and its named refusals. -/
def probePage (b : ByteArray) (page : PdfRead.PageSelection) : Except String Source :=
  if sliceEq b 0 [0x25, 0x50, 0x44, 0x46] then probePdf b page
  else probe b

/-! ## The plan: a pure match

Every non-source input to the embedding decision is a `PlanParams` field —
the projection of a declared output contract onto images (a later slice
wires it; the driver passes `default` today) — and every field is in the
cache key (`PlanParams.key`, injective by `planParams_serialize_inj`), so
two plans that could differ never share a cache entry and nothing that is
not a plan input (a document path, an output path) enters the key. -/

/-- What to do with an embedded colour profile: carry it as `/ICCBased`
(the emission is a later slice's; the plan is typed for it), or drop it
and say so (`.iccDropped`, the driver's W0603). -/
inductive IccPolicy where
  | dropWithDiag
  | carry
  deriving Repr, DecidableEq, Inhabited

structure PlanParams where
  /-- May a JPEG 2000 codestream pass through as `/JPXDecode`? The arm is a
  later slice's; every value refuses today, and the key already carries it. -/
  jpxPermitted : Bool := false
  /-- May a plan carry a soft mask (`/SMask`)? A profile that forbids
  transparency says no, and the alpha arm then refuses instead of
  flattening. -/
  softMaskPermitted : Bool := true
  /-- The deepest sample a pass-through may declare; deeper refuses (never
  downsampled). -/
  maxBpc : Nat := 16
  iccPolicy : IccPolicy := .dropWithDiag
  deriving Repr, DecidableEq, Inhabited

/-- The parameters the driver passes until a declaration projects them. -/
def PlanParams.default : PlanParams := {}

/-- Fixed-width bytes: two flags, `maxBpc` as u32, the policy tag. The
shape `planParams_serialize_inj` reads. -/
def PlanParams.serialize (p : PlanParams) : ByteArray :=
  ⟨#[cond p.jpxPermitted 1 0, cond p.softMaskPermitted 1 0,
     UInt8.ofNat (p.maxBpc / 16777216 % 256), UInt8.ofNat (p.maxBpc / 65536 % 256),
     UInt8.ofNat (p.maxBpc / 256 % 256), UInt8.ofNat (p.maxBpc % 256),
     match p.iccPolicy with | .dropWithDiag => 0 | .carry => 1]⟩

private theorem ofNat_inj_of_lt (x y : Nat) (hx : x < 256) (hy : y < 256)
    (h : UInt8.ofNat x = UInt8.ofNat y) : x = y := by
  have := congrArg UInt8.toNat h
  simpa [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-- **The key tells plans apart.** Two parameter records with the same
serialization are the same record (for a `maxBpc` inside the u32 the
format spells — every declared depth is). -/
theorem planParams_serialize_inj (a b : PlanParams)
    (ha : a.maxBpc < 4294967296) (hb : b.maxBpc < 4294967296)
    (h : a.serialize = b.serialize) : a = b := by
  obtain ⟨aj, as_, am, ai⟩ := a
  obtain ⟨bj, bs, bm, bi⟩ := b
  simp only at ha hb
  have hm : am = bm := by
    unfold PlanParams.serialize at h
    simp only [ByteArray.mk.injEq] at h
    have h := List.toArray_inj h
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨-, -, h3, h4, h5, h6, -⟩ := h
    have e3 := ofNat_inj_of_lt _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h3
    have e4 := ofNat_inj_of_lt _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h4
    have e5 := ofNat_inj_of_lt _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h5
    have e6 := ofNat_inj_of_lt _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h6
    omega
  subst hm
  cases aj <;> cases bj <;> cases as_ <;> cases bs <;> cases ai <;> cases bi <;>
    simp_all [PlanParams.serialize]

/-- The cache-key segment: the serialization in hex. -/
def PlanParams.key (p : PlanParams) : String := Id.run do
  let digits := "0123456789ABCDEF".toList.toArray
  let mut s := ""
  for byte in p.serialize do
    s := s.push (digits[byte.toNat / 16]?.getD '0')
    s := s.push (digits[byte.toNat % 16]?.getD '0')
  return s

/-- The refusal for a format no PDF filter decodes: the format's own name
opens it (`plan_refuses_named`). -/
def unembeddableMsg (f : Format) : String :=
  f.name ++ " images cannot be embedded in a PDF (no PDF filter decodes the format); \
re-export as PNG or JPEG"

def jpxRefusedMsg : String :=
  Format.jpx.name ++ " images are not passed through yet; re-export as PNG or JPEG"

/-- Is the source's profile dropped by this plan? Yes under the dropping
policy, and for an indexed image under either (an `/Indexed` base of
`/ICCBased` is the emission slice's). -/
def iccDropped (p : PlanParams) (s : Source) (space : Space) : Bool :=
  s.icc.size != 0 && (p.iccPolicy matches .dropWithDiag || space matches .indexed)

/-- The ledger every successful plan carries: each `Source` fact this
slice's plans do not carry, named once. -/
def lossesOf (p : PlanParams) (s : Source) (space : Space) : Array PlanLoss :=
  (if iccDropped p s space then #[.iccDropped] else #[]) ++
    (if s.orientation != 1 then #[.orientationDropped] else #[])

/-- The profile as `/FlateDecode` bytes: an iCCP payload is zlib already, a
JPEG's concatenated segments deflate here. -/
def iccZlib (s : Source) : ByteArray :=
  if s.iccIsZlib then s.icc else Flate.deflate s.icc

/-- The colour space a plan declares for `space`, the profile carried only
when the policy says so and the base is a device space. -/
def colorOf (p : PlanParams) (s : Source) (space : Space) : ColorSpaceDecl :=
  match space, iccDropped p s space || s.icc.size == 0 with
  | .indexed, _ => .indexed s.palette
  | .gray, true => .gray
  | .rgb, true => .rgb
  | .gray, false => .iccBased 1 (iccZlib s)
  | .rgb, false => .iccBased 3 (iccZlib s)

/-- The PNG arm: pass-through for colour types 0/2/3 (`plan_passthrough_exact`),
the alpha split for 4/6, and the named refusals — interlace, a 16-bit
alpha, a depth over the declared limit, a colour key the readers drop, a
soft mask the declaration forbids. Spelled as matches, not a `do` block, so
each theorem is a case split. -/
def planPng (p : PlanParams) (s : Source) : Except String Plan :=
  if s.interlace then .error "interlaced (Adam7) PNG is not supported; re-export without interlacing"
  else match pngSpace s.colorType with
  | none => .error s!"corrupt PNG: colour type {s.colorType}"
  | some (space, none) =>
    if p.maxBpc < s.bitDepth then
      .error s!"PNG at {s.bitDepth} bits per sample is deeper than the declared output allows \
({p.maxBpc}); re-export at a lower depth"
    else match (match s.trns with
        | none => .ok #[]
        | some tr => colorKeyRanges space s.bitDepth tr s.palette : Except String (Array Nat)) with
    | .error e => .error e
    | .ok key =>
      -- A 16-bit colour key is exact by the spec (`colorKeyRanges_rgb_exact`)
      -- and ignored by two of the four target readers, measured: Poppler
      -- and PDFium reduce the samples to 8 bits and compare the key
      -- unscaled, so the keyed pixels paint. Ghostscript and pdf.js honour
      -- it. A mask half the readers drop is the silent loss moved into the
      -- reader, so it is refused until the reader matrix says otherwise or
      -- the soft-mask arm carries it as an 8-bit `/SMask`.
      if s.bitDepth == 16 && !key.isEmpty then
        .error "PNG with a 16-bit colour key (tRNS) is not shown transparent by common PDF \
readers; re-export at 8 bits or with a full alpha channel"
      else .ok { pxW := s.pxW, pxH := s.pxH, dpiX := s.dpiX, dpiY := s.dpiY,
                 bitDepth := s.bitDepth, color := colorOf p s space,
                 filter := .flatePredictor, data := s.payload,
                 alpha := if key.isEmpty then .opaque else .colorKey key,
                 recoded := false, losses := lossesOf p s space,
                 orientation := s.orientation }
  | some (space, some channels) =>
    if s.bitDepth != 8 then
      .error s!"PNG with a {s.bitDepth}-bit alpha channel is not supported; \
re-export at 8 bits or flatten it"
    else if !p.softMaskPermitted then
      .error "PNG with an alpha channel needs a soft mask, which the declared output forbids; \
flatten it onto a background and re-export"
    else
      -- The samples cannot pass through as one stream: inflate against the
      -- size the geometry declares, then deinterleave the filtered residuals
      -- into the colour plane and the alpha plane — each row's own filter
      -- kept, no pixel ever reconstructed (`splitPredictedAlpha_exact`) —
      -- and deflate each, so the embedded object costs on the order of what
      -- the source cost, never what the raw samples weigh.
      let rowBytes := s.pxW * channels
      match Flate.inflate s.payload (s.pxH * (1 + rowBytes)) with
      | .error e => .error e
      | .ok raw =>
        if raw.size != s.pxH * (1 + rowBytes) then
          .error "corrupt PNG: sample data does not match the declared size"
        else
          let planes := splitPredictedAlpha raw s.pxH s.pxW channels
          .ok { pxW := s.pxW, pxH := s.pxH, dpiX := s.dpiX, dpiY := s.dpiY, bitDepth := 8,
                color := colorOf p s space, filter := .flatePredictor,
                data := Flate.deflate planes.1, alpha := .soft (Flate.deflate planes.2) 8,
                recoded := true, losses := lossesOf p s space, orientation := s.orientation }

/-- The JPEG arm: the whole file as `/DCTDecode`, one or three components
at 8 bits; CMYK and other precisions refused by name. -/
def planJpeg (p : PlanParams) (s : Source) : Except String Plan :=
  if s.bitDepth != 8 then
    .error s!"JPEG sample precision {s.bitDepth} is not supported (8 expected)"
  else match s.colorType with
  | 1 => .ok { pxW := s.pxW, pxH := s.pxH, dpiX := s.dpiX, dpiY := s.dpiY, bitDepth := 8,
               color := colorOf p s .gray, filter := .dct, data := s.payload,
               losses := lossesOf p s .gray, orientation := s.orientation }
  | 3 => .ok { pxW := s.pxW, pxH := s.pxH, dpiX := s.dpiX, dpiY := s.dpiY, bitDepth := 8,
               color := colorOf p s .rgb, filter := .dct, data := s.payload,
               losses := lossesOf p s .rgb, orientation := s.orientation }
  | 4 => .error "four-component (CMYK) JPEG is not supported; re-export as RGB"
  | n => .error s!"corrupt JPEG: {n} components"

/-- The embedding decision, a pure match over the source's format. -/
def plan (p : PlanParams) (s : Source) : Except String Plan :=
  match s.format with
  | .png => planPng p s
  | .jpeg => planJpeg p s
  | .pdf => .ok { pxW := s.pxW, pxH := s.pxH, form := s.form, losses := lossesOf p s .rgb,
                  orientation := s.orientation }
  | .webp => .error (unembeddableMsg .webp)
  | .avif => .error (unembeddableMsg .avif)
  | .jxl => .error (unembeddableMsg .jxl)
  | .jpx => .error jpxRefusedMsg

/-- Does planning this source do real work — inflate, split, recompress?
True exactly for the PNG colour types with an alpha channel (4 and 6): what
the driver's image cache keys on, decided from the header alone and agreeing
with the planner on every plan that succeeds (`recodes_iff`). -/
def Plan.recodes (_p : PlanParams) (s : Source) : Bool :=
  match s.format, pngSpace s.colorType with
  | .png, some (_, some _) => true
  | _, _ => false

/-- Decode any embeddable asset under the default parameters: today's one
call for every consumer. -/
def decode (b : ByteArray) : Except String Plan :=
  probe b >>= plan PlanParams.default

/-- **Pass-through is verbatim.** A plan for a PNG of colour type 0, 2, or 3
embeds the source's IDAT bytes as they stand and recodes nothing — for
every parameter record and every source the planner accepts. -/
theorem plan_passthrough_exact (p : PlanParams) (s : Source) (pl : Plan)
    (hf : s.format = .png) (hct : s.colorType = 0 ∨ s.colorType = 2 ∨ s.colorType = 3)
    (h : plan p s = .ok pl) : pl.data = s.payload ∧ pl.recoded = false := by
  simp only [plan, hf, planPng] at h
  split at h
  · exact absurd h (by simp)
  · have hsp : ∃ space, pngSpace s.colorType = some (space, none) := by
      rcases hct with h0 | h2 | h3
      · exact ⟨.gray, by rw [h0]; rfl⟩
      · exact ⟨.rgb, by rw [h2]; rfl⟩
      · exact ⟨.indexed, by rw [h3]; rfl⟩
    obtain ⟨space, hspace⟩ := hsp
    rw [hspace] at h
    simp only at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- `.iccDropped` sits in the ledger whenever the policy drops. -/
theorem mem_lossesOf_icc (p : PlanParams) (s : Source) (space : Space)
    (hp : p.iccPolicy = .dropWithDiag) (hi : s.icc.size ≠ 0) :
    PlanLoss.iccDropped ∈ lossesOf p s space := by
  have hd : iccDropped p s space = true := by
    simp [iccDropped, hp, hi]
  simp [lossesOf, hd]

/-- `.orientationDropped` sits in the ledger whenever the tag is not 1. -/
theorem mem_lossesOf_orientation (p : PlanParams) (s : Source) (space : Space)
    (ho : s.orientation ≠ 1) :
    PlanLoss.orientationDropped ∈ lossesOf p s space := by
  simp [lossesOf, ho]

/-- Under the dropping policy no plan's colour carries a profile. -/
theorem colorOf_dropWithDiag (p : PlanParams) (s : Source) (space : Space)
    (hp : p.iccPolicy = .dropWithDiag) (n : Nat) (prof : ByteArray) :
    colorOf p s space ≠ .iccBased n prof := by
  have hd : iccDropped p s space = true ∨ s.icc.size = 0 := by
    by_cases hi : s.icc.size = 0
    · exact .inr hi
    · exact .inl (by simp [iccDropped, hp, hi])
  unfold colorOf
  rcases hd with hd | hd <;> cases space <;> simp [hd]

/-- **No fact is dropped wordlessly.** Every plan the planner accepts
carries in `losses` each `Source` fact this slice does not embed: an
embedded profile under the dropping policy (and the plan's colour is then
a device space — the profile went nowhere else), and an orientation other
than 1. The driver maps each entry to its diagnostic (W0603, W0604). -/
theorem plan_losses_accounts (p : PlanParams) (s : Source) (pl : Plan)
    (h : plan p s = .ok pl) :
    (p.iccPolicy = .dropWithDiag → s.icc.size ≠ 0 →
      PlanLoss.iccDropped ∈ pl.losses ∧ ∀ n prof, pl.color ≠ .iccBased n prof) ∧
    (s.orientation ≠ 1 → PlanLoss.orientationDropped ∈ pl.losses) := by
  -- Every accepting arm writes `losses := lossesOf p s space` and
  -- `color := colorOf p s space` (or a device space), so the two ledger
  -- lemmas close each.
  have arm : ∀ space, pl.losses = lossesOf p s space →
      (∀ n prof, pl.color ≠ .iccBased n prof ∨ pl.color = colorOf p s space) →
      (p.iccPolicy = .dropWithDiag → s.icc.size ≠ 0 →
        PlanLoss.iccDropped ∈ pl.losses ∧ ∀ n prof, pl.color ≠ .iccBased n prof) ∧
      (s.orientation ≠ 1 → PlanLoss.orientationDropped ∈ pl.losses) := by
    intro space hl hc
    refine ⟨fun hp hi => ⟨hl ▸ mem_lossesOf_icc p s space hp hi, fun n prof => ?_⟩,
      fun ho => hl ▸ mem_lossesOf_orientation p s space ho⟩
    rcases hc n prof with hne | heq
    · exact hne
    · rw [heq]; exact colorOf_dropWithDiag p s space hp n prof
  unfold plan at h
  split at h
  · -- PNG
    unfold planPng at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    · next space _ =>
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      simp only [Except.ok.injEq] at h
      subst h
      exact arm space rfl (fun _ _ => .inr rfl)
    · next space _ _ =>
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      simp only at h
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      simp only [Except.ok.injEq] at h
      subst h
      exact arm space rfl (fun _ _ => .inr rfl)
  · -- JPEG
    unfold planJpeg at h
    split at h
    · exact absurd h (by simp)
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact arm .gray rfl (fun _ _ => .inr rfl)
    · simp only [Except.ok.injEq] at h
      subst h
      exact arm .rgb rfl (fun _ _ => .inr rfl)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- PDF
    simp only [Except.ok.injEq] at h
    subst h
    exact arm .rgb rfl (fun _ _ => .inl (by simp))
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The cache gate is the planner's decision.** On every plan the planner
accepts, `recoded` and the header-only `Plan.recodes` agree — the two read
the one colour-type table. -/
theorem recodes_iff (p : PlanParams) (s : Source) (pl : Plan) (h : plan p s = .ok pl) :
    pl.recoded = true ↔ Plan.recodes p s = true := by
  unfold plan at h
  unfold Plan.recodes
  split at h
  · next hf =>
    unfold planPng at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    · next space hsp =>
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      simp only [Except.ok.injEq] at h
      subst h
      simp [hf, hsp]
    · next space channels hsp =>
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      simp only at h
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      simp only [Except.ok.injEq] at h
      subst h
      simp [hf, hsp]
  · next hf =>
    unfold planJpeg at h
    split at h
    · exact absurd h (by simp)
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      simp [hf]
    · simp only [Except.ok.injEq] at h
      subst h
      simp [hf]
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · next hf =>
    simp only [Except.ok.injEq] at h
    subst h
    simp [hf]
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **A refusal names the format.** A source whose signature said WebP,
AVIF, or JPEG XL is refused, and the refusal opens with the format's own
name — stated over `Format.name`, the one constant the message reads. -/
theorem plan_refuses_named (p : PlanParams) (s : Source)
    (hf : s.format = .webp ∨ s.format = .avif ∨ s.format = .jxl) :
    ∃ rest, plan p s = .error (s.format.name ++ rest) := by
  rcases hf with hf | hf | hf <;> exact ⟨_, by unfold plan; rw [hf]; rfl⟩

/-! ## The driver's image cache: serialization

A plan as bytes: the value the driver files under the source's content key
and the parameters' key, so the expensive plan (inflate, split, deflate)
runs once per content and parameters. Only raster fields ride — a form
XObject never enters the cache; its plan is cheap and its `wf` witness
cannot be serialized. Transparency is `decodeBin_encodeBin_id` (staged in
`Obligations/`, exercised in `lake test`): a cache hit *is* the
recomputation's value, keeping the artifact a function of the document
and the font environment. The magic carries a format version: a change
here orphans old entries rather than misreading them. -/

/-- `LTIMG3`, the magic-and-format-version the decoder checks: version 3 is
the typed plan (three tag bytes for the three sums, the ledger, the
orientation), so every `LTIMG1` and `LTIMG2` entry is a miss. -/
private def binMagic : List Nat := [76, 84, 73, 77, 71, 51]

private def colorTag : ColorSpaceDecl → UInt8
  | .gray => 0
  | .rgb => 1
  | .indexed _ => 2
  | .iccBased _ _ => 3

private def filterTag : FilterDecl → UInt8
  | .flatePredictor => 0
  | .dct => 1

private def alphaTag : Alpha → UInt8
  | .opaque => 0
  | .colorKey _ => 1
  | .soft _ _ => 2

private def lossTag : PlanLoss → UInt8
  | .iccDropped => 0
  | .orientationDropped => 1

/-- The fixed header's length: magic, four tag bytes, fourteen u32 fields. -/
private def binHeader : Nat := 6 + 4 + 4 * 14

/-- Serialize a raster `Plan` (`form` is dropped; the cache never holds
one — `Plan.recodes` gates what is cached). Layout: magic; the colour,
filter, alpha tags and the recoded flag; u32s for the geometry (width,
height, two densities, bit depth, orientation), then the variable parts'
sizes (profile components, palette, profile, key count, soft-mask depth,
plane, data, losses); then the key values as u32s, the loss tags, and the
palette, profile, plane and data bytes. -/
def encodeBin (i : Plan) : ByteArray := Id.run do
  let (palette, iccN, profile) := match i.color with
    | .gray => (ByteArray.empty, 0, ByteArray.empty)
    | .rgb => (ByteArray.empty, 0, ByteArray.empty)
    | .indexed pal => (pal, 0, ByteArray.empty)
    | .iccBased n prof => (ByteArray.empty, n, prof)
  let (keys, softBpc, plane) := match i.alpha with
    | .opaque => (#[], 0, ByteArray.empty)
    | .colorKey ks => (ks, 0, ByteArray.empty)
    | .soft pl bpc => (#[], bpc, pl)
  let mut out := ByteArray.emptyWithCapacity
    (binHeader + 4 * keys.size + i.losses.size + palette.size + profile.size + plane.size +
      i.data.size)
  for v in binMagic do
    out := out.push (UInt8.ofNat v)
  out := out.push (colorTag i.color)
  out := out.push (filterTag i.filter)
  out := out.push (alphaTag i.alpha)
  out := out.push (if i.recoded then 1 else 0)
  out := Flate.pushBe32 out i.pxW
  out := Flate.pushBe32 out i.pxH
  out := Flate.pushBe32 out i.dpiX
  out := Flate.pushBe32 out i.dpiY
  out := Flate.pushBe32 out i.bitDepth
  out := Flate.pushBe32 out i.orientation
  out := Flate.pushBe32 out iccN
  out := Flate.pushBe32 out palette.size
  out := Flate.pushBe32 out profile.size
  out := Flate.pushBe32 out keys.size
  out := Flate.pushBe32 out softBpc
  out := Flate.pushBe32 out plane.size
  out := Flate.pushBe32 out i.data.size
  out := Flate.pushBe32 out i.losses.size
  for v in keys do
    out := Flate.pushBe32 out v
  for l in i.losses do
    out := out.push (lossTag l)
  return out ++ palette ++ profile ++ plane ++ i.data

/-- Read `encodeBin`'s bytes back; `none` for anything else — a foreign,
truncated, or older-format file is a cache miss, never a wrong image. -/
def decodeBin (b : ByteArray) : Option Plan := do
  guard (sliceEq b 0 binMagic)
  let cTag ← u8? b 6
  let filter ← match ← u8? b 7 with
    | 0 => some FilterDecl.flatePredictor
    | 1 => some FilterDecl.dct
    | _ => none
  let aTag ← u8? b 8
  let rc ← u8? b 9
  let pxW ← u32be? b 10
  let pxH ← u32be? b 14
  let dpiX ← u32be? b 18
  let dpiY ← u32be? b 22
  let bitDepth ← u32be? b 26
  let orientation ← u32be? b 30
  let iccN ← u32be? b 34
  let pLen ← u32be? b 38
  let prLen ← u32be? b 42
  let kLen ← u32be? b 46
  let softBpc ← u32be? b 50
  let plLen ← u32be? b 54
  let dLen ← u32be? b 58
  let lLen ← u32be? b 62
  -- The size check first: it bounds the loops below by the file.
  guard (b.size == binHeader + 4 * kLen + lLen + pLen + prLen + plLen + dLen)
  let mut keys : Array Nat := Array.emptyWithCapacity kLen
  for j in [0:kLen] do
    keys := keys.push (← u32be? b (binHeader + 4 * j))
  let lossBase := binHeader + 4 * kLen
  let mut losses : Array PlanLoss := Array.emptyWithCapacity lLen
  for j in [0:lLen] do
    losses := losses.push (← match ← u8? b (lossBase + j) with
      | 0 => some PlanLoss.iccDropped
      | 1 => some PlanLoss.orientationDropped
      | _ => none)
  let base := lossBase + lLen
  let palette := b.extract base (base + pLen)
  let profile := b.extract (base + pLen) (base + pLen + prLen)
  let plane := b.extract (base + pLen + prLen) (base + pLen + prLen + plLen)
  let data := b.extract (base + pLen + prLen + plLen) (base + pLen + prLen + plLen + dLen)
  let color ← match cTag with
    | 0 => some ColorSpaceDecl.gray
    | 1 => some ColorSpaceDecl.rgb
    | 2 => some (ColorSpaceDecl.indexed palette)
    | 3 => some (ColorSpaceDecl.iccBased iccN profile)
    | _ => none
  let alpha ← match aTag with
    | 0 => some Alpha.opaque
    | 1 => some (Alpha.colorKey keys)
    | 2 => some (Alpha.soft plane softBpc)
    | _ => none
  return { pxW, pxH, dpiX, dpiY, bitDepth, color, filter, data, alpha
           recoded := rc == 1, losses, orientation }


/-! ## The store: effects as data

An image requests a source and a page (`Ir.imageRequests` lists them);
the CLI driver reads and decodes each,
and layout and the backends consume this value. An entry whose `info` is
`none` did not load — the driver has already said why — and every consumer
places its placeholder box instead. -/

/-- Everything that can change which image reaches a page. Sizing is local
to the include and does not change the loaded asset. -/
structure Request where
  src : String
  page : PdfRead.PageSelection := .first
  /-- An animated include may use its source SVG for the browser while
  the selected PDF page supplies the static print face. -/
  animated : Bool := false
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

/-- The animate manual §6.1 fixes the animation canvas from its first
frame, independently of the poster. The selected plan still supplies the
ink; both backends read the separate canvas when sizing the include. -/
def decodeRequest (params : PlanParams) (bytes : ByteArray) (req : Request) :
    Except String (Plan × Option (Dim.Sp × Dim.Sp)) := do
  let selected ← probePage bytes req.page >>= plan params
  let canvas ← if req.animated then do
      let first ← if req.page == .first then pure selected
        else probe bytes >>= plan params
      pure (some (first.width, first.height))
    else pure none
  return (selected, canvas)

structure Loaded extends Request where
  /-- The relative path the driver resolved, when it differs from `src`: a
  bare graphicx name (`figures/plot`) gains the extension the file on disk
  has, and an HTML link must name it. -/
  href : String := ""
  info : Option Plan := none
  /-- An animation's canvas comes from its first frame (animate §6.1),
  even when the selected poster has a different aspect ratio. -/
  canvasSize : Option (Dim.Sp × Dim.Sp) := none
  /-- A browser SVG supplied by the driver: original animation bytes or
  the selected PDF page converted to SVG. It is published as an image
  asset, never inserted into the document's HTML tree. -/
  webSvg : Option ByteArray := none
  /-- A static browser face of the selected animation poster. HTML uses
  it for print and reduced motion, while `webSvg` carries the animation. -/
  posterSvg : Option ByteArray := none
  /-- A mandatory browser-face conversion failed. Keep the native plan,
  but publish a named placeholder rather than the uncooked source. -/
  webError : Option String := none
  /-- The exact bytes the driver read for this source (`fetchImage`), kept
  so the browser-face conversion uses them without rereading the file. -/
  source : Option ByteArray := none
  /-- The exact bytes of an animation's companion SVG, read once beside the
  PDF, so preserving movement never rereads a second file. -/
  companion : Option ByteArray := none
  deriving Inhabited

/-- The captured face the browser receives; naming and publication read
these same bytes, even if the source file changes during the build. -/
def Loaded.browserBytes (en : Loaded) : Option ByteArray :=
  en.webSvg.orElse fun _ => en.source

/-- One intrinsic size for both backends: a successfully loaded image's
animation canvas, or its own geometry for an ordinary include. -/
def Loaded.size? (en : Loaded) : Option (Dim.Sp × Dim.Sp) :=
  en.info.map fun inf => en.canvasSize.getD (inf.width, inf.height)

/-- The intrinsic box both backends read keeps a declared animation canvas
independently of the selected poster's geometry. -/
theorem Loaded.size?_exact (en : Loaded) (inf : Plan) (h : en.info = some inf) :
    en.size? = some (en.canvasSize.getD (inf.width, inf.height)) := by
  simp [Loaded.size?, h]

/-- Extension recognition for the browser image format. The CLI still
validates its print face through the converter and native PDF reader. -/
def isSvg (src : String) : Bool := src.toLower.endsWith ".svg"

/-- graphicx resolves an extensionless name against its extension list; the
same convention here, over the formats that embed — `.pdf` first past the
name as written, graphicx's own order under pdfTeX. -/
def sourceCandidates (src : String) : List String :=
  [src, src ++ ".pdf", src ++ ".png", src ++ ".jpg", src ++ ".jpeg",
   src ++ ".PDF", src ++ ".PNG", src ++ ".JPG", src ++ ".JPEG", src ++ ".svg", src ++ ".SVG"]

structure Store where
  entries : Array Loaded := #[]
  deriving Inhabited

def Store.findRequest? (s : Store) (req : Request) : Option Nat :=
  s.entries.findIdx? (·.toRequest == req)

def Store.find? (s : Store) (src : String) : Option Nat :=
  s.findRequest? { src }

def Store.get? (s : Store) (i : Nat) : Option Loaded :=
  s.entries[i]?

/-- The decoded image behind a source, when the driver loaded one: the one
resolving question a consumer asks of the store — `none` is the placeholder
box, whatever the reason (`Ir.pending` counts exactly these). -/
def Store.infoRequest? (s : Store) (req : Request) : Option Plan :=
  (s.entries.find? (·.toRequest == req)).bind (·.info)

def Store.info? (s : Store) (src : String) : Option Plan :=
  s.infoRequest? { src }

/-! ## Fulfilment: the decision half of the image effect

The driver reads files; deciding what each read means — an entry with a
payload, or a placeholder box with the diagnostic that names it — is a
pure function here, so the naming is a theorem (`fulfil_named`) and the
store's coverage another (`fulfil_covers`), not a convention of the
driver's loop. -/

/-- W0601: the image file exists but reading it failed. -/
def imageUnreadable (src err : String) : Diag :=
  Diag.of .W0601 s!"cannot read image '{src}': {err}; a placeholder box holds its place"
    (subject := some src)

/-- W0601: no file answers the image source. -/
def imageMissing (src looked : String) : Diag :=
  Diag.of .W0601 s!"image file not found: '{src}'; a placeholder box holds its place"
    (help := s!"looked at: {looked}, also with .pdf/.png/.jpg/.jpeg/.svg added")
    (subject := some src)

/-- W0602: the image bytes are not a format the engine embeds. -/
def imageUndecodable (src err : String) : Diag :=
  Diag.of .W0602 s!"cannot use image '{src}': {err}; a placeholder box holds its place"
    (help := "PNG, JPEG, and PDF embed natively: re-export the image as one")
    (subject := some src)

/-- W0603: the source carries a colour profile the plan did not. -/
def imageIccDropped (src : String) : Diag :=
  Diag.of .W0603
    s!"image '{src}' carries an embedded colour profile; the page reads its samples as device colour"
    (help := "re-export the image without the profile, or accept the device reading with \
\\allow{W0603}")
    (subject := some src)

/-- W0604: the source carries an orientation tag the plan did not apply. -/
def imageOrientationDropped (src : String) (orientation : Nat) : Diag :=
  Diag.of .W0604
    s!"image '{src}' carries orientation tag {orientation}; the page shows the stored orientation"
    (help := "rotate the pixels and re-export with orientation tag 1, or accept it with \
\\allow{W0604}")
    (subject := some src)

/-- The diagnostic one ledger entry names, for the plan that carries it. -/
def lossDiag (src : String) (pl : Plan) : PlanLoss → Diag
  | .iccDropped => imageIccDropped src
  | .orientationDropped => imageOrientationDropped src pl.orientation

/-- Every diagnostic a loaded plan's ledger names, in ledger order. -/
def lossDiags (src : String) (pl : Plan) : Array Diag :=
  pl.losses.map (lossDiag src pl)

/-- What the driver found for one image source, before the pure decision
names it: a file (or a boundary picture's drawn PDF) decoded — through the
driver's content cache, which equals the pure decode
(`decodeBin_encodeBin_id`) — with the relative path an HTML link needs; no
file; a file that would not read; or a boundary picture nothing drew,
carrying the boundary's own diagnostic (E0382, W0379), whose subject
`fulfil` sets so the refusal names the picture whatever words it chose. -/
inductive Fetch where
  | decoded (href : String) (res : Except String Plan) (webSvg : Option ByteArray)
      (canvasSize : Option (Dim.Sp × Dim.Sp)) (source : Option ByteArray)
      (companion : Option ByteArray)
  | missing (looked : String)
  | unreadable (err : String)
  | refused (why : Diag)

/-- One source's decision: its store entry, and the diagnostic naming the
gap when there is one. Every arm that leaves `info := none` also returns
a diagnostic whose subject is the source — `fulfilOne_named`. -/
def fulfilOne (req : Request) : Fetch → Loaded × Option Diag
  | .decoded href (.ok info) webSvg canvasSize source companion =>
    ({ toRequest := req, href, info := some info, webSvg, canvasSize, source, companion }, none)
  | .decoded href (.error e) _ _ _ _ =>
    ({ toRequest := req, href }, some (imageUndecodable req.src e))
  | .missing looked => ({ toRequest := req }, some (imageMissing req.src looked))
  | .unreadable err => ({ toRequest := req }, some (imageUnreadable req.src err))
  | .refused why => ({ toRequest := req }, some { why with subject := some req.src })

def fulfilList (entries : Array Loaded) (diags : Array Diag) :
    List (Request × Fetch) → Store × Array Diag
  | [] => ({ entries }, diags)
  | (src, f) :: rest =>
    fulfilList (entries.push (fulfilOne src f).1)
      (match (fulfilOne src f).2 with | some d => diags.push d | none => diags) rest

/-- The store and the diagnostics one run's reads decide, in the order the
document requested them (`Ir.imageRequests`, the driver's loop). -/
def fulfilRequests (fetched : Array (Request × Fetch)) : Store × Array Diag :=
  fulfilList #[] #[] fetched.toList

/-- The default first-page request, for callers that only carry paths. -/
def fulfil (fetched : Array (String × Fetch)) : Store × Array Diag :=
  fulfilRequests (fetched.map fun (src, f) => ({ src }, f))

/-- A gap is named: whenever the decision leaves no payload, it also returns
a diagnostic whose subject is the source. -/
theorem fulfilOne_named (req : Request) (f : Fetch) (h : (fulfilOne req f).1.info = none) :
    ∃ d, (fulfilOne req f).2 = some d ∧ d.subject = some req.src := by
  cases f with
  | decoded href res webSvg canvasSize source companion =>
    cases res with
    | ok info => simp [fulfilOne] at h
    | error e => exact ⟨_, rfl, rfl⟩
  | missing looked => exact ⟨_, rfl, rfl⟩
  | unreadable err => exact ⟨_, rfl, rfl⟩
  | refused why => exact ⟨_, rfl, rfl⟩

/-- Every entry the decision writes is the fetched source's, in order. -/
theorem fulfilOne_request (req : Request) (f : Fetch) :
    (fulfilOne req f).1.toRequest = req := by
  cases f with
  | decoded href res webSvg canvasSize source companion => cases res <;> rfl
  | missing _ | unreadable _ | refused _ => rfl

theorem fulfilOne_src (req : Request) (f : Fetch) : (fulfilOne req f).1.src = req.src :=
  congrArg Request.src (fulfilOne_request req f)

/-- **A decoded source's bytes reach its store entry unchanged.** When the
driver decodes a source, the entry the store carries holds exactly the
bytes `fetchImage` read — its `source` and animation `companion` — so the
browser-face conversion converts those bytes and never rereads the file.
Stated on the `.ok` arm, the only one that loads a plan and so the only one
a browser face is planned for; a failed decode carries no bytes and needs
none. -/
theorem fulfilOne_bytes (req : Request) (href : String) (info : Plan)
    (webSvg source companion : Option ByteArray) (canvasSize : Option (Dim.Sp × Dim.Sp)) :
    (fulfilOne req (.decoded href (.ok info) webSvg canvasSize source companion)).1.source = source ∧
    (fulfilOne req (.decoded href (.ok info) webSvg canvasSize source companion)).1.companion
      = companion := ⟨rfl, rfl⟩

private theorem fulfilList_named (entries : Array Loaded) (diags : Array Diag)
    (hacc : ∀ en ∈ entries, en.info = none → ∃ d ∈ diags, d.subject = some en.src) :
    ∀ (fs : List (Request × Fetch)) (en : Loaded),
      en ∈ (fulfilList entries diags fs).1.entries → en.info = none →
      ∃ d ∈ (fulfilList entries diags fs).2, d.subject = some en.src := by
  intro fs
  induction fs generalizing entries diags with
  | nil => intro en hmem hnone; exact hacc en hmem hnone
  | cons p rest ih =>
    intro en hmem hnone
    obtain ⟨src, f⟩ := p
    simp only [fulfilList] at hmem ⊢
    refine ih _ _ ?_ en hmem hnone
    intro en' hmem' hnone'
    rw [Array.mem_push] at hmem'
    rcases hmem' with hold | heq
    · obtain ⟨d, hd, hs⟩ := hacc en' hold hnone'
      refine ⟨d, ?_, hs⟩
      split <;> simp [hd]
    · subst heq
      obtain ⟨d, hd, hs⟩ := fulfilOne_named src f hnone'
      refine ⟨d, ?_, by rw [hs, fulfilOne_src]⟩
      rw [hd]
      simp

/-- **Every gap in the store is named.** An entry with no payload — the
placeholder box every consumer places — has a diagnostic in the same
run's output whose subject is its source. The image half of the
resolution gate (`pending_named`). -/
theorem fulfilRequests_named (fetched : Array (Request × Fetch)) :
    ∀ en ∈ (fulfilRequests fetched).1.entries, en.info = none →
      ∃ d ∈ (fulfilRequests fetched).2, d.subject = some en.src :=
  fulfilList_named #[] #[] (fun _ h => by simp at h) fetched.toList

theorem fulfil_named (fetched : Array (String × Fetch)) :
    ∀ en ∈ (fulfil fetched).1.entries, en.info = none →
      ∃ d ∈ (fulfil fetched).2, d.subject = some en.src :=
  fulfilRequests_named _

private theorem fulfilList_covers (entries : Array Loaded) (diags : Array Diag) :
    ∀ fs : List (Request × Fetch),
      ((fulfilList entries diags fs).1.entries.map (·.toRequest)).toList =
        (entries.map (·.toRequest)).toList ++ fs.map (·.1) := by
  intro fs
  induction fs generalizing entries diags with
  | nil => simp [fulfilList]
  | cons p rest ih =>
    obtain ⟨src, f⟩ := p
    simp only [fulfilList]
    rw [ih]
    simp [Array.toList_map, Array.toList_push, fulfilOne_request]

/-- **The store covers the request.** The entries are the fetched sources,
one each, in order: the driver fetches `Ir.imageRequests doc`, so every source
the document names has an entry to read. -/
theorem fulfilRequests_covers (fetched : Array (Request × Fetch)) :
    (fulfilRequests fetched).1.entries.map (·.toRequest) = fetched.map (·.1) := by
  rw [← Array.toList_inj, fulfilRequests, fulfilList_covers]
  simp [Array.toList_map]

theorem fulfil_covers (fetched : Array (String × Fetch)) :
    (fulfil fetched).1.entries.map (·.src) = fetched.map (·.1) := by
  have h := congrArg (·.map Request.src)
    (fulfilRequests_covers (fetched.map fun (src, f) => ({ src }, f)))
  simpa [fulfil, Array.map_map, Function.comp_def] using h

/-! ## Sizing

The request a document states (`width = 0.8\textwidth`, `height = 3cm`,
`scale = 0.5`, `keepaspectratio`) resolves against the intrinsic physical
size. The semantics are graphicx's: one declared dimension scales the other
to the intrinsic ratio; both declared set the box exactly, unless
`keepaspectratio` fits the image inside them; neither takes the intrinsic
size, times any `scale`. The theorems after the function are the contract:
declared size wins to the sp, and every derived dimension holds the
intrinsic ratio to within one sp of rounding. -/

/-- A requested dimension as the shared typed affine algebra. Local measure
names survive only as `Measure` constructors until the layout context is
known. -/
structure Len where
  value : Affine Measure := .lit {}
  deriving Repr, BEq, Inhabited

/-- An absolute requested dimension. -/
def Len.abs (sp : Sp) : Len := ⟨.lit { width := .ofSp sp }⟩

/-- A fraction of one local measure. -/
def Len.frac (measure : Measure) (permille : Int) : Len :=
  ⟨Affine.scaleQ permille 1000 (.ref measure)⟩

/-- Resolve with the local horizontal measure and text height supplied by
layout. Every horizontal source name denotes the containing box here, as a
minipage initializes them. -/
def Len.resolve (l : Len) (textW textH : Sp) : Sp :=
  l.value.resolveWidth (MeasureValues.horizontal textW textH)

/-- The sizing request from the source, unresolved. `scaleNum/scaleDen`
carry `scale = 0.6` exactly; 1/1 is unscaled. -/
structure SizeSpec where
  width : Option Len := none
  height : Option Len := none
  scaleNum : Int := 1
  scaleDen : Nat := 1
  keepAspect : Bool := false
  deriving Repr, BEq, Inhabited

/-- An include's local sizing plus the asset selection shared by both
backends. An animation's selected page is its static PDF poster. -/
structure Spec extends SizeSpec where
  page : PdfRead.PageSelection := .first
  animated : Bool := false
  deriving Repr, BEq, Inhabited

def Spec.request (spec : Spec) (src : String) : Request :=
  { src, page := spec.page, animated := spec.animated }

/-- The placed box, in sp. `iW`/`iH` are the intrinsic physical size. -/
def resolveSize (spec : SizeSpec) (iW iH : Sp) (textW textH : Sp) : Sp × Sp :=
  match spec.width, spec.height with
  | none, none =>
    (iW * spec.scaleNum / spec.scaleDen, iH * spec.scaleNum / spec.scaleDen)
  | some w, none =>
    let w := w.resolve textW textH
    (w, w * iH / iW)
  | none, some h =>
    let h := h.resolve textW textH
    (h * iW / iH, h)
  | some w, some h =>
    let w := w.resolve textW textH
    let h := h.resolve textW textH
    if spec.keepAspect then
      if w * iH ≤ h * iW then (w, w * iH / iW) else (h * iW / iH, h)
    else
      (w, h)

/-- Division against a positive divisor loses less than one unit: the fact
every aspect statement below reduces to. -/
private theorem ediv_within_one (a d : Int) (hd : 0 < d) :
    a / d * d ≤ a ∧ a < (a / d + 1) * d := by
  have h : a % d + d * (a / d) = a :=
    (((Int.ediv_emod_unique (a := a) (b := d) (q := a / d) (r := a % d) hd).mp
      ⟨rfl, rfl⟩)).1
  have h0 := Int.emod_nonneg a (by omega : d ≠ 0)
  have h1 := Int.emod_lt_of_pos a hd
  have hm : a / d * d = d * (a / d) := Int.mul_comm _ _
  have hs : (a / d + 1) * d = d * (a / d) + d := by
    rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  constructor
  · rw [hm]
    calc d * (a / d) ≤ a % d + d * (a / d) := Int.le_add_of_nonneg_left h0
      _ = a := h
  · rw [hs]
    calc a = a % d + d * (a / d) := h.symm
      _ < d + d * (a / d) := Int.add_lt_add_right h1 _
      _ = d * (a / d) + d := Int.add_comm _ _

/-- Declared size wins: with both dimensions given and no `keepaspectratio`,
the box is exactly the declared size. -/
theorem resolveSize_both_exact (w h : Len) (n : Int) (d : Nat) (iW iH textW textH : Sp) :
    resolveSize { width := some w, height := some h, scaleNum := n, scaleDen := d }
      iW iH textW textH = (w.resolve textW textH, h.resolve textW textH) := by
  simp [resolveSize]

/-- With nothing declared the box is the intrinsic physical size. -/
theorem resolveSize_intrinsic (ka : Bool) (iW iH textW textH : Sp) :
    resolveSize { keepAspect := ka } iW iH textW textH = (iW, iH) := by
  simp [resolveSize]

/-- With `width` alone, the width is exact and the height holds the
intrinsic ratio to within one sp: `out.2 / out.1 = iH / iW` up to the
division's unit of rounding, stated multiplicatively so it is exact. -/
theorem resolveSize_width_keeps_aspect (w : Len) (n : Int) (d : Nat) (ka : Bool)
    (iW iH textW textH : Sp) (hW : 0 < iW) :
    (resolveSize { width := some w, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).1 = w.resolve textW textH ∧
    (resolveSize { width := some w, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).2 * iW ≤ w.resolve textW textH * iH ∧
    w.resolve textW textH * iH <
      ((resolveSize { width := some w, scaleNum := n, scaleDen := d, keepAspect := ka }
        iW iH textW textH).2 + 1) * iW := by
  have h := ediv_within_one (w.resolve textW textH * iH) iW hW
  exact ⟨rfl, h.1, h.2⟩

/-- The mirror statement for `height` alone. -/
theorem resolveSize_height_keeps_aspect (h : Len) (n : Int) (d : Nat) (ka : Bool)
    (iW iH textW textH : Sp) (hH : 0 < iH) :
    (resolveSize { height := some h, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).2 = h.resolve textW textH ∧
    (resolveSize { height := some h, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).1 * iH ≤ h.resolve textW textH * iW ∧
    h.resolve textW textH * iW <
      ((resolveSize { height := some h, scaleNum := n, scaleDen := d, keepAspect := ka }
        iW iH textW textH).1 + 1) * iH := by
  have hh := ediv_within_one (h.resolve textW textH * iW) iH hH
  exact ⟨rfl, hh.1, hh.2⟩

/-- With both given and `keepaspectratio`, the box fits inside the declared
rectangle: the binding dimension is exact and the other never exceeds its
declaration. -/
theorem resolveSize_keepAspect_fits (w h : Len) (iW iH textW textH : Sp)
    (hW : 0 < iW) (hH : 0 < iH) :
    (resolveSize { width := some w, height := some h, keepAspect := true }
      iW iH textW textH).1 ≤ w.resolve textW textH ∧
    (resolveSize { width := some w, height := some h, keepAspect := true }
      iW iH textW textH).2 ≤ h.resolve textW textH := by
  have hred : resolveSize { width := some w, height := some h, keepAspect := true }
      iW iH textW textH =
      (if w.resolve textW textH * iH ≤ h.resolve textW textH * iW then
        (w.resolve textW textH, w.resolve textW textH * iH / iW)
      else (h.resolve textW textH * iW / iH, h.resolve textW textH)) := rfl
  rw [hred]
  split
  · next hc =>
    -- Width binds: (w·iH/iW)·iW ≤ w·iH ≤ h·iW, and dividing out the
    -- positive iW keeps the order.
    have h1 := (ediv_within_one (w.resolve textW textH * iH) iW hW).1
    exact ⟨Int.le_refl _, Int.le_of_mul_le_mul_right (Int.le_trans h1 hc) hW⟩
  · next hc =>
    -- Height binds: (h·iW/iH)·iH ≤ h·iW < w·iH, same argument against iH.
    have h1 := (ediv_within_one (h.resolve textW textH * iW) iH hH).1
    have hlt : h.resolve textW textH * iW < w.resolve textW textH * iH :=
      Int.not_le.mp hc
    exact ⟨Int.le_of_mul_le_mul_right (Int.le_trans h1 (Int.le_of_lt hlt)) hH,
      Int.le_refl _⟩

end LeanTex.Core.Image
