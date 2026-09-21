import LeanTex.Core.Diag
import LeanTex.Core.Dim
import LeanTex.Core.Flate
import LeanTex.Core.PdfRead

namespace LeanTex.Core.Image

open LeanTex.Core.Dim

/-! # External images

Pure decoders for the two formats a first slice needs: PNG and JPEG. Reading
the file is the driver's effect; everything here is a total function over a
`ByteArray` — a truncated or foreign file yields an error value, never a
crash and never a wrong number. The decoders read only what placement and
embedding need: the pixel dimensions, the declared physical density, and
enough of the header to hand the compressed data to the PDF writer
(`/FlateDecode` with PNG prediction, `/DCTDecode`). Opaque and indexed PNGs
pass their IDAT through untouched; a PNG with an alpha channel inflates
once and deinterleaves its filtered rows into a colour stream and a
soft-mask stream — never its pixels — since a PDF image holds exactly its
colour space's samples and carries opacity as a separate `/SMask` image.
A `tRNS` chunk on the pass-through types becomes the exact colour-key
`/Mask`, or a refusal where no single range can carry it.
Interlaced and 16-bit-alpha PNGs are refused with a reason the driver can
show. -/

/-- Both specs can leave the physical size undeclared — PNG's pHYs is
optional and "the physical size of each pixel is unknown" without it
(ISO/IEC 15948 §11.3.5.3), JFIF density unit 0 declares aspect ratio only
(ISO/IEC 10918-5 §5). The engine then adopts 72 pixels per inch, pdfTeX's
`\pdfimageresolution` default, so one pixel is one point. -/
def defaultDpi : Nat := 72

inductive Format where
  | png
  | jpeg
  /-- Page 1 of a PDF, embedded as a form XObject: vector stays vector. -/
  | pdf
  deriving Repr, BEq, Inhabited

/-- The colour interpretation the PDF image dictionary needs. -/
inductive Space where
  | gray
  | rgb
  /-- PNG colour type 3: samples index the PLTE palette. -/
  | indexed
  deriving Repr, BEq, Inhabited

/-- What placement and embedding read from a decoded file. `data` is the
stream the PDF writer embeds as-is: a PNG's concatenated IDAT zlib stream
(legal as `/FlateDecode` with the PNG predictor declared, ISO 32000-2
§7.4.4.4), a JPEG's whole file (`/DCTDecode`). -/
structure Info where
  format : Format
  pxW : Nat
  pxH : Nat
  dpiX : Nat := defaultDpi
  dpiY : Nat := defaultDpi
  bitDepth : Nat := 8
  space : Space := .rgb
  /-- PNG colour type 3: the PLTE payload, RGB triples. -/
  palette : ByteArray := ByteArray.empty
  data : ByteArray := ByteArray.empty
  /-- PNG only: `data` is PNG-predicted zlib — a pass-through IDAT
  stream, or the colour plane deinterleaved from an alpha PNG's filtered
  rows and deflated again — and the PDF dictionary must declare the
  predictor. -/
  predictor : Bool := false
  /-- An alpha channel, as its own zlib-compressed 8-bit gray plane under
  the source rows' own filters: the PDF soft mask, Predictor 15 declared.
  Empty when the image is opaque. -/
  smask : ByteArray := ByteArray.empty
  /-- Colour-key transparency (ISO 32000-2 §8.9.6.4): the `/Mask` ranges,
  two per component in sample units at `bitDepth`, a pixel inside every
  range not painted — a PNG `tRNS` chunk mapped exactly (`colorKeyRanges`).
  Empty when no sample is keyed. -/
  colorKey : Array Nat := #[]
  /-- A PDF page read as a form XObject (`format == .pdf`): the box, the
  content, and the copied resource graph. The `wf` witness rides with it —
  `PdfRead.resources_closed` — so the writer never meets a dangling
  reference. -/
  form : Option { f : PdfRead.Form // f.wf } := none
  deriving Inhabited

/-- Samples per pixel, for `/DecodeParms /Colors`. -/
def Space.components : Space → Nat
  | .gray => 1
  | .rgb => 3
  | .indexed => 1

/-- Intrinsic physical width: pixels over density, in sp — and for a PDF
page, its box, exact to the sp (the `form_bbox_exact` half of the story:
the intrinsic size *is* the page box). -/
def Info.width (i : Info) : Sp :=
  match i.form with
  | some f => f.val.w
  | none => (i.pxW : Int) * 72 * spPerPt / max i.dpiX 1

def Info.height (i : Info) : Sp :=
  match i.form with
  | some f => f.val.h
  | none => (i.pxH : Int) * 72 * spPerPt / max i.dpiY 1

/-- At the default density one pixel is one point: the convention is not
just a comment, it is what `Info.width` computes. -/
theorem width_at_default_dpi (px : Nat) :
    Info.width { format := .png, pxW := px, pxH := px } = Dim.pt px := by
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

def decodePng (b : ByteArray) : Except String Info := do
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
  if interlace != 0 then
    throw "interlaced (Adam7) PNG is not supported; re-export without interlacing"
  -- `alpha` is the channel count of a type that must really decode.
  let (space, alpha) ← match colorType with
    | 0 => pure (Space.gray, none)
    | 2 => pure (Space.rgb, none)
    | 3 => pure (Space.indexed, none)
    | 4 => pure (Space.gray, some 2)
    | 6 => pure (Space.rgb, some 4)
    | t => throw s!"corrupt PNG: colour type {t}"
  unless [1, 2, 4, 8, 16].contains bitDepth do
    throw s!"corrupt PNG: bit depth {bitDepth}"
  if space == .rgb && alpha.isNone && bitDepth < 8 then
    throw s!"corrupt PNG: truecolour at bit depth {bitDepth}"
  if alpha.isSome && bitDepth != 8 then
    throw s!"PNG with a {bitDepth}-bit alpha channel is not supported; \
re-export at 8 bits or flatten it"
  -- Walk the chunks. `i` advances by at least 12 per step, so the loop over
  -- `b.size` iterations covers every well-formed file; a lying length that
  -- points past the end is caught by the bounds-checked reads.
  let mut dpiX := defaultDpi
  let mut dpiY := defaultDpi
  let mut palette := ByteArray.empty
  let mut trns : Option ByteArray := none
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
  match alpha with
  | none =>
    let colorKey ← match trns with
      | none => pure #[]
      | some tr => colorKeyRanges space bitDepth tr palette
    -- A 16-bit colour key is exact by the spec (`colorKeyRanges_rgb_exact`)
    -- and ignored by two of the four target readers, measured: Poppler
    -- and PDFium reduce the samples to 8 bits and compare the key
    -- unscaled, so the keyed pixels paint. Ghostscript and pdf.js honour
    -- it. A mask half the readers drop is the silent loss moved into the
    -- reader, so it is refused until the reader matrix says otherwise or
    -- the soft-mask arm carries it as an 8-bit `/SMask`.
    if bitDepth == 16 && !colorKey.isEmpty then
      throw "PNG with a 16-bit colour key (tRNS) is not shown transparent by common PDF \
readers; re-export at 8 bits or with a full alpha channel"
    return { format := .png, pxW, pxH, dpiX, dpiY, bitDepth, space, palette,
             data := idat, predictor := true, colorKey }
  | some channels =>
    -- The samples cannot pass through as one stream: inflate against the
    -- size the geometry declares, then deinterleave the filtered residuals
    -- into the colour plane and the alpha plane — each row's own filter
    -- kept, no pixel ever reconstructed (`splitPredictedAlpha_exact`) —
    -- and deflate each, so the embedded object costs on the order of what
    -- the source cost, never what the raw samples weigh.
    let rowBytes := pxW * channels
    let raw ← Flate.inflate idat (pxH * (1 + rowBytes))
    if raw.size != pxH * (1 + rowBytes) then
      throw "corrupt PNG: sample data does not match the declared size"
    let (color, alphaPlane) := splitPredictedAlpha raw pxH pxW channels
    return { format := .png, pxW, pxH, dpiX, dpiY, bitDepth := 8, space,
             data := Flate.deflate color
             predictor := true
             smask := Flate.deflate alphaPlane }

/-! ## JPEG

A marker stream: `FF xx`, most segments carrying a big-endian length that
includes its own two bytes. `SOFn` carries the dimensions (ISO/IEC 10918-1
§B.2.2), the JFIF `APP0` the density. The entropy-coded data after `SOS`
never contains a bare `FF xx` marker except via `FF 00` stuffing and the
restart markers, so the header walk stops there — the dimensions must have
appeared first for the file to be an image at all. -/

/-- Is this marker byte an SOFn frame header? DHT (C4), JPG (C8) and DAC
(CC) share the Cx block and are not. -/
private def isSof (m : Nat) : Bool :=
  0xC0 ≤ m && m ≤ 0xCF && m != 0xC4 && m != 0xC8 && m != 0xCC

def decodeJpeg (b : ByteArray) : Except String Info := do
  unless sliceEq b 0 [0xFF, 0xD8] do
    throw "not a JPEG file (no SOI marker)"
  let mut i := 2
  let mut dpiX := defaultDpi
  let mut dpiY := defaultDpi
  let mut dims : Option (Nat × Nat × Nat × Nat) := none
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
    i := j + 1 + len
  let some (pxW, pxH, precision, ncomp) := dims
    | throw "corrupt JPEG: no frame header (SOFn) before the scan"
  if pxW == 0 || pxH == 0 then
    throw "corrupt JPEG: zero width or height"
  unless precision == 8 do
    throw s!"JPEG sample precision {precision} is not supported (8 expected)"
  let space ← match ncomp with
    | 1 => pure Space.gray
    | 3 => pure Space.rgb
    | 4 => throw "four-component (CMYK) JPEG is not supported; re-export as RGB"
    | n => throw s!"corrupt JPEG: {n} components"
  return { format := .jpeg, pxW, pxH, dpiX, dpiY, bitDepth := 8, space,
           data := b }

/-- Decode any embeddable asset, told apart by signature: PNG, JPEG, or a
PDF whose page 1 embeds as a form XObject. -/
def decode (b : ByteArray) : Except String Info :=
  if sliceEq b 0 pngSig then decodePng b
  else if sliceEq b 0 [0xFF, 0xD8] then decodeJpeg b
  else if sliceEq b 0 [0x25, 0x50, 0x44, 0x46] then do
    let f ← PdfRead.readForm b
    -- The pixel fields are the box rounded to whole points: only the dump
    -- and the placeholder read them; placement reads the box exactly.
    return { format := .pdf
             pxW := (max 0 f.val.w / spPerPt).toNat
             pxH := (max 0 f.val.h / spPerPt).toNat
             form := some f }
  else .error "not a PNG, JPEG, or PDF file (unrecognised signature)"

/-- Does decoding these bytes do real work — inflate, unfilter, split,
recompress? True exactly for the PNG colour types with an alpha channel
(4 and 6, ISO/IEC 15948 §11.2.2): what the driver's image cache keys on,
since a pass-through decode is cheaper than any cache read. -/
def decodeRecodes (b : ByteArray) : Bool :=
  sliceEq b 0 pngSig && (u8? b 25 == some 4 || u8? b 25 == some 6)

/-! ## The driver's image cache: serialization

A decoded image object as bytes: the value the driver files under the
source's content key, so the expensive decode (inflate, unfilter, split,
deflate) runs once per content. Only raster fields ride — a form XObject
never enters the cache; its decode is cheap and its `wf` witness cannot
be serialized. Transparency is `decodeBin_encodeBin_id` (staged in
`Obligations/`, exercised in `lake test`): a cache hit *is* the
recomputation's value, keeping the artifact a function of the document
and the font environment. The magic carries a format version: a change
here orphans old entries rather than misreading them. -/

private def pushU32 (b : ByteArray) (v : Nat) : ByteArray :=
  ((((b.push (UInt8.ofNat (v / 16777216 % 256))).push
    (UInt8.ofNat (v / 65536 % 256))).push
    (UInt8.ofNat (v / 256 % 256))).push (UInt8.ofNat (v % 256)))

/-- `LTIMG2`, the magic-and-format-version the decoder checks: version 2
added the colour-key ranges, so every `LTIMG1` entry is a miss. -/
private def binMagic : List Nat := [76, 84, 73, 77, 71, 50]

/-- Serialize a raster `Info` (`form` is dropped; the cache never holds
one — `decodeRecodes` gates what is cached). Layout: magic, three tag
bytes, nine u32 fields (the last the colour-key count), the key values as
u32s, then the palette, data, and soft-mask bytes. -/
def encodeBin (i : Info) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity
    (45 + 4 * i.colorKey.size + i.palette.size + i.data.size + i.smask.size)
  for v in binMagic do
    out := out.push (UInt8.ofNat v)
  out := out.push (match i.format with | .png => 0 | .jpeg => 1 | .pdf => 2)
  out := out.push (match i.space with | .gray => 0 | .rgb => 1 | .indexed => 2)
  out := out.push (if i.predictor then 1 else 0)
  out := pushU32 out i.pxW
  out := pushU32 out i.pxH
  out := pushU32 out i.dpiX
  out := pushU32 out i.dpiY
  out := pushU32 out i.bitDepth
  out := pushU32 out i.palette.size
  out := pushU32 out i.data.size
  out := pushU32 out i.smask.size
  out := pushU32 out i.colorKey.size
  for v in i.colorKey do
    out := pushU32 out v
  return out ++ i.palette ++ i.data ++ i.smask

/-- Read `encodeBin`'s bytes back; `none` for anything else — a foreign,
truncated, or older-format file is a cache miss, never a wrong image. -/
def decodeBin (b : ByteArray) : Option Info := do
  guard (sliceEq b 0 binMagic)
  let format ← match ← u8? b 6 with
    | 0 => some Format.png
    | 1 => some Format.jpeg
    | _ => none
  let space ← match ← u8? b 7 with
    | 0 => some Space.gray
    | 1 => some Space.rgb
    | 2 => some Space.indexed
    | _ => none
  let pr ← u8? b 8
  let pxW ← u32be? b 9
  let pxH ← u32be? b 13
  let dpiX ← u32be? b 17
  let dpiY ← u32be? b 21
  let bitDepth ← u32be? b 25
  let pLen ← u32be? b 29
  let dLen ← u32be? b 33
  let sLen ← u32be? b 37
  let kLen ← u32be? b 41
  -- The size check first: it bounds the key loop below by the file.
  guard (b.size == 45 + 4 * kLen + pLen + dLen + sLen)
  let mut colorKey : Array Nat := Array.emptyWithCapacity kLen
  for j in [0:kLen] do
    colorKey := colorKey.push (← u32be? b (45 + 4 * j))
  let base := 45 + 4 * kLen
  return { format, pxW, pxH, dpiX, dpiY, bitDepth, space
           palette := b.extract base (base + pLen)
           data := b.extract (base + pLen) (base + pLen + dLen)
           predictor := pr == 1
           smask := b.extract (base + pLen + dLen) (base + pLen + dLen + sLen)
           colorKey }

/-! ## The store: effects as data

An image is a file, so the elaborated document carries only the path it
wrote (`Ir.imageRefs` lists them); the CLI driver reads and decodes each,
and layout and the backends consume this value. An entry whose `info` is
`none` did not load — the driver has already said why — and every consumer
places its placeholder box instead. -/

structure Loaded where
  src : String
  /-- The relative path the driver resolved, when it differs from `src`: a
  bare graphicx name (`figures/plot`) gains the extension the file on disk
  has, and an HTML link must name it. -/
  href : String := ""
  info : Option Info := none
  deriving Inhabited

/-- graphicx resolves an extensionless name against its extension list; the
same convention here, over the formats that embed — `.pdf` first past the
name as written, graphicx's own order under pdfTeX. -/
def sourceCandidates (src : String) : List String :=
  [src, src ++ ".pdf", src ++ ".png", src ++ ".jpg", src ++ ".jpeg",
   src ++ ".PDF", src ++ ".PNG", src ++ ".JPG", src ++ ".JPEG"]

structure Store where
  entries : Array Loaded := #[]
  deriving Inhabited

def Store.find? (s : Store) (src : String) : Option Nat :=
  s.entries.findIdx? (·.src == src)

def Store.get? (s : Store) (i : Nat) : Option Loaded :=
  s.entries[i]?

/-- The decoded image behind a source, when the driver loaded one: the one
resolving question a consumer asks of the store — `none` is the placeholder
box, whatever the reason (`Ir.pending` counts exactly these). -/
def Store.info? (s : Store) (src : String) : Option Info :=
  (s.entries.find? (·.src == src)).bind (·.info)

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
    (help := s!"looked at: {looked}, also with .pdf/.png/.jpg/.jpeg added")
    (subject := some src)

/-- W0602: the image bytes are not a format the engine embeds. -/
def imageUndecodable (src err : String) : Diag :=
  Diag.of .W0602 s!"cannot use image '{src}': {err}; a placeholder box holds its place"
    (help := "PNG, JPEG, and PDF embed natively: re-export the image as one")
    (subject := some src)

/-- What the driver found for one image source, before the pure decision
names it: a file (or a boundary picture's drawn PDF) decoded — through the
driver's content cache, which equals the pure decode
(`decodeBin_encodeBin_id`) — with the relative path an HTML link needs; no
file; a file that would not read; or a boundary picture nothing drew,
carrying the boundary's own diagnostic (W0378, W0379), whose subject
`fulfil` sets so the refusal names the picture whatever words it chose. -/
inductive Fetch where
  | decoded (href : String) (res : Except String Info)
  | missing (looked : String)
  | unreadable (err : String)
  | refused (why : Diag)

/-- One source's decision: its store entry, and the diagnostic naming the
gap when there is one. Every arm that leaves `info := none` also returns
a diagnostic whose subject is the source — `fulfilOne_named`. -/
def fulfilOne (src : String) : Fetch → Loaded × Option Diag
  | .decoded href (.ok info) => ({ src, href, info := some info }, none)
  | .decoded href (.error e) => ({ src, href }, some (imageUndecodable src e))
  | .missing looked => ({ src }, some (imageMissing src looked))
  | .unreadable err => ({ src }, some (imageUnreadable src err))
  | .refused why => ({ src }, some { why with subject := some src })

def fulfilList (entries : Array Loaded) (diags : Array Diag) :
    List (String × Fetch) → Store × Array Diag
  | [] => ({ entries }, diags)
  | (src, f) :: rest =>
    fulfilList (entries.push (fulfilOne src f).1)
      (match (fulfilOne src f).2 with | some d => diags.push d | none => diags) rest

/-- The store and the diagnostics one run's reads decide, in the order the
document requested them (`Ir.imageRefs`, the driver's loop). -/
def fulfil (fetched : Array (String × Fetch)) : Store × Array Diag :=
  fulfilList #[] #[] fetched.toList

/-- A gap is named: whenever the decision leaves no payload, it also returns
a diagnostic whose subject is the source. -/
theorem fulfilOne_named (src : String) (f : Fetch) (h : (fulfilOne src f).1.info = none) :
    ∃ d, (fulfilOne src f).2 = some d ∧ d.subject = some src := by
  cases f with
  | decoded href res =>
    cases res with
    | ok info => simp [fulfilOne] at h
    | error e => exact ⟨_, rfl, rfl⟩
  | missing looked => exact ⟨_, rfl, rfl⟩
  | unreadable err => exact ⟨_, rfl, rfl⟩
  | refused why => exact ⟨_, rfl, rfl⟩

/-- Every entry the decision writes is the fetched source's, in order. -/
theorem fulfilOne_src (src : String) (f : Fetch) : (fulfilOne src f).1.src = src := by
  cases f with
  | decoded href res => cases res <;> rfl
  | missing _ | unreadable _ | refused _ => rfl

private theorem fulfilList_named (entries : Array Loaded) (diags : Array Diag)
    (hacc : ∀ en ∈ entries, en.info = none → ∃ d ∈ diags, d.subject = some en.src) :
    ∀ (fs : List (String × Fetch)) (en : Loaded),
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
theorem fulfil_named (fetched : Array (String × Fetch)) :
    ∀ en ∈ (fulfil fetched).1.entries, en.info = none →
      ∃ d ∈ (fulfil fetched).2, d.subject = some en.src :=
  fulfilList_named #[] #[] (fun _ h => by simp at h) fetched.toList

private theorem fulfilList_covers (entries : Array Loaded) (diags : Array Diag) :
    ∀ fs : List (String × Fetch),
      ((fulfilList entries diags fs).1.entries.map (·.src)).toList =
        (entries.map (·.src)).toList ++ fs.map (·.1) := by
  intro fs
  induction fs generalizing entries diags with
  | nil => simp [fulfilList]
  | cons p rest ih =>
    obtain ⟨src, f⟩ := p
    simp only [fulfilList]
    rw [ih]
    simp [Array.toList_map, Array.toList_push, fulfilOne_src]

/-- **The store covers the request.** The entries are the fetched sources,
one each, in order: the driver fetches `Ir.imageRefs doc`, so every source
the document names has an entry to read. -/
theorem fulfil_covers (fetched : Array (String × Fetch)) :
    (fulfil fetched).1.entries.map (·.src) = fetched.map (·.1) := by
  rw [← Array.toList_inj, fulfil, fulfilList_covers]
  simp [Array.toList_map]

/-! ## Sizing

The request a document states (`width = 0.8\textwidth`, `height = 3cm`,
`scale = 0.5`, `keepaspectratio`) resolves against the intrinsic physical
size. The semantics are graphicx's: one declared dimension scales the other
to the intrinsic ratio; both declared set the box exactly, unless
`keepaspectratio` fits the image inside them; neither takes the intrinsic
size, times any `scale`. The theorems after the function are the contract:
declared size wins to the sp, and every derived dimension holds the
intrinsic ratio to within one sp of rounding. -/

/-- A requested dimension: an absolute part plus per-mille fractions of the
text width and text height, so `0.8\textwidth` rides symbolically to layout
where the measure is known. -/
structure Len where
  sp : Sp := 0
  tw : Int := 0
  th : Int := 0
  deriving Repr, BEq, Inhabited

def Len.resolve (l : Len) (textW textH : Sp) : Sp :=
  l.sp + l.tw * textW / 1000 + l.th * textH / 1000

/-- The sizing request from the source, unresolved. `scaleNum/scaleDen`
carry `scale = 0.6` exactly; 1/1 is unscaled. -/
structure SizeSpec where
  width : Option Len := none
  height : Option Len := none
  scaleNum : Int := 1
  scaleDen : Nat := 1
  keepAspect : Bool := false
  deriving Repr, BEq, Inhabited

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
