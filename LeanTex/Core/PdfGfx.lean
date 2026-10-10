module

public import LeanTex.Core.Gfx
public import LeanTex.Core.PdfRead
public import LeanTex.Core.PdfContentLex
public import LeanTex.Core.PdfFont
public import LeanTex.Core.PdfOps
public import Std.Data.HashMap
import LeanTex.Core.GfxAffine
import LeanTex.Core.PdfGfx.Fn
import LeanTex.Core.GfxPdf
import LeanTex.Core.PdfFilters
import LeanTex.Core.PngEncode
import LeanTex.Core.Ink

/-!
# A PDF page as a figure

The interpreter of a content stream's graphics (ISO 32000-2 §8) and text
(§9) onto the one vector model both backends emit (`Gfx.Figure`): what the
PDF backend embeds verbatim, the HTML backend draws from this reading.

The graphics state is read as PDF defines it; its structure becomes the
model's. A `cm` or a clip opens a group whose kids are everything painted
after it until the `Q` that restores the state it changed — so the frames
compose and the clips accumulate exactly as the state did, and no path is
ever carried back through an inverted matrix. A box that is the state's
rather than the path's — a constant soft mask's, a shading's — clips each
mark painted under it in the space it was declared in (`clipIn`). A form becomes a group under its matrix
(a symbol when it paints more than once with one inherited state), an
isolated transparency group a group with the alpha that composites it; a
glyph of an embedded font program a stamp of its outline (one outline per
glyph, one stamp per placement); a Type 3 glyph procedure a stamp of what
it fills, or a symbol when it paints with its own colours; an image a
raster, re-encoded as PNG (a JPEG passes through); a shading a gradient.

What the model cannot say is a keyed loss (`Gfx.Loss`), never silence: a
Type 1 or unembedded font, text shown with none set, vertical writing, a
shading of types 1 and 4–7, a shading function its stops only approach, a
radial shading whose start circle leaves its end circle, a shading pattern
that does not extend, a tiling pattern that strokes or paints a glyph, a
stencil mask painted with a pattern, a JPEG under a remapping `Decode`, a
JBIG2, JPX or CCITT image, a soft mask other than a constant one, alpha
read as shape, a transfer function, a blend mode, a knockout group, a text
clip mode, an ICC profile other than sRGB, Separation, DeviceN, Lab and an
unknown colour space, and a resource its name does not resolve. A device
CMYK colour previews as a viewer previews it (`cmykRgb`). Total over
arbitrary bytes: a form is never re-entered along the path that reached it
(`Entered`), and every loop is bounded by its input.
-/

namespace LeanTex.Core.PdfGfx

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx
open LeanTex.Core.PdfRead (Obj Doc)
open LeanTex.Core.PdfContentLex (Tok)

/-! ## Numbers and matrices -/

/-- A number operand exactly. -/
public def ratOf (o : Obj) : Option Rat := PdfContentLex.numRat? o

/-- A rational in sp, `65536` to the point, rounded half away from zero —
`Obj.sp?`'s reading of a decimal. -/
public def spOfRat (r : Rat) : Sp :=
  let v := r * 65536
  if v < 0 then -((-v + (1 : Rat) / 2).floor) else (v + (1 : Rat) / 2).floor

/-- A number's parts (`PdfContentLex.numParts?`) in sp, in integers: its
`n / scale` points times 65536, rounded half away from zero — `spOfRat`'s
value with no rational arithmetic (`spOf_exact`). -/
public def spOfParts (p : Bool × Nat × Nat) : Sp :=
  let (neg, n, scale) := p
  let q : Int := ((2 * 65536 * n + scale) / (2 * scale) : Nat)
  if neg then -q else q

/-- A length operand in sp. -/
public def spOf (o : Obj) : Option Sp := (PdfContentLex.numParts? o).map spOfParts

private theorem floor_natDiv (N D : Nat) (hD : 0 < D) :
    ((N : Rat) / (D : Rat)).floor = ((N / D : Nat) : Int) := by
  have hD' : (0 : Rat) < D := by exact_mod_cast hD
  apply Int.le_antisymm
  · have h : ((N : Rat) / (D : Rat)) < (((N / D : Nat) : Int) + 1 : Int) := by
      have hlt : N < (N / D + 1) * D := by
        have := Nat.lt_div_mul_add hD (a := N)
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [Rat.div_lt_iff hD']
      have : ((N : Rat)) < ((N / D + 1 : Nat) : Rat) * (D : Rat) := by exact_mod_cast hlt
      push_cast at this ⊢
      exact this
    have := (Rat.floor_lt_iff).mpr h
    omega
  · apply Rat.le_floor_iff.mpr
    have hle : (N / D) * D ≤ N := Nat.div_mul_le_self N D
    have hle' : (((N / D : Nat) : Rat)) * (D : Rat) ≤ (N : Rat) := by exact_mod_cast hle
    rw [← Rat.not_lt, Rat.div_lt_iff hD', Rat.not_lt]
    push_cast at hle' ⊢
    exact hle'

private theorem spOfParts_rat (neg : Bool) (n s : Nat) :
    spOfParts (neg, n, s) = spOfRat (let v : Rat := mkRat n s; if neg then -v else v) := by
  have h0 : ((1 : Rat) / 2).floor = 0 := by
    have := floor_natDiv 1 2 (by decide)
    simpa using this
  by_cases hs : s = 0
  · subst hs
    cases neg <;> simp [spOfParts, spOfRat] <;> rw [Rat.zero_add, h0]
  · have hs' : 0 < s := Nat.pos_of_ne_zero hs
    have hsR : (s : Rat) ≠ 0 := by exact_mod_cast hs
    have key : (mkRat (n : Int) s) * 65536 + 1 / 2 =
        (((2 * 65536 * n + s : Nat) : Rat) / ((2 * s : Nat) : Rat)) := by
      rw [Rat.mkRat_eq_div]
      push_cast
      grind
    have hn0 : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
    have hnn : ¬ (mkRat (n : Int) s) * 65536 < 0 := by
      rw [Rat.mkRat_eq_div, Rat.not_lt]
      have : (0 : Rat) ≤ (n : Rat) / (s : Rat) := by
        rw [← Rat.not_lt, Rat.div_lt_iff (by exact_mod_cast hs')]
        exact Rat.not_lt.mpr (by grind)
      push_cast
      grind
    have hq := floor_natDiv (2 * 65536 * n + s) (2 * s) (by omega)
    cases neg with
    | false =>
      simp only [spOfParts, spOfRat, Bool.false_eq_true, ↓reduceIte, hnn]
      rw [key, hq]
    | true =>
      by_cases hn : n = 0
      · subst hn
        have hsd : s / (2 * s) = 0 := Nat.div_eq_of_lt (by omega)
        simp [spOfParts, spOfRat, hsd]
        rw [Rat.zero_add, h0]
      · have hpos : (0 : Rat) < (n : Rat) / (s : Rat) := by
          rw [Rat.lt_div_iff (by exact_mod_cast hs')]
          have : (0 : Rat) < (n : Rat) := by exact_mod_cast Nat.pos_of_ne_zero hn
          grind
        have hneg : -(mkRat (n : Int) s) * 65536 < 0 := by
          rw [Rat.mkRat_eq_div]
          push_cast
          grind
        have hflip : -(-(mkRat (n : Int) s) * 65536) + 1 / 2 = (mkRat (n : Int) s) * 65536 + 1 / 2 := by
          grind
        simp only [spOfParts, spOfRat, ↓reduceIte, hneg]
        rw [hflip, key, hq]

/-- **A length read in integers is its exact reading, rounded** (`_exact`):
`spOf`'s integer arithmetic over a number's parts is `spOfRat` of the
number's exact rational — one rounding, at a sample's cost. -/
public theorem spOf_exact (o : Obj) : spOf o = (ratOf o).map spOfRat := by
  unfold spOf ratOf
  rw [PdfContentLex.numRat?_parts]
  cases PdfContentLex.numParts? o with
  | none => rfl
  | some p =>
    obtain ⟨neg, n, s⟩ := p
    simp only [Option.map_some]
    exact congrArg some (spOfParts_rat neg n s)

/-- Six numbers as a matrix (§8.3.4): the linear part as it stands, the
translation from points to sp. -/
public def affineOf (xs : Array Rat) : Option Affine :=
  if h : xs.size = 6 then
    some ⟨xs[0], xs[1], xs[2], xs[3], xs[4] * 65536, xs[5] * 65536⟩
  else none

/-- A matrix's determinant. -/
public def Affine.det (m : Affine) : Rat := m.a * m.d - m.b * m.c

/-- A matrix's exact inverse, where it has one. -/
public def Affine.inv? (m : Affine) : Option Affine :=
  let det := Affine.det m
  if det = 0 then none else
  some { a := m.d / det, b := -m.b / det, c := -m.c / det, d := m.a / det
         e := (m.c * m.f - m.d * m.e) / det, f := (m.b * m.e - m.a * m.f) / det }

/-! ## Colour -/

/-- The colour spaces a figure paints in (§8.6). Indexed reads its base
through its lookup table; Pattern names a pattern, with the space of its
colour when the pattern is uncoloured; Separation, DeviceN and Lab are read
as their component counts and named as a loss. -/
public inductive Space where
  | gray
  | rgb
  | cmyk
  | indexed (base : Space) (hival : Nat) (lookup : ByteArray)
  | pattern (under : Option Space)
  | lossy (key : String) (n : Nat)
  deriving Inhabited

/-- How many components a colour in the space has. -/
public def Space.comps : Space → Nat
  | .gray => 1
  | .rgb => 3
  | .cmyk => 4
  | .indexed _ _ _ => 1
  | .pattern _ => 0
  | .lossy _ n => n

/-- A component in [0, 1] as a byte, rounded to the nearest. -/
public def byteOf (v : Rat) : UInt8 :=
  let x := (v * 255 + (1 : Rat) / 2).floor
  UInt8.ofNat (max 0 (min 255 x)).toNat

/-- A component clamped to [0, 1]. -/
private def unit01 (v : Rat) : Rat := max 0 (min 1 v)

/-- A number's spelling as the PDF wrote it. -/
private def spelling (o : Obj) : String :=
  match o with
  | .int n => toString n
  | .real raw => raw
  | _ => "0"

/-- **A CMYK colour as a screen shows a figure's**: the sRGB each corner of
the CMYK cube previews as, index `8c + 4m + 2y + k`, as pdftoppm (Poppler
26.09) renders a device CMYK fill with no output profile — measured by
`scripts/pdffig-diff.lean --cmyk`, which holds the interpolation
(`cmykRgb`) to its rendering of interior colours too. The engine's own
CMYK colours preview by xcolor's formula (`Ir.Color.ofCmyk`); this is what
a PDF viewer makes of an imported figure's, whose PDF face the viewer
paints. -/
public def cmykCorners : Array (UInt8 × UInt8 × UInt8) :=
  #[(255, 255, 255), (35, 31, 32), (255, 242, 0), (28, 26, 0),
    (236, 0, 140), (36, 0, 0), (237, 28, 36), (34, 0, 0),
    (0, 173, 239), (0, 15, 36), (0, 166, 80), (0, 19, 0),
    (46, 49, 146), (0, 0, 2), (54, 54, 57), (0, 0, 0)]

/-- A corner's weight at a colour: the product, over the four components,
of the component where the corner's bit is set and its complement where it
is not. -/
private def cornerWeight (v : Array Rat) (i : Nat) : Rat :=
  (List.range 4).foldl (fun acc j =>
    let x := v[j]?.getD 0
    acc * (if (i / 2 ^ (3 - j)) % 2 == 1 then x else 1 - x)) 1

/-- **A CMYK colour's preview** (`cmykCorners`), components in [0, 1]:
the corners' colours weighted multilinearly, each channel rounded to its
nearest byte. -/
public def cmykRgb (c m y k : Rat) : UInt8 × UInt8 × UInt8 :=
  let v := #[unit01 c, unit01 m, unit01 y, unit01 k]
  let ch (f : UInt8 × UInt8 × UInt8 → UInt8) : UInt8 :=
    byteOf ((List.range 16).foldl (fun acc i =>
      acc + cornerWeight v i * ((f (cmykCorners[i]?.getD (0, 0, 0))).toNat : Rat)) 0 / 255)
  (ch (·.1), ch (·.2.1), ch (·.2.2))

/-- `cmykRgb` over byte components, in integers: each corner's weight in
`255⁴`ths, the sum rounded to the nearest byte — the same rounding of the
same exact value (`pdfStateChecks`), at a sample's cost. -/
public def cmykRgb8 (c m y k : UInt8) : UInt8 × UInt8 × UInt8 := Id.run do
  let b : Array UInt64 := #[c.toUInt64, m.toUInt64, y.toUInt64, k.toUInt64]
  let mut r : UInt64 := 0
  let mut g : UInt64 := 0
  let mut bl : UInt64 := 0
  for i in [0:16] do
    let mut w : UInt64 := 1
    for j in [0:4] do
      let x := b[j]?.getD 0
      w := w * (if (i >>> (3 - j)) % 2 == 1 then x else 255 - x)
    let (cr, cg, cb) := cmykCorners[i]?.getD (0, 0, 0)
    r := r + w * cr.toUInt64
    g := g + w * cg.toUInt64
    bl := bl + w * cb.toUInt64
  let n : UInt64 := 4228250625
  let round (x : UInt64) : UInt8 := ((2 * x + n) / (2 * n)).toUInt8
  return (round r, round g, round bl)

/-- A device colour from its components (§8.6.4): its screen preview — CMYK
as a viewer previews it (`cmykRgb`) — and its device model with the
components as the PDF spelled them. -/
public def deviceColor (sp : Space) (cs : Array Obj) : Ir.Color :=
  let v (i : Nat) : Rat := unit01 ((cs[i]?.bind ratOf).getD 0)
  let raw (i : Nat) : String := spelling (cs[i]?.getD (.int 0))
  match sp with
  | .gray =>
    let g := byteOf (v 0)
    { r := g, g := g, b := g, pdfModel := some (.gray (raw 0)) }
  | .rgb =>
    { r := byteOf (v 0), g := byteOf (v 1), b := byteOf (v 2)
      pdfModel := some (.rgb (raw 0) (raw 1) (raw 2)) }
  | .cmyk =>
    let (r, g, b) := cmykRgb (v 0) (v 1) (v 2) (v 3)
    { r, g, b, pdfModel := some (.cmyk (raw 0) (raw 1) (raw 2) (raw 3)) }
  | .indexed _ _ _ => { r := 0, g := 0, b := 0 }
  | .pattern _ => { r := 0, g := 0, b := 0 }
  | .lossy _ _ => { r := 128, g := 128, b := 128 }

/-- An indexed space's palette as screen colours, entry by entry (§8.6.6.3):
the lookup table's bytes in the base space, a CMYK base previewed as a
viewer previews it. -/
public def palette (base : Space) (hival : Nat) (lookup : ByteArray) : Array (UInt8 × UInt8 × UInt8) :=
  let n := base.comps
  (Array.range (hival + 1)).map fun i =>
    let lk (k : Nat) : UInt8 := lookup[i * n + k]?.getD 0
    match base with
    | .gray => (lk 0, lk 0, lk 0)
    | .rgb => (lk 0, lk 1, lk 2)
    | .cmyk => cmykRgb8 (lk 0) (lk 1) (lk 2) (lk 3)
    | _ => (0, 0, 0)

/-- A colour from components in a space: a device colour, or an indexed
colour through its lookup table. -/
public def colorIn (sp : Space) (cs : Array Obj) : Ir.Color :=
  match sp with
  | .indexed base hival lookup =>
    let i := min hival (((cs[0]?.bind ratOf).getD 0).floor.toNat)
    let (r, g, b) := (palette base hival lookup)[i]?.getD (0, 0, 0)
    { r, g, b }
  | sp => deviceColor sp cs

/-- A space's initial colour (§8.6.8): black, the first index, none for a
pattern. -/
public def Space.initial (sp : Space) : Array Obj :=
  match sp with
  | .gray => #[.int 0]
  | .rgb => #[.int 0, .int 0, .int 0]
  | .cmyk => #[.int 0, .int 0, .int 0, .int 1]
  | .indexed _ _ _ => #[.int 0]
  | .pattern _ => #[]
  | .lossy _ n => Array.replicate n (.int 1)

/-! ## The reading state -/

/-- What a fill or stroke paints with: a colour, or a pattern by its
resource name, with the colour an uncoloured pattern paints in. -/
public inductive Ink where
  | color (c : Ir.Color)
  | pattern (name : String) (under : Option Ir.Color)
  deriving Inhabited

/-- The graphics state (§8.4.1), its text state (§9.3) included, in the
frame of the stream that reads it: `ctm` is the current user space in the
figure's frame. -/
public structure GState where
  ctm : Affine
  fillSpace : Space
  strokeSpace : Space
  fill : Ink
  stroke : Ink
  width : Sp
  cap : Cap
  join : Join
  miter : Rat
  dash : Array Sp
  phase : Sp
  ca : Alpha
  cA : Alpha
  font : Option (Obj × Nat)
  size : Rat
  charSpace : Rat
  wordSpace : Rat
  hScale : Rat
  leading : Rat
  rise : Rat
  render : Nat
  /-- A soft mask read as the constant alpha it is (`maskConst`). -/
  mask : Alpha
  /-- The box outside which that mask paints nothing, with the figure-frame
  matrix of the user space the `gs` that set it stood in: part of the state,
  so `q`/`Q` save and restore it and a later `gs` replaces or drops it. -/
  maskClip : Option (Affine × Clip)
  deriving Inhabited

/-- PDF's initial graphics state under a frame. -/
public def GState.initial (ctm : Affine) : GState :=
  { ctm, fillSpace := .gray, strokeSpace := .gray, fill := .color { r := 0, g := 0, b := 0 }
    stroke := .color { r := 0, g := 0, b := 0 }, width := 65536, cap := .butt, join := .miter
    miter := 10, dash := #[], phase := 0, ca := Alpha.opaque, cA := Alpha.opaque, font := none
    size := 0, charSpace := 0, wordSpace := 0, hScale := 1, leading := 0, rise := 0, render := 0
    mask := Alpha.opaque, maskClip := none }

/-- Two alphas composited: their product, in thousandths, rounded. (Not
`Fin`'s multiplication, which wraps.) -/
public def alphaProduct (a b : Alpha) : Alpha := ⟨min 1000 ((a.val * b.val + 500) / 1000), by omega⟩

/-- The constant alpha a fill paints with: the state's, under its mask. -/
public def GState.fillAlpha (gs : GState) : Alpha := alphaProduct gs.ca gs.mask

/-- The constant alpha a stroke paints with. -/
public def GState.strokeAlpha (gs : GState) : Alpha := alphaProduct gs.cA gs.mask

/-- A group being filled: its frame, its clips, its alpha, what it holds
so far, and whether a `cm` or clip may still fold into it. -/
public structure Open where
  xf : Affine
  clips : Array Clip
  alpha : Alpha
  kids : Array (Node Run)
  deriving Inhabited

/-- What the reading has built that outlives one stream: the outlines,
symbols and rasters the figure will hold, its losses, and the caches that
read each font, glyph, form and image once. -/
public structure Store where
  outlines : Array (Array Subpath)
  symbols : Array (Array (Node Run))
  rasters : Array Raster
  losses : Array Loss
  fonts : Std.HashMap Nat PdfFont.Loaded
  glyphs : Std.HashMap (Nat × Nat) (Option Nat)
  type3 : Std.HashMap (Nat × String) (Option (Bool × Nat))
  forms : Std.HashMap String Nat
  images : Std.HashMap String (Option Nat)
  /-- Font dictionaries read in place (not by reference): each takes a key
  of its own past every object number, so no two share a glyph cache. -/
  direct : Nat
  deriving Inhabited

public def Store.empty : Store :=
  { outlines := #[], symbols := #[], rasters := #[], losses := #[], fonts := {}, glyphs := {}
    type3 := {}, forms := {}, images := {}, direct := 0 }

/-- Where the keys of fonts read in place start: past any object number a
PDF can hold (ISO 32000-2 Annex C: below 2²³). -/
public def directKeyBase : Nat := 2 ^ 32

/-- A loss, once. -/
public def Store.lose (s : Store) (l : Loss) : Store :=
  if s.losses.contains l then s else { s with losses := s.losses.push l }

/-- The state of one stream's reading. `saved` is the graphics-state
stack (§8.4.2), each entry the state `q` saved and the frame count it saw;
`level` is the frame count at the innermost `q` — what a `cm` or clip
folds into — kept beside the stack so that no operator but `q` and `Q`
reads the stack, which no operator but they writes (`gsave_restore_id`). -/
public structure St where
  gs : GState
  saved : Array (GState × Nat)
  level : Nat
  frames : Array Open
  path : Array Pdf.PathOp
  cur : Pt
  start : Pt
  clip : Option Rule
  tm : Affine
  tlm : Affine
  inText : Bool
  words : String
  ops : Array Obj
  hidden : Nat
  marks : Array Bool
  compat : Nat
  store : Store
  deriving Inhabited

/-- Where a stream is read: the document, the resources its names resolve
in, the figure-frame matrix of its default space (what a pattern's matrix
maps into, §8.7.2), the optional-content groups that are off, and the
figure's box. -/
public structure Ctx where
  doc : Doc
  res : Obj
  base : Affine
  off : Array Nat
  box : Box

/-! ## Groups -/

/-- A closed group into its parent's kids: its kids spliced when it changes
nothing, dropped when it holds nothing. -/
private def closeInto (parent : Open) (g : Open) : Open :=
  if g.kids.isEmpty then parent
  else if g.xf = Affine.unit ∧ g.clips.isEmpty ∧ g.alpha = Alpha.opaque then
    { parent with kids := parent.kids ++ g.kids }
  else { parent with kids := parent.kids.push (.group g.xf g.clips g.alpha g.kids) }

/-- Close open groups until `n` remain (the root is never closed). -/
private def closeTo (frames : Array Open) (n : Nat) : Array Open := Id.run do
  let mut fs := frames
  for _ in [0:frames.size] do
    if fs.size ≤ max n 1 then break
    -- Popped before they are joined, so a group's kids are appended to in
    -- place: a shared parent would copy every kid it holds at each close.
    let top := fs.back?
    fs := fs.pop
    let parent := fs.back?
    fs := fs.pop
    match top, parent with
    | some top, some parent => fs := fs.push (closeInto parent top)
    | _, _ => break
  return fs

/-- The frame count the current `q` level opened groups above. -/
private def St.levelBase (st : St) : Nat := st.level

/-- A node clipped to a box declared in another user space, `rel` that
space's matrix into the current one: the box itself where the two agree;
else a group in the box's own frame, holding one back in the current frame
under `rel`'s inverse — exact, so the node's frame is the one it was painted
in. A degenerate `rel` paints nothing visible, and the node stands. -/
private def clipIn (rel : Affine) (c : Clip) (n : Node Run) : Node Run :=
  if rel = Affine.unit then .group Affine.unit #[c] Alpha.opaque #[n] else
  match Affine.inv? rel with
  | some back => .group rel #[c] Alpha.opaque #[.group back #[] Alpha.opaque #[n]]
  | none => n

/-- A node clipped to the box of the constant soft mask in force
(`GState.maskClip`): outside it the mask paints nothing (§11.6.5.2). Words
carry no ink. -/
private def St.masked (st : St) (n : Node Run) : Node Run :=
  match st.gs.maskClip, n with
  | _, .words _ => n
  | none, _ => n
  | some (m0, c), _ =>
    match Affine.inv? st.gs.ctm with
    | some ic => clipIn (ic.compose m0) c n
    | none => n

/-- A node painted into the innermost open group, under the soft mask in
force (`St.masked`). -/
private def St.emit (st : St) (n : Node Run) : St :=
  if st.hidden > 0 then st else
  let n := st.masked n
  -- The frames taken out of the state, and the innermost one out of them,
  -- before its kids grow: each held once, so the push is in place. A
  -- frame shared with the state would copy every kid it holds per node.
  let frames := st.frames
  let st := { st with frames := #[] }
  match frames.back? with
  | some top =>
    let frames := frames.pop
    { st with frames := frames.push { top with kids := top.kids.push n } }
  | none => { st with frames }

/-- A `cm`: the user space moves, and what is painted after it until the
level's `Q` lives in a child frame — folded into the innermost group when
that group was opened at this level and holds nothing yet. -/
private def St.concat (st : St) (m : Affine) : St :=
  if m = Affine.unit then st else
  let gs := { st.gs with ctm := st.gs.ctm.compose m }
  match st.frames.back? with
  | some top =>
    if st.frames.size > st.levelBase && top.kids.isEmpty && top.clips.isEmpty then
      { st with gs, frames := st.frames.pop.push { top with xf := top.xf.compose m } }
    else { st with gs, frames := st.frames.push { xf := m, clips := #[], alpha := Alpha.opaque, kids := #[] } }
  | none => st

/-- A clip: what is painted after it until the level's `Q` is clipped to it,
in the current user space. -/
private def St.addClip (st : St) (c : Clip) : St :=
  match st.frames.back? with
  | some top =>
    if st.frames.size > st.levelBase && top.kids.isEmpty then
      { st with frames := st.frames.pop.push { top with clips := top.clips.push c } }
    else { st with frames := st.frames.push { xf := Affine.unit, clips := #[c], alpha := Alpha.opaque, kids := #[] } }
  | none => st

/-! ## Resources -/

/-- A resource by category and name, one reference followed. -/
private def resource (cx : Ctx) (cat name : String) : Option Obj :=
  match (cx.doc.field cx.res cat).toOption.getD none with
  | some (.dict es) => (es.find? (·.1 == name)).map (·.2)
  | _ => none

/-- An operand one name or reference resolved: a colour space named in the
resources, a reference followed. -/
private def resolveSpace (cx : Ctx) (o : Obj) : Obj :=
  let o := (cx.doc.deref o).toOption.getD .null
  let family (n : String) : Bool :=
    n == "DeviceGray" || n == "G" || n == "CalGray" || n == "DeviceRGB" || n == "RGB" ||
      n == "CalRGB" || n == "DeviceCMYK" || n == "CMYK" || n == "Pattern" || n == "I" ||
      n == "Indexed"
  if let .name n := o then
    if family n then o
    else ((resource cx "ColorSpace" n).bind fun r => (cx.doc.deref r).toOption).getD o
  else o

/-- A colour space read with nothing under it: a device family, ICCBased by
its component count (§8.6.5.5), the CIE families as their device family,
the three families named as losses. -/
private def flatSpace (cx : Ctx) (o : Obj) : Space :=
  match o with
  | .name "DeviceGray" | .name "G" | .name "CalGray" => .gray
  | .name "DeviceRGB" | .name "RGB" | .name "CalRGB" => .rgb
  | .name "DeviceCMYK" | .name "CMYK" => .cmyk
  | .name "Pattern" => .pattern none
  | .arr xs =>
    match (xs[0]? : Option Obj) with
    | some (.name "ICCBased") =>
      let n : Int := match (cx.doc.stream ((xs[1]?).getD .null)).toOption.getD none with
        | some (dict, _) => ((dict.get? "N").bind Obj.int?).getD 3
        | none => 3
      if n == 1 then .gray else if n == 4 then .cmyk else .rgb
    | some (.name "CalRGB") => .rgb
    | some (.name "CalGray") => .gray
    | some (.name "Separation") => .lossy "separation" 1
    | some (.name "DeviceN") =>
      let n := match (xs[1]?).bind fun x => (cx.doc.deref x).toOption with
        | some (.arr ns) => ns.size
        | _ => 1
      .lossy "devicen" n
    | some (.name "Lab") => .lossy "lab" 3
    | some (.name "DeviceGray") => .gray
    | some (.name "DeviceRGB") => .rgb
    | some (.name "DeviceCMYK") => .cmyk
    | _ => .lossy "colorspace-unknown" 1
  | _ => .lossy "colorspace-unknown" 1

/-- An ICC profile's description (ICC.1 §9.2.41: the `desc` tag, as v2's
text description or v4's first localized string). -/
private def iccDescription (p : ByteArray) : Option String := do
  let u32 (o : Nat) : Nat := (p[o]?.getD 0).toNat * 16777216 + (p[o + 1]?.getD 0).toNat * 65536 +
    (p[o + 2]?.getD 0).toNat * 256 + (p[o + 3]?.getD 0).toNat
  let n := min (u32 128) 256
  let entry ← (List.range n).find? fun i => p.extract (132 + 12 * i) (136 + 12 * i) == "desc".toUTF8
  let off := u32 (136 + 12 * entry)
  let size := u32 (140 + 12 * entry)
  let tag := p.extract off (off + size)
  let kind := tag.extract 0 4
  if kind == "desc".toUTF8 then
    let count := u32 (off + 8)
    String.fromUTF8? ((tag.extract 12 (12 + count)).toList.filter (· != 0) |>.toByteArray)
  else if kind == "mluc".toUTF8 then
    let len := u32 (off + 20)
    let first := u32 (off + 24)
    let units := (List.range (len / 2)).map fun i =>
      (tag[first + 2 * i]?.getD 0).toNat * 256 + (tag[first + 2 * i + 1]?.getD 0).toNat
    some (String.ofList (units.map Char.ofNat))
  else none

/-- The loss an ICC-based space's reading carries (§8.6.5.5): none for an
RGB profile that describes itself as sRGB — the space a screen's device RGB
is — and otherwise the profile, which a colour-managed reader converts
through and the device family of its component count only stands in for. -/
private def iccLoss (cx : Ctx) (profileRef : Obj) : Option String :=
  match (cx.doc.stream profileRef).toOption.getD none with
  | some (dict, raw) =>
    let n := ((dict.get? "N").bind Obj.int?).getD 3
    let profile := match PdfFilters.decode dict raw with
      | .ok (.bytes b) => b
      | _ => ByteArray.empty
    let srgb := n == 3 && profile.extract 16 20 == "RGB ".toUTF8 &&
      (iccDescription profile).any fun d => (d.splitOn "sRGB").length > 1
    if srgb then none else some "icc-profile"
  | none => some "icc-profile"

/-- **The loss a colour space's reading carries** where the device family
stands in for it (`iccLoss`), the space under an Indexed base or a
pattern's colour included. -/
private def spaceApprox (cx : Ctx) (o : Obj) : Option String :=
  let icc (o : Obj) : Option String := match o with
    | .arr xs =>
      if xs[0]? == some (.name "ICCBased") then iccLoss cx ((xs[1]?).getD .null) else none
    | _ => none
  match resolveSpace cx o with
  | .arr xs =>
    match (xs[0]? : Option Obj) with
    | some (.name "ICCBased") => icc (.arr xs)
    | some (.name "Indexed") | some (.name "I") | some (.name "Pattern") =>
      (xs[1]?).bind fun b => icc (resolveSpace cx b)
    | _ => none
  | _ => none

/-- **A colour space by its operand** (§8.6): a device family's name,
`Pattern`, a resource name, or an array — Indexed over a base, Pattern over
the space an uncoloured pattern's colour is in; the base read flat, as the
space a base may be (§8.6.6.3: neither Indexed nor Pattern). -/
public def spaceOf (cx : Ctx) (o : Obj) : Space :=
  match resolveSpace cx o with
  | .arr xs =>
    match (xs[0]? : Option Obj) with
    | some (.name "Indexed") | some (.name "I") =>
      let base := flatSpace cx (resolveSpace cx ((xs[1]?).getD (.name "DeviceRGB")))
      let hival := (((xs[2]?).bind fun x => (cx.doc.deref x).toOption).bind Obj.int?).getD 0
      let lookup : ByteArray := match (xs[3]?).getD .null with
        | .str s => (PdfContentLex.strBytes? (.str s)).getD ByteArray.empty
        | other => (PdfFont.streamBytes cx.doc other).getD ByteArray.empty
      .indexed base hival.toNat lookup
    | some (.name "Pattern") => .pattern ((xs[1]?).map fun b => flatSpace cx (resolveSpace cx b))
    | _ => flatSpace cx (.arr xs)
  | o => flatSpace cx o

/-! ## Functions and shadings -/

/-- A function object's dictionary, and its stream data when it has one. -/
private def fnDict (doc : Doc) (f : Obj) : Obj × Option ByteArray :=
  match (doc.stream f).toOption.getD none with
  | some (d, raw) =>
    match PdfFilters.decode d raw with
    | .ok (.bytes b) => (d, some b)
    | _ => (d, none)
  | none => ((doc.deref f).toOption.getD .null, none)

/-- A function's numbers under a key. -/
private def fnNums (doc : Doc) (dict : Obj) (k : String) : Array Rat :=
  match (dict.get? k).bind fun x => (doc.deref x).toOption with
  | some (.arr xs) => xs.filterMap fun x => (doc.deref x).toOption.bind ratOf
  | _ => #[]

/-- The functions a stitching joins, as written. -/
private def stitchFns (doc : Doc) (dict : Obj) : Array Obj :=
  match (dict.get? "Functions").bind fun x => (doc.deref x).toOption with
  | some (.arr xs) => xs
  | _ => #[]

/-- A function object read as a piece (§7.10): an exponential or a sampled
function, the defaults its dictionary leaves out filled as §7.10.2–3 say;
anything else — a calculator, a stitching inside a stitching — read as
nothing. -/
private def readPiece (doc : Doc) (f : Obj) : Piece :=
  let (dict, data) := fnDict doc f
  let ty := ((dict.get? "FunctionType").bind Obj.int?).getD (-1)
  let dom := fnNums doc dict "Domain"
  let d0 := dom[0]?.getD 0
  let d1 := dom[1]?.getD 1
  if ty == 2 then
    let c0 := let c := fnNums doc dict "C0"; if c.isEmpty then #[0] else c
    let c1 := let c := fnNums doc dict "C1"; if c.isEmpty then #[1] else c
    .expo { d0, d1, c0, c1, n := ((dict.get? "N").bind ratOf).getD 1 }
  else if ty == 0 then
    let size := ((fnNums doc dict "Size")[0]?.getD 2).floor.toNat
    let range := fnNums doc dict "Range"
    let enc := fnNums doc dict "Encode"
    let dec := fnNums doc dict "Decode"
    .sampled { d0, d1, size, bps := (((dict.get? "BitsPerSample").bind Obj.int?).getD 8).toNat,
               nout := max 1 (range.size / 2), e0 := enc[0]?.getD 0, e1 := enc[1]?.getD ((size : Rat) - 1),
               decode := if dec.size == range.size && !dec.isEmpty then dec else range, raw := data }
  else .unread

/-- **A function object read** (§7.10): a stitching of the pieces it joins
(Type 3), or a piece. -/
private def readFn (doc : Doc) (f : Obj) : Fn :=
  let (dict, _) := fnDict doc f
  if ((dict.get? "FunctionType").bind Obj.int?) == some 3 then
    let dom := fnNums doc dict "Domain"
    .stitch { d0 := dom[0]?.getD 0, d1 := dom[1]?.getD 1, bounds := fnNums doc dict "Bounds",
              enc := fnNums doc dict "Encode", subs := (stitchFns doc dict).map (readPiece doc) }
  else .piece (readPiece doc f)

/-- **A shading's stops** (§8.7.4.5.3): its function read at each point
its stops give (`Fn.stops`) — at a stop after the first, both the value
the function approaches from below and the one it takes there, one stop
where they agree and two at one offset where the colour jumps — each colour
in the shading's space. The second component is whether the gradient is
the shading: the function's stops are exact (`stitch_exact` for an
exponential and a stitching of them; pending work for a sampled
function), every component at every stop is inside [0, 1], so the colour
space clips none of the line between them, and a CMYK colour previews as a
line between stops — at most one of its components changing between any
two. -/
private def shadingStops (cx : Ctx) (sh : Obj) (sp : Space) : Option (Array Stop × Bool) := do
  let fnObj ← sh.get? "Function"
  let dom : Array Rat := match (sh.get? "Domain").bind fun x => (cx.doc.deref x).toOption with
    | some (.arr xs) => xs.filterMap fun x => (cx.doc.deref x).toOption.bind ratOf
    | _ => #[0, 1]
  let t0 := dom[0]?.getD 0
  let t1 := dom[1]?.getD 1
  let fns : Array Fn := (match (cx.doc.deref fnObj).toOption with
    | some (.arr xs) => xs
    | _ => #[fnObj]).map (readFn cx.doc)
  let read := fns.map fun f => f.stops t0 t1
  let pts := ((read.foldl (fun acc r => acc ++ r.1) #[]).qsort (· < ·)).foldl
    (fun acc x => if acc.back? == some x then acc else acc.push x) #[]
  let compsAt (t : Rat) (left : Bool) : Option (Array Rat) :=
    if fns.size == 1 then (fns[0]?.getD (Fn.piece .unread)).eval t left
    else fns.mapM fun f => (f.eval t left).map fun v => v[0]?.getD 0
  let offsetOf (t : Rat) : Fin 65537 :=
    let s := if t1 == t0 then 0 else (t - t0) / (t1 - t0)
    let v := (unit01 s * 65536 + (1 : Rat) / 2).floor.toNat
    ⟨min v 65536, by omega⟩
  let mut out : Array Stop := #[]
  let mut seen : Array (Array Rat) := #[]
  for h : i in [0:pts.size] do
    let t := pts[i]
    let c ← compsAt t false
    if i > 0 then
      let before ← compsAt t true
      seen := seen.push before
      if deviceColorRat sp before != deviceColorRat sp c then
        out := out.push { offset := offsetOf t, color := deviceColorRat sp before }
    seen := seen.push c
    out := out.push { offset := offsetOf t, color := deviceColorRat sp c }
  return (out, read.all (·.2) && linearIn sp seen)
where
  deviceColorRat (sp : Space) (comps : Array Rat) : Ir.Color :=
    let v (i : Nat) : Rat := unit01 (comps[i]?.getD 0)
    match sp with
    | .gray => let g := byteOf (v 0); { r := g, g := g, b := g }
    | .rgb => { r := byteOf (v 0), g := byteOf (v 1), b := byteOf (v 2) }
    | .cmyk =>
      let (r, g, b) := cmykRgb (v 0) (v 1) (v 2) (v 3)
      { r, g, b }
    | _ => { r := 128, g := 128, b := 128 }
  linearIn (sp : Space) (cs : Array (Array Rat)) : Bool :=
    cs.all (fun v => v.all fun x => 0 ≤ x && x ≤ 1) &&
      match sp with
      | .cmyk =>
        -- The preview is multilinear (`cmykRgb`): a line between two stops
        -- stays a line where at most one component changes along it. The
        -- colours are read stop by stop as each segment's two ends (`seen`:
        -- a stop's value, then the next one's as approached), so a
        -- segment is a pair at an even index; the pair after it is a jump.
        (List.range (cs.size / 2)).all fun i =>
          let a := cs[2 * i]?.getD #[]
          let b := cs[2 * i + 1]?.getD #[]
          ((List.range 4).filter fun j => a[j]?.getD 0 != b[j]?.getD 0).length ≤ 1
      | _ => true

/-- A shading read as a gradient in its own space: whether it extends past
its start and its end, and the loss key of what the gradient only
approaches — a function its stops do not equal, a radial shading whose
start circle is not inside its end circle (the model's radial gradients
are; a cone is not). -/
private structure Shade where
  g : Gradient
  e0 : Bool
  e1 : Bool
  approx : Option String
  /-- The shading's `BBox` (§8.7.4.5.1), a clip in the space it paints in. -/
  bbox : Option Clip
  /-- The loss its colour space's reading carries (`spaceApprox`). -/
  spaceLoss : Option String

/-- A shading dictionary as a gradient in its own space (§8.7.4.5): an
axial or radial shading over a function the stops read; the loss key where
it is not one. -/
private def gradientOf (cx : Ctx) (shObj : Obj) : Except String Shade := do
  let sh ← match (cx.doc.stream shObj).toOption.getD none with
    | some (d, _) => pure d
    | none => match (cx.doc.deref shObj).toOption with
      | some d => pure d
      | none => throw "shading-unreadable"
  let ty := ((sh.get? "ShadingType").bind Obj.int?).getD 0
  unless ty == 2 || ty == 3 do throw s!"shading-type-{ty}"
  let sp := spaceOf cx ((sh.get? "ColorSpace").getD (.name "DeviceRGB"))
  match sp with
  | .lossy k _ => throw k
  | .indexed _ _ _ | .pattern _ => throw "shading-space"
  | _ => pure ()
  let coords : Array Rat := match (sh.get? "Coords").bind fun x => (cx.doc.deref x).toOption with
    | some (.arr xs) => xs.filterMap fun x => (cx.doc.deref x).toOption.bind ratOf
    | _ => #[]
  let some (stops, exact) := shadingStops cx sh sp | throw "shading-function"
  let ext : Array Bool := match (sh.get? "Extend").bind fun x => (cx.doc.deref x).toOption with
    | some (.arr xs) => xs.map fun x => x == .bool true
    | _ => #[false, false]
  let e0 := ext[0]?.getD false
  let e1 := ext[1]?.getD false
  let fnLoss : Option String := if exact then none else some "shading-function-approximated"
  let c (i : Nat) : Sp := spOfRat (coords[i]?.getD 0)
  let bbox : Option Clip := match (sh.get? "BBox").bind fun x => (cx.doc.deref x).toOption with
    | some (.arr xs) =>
      let v := xs.filterMap fun x => (cx.doc.deref x).toOption.bind spOf
      if h : v.size = 4 then
        let x0 := min v[0] v[2]
        let y0 := min v[1] v[3]
        some { geom := .rect x0 y0 (max v[0] v[2] - x0) (max v[1] v[3] - y0), rule := .nonzero }
      else none
    | _ => none
  if ty == 2 then
    unless coords.size == 4 do throw "shading-coords"
    return { g := .linear (c 0, c 1) (c 2, c 3) stops Affine.unit, e0, e1, approx := fnLoss, bbox
             spaceLoss := spaceApprox cx ((sh.get? "ColorSpace").getD (.name "DeviceRGB")) }
  unless coords.size == 6 do throw "shading-coords"
  let r (i : Nat) : Rat := coords[i]?.getD 0
  let dx := r 3 - r 0
  let dy := r 4 - r 1
  let inside := r 2 ≤ r 5 && dx * dx + dy * dy ≤ (r 5 - r 2) * (r 5 - r 2)
  return { g := .radial (c 0, c 1) (c 2) (c 3, c 4) (c 5) stops Affine.unit, e0, e1
           approx := if inside then fnLoss else some "shading-radial-cone", bbox
           spaceLoss := spaceApprox cx ((sh.get? "ColorSpace").getD (.name "DeviceRGB")) }

/-- The region an axial shading paints without extension, over an area
whose corners are `area`: the strip between the normals through its ends,
reaching past every corner — a normal's length at least the farthest
corner's distance from the start, so no point of the area the shading
paints is outside it. -/
private def stripPath (p0 p1 : Pt) (area : Box) (e0 e1 : Bool) : Subpath :=
  let dx := p1.1 - p0.1
  let dy := p1.2 - p0.2
  let n := max 1 (dx.natAbs + dy.natAbs)
  let corners : List Pt := [area.1, (area.2.1, area.1.2), area.2, (area.1.1, area.2.2)]
  let far : Nat := corners.foldl (fun m q => max m ((q.1 - p0.1).natAbs + (q.2 - p0.2).natAbs)) 0
  let k : Int := (2 * (far + 65536) / n : Nat) + 1
  let nx := -dy * k
  let ny := dx * k
  let ex := dx * k
  let ey := dy * k
  let a := if e0 then (p0.1 - ex, p0.2 - ey) else p0
  let b := if e1 then (p1.1 + ex, p1.2 + ey) else p1
  { start := (a.1 + nx, a.2 + ny)
    segs := #[.line (b.1 + nx, b.2 + ny), .line (b.1 - nx, b.2 - ny), .line (a.1 - nx, a.2 - ny)]
    closed := true }

/-! ## Images -/

/-- An image's rows as samples (§8.9.3): `bpc` bits each, each row padded
to whole bytes; a 16-bit sample read by its high byte. -/
private structure Samples where
  data : ByteArray
  bpc : Nat
  rowBytes : Nat

/-- The `k`th sample of row `r`. -/
private def Samples.at (s : Samples) (r k : Nat) : Nat :=
  if s.bpc == 8 then (s.data[r * s.rowBytes + k]?.getD 0).toNat
  else if s.bpc == 16 then (s.data[r * s.rowBytes + 2 * k]?.getD 0).toNat
  else
    let bit := k * s.bpc
    let byte := (s.data[r * s.rowBytes + bit / 8]?.getD 0).toNat
    (byte >>> (8 - s.bpc - bit % 8)) % (2 ^ s.bpc)

/-- The largest value a sample reads as. -/
private def sampleFull (bpc : Nat) : Nat := if bpc == 16 then 255 else 2 ^ bpc - 1

/-- **A component's decoding as a table** (§8.9.5.2): each sample value's
byte through the `Decode` array's pair for component `j`, so a row decodes
at one lookup a sample. -/
private def decodeLut (bpc : Nat) (decode : Array Rat) (j : Nat) : Array UInt8 :=
  let full := sampleFull bpc
  (Array.range (full + 1)).map fun (v : Nat) =>
    let x : Rat := mkRat (v : Int) full
    byteOf (unit01 (match decode[2 * j]?, decode[2 * j + 1]? with
      | some d0, some d1 => d0 + x * (d1 - d0)
      | _, _ => x))

/-- Whether a `Decode` array is the default for `n` components in [0, 1]. -/
private def decodeIdentity (decode : Array Rat) (n : Nat) : Bool :=
  decode.isEmpty || decode == (List.replicate n [(0 : Rat), 1]).flatten.toArray

/-- An image's pixels as a PNG holds them: its header, its rows, the
palette an indexed one keeps. -/
private structure Pixels where
  header : PngEncode.Header
  rows : ByteArray
  palette : Option ByteArray := none

/-- **An image's samples as PNG rows** (§8.9): a grey or indexed image under
the default decoding at its own depth — its rows are PNG's as they stand, an
indexed one beside its palette, clamped as PDF clamps an index — and an RGB
one at eight bits; otherwise one byte a component through each component's
decoding table (`decodeLut`), CMYK previewed as a viewer previews it
(`cmykRgb8`), a stencil mask painted in the fill colour, an alpha beside.
Integer work, a lookup a sample. -/
private def imagePixels (sp : Space) (w h bpc : Nat) (data : ByteArray) (decode : Array Rat)
    (mask : Option Ir.Color) (alpha : Option ByteArray) : Option Pixels := Id.run do
  let comps := if mask.isSome then 1 else sp.comps
  if comps == 0 || w == 0 || h == 0 || !([1, 2, 4, 8, 16].contains bpc) then return none
  let rowBytes := (w * comps * bpc + 7) / 8
  if data.size < rowBytes * h then return none
  let s : Samples := { data, bpc, rowBytes }
  let header (depth ct : Nat) : PngEncode.Header := { width := w, height := h, bitDepth := depth, colorType := ct }
  if mask.isNone && alpha.isNone && bpc ≤ 8 then
    let rows := data.extract 0 (rowBytes * h)
    match sp with
    | .gray => if decodeIdentity decode 1 then return some { header := header bpc 0, rows }
    | .rgb => if bpc == 8 && decodeIdentity decode 3 then return some { header := header 8 2, rows }
    | .indexed base hival lookup =>
      if decode.isEmpty || decode == #[0, ((2 ^ bpc - 1 : Nat) : Rat)] then
        let pal := palette base hival lookup
        let plte := (Array.range (2 ^ bpc)).foldl (fun acc i =>
          let (r, g, b) := pal[min i hival]?.getD (0, 0, 0)
          acc.push r |>.push g |>.push b) ByteArray.empty
        return some { header := header bpc 3, rows, palette := some plte }
    | _ => pure ()
  let a (r x : Nat) : UInt8 := (alpha.bind fun al => al[r * w + x]?).getD 255
  match mask with
  | some c =>
    let inverted := decode[0]? == some 1
    let mut out := ByteArray.emptyWithCapacity (w * h * 4)
    for r in [0:h] do
      for x in [0:w] do
        let v := s.at r x
        let painted := if inverted then v == 1 else v == 0
        out := out.push c.r |>.push c.g |>.push c.b |>.push (if painted then 255 else 0)
    return some { header := header 8 6, rows := out }
  | none =>
    let hasAlpha := alpha.isSome
    match sp with
    | .gray =>
      let lut := decodeLut bpc decode 0
      let mut out := ByteArray.emptyWithCapacity (w * h * (if hasAlpha then 2 else 1))
      for r in [0:h] do
        for x in [0:w] do
          out := out.push (lut[s.at r x]?.getD 0)
          if hasAlpha then out := out.push (a r x)
      return some { header := header 8 (if hasAlpha then 4 else 0), rows := out }
    | .rgb | .cmyk | .indexed _ _ _ =>
      let luts := (Array.range comps).map (decodeLut bpc decode)
      let lutAt (j v : Nat) : UInt8 := (luts[j]?.bind (·[v]?)).getD 0
      let pal := match sp with
        | .indexed base hival lookup => palette base hival lookup
        | _ => #[]
      let maxV := 2 ^ bpc - 1
      let hival := pal.size - 1
      let indexOf : Array Nat := (Array.range (sampleFull bpc + 1)).map fun (v : Nat) =>
        min hival (match decode[0]?, decode[1]? with
          | some d0, some d1 => (d0 + mkRat (v : Int) maxV * (d1 - d0)).floor.toNat
          | _, _ => v)
      let mut out := ByteArray.emptyWithCapacity (w * h * (if hasAlpha then 4 else 3))
      for r in [0:h] do
        for x in [0:w] do
          let (pr, pg, pb) : UInt8 × UInt8 × UInt8 := match sp with
            | .rgb => (lutAt 0 (s.at r (3 * x)), lutAt 1 (s.at r (3 * x + 1)), lutAt 2 (s.at r (3 * x + 2)))
            | .cmyk => cmykRgb8 (lutAt 0 (s.at r (4 * x))) (lutAt 1 (s.at r (4 * x + 1)))
                (lutAt 2 (s.at r (4 * x + 2))) (lutAt 3 (s.at r (4 * x + 3)))
            | _ => pal[(indexOf[s.at r x]?.getD 0)]?.getD (0, 0, 0)
          out := out.push pr |>.push pg |>.push pb
          if hasAlpha then out := out.push (a r x)
      return some { header := header 8 (if hasAlpha then 6 else 2), rows := out }
    | _ => return none

/-- One 8-bit value a pixel of an image `w × h`, read from a grey image
`mw × mh` nearest-sampled (§11.6.5.3): its samples through its decoding. -/
private def grayResampled (w h mw mh bpc : Nat) (data : ByteArray) (decode : Array Rat) :
    Option ByteArray := Id.run do
  if w == 0 || h == 0 || mw == 0 || mh == 0 || !([1, 2, 4, 8, 16].contains bpc) then return none
  let rowBytes := (mw * bpc + 7) / 8
  if data.size < rowBytes * mh then return none
  let s : Samples := { data, bpc, rowBytes }
  let lut := decodeLut bpc decode 0
  let mut out := ByteArray.emptyWithCapacity (w * h)
  for r in [0:h] do
    let sy := r * mh / h
    for x in [0:w] do
      out := out.push (lut[s.at sy (x * mw / w)]?.getD 255)
  return some out

/-- A soft mask's samples (§11.6.5.3) as one 8-bit alpha per pixel of an
image `w × h`, nearest-sampled when its own size differs. -/
private def smaskAlpha (cx : Ctx) (o : Obj) (w h : Nat) : Option ByteArray := do
  let (dict, raw) ← (cx.doc.stream o).toOption.getD none
  let mw := ((dict.get? "Width").bind Obj.int?).getD 0 |>.toNat
  let mh := ((dict.get? "Height").bind Obj.int?).getD 0 |>.toNat
  let bpc := ((dict.get? "BitsPerComponent").bind Obj.int?).getD 8 |>.toNat
  let .ok (.bytes data) := PdfFilters.decode dict raw | none
  let decode : Array Rat := match (dict.get? "Decode").bind fun x => (cx.doc.deref x).toOption with
    | some (.arr xs) => xs.filterMap ratOf
    | _ => #[]
  grayResampled w h mw mh bpc data decode

/-- **An image as a raster** (§8.9.5): its stream decoded and re-encoded as
PNG — a stream deflated under a PNG predictor in gray or RGB at eight bits
becomes the PNG's data as it stands — or a JPEG handed on whole; a soft
mask or a colour-key mask as alpha. The loss key where it cannot be. -/
private def rasterOf (cx : Ctx) (dict : Obj) (raw : ByteArray) (fill : Option Ir.Color) :
    Except String Raster := do
  let get (k abbr : String) : Option Obj :=
    ((dict.get? k).orElse fun _ => dict.get? abbr).bind fun x => (cx.doc.deref x).toOption
  let w := ((get "Width" "W").bind Obj.int?).getD 0 |>.toNat
  let h := ((get "Height" "H").bind Obj.int?).getD 0 |>.toNat
  let isMask := get "ImageMask" "IM" == some (.bool true)
  let bpc := if isMask then 1 else ((get "BitsPerComponent" "BPC").bind Obj.int?).getD 8 |>.toNat
  let sp := if isMask then Space.gray else spaceOf cx ((get "ColorSpace" "CS").getD (.name "DeviceGray"))
  match sp with
  | .lossy k _ => throw k
  | .pattern _ => throw "image-pattern-space"
  | _ => pure ()
  let decode : Array Rat := match get "Decode" "D" with
    | some (.arr xs) => xs.filterMap fun x => (cx.doc.deref x).toOption.bind ratOf
    | _ => #[]
  let smooth := get "Interpolate" "I" == some (.bool true)
  if isMask && fill.isNone then throw "stencil-pattern"
  let alpha := (dict.get? "SMask").bind fun s => smaskAlpha cx s w h
  if (dict.get? "SMask").isSome && alpha.isNone then throw "smask-image"
  -- A matte names colours pre-blended with it (§11.6.5.3), which a raster
  -- with straight alpha would show blended twice.
  if ((dict.get? "SMask").bind fun s => (cx.doc.stream s).toOption.getD none).any
      fun (md, _) => (md.get? "Matte").isSome then throw "smask-matte"
  if (get "SMaskInData" "SMaskInData").isSome then throw "smask-in-data"
  let decoded ← match PdfFilters.decode dict raw with
    | .ok d => pure d
    | .error _ => throw "image-data"
  match decoded with
  | .refused f => throw f
  | .dct jpeg =>
    if alpha.isSome || isMask || (dict.get? "Mask").isSome then throw "dct-alpha"
    -- The JPEG's samples stand as they are; a `Decode` other than the
    -- identity would remap them.
    let identity : Array Rat := (List.replicate sp.comps [(0 : Rat), 1]).flatten.toArray
    unless decode.isEmpty || decode == identity do throw "dct-decode"
    match sp with
    | .gray | .rgb => return { bytes := jpeg, jpeg := true, pxW := w, pxH := h, smooth }
    | _ => throw "dct-cmyk"
  | .bytes data =>
    -- The predictor's rows, unfiltered by the decode, are what a PNG
    -- holds: the original deflated stream stands as its data.
    let parms := (dict.get? "DecodeParms").orElse fun _ => dict.get? "DP"
    let parm (k : String) (d : Int) : Int := ((parms.bind (·.get? k)).bind Obj.int?).getD d
    let pred := parm "Predictor" 1
    let colors := parm "Colors" 1
    let filterIsFlate := match (dict.get? "Filter").orElse fun _ => dict.get? "F" with
      | some (.name "FlateDecode") | some (.name "Fl") => true
      | _ => false
    let colorType := match sp with
      | .gray => some 0
      | .rgb => some 2
      | _ => none
    -- The rows stand as a PNG's only where the predictor's row layout is
    -- the image's own: its colours, eight bits each, its width.
    if pred ≥ 10 && filterIsFlate && bpc == 8 && decode.isEmpty && alpha.isNone && !isMask &&
        (dict.get? "Mask").isNone && colorType.isSome &&
        (colors == 1 || colors == 3) && (colors == 1) == (colorType == some 0) &&
        parm "BitsPerComponent" 8 == 8 && parm "Columns" 1 == w then
      return { bytes := PngEncode.encodeIdat
                 { width := w, height := h, bitDepth := 8, colorType := colorType.getD 2 } raw
               jpeg := false, pxW := w, pxH := h, smooth }
    if (match dict.get? "Mask" with | some (.arr _) => bpc != 8 | _ => false) then
      throw "color-key-mask"
    let alpha := alpha.orElse fun _ => match dict.get? "Mask" with
      | some (.arr ranges) =>
        -- §8.9.6.4: a pixel whose every component lies in its range is masked.
        let rs := ranges.filterMap fun x => (cx.doc.deref x).toOption.bind Obj.int?
        let comps := sp.comps
        let rowBytes := w * comps
        let lo (j : Nat) : Nat := ((rs[2 * j]?).getD 0).toNat
        let hi (j : Nat) : Nat := ((rs[2 * j + 1]?).getD 255).toNat
        some <| Id.run do
          let mut out := ByteArray.emptyWithCapacity (w * h)
          for r in [0:h] do
            for x in [0:w] do
              let mut inRange := true
              for j in [0:comps] do
                let v := (data[r * rowBytes + x * comps + j]?.getD 0).toNat
                if v < lo j || v > hi j then inRange := false
              out := out.push (if inRange then 0 else 255)
          return out
      | some m => match (cx.doc.stream m).toOption.getD none with
        | some (md, mraw) =>
          match PdfFilters.decode md mraw with
          | .ok (.bytes mdata) =>
            -- §8.9.6.3: a stencil mask whose 0 samples paint, under its
            -- own decoding; as an alpha, 255 where the image shows.
            let mw := ((md.get? "Width").bind Obj.int?).getD 0 |>.toNat
            let mh := ((md.get? "Height").bind Obj.int?).getD 0 |>.toNat
            let inverted := match md.get? "Decode" with
              | some (.arr xs) => (xs[0]?.bind ratOf) == some 1
              | _ => false
            grayResampled w h mw mh 1 mdata (if inverted then #[0, 1] else #[1, 0])
          | _ => none
        | _ => none
      | _ => none
    let some px := imagePixels sp w h bpc data decode (if isMask then fill else none) alpha
      | throw "image-samples"
    return { bytes := PngEncode.encode px.header px.rows px.palette, jpeg := false, pxW := w, pxH := h, smooth }

/-- A raster smoothed where it is drawn smaller than its samples: more than
one sample per point along its width, where a reader that paints each
sample as a square only aliases. A sample larger than a point stays a
square unless the image asks to be smoothed (`/Interpolate`). -/
private def smoothAt (r : Raster) (ctm : Affine) : Raster :=
  if r.smooth then r else
  let w2 := ctm.a * ctm.a + ctm.b * ctm.b
  if ((r.pxW * r.pxW : Nat) : Rat) ≥ w2 then { r with smooth := true } else r

/-! ## Glyph outlines -/

/-- An `Ink` outline as subpaths, one font unit to one frame unit (65536
sp): quadratics raised to the cubics that draw them, every contour closed. -/
public def outlineOf (cmds : Array Ink.Cmd) : Array Subpath := Id.run do
  let u : Int := 65536
  let mut out : Array Subpath := #[]
  let mut cur : Option Subpath := none
  let mut pen : Pt := (0, 0)
  for c in cmds do
    match c with
    | .move x y =>
      if let some s := cur then out := out.push { s with closed := true }
      pen := (x * u, y * u)
      cur := some { start := pen, segs := #[], closed := false }
    | .line x y =>
      let p := (x * u, y * u)
      cur := cur.map fun s => { s with segs := s.segs.push (.line p) }
      pen := p
    | .quad cx cy x y =>
      let p := (x * u, y * u)
      let q := (cx * u, cy * u)
      let seg := Kit.quadToCubic pen q p
      cur := cur.map fun s => { s with segs := s.segs.push seg }
      pen := p
    | .cube a b c d x y =>
      let p := (x * u, y * u)
      cur := cur.map fun s => { s with segs := s.segs.push (.cubic (a * u, b * u) (c * u, d * u) p) }
      pen := p
  if let some s := cur then out := out.push { s with closed := true }
  return out

/-! ## Reading a stream -/

/-- The object numbers a reading has entered on the path that reached it:
distinct, each listed by the document — so the nesting of forms, Type 3
glyphs and tiling patterns is bounded by the document's own size. -/
public structure Entered (d : Doc) where
  list : List Nat
  nodup : list.Nodup
  listed : ∀ x ∈ list, x ∈ d.objectNumbers

/-- A nodup list inside another list is no longer than it. -/
private theorem nodup_length_le {l u : List Nat} (hn : l.Nodup) (hs : ∀ x ∈ l, x ∈ u) :
    l.length ≤ u.length := by
  induction l generalizing u with
  | nil => simp
  | cons x l ih =>
    have hx : x ∈ u := hs x (by simp)
    have hn' := List.nodup_cons.mp hn
    have hsub : ∀ y ∈ l, y ∈ u.erase x := fun y hy => by
      have hy' := hs y (by simp [hy])
      have hne : y ≠ x := fun h => hn'.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr hy'
    have := ih hn'.2 hsub
    rw [List.length_erase_of_mem hx] at this
    have hpos : 0 < u.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- How many more objects a reading may enter. -/
public def Entered.room {d : Doc} (e : Entered d) : Nat := d.objectNumbers.length - e.list.length

/-- One object more entered. -/
public def Entered.push {d : Doc} (e : Entered d) (n : Nat) (hn : d.lists n = true)
    (hf : n ∉ e.list) : Entered d :=
  { list := n :: e.list, nodup := List.nodup_cons.mpr ⟨hf, e.nodup⟩
    listed := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | h
      · exact d.lists_mem x hn
      · exact e.listed x h }

/-- **Entering an object leaves less room** (`_between`): what bounds the
recursion through forms, Type 3 glyphs and tiling patterns. -/
public theorem Entered.push_room_between {d : Doc} (e : Entered d) (n : Nat) (hn : d.lists n = true)
    (hf : n ∉ e.list) : (e.push n hn hf).room < e.room := by
  have hle := nodup_length_le (e.push n hn hf).nodup (e.push n hn hf).listed
  simp only [Entered.room, Entered.push, List.length_cons] at hle ⊢
  omega

/-- **The nesting a reading can reach is bounded** (`_between`): the forms,
Type 3 glyph procedures and tiling cells a reading is inside — each entered
inside the one before — are distinct objects the document lists, so they
and the room left (`Entered.room`, which each entry shrinks) part the
document's object count between them: neither exceeds it. -/
public theorem forms_between {d : Doc} (e : Entered d) :
    e.list.length + e.room = d.objectNumbers.length ∧ e.room ≤ d.objectNumbers.length := by
  have h := nodup_length_le e.nodup e.listed
  unfold Entered.room
  omega

/-- The initial state of a stream's reading under a graphics state. -/
private def St.initial (gs : GState) (store : Store) : St :=
  { gs, saved := #[], level := 1, frames := #[{ xf := Affine.unit, clips := #[], alpha := Alpha.opaque, kids := #[] }]
    path := #[], cur := (0, 0), start := (0, 0), clip := none, tm := Affine.unit, tlm := Affine.unit
    inText := false, words := "", ops := #[], hidden := 0, marks := #[], compat := 0, store }

/-- A stream's reading finished: every group closed, the words of an open
text object kept. -/
private def St.finish (st : St) : Array (Node Run) :=
  let fs := closeTo st.frames 1
  let kids := (fs[0]?.map (·.kids)).getD #[]
  if st.words.isEmpty then kids else kids.push (.words st.words)

/-- The operands as numbers. -/
private def St.nums (st : St) : Array Rat := st.ops.filterMap ratOf

/-- The `i`th operand. -/
private def St.op (st : St) (i : Nat) : Option Obj := st.ops[i]?

/-- The luminosity of a colour in a group's space (ISO 32000-2 §11.5.3):
grey as it is, RGB weighted 0.3, 0.59, 0.11. -/
private def luminosity (sp : Space) (cs : Array Rat) : Option Rat :=
  let v (i : Nat) : Rat := unit01 (cs[i]?.getD 0)
  match sp with
  | .gray => some (v 0)
  | .rgb => some ((3 : Rat) / 10 * v 0 + (59 : Rat) / 100 * v 1 + (11 : Rat) / 100 * v 2)
  | _ => none

/-- **A soft mask that is a constant alpha** (§11.6.5.2), as cairo spells an
opacity over a gradient: a luminosity mask, no transfer function, a black
backdrop, whose group paints one constant colour over its whole box — an
axial shading extended both ways whose function is constant, or a
rectangle filled. Inside its box the mask is that colour's luminosity, and
outside the backdrop's, nothing: the alpha it is, and the box as a clip, in
the space the `gs` that sets it stands in. Any other mask is a loss. -/
private def maskConst (cx : Ctx) (sm : Obj) : Option (Alpha × Clip) := do
  let smd ← (cx.doc.deref sm).toOption
  guard (smd.get? "S" == some (.name "Luminosity"))
  guard ((smd.get? "TR").all (· == .name "Identity"))
  guard ((smd.get? "BC").all fun b => match (cx.doc.deref b).toOption with
    | some (.arr xs) => xs.all fun x => ratOf x == some 0
    | _ => false)
  let gref ← smd.get? "G"
  let (gd, graw) ← (cx.doc.stream gref).toOption.getD none
  let data ← match PdfFilters.decode gd graw with
    | .ok (.bytes b) => some b
    | _ => none
  -- Luminosity is read in the group's blending space (§11.5.3): grey and
  -- RGB weigh a colour the same way whichever of the two it was set in.
  let blendOk : Bool := match (gd.get? "Group").bind fun x => (cx.doc.deref x).toOption with
    | some grp => match spaceOf cx ((grp.get? "CS").getD (.name "DeviceGray")) with
      | .gray | .rgb => true
      | _ => false
    | none => true
  guard blendOk
  let res := ((gd.get? "Resources").bind fun x => (cx.doc.deref x).toOption).getD cx.res
  let gcx : Ctx := { cx with res }
  let bbox : Array Rat := match (gd.get? "BBox").bind fun x => (cx.doc.deref x).toOption with
    | some (.arr xs) => xs.filterMap fun x => (cx.doc.deref x).toOption.bind ratOf
    | _ => #[]
  guard (bbox.size == 4)
  guard (((gd.get? "Matrix").bind fun x => (cx.doc.deref x).toOption).all fun m => match m with
    | .arr xs => (affineOf (xs.filterMap ratOf)) == some Affine.unit
    | _ => false)
  let toks := PdfContentLex.scan data
  let mut ops : Array Obj := #[]
  let mut fill : Option Rat := some 0
  let mut lum : Option Rat := none
  let mut paints := 0
  let mut rect : Option (Array Rat) := none
  for t in toks do
    match t with
    | .val o => ops := ops.push o
    | .op name =>
      let nums := ops.filterMap ratOf
      if name == "g" then fill := luminosity .gray nums
      else if name == "rg" then fill := luminosity .rgb nums
      else if name == "re" then rect := some nums
      else if name == "f" || name == "F" then
        match rect with
        | some r =>
          let covers := r.size == 4 && (r[0]?.getD 0) ≤ min (bbox[0]?.getD 0) (bbox[2]?.getD 0) &&
            (r[1]?.getD 0) ≤ min (bbox[1]?.getD 0) (bbox[3]?.getD 0) &&
            (r[0]?.getD 0) + (r[2]?.getD 0) ≥ max (bbox[0]?.getD 0) (bbox[2]?.getD 0) &&
            (r[1]?.getD 0) + (r[3]?.getD 0) ≥ max (bbox[1]?.getD 0) (bbox[3]?.getD 0)
          if covers then
            lum := fill
            paints := paints + 1
          else paints := paints + 2
        | none => paints := paints + 2
        rect := none
      else if name == "sh" then
        let shObj := (ops[0]?).bind fun o => match o with
          | .name n => resource gcx "Shading" n
          | _ => none
        let sh := shObj.bind fun r => match (cx.doc.stream r).toOption.getD none with
          | some (d, _) => some d
          | none => (cx.doc.deref r).toOption
        match sh with
        | some d =>
          let fnObj := (d.get? "Function").getD .null
          let (fd, _) := fnDict cx.doc fnObj
          let ext := match (d.get? "Extend").bind fun x => (cx.doc.deref x).toOption with
            | some (.arr xs) => xs.all (· == .bool true)
            | _ => false
          let sp := spaceOf gcx ((d.get? "ColorSpace").getD (.name "DeviceGray"))
          let c0 := fnNums cx.doc fd "C0"
          let c1 := fnNums cx.doc fd "C1"
          let constant := ((fd.get? "FunctionType").bind Obj.int?) == some 2 && c0 == c1 && !c0.isEmpty
          if ext && constant then
            lum := luminosity sp c0
            paints := paints + 1
          else paints := paints + 2
        | none => paints := paints + 2
      else if name == "q" || name == "Q" || name == "gs" || name == "n" || name == "W" ||
          name == "BX" || name == "EX" then pure ()
      else paints := paints + 2
      ops := #[]
    | .inline _ _ => paints := paints + 2
  guard (paints == 1)
  let l ← lum
  let a : Alpha := ⟨min 1000 ((l * 1000 + (1 : Rat) / 2).floor.toNat), by omega⟩
  let x0 := spOfRat (min (bbox[0]?.getD 0) (bbox[2]?.getD 0))
  let x1 := spOfRat (max (bbox[0]?.getD 0) (bbox[2]?.getD 0))
  let y0 := spOfRat (min (bbox[1]?.getD 0) (bbox[3]?.getD 0))
  let y1 := spOfRat (max (bbox[1]?.getD 0) (bbox[3]?.getD 0))
  return (a, { geom := .rect x0 y0 (x1 - x0) (y1 - y0), rule := .nonzero })

/-- The graphics-state parameters an ExtGState sets (§8.4.5): line width,
caps, joins, miter limit, dash, alphas, the font; a soft mask other than
`None`, a blend mode other than `Normal` named as a loss. -/
private def applyExtG (cx : Ctx) (st : St) (name : String) : St := Id.run do
  let some r := resource cx "ExtGState" name
    | return { st with store := st.store.lose (.resource "extgstate-unresolved") }
  let some g := (cx.doc.deref r).toOption | return st
  let mut st := st
  let alphaOf (o : Obj) : Option Alpha := (ratOf o).map fun v =>
    let x := (unit01 v * 1000 + (1 : Rat) / 2).floor.toNat
    ⟨min x 1000, by omega⟩
  let val (k : String) : Option Obj := (g.get? k).bind fun x => (cx.doc.deref x).toOption
  if let some a := (val "ca").bind alphaOf then st := { st with gs := { st.gs with ca := a } }
  if let some a := (val "CA").bind alphaOf then st := { st with gs := { st.gs with cA := a } }
  if let some w := (val "LW").bind spOf then st := { st with gs := { st.gs with width := w } }
  if let some c := (val "LC").bind Obj.int? then
    st := { st with gs := { st.gs with cap := if c == 1 then .round else if c == 2 then .square else .butt } }
  if let some j := (val "LJ").bind Obj.int? then
    st := { st with gs := { st.gs with join := if j == 1 then .round else if j == 2 then .bevel else .miter } }
  if let some m := (val "ML").bind ratOf then st := { st with gs := { st.gs with miter := m } }
  match val "D" with
  | some (.arr #[.arr ds, ph]) =>
    st := { st with gs := { st.gs with dash := ds.filterMap spOf, phase := (spOf ph).getD 0 } }
  | _ => pure ()
  match val "Font" with
  | some (.arr #[f, sz]) =>
    st := { st with gs := { st.gs with font := some (f, 0), size := (ratOf sz).getD 0 } }
  | _ => pure ()
  match val "SMask" with
  | some (.name "None") => st := { st with gs := { st.gs with mask := Alpha.opaque, maskClip := none } }
  | none => pure ()
  | some _ =>
    match (g.get? "SMask").bind (maskConst cx) with
    | some (a, clip) => st := { st with gs := { st.gs with mask := a, maskClip := some (st.gs.ctm, clip) } }
    | none =>
      st := { st with gs := { st.gs with mask := Alpha.opaque, maskClip := none }
                      store := st.store.lose (.property "soft-mask") }
  -- §11.6.4.3: alpha read as shape changes how a group composites; a
  -- transfer function remaps every colour component (§10.5). Black
  -- generation, undercolour removal and halftones shape a printer's
  -- separations, not what a screen shows.
  if val "AIS" == some (.bool true) then
    st := { st with store := st.store.lose (.property "alpha-is-shape") }
  for k in ["TR", "TR2"] do
    match val k with
    | none | some (.name "Identity") | some (.name "Default") => pure ()
    | some _ => st := { st with store := st.store.lose (.property "transfer-function") }
  match val "BM" with
  | some (.name "Normal") | some (.name "Compatible") | none => pure ()
  | some (.arr xs) =>
    if !(xs[0]? == some (.name "Normal") || xs[0]? == some (.name "Compatible")) then
      st := { st with store := st.store.lose (.property "blend-mode") }
  | some _ => st := { st with store := st.store.lose (.property "blend-mode") }
  return st

/-- What an ink paints with: its paint, and the clip it carries — a shading
pattern's `BBox`, in pattern space, with that space's matrix into the current
user space (`clipIn`). -/
private structure Painted where
  paint : Paint
  clip : Option (Affine × Clip)

/-- The paint an ink resolves to, read in the current user space: a colour,
or a shading pattern's gradient — its matrix maps pattern space to the
stream's default space (§8.7.2), so the gradient's own frame is that
matrix carried back through the current one. A tiling pattern fills a path
by `tileNodes`; anything else it paints — a stroke, a glyph — is a loss. -/
private def paintOf (cx : Ctx) (st : St) (ink : Ink) : St × Option Painted :=
  let solid (c : Ir.Color) : Painted := { paint := .solid c, clip := none }
  match ink with
  | .color c => (st, some (solid c))
  | .pattern name under =>
    match resource cx "Pattern" name with
    | none => ({ st with store := st.store.lose (.resource "pattern-unresolved") }, under.map solid)
    | some r =>
      let pat := (match (cx.doc.stream r).toOption.getD none with
        | some (d, _) => some d
        | none => (cx.doc.deref r).toOption).getD .null
      let ty : Int := ((pat.get? "PatternType").bind Obj.int?).getD 0
      if ty == 2 then
        let m := match (pat.get? "Matrix").bind fun x => (cx.doc.deref x).toOption with
          | some (.arr xs) => (affineOf (xs.filterMap fun x => (cx.doc.deref x).toOption.bind ratOf)).getD Affine.unit
          | _ => Affine.unit
        match gradientOf cx ((pat.get? "Shading").getD .null), Affine.inv? st.gs.ctm with
        | .ok sh, some inv =>
          -- A pattern paints its shading only where the shading paints:
          -- an unextended one leaves the rest of the path unpainted, which
          -- a gradient paint, padded, does not.
          let st := match sh.approx with
            | some k => { st with store := st.store.lose (.resource k) }
            | none => st
          let st := match sh.spaceLoss with
            | some k => { st with store := st.store.lose (.value k) }
            | none => st
          let st := if sh.e0 && sh.e1 then st else { st with store := st.store.lose (.resource "shading-unextended") }
          let xf := inv.compose (cx.base.compose m)
          (st, some { paint := .gradient (sh.g.withXf xf), clip := sh.bbox.map (xf, ·) })
        | .error k, _ => ({ st with store := st.store.lose (.resource k) }, under.map solid)
        | .ok _, none => (st, none)
      else if ty == 1 then ({ st with store := st.store.lose (.resource "tiling-paint") }, under.map solid)
      else ({ st with store := st.store.lose (.resource "pattern-type") }, under.map solid)

/-- A node under the clip its paint carries. -/
private def withPaintClip (clip : Option (Affine × Clip)) (n : Node Run) : Node Run :=
  match clip with
  | some (rel, c) => clipIn rel c n
  | none => n

/-- The current path's geometry, as the typed operators read it: one `re`
of negative extent is the path PDF traces for it, from its corner toward
the negative extents — a figure's rectangles have none, and a dash pattern
starts where the path does. -/
private def St.geom (st : St) : Geom :=
  match GfxPdf.geomOf st.path.toList with
  | .rect x y w h => if w < 0 || h < 0 then .path #[Kit.rectPath x y w h] else .rect x y w h
  | .ellipse cx cy rx ry => .ellipse cx cy rx ry
  | .path subs => .path subs

/-- A path painted (§8.5.3): filled by its rule, stroked with the state in
force, each with its constant alpha; then the clip it was marked for. -/
private def paintPath (cx : Ctx) (st : St) (fill : Option Rule) (stroke : Bool) (close : Bool)
    (tiles : Option (Array (Node Run)) := none) : St :=
  let st := if close && !st.path.isEmpty then { st with path := st.path.push .close } else st
  let geom := st.geom
  -- A tiling pattern's fill is its tiles, not a paint.
  let (st, fp) := match fill, tiles with
    | some _, none => paintOf cx st st.gs.fill
    | _, _ => (st, none)
  let (st, sp) := if stroke then paintOf cx st st.gs.stroke else (st, none)
  let fl : Option Fill := match fill, fp with
    | some r, some p => some { paint := p.paint, rule := r, alpha := st.gs.fillAlpha }
    | _, _ => none
  let sk : Option Stroke := if stroke then sp.map fun p =>
      { paint := p.paint, width := st.gs.width, cap := st.gs.cap, join := st.gs.join
        miterLimit := st.gs.miter, dash := Kit.normDash st.gs.dash, phase := st.gs.phase, alpha := st.gs.strokeAlpha }
    else none
  let fillClip := fp.bind (·.clip)
  let strokeClip := sp.bind (·.clip)
  let st := match tiles, fill with
    | some ts, some rule =>
      let st := if st.path.isEmpty || ts.isEmpty then st
        else st.emit (.group Affine.unit #[{ geom, rule }] Alpha.opaque ts)
      if st.path.isEmpty || sk.isNone then st else st.emit (withPaintClip strokeClip (.draw geom none sk))
    | _, _ =>
      if st.path.isEmpty || (fl.isNone && sk.isNone) then st
      else if fillClip.isNone && strokeClip.isNone then st.emit (.draw geom fl sk)
      else
        -- Paints clipped apart are two marks, the fill first (§8.5.3).
        let st := if fl.isNone then st else st.emit (withPaintClip fillClip (.draw geom fl none))
        if sk.isNone then st else st.emit (withPaintClip strokeClip (.draw geom none sk))
  let st := match st.clip with
    | some rule => if st.path.isEmpty then st else st.addClip { geom, rule }
    | none => st
  { st with path := #[], clip := none }

/-- The point a `v` or `y` takes from the current point. -/
private def St.moveTo (st : St) (p : Pt) : St :=
  { st with path := st.path.push (.moveTo p.1 p.2), cur := p, start := p }

/-- The text rendering matrix's frame for one glyph (§9.4.4): the text
matrix, the font size, the horizontal scale and the rise, in the current
user space. -/
private def textFrame (st : St) : Affine :=
  st.tm.compose ⟨st.gs.size * st.gs.hScale, 0, 0, st.gs.size, 0, st.gs.rise * 65536⟩

/-- The text matrix moved along the baseline by `tx` text-space units. -/
private def St.advance (st : St) (tx : Rat) : St :=
  { st with tm := st.tm.compose ⟨1, 0, 0, 1, tx * 65536, 0⟩ }

/-- A font matrix as an affine map, translation in sp. -/
private def fontMatrix (m : Array Rat) : Affine :=
  (affineOf m).getD ⟨mkRat 1 1000, 0, 0, mkRat 1 1000, 0, 0⟩

/-- What a text rendering mode paints (§9.3.6): fill, stroke, whether it
adds to the clip. -/
private def renderPaints (mode : Nat) : Bool × Bool × Bool :=
  match mode with
  | 0 => (true, false, false)
  | 1 => (false, true, false)
  | 2 => (true, true, false)
  | 3 => (false, false, false)
  | 4 => (true, false, true)
  | 5 => (false, true, true)
  | 6 => (true, true, true)
  | _ => (false, false, true)

/-- The factor a frame scales every length by, where it is an axis-aligned
similarity: no shear, no rotation, the two axes scaled alike up to a
reflection. -/
public def frameScale? (m : Affine) : Option Rat :=
  if m.b = 0 ∧ m.c = 0 ∧ m.a ≠ 0 ∧ (m.d = m.a ∨ m.d = -m.a) then
    some (if m.a < 0 then -m.a else m.a)
  else none

/-- A user-space length carried into a glyph frame: its sp divided by the
frame's scale (`frameScale?`), rounded once to the frame's sp; `none` where
the frame scales no length alike in every direction. -/
public def strokeIn (m : Affine) (w : Sp) : Option Sp :=
  (frameScale? m).map fun s => spOfRat ((w : Rat) / 65536 / s)

/-- `spOfRat` rounds to the nearest sp: within half of one. -/
public theorem spOfRat_between (r : Rat) :
    r * 65536 - 1 / 2 ≤ (spOfRat r : Rat) ∧ (spOfRat r : Rat) ≤ r * 65536 + 1 / 2 := by
  unfold spOfRat
  have floorLe (x : Rat) : ((x.floor : Int) : Rat) ≤ x := Rat.le_floor_iff.mp (Int.le_refl _)
  have ltFloor (x : Rat) : x < ((x.floor + 1 : Int) : Rat) := Rat.floor_lt_iff.mp (Int.lt_succ _)
  simp only
  split
  · next hv =>
    have h1 := floorLe (-(r * 65536) + 1 / 2)
    have h2 := ltFloor (-(r * 65536) + 1 / 2)
    push_cast at h1 h2 ⊢
    constructor <;> grind
  · next hv =>
    have h1 := floorLe (r * 65536 + 1 / 2)
    have h2 := ltFloor (r * 65536 + 1 / 2)
    push_cast at h1 h2 ⊢
    constructor <;> grind

/-- **A length carried into a glyph frame lands back on itself**
(`_between`): where `strokeIn` answers, the frame scales lengths by a
positive `s`, and the carried length drawn through the frame is the user
space's within half of the frame's sp — one rounding, in the frame. A
glyph stroked through its frame strokes the width, dash and phase the
graphics state set. -/
public theorem strokeIn_between (m : Affine) (w w' : Sp) (h : strokeIn m w = some w') :
    ∃ s : Rat, 0 < s ∧ m.b = 0 ∧ m.c = 0 ∧ (m.a = s ∨ m.a = -s) ∧ (m.d = s ∨ m.d = -s) ∧
      (w : Rat) - s / 2 ≤ (w' : Rat) * s ∧ (w' : Rat) * s ≤ (w : Rat) + s / 2 := by
  unfold strokeIn frameScale? at h
  split at h
  · next hm =>
    obtain ⟨hb, hc, ha, hd⟩ := hm
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨if m.a < 0 then -m.a else m.a, ?_, hb, hc, ?_, ?_, ?_⟩
    · split <;> grind
    · split <;> grind
    · split <;> grind
    · have hs : (0 : Rat) < (if m.a < 0 then -m.a else m.a) := by split <;> grind
      generalize (if m.a < 0 then -m.a else m.a) = s at hs ⊢
      have hr := spOfRat_between ((w : Rat) / 65536 / s)
      have e : (w : Rat) / 65536 / s * 65536 = (w : Rat) / s := by grind
      rw [e] at hr
      obtain ⟨lo, hi⟩ := hr
      have hlo := Rat.mul_le_mul_of_nonneg_right lo (Rat.le_of_lt hs)
      have hhi := Rat.mul_le_mul_of_nonneg_right hi (Rat.le_of_lt hs)
      have e2 : ((w : Rat) / s - 1 / 2) * s = (w : Rat) - s / 2 := by grind
      have e3 : ((w : Rat) / s + 1 / 2) * s = (w : Rat) + s / 2 := by grind
      rw [e2] at hlo
      rw [e3] at hhi
      exact ⟨hlo, hhi⟩
  · simp at h

/-- The colour a stencil mask paints in (§8.9.6.2): the fill colour; a
pattern is none, and `rasterOf` names the mask a loss. -/
private def fillColor (st : St) : Option Ir.Color :=
  match st.gs.fill with
  | .color c => some c
  | .pattern _ _ => none

/-- The inherited state a form's reading starts from, as a key: two `Do`s
of one form with one key read the same, so the second uses the first's
symbol. -/
private def stateKey (gs : GState) : String :=
  let ink : Ink → String
    | .color c => s!"{c.r} {c.g} {c.b} {reprStr c.pdfModel} {reprStr c.cmyk}"
    | .pattern n _ => "/" ++ n
  let fontKey := match gs.font with
    | some (.ref n _, _) => toString n
    | some _ => "direct"
    | none => "-"
  s!"{ink gs.fill}|{ink gs.stroke}|{gs.width}|{reprStr gs.cap}|{reprStr gs.join}|{gs.miter}|\
{gs.dash}|{gs.phase}|{gs.ca.val}|{gs.cA.val}|{gs.mask.val}|{fontKey}|{gs.size}|{gs.charSpace}|{gs.wordSpace}|\
{gs.hScale}|{gs.leading}|{gs.rise}|{gs.render}"

/-- Whether an optional-content reference names a group that is off. -/
private def ocOff (cx : Ctx) (o : Obj) : Bool :=
  match o with
  | .ref n _ =>
    if cx.off.contains n then true else
    match (cx.doc.deref o).toOption with
    | some d =>
      if d.get? "Type" == some (.name "OCMD") then
        -- `OCGs` is one group's reference or an array of them (§8.11.2.2);
        -- the visibility policy reads the array.
        let refs : Array Nat := match d.get? "OCGs" with
          | some (.ref m g) => match (cx.doc.deref (.ref m g)).toOption with
            | some (.arr xs) => xs.filterMap fun x => match x with
              | .ref k _ => some k
              | _ => none
            | _ => #[m]
          | some (.arr xs) => xs.filterMap fun x => match x with
            | .ref k _ => some k
            | _ => none
          | _ => #[]
        let pol := (d.get? "P").getD (.name "AnyOn")
        if refs.isEmpty then false
        else if pol == .name "AllOn" then refs.any cx.off.contains
        else if pol == .name "AnyOff" then refs.all fun r => !cx.off.contains r
        else if pol == .name "AllOff" then refs.any fun r => !cx.off.contains r
        else refs.all cx.off.contains
      else false
    | none => false
  | _ => false

/-- The ink box of nodes in their own frame, rasters by their unit square. -/
private def nodesInk (nodes : Array (Node Run)) (outlines : Array (Array Subpath))
    (symbols : Array (Array (Node Run))) : Option Box :=
  let fig : Figure Run :=
    { box := ((0, 0), (0, 0)), clipToBox := false, nodes, outlines, symbols, rasters := #[]
      title := none, losses := #[] }
  fig.inkBox fun _ => none

/-- A form's box as a rectangle clip, when what it painted reaches past it:
a box that holds every mark's ink clips nothing, so it is no clip at all. -/
private def bboxClip (dict : Obj) (doc : Doc) (body : Array (Node Run)) (store : Store) : Array Clip :=
  match (dict.get? "BBox").bind fun x => (doc.deref x).toOption with
  | some (.arr xs) =>
    let v := xs.filterMap fun x => (doc.deref x).toOption.bind spOf
    if h : v.size = 4 then
      let x0 := min v[0] v[2]
      let x1 := max v[0] v[2]
      let y0 := min v[1] v[3]
      let y1 := max v[1] v[3]
      let inside := match nodesInk body store.outlines store.symbols with
        | some ((a, b), (c, d)) => x0 ≤ a && y0 ≤ b && c ≤ x1 && d ≤ y1
        | none => true
      if inside then #[] else #[{ geom := .rect x0 y0 (x1 - x0) (y1 - y0), rule := .nonzero }]
    else #[]
  | _ => #[]

/-- A shading painted over the current clip (`sh`, §8.7.4.2): its gradient in
the current user space, over the figure's box carried into that space — the
region a shading without extension paints, where it does not extend: the
strip between its normals, or its end circle less its start circle. -/
private def shadeOp (cx : Ctx) (st : St) : St :=
  if st.hidden > 0 then st else
  match st.op 0 with
  | some (.name shName) =>
    match resource cx "Shading" shName with
    | none => { st with store := st.store.lose (.resource "shading-unresolved") }
    | some r =>
      match gradientOf cx r, Affine.inv? st.gs.ctm with
      | .error k, _ => { st with store := st.store.lose (.resource k) }
      | .ok _, none => st
      | .ok sh, some inv =>
        let st := match sh.approx with
          | some k => { st with store := st.store.lose (.resource k) }
          | none => st
        let st := match sh.spaceLoss with
          | some k => { st with store := st.store.lose (.value k) }
          | none => st
        let area := Box.image inv cx.box
        let all : Geom := .rect area.1.1 area.1.2 (area.2.1 - area.1.1) (area.2.2 - area.1.2)
        let (geom, rule) : Geom × Rule := match sh.g with
          | .linear p0 p1 _ _ =>
            if sh.e0 && sh.e1 then (all, .nonzero) else (.path #[stripPath p0 p1 area sh.e0 sh.e1], .nonzero)
          | .radial c0 r0 c1 r1 _ _ =>
            -- Unextended past its start, a radial shading leaves the start
            -- circle's inside unpainted.
            let hole := if sh.e0 || r0 == 0 then #[] else Kit.ellipse c0.1 c0.2 r0 r0
            let outer := if sh.e1 then
                #[Kit.rectPath area.1.1 area.1.2 (area.2.1 - area.1.1) (area.2.2 - area.1.2)]
              else Kit.ellipse c1.1 c1.2 r1 r1
            if sh.e1 && hole.isEmpty then (all, .nonzero)
            else (.path (outer ++ hole), if hole.isEmpty then .nonzero else .evenOdd)
        -- The shading's own box clips it, in the space it paints in (§8.7.4.5.1).
        let draw : Node Run := .draw geom (some { paint := .gradient sh.g, rule, alpha := st.gs.fillAlpha }) none
        st.emit (withPaintClip (sh.bbox.map (Affine.unit, ·)) draw)
  | _ => st

/-- The words a text object says, a space put where the pen jumps by more
than a fifth of the font size. -/
private def St.addWords (st : St) (t : String) : St :=
  if t.isEmpty then st else { st with words := st.words ++ t }

private def St.space (st : St) : St :=
  if st.words.isEmpty || st.words.endsWith " " then st else { st with words := st.words ++ " " }

/-- A font resource read once per font object. -/
public def fontOf (cx : Ctx) (st : St) : St × Option (PdfFont.Loaded × Nat) :=
  match st.gs.font with
  | none => (st, none)
  | some (fo, _) =>
    match fo with
    | .ref n _ =>
      match st.store.fonts.get? n with
      | some f => (st, some (f, n))
      | none =>
        let fd := (cx.doc.deref fo).toOption.getD .null
        let f := PdfFont.load cx.doc fd
        let store := { st.store with fonts := st.store.fonts.insert n f }
        let store := f.losses.foldl Store.lose store
        ({ st with store }, some (f, n))
    | fd =>
      let f := PdfFont.load cx.doc fd
      let key := directKeyBase + st.store.direct
      let st := { st with store := { st.store with direct := st.store.direct + 1 } }
      let st := { st with store := f.losses.foldl Store.lose st.store }
      (st, some (f, key))

/-- A glyph's outline index in an `Ink` program, decoded once. -/
private def glyphOutline (st : St) (key : Nat) (src : Ink.Src) (gid : Nat) : St × Option Nat :=
  match st.store.glyphs.get? (key, gid) with
  | some r => (st, r)
  | none =>
    let r : Option (Array Subpath) := (src.cmdsAt gid).map outlineOf
    match r with
    | some o =>
      if o.isEmpty then
        ({ st with store := { st.store with glyphs := st.store.glyphs.insert (key, gid) none } }, none)
      else
        let k := st.store.outlines.size
        ({ st with store := { st.store with outlines := st.store.outlines.push o
                                            glyphs := st.store.glyphs.insert (key, gid) (some k) } }, some k)
    | none =>
      ({ st with store := { (st.store.lose (.font "glyph-undecodable")) with
                            glyphs := st.store.glyphs.insert (key, gid) none } }, none)

/-- One glyph stamped at the text frame: its outline under the frame and
the font's matrix, painted by the rendering mode. -/
private def stampGlyph (cx : Ctx) (st : St) (outline : Nat) (gm : Affine) (rule : Rule) : St :=
  let (fillP, strokeP, clipP) := renderPaints st.gs.render
  let st := if clipP then { st with store := st.store.lose (.value "text-clip") } else st
  let xf := (textFrame st).compose gm
  let (st, fp) := if fillP then paintOf cx st st.gs.fill else (st, none)
  let (st, sp) := if strokeP then paintOf cx st st.gs.stroke else (st, none)
  let fl := fp.map fun p => ({ paint := p.paint, rule, alpha := st.gs.fillAlpha } : Fill)
  let (st, sk) := match sp with
    | some p =>
      -- The stroke's lengths — width, dash and phase — are the user space's,
      -- carried into the glyph frame by its scale.
      match strokeIn xf st.gs.width, st.gs.dash.mapM (strokeIn xf), strokeIn xf st.gs.phase with
      | some w, some dash, some phase =>
        (st, some ({ paint := p.paint, width := w, cap := st.gs.cap, join := st.gs.join
                     miterLimit := st.gs.miter, dash := Kit.normDash dash, phase
                     alpha := st.gs.strokeAlpha } : Stroke))
      | _, _, _ => ({ st with store := st.store.lose (.value "text-stroke-frame") }, none)
    | none => (st, none)
  let fillClip := fp.bind (·.clip)
  let strokeClip := sp.bind (·.clip)
  if fl.isNone && sk.isNone then st
  else if fillClip.isNone && strokeClip.isNone then st.emit (.stamp outline xf fl sk)
  else
    let st := if fl.isNone then st else st.emit (withPaintClip fillClip (.stamp outline xf fl none))
    if sk.isNone then st else st.emit (withPaintClip strokeClip (.stamp outline xf none sk))

/-- The most tiles a tiling pattern paints one region with. -/
public def tileCap : Nat := 4096

/-- A geometry as the subpaths it fills: an ellipse as its arcs, a
rectangle as its path. -/
public def subpathsOf (g : Geom) : Array Subpath :=
  match g.normal with
  | .path ss => ss
  | .rect x y w h => #[Kit.rectPath x y w h]
  | .ellipse _ _ _ _ => #[]

/-- **What a Type 3 procedure stamps** (§9.6.4): the outline of its one
fill, when it is a `d1` procedure — whose colour is the text's — whose one
painting is a fill by the nonzero rule and no stroke. One fill is what a
stamp painted in the text's fill reproduces: several fills are not one
path's nonzero fill where their windings meet, so they stay a symbol. -/
public def type3Stamp? (isD1 : Bool) (body : Array (Node Run)) : Option (Array Subpath) :=
  if !isD1 then none else
  match (body.filter fun nd => match nd with
      | .words _ => false
      | .draw _ _ _ | .group _ _ _ _ | .use _ _ | .stamp _ _ _ _ | .image _ _ | .label _ => true).toList with
  | [.draw g (some fl) none] => if fl.rule = .nonzero then some (subpathsOf g) else none
  | _ => none

/-- **A Type 3 procedure's stamp is its one fill** (`_exact`): `type3Stamp?`
answers only for a `d1` procedure whose reading paints exactly one nonzero
fill and no stroke, and the outline it answers is that fill's geometry —
what `type3Glyph` stamps, read with neutral colours, in the text's paints. -/
public theorem type3_exact (isD1 : Bool) (body : Array (Node Run)) (subs : Array Subpath)
    (h : type3Stamp? isD1 body = some subs) :
    isD1 = true ∧ ∃ g fl, (body.filter fun nd => match nd with
        | .words _ => false
        | .draw _ _ _ | .group _ _ _ _ | .use _ _ | .stamp _ _ _ _ | .image _ _ | .label _ => true).toList =
        [.draw g (some fl) none] ∧ fl.rule = .nonzero ∧ subs = subpathsOf g := by
  unfold type3Stamp? at h
  cases isD1 with
  | false => simp at h
  | true =>
    refine ⟨rfl, ?_⟩
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · next g fl heq =>
      split at h
      · next hr =>
        simp only [Option.some.injEq] at h
        exact ⟨g, fl, heq, hr, h.symm⟩
      · simp at h
    · simp at h

/-- The loss an image's colour space carries (`spaceApprox`); a stencil
mask has none. -/
private def imageSpaceLoss (cx : Ctx) (dict : Obj) : Option String :=
  let get (k abbr : String) : Option Obj := (dict.get? k).orElse fun _ => dict.get? abbr
  if get "ImageMask" "IM" == some (.bool true) then none
  else (get "ColorSpace" "CS").bind (spaceApprox cx)

/-- A raster painted in the unit square of the current space: smoothed as
it is drawn (`smoothAt`), its colour space's loss named. -/
private def St.paintRaster (cx : Ctx) (st : St) (dict : Obj) (r : Raster) : St × Nat :=
  let r := smoothAt r st.gs.ctm
  let k := st.store.rasters.size
  let store := { st.store with rasters := st.store.rasters.push r }
  let store := match imageSpaceLoss cx dict with
    | some key => store.lose (.value key)
    | none => store
  ({ st with store } |>.emit (.image k Affine.unit), k)

/-- An inline image (§8.9.7) painted, or its loss named. -/
private def inlineImage (cx : Ctx) (st : St) (dict : Array (String × Obj)) (data : ByteArray) : St :=
  if st.hidden > 0 then st else
  match rasterOf cx (.dict dict) data (fillColor st) with
  | .ok r => (st.paintRaster cx (.dict dict) r).1
  | .error key => { st with store := st.store.lose (.resource key) }

mutual

/-- **Read a content stream's tokens** from `i`: an operand kept for the
operator after it, an operator read, an inline image painted. -/
public def runToks (cx : Ctx) (e : Entered cx.doc) (toks : Array Tok) (i : Nat) (st : St) : St :=
  if h : i < toks.size then
    let st := match toks[i] with
      | .val o => { st with ops := st.ops.push o }
      | .inline dict data => inlineImage cx { st with ops := #[] } dict data
      | .op name => { stepOp cx e name st with ops := #[] }
    runToks cx e toks (i + 1) st
  else st
termination_by (e.room, 3, toks.size - i)

/-- **One operator read** (ISO 32000-2 Annex A): `q` saves the graphics
state, `Q` restores the one saved last, and every other operator is
`stepRest`'s, which reads and writes the state but its stack: the stack
and the level it opened stand as they were. -/
private def stepOp (cx : Ctx) (e : Entered cx.doc) (name : String) (st : St) : St :=
  if name == "q" then { st with saved := st.saved.push (st.gs, st.frames.size), level := st.frames.size }
  else if name == "Q" then
    match st.saved.back? with
    | some (gs, k) =>
      let frames := st.frames
      let st := { st with frames := #[] }
      { st with gs, saved := st.saved.pop, frames := closeTo frames k
                level := (st.saved.pop.back?.map (·.2)).getD 1 }
    | none => st
  else
    -- Read before the step, so the state reaches it held once.
    let saved := st.saved
    let level := st.level
    { stepRest cx e name st with saved, level }
termination_by (e.room, 2, 1)

/-- Every operator but `q` and `Q`. -/
private def stepRest (cx : Ctx) (e : Entered cx.doc) (name : String) (st : St) : St :=
  let n := st.nums
  let num (i : Nat) : Rat := n[i]?.getD 0
  -- A coordinate in integers (`spOf_exact`: `spOfRat` of the number).
  let sps := st.ops.filterMap spOf
  let sp (i : Nat) : Sp := sps[i]?.getD 0
  let pt (i : Nat) : Pt := (sp i, sp (i + 1))
  match name with
  | "l" =>
    let p := pt 0
    { st with path := st.path.push (.lineTo p.1 p.2), cur := p }
  | "c" =>
    let p := pt 4
    { st with path := st.path.push (.curveTo (sp 0) (sp 1) (sp 2) (sp 3) p.1 p.2), cur := p }
  | "m" => st.moveTo (pt 0)
  | "h" => { st with path := st.path.push .close, cur := st.start }
  | "v" =>
    let p := pt 2
    { st with path := st.path.push (.curveTo st.cur.1 st.cur.2 (sp 0) (sp 1) p.1 p.2), cur := p }
  | "y" =>
    let p := pt 2
    { st with path := st.path.push (.curveTo (sp 0) (sp 1) p.1 p.2 p.1 p.2), cur := p }
  | "re" =>
    let x := sp 0
    let y := sp 1
    { st with path := st.path.push (.rect x y (sp 2) (sp 3)), cur := (x, y), start := (x, y) }
  | "f" | "F" => paintWith cx e st (some .nonzero) false false
  | "f*" => paintWith cx e st (some .evenOdd) false false
  | "S" => paintPath cx st none true false
  | "s" => paintPath cx st none true true
  | "B" => paintWith cx e st (some .nonzero) true false
  | "B*" => paintWith cx e st (some .evenOdd) true false
  | "b" => paintWith cx e st (some .nonzero) true true
  | "b*" => paintWith cx e st (some .evenOdd) true true
  | "n" => paintPath cx st none false false
  | "W" => { st with clip := some .nonzero }
  | "W*" => { st with clip := some .evenOdd }
  | "cm" => match affineOf n with
    | some m => st.concat m
    | none => st
  | "w" => { st with gs := { st.gs with width := sp 0 } }
  | "J" => { st with gs := { st.gs with
      cap := if num 0 == 1 then .round else if num 0 == 2 then .square else .butt } }
  | "j" => { st with gs := { st.gs with
      join := if num 0 == 1 then .round else if num 0 == 2 then .bevel else .miter } }
  | "M" => { st with gs := { st.gs with miter := num 0 } }
  | "d" =>
    match st.op 0 with
    | some (.arr ds) =>
      { st with gs := { st.gs with dash := ds.filterMap spOf, phase := ((st.op 1).bind spOf).getD 0 } }
    | _ => st
  | "gs" =>
    match st.op 0 with
    | some (.name g) => applyExtG cx st g
    | _ => st
  | "ri" | "i" => st
  | "g" | "G" | "rg" | "RG" | "k" | "K" =>
    let space : Space := if name == "g" || name == "G" then .gray
      else if name == "rg" || name == "RG" then .rgb else .cmyk
    let c := deviceColor space st.ops
    if name == "g" || name == "rg" || name == "k" then
      { st with gs := { st.gs with fillSpace := space, fill := .color c } }
    else { st with gs := { st.gs with strokeSpace := space, stroke := .color c } }
  | "cs" | "CS" =>
    let spaceObj := (st.op 0).getD (.name "DeviceGray")
    let space := spaceOf cx spaceObj
    let st := match space with
      | .lossy k _ => { st with store := st.store.lose (.value k) }
      | _ => st
    let st := match spaceApprox cx spaceObj with
      | some k => { st with store := st.store.lose (.value k) }
      | none => st
    let ink : Ink := match space with
      | .pattern _ => .pattern "" none
      | sp => .color (colorIn sp sp.initial)
    if name == "cs" then { st with gs := { st.gs with fillSpace := space, fill := ink } }
    else { st with gs := { st.gs with strokeSpace := space, stroke := ink } }
  | "sc" | "scn" | "SC" | "SCN" =>
    let fillOp := name == "sc" || name == "scn"
    let space := if fillOp then st.gs.fillSpace else st.gs.strokeSpace
    let ink : Ink := match space, st.ops.back? with
      | .pattern under, some (.name p) => .pattern p (under.map fun u => colorIn u st.ops.pop)
      | sp, _ => .color (colorIn sp st.ops)
    if fillOp then { st with gs := { st.gs with fill := ink } }
    else { st with gs := { st.gs with stroke := ink } }
  | "sh" => shadeOp cx st
  | "Do" =>
    match st.op 0 with
    | some (.name xName) => doXObject cx e xName st
    | _ => st
  | "BT" => { st with inText := true, tm := Affine.unit, tlm := Affine.unit }
  | "ET" =>
    let st := if st.words.isEmpty then st else st.emit (.words st.words)
    { st with inText := false, words := "" }
  | "Tc" => { st with gs := { st.gs with charSpace := num 0 } }
  | "Tw" => { st with gs := { st.gs with wordSpace := num 0 } }
  | "Tz" => { st with gs := { st.gs with hScale := num 0 / 100 } }
  | "TL" => { st with gs := { st.gs with leading := num 0 } }
  | "Ts" => { st with gs := { st.gs with rise := num 0 } }
  | "Tr" => { st with gs := { st.gs with render := (num 0).floor.toNat } }
  | "Tf" =>
    match st.op 0 with
    | some (.name fName) =>
      let size := ((st.op 1).bind ratOf).getD 0
      match resource cx "Font" fName with
      | some fo => { st with gs := { st.gs with font := some (fo, 0), size } }
      | none =>
        -- A name the resources do not hold shows nothing; a reader whose
        -- resources it misses can only say so.
        { st with gs := { st.gs with font := none, size }, store := st.store.lose (.resource "font-unresolved") }
    | _ => st
  | "Td" =>
    let tlm := st.tlm.compose ⟨1, 0, 0, 1, num 0 * 65536, num 1 * 65536⟩
    let st := if num 1 != 0 || num 0 > 0 then st.space else st
    { st with tlm, tm := tlm }
  | "TD" =>
    let tlm := st.tlm.compose ⟨1, 0, 0, 1, num 0 * 65536, num 1 * 65536⟩
    { st.space with tlm, tm := tlm, gs := { st.gs with leading := -(num 1) } }
  | "T*" =>
    let tlm := st.tlm.compose ⟨1, 0, 0, 1, 0, -st.gs.leading * 65536⟩
    { st.space with tlm, tm := tlm }
  | "Tm" => match affineOf n with
    | some m => { st.space with tlm := m, tm := m }
    | none => st
  | "Tj" =>
    match (st.op 0).bind PdfContentLex.strBytes? with
    | some s => showString cx e s st
    | none => st
  | "'" =>
    let tlm := st.tlm.compose ⟨1, 0, 0, 1, 0, -st.gs.leading * 65536⟩
    let st := { st.space with tlm, tm := tlm }
    match st.ops.back?.bind PdfContentLex.strBytes? with
    | some s => showString cx e s st
    | none => st
  | "\"" =>
    let st := { st with gs := { st.gs with wordSpace := num 0, charSpace := num 1 } }
    let tlm := st.tlm.compose ⟨1, 0, 0, 1, 0, -st.gs.leading * 65536⟩
    let st := { st.space with tlm, tm := tlm }
    match st.ops.back?.bind PdfContentLex.strBytes? with
    | some s => showString cx e s st
    | none => st
  | "TJ" =>
    match st.op 0 with
    | some (.arr items) => showArray cx e items.toList st
    | _ => st
  | "d0" | "d1" => st
  | "BMC" => { st with marks := st.marks.push false }
  | "BDC" =>
    let off := match st.op 0, st.op 1 with
      | some (.name "OC"), some (.name prop) =>
        match resource cx "Properties" prop with
        | some r => ocOff cx r
        | none => false
      | _, _ => false
    { st with marks := st.marks.push off, hidden := if off then st.hidden + 1 else st.hidden }
  | "EMC" =>
    match st.marks.back? with
    | some off => { st with marks := st.marks.pop, hidden := if off then st.hidden - 1 else st.hidden }
    | none => st
  | "MP" | "DP" => st
  | "BX" => { st with compat := st.compat + 1 }
  | "EX" => { st with compat := st.compat - 1 }
  | other =>
    if st.compat > 0 then st else { st with store := st.store.lose (.operator other) }
termination_by (e.room, 2, 0)

/-- A path painted, its fill a tiling pattern's tiles where the fill
names one (§8.7.3.1). -/
private def paintWith (cx : Ctx) (e : Entered cx.doc) (st : St) (fill : Option Rule) (stroke : Bool)
    (close : Bool) : St :=
  match fill, st.gs.fill with
  | some _, .pattern name _ =>
    match resource cx "Pattern" name with
    | some r =>
      let tiling := match (cx.doc.stream r).toOption.getD none with
        | some (d, _) => ((d.get? "PatternType").bind Obj.int?) == some 1
        | none => false
      if tiling then
        let st0 := if close && !st.path.isEmpty then { st with path := st.path.push .close } else st
        let (st1, tiles) := tileNodes cx e st0 r st0.geom
        paintPath cx st1 fill stroke false (some (tiles.getD #[]))
      else paintPath cx st fill stroke close
    | none => paintPath cx st fill stroke close
  | _, _ => paintPath cx st fill stroke close
termination_by (e.room, 1, 2)

/-- **A tiling pattern's tiles over a region** (§8.7.3): its cell read once
in pattern space as a symbol clipped to the cell's box, used at every step
its matrix carries across the region's box — at most `tileCap` tiles, past
which the loss is named. An uncoloured pattern is a loss. -/
private def tileNodes (cx : Ctx) (e : Entered cx.doc) (st : St) (pat : Obj) (region : Geom) :
    St × Option (Array (Node Run)) :=
  match pat with
  | .ref pn _ =>
    if h : cx.doc.lists pn = true ∧ pn ∉ e.list then
      match (cx.doc.stream pat).toOption.getD none with
      | none => (st, none)
      | some (pd, raw) =>
        if (((pd.get? "PaintType").bind Obj.int?).getD 1) != 1 then
          ({ st with store := st.store.lose (.resource "uncoloured-tiling") }, none)
        else
        let nums (k : String) : Array Rat := match (pd.get? k).bind fun x => (cx.doc.deref x).toOption with
          | some (.arr xs) => xs.filterMap fun x => (cx.doc.deref x).toOption.bind ratOf
          | some o => (ratOf o).toArray
          | none => #[]
        let m := (affineOf (nums "Matrix")).getD Affine.unit
        let bb := nums "BBox"
        let xs := ((nums "XStep")[0]?).getD 0
        let ys := ((nums "YStep")[0]?).getD 0
        let space := cx.base.compose m
        match Affine.inv? st.gs.ctm, PdfFilters.decode pd raw with
        | some invC, .ok (.bytes data) =>
          if bb.size != 4 || xs == 0 || ys == 0 then (st, none) else
          let q := invC.compose space
          let key := s!"tile|{pn}"
          let (st, k) := match st.store.forms.get? key with
            | some k => (st, k)
            | none =>
              let res := ((pd.get? "Resources").bind fun x => (cx.doc.deref x).toOption).getD cx.res
              let cx' : Ctx := { cx with res, base := space }
              let store := st.store
              let st := { st with store := Store.empty }
              let inner := runToks cx' (e.push pn h.1 h.2) (PdfContentLex.scan data) 0
                (St.initial (GState.initial space) store)
              let bx0 := spOfRat (min (bb[0]?.getD 0) (bb[2]?.getD 0))
              let bx1 := spOfRat (max (bb[0]?.getD 0) (bb[2]?.getD 0))
              let by0 := spOfRat (min (bb[1]?.getD 0) (bb[3]?.getD 0))
              let by1 := spOfRat (max (bb[1]?.getD 0) (bb[3]?.getD 0))
              let body := #[Node.group Affine.unit #[{ geom := .rect bx0 by0 (bx1 - bx0) (by1 - by0), rule := .nonzero }]
                Alpha.opaque inner.finish]
              let store := inner.store
              let k := store.symbols.size
              ({ st with store := { store with symbols := store.symbols.push body
                                               forms := store.forms.insert key k } }, k)
          match Affine.inv? q, region.hull with
          | some invQ, some box =>
            let pb := Box.image invQ box
            -- Tile `i` covers the cell moved by `i` steps; it meets the
            -- region where the open intervals overlap.
            let lo (v : Sp) (step : Rat) (cellHi : Rat) : Int := ((((v : Rat) / 65536) - cellHi) / step).floor + 1
            let hi (v : Sp) (step : Rat) (cellLo : Rat) : Int := ((((v : Rat) / 65536) - cellLo) / step).ceil - 1
            let sx := if xs < 0 then -xs else xs
            let sy := if ys < 0 then -ys else ys
            let cx0 := min (bb[0]?.getD 0) (bb[2]?.getD 0)
            let cx1 := max (bb[0]?.getD 0) (bb[2]?.getD 0)
            let cy0 := min (bb[1]?.getD 0) (bb[3]?.getD 0)
            let cy1 := max (bb[1]?.getD 0) (bb[3]?.getD 0)
            let i0 := lo pb.1.1 sx cx1
            let i1 := hi pb.2.1 sx cx0
            let j0 := lo pb.1.2 sy cy1
            let j1 := hi pb.2.2 sy cy0
            let ni := (i1 - i0 + 1).toNat
            let nj := (j1 - j0 + 1).toNat
            if ni * nj > tileCap then ({ st with store := st.store.lose (.budget "tiles") }, none) else
            let tiles := (List.range ni).foldl (fun acc (a : Nat) => (List.range nj).foldl (fun acc (b : Nat) =>
              let t : Affine := ⟨1, 0, 0, 1, ((i0 + a : Int) : Rat) * sx * 65536, ((j0 + b : Int) : Rat) * sy * 65536⟩
              acc.push (Node.use k (q.compose t))) acc) #[]
            (st, some tiles)
          | _, _ => (st, some #[])
        | none, _ => (st, some #[])
        | _, _ => ({ st with store := st.store.lose (.resource "tiling-data") }, none)
    else ({ st with store := st.store.lose (.budget "tiling-recursion") }, none)
  | _ => (st, none)
termination_by (e.room, 0, 0)
decreasing_by
  simp_wf
  apply Prod.Lex.left
  exact Entered.push_room_between e _ _ _

/-- A `TJ` array: strings shown, numbers moving the pen back by thousandths
of the font size. -/
private def showArray (cx : Ctx) (e : Entered cx.doc) (items : List Obj) (st : St) : St :=
  match items with
  | [] => st
  | o :: rest =>
    let st := match ratOf o with
      | some adj =>
        let st := st.advance (-(adj / 1000) * st.gs.size * st.gs.hScale)
        if adj < -200 then st.space else st
      | none =>
        match PdfContentLex.strBytes? o with
        | some s => showString cx e s st
        | none => st
    showArray cx e rest st
termination_by (e.room, 1, items.length + 1)

/-- A string shown (§9.4.3): each code's glyph stamped at the pen, the pen
advanced by its width, the character and word spacing, and the horizontal
scale. -/
public def showString (cx : Ctx) (e : Entered cx.doc) (s : ByteArray) (st : St) : St :=
  -- Reading the font and painting a glyph change the store and the frames,
  -- never the words or the hidden depth: those are kept by construction,
  -- what `words_exact` reads.
  let (loaded, fo) := fontOf cx st
  let st := { loaded with words := st.words, hidden := st.hidden }
  match fo with
  | none =>
    -- Text shown with no font set shows nothing in any reader.
    if st.hidden > 0 || s.isEmpty then st else { st with store := st.store.lose (.font "unset") }
  | some (font, key) =>
    (font.codes? s).foldl (fun st code =>
      let st := if st.hidden > 0 then st else st.addWords code.text
      let words := st.words
      let hidden := st.hidden
      let painted := if hidden > 0 then st else
        match font.program, code.glyph with
        | .ink src m, some (.gid g) =>
          let gm := fontMatrix ((src.cffMatrix g).getD m)
          let (st, o) := glyphOutline st key src g
          match o with
          | some k => stampGlyph cx st k gm .nonzero
          | none => st
        | .type3 _ m _, some (.proc pn) => type3Glyph cx e font key pn (fontMatrix m) st
        | _, _ => st
      let st := { painted with words, hidden }
      let w : Rat := match font.program with
        | .type3 _ m _ => code.width * (m[0]?.getD (mkRat 1 1000)) * 1000
        | _ => code.width
      let space : Rat := if code.bytes == 1 && code.code == 32 then st.gs.wordSpace else 0
      st.advance (((w / 1000) * st.gs.size + st.gs.charSpace + space) * st.gs.hScale)) st
termination_by (e.room, 1, 0)

/-- A Type 3 glyph (§9.6.4): its procedure read in glyph space with the
graphics state in force — the frame the glyph's own, the soft mask's box
left to where the glyph is placed. A `d1` procedure is a stencil whose
colours are the text's: read once with neutral colours, its one nonzero fill
(`type3Stamp?`) is a stamp, painted with the text's paints wherever it is
shown. Any other procedure is a symbol of what it paints, read once per
inherited state, since a `d0` glyph paints with whatever it does not set
itself — colours, line width, dash, alphas. -/
private def type3Glyph (cx : Ctx) (e : Entered cx.doc) (font : PdfFont.Loaded) (key : Nat)
    (proc : String) (fm : Affine) (st : St) : St :=
  let inherited := { st.gs with ctm := Affine.unit, maskClip := none }
  let symKey := s!"t3|{key}|{proc}|{stateKey inherited}"
  let place (st : St) (r : Bool × Nat) : St :=
    if r.1 then stampGlyph cx st r.2 fm .nonzero
    else st.emit (.use r.2 ((textFrame st).compose fm))
  let first := st.store.type3.get? (key, proc)
  let cached : Option (Option (Bool × Nat)) := match first with
    | some (some (false, _)) => (st.store.forms.get? symKey).map fun k => some (false, k)
    | some (some (true, _)) | some none | none => first
  match cached with
  | some (some r) => place st r
  | some none => st
  | none =>
    match font.program with
    | .type3 procs _ res =>
      match procs.find? (·.1 == proc) with
      | some (_, .ref pn _) =>
        if h : cx.doc.lists pn = true ∧ pn ∉ e.list then
          match (cx.doc.stream (.ref pn 0)).toOption.getD none with
          | some (dict, raw) =>
            match PdfFilters.decode dict raw with
            | .ok (.bytes data) =>
              let toks := PdfContentLex.scan data
              let cx' : Ctx := { cx with res := res.getD cx.res, base := Affine.unit }
              let isD1 := toks.any fun t => match t with
                | .op "d1" => true
                | _ => false
              let black : Ink := .color { r := 0, g := 0, b := 0 }
              -- The store goes with each reading, held once.
              let store := st.store
              let st := { st with store := Store.empty }
              let (stencil, store) : Option (Array Subpath) × Store := if isD1 then
                  let neutral := { inherited with fill := black, stroke := black, ca := Alpha.opaque
                                                  cA := Alpha.opaque, mask := Alpha.opaque }
                  let inner := runToks cx' (e.push pn h.1 h.2) toks 0 (St.initial neutral store)
                  (type3Stamp? true inner.finish, inner.store)
                else (none, store)
              match stencil with
              | some subs =>
                -- A procedure that paints nothing (a space) is a glyph with no ink.
                if subs.isEmpty then
                  { st with store := { store with type3 := store.type3.insert (key, proc) none } }
                else
                  let r : Bool × Nat := (true, store.outlines.size)
                  let store := { store with outlines := store.outlines.push subs }
                  place { st with store := { store with type3 := store.type3.insert (key, proc) (some r) } } r
              | none =>
                let inner := runToks cx' (e.push pn h.1 h.2) toks 0 (St.initial inherited store)
                let body := inner.finish
                let store := inner.store
                if body.isEmpty then
                  { st with store := { store with type3 := store.type3.insert (key, proc) none } }
                else
                  let r : Bool × Nat := (false, store.symbols.size)
                  let store := { store with symbols := store.symbols.push body
                                            forms := store.forms.insert symKey store.symbols.size }
                  place { st with store := { store with type3 := store.type3.insert (key, proc) (some r) } } r
            | _ => { st with store := { (st.store.lose (.font "type3-procedure")) with
                       type3 := st.store.type3.insert (key, proc) none } }
          | none => st
        else { st with store := st.store.lose (.budget "type3-recursion") }
      | _ => st
    | _ => st
termination_by (e.room, 0, 0)
decreasing_by
  all_goals
    simp_wf
    apply Prod.Lex.left
    exact Entered.push_room_between e _ _ _

/-- An XObject painted (§8.8, §8.10): an image as a raster in the unit
square of the current space; a form read in its own space under its matrix
— an isolated transparency group with the alpha in force as the group's,
and the alpha reset inside it — once per inherited state, every later
`Do` with that state using the first reading's symbol. -/
private def doXObject (cx : Ctx) (e : Entered cx.doc) (xName : String) (st : St) : St :=
  match resource cx "XObject" xName with
  | some (.ref xn _) =>
    if st.hidden > 0 then st else
    match (cx.doc.stream (.ref xn 0)).toOption.getD none with
    | none => { st with store := st.store.lose (.resource "xobject-unresolved") }
    | some (dict, raw) =>
      if (dict.get? "OC").any (ocOff cx) then st else
      match dict.get? "Subtype" with
      | some (.name "Image") =>
        let isMask := dict.get? "ImageMask" == some (.bool true)
        let ikey := if isMask then s!"{xn}|{(fillColor st).map Ir.Color.css}" else toString xn
        match st.store.images.get? ikey with
        | some (some k) => st.emit (.image k Affine.unit)
        | some none => st
        | none =>
          match rasterOf cx dict raw (fillColor st) with
          | .ok r =>
            let (st, k) := st.paintRaster cx dict r
            { st with store := { st.store with images := st.store.images.insert ikey (some k) } }
          | .error key =>
            { st with store := { (st.store.lose (.resource key)) with images := st.store.images.insert ikey none } }
      | some (.name "Form") =>
        if h : cx.doc.lists xn = true ∧ xn ∉ e.list then
          let m := match (dict.get? "Matrix").bind fun x => (cx.doc.deref x).toOption with
            | some (.arr xs) => (affineOf (xs.filterMap fun x => (cx.doc.deref x).toOption.bind ratOf)).getD Affine.unit
            | _ => Affine.unit
          let group := (dict.get? "Group").bind fun x => (cx.doc.deref x).toOption
          let transparency := group.any fun g => g.get? "S" == some (.name "Transparency")
          let st := if group.any (fun g => g.get? "K" == some (.bool true)) then
              { st with store := st.store.lose (.property "knockout") } else st
          let alpha := if transparency then st.gs.fillAlpha else Alpha.opaque
          let key := s!"{xn}|{stateKey st.gs}"
          match st.store.forms.get? key with
          | some k => st.emit (.group Affine.unit #[] alpha #[.use k m])
          | none =>
            let res := ((dict.get? "Resources").bind fun x => (cx.doc.deref x).toOption).getD cx.res
            match PdfFilters.decode dict raw with
            | .ok (.bytes data) =>
              let toks := PdfContentLex.scan data
              let ctm := st.gs.ctm.compose m
              let cx' : Ctx := { cx with res, base := ctm }
              -- The mask's box clips the form where it is painted, once.
              let gs := { st.gs with ctm, maskClip := none }
              let gs := if transparency then { gs with ca := Alpha.opaque, cA := Alpha.opaque, mask := Alpha.opaque } else gs
              let store := st.store
              let st := { st with store := Store.empty }
              let inner := runToks cx' (e.push xn h.1 h.2) toks 0 (St.initial gs store)
              let body := inner.finish
              let store := inner.store
              let clips := bboxClip dict cx.doc body store
              let body := if clips.isEmpty then body else #[.group Affine.unit clips Alpha.opaque body]
              -- The reading is kept as a symbol: a later `Do` of this form
              -- with this state uses it.
              let k := store.symbols.size
              let store := { store with symbols := store.symbols.push body, forms := store.forms.insert key k }
              { st with store } |>.emit (.group Affine.unit #[] alpha #[.use k m])
            | _ => { st with store := st.store.lose (.resource "form-data") }
        else { st with store := st.store.lose (.budget "form-recursion") }
      | _ => { st with store := st.store.lose (.resource "xobject-subtype") }
  | _ => if st.hidden > 0 then st else { st with store := st.store.lose (.resource "xobject-unresolved") }
termination_by (e.room, 1, 1)
decreasing_by
  simp_wf
  apply Prod.Lex.left
  exact Entered.push_room_between e _ _ _

end

/-! ## The graphics-state stack -/

/-- One token's reading, as `runToks` takes it. -/
public def tokStep (cx : Ctx) (e : Entered cx.doc) (st : St) (t : Tok) : St :=
  match t with
  | .val o => { st with ops := st.ops.push o }
  | .inline dict data => inlineImage cx { st with ops := #[] } dict data
  | .op name => { stepOp cx e name st with ops := #[] }

/-- `runToks` is the fold of `tokStep` over the tokens it has left. -/
private theorem runToks_foldl (cx : Ctx) (e : Entered cx.doc) (toks : Array Tok) :
    ∀ (i : Nat) (st : St), runToks cx e toks i st = (toks.toList.drop i).foldl (tokStep cx e) st := by
  intro i
  induction h : toks.size - i generalizing i with
  | zero =>
    intro st
    rw [runToks]
    have hi : ¬ i < toks.size := by omega
    simp only [hi, ↓reduceDIte]
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro st
    rw [runToks]
    have hi : i < toks.size := by omega
    have hl : i < toks.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hl]
    simp only [hi, ↓reduceDIte, List.foldl_cons]
    rw [ih (i + 1) (by omega)]
    simp only [Array.getElem_toList]
    rfl

private theorem emit_saved (st : St) (nd : Node Run) :
    (st.emit nd).saved = st.saved ∧ (st.emit nd).gs = st.gs := by
  unfold St.emit
  by_cases h : st.hidden > 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    cases hb : st.frames.back? <;> exact ⟨rfl, rfl⟩

private theorem inlineImage_saved (cx : Ctx) (st : St) (dict : Array (String × Obj)) (data : ByteArray) :
    (inlineImage cx st dict data).saved = st.saved := by
  unfold inlineImage
  split
  · rfl
  · split
    · exact (emit_saved _ _).1
    · rfl

/-- No token but `q` and `Q` touches the stack. -/
private theorem tokStep_saved (cx : Ctx) (e : Entered cx.doc) (st : St) (t : Tok)
    (hq : t ≠ .op "q") (hQ : t ≠ .op "Q") : (tokStep cx e st t).saved = st.saved := by
  cases t with
  | val o => rfl
  | inline dict data =>
    simp only [tokStep]
    exact inlineImage_saved cx _ dict data
  | op name =>
    have h1 : (name == "q") = false := by simpa using fun h => hq (by rw [h])
    have h2 : (name == "Q") = false := by simpa using fun h => hQ (by rw [h])
    simp only [tokStep]
    rw [stepOp]
    simp [h1, h2]

/-- How deep a run of tokens leaves the stack from depth `d`: one deeper at
each `q`, one shallower at each `Q`; `none` when a `Q` would pop below the
run's start. -/
@[expose] public def qDepth? : List Tok → Nat → Option Nat
  | [], d => some d
  | .op n :: ts, d =>
    if n == "q" then qDepth? ts (d + 1)
    else if n == "Q" then (if d = 0 then none else qDepth? ts (d - 1))
    else qDepth? ts d
  | .val _ :: ts, d => qDepth? ts d
  | .inline _ _ :: ts, d => qDepth? ts d

/-- **A run reaches no deeper into the stack than it may** — the entries
below the `d` it may pop are untouched, and it leaves its final depth's
worth above them. -/
private theorem foldl_saved (cx : Ctx) (e : Entered cx.doc) :
    ∀ (ts : List Tok) (d d' : Nat) (st : St), d ≤ st.saved.size → qDepth? ts d = some d' →
      ∃ ext : List (GState × Nat),
        (ts.foldl (tokStep cx e) st).saved.toList = st.saved.toList.take (st.saved.size - d) ++ ext ∧
        ext.length = d' := by
  intro ts
  induction ts with
  | nil =>
    intro d d' st hd h
    simp only [qDepth?, Option.some.injEq] at h
    subst h
    refine ⟨st.saved.toList.drop (st.saved.size - d), ?_, ?_⟩
    · simp
    · simp; omega
  | cons t ts ih =>
    intro d d' st hd h
    simp only [List.foldl_cons]
    cases t with
    | op n =>
      by_cases hq : n = "q"
      · subst hq
        simp only [qDepth?, beq_self_eq_true, ↓reduceIte] at h
        have hs : (tokStep cx e st (.op "q")).saved = st.saved.push (st.gs, st.frames.size) := by
          simp only [tokStep]; rw [stepOp]; simp
        obtain ⟨ext, he, hl⟩ := ih (d + 1) d' _ (by rw [hs]; simp; omega) h
        rw [hs] at he
        refine ⟨ext, ?_, hl⟩
        rw [he]
        simp only [Array.toList_push, Array.size_push]
        rw [List.take_append_of_le_length (by simp)]
        congr 2
        omega
      · by_cases hQ : n = "Q"
        · subst hQ
          simp only [qDepth?, beq_self_eq_true, ↓reduceIte, show ("Q" == "q") = false from rfl,
            Bool.false_eq_true] at h
          split at h
          · exact absurd h (by simp)
          · next hd0 =>
            obtain ⟨top, htop⟩ : ∃ top, st.saved.back? = some top := by
              cases hb : st.saved.back? with
              | some top => exact ⟨top, rfl⟩
              | none =>
                exfalso
                have : st.saved.size = 0 := by simpa [Array.back?_eq_none_iff] using hb
                omega
            have hs : (tokStep cx e st (.op "Q")).saved = st.saved.pop := by
              simp only [tokStep]; rw [stepOp]; simp [htop]
            obtain ⟨ext, he, hl⟩ := ih (d - 1) d' _ (by rw [hs]; simp; omega) h
            rw [hs] at he
            refine ⟨ext, ?_, hl⟩
            rw [he]
            simp only [Array.toList_pop, Array.size_pop]
            rw [List.dropLast_eq_take, List.take_take]
            rw [show min (st.saved.size - 1 - (d - 1)) (st.saved.toList.length - 1) = st.saved.size - 1 - (d - 1) by
              simp]
            congr 2
            omega
        · have hs := tokStep_saved cx e st (.op n) (by simpa using hq) (by simpa using hQ)
          have h' : qDepth? ts d = some d' := by
            simp only [qDepth?] at h
            have h1 : (n == "q") = false := by simpa using hq
            have h2 : (n == "Q") = false := by simpa using hQ
            simpa [h1, h2] using h
          obtain ⟨ext, he, hl⟩ := ih d d' _ (by rw [hs]; exact hd) h'
          rw [hs] at he
          exact ⟨ext, he, hl⟩
    | val o =>
      have hs := tokStep_saved cx e st (.val o) (by simp) (by simp)
      obtain ⟨ext, he, hl⟩ := ih d d' _ (by rw [hs]; exact hd) (by simpa [qDepth?] using h)
      rw [hs] at he
      exact ⟨ext, he, hl⟩
    | inline dict data =>
      have hs := tokStep_saved cx e st (.inline dict data) (by simp) (by simp)
      obtain ⟨ext, he, hl⟩ := ih d d' _ (by rw [hs]; exact hd) (by simpa [qDepth?] using h)
      rw [hs] at he
      exact ⟨ext, he, hl⟩

/-- `Q` restores the state the stack's top saved, and pops it. -/
private theorem tokStep_Q (cx : Ctx) (e : Entered cx.doc) (st : St) (g : GState) (k : Nat)
    (h : st.saved.back? = some (g, k)) :
    (tokStep cx e st (.op "Q")).gs = g ∧ (tokStep cx e st (.op "Q")).saved = st.saved.pop := by
  simp only [tokStep]
  rw [stepOp]
  simp [h]

/-- **A `q … Q` pair restores the graphics state** (`_id`, §8.4.2): reading
`q`, then a run whose own `q` and `Q` pair up, then `Q`, leaves the graphics
state, and the stack of states saved before it, as they were — whatever the
run between painted, clipped, transformed or set. -/
public theorem gsave_restore_id (cx : Ctx) (e : Entered cx.doc) (inner : List Tok)
    (h : qDepth? inner 0 = some 0) (st : St) :
    let st' := runToks cx e (#[.op "q"] ++ inner.toArray ++ #[.op "Q"]) 0 st
    st'.gs = st.gs ∧ st'.saved = st.saved := by
  intro st'
  have hst' : st' = (.op "Q" :: []).foldl (tokStep cx e)
      ((inner).foldl (tokStep cx e) (tokStep cx e st (.op "q"))) := by
    show runToks cx e _ 0 st = _
    rw [runToks_foldl]
    simp
  have hq : (tokStep cx e st (.op "q")).saved = st.saved.push (st.gs, st.frames.size) := by
    simp only [tokStep]; rw [stepOp]; simp
  let st1 := tokStep cx e st (.op "q")
  obtain ⟨ext, he, hl⟩ := foldl_saved cx e inner 0 0 st1 (Nat.zero_le _) h
  have hl0 : ext = [] := List.eq_nil_of_length_eq_zero hl
  subst hl0
  have hinner : (inner.foldl (tokStep cx e) st1).saved = st.saved.push (st.gs, st.frames.size) := by
    apply Array.toList_inj.mp
    rw [he, List.append_nil, Nat.sub_zero]
    show List.take (tokStep cx e st (.op "q")).saved.size (tokStep cx e st (.op "q")).saved.toList = _
    rw [hq, List.take_of_length_le (by simp)]
  have hback : (inner.foldl (tokStep cx e) st1).saved.back? = some (st.gs, st.frames.size) := by
    rw [hinner]; simp
  obtain ⟨hg, hs⟩ := tokStep_Q cx e _ _ _ hback
  rw [hst']
  simp only [List.foldl_cons, List.foldl_nil]
  exact ⟨hg, by rw [hs, hinner]; simp⟩

/-! ## The words a figure says -/

/-- The text a string's codes mean, in order. -/
@[expose] public def codesText (codes : Array PdfFont.Code) : String :=
  String.join (codes.toList.map (·.text))

private theorem fold_words (f : St → PdfFont.Code → St)
    (hf : ∀ st code, (f st code).words = st.words ++ (if st.hidden > 0 then "" else code.text) ∧
      (f st code).hidden = st.hidden) :
    ∀ (codes : List PdfFont.Code) (st : St), (codes.foldl f st).words =
      st.words ++ (if st.hidden > 0 then "" else String.join (codes.map (·.text))) ∧
      (codes.foldl f st).hidden = st.hidden := by
  intro codes
  induction codes with
  | nil => intro st; simp [String.join_nil]
  | cons c cs ih =>
    intro st
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := hf st c
    obtain ⟨h3, h4⟩ := ih (f st c)
    refine ⟨?_, h4.trans h2⟩
    rw [h3, h1, h2]
    by_cases hh : st.hidden > 0
    · simp [hh]
    · simp [hh, String.join_cons, List.map_cons, String.append_assoc]

/-- **A shown string says its codes' text** (`_exact`, §9.10): a string
shown in visible content adds to the words, in order, the text each of its
codes means through the font — its `ToUnicode` entry, else its glyph name —
and in hidden optional content adds none; reading the font and painting
the glyphs never touch the words. -/
public theorem words_exact (cx : Ctx) (e : Entered cx.doc) (s : ByteArray) (st : St) :
    (showString cx e s st).words = st.words ++
      (match (fontOf cx st).2 with
       | none => ""
       | some (font, _) => if st.hidden > 0 then "" else codesText (font.codes? s)) := by
  rw [showString]
  rcases hf : fontOf cx st with ⟨loaded, fo⟩
  simp only
  rcases fo with _ | ⟨font, key⟩
  · simp only [String.append_empty]
    split <;> rfl
  · simp only [codesText]
    rw [← Array.foldl_toList]
    have step : ∀ (st' : St) (code : PdfFont.Code),
        let st'' := if st'.hidden > 0 then st' else st'.addWords code.text
        st''.words = st'.words ++ (if st'.hidden > 0 then "" else code.text) ∧ st''.hidden = st'.hidden := by
      intro st' code
      simp only
      split
      · simp
      · unfold St.addWords
        split <;> simp_all
    refine (fold_words _ ?_ (font.codes? s).toList _).1.trans ?_
    · intro st' code
      obtain ⟨h1, h2⟩ := step st' code
      simp only [St.advance]
      exact ⟨h1, h2⟩
    · simp

/-! ## A page as a figure -/

/-- The optional-content groups a document's default configuration turns
off (§8.11.4.3). -/
private def offGroups (doc : Doc) : Array Nat :=
  match (doc.get doc.root).toOption with
  | some (cat, _) =>
    match (doc.field cat "OCProperties").toOption.getD none with
    | some ocp =>
      match (doc.field ocp "D").toOption.getD none with
      | some dflt =>
        match (doc.field dflt "OFF").toOption.getD none with
        | some (.arr xs) => xs.filterMap fun x => match x with
          | .ref n _ => some n
          | _ => none
        | _ => #[]
      | none => #[]
    | none => #[]
  | none => #[]

/-- What importing a page returns: the figure, and the page's one-based
number. -/
public structure Imported where
  figure : Figure Run
  page : Nat
  deriving Inhabited

/-- A page's content read in its default space as a figure in `box`,
clipped to it, its losses named. -/
private def figureOf (doc : Doc) (page : PdfRead.Page) (box : Box) (content : ByteArray) : Figure Run :=
  let res := ((page.resources.map fun r => (doc.deref r).toOption.getD .null)).getD (.dict #[])
  let cx : Ctx := { doc, res, base := Affine.unit, off := offGroups doc, box }
  let toks := PdfContentLex.scan content
  let e : Entered doc := { list := [], nodup := List.nodup_nil, listed := fun _ h => by cases h }
  let st := runToks cx e toks 0 (St.initial (GState.initial Affine.unit) Store.empty)
  let s := st.store
  { box, clipToBox := true, nodes := st.finish, outlines := s.outlines, symbols := s.symbols
    rasters := s.rasters, title := none, losses := s.losses }

/-- **A PDF page as a figure** (ISO 32000-2 §8, §9): its box — the page's
(`Doc.pageBox`), as the PDF backend places it (`PdfRead.readForm`) —
clipping, its content read in the page's default space, its losses named.
A rotated page is refused, as the PDF backend refuses it. -/
public def importPage (bytes : ByteArray) (sel : PdfRead.PageSelection := .first) :
    Except String Imported := do
  let doc ← Doc.ofBytes bytes
  -- §7.6: an encrypted file's strings and streams are ciphertext; reading
  -- them as content would draw noise.
  if (doc.trailer.get? "Encrypt").isSome then
    throw "the PDF is encrypted; its content cannot be read"
  let (num, page) ← doc.page sel
  let (x0, y0, x1, y1) ← doc.pageBox page
  doc.unrotated page
  let content ← doc.content page
  return { page := num, figure := figureOf doc page ((x0, y0), (x1, y1)) content }

/-- **The figure's box is the page's** (`_exact`): an imported figure
stands in the page box (`Doc.pageBox`) of the page it was read from. -/
public theorem import_box_exact (b : ByteArray) (sel : PdfRead.PageSelection) (imp : Imported)
    (h : importPage b sel = .ok imp) :
    ∃ d n p, Doc.ofBytes b = .ok d ∧ d.page sel = .ok (n, p) ∧
      d.pageBox p = .ok (imp.figure.box.1.1, imp.figure.box.1.2, imp.figure.box.2.1, imp.figure.box.2.2) := by
  unfold importPage at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hd : Doc.ofBytes b with
  | error e => simp [hd] at h
  | ok d =>
    simp only [hd] at h
    split at h
    · simp at h
    · cases hp : d.page sel with
      | error e => simp [hp] at h
      | ok np =>
        obtain ⟨n, p⟩ := np
        simp only [hp] at h
        cases hb : d.pageBox p with
        | error e => simp [hb] at h
        | ok box =>
          obtain ⟨x0, y0, x1, y1⟩ := box
          simp only [hb] at h
          cases hu : d.unrotated p with
          | error e => simp [hu] at h
          | ok u =>
            simp only [hu] at h
            cases hc : d.content p with
            | error e => simp [hc] at h
            | ok c =>
              simp only [hc, Except.ok.injEq] at h
              subst h
              exact ⟨d, n, p, rfl, hp, by simp [figureOf, hb]⟩

/-- **A PDF figure's two faces stand in one box** (`_agree`): the box the
PDF backend places the page's form in (`PdfRead.readForm`) and the box the
web face's figure is drawn in — its standalone SVG's viewBox — are one
reading of the page (`Doc.pageBox`), so the two artifacts reserve the same
extent and aspect for the figure. -/
public theorem _root_.LeanTex.Core.Gfx.pdfHtml_box_agree (b : ByteArray) (sel : PdfRead.PageSelection)
    (f : { f : PdfRead.Form // f.wf }) (imp : Imported)
    (hf : PdfRead.readForm b sel = .ok f) (hi : importPage b sel = .ok imp) :
    imp.figure.box = ((f.1.x0, f.1.y0), (f.1.x1, f.1.y1)) := by
  obtain ⟨d, n, p, hd, hp, hb⟩ := PdfRead.readForm_box_exact b sel f hf
  obtain ⟨d', n', p', hd', hp', hb'⟩ := import_box_exact b sel imp hi
  rw [hd] at hd'
  cases hd'
  rw [hp] at hp'
  cases hp'
  rw [hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨h1, h2, h3, h4⟩ := hb'
  ext <;> simp [h1, h2, h3, h4]

end LeanTex.Core.PdfGfx
