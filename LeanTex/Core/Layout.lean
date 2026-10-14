module

import Std.Data.HashSet
import Init.Internal.Order.While
import Init.Data.Range.Lemmas
import Init.Data.List.Monadic
public import LeanTex.Core.Dim
public import LeanTex.Core.Font
public import LeanTex.Core.Hyphen
public import LeanTex.Core.Ir
public import LeanTex.Core.GfxPicture
import LeanTex.Core.Oklab
import LeanTex.Core.Listing
import LeanTex.Core.ListMark
public import LeanTex.Core.Diag
import all LeanTex.Core.Diag
public import LeanTex.Core.Struct
import LeanTex.Core.Loop
import LeanTex.Core.Layout.GlyphBounds
public import LeanTex.Core.Layout.LabelAudit
import LeanTex.Core.LoopProgress

namespace LeanTex.Core.Layout

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Ir

/-- The per-level list indent: 1.5 em of the base size,
as classes.dtx sets its leftmargin stack in ems. -/
public def listIndentFor (base : Sp) : Sp := base * 3 / 2

public def frameBodySkip (hasTitle : Bool) (valign : VAlign) (size : Sp) : Sp :=
  (Ir.frameBodySkip hasTitle valign).resolve size 0

public theorem frameBodySkip_projects (hasTitle : Bool) (valign : VAlign) (size : Sp) :
    frameBodySkip hasTitle valign size = (Ir.frameBodySkip hasTitle valign).resolve size 0 := by
  simp only [frameBodySkip]

public structure Geom where
  pageW : Sp := pt 612
  pageH : Sp := pt 792
  hmargin : Sp := inch 1
  vmargin : Sp := inch 1
  fontSize : Sp := Ir.baseFontSize
  /-- TeX's `\topskip` (TeXbook ch. 15); `none` on a frame page, which beamer sets as one box. -/
  topskip : Option Sp := none
  parskip : SymGlue := Ir.parskipDefault Ir.baseFontSize
  /-- The `\parskip` TeX adds after a trivlist's `\topsep`: the
  declared parskip, else the standard classes' `0pt plus 1pt`. -/
  texParskip : SymGlue := Ir.texParskipDefault
  /-- The list indent of a lineage whose class declares no `\leftmargin` stack. -/
  listIndent : Sp := listIndentFor Ir.baseFontSize
  leading : Nat := 1000
  hyphenate : Bool := true
  justify : Bool := true
  /-- Whether lines hang ragged from the right edge of the measure, as `\raggedleft` sets them. -/
  flushRight : Bool := false
  /-- Whether boundary glyphs protrude into the margin (microtype's character protrusion). -/
  protrude : Bool := true
  /-- Whether font boxes may expand within ±`expandLimit` (microtype's font expansion). -/
  expand : Bool := true
  flushBottom : Bool := false
  /-- Bleed past the trim edge, for the PDF writer; layout works in trim coordinates. -/
  bleed : Sp := 0
  /-- Whether the pages ship printer's cut marks (`cutMarks`). -/
  marks : Bool := false
  markGap : Sp := Ir.cutMarkGap
  markThick : Sp := Ir.cutMarkThickness
  /-- How far inside the medium the trim cut by the
  document's own drawn marks lies (`drawnTrim`). -/
  trimInset : Sp := 0
  /-- The band a page footer reserves above the bottom margin
  (`furnitureBand`); zero when the margin holds it. -/
  footBand : Sp := 0
  /-- The band a running head reserves below the top margin
  (`furnitureBand`); zero when the margin holds it. -/
  headBand : Sp := 0
  /-- The size ladder in force (`Ir.PageSpec.scale`), through which named size runs resolve. -/
  scale : List (String × Nat) := Ir.sizeScale
  /-- The skip column in force (`Ir.PageSpec.skipScale`): each named step's `\baselineskip`. -/
  skips : List (String × Nat) := Ir.sizeSkipScale
  /-- Whether ragged lines fill first, as LaTeX's `\@flushglue` sets a `\raggedright` scope. -/
  raggedFil : Bool := false
  /-- beamer's `\textheight` on a frame whose pages carry the footline; `none` elsewhere. -/
  frameTextHeight : Option Sp := none
  deriving Repr

public def Geom.textWidth (g : Geom) : Sp := g.pageW - 2 * g.hmargin

public def Geom.bodyBottom (g : Geom) : Sp := g.pageH - g.vmargin - g.footBand

public def Geom.bodyTop (g : Geom) : Sp := g.vmargin + g.headBand

/-- One side's running furniture: `edge` runs from the page edge to its nearest
ink, and `band` is what its ink and body-side gap need beyond the margin. -/
public structure FurnBand where
  edge : Sp
  band : Sp
  deriving Repr

/-- One side's edge gap: what the margin leaves after the ink
and a declared gap, floored at zero, else half the margin. -/
public def furnEdge (vmargin ink : Sp) (gap : Option Sp) : Sp :=
  match gap with
  | some g => max 0 (vmargin - ink - g)
  | none => vmargin / 2

public def furnitureBand (vmargin ink : Sp) (gap : Option Sp) : FurnBand :=
  { edge := furnEdge vmargin ink gap
    band := max 0 (furnEdge vmargin ink gap + ink + gap.getD inkClearance - vmargin) }

public def furnHeadY (b : FurnBand) (ascent : Sp) : Sp := b.edge + ascent

public def furnFootY (b : FurnBand) (pageH descent : Sp) : Sp := pageH - b.edge - descent

/-- The foot line's baseline under a declared `\footskip`, baseline to
baseline below the text area's floor (ltpage.dtx, ltoutput.dtx). -/
public def latexFootY (g : Geom) (footskip : Sp) : Sp := g.bodyBottom + footskip

private theorem furn_reserves (vm ink req edge : Int) :
    edge + ink + req ≤ vm + max 0 (edge + ink + req - vm) := by
  omega

private theorem furn_reserves_below (pageH vm ink req edge band : Int)
    (h : edge + ink + req ≤ vm + band) :
    pageH - vm - band + ink + req ≤ pageH - edge := by
  omega

public theorem furniture_band_reserves (vmargin ink : Sp) (gap : Option Sp) :
    (furnitureBand vmargin ink gap).edge + ink + gap.getD inkClearance
      ≤ vmargin + (furnitureBand vmargin ink gap).band := by
  simp only [furnitureBand]
  exact furn_reserves vmargin ink (gap.getD inkClearance) (furnEdge vmargin ink gap)

public theorem bodyTop_clears_head (g : Geom) (ink : Sp) (gap : Option Sp)
    (h : g.headBand = (furnitureBand g.vmargin ink gap).band) :
    (furnitureBand g.vmargin ink gap).edge + ink + gap.getD inkClearance ≤ g.bodyTop := by
  simp only [Geom.bodyTop]
  rw [h]
  exact furniture_band_reserves g.vmargin ink gap

public theorem bodyBottom_clears_footer (g : Geom) (ink : Sp) (gap : Option Sp)
    (h : g.footBand = (furnitureBand g.vmargin ink gap).band) :
    g.bodyBottom + ink + gap.getD inkClearance
      ≤ g.pageH - (furnitureBand g.vmargin ink gap).edge := by
  simp only [Geom.bodyBottom]
  rw [h]
  exact furn_reserves_below g.pageH g.vmargin ink (gap.getD inkClearance)
    (furnitureBand g.vmargin ink gap).edge (furnitureBand g.vmargin ink gap).band
    (furniture_band_reserves g.vmargin ink gap)

private theorem furn_symmetric (pageH vm a d edge band : Int) :
    (edge + a) - a = pageH - ((pageH - edge - d) + d) ∧
    (vm + band) - ((edge + a) + d) =
      ((pageH - edge - d) - a) - (pageH - vm - band) := by
  omega

public theorem furniture_symmetric (g : Geom) (a d : Sp) (b : FurnBand)
    (hh : g.headBand = b.band) (hf : g.footBand = b.band) :
    furnHeadY b a - a = g.pageH - (furnFootY b g.pageH d + d) ∧
    g.bodyTop - (furnHeadY b a + d) =
      (furnFootY b g.pageH d - a) - g.bodyBottom := by
  simp only [furnHeadY, furnFootY, Geom.bodyTop, Geom.bodyBottom, hh, hf]
  exact furn_symmetric g.pageH g.vmargin a d b.edge b.band

private theorem furn_gap_exact (vm ink g : Int) :
    (vm + max 0 (max 0 (vm - ink - g) + ink + g - vm))
      - (max 0 (vm - ink - g) + ink) = g := by
  omega

public theorem furniture_gap_exact (vmargin ink gap : Sp) :
    (vmargin + (furnitureBand vmargin ink (some gap)).band)
      - ((furnitureBand vmargin ink (some gap)).edge + ink) = gap := by
  simp only [furnitureBand, furnEdge, Option.getD]
  exact furn_gap_exact vmargin ink gap

/-- The ink gap of a declared `\headsep`, which LaTeX measures from the header's baseline. -/
public def furnGapOfSep (sep descent : Sp) : Sp := sep - descent

/-- The inverse of `furnGapOfSep`. -/
public def furnSepOfGap (gap descent : Sp) : Sp := gap + descent

private theorem furn_roundtrip (sep d vm ink : Int) (h : ink + (sep - d) ≤ vm) :
    (sep - d) + d = sep ∧ max 0 (vm - ink - (sep - d)) + ink + (sep - d) = vm := by
  omega

public theorem geometry_roundtrip (sep descent vmargin ink : Sp)
    (h : ink + furnGapOfSep sep descent ≤ vmargin) :
    furnSepOfGap (furnGapOfSep sep descent) descent = sep ∧
    (furnitureBand vmargin ink (some (furnGapOfSep sep descent))).edge + ink +
      furnGapOfSep sep descent = vmargin := by
  simp only [furnGapOfSep, furnSepOfGap, furnitureBand, furnEdge] at h ⊢
  exact furn_roundtrip sep descent vmargin ink h

public def Geom.textHeight (g : Geom) : Sp := g.frameTextHeight.getD (g.pageH - 2 * g.vmargin)

public def bandSlotX (g : Geom) (side : Ir.BandSide) (w : Sp) : Sp :=
  match side with
  | .left => Ir.footline.left
  | .right => g.pageW - Ir.footline.right - w

public theorem bandSlotX_right_pinned (g : Geom) (w : Sp) :
    bandSlotX g .right w + w = g.pageW - Ir.footline.right := by
  have key : ∀ a b c : Int, a - b - c + c = a - b := by intro a b c; omega
  simp only [bandSlotX]
  exact key g.pageW Ir.footline.right w

public def footBaseline (pageH d : Sp) : Sp := pageH - Ir.footline.raise - d

/-- The floor of a frame's text area, `gap` above a footline
band whose box stands `h` above and `d` below its baseline. -/
public def footFloor (pageH gap h d : Sp) : Sp := footBaseline pageH d - h - gap

public theorem footFloor_exact (pageH gap h d : Sp) :
    footFloor pageH gap h d + gap + h + d + Ir.footline.raise = pageH ∧
      footBaseline pageH d - h - footFloor pageH gap h d = gap := by
  have key : ∀ H g h d r : Int, H - r - d - h - g + g + h + d + r = H ∧
      H - r - d - h - (H - r - d - h - g) = g := by intros; omega
  exact key pageH gap h d Ir.footline.raise

/-- The floor of a frame's text area: `gap` above the footline box
where the page carries one, else `gap` above the paper's edge. -/
public def frameFloor (pageH gap : Sp) : Option (Sp × Sp) → Sp
  | some (h, d) => footFloor pageH gap h d
  | none => pageH - gap

public theorem frameFloor_exact (pageH gap : Sp) (box : Option (Sp × Sp)) :
    frameFloor pageH gap box + gap +
      (match box with
       | some (h, d) => h + d + Ir.footline.raise
       | none => 0) = pageH := by
  cases box with
  | none =>
    have key : ∀ H g : Int, H - g + g + 0 = H := by intros; omega
    exact key pageH gap
  | some hd =>
    obtain ⟨h, d⟩ := hd
    have key : ∀ H g h d r : Int, H - r - d - h - g + g + (h + d + r) = H := by intros; omega
    exact key pageH gap h d Ir.footline.raise


/-- Whether a box `w` wide whose left edge stands at `x` lies on the
medium, which runs from `-bleed` to `pageW + bleed` in trim space. -/
public def Geom.onMedium (g : Geom) (x w : Sp) : Bool :=
  -g.bleed ≤ x && x + w ≤ g.pageW + g.bleed

/-- How far off the medium a box reaches; zero when it lies on it. -/
public def Geom.offMedium (g : Geom) (x w : Sp) : Sp :=
  max 0 (max (x + w - (g.pageW + g.bleed)) (-g.bleed - x))

public theorem offMedium_agree (g : Geom) (x w : Sp) :
    g.offMedium x w = 0 ↔ g.onMedium x w = true := by
  have key : ∀ b pw x w : Int,
      max 0 (max (x + w - (pw + b)) (-b - x)) = 0 ↔
        ((-b ≤ x && x + w ≤ pw + b) = true) := by
    intro b pw x w
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact key g.bleed g.pageW x w

public theorem slides_lines_in_band :
    ∀ r ∈ Ir.slidesStages,
      10 ≤ (r.2.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ∧
      (r.2.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ≤ 20 := by
  decide

public theorem slides_lines_survive_bands (a d f : Sp)
    (hh : a + d ≤ 2 * Ir.slidesFontSize) (hf : f ≤ 2 * Ir.slidesFontSize)
    (g : Geom)
    (hg : g.pageH ∈ Ir.slidesStages.map (·.2.2))
    (hv : g.vmargin = Ir.slidesVMargin)
    (hhb : g.headBand = (furnitureBand g.vmargin (a + d) none).band)
    (hfb : g.footBand = (furnitureBand g.vmargin f none).band) :
    0 < g.bodyBottom - g.bodyTop ∧
    10 ≤ (g.bodyBottom - g.bodyTop) / leadingFor Ir.slidesFontSize ∧
    (g.bodyBottom - g.bodyTop) / leadingFor Ir.slidesFontSize ≤ 20 := by
  have hvm : Ir.slidesVMargin = 1730150 := by decide
  have hfs : Ir.slidesFontSize = 720896 := by decide
  have hld : leadingFor Ir.slidesFontSize = 865075 := by decide
  have hls : inkClearance = 65536 := by decide
  have hrange : ∀ r ∈ Ir.slidesStages,
      16719420 ≤ r.2.2 ∧ r.2.2 ≤ 19505990 := by decide
  have ⟨r, hr, heq⟩ := Array.mem_map.mp hg
  have hH : 16719420 ≤ g.pageH ∧ g.pageH ≤ 19505990 := heq ▸ hrange r hr
  have key : ∀ a d f hb fb H : Int,
      a + d ≤ 2 * 720896 → f ≤ 2 * 720896 →
      16719420 ≤ H → H ≤ 19505990 →
      hb = max 0 (1730150 / 2 + (a + d) + 65536 - 1730150) →
      fb = max 0 (1730150 / 2 + f + 65536 - 1730150) →
      0 < H - 1730150 - fb - (1730150 + hb) ∧
      10 ≤ (H - 1730150 - fb - (1730150 + hb)) / 865075 ∧
      (H - 1730150 - fb - (1730150 + hb)) / 865075 ≤ 20 := by
    intro a d f hb fb H hh hf hlo hhi hhb hfb
    omega
  rw [hfs] at hh hf
  simp only [furnitureBand, furnEdge, Option.getD, hls, hv, hvm] at hhb hfb
  rw [hld]
  simp only [Geom.bodyBottom, Geom.bodyTop]
  rw [hv, hvm]
  exact key a d f g.headBand g.footBand g.pageH hh hf hH.1 hH.2 hhb hfb

/-- How a page distributes its leftover vertical space: thousandths of a fil
above and below the content, and whether a body `\vfill` joins them (`joins`). -/
public structure VDist where
  above : Nat
  below : Nat
  joins : Bool
  deriving Repr, BEq, Inhabited

public def VDist.top : VDist := ⟨0, 1000, false⟩
public def VDist.center : VDist := ⟨1000, 1000, false⟩
public def VDist.bottom : VDist := ⟨1000, 0, false⟩
public def VDist.golden : VDist := ⟨3618, 2000, false⟩

/-- The shift of a line with `k` of its page's `n` fil units above it,
as a share of the leftover; content taller than the area stays put. -/
public def filShare (leftover : Sp) (k n : Nat) : Sp :=
  if leftover ≤ 0 then 0
  else if n = 0 then 0
  else leftover * k / n

public theorem filShare_sound (l : Sp) (k k' n : Nat) (hk : k ≤ k') (hk' : k' ≤ n) :
    0 ≤ filShare l k n ∧ (0 ≤ l → filShare l k' n ≤ l) ∧
    filShare l k n ≤ filShare l k' n := by
  unfold filShare
  by_cases hl : l ≤ 0
  · simp [hl]
  · by_cases hn : n = 0
    · simp [hl, hn]
    · have hnn : (0 : Int) < (n : Int) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hl0 : (0 : Int) < l := Int.not_le.mp hl
      simp only [hl, hn, ite_false]
      refine ⟨?_, fun _ => ?_, ?_⟩
      · exact Int.ediv_nonneg (Int.mul_nonneg (by omega) (Int.natCast_nonneg _)) (by omega)
      · calc l * (k' : Int) / (n : Int)
            ≤ l * (n : Int) / (n : Int) :=
              Int.ediv_le_ediv hnn
                (Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hk') (by omega))
          _ = l := Int.mul_ediv_cancel l (by omega)
      · exact Int.ediv_le_ediv hnn
          (Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hk) (by omega))

public def VDist.aboveShare (d : VDist) (leftover : Sp) : Sp :=
  filShare leftover d.above (d.above + d.below)

public theorem VDist.split_exact (d : VDist) (l : Int) :
    0 ≤ d.aboveShare l ∧ (0 ≤ l → d.aboveShare l ≤ l) ∧
    d.aboveShare l + (l - d.aboveShare l) = l := by
  have h := filShare_sound l d.above d.above (d.above + d.below)
    (Nat.le_refl _) (Nat.le_add_right _ _)
  have hcancel : ∀ x y : Int, x + (y - x) = y := by omega
  exact ⟨h.1, h.2.1, hcancel _ _⟩

public theorem VDist.center_is_halving (l : Sp) :
    VDist.center.aboveShare l = if l ≤ 0 then 0 else l / 2 := by
  unfold aboveShare filShare center
  split
  · rfl
  · have h1 : ((1000 : Nat) : Int) = 1000 := rfl
    have h2 : ((1000 + 1000 : Nat) : Int) = 2000 := rfl
    have hn : (1000 + 1000 : Nat) = 0 ↔ False := by decide
    have key : ∀ x : Int, x * 1000 / 2000 = x / 2 := by intro x; omega
    simp only [hn, ite_false, h1, h2]
    exact key l

public theorem filShare_half_exact (l : Sp) : filShare l 1 2 = VDist.center.aboveShare l := by
  rw [VDist.center_is_halving]
  unfold filShare
  split <;> simp

public theorem VDist.top_is_flush (l : Sp) : VDist.top.aboveShare l = 0 := by
  unfold aboveShare filShare top
  split
  · rfl
  · simp

public theorem VDist.center_split_exact (l : Int) (h : 0 ≤ l) :
    VDist.center.aboveShare l ≤ l - VDist.center.aboveShare l ∧
      l - VDist.center.aboveShare l ≤ VDist.center.aboveShare l + 1 := by
  have key : ∀ x s : Int, 0 ≤ x → s = (if x ≤ 0 then 0 else x / 2) →
      s ≤ x - s ∧ x - s ≤ s + 1 := by
    intro x s hx hs
    split at hs <;> omega
  exact key l _ h (VDist.center_is_halving l)

/-- The distribution a frame's declaration names under
the deck's keys, projected from `Ir.frameGlue`. -/
@[expose] public def VDist.of (keys : Ir.FrameKeys) (v : Ir.VAlign) (breakable : Bool := false) :
    VDist :=
  let g := Ir.frameGlue keys breakable v
  ⟨g.above, g.below, g.joins⟩

public theorem VDist.golden_projects (keys : Ir.FrameKeys) :
    VDist.golden = VDist.of keys .golden := by
  cases keys <;> rfl

public theorem VDist.center_projects : VDist.center = VDist.of .moloch .center := by rfl

/-- The fil units above a line (`filShare`'s `k`), counted from the
`\vfill` units on the page and the page's own shares where they join. -/
@[expose] public def VDist.filAbove (d : VDist) (k : Nat) : Nat :=
  if d.joins then d.above + Ir.fillUnit * k else k

@[expose] public def VDist.filTotal (d : VDist) (n : Nat) : Nat :=
  if d.joins then d.above + Ir.fillUnit * n + d.below else n

public theorem VDist.filUnits_id (d : VDist) (h : d.joins = false) (k n : Nat) :
    d.filAbove k = k ∧ d.filTotal n = n := by
  simp [VDist.filAbove, VDist.filTotal, h]

/-- The ground a title page declares, the design's resolved `titlepage`
pair under the palette in force; `none` for every other frame. -/
public def titleGround (pal : Ir.Palette) (valign : Ir.VAlign) : Option Ir.Color :=
  Ir.titleGroundOf pal valign

/-- The ink on a declared title-page ground; `none` where no ground is declared. -/
public def titleInk (pal : Ir.Palette) (valign : Ir.VAlign) : Option Ir.Color :=
  if valign matches .golden then (Ir.Design.ofPalette pal).titlepage.map (·.fg)
  else none

public theorem titleGround_projects (pal : Ir.Palette) (valign : Ir.VAlign) :
    titleGround pal valign =
      if valign matches .golden then Ir.Design.declared? pal .titlePageGround else none := by
  unfold titleGround Ir.titleGroundOf
  cases valign <;> simp [Ir.Design.titleGround_exact]

/-- Where a run's ink comes from, for the backends' marked content. -/
public inductive Attribution where
  /-- Ink of Struct leaf `k`: one inline atom's text. -/
  | leaf (k : Nat)
  /-- Generated ink of the block whose first leaf is `k`, owned by no single leaf. -/
  | block (k : Nat)
  /-- The discretionary hyphen the breaker set at a line end. -/
  | hyphen
  /-- Generated marker ink: a list bullet or number, an algorithm line number. -/
  | label
  /-- The footnote mark's digits, in the text and leading the note block. -/
  | noteMark (num : Nat)
  /-- Ink the projection does not census: furniture, measuring
  passes, the abstract heading and the headline band. -/
  | unattributed
  deriving Repr, BEq, Inhabited

/-- The face, size and colour in force where a through-line starts. -/
public structure DecorationSource where
  slot : Nat := 0
  weight : Ir.Weight := .m
  italic : Bool := false
  color : Ir.Color := Ir.Color.black
  scale : Nat := 1000
  fontSize : Option (Affine Measure) := none
  deriving Repr, BEq, Inhabited

public structure ActiveDecorations where
  underline : Bool := false
  lineThrough : Option DecorationSource := none
  /-- A mark's colour and its command-entry source, whose face sets the band. -/
  highlight : Option (Ir.Color × DecorationSource) := none
  deriving Repr, BEq, Inhabited

/-- One resolved decoration band: `raise` is its bottom
above the baseline, and `thickness` grows upward from it. -/
public structure DecorationRule where
  color : Ir.Color := Ir.Color.black
  thickness : Sp := 0
  raise : Sp := 0
  deriving Repr, BEq, Inhabited

/-- The decoration slots of runs and spaces: runs defer underline resolution
to their fallback face (`Bool`), spaces carry a resolved band. -/
public structure Decorations (U : Type := Bool) [Inhabited U] where
  underline : U := default
  lineThrough : Option DecorationRule := none
  /-- A mark behind the text, its band the command-entry face's. -/
  highlight : Option DecorationRule := none
  deriving Repr, BEq, Inhabited

/-- An inline formula's ambient text metrics at `size`
and its signed outline bounds before the run's raise. -/
public structure MathLineMetrics where
  size : Sp
  ascent : Sp
  descent : Sp
  top : Sp
  bottom : Sp
  deriving Repr, BEq, Inhabited

/-- A run's line metrics: its face's leaded box, or for math
the ambient text box with the formula's measured bounds. -/
public structure RunMetrics where
  leading : Option Sp := none
  math : Option MathLineMetrics := none
  deriving Repr, BEq, Inhabited

public inductive Item where
  | box (w : Sp) (fontIdx : Nat) (color : Ir.Color) (link : Option String)
      (glyphs : Array (Nat × Char × Sp)) (size : Sp) (metrics : RunMetrics)
      (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
      (attr : Attribution)
  | glue (g : Glue)
  /-- Breakable authored glue with resolved decoration bands. -/
  | decoratedGlue (g : Glue) (decorations : Decorations (Option DecorationRule))
  | pen (w : Sp) (cost : Int) (flagged : Bool) (fontIdx : Nat) (color : Ir.Color)
      (glyphs : Array (Nat × Char × Sp))
  /-- An unbreakable image box `w` wide standing `h` above the baseline; `store` indexes the
  `Image.Store`, `none` places a placeholder, and `ink` false ships nothing in its box. -/
  | img (store : Option Nat) (w : Sp) (h : Sp) (ink : Bool)
  /-- A horizontal rule `w` wide and `thickness` tall, its
  bottom at the baseline plus `raise`; never a breakpoint. -/
  | rule (w : Sp) (thickness : Sp) (raise : Sp) (color : Ir.Color)
  /-- A filled polygon taking no width, its points from where
  it stands and the baseline, y up; never a breakpoint. -/
  | poly (pts : Array (Sp × Sp)) (color : Ir.Color)
  deriving Repr, Inhabited

private def Item.boxChars : Item → List Char
  | .box _ _ _ _ glyphs .. => glyphs.toList.map (·.2.1)
  | .glue _ | .decoratedGlue _ _ | .pen .. | .img .. | .rule .. | .poly .. => []

public def forcedCost : Int := -10000

/-- plain TeX's `\hyphenpenalty=50` (TeXbook p.96). -/
public def hyphenPenalty : Int := 50

/-- Where prose may end a line after a character it
sets: after an explicit hyphen, at `hyphenPenalty`. -/
public def proseBreak (c : Char) : Option Nat :=
  if c == '-' then some hyphenPenalty.toNat else none

/-- latex.ltx's `\binoppenalty` and `\relpenalty`. -/
public def binopPenalty : Nat := 700
public def relPenalty : Nat := 500

/-- url.sty's break table: `\UrlBreaks` at `\binoppenalty`, `\UrlBigBreaks`
at `\relpenalty`, and after a hyphen as its `hyphens` option adds. -/
public def urlBreak (c : Char) : Option Nat :=
  if ".@\\/!_|;>]),?&'+=#-".contains c then some binopPenalty
  else if c == ':' then some relPenalty
  else none

/-- Where a browser breaks a table cell's code: after a hyphen
that no hyphen follows (UAX #14, LB21), and nowhere else. -/
public def cellCodeBreak (_prev : Option Char) (c : Char) (next : Option Char) : Option Nat :=
  if c == '-' && next.any (· != '-') then some hyphenPenalty.toNat
  else none

public inductive Seg where
  /-- A glyph run: each glyph carries its laid-out advance, `raise` lifts the
  run's baseline, and `attr` names the structure leaf its ink stands for. -/
  | run (fontIdx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
      (glyphs : Array (Nat × Char × Sp)) (size : Sp) (metrics : RunMetrics)
      (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
      (attr : Attribution)
  /-- Horizontal space; `word` marks glue from `interword`,
  a space between two words of one leaf's text. -/
  | gap (w : Sp) (word : Bool)
  /-- A set interword or authored gap retaining both decoration bands. -/
  | decoratedGap (w : Sp) (word : Bool) (decorations : Decorations (Option DecorationRule))
  /-- A text-decoration rule, painted as a generic rule and kept apart by its kind. -/
  | decoration (kind : Ir.Decoration) (w : Sp) (thickness : Sp) (raise : Sp)
      (color : Ir.Color)
  /-- A horizontal rule `w` wide and `thickness` thick, on the baseline plus `raise`. -/
  | rule (w : Sp) (thickness : Sp) (raise : Sp) (color : Ir.Color)
  /-- An image box standing `h` up from the baseline; `store` indexes the backends'
  `Image.Store`, an entry that did not load renders as a placeholder, and `ink` false ships nothing. -/
  | image (store : Option Nat) (w : Sp) (h : Sp) (ink : Bool)
  /-- A filled polygon with no width, its points from the pen position and the baseline, y up. -/
  | poly (pts : Array (Sp × Sp)) (color : Ir.Color)
  deriving Repr, Inhabited

public def Seg.glyphChars : Seg → List Char
  | .run _ _ _ _ glyphs .. => glyphs.toList.map (·.2.1)
  | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => []

public structure LineOut where
  x : Sp
  y : Sp
  size : Sp
  segs : Array Seg
  setWidth : Sp
  /-- Baseline-relative extent measured by the placer. -/
  regionExtent : Option (Sp × Sp) := none
  /-- How far the line's first glyph hangs left of the measure
  (character protrusion); `x + hang` is the measure edge. -/
  hang : Sp := 0
  /-- The line's font-expansion factor in per-mille, already applied to every run's width. -/
  expand : Int := 0
  /-- Whether the line is engine-placed running furniture in a margin band. -/
  furniture : Bool := false
  /-- Whether the line is a footnote line or the footnote rule. -/
  note : Bool := false
  /-- Whether the line is a counted galley line, which `\page{ linenumbers = on }` numbers. -/
  counted : Bool := false
  /-- Zero-ink destinations the line carries. -/
  anchors : Array String := #[]
  /-- The preorder index of the structure leaf whose text the line paints;
  `none` on furniture and on generated ink the tree does not census. -/
  leaf : Option Nat := none
  /-- A collected picture label's occurrence and glyph reserve. -/
  pictureLabel : Option LabelAudit.Stamp := none
  /-- How far below its own baseline the line's last baseline
  stands; nonzero only for a display alignment's rows. -/
  lastBase : Sp := 0
  /-- Placed by hidden overlay content: the line keeps its place and ships no ink. -/
  hidden : Bool := false
  deriving Repr, Inhabited

/-- A filled rectangle behind a page's text, its top-left
corner at `x`, `y` in layout coordinates (y down). -/
public structure Fill where
  x : Sp
  y : Sp
  w : Sp
  h : Sp
  color : Ir.Color
  deriving Repr, Inhabited

/-- The page's ground: one fill over the whole medium, bleed included. -/
public def Geom.ground (g : Geom) (c : Ir.Color) : Fill :=
  { x := -g.bleed, y := -g.bleed, w := g.pageW + 2 * g.bleed,
    h := g.pageH + 2 * g.bleed, color := c }

/-- The ground a page ships: its own frame or title style, else the palette epoch in force. -/
public def effectivePageGround (page epoch : Option Ir.Color) : Option Ir.Color :=
  page.orElse fun _ => epoch

public theorem effectivePageGround_page_exact (c : Ir.Color) (epoch : Option Ir.Color) :
    effectivePageGround (some c) epoch = some c := by rfl

public theorem effectivePageGround_epoch_exact (epoch : Option Ir.Color) :
    effectivePageGround none epoch = epoch := by rfl

public theorem effectivePageGround_clear_exact :
    effectivePageGround none none = none := by rfl

/-- The eight printer's cut marks of a `trimW × trimH` trim, each
extending a trim line into the bleed and ending `gap` before the trim. -/
public def cutMarks (trimW trimH bleed gap thick : Sp) (color : Ir.Color) : Array Fill :=
  let hw := thick / 2
  let len := bleed - gap
  #[
    ⟨-hw, -bleed, 2 * hw, len, color⟩,
    ⟨-hw, trimH + gap, 2 * hw, len, color⟩,
    ⟨trimW - hw, -bleed, 2 * hw, len, color⟩,
    ⟨trimW - hw, trimH + gap, 2 * hw, len, color⟩,
    ⟨-bleed, -hw, len, 2 * hw, color⟩,
    ⟨trimW + gap, -hw, len, 2 * hw, color⟩,
    ⟨-bleed, trimH - hw, len, 2 * hw, color⟩,
    ⟨trimW + gap, trimH - hw, len, 2 * hw, color⟩]

private theorem cutmarks_trim_arith (W H t : Int) :
    2 * -(t / 2) + 2 * (t / 2) = 0 ∧
    2 * (W - t / 2) + 2 * (t / 2) = 2 * W ∧
    2 * (H - t / 2) + 2 * (t / 2) = 2 * H := by omega

public theorem cutmarks_on_trim_exact (W H b g t : Int) (c : Ir.Color) :
    ∀ f ∈ cutMarks W H b g t c,
      2 * f.x + f.w = 0 ∨ 2 * f.x + f.w = 2 * W ∨
      2 * f.y + f.h = 0 ∨ 2 * f.y + f.h = 2 * H := by
  intro f hf
  have h := cutmarks_trim_arith W H t
  simp only [cutMarks, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl h.1
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr h.2.2))
  · exact Or.inr (Or.inr (Or.inr h.2.2))

private theorem cutmarks_bleed_arith (W H b g t : Int)
    (hW : 0 ≤ W) (hH : 0 ≤ H) (hg : 0 ≤ g) (hgb : g ≤ b) (htg : t ≤ 2 * g) :
    ((-b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ W + b ∧
      -b ≤ -b ∧ -b + (b - g) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ W + b ∧
      -b ≤ H + g ∧ H + g + (b - g) ≤ H + b) ∧ H ≤ H + g) ∧
    ((-b ≤ W - t / 2 ∧ W - t / 2 + 2 * (t / 2) ≤ W + b ∧
      -b ≤ -b ∧ -b + (b - g) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ W - t / 2 ∧ W - t / 2 + 2 * (t / 2) ≤ W + b ∧
      -b ≤ H + g ∧ H + g + (b - g) ≤ H + b) ∧ H ≤ H + g) ∧
    ((-b ≤ -b ∧ -b + (b - g) ≤ W + b ∧
      -b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ W + g ∧ W + g + (b - g) ≤ W + b ∧
      -b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ H + b) ∧ W ≤ W + g) ∧
    ((-b ≤ -b ∧ -b + (b - g) ≤ W + b ∧
      -b ≤ H - t / 2 ∧ H - t / 2 + 2 * (t / 2) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ W + g ∧ W + g + (b - g) ≤ W + b ∧
      -b ≤ H - t / 2 ∧ H - t / 2 + 2 * (t / 2) ≤ H + b) ∧ W ≤ W + g) := by
  omega

public theorem cutmarks_in_bleed_covers (W H b g t : Int) (c : Ir.Color)
    (hW : 0 ≤ W) (hH : 0 ≤ H) (hg : 0 ≤ g) (hgb : g ≤ b) (htg : t ≤ 2 * g) :
    ∀ f ∈ cutMarks W H b g t c,
      (-b ≤ f.x ∧ f.x + f.w ≤ W + b ∧ -b ≤ f.y ∧ f.y + f.h ≤ H + b) ∧
      (f.x + f.w ≤ 0 ∨ W ≤ f.x ∨ f.y + f.h ≤ 0 ∨ H ≤ f.y) := by
  intro f hf
  have h := cutmarks_bleed_arith W H b g t hW hH hg hgb htg
  simp only [cutMarks, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨h.1.1, Or.inr (Or.inr (Or.inl h.1.2))⟩
  · exact ⟨h.2.1.1, Or.inr (Or.inr (Or.inr h.2.1.2))⟩
  · exact ⟨h.2.2.1.1, Or.inr (Or.inr (Or.inl h.2.2.1.2))⟩
  · exact ⟨h.2.2.2.1.1, Or.inr (Or.inr (Or.inr h.2.2.2.1.2))⟩
  · exact ⟨h.2.2.2.2.1.1, Or.inl h.2.2.2.2.1.2⟩
  · exact ⟨h.2.2.2.2.2.1.1, Or.inr (Or.inl h.2.2.2.2.2.1.2)⟩
  · exact ⟨h.2.2.2.2.2.2.1.1, Or.inl h.2.2.2.2.2.2.1.2⟩
  · exact ⟨h.2.2.2.2.2.2.2.1, Or.inr (Or.inl h.2.2.2.2.2.2.2.2)⟩

private theorem cutmarks_flip_arith (W b g d : Int) :
    W - d = W - -d - 2 * d ∧ -d = W - (W - d) - 2 * d ∧
    W + g = W - -b - (b - g) ∧ -b = W - (W + g) - (b - g) := by
  omega

public theorem cutmarks_symmetric_mem (W H b g t : Int) (c : Ir.Color) :
    ∀ f ∈ cutMarks W H b g t c,
      ∃ f' ∈ cutMarks W H b g t c,
        f'.x = W - f.x - f.w ∧ f'.y = f.y ∧ f'.w = f.w ∧ f'.h = f.h := by
  intro f hf
  have h := cutmarks_flip_arith W b g (t / 2)
  simp only [cutMarks, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hf
  simp only [cutMarks]
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_toArray.mpr (.tail _ (.tail _ (.head _))),
      h.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr (.tail _ (.tail _ (.tail _ (.head _)))),
      h.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr (.head _), h.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr (.tail _ (.head _)), h.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))),
      h.2.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))),
      h.2.2.2, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))),
      h.2.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))),
      h.2.2.2, rfl, rfl, rfl⟩

/-- The trim a `trimMarked` page with no declared bleed declares by
drawing exactly `cutMarks` of one trim: its inset, gap and thickness. -/
public def drawnTrim (spec : Ir.PageSpec) : Option (Sp × Sp × Sp) := do
  guard (spec.bleed == 0 && spec.trimMarked && spec.drawn.size == 8)
  let lead ← spec.drawn.foldl (fun m r =>
    if r.y == 0 && r.w < r.h && m.all (r.x < ·.x) then some r else m) none
  let t := lead.w
  let b := lead.x + t / 2
  let g := b - lead.h
  guard (t % 2 == 0 && 0 < t && 0 ≤ g && t ≤ 2 * g && g < b)
  let marks := cutMarks (spec.width - 2 * b) (spec.height - 2 * b) b g t Ir.Color.black
  let same (r : Ir.DrawnRule) (f : Fill) : Bool :=
    r.x == f.x + b && r.y == f.y + b && r.w == f.w && r.h == f.h
  guard (spec.drawn.all fun r => marks.any (same r ·))
  guard (marks.all fun f => spec.drawn.any (same · f))
  return (b, g, t)

/-- Resolve a document's `\page` declaration into layout
geometry, the one source layout reads geometry from. -/
public def Geom.ofPage (spec : Ir.PageSpec) (base : Geom := {}) : Geom :=
  { base with
    pageW := spec.width
    pageH := spec.height
    hmargin := spec.hmargin
    vmargin := spec.vmargin
    fontSize := spec.fontSize
    listIndent := listIndentFor spec.fontSize
    leading := spec.leading
    parskip := spec.parskip.getD (Ir.parskipDefault spec.fontSize)
    texParskip := spec.parskip.getD base.texParskip
    hyphenate := spec.hyphenate.getD base.hyphenate
    justify := spec.justify.getD base.justify
    protrude := spec.protrude.getD base.protrude
    expand := spec.expand.getD base.expand
    flushBottom := spec.flushBottom.getD base.flushBottom
    bleed := spec.bleed
    marks := spec.marks
    markGap := spec.markGap
    markThick := spec.markThickness
    trimInset := ((drawnTrim spec).map (·.1)).getD 0
    scale := spec.scale
    skips := spec.skipScale
    raggedFil := spec.raggedFil }

/-- A picture's ink on the page: its figure, its label keys, the isometry from
picture coordinates (y up) to layout coordinates (y down), and the leaf it paints. -/
public structure InkOut where
  fig : Gfx.Figure (Nat × Nat)
  place : Gfx.Iso
  leaf : Option Nat := none
  deriving Repr, Inhabited

@[expose] public def InkOut.shiftY (d : Sp) (k : InkOut) : InkOut :=
  { k with place := { k.place with dy := k.place.dy + d } }

@[expose] public def InkOut.shiftX (d : Sp) (k : InkOut) : InkOut :=
  { k with place := { k.place with dx := k.place.dx + d } }

public theorem InkOut.shiftY_zero_id (k : InkOut) : k.shiftY 0 = k := by
  simp [InkOut.shiftY]

public theorem InkOut.shiftY_add_exact (k : InkOut) (a b : Sp) :
    (k.shiftY a).shiftY b = k.shiftY (a + b) := by
  simp [InkOut.shiftY, Int.add_assoc]

public theorem InkOut.shiftY_cancel_id (k : InkOut) (d : Sp) :
    (k.shiftY d).shiftY (-d) = k := by
  rw [shiftY_add_exact, Int.add_right_neg, shiftY_zero_id]

/-- The page boxes an ink's marks claim: each geometry's control hull
through its frame and placement, padded by half its stroke width. -/
public def InkOut.claims (k : InkOut) : Array Gfx.Box :=
  k.fig.marks.filterMap fun mk => match mk with
    | .paint ctm g _ st _ _ =>
      g.hull.map fun b =>
        let b := if ctm == Gfx.Affine.unit then b else Gfx.Box.image ctm b
        Gfx.Box.dilate (k.place.box b) ((st.map (·.width / 2)).getD 0)
    | .raster ctm _ _ _ => some (k.place.box (Gfx.Box.image ctm Gfx.rasterUnit))
    | .shading _ _ _ => none

public structure LinkRect where
  x : Sp
  y : Sp
  w : Sp
  h : Sp
  target : String
  deriving Repr, BEq, Inhabited

/-- A frame's identity in the layout input: its zero-based
block index in `pdfView doc` and its one-based overlay step. -/
public structure FrameOrigin where
  source : Nat
  step : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Which text area a frame's pages use: the slides margins,
beamer's `\textheight`, or the whole paper of a plain frame. -/
public inductive FrameArea where
  | margins
  | text
  | paper
  deriving Repr, BEq, DecidableEq, Inhabited

public def frameAreaFor (footAllowed : Bool) (valign : VAlign) : FrameArea :=
  if Ir.frameInTextArea footAllowed valign then .text else .margins

public theorem frameAreaFor_projects (footAllowed : Bool) (valign : VAlign) :
    (frameAreaFor footAllowed valign == .text) = Ir.frameInTextArea footAllowed valign := by
  unfold frameAreaFor
  cases Ir.frameInTextArea footAllowed valign <;> rfl

/-- What the page does with a frame whose content stands past its text area beyond its glue's
shrink: continue it, or stand it overfull to measure it or within its footline gap. -/
public inductive FrameFitMode where
  | spill
  | measure
  | overhang
  | continues
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The inputs in force when the collector opens a frame. -/
public structure FrameOpening where
  origin : Option FrameOrigin
  number : Option Nat
  /-- The frame's label (`Ir.Doc.frameLabels`), by which diagnostics name it. -/
  label : Option String := none
  chrome : Ir.Chrome
  note : Option (Array Ir.Inline)
  sectionTitle : Array Ir.Inline
  count : Nat
  standout : Bool
  allowed : Bool
  palette : Ir.Palette
  area : FrameArea := .margins
  fit : FrameFitMode := .spill
  deriving Repr, Inhabited

public def FrameOpening.footer (f : FrameOpening) : Option (Array Ir.BandSlot) :=
  if f.allowed then
    f.chrome.frameFootBand f.note f.sectionTitle f.number f.count f.standout
  else none

public def FrameOpening.look (f : FrameOpening) : Ir.TitledLook :=
  (Ir.Design.ofPalette f.palette).frameFootLook (f.standout && f.footer.isSome)

/-- The joint observation a physical page owes its collected opening. -/
public abbrev FrameStamp :=
  Option FrameOrigin × Option Nat × Option (Array Ir.BandSlot)

public def FrameOpening.stamp (f : FrameOpening) : FrameStamp :=
  (f.origin, f.number, f.footer)

/-- Unowned flow pages carry no frame furniture, and every
owned page matches a collected opening, its footer included. -/
public def SelectedFrame (openings : Array FrameOpening) (stamp : FrameStamp) : Prop :=
  stamp = (none, none, none) ∨ ∃ f ∈ openings, stamp = f.stamp

/-- A line of a re-flowed declared line that runs past the
measure: its rank, where it opens, and how far past. -/
public structure Overrun where
  rank : Nat := 0
  site : Option Span := none
  excess : Sp := 0
  deriving Repr, Inhabited

/-- One declared line that re-flowed: its rank among the paragraph's declared
lines, its first located item, how many lines it ships as, and its overruns. -/
public structure ReflowedLine where
  ordinal : Nat := 0
  site : Option Span := none
  ships : Nat := 0
  over : Array Overrun := #[]
  deriving Repr, Inhabited

/-- The break decisions committed by one paragraph placement, as positions in its item array. -/
public structure ParagraphBreaks where
  site : Nat
  leaf : Option Nat
  frame : Option FrameOrigin
  forced : Array Nat
  chosen : Array Nat
  endFills : Array Nat
  /-- The source of its first re-flowed declared line: the
  census key of a paragraph no structure leaf names. -/
  key : Option Span := none
  /-- Each declared line of it that re-flowed, in order. -/
  lines : Array ReflowedLine := #[]
  frameNumber : Option Nat := none
  deriving Repr, Inhabited

/-- A paragraph's re-flow census key: its structure leaf, else
where its first re-flowed declared line stands, else its index. -/
public def ParagraphBreaks.subject (p : ParagraphBreaks) : String :=
  match p.leaf, p.key with
  | some n, _ => s!"reflow:leaf:{n}"
  | none, some s => s!"reflow:{s.file}:{s.pos.line}:{s.pos.col}"
  | none, none => s!"paragraph:{p.site}"

/-- A chosen break splits an authored segment if it occurs before an
interior forced end and is neither a forced end nor its preceding fill. -/
public def ParagraphBreaks.Splits (p : ParagraphBreaks) (k : Nat) : Prop :=
  k ∈ p.chosen ∧ (∃ stop ∈ p.forced.pop, k < stop) ∧
    k ∉ p.forced ∧ k ∉ p.endFills

/-- Whether a break splits an authored segment, as `Splits`
reads a chosen one, reading the forced ends once. -/
public def ParagraphBreaks.splitAt (p : ParagraphBreaks) : Nat → Bool :=
  let top := p.forced.pop.foldl max 0
  let ends : Std.HashSet Nat := Std.HashSet.ofList (p.forced.toList ++ p.endFills.toList)
  fun k => decide (k < top) && !ends.contains k

/-- The chosen breaks that split an authored segment. -/
public def ParagraphBreaks.reflows (p : ParagraphBreaks) : Array Nat :=
  p.chosen.filter p.splitAt

private theorem lt_foldl_max (k : Nat) : ∀ (l : List Nat) (acc : Nat),
    k < l.foldl max acc ↔ k < acc ∨ ∃ x ∈ l, k < x := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    have hm : k < max acc x ↔ k < acc ∨ k < x := by omega
    rw [List.foldl_cons, ih, hm]
    constructor
    · rintro ((h | h) | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, by simp, h⟩
      · exact Or.inr ⟨y, by simp [hy], h⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl (Or.inl h)
      · simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨y, hy, h⟩

public theorem ParagraphBreaks.reflows_mem (p : ParagraphBreaks) (k : Nat) :
    k ∈ p.reflows ↔ p.Splits k := by
  have htop : k < p.forced.pop.foldl max 0 ↔ ∃ stop ∈ p.forced.pop, k < stop := by
    rw [← Array.foldl_toList, lt_foldl_max]
    simp only [Nat.not_lt_zero, false_or, Array.mem_def]
  simp only [ParagraphBreaks.reflows, ParagraphBreaks.splitAt, ParagraphBreaks.Splits,
    Array.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, htop,
    Std.HashSet.contains_ofList, List.contains_append, Bool.or_eq_false_iff,
    Array.contains_toList, Array.contains_eq_mem, decide_eq_false_iff_not]

public def ReflowsNamed (paragraphs : Array ParagraphBreaks) (diags : Array Diag) : Prop :=
  ∀ p ∈ paragraphs, ∀ k, p.Splits k →
    ∃ d ∈ diags, d.code = "W0386" ∧ d.subject = some p.subject

/-- Which of a page's fills, pictures and links hidden overlay content placed, by index. -/
public structure PageHidden where
  fills : Array Nat := #[]
  inks : Array Nat := #[]
  links : Array Nat := #[]
  deriving Repr, Inhabited

public structure PageOut where
  /-- The shared logical folio and running style at shipment. -/
  pageState : Ir.PageState := {}
  lines : Array LineOut := #[]
  fills : Array Fill := #[]
  /-- One placed rectangle per page segment of a block link. -/
  links : Array LinkRect := #[]
  /-- Picture ink, one per picture, painted after the fills and before the text. -/
  inks : Array InkOut := #[]
  /-- The chrome footer's slots this page carries, resolved at
  collection; `none` where the page carries no declared furniture. -/
  foot : Option (Array Ir.BandSlot) := none
  /-- The chrome footer's box, its height above and depth below the
  baseline, measured where the page was built; `none` where `foot` is. -/
  footBox : Option (Sp × Sp) := none
  /-- The text area the page was built in (`FrameOpening.area`). -/
  frameArea : FrameArea := .margins
  /-- The footer's resolved colour pair from the frame's palette epoch. -/
  footLook : Option Ir.TitledLook := none
  /-- The displayed frame counter (`Ir.frameNumbers`), which is no source identity. -/
  frame : Option Nat := none
  /-- The source frame and overlay step owning this physical
  page; continuation pages keep the step that spilled. -/
  frameOrigin : Option FrameOrigin := none
  /-- The fill glue units the page's close shared its leftover
  among, one per run of fill glue between two boxes. -/
  fils : Nat := 0
  /-- The bottom edge of the page-top chrome bar, when one painted. -/
  band : Option Sp := none
  /-- What hidden overlay content placed, which keeps its place and ships nothing (`shipped`). -/
  hidden : PageHidden := {}
  deriving Repr, Inhabited

/-- A page that shows nothing: no line, no fill and no
placed picture ink; every emptiness test reads this. -/
@[expose] public def PageOut.blank (p : PageOut) : Bool :=
  p.lines.isEmpty && p.fills.isEmpty && p.inks.isEmpty

public def PageOut.frameStamp (p : PageOut) : FrameStamp :=
  (p.frameOrigin, p.frame, p.foot)

/-- Resolve a destination from the finalized lines: the first shipped
declaration owns the target and supplies its page and coordinates. -/
public def destination? (pages : Array PageOut) (name : String) : Option (Nat × LineOut) :=
  (pages.zipIdx).findSome? fun (page, i) =>
    (page.lines.find? (fun line => line.anchors.contains name)).map (i, ·)

/-- One entry of the PDF document outline (ISO 32000-2 §12.3.3), with
an in-document page index, an external URL, or no destination. -/
public structure OutlineEntry where
  title : String
  page : Option Nat := none
  url : Option String := none
  deriving Repr, BEq, Inhabited

public structure Out where
  pages : Array PageOut
  diags : Array Diag
  /-- The committed paragraph break decisions, retained through furniture. -/
  paragraphBreaks : Array ParagraphBreaks := #[]
  /-- Per overlay step of a frame the overflow ladder marked: how far its content
  reached past its text area, and the least gap above its footline its pages left. -/
  overruns : Array (FrameOrigin × Sp × Sp) := #[]
  /-- Per marked overlay step whose page could not set it at its glue's
  natural size: the largest distance its content stood past the floor. -/
  needs : Array (FrameOrigin × Sp) := #[]
  /-- The marked overlay steps that continued on a next page, each once. -/
  spilled : Array FrameOrigin := #[]
  /-- The document outline, one entry per unpinned-nav link in document order. -/
  outline : Array OutlineEntry := #[]

/-- The paint of ink that keeps its place and ships nothing, its CMYK rider outside every
document's range. -/
@[expose] public def hiddenPaint : Ir.Color :=
  { r := 0, g := 0, b := 0, cmyk := some (1001, 1001, 1001, 1001) }

/-- Is a decoration band painted in the hidden paint? -/
@[expose] public def hiddenRule (r : Option DecorationRule) : Bool := r.any (·.color == hiddenPaint)

/-- Does a segment carry ink that ships nothing? -/
@[expose] public def Seg.hides : Seg → Bool
  | .run _ c .. | .decoration _ _ _ _ c | .rule _ _ _ c | .poly _ c => c == hiddenPaint
  | .decoratedGap _ _ d =>
    hiddenRule d.underline || hiddenRule d.lineThrough || hiddenRule d.highlight
  | .gap .. => false
  | .image _ _ _ ink => !ink

/-- A segment repainted to ship nothing, its kind and box kept. -/
@[expose] public def Seg.hide : Seg → Seg
  | .run f _ l w gs sz m d r g a => .run f hiddenPaint l w gs sz m d r g a
  | .decoration k w t r _ => .decoration k w t r hiddenPaint
  | .rule w t r _ => .rule w t r hiddenPaint
  | .poly pts _ => .poly pts hiddenPaint
  | .decoratedGap w word d =>
    .decoratedGap w word { underline := d.underline.map ({ · with color := hiddenPaint })
                           lineThrough := d.lineThrough.map ({ · with color := hiddenPaint })
                           highlight := d.highlight.map ({ · with color := hiddenPaint }) }
  | .gap w word => .gap w word
  | .image s w h _ => .image s w h false

/-- A segment as it ships: hidden ink a gap as wide, a hidden polygon nothing. -/
@[expose] public def Seg.shipped (s : Seg) : Option Seg :=
  if !s.hides then some s else
  match s with
  | .poly .. => none
  | .decoratedGap w word d =>
    let kept : Decorations (Option DecorationRule) :=
      { underline := if hiddenRule d.underline then none else d.underline
        lineThrough := if hiddenRule d.lineThrough then none else d.lineThrough
        highlight := if hiddenRule d.highlight then none else d.highlight }
    some (if kept.underline.isNone && kept.lineThrough.isNone && kept.highlight.isNone then
      .gap w word else .decoratedGap w word kept)
  | .gap w word => some (.gap w word)
  | .run _ _ _ w .. | .decoration _ w .. | .rule w .. | .image _ w .. => some (.gap w false)

/-- The elements whose index `drop` does not list. -/
@[expose] public def keepUnlisted {α : Type} (xs : Array α) (drop : Array Nat) : Array α :=
  if drop.isEmpty then xs else (xs.zipIdx.filter fun (_, i) => !drop.contains i).map (·.1)

/-- A page as it ships: hidden content keeps its place and ships no ink. -/
@[expose] public def PageOut.shipped (p : PageOut) : PageOut :=
  { p with
    lines := p.lines.map fun l =>
      { l with segs := (if l.hidden then l.segs.map Seg.hide else l.segs).filterMap Seg.shipped }
    fills := keepUnlisted p.fills p.hidden.fills
    inks := keepUnlisted p.inks p.hidden.inks
    links := keepUnlisted p.links p.hidden.links
    hidden := {} }

public structure TextStyle where
  slot : Nat := 0
  /-- The weight axis in force (`Ir.Weight`), `\fontseries`'s series. -/
  weight : Ir.Weight := .m
  italic : Bool := false
  color : Ir.Color := Ir.Color.black
  /-- Destination of the enclosing `\href`, if any. -/
  link : Option String := none
  /-- Size relative to the surrounding text, per mille,
  absolute rather than compounding as in LaTeX. -/
  scale : Nat := 1000
  /-- An arbitrary `\fontsize` size, resolved against the local
  measure and font metrics; named size commands clear it. -/
  fontSize : Option (Affine Measure) := none
  /-- The baseline skip from `\fontsize`; `none` uses the ordinary
  leading, and `some 0` keeps an explicitly zero skip. -/
  leading : Option (Affine Measure) := none
  /-- The named size step in force (`\small`, `\Large`); `none`
  under no size command or after an explicit `\fontsize`. -/
  step : Option String := none
  /-- Set as small caps, applied to the word rather than the face (`smallCapSynth`). -/
  smallcaps : Bool := false
  decorations : ActiveDecorations := {}
  /-- A language switch in force (`Style.lang`), a BCP
  47 tag; `none` is the document's main language. -/
  lang : Option String := none
  /-- The surface this run's ink stands on, as the
  walk declares it; `none` is the undeclared page. -/
  ground : Option Ir.Color := none
  /-- Whether a typewriter run breaks as url.sty sets a path (`urlBreak`) rather than as prose. -/
  urlBreaks : Bool := false
  /-- Whether a typewriter run in a narrowing table cell breaks
  as a browser breaks a cell's code (`cellCodeBreak`). -/
  cellCode : Bool := false
  /-- Inside invisible overlay content (`Ir.OverlaySpec.invisible`) on a step it does not show. -/
  hidden : Bool := false
  deriving Repr, BEq, Inhabited

/-- The paint the style's ink takes: its colour, or the hidden paint inside hidden content. -/
@[expose] public def TextStyle.paint (sty : TextStyle) : Ir.Color :=
  if sty.hidden then hiddenPaint else sty.color

/-- Where a run of this style may end a line after a
character, unhyphenated, given its neighbours in the word. -/
private def TextStyle.explicitBreak (sty : TextStyle) :
    Option Char → Char → Option Char → Option Nat :=
  if sty.slot == 2 && sty.urlBreaks then fun _ c _ => urlBreak c
  else if sty.slot == 2 && sty.cellCode then cellCodeBreak
  else fun _ c _ => proseBreak c

/-- Snapshot the command-entry properties ulem uses for a through-line. -/
private def TextStyle.decorationSource (sty : TextStyle) : DecorationSource :=
  { slot := sty.slot, weight := sty.weight, italic := sty.italic, color := sty.paint,
    scale := sty.scale, fontSize := sty.fontSize }

private inductive Tk where
  /-- Source scopes are metadata only: they never split a shaped word. -/
  | origin (span : Option Span)
  | word (style : TextStyle) (chars : Array Char) (attr : Attribution)
  | anchor (name : String)
  | space (style : TextStyle)
  | fill
  | hskip (style : TextStyle) (glue : Affine Measure) (keep : Bool)
  | rule (style : TextStyle) (width height raise : Affine Measure)
  /-- A strut: zero width, this much height above the baseline. -/
  | strut (height : SymGlue)
  | brk (extra : SymGlue)
  /-- An image reference, resolved against the store when items are built; `ink` false keeps its
  box and ships nothing. -/
  | img (src : String) (spec : Image.Spec) (ink : Bool)
  /-- An elaborated formula, set by `itemsOfInlines` as one unbreakable run attributed `attr`. -/
  | formula (display : Bool) (style : TextStyle) (body : Math.MList) (attr : Attribution)
  /-- An icon: one scalar set in whichever face the per-scalar fallback chain covers it with. -/
  | icon (style : TextStyle) (c : Char) (attr : Attribution)
  /-- A footnote mark with its note body: the mark sets raised at scriptsize,
  the body as its own note block; `bodyLeaf` is the note's first leaf. -/
  | note (num : Nat) (style : TextStyle) (body : Array Ir.Inline) (bodyLeaf : Option Nat)
  /-- TeX's italic correction (`Ir.Inline.italicCorr`) under the style in force. -/
  | corr (maybe : Bool) (style : TextStyle)
  deriving Repr

/-- The attribution a token's ink carries; `none` for a token that ships no run of its own. -/
private def Tk.attr? : Tk → Option Attribution
  | .word _ _ a => some a
  | .icon _ _ a => some a
  | .formula _ _ _ a => some a
  | .note num _ _ _ => some (.noteMark num)
  | .origin _ | .anchor _ | .space _ | .fill | .hskip _ _ _ | .rule _ _ _ _ | .strut _ | .brk _ | .img _ _ _ | .corr _ _ => none

/-- The Layout-private role a decorating site wraps its
declared content in; a NUL cannot come from source text. -/
private def leafRole : String := "\u0000content"

/-- A decorating site's declared content, marked for the counter; empty content stays empty. -/
private def markContent (xs : Array Inline) : Array Inline :=
  if xs.isEmpty then xs else #[.role leafRole xs]

/-- The inline counter: which leaf the next atom takes, advanced by
`flatten` at exactly the arms `Struct.inlineRaw` gives a leaf. -/
private inductive LeafCtr where
  /-- Every atom takes `a`: generated ink with no leaf behind it. -/
  | fixed (a : Attribution)
  /-- The block opening at `k` sets exactly its declared content, and each atom takes `next`. -/
  | counting (k next : Nat)
  /-- The block opening at `k` sets decorated content: every atom is
  `.block k` until a `leafRole` marker, whose body counts from `next`. -/
  | riding (k next : Nat)
  deriving Repr, BEq, Inhabited

/-- The attribution the next atom takes, and the counter past it. -/
private def LeafCtr.take : LeafCtr → Attribution × LeafCtr
  | .fixed a => (a, .fixed a)
  | .counting k next => (.leaf next, .counting k (next + 1))
  | .riding k next => (.block k, .riding k next)

/-- The attribution for generated ink at the counter's position: the
block's, with no leaf consumed. -/
private def LeafCtr.generated : LeafCtr → Attribution
  | .fixed a => a
  | .counting k _ => .block k
  | .riding k _ => .block k

/-- The leaf the counter stands at, when it counts. -/
private def LeafCtr.next? : LeafCtr → Option Nat
  | .fixed _ => none
  | .counting _ next => some next
  | .riding _ _ => none

/-- Step over `n` leaves that ship no run of their own. -/
private def LeafCtr.skip (n : Nat) : LeafCtr → LeafCtr
  | .fixed a => .fixed a
  | .counting k next => .counting k (next + n)
  | .riding k next => .riding k next

/-- Entering the content marker: a riding counter counts its body. -/
private def LeafCtr.enter : LeafCtr → LeafCtr
  | .fixed a => .fixed a
  | .counting k next => .counting k next
  | .riding k next => .counting k next

/-- Leaving the content marker: `inner` is the counter
the body left and `outer` the one that entered. -/
private def LeafCtr.leave (inner outer : LeafCtr) : LeafCtr :=
  match inner, outer with
  | .counting k next, .riding _ _ => .riding k next
  | .counting k next, .counting _ _ | .counting k next, .fixed _ => .counting k next
  | .fixed a, _ => .fixed a
  | .riding k next, _ => .riding k next

/-- The counter a block's inlines start from: none without a leaf, counting
when the inlines are exactly the declared content, else riding. -/
private def LeafCtr.of (leaf : Option Nat) (span : Nat) (xs : Array Inline) : LeafCtr :=
  match leaf with
  | none => .fixed .unattributed
  | some k => if Struct.leafCountInlines xs == span then .counting k k else .riding k k

private structure FlattenSt where
  toks : Array Tk := #[]
  warnedMath : Bool := false
  diags : Array Diag := #[]
  /-- The size ladder named runs resolve through (`Geom.scale`). -/
  ladder : List (String × Nat) := Ir.sizeScale
  /-- Internal title-part roles whose size and optional
  baseline skip are resolved at the slot boundary. -/
  roleMetrics : List (String × (Sp × Option Sp)) := []
  ctr : LeafCtr := .fixed .unattributed
  /-- The overlay step this page sets, which `Ir.altShowsFirst` reads; 1 on unstepped pages. -/
  step : Nat := 1
  /-- The steps of the frame this page sets (`Ir.frameSteps`); zero outside a frame. -/
  steps : Nat := 0

private def warn (st : FlattenSt) (code : DiagCode) (msg : String)
    (help : Option String := none) : FlattenSt :=
  { st with diags := st.diags.push (Diag.of code msg (help := help)) }

/-- Small caps at synthesis size relative to the surrounding
text: 800‰, the fontinst fake-caps tradition. -/
public def smallCapScale : Nat := 800

/-- The per-face synthesis scale over (x-height, cap height) in font
units: 800‰, raised to reach the x-height and capped at full capitals. -/
public def smallCapScaleCore (x c : Nat) : Nat :=
  min 1000 (max smallCapScale (x * 1000 / c))

/-- The per-face synthesis scale from the face's optical x-height and its cap height. -/
public def smallCapScaleFor (f : Font) : Nat :=
  smallCapScaleCore f.xHeightOptical f.capHeight.toNat

public theorem smallcap_height_between (x c : Nat) (hc : 0 < c) (hx : x ≤ c) :
    x * 1000 / c ≤ smallCapScaleCore x c ∧
      smallCapScale ≤ smallCapScaleCore x c ∧ smallCapScaleCore x c ≤ 1000 := by
  have h1 : x * 1000 ≤ c * 1000 := Nat.mul_le_mul_right 1000 hx
  have hq : x * 1000 / c ≤ 1000 := by
    have h2 : x * 1000 / c ≤ c * 1000 / c := Nat.div_le_div_right h1
    rwa [Nat.mul_div_cancel_left 1000 hc] at h2
  unfold smallCapScaleCore smallCapScale
  omega

/-- The synthesised uniform small-caps form of one word: every
letter in its capital form, the whole word at the face's scale. -/
public def smallCapSynth (scale : Nat) (sty : TextStyle) (chars : Array Char) :
    TextStyle × Array Char :=
  let sty := match sty.fontSize with
    | some size => { sty with fontSize := some (Affine.scaleQ scale 1000 size) }
    | none => { sty with scale := sty.scale * scale / 1000 }
  (sty, chars.map (·.toUpper))

private def pushWord (st : FlattenSt) (sty : TextStyle) (cur : Array Char)
    (attr : Attribution) : FlattenSt :=
  { st with toks := st.toks.push (.word sty cur attr) }

/-- One text atom's characters into words and spaces, every word carrying `attr`. -/
private def pushChars (sty : TextStyle) (attr : Attribution) (st : FlattenSt)
    (cur : Array Char) : List Char → FlattenSt
  | [] => if cur.isEmpty then st else pushWord st sty cur attr
  | c :: rest =>
    if c == ' ' then
      let st := if cur.isEmpty then st else pushWord st sty cur attr
      pushChars sty attr { st with toks := st.toks.push (.space sty) } #[] rest
    else pushChars sty attr st (cur.push c) rest

/-- One text atom's words and spaces, every word carrying `attr`. -/
private def pushTextAttr (st : FlattenSt) (sty : TextStyle) (s : String)
    (attr : Attribution) : FlattenSt :=
  pushChars sty attr st #[] s.toList

/-- One leaf-bearing text atom: takes the counter's next leaf. -/
private def pushText (st : FlattenSt) (sty : TextStyle) (s : String) : FlattenSt :=
  let (attr, ctr) := st.ctr.take
  pushTextAttr { st with ctr := ctr } sty s attr

/-- Apply one markup style to the active text style; `\normalfont` resets to the body face. -/
private def applyStyle (ladder : List (String × Nat)) (sty : TextStyle) :
    Ir.Style → TextStyle
  | .bold => { sty with weight := .b }
  | .italic => { sty with italic := true }
  | .emph => { sty with italic := !sty.italic }
  | .mono => { sty with slot := 2 }
  | .sans => { sty with slot := 1 }
  | .smallcaps => { sty with smallcaps := true }
  | .roman => { sty with slot := 0 }
  | .family s => { sty with slot := s }
  | .medium => { sty with weight := .m }
  | .series w => { sty with weight := w }
  -- NFSS shapes are exclusive (fntguide §2.2): upright clears both.
  | .upright => { sty with italic := false, smallcaps := false }
  -- `\normalfont` resets family, series and shape, never size or colour, as lualatex sets it.
  | .normal => { sty with slot := 0, weight := .m, italic := false, smallcaps := false }
  | .lang tag => { sty with lang := some tag }
  | .size n => match ladder.lookup n with
    | some k => { sty with scale := k, fontSize := none, leading := none, step := some n }
    | none => sty
  | .fontSize size leading =>
    { sty with fontSize := some size, leading := some leading, step := none }

/-- The leading the style's named size step sets on `base` (`Ir.stepLead`); `none` under no step. -/
private def TextStyle.stepLead (sty : TextStyle) (skips : List (String × Nat)) (base : Sp) :
    Option Sp :=
  sty.step.bind (Ir.stepLead skips · base)

private theorem weight_agree (ladder : List (String × Nat)) (sty : TextStyle)
    (s : Ir.Style) :
    (applyStyle ladder sty s).weight = (s.weight?).getD sty.weight := by
  cases s <;> simp [applyStyle, Ir.Style.weight?]
  case size n => cases ladder.lookup n <;> simp

mutual

private def flatten (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : Array Inline) : FlattenSt :=
  flattenList mathOk noteOk st sty xs.toList

private def flattenList (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : List Inline) : FlattenSt :=
  match xs with
  | [] => st
  | x :: rest => flattenList mathOk noteOk (flattenOne mathOk noteOk st sty x) sty rest

private def flattenOne (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (x : Inline) : FlattenSt :=
  match x with
  | .text s => pushText st sty s
  | .label name => { st with toks := st.toks.push (.anchor name) }
  | .ref _ _ text _ => pushText st sty text
  | .cite _ keys => pushText st sty (Ir.citeMarks keys)
  -- Without a note apparatus (furniture, markers, captions, a card face) the body stays inline.
  | .footnote num body =>
    if noteOk then
      { st with toks := st.toks.push (.note (num.getD 0) sty body st.ctr.next?)
                ctr := st.ctr.skip (Struct.leafCountInlines body) }
    else flatten mathOk noteOk st sty body
  | .icon c _ =>
    let (attr, ctr) := st.ctr.take
    { st with toks := st.toks.push (.icon sty c attr), ctr := ctr }
  | .image src spec _ =>
    { st with toks := st.toks.push (.img src spec !sty.hidden),
              ctr := st.ctr.skip 1 }
  | .linebreak extra => { st with toks := st.toks.push (.brk extra), ctr := st.ctr.skip 1 }
  | .fill => { st with toks := st.toks.push .fill }
  | .hspace g keep => { st with toks := st.toks.push (.hskip sty g keep) }
  | .rule width height raise =>
    { st with toks := st.toks.push (.rule sty width height raise) }
  | .strut h => { st with toks := st.toks.push (.strut h) }
  | .italicCorr maybe => { st with toks := st.toks.push (.corr maybe sty) }
  | .math _ src => pushText st sty (Ir.mathFloor src)
  | .formula display _ body =>
    if mathOk then
      let (attr, ctr) := st.ctr.take
      { st with toks := st.toks.push (.formula display sty body attr), ctr := ctr }
    else
      let st := if st.warnedMath then st
        else { warn st .W0003 "no math font is available; math is set as plain text"
                 (some "declare \\fonts{ math = \"...\" } naming an installed \
OpenType math face; `leantex fonts` lists families") with warnedMath := true }
      pushText st sty (Ir.formulaFloor body)
  | .styled s body => flatten mathOk noteOk st (applyStyle st.ladder sty s) body
  | .colored c _ body => flatten mathOk noteOk st { sty with color := c } body
  | .located source body =>
    let inner := flatten mathOk noteOk { st with toks := st.toks.push (.origin (some source)) } sty body
    { inner with toks := inner.toks.push (.origin none) }
  | .role n body =>
    if n == leafRole then
      let inner := flatten mathOk noteOk { st with ctr := st.ctr.enter } sty body
      { inner with ctr := LeafCtr.leave inner.ctr st.ctr }
    else
      match st.roleMetrics.lookup n with
      | some (size, leading) =>
        flatten mathOk noteOk st
          { sty with
            fontSize := some (.lit { width := Dim.Length.ofSp size })
            leading := leading.map fun l => .lit { width := Dim.Length.ofSp l } }
          body
      | none => flatten mathOk noteOk st sty body
  -- The underline is the link's affordance, never colour alone (WCAG 2.2 SC 1.4.1).
  | .link url body =>
    flatten mathOk noteOk st
      { sty with link := some url
                 decorations := { sty.decorations with underline := true } } body
  | .decorated kind body =>
    match kind with
    | .underline =>
      flatten mathOk noteOk st
        { sty with decorations := { sty.decorations with underline := true } } body
    | .lineThrough =>
      flatten mathOk noteOk st
        { sty with decorations :=
            { sty.decorations with lineThrough := some sty.decorationSource } } body
    -- marked text stands on its mark: the run's ground is the mark's
    | .highlight c _ =>
      flatten mathOk noteOk st
        { sty with decorations :=
            { sty.decorations with highlight := some (if sty.hidden then hiddenPaint else c,
                sty.decorationSource) }
                   ground := some c } body
  -- The PDF dims pending content by recolouring copies before layout, and hides invisible content here.
  | .onSteps spec body =>
    flatten mathOk noteOk st
      (if spec.hidesAt st.step st.steps then { sty with hidden := true } else sty)
      body
  | .altSteps spec firstPage otherPage =>
    -- The counter steps over the group the page does not ink, so the inked one keeps `Struct`'s id.
    if spec.showsFirst st.step then
      let inner := flatten mathOk noteOk st sty firstPage
      { inner with ctr := inner.ctr.skip (Struct.leafCountInlines otherPage) }
    else
      flatten mathOk noteOk { st with ctr := st.ctr.skip (Struct.leafCountInlines firstPage) }
        sty otherPage
  -- Placeholders are substituted before layout; one reaching here is generated ink of the block.
  | .pageNumber => pushTextAttr st sty "?" st.ctr.generated
  | .pageCount => pushTextAttr st sty "?" st.ctr.generated

end

private theorem role_transparent_layout (mathOk noteOk : Bool) (st : FlattenSt)
    (sty : TextStyle) (n : String) (body : Array Inline) (h : n ≠ leafRole)
    (hs : st.roleMetrics.lookup n = none) :
    flattenOne mathOk noteOk st sty (.role n body)
      = flatten mathOk noteOk st sty body := by
  simp [flattenOne, h, hs]

private theorem linkLeafAfford_projects (mathOk noteOk : Bool) (st : FlattenSt)
    (sty : TextStyle) (s : Styles) (kind : String) (x : Inline)
    (h : x.bearsLinkText = true) :
    flattenOne mathOk noteOk st sty (s.linkLeafAfford kind x)
      = (match (s.find? kind).bind (·.color) with
         | some (c, _) =>
             flattenOne mathOk noteOk st
               { sty with color := c,
                          decorations := { sty.decorations with underline := true } } x
         | none =>
             flattenOne mathOk noteOk st
               { sty with decorations := { sty.decorations with underline := true } } x) := by
  rw [Styles.linkLeafAfford_afford s kind x h]
  cases hc : (s.find? kind).bind (·.color) with
  | none => simp [flattenOne, flatten, flattenList]
  | some p => obtain ⟨c, _⟩ := p; simp [flattenOne, flatten, flattenList]

/-- Whether an attribution names a leaf, a block or a note mark. -/
private def Attribution.named (a : Attribution) : Bool :=
  a matches .leaf _ | .block _ | .noteMark _

private def Tk.attributed (tk : Tk) : Bool :=
  match tk.attr? with
  | none => true
  | some a => a.named

/-- A counter standing in a block: what it hands out names that block. -/
private def LeafCtr.attributes : LeafCtr → Bool
  | .fixed _ => false
  | .counting _ _ | .riding _ _ => true

private theorem LeafCtr.take_attributes (c : LeafCtr) (h : c.attributes = true) :
    c.take.1.named = true ∧ c.take.2.attributes = true := by
  cases c <;> simp_all [take, attributes, Attribution.named]

private theorem LeafCtr.generated_attributes (c : LeafCtr) (h : c.attributes = true) :
    c.generated.named = true := by
  cases c <;> simp_all [generated, attributes, Attribution.named]

private theorem LeafCtr.skip_attributes (n : Nat) (c : LeafCtr) :
    (c.skip n).attributes = c.attributes := by
  cases c <;> rfl

private theorem LeafCtr.enter_attributes (c : LeafCtr) : c.enter.attributes = c.attributes := by
  cases c <;> rfl

private theorem LeafCtr.leave_attributes (inner outer : LeafCtr) :
    (LeafCtr.leave inner outer).attributes = inner.attributes := by
  cases inner <;> cases outer <;> rfl

private theorem pushWord_toks (st : FlattenSt) (sty : TextStyle) (cur : Array Char)
    (attr : Attribution) (h : attr.named = true) :
    (pushWord st sty cur attr).ctr = st.ctr ∧
      ∀ tk ∈ (pushWord st sty cur attr).toks, tk ∈ st.toks ∨ tk.attributed = true := by
  refine ⟨rfl, fun tk hm => ?_⟩
  simp only [pushWord, Array.mem_push] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · subst hm
    exact Or.inr (by simpa [Tk.attributed, Tk.attr?] using h)

private theorem pushChars_toks (sty : TextStyle) (attr : Attribution) (h : attr.named = true)
    (cs : List Char) : ∀ (st : FlattenSt) (cur : Array Char),
    (pushChars sty attr st cur cs).ctr = st.ctr ∧
      ∀ tk ∈ (pushChars sty attr st cur cs).toks, tk ∈ st.toks ∨ tk.attributed = true := by
  induction cs with
  | nil =>
    intro st cur
    simp only [pushChars]
    split
    · exact ⟨rfl, fun tk hm => Or.inl hm⟩
    · exact pushWord_toks st sty cur attr h
  | cons c rest ih =>
    intro st cur
    simp only [pushChars]
    split
    ·
      have hflush := show ∀ st', st' = (if cur.isEmpty then st else pushWord st sty cur attr) →
          st'.ctr = st.ctr ∧ ∀ tk ∈ st'.toks, tk ∈ st.toks ∨ tk.attributed = true from
        fun st' he => by
          subst he
          split
          · exact ⟨rfl, fun tk hm => Or.inl hm⟩
          · exact pushWord_toks st sty cur attr h
      obtain ⟨hc, hm⟩ := hflush _ rfl
      obtain ⟨hc', hm'⟩ := ih { (if cur.isEmpty then st else pushWord st sty cur attr) with
        toks := (if cur.isEmpty then st else pushWord st sty cur attr).toks.push (.space sty) } #[]
      refine ⟨by rw [hc']; exact hc, fun tk htk => ?_⟩
      rcases hm' tk htk with h1 | h1
      · simp only [Array.mem_push] at h1
        rcases h1 with h1 | h1
        · exact hm tk h1
        · subst h1
          exact Or.inr rfl
      · exact Or.inr h1
    · exact ih st (cur.push c)

private theorem pushTextAttr_toks (st : FlattenSt) (sty : TextStyle) (s : String)
    (attr : Attribution) (h : attr.named = true) :
    (pushTextAttr st sty s attr).ctr = st.ctr ∧
      ∀ tk ∈ (pushTextAttr st sty s attr).toks, tk ∈ st.toks ∨ tk.attributed = true :=
  pushChars_toks sty attr h s.toList st #[]

private theorem pushText_toks (st : FlattenSt) (sty : TextStyle) (s : String)
    (h : st.ctr.attributes = true) :
    (pushText st sty s).ctr.attributes = true ∧
      ∀ tk ∈ (pushText st sty s).toks, tk ∈ st.toks ∨ tk.attributed = true := by
  obtain ⟨hn, ha⟩ := LeafCtr.take_attributes st.ctr h
  obtain ⟨hc, hm⟩ := pushTextAttr_toks { st with ctr := st.ctr.take.2 } sty s st.ctr.take.1 hn
  exact ⟨by simp only [pushText]; rw [hc]; exact ha, by simpa [pushText] using hm⟩

private theorem warn_toks (st : FlattenSt) (code : DiagCode) (msg : String) (help : Option String) :
    (warn st code msg help).toks = st.toks ∧ (warn st code msg help).ctr = st.ctr :=
  ⟨rfl, rfl⟩

mutual

private theorem flatten_attr_covers (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : Array Inline) (h : st.ctr.attributes = true) :
    (flatten mathOk noteOk st sty xs).ctr.attributes = true ∧
      ∀ tk ∈ (flatten mathOk noteOk st sty xs).toks, tk ∈ st.toks ∨ tk.attributed = true := by
  simp only [flatten]
  exact flattenList_attr_covers mathOk noteOk st sty xs.toList h

private theorem flattenList_attr_covers (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : List Inline) (h : st.ctr.attributes = true) :
    (flattenList mathOk noteOk st sty xs).ctr.attributes = true ∧
      ∀ tk ∈ (flattenList mathOk noteOk st sty xs).toks, tk ∈ st.toks ∨ tk.attributed = true := by
  match xs with
  | [] => exact ⟨h, fun tk hm => Or.inl hm⟩
  | x :: rest =>
    obtain ⟨h1, m1⟩ := flattenOne_attr_covers mathOk noteOk st sty x h
    obtain ⟨h2, m2⟩ := flattenList_attr_covers mathOk noteOk
      (flattenOne mathOk noteOk st sty x) sty rest h1
    refine ⟨by simpa [flattenList] using h2, fun tk hm => ?_⟩
    rcases m2 tk (by simpa [flattenList] using hm) with hm' | hm'
    · exact m1 tk hm'
    · exact Or.inr hm'

private theorem flattenOne_attr_covers (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (x : Inline) (h : st.ctr.attributes = true) :
    (flattenOne mathOk noteOk st sty x).ctr.attributes = true ∧
      ∀ tk ∈ (flattenOne mathOk noteOk st sty x).toks, tk ∈ st.toks ∨ tk.attributed = true := by
  match x with
  | .text s => exact pushText_toks st sty s h
  | .label name =>
    refine ⟨h, fun tk hm => ?_⟩
    simp only [flattenOne, Array.mem_push] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · subst hm; exact Or.inr rfl
  | .ref _ _ text _ => exact pushText_toks st sty text h
  | .cite _ keys => exact pushText_toks st sty (Ir.citeMarks keys) h
  | .footnote num body =>
    simp only [flattenOne]
    split
    · refine ⟨by rw [LeafCtr.skip_attributes]; exact h, fun tk hm => ?_⟩
      simp only [Array.mem_push] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · subst hm; exact Or.inr rfl
    · exact flatten_attr_covers mathOk noteOk st sty body h
  | .icon c _ =>
    obtain ⟨hn, ha⟩ := LeafCtr.take_attributes st.ctr h
    refine ⟨by simpa [flattenOne] using ha, fun tk hm => ?_⟩
    simp only [flattenOne, Array.mem_push] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · subst hm
      exact Or.inr (by simpa [Tk.attributed, Tk.attr?] using hn)
  | .image src spec _ =>
    refine ⟨by simp only [flattenOne]; rw [LeafCtr.skip_attributes]; exact h, fun tk hm => ?_⟩
    simp only [flattenOne, Array.mem_push] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · subst hm; exact Or.inr rfl
  | .linebreak extra =>
    refine ⟨by simp only [flattenOne]; rw [LeafCtr.skip_attributes]; exact h, fun tk hm => ?_⟩
    simp only [flattenOne, Array.mem_push] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · subst hm; exact Or.inr rfl
  | .fill | .hspace _ _ | .rule _ _ _ =>
    refine ⟨h, fun tk hm => ?_⟩
    simp only [flattenOne, Array.mem_push] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · subst hm; exact Or.inr rfl
  | .strut hg =>
    refine ⟨h, fun tk hm => ?_⟩
    simp only [flattenOne, Array.mem_push] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · subst hm; exact Or.inr rfl
  | .italicCorr maybe =>
    refine ⟨h, fun tk hm => ?_⟩
    simp only [flattenOne, Array.mem_push] at hm
    rcases hm with hm | hm
    · exact Or.inl hm
    · subst hm; exact Or.inr rfl
  | .math _ src => exact pushText_toks st sty (Ir.mathFloor src) h
  | .formula display _ body =>
    simp only [flattenOne]
    split
    · obtain ⟨hn, ha⟩ := LeafCtr.take_attributes st.ctr h
      refine ⟨ha, fun tk hm => ?_⟩
      simp only [Array.mem_push] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · subst hm
        exact Or.inr (by simpa [Tk.attributed, Tk.attr?] using hn)
    ·
      split
      · exact pushText_toks st sty (Ir.formulaFloor body) h
      · exact pushText_toks _ sty (Ir.formulaFloor body) h
  | .styled s body => exact flatten_attr_covers mathOk noteOk st _ body h
  | .colored c _ body => exact flatten_attr_covers mathOk noteOk st _ body h
  | .located source body =>
    obtain ⟨hc, hm⟩ := flatten_attr_covers mathOk noteOk
      { st with toks := st.toks.push (.origin (some source)) } sty body h
    refine ⟨hc, fun tk htk => ?_⟩
    simp only [flattenOne, Array.mem_push] at htk
    rcases htk with htk | htk
    · rcases hm tk htk with old | named
      · simp only [Array.mem_push] at old
        rcases old with old | marker
        · exact Or.inl old
        · subst marker; exact Or.inr rfl
      · exact Or.inr named
    · subst htk; exact Or.inr rfl
  | .role n body =>
    simp only [flattenOne]
    split
    · obtain ⟨h1, m1⟩ := flatten_attr_covers mathOk noteOk { st with ctr := st.ctr.enter } sty body
        (by rw [LeafCtr.enter_attributes]; exact h)
      exact ⟨by rw [LeafCtr.leave_attributes]; exact h1, m1⟩
    · split
      · exact flatten_attr_covers mathOk noteOk st _ body h
      · exact flatten_attr_covers mathOk noteOk st sty body h
  | .link url body => exact flatten_attr_covers mathOk noteOk st _ body h
  | .decorated kind body =>
    cases kind <;> exact flatten_attr_covers mathOk noteOk st _ body h
  | .onSteps _ body => exact flatten_attr_covers mathOk noteOk st _ body h
  | .altSteps _ firstPage otherPage =>
    simp only [flattenOne]
    split
    · obtain ⟨h1, m1⟩ := flatten_attr_covers mathOk noteOk st sty firstPage h
      exact ⟨by simpa [LeafCtr.skip_attributes] using h1, fun tk hm => m1 tk (by simpa using hm)⟩
    · obtain ⟨h2, m2⟩ := flatten_attr_covers mathOk noteOk
        { st with ctr := st.ctr.skip (Struct.leafCountInlines firstPage) } sty otherPage
        (by simpa [LeafCtr.skip_attributes] using h)
      exact ⟨h2, fun tk hm => m2 tk hm⟩
  | .pageNumber =>
    obtain ⟨hc, hm⟩ := pushTextAttr_toks st sty "?" st.ctr.generated
      (LeafCtr.generated_attributes st.ctr h)
    exact ⟨by simp only [flattenOne]; rw [hc]; exact h, hm⟩
  | .pageCount =>
    obtain ⟨hc, hm⟩ := pushTextAttr_toks st sty "?" st.ctr.generated
      (LeafCtr.generated_attributes st.ctr h)
    exact ⟨by simp only [flattenOne]; rw [hc]; exact h, hm⟩

end

private def scaledAt (size : Sp) (font : Font) (units : Nat) : Sp :=
  (units * size.toNat) / font.unitsPerEm

private def glyphOf (size : Sp) (font : Font) (c : Char) : Option (Nat × Char × Sp) :=
  match font.gid c with
  | some g => some (g, c, scaledAt size font (font.widths[g]?.getD 0))
  | none => none

/-- `glyphOf` through the face's small-caps substitution
when the run is small caps; the char stays as typed. -/
private def glyphOfSc (smallcaps : Bool) (size : Sp) (font : Font) (c : Char) :
    Option (Nat × Char × Sp) :=
  (font.gid c).map fun g0 =>
    let g := if smallcaps then font.smallCapGid g0 else g0
    (g, c, scaledAt size font (font.widths[g]?.getD 0))

public def hyphenGlyph (size : Sp) (font : Font) : Array (Nat × Char × Sp) :=
  match glyphOf size font '-' with
  | some g => #[g]
  | none => #[]

public def boxWidth (box : Array (Nat × Char × Sp)) : Sp :=
  box.foldl (fun w g => w + g.2.2) 0

public theorem boxWidth_push (xs : Array (Nat × Char × Sp)) (a : Nat × Char × Sp) :
    boxWidth (xs.push a) = boxWidth xs + a.2.2 := by
  unfold boxWidth
  rw [Array.foldl_push]

@[expose] public def kernEnabled (features : Ir.Features) : Bool := features.kern

/-- A face's pair kern between two glyphs at `size`; 0
when kerning is off or the face has no kern data. -/
public def pairKern (features : Ir.Features) (size : Sp) (font : Font) (g1 g2 : Nat) : Sp :=
  (if kernEnabled features then font.kernAdv g1 g2 else 0) * size /
    (font.unitsPerEm : Int)

/-- A glyph's pair kern with its face's space glyph at
`size`: `(g, space)` when `after`, else `(space, g)`. -/
public def spacePairKern (features : Ir.Features) (size : Sp) (font : Font)
    (after : Bool) (g : Nat) : Sp :=
  (if kernEnabled features then font.spaceKernAdv after g else 0) * size /
    (font.unitsPerEm : Int)

/-- The scaled pair kern the next glyph owes against the box's last; 0 at a box head. -/
public def kernVal (features : Ir.Features) (size : Sp) (font : Font)
    (box : Array (Nat × Char × Sp)) (g1 : Nat) : Sp :=
  match box.back? with
  | some (pg, _, _) => pairKern features size font pg g1
  | none => 0

/-- Apply a pair kern to the box's last glyph's advance. -/
public def kernApply (box : Array (Nat × Char × Sp)) (ks : Sp) : Array (Nat × Char × Sp) :=
  match box.back? with
  | some (pg, pc, padv) => box.pop.push (pg, pc, padv + ks)
  | none => box

private theorem back?_pop_push {α : Type} (xs : Array α) (a : α)
    (h : xs.back? = some a) : xs = xs.pop.push a := by
  unfold Array.back? at h
  apply Array.toList_inj.mp
  simp only [Array.toList_push, Array.toList_pop]
  have hg : xs.toList.getLast? = some a := by
    rw [List.getLast?_eq_getElem?]
    simpa using h
  have hne : xs.toList ≠ [] := by rintro h0; simp [h0] at hg
  rw [List.getLast?_eq_some_getLast hne] at hg
  have := List.dropLast_concat_getLast hne
  rw [Option.some_inj.mp hg] at this
  exact this.symm

private theorem kernApply_sourceChars (box : Array (Nat × Char × Sp)) (ks : Sp) :
    (kernApply box ks).toList.map (·.2.1) = box.toList.map (·.2.1) := by
  cases hb : box.back? with
  | none => simp [kernApply, hb]
  | some p =>
    obtain ⟨pg, pc, padv⟩ := p
    have hbox := back?_pop_push box _ hb
    have hc : box.toList.map (·.2.1) = box.pop.toList.map (·.2.1) ++ [pc] := by
      rw [hbox]
      simp
    rw [hc]
    simp [kernApply, hb]

public theorem kern_measure_exact (box : Array (Nat × Char × Sp))
    (ks : Sp) (g : Nat × Char × Sp) (h : box.back?.isSome) :
    boxWidth ((kernApply box ks).push g) = boxWidth box + ks + g.2.2 := by
  cases hb : box.back? with
  | none => simp [hb] at h
  | some p =>
    obtain ⟨pg, pc, padv⟩ := p
    have hbox := back?_pop_push box _ hb
    have hw : boxWidth box = boxWidth box.pop + padv := by
      rw [hbox]
      simp [boxWidth, Array.pop_push]
    rw [show kernApply box ks = box.pop.push (pg, pc, padv + ks) by
      unfold kernApply
      rw [hb]]
    rw [boxWidth_push, boxWidth_push, hw]
    change boxWidth box.pop + (padv + ks) + g.2.2
      = boxWidth box.pop + padv + ks + g.2.2
    rw [Int.add_assoc (boxWidth box.pop) padv ks]

public theorem kernVal_head (features : Ir.Features) (size : Sp) (font : Font) (g1 : Nat)
    (box : Array (Nat × Char × Sp)) (h : box.back? = none) :
    kernVal features size font box g1 = 0 := by
  unfold kernVal
  rw [h]

/-- Fixed-width spaces as a fraction of the em, set as kerns rather than looked up as glyphs. -/
public def fixedSpace (c : Char) : Option (Nat × Nat) :=
  if c == '\u2009' then some (1, 6)        -- thin space, TeX's \,
  else if c == '\u202F' then some (1, 6)   -- narrow no-break: siunitx's \, between number and unit
  else if c == '\u2005' then some (1, 4)   -- four-per-em, \:
  else if c == '\u2004' then some (1, 3)   -- three-per-em, \;
  else if c == '\u2007' then some (1, 2)   -- figure space
  else if c == '\u2002' then some (1, 2)   -- en space: \enspace, \labelsep's .5em
  else if c == '\u2003' then some (1, 1)   -- em quad: \paragraph's run-in gap
  else none

/-- First loss sites, keyed by the diagnostic and its glyph request. -/
private abbrev GlyphOrigins := Array (DiagCode × Nat × Char × Span)

private def rememberGlyph (sites : GlyphOrigins) (code : DiagCode)
    (idx : Nat) (c : Char) (source : Option Span) : GlyphOrigins :=
  match source with
  | none => sites
  | some source => sites.push (code, idx, c, source)

private def glyphOrigin (sites : GlyphOrigins) (code : DiagCode)
    (idx : Nat) (c : Char) : Option Span :=
  (sites.find? fun site => site.1 == code && site.2.1 == idx && site.2.2.1 == c).map (·.2.2.2)

private theorem scalarLoop_census {α β γ : Type} (read : β → List γ)
    (emit : α → List γ) (f : α → β → Id (ForInStep β)) :
    ∀ (xs : List α) (init : β),
    (∀ x ∈ xs, ∀ b, ∃ next, f x b = .yield next ∧ read next = read b ++ emit x) →
    read (forIn xs init f : Id β).run = read init ++ xs.flatMap emit := by
  intro xs
  induction xs with
  | nil => intro init _; simp
  | cons x xs ih =>
    intro init step
    obtain ⟨next, hn, hc⟩ := step x (by simp) init
    rw [List.forIn_cons, hn]
    change read (forIn xs next f : Id β).run = _
    rw [ih next (fun x hx => step x (by simp [hx])), hc]
    simp [List.append_assoc]

private theorem scalarLoop_array_census {α β γ : Type} (read : β → List γ)
    (emit : α → List γ) (f : α → β → Id (ForInStep β)) (xs : Array α) (init : β)
    (step : ∀ x ∈ xs, ∀ b, ∃ next, f x b = .yield next ∧ read next = read b ++ emit x) :
    read (forIn xs init f : Id β).run = read init ++ xs.toList.flatMap emit := by
  rw [← Array.forIn_toList]
  exact scalarLoop_census read emit f xs.toList init
    (fun x hx => step x (by simpa using hx))

private theorem scalarLoop_range_census {β γ : Type} (read : β → List γ)
    (emit : Nat → List γ) (f : Nat → β → Id (ForInStep β)) (lo hi : Nat) (init : β)
    (step : ∀ k, lo ≤ k → k < hi → ∀ b,
      ∃ next, f k b = .yield next ∧ read next = read b ++ emit k) :
    read (forIn [lo:hi] init f : Id β).run =
      read init ++ (List.range' lo (hi-lo)).flatMap emit := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size] using
    scalarLoop_census read emit f (List.range' lo (hi-lo)) init (by
      intro k hk b
      simp only [List.mem_range'] at hk
      exact step k (by omega) (by omega) b)

/-- Flush the shaped buffer, keeping each ownership fragment and its expansion origin. -/
private def flushWord (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (items : Array Item) (offsets : Std.HashMap Nat Sp)
    (sources : Array (Nat × Nat)) (box : Array (Nat × Char × Sp))
    (boxOwners : Array Attribution) (boxSources : Array Nat) (w : Sp) :
    Array Item × Std.HashMap Nat Sp × Array (Nat × Nat) := Id.run do
  if box.isEmpty then return (items, offsets, sources)
  let first := boxOwners[0]?.getD attr
  if boxOwners.all (· == first) then
    -- The item count is read before the push, so the push writes in place.
    let sources := sources ++ boxSources.map (·, items.size)
    return (items.push (.box w fontIdx color link box size {leading} decorations 0 ground first),
      offsets, sources)
  let mut items := items
  let mut offsets := offsets
  let mut sources := sources
  let mut offset := 0
  let mut run := #[]
  let mut runW := 0
  let mut owner := first
  for (g, k) in box.zipIdx do
    let next := boxOwners[k]?.getD attr
    if next != owner then
      if offset != 0 then offsets := offsets.insert items.size offset
      items := items.push (.box runW fontIdx color link run size {leading} decorations 0 ground owner)
      offset := offset + runW
      run := #[]
      runW := 0
      owner := next
    run := run.push g
    runW := runW + g.2.2
    sources := sources.push (boxSources[k]!, items.size)
  if offset != 0 then offsets := offsets.insert items.size offset
  return (items.push (.box runW fontIdx color link run size {leading} decorations 0 ground owner),
    offsets, sources)

private theorem flushWord_boxChars (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (items : Array Item) (offsets : Std.HashMap Nat Sp)
    (sources : Array (Nat × Nat)) (box : Array (Nat × Char × Sp))
    (boxOwners : Array Attribution) (boxSources : Array Nat) (w : Sp) :
    (flushWord fontIdx color link size leading decorations ground attr items offsets sources
      box boxOwners boxSources w).1.toList.flatMap Item.boxChars =
      items.toList.flatMap Item.boxChars ++ box.toList.map (·.2.1) := by
  unfold flushWord
  dsimp only
  split
  · rename_i h
    have hb : box = #[] := Array.isEmpty_iff.mp h
    simp [hb]
  · split
    · simp [Item.boxChars]
    · apply Loop.bind_of_inv
        (P := fun st : Array Item × Std.HashMap Nat Sp × Array (Nat × Nat) ×
            Sp × Array (Nat × Char × Sp) × Sp × Attribution =>
          st.1.toList.flatMap Item.boxChars ++ st.2.2.2.2.1.toList.map (·.2.1) =
            items.toList.flatMap Item.boxChars ++ box.toList.map (·.2.1))
        (Q := fun out : Array Item × Std.HashMap Nat Sp × Array (Nat × Nat) =>
          out.1.toList.flatMap Item.boxChars =
            items.toList.flatMap Item.boxChars ++ box.toList.map (·.2.1))
      · refine Eq.trans (b := items.toList.flatMap Item.boxChars ++ [] ++
          box.zipIdx.toList.flatMap (fun x => [x.1.2.1])) ?_ ?_
        · apply scalarLoop_array_census
            (fun st : Array Item × Std.HashMap Nat Sp × Array (Nat × Nat) ×
                Sp × Array (Nat × Char × Sp) × Sp × Attribution =>
              st.1.toList.flatMap Item.boxChars ++ st.2.2.2.2.1.toList.map (·.2.1))
            (fun x : (Nat × Char × Sp) × Nat => [x.1.2.1])
          intro x _ st
          rcases st with ⟨is, os, ss, off, run, rw, owner⟩
          dsimp only
          split
          · split <;> refine ⟨_, rfl, ?_⟩ <;>
              simp [Item.boxChars, List.append_assoc]
          · refine ⟨_, rfl, ?_⟩
            simp [List.append_assoc]
        · simp only [List.append_nil, Array.toList_zipIdx, ← List.map_eq_flatMap]
          congr 1
          simpa only [List.map_map, Function.comp_def] using
            congrArg (List.map (fun x : Nat × Char × Sp => x.2.1))
              (List.zipIdx_map_fst 0 box.toList)
      · intro st hst
        split <;> simpa [Item.boxChars] using hst

private theorem cursorLoop_complete {α β : Type} (P : β → Prop) (pos : β → Nat)
    (n : Nat) (f : α → β → Id (ForInStep β)) :
    ∀ (xs : List α) (init : β), P init → n ≤ pos init + xs.length →
      (∀ x ∈ xs, ∀ st, P st →
        match (f x st).run with
        | .yield next => P next ∧ pos st < pos next
        | .done next => P next ∧ n ≤ pos next) →
      P (forIn xs init f : Id β).run ∧ n ≤ pos (forIn xs init f : Id β).run := by
  intro xs
  induction xs with
  | nil => intro init hp hn _; simpa using And.intro hp hn
  | cons x xs ih =>
    intro init hp hn hs
    have step := hs x (by simp) init hp
    rw [List.forIn_cons]
    cases hf : f x init with
    | done next =>
      change P next ∧ n ≤ pos next
      simpa only [hf, Id.run] using step
    | yield next =>
      simp only [hf, Id.run] at step
      change P (forIn xs next f : Id β).run ∧ n ≤ pos (forIn xs next f : Id β).run
      exact ih next step.1 (by simp only [List.length_cons] at hn; omega)
        (fun y hy st hst => hs y (by simp [hy]) st hst)

private theorem cursorLoop_range_complete {β : Type} (P : β → Prop) (pos : β → Nat)
    (n budget : Nat) (f : Nat → β → Id (ForInStep β)) (init : β)
    (hp : P init) (hn : n ≤ pos init + budget)
    (step : ∀ k, k < budget → ∀ st, P st →
      match (f k st).run with
      | .yield next => P next ∧ pos st < pos next
      | .done next => P next ∧ n ≤ pos next) :
    P (forIn [:budget] init f : Id β).run ∧
      n ≤ pos (forIn [:budget] init f : Id β).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply cursorLoop_complete P pos n
  · exact hp
  · simpa using hn
  · intro k hk st hs
    apply step k _ st hs
    rcases List.mem_range'.mp hk with ⟨j, hj, he⟩
    simp [Std.Legacy.Range.size] at hj he
    omega

private theorem glyphOfSc_char (sc : Bool) (size : Sp) (font : Font)
    (c : Char) (g : Nat × Char × Sp) (h : glyphOfSc sc size font c = some g) :
    g.2.1 = c := by
  unfold glyphOfSc at h
  cases hg : font.gid c <;> simp only [hg, Option.map_none, Option.map_some] at h
  · contradiction
  · cases h
    rfl

/-- The next contiguous letter run from `start`, for `wordItems`. -/
private def letterRun (chars : Array Char) (start : Nat) : Nat × Array Char := Id.run do
  let mut j := start
  let mut run : Array Char := #[]
  for _ in [start:chars.size] do
    if h : j < chars.size then
      if Nfc.isLetter chars[j] then
        run := run.push chars[j]
        j := j + 1
      else
        break
    else
      break
  return (j, run)

private theorem letterRun_prefix (chars : Array Char) (start : Nat)
    (hstart : start ≤ chars.size) :
    start ≤ (letterRun chars start).1 ∧ (letterRun chars start).1 ≤ chars.size ∧
      chars.toList.take (letterRun chars start).1 =
        chars.toList.take start ++ (letterRun chars start).2.toList ∧
      ∀ c ∈ (letterRun chars start).2, Nfc.isLetter c = true := by
  unfold letterRun
  dsimp only
  apply Loop.bind_of_inv
    (P := fun st : Nat × Array Char =>
      start ≤ st.1 ∧ st.1 ≤ chars.size ∧
      chars.toList.take st.1 = chars.toList.take start ++ st.2.toList ∧
      ∀ c ∈ st.2, Nfc.isLetter c = true)
    (Q := fun out : Nat × Array Char =>
      start ≤ out.1 ∧ out.1 ≤ chars.size ∧
      chars.toList.take out.1 = chars.toList.take start ++ out.2.toList ∧
      ∀ c ∈ out.2, Nfc.isLetter c = true)
  · apply Loop.forIn_range_inv
      (P := fun st : Nat × Array Char =>
        start ≤ st.1 ∧ st.1 ≤ chars.size ∧
        chars.toList.take st.1 = chars.toList.take start ++ st.2.toList ∧
        ∀ c ∈ st.2, Nfc.isLetter c = true)
    · simp [hstart]
    · intro k _ _ st hs
      rcases st with ⟨j, run⟩
      rcases hs with ⟨hlo, hhi, hp, hletters⟩
      dsimp only
      split
      · rename_i hj
        split
        · rename_i hl
          change start ≤ j + 1 ∧ j + 1 ≤ chars.size ∧
            chars.toList.take (j + 1) = chars.toList.take start ++ (run.push chars[j]).toList ∧
            ∀ c ∈ run.push chars[j], Nfc.isLetter c = true
          refine ⟨by omega, by omega, ?_, ?_⟩
          · rw [List.take_succ_eq_append_getElem (l := chars.toList)
              (by simpa only [Array.length_toList] using hj), hp]
            simp [List.append_assoc]
          · intro c hc
            rcases Array.mem_push.mp hc with hc | rfl
            · exact hletters c hc
            · exact hl
        · exact ⟨hlo, hhi, hp, hletters⟩
      · exact ⟨hlo, hhi, hp, hletters⟩
  · intro st hs
    exact hs

private theorem letterRun_advances (chars : Array Char) (start : Nat)
    (hstart : start < chars.size) (hletter : Nfc.isLetter chars[start] = true) :
    start < (letterRun chars start).1 := by
  unfold letterRun
  simp only [Id.run, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  have hn : chars.size - start = (chars.size - start - 1) + 1 := by omega
  rw [hn, List.range'_succ, List.forIn_cons]
  simp only [hstart, hletter, ↓reduceDIte, ↓reduceIte, bind]
  change start < (forIn _ (start + 1, #[chars[start]]) _ : Id (Nat × Array Char)).run.1
  apply Loop.forIn_inv (P := fun st : Nat × Array Char => start < st.1)
  · simp
  · intro k _ st hs
    rcases st with ⟨j, run⟩
    dsimp only
    split
    · split
      · change start < j + 1
        omega
      · exact hs
    · exact hs

private theorem cleanLoop_census {α β γ : Type} (Clean : β → Prop) (read : β → List γ)
    (emit : α → List γ) (f : α → β → Id (ForInStep β)) :
    ∀ (xs : List α) (init : β),
      (∀ x ∈ xs, ∀ st, ∃ next, f x st = .yield next ∧
        (Clean next → Clean st ∧ read next = read st ++ emit x)) →
      Clean (forIn xs init f : Id β).run →
      Clean init ∧ read (forIn xs init f : Id β).run = read init ++ xs.flatMap emit := by
  intro xs
  induction xs with
  | nil =>
    intro init _ hc
    simpa using And.intro hc (Eq.refl (read init))
  | cons x xs ih =>
    intro init hs
    obtain ⟨next, hf, hnext⟩ := hs x (by simp) init
    rw [List.forIn_cons, hf]
    intro hc
    have ⟨hnc, hnr⟩ := ih next (fun y hy => hs y (by simp [hy])) hc
    have ⟨hic, hir⟩ := hnext hnc
    refine ⟨hic, ?_⟩
    change read (forIn xs next f : Id β).run = _
    rw [hnr, hir]
    simp [List.append_assoc]

private theorem cleanLoop_array_census {α β γ : Type} (Clean : β → Prop) (read : β → List γ)
    (emit : α → List γ) (f : α → β → Id (ForInStep β)) (xs : Array α) (init : β)
    (step : ∀ x ∈ xs, ∀ st, ∃ next, f x st = .yield next ∧
      (Clean next → Clean st ∧ read next = read st ++ emit x)) :
    Clean (forIn xs init f : Id β).run →
    Clean init ∧ read (forIn xs init f : Id β).run = read init ++ xs.toList.flatMap emit := by
  rw [← Array.forIn_toList]
  exact cleanLoop_census Clean read emit f xs.toList init
    (fun x hx => step x (by simpa using hx))

/-- Word shaping state: emitted fragments and the
buffered glyphs; loss ledgers survive every flush. -/
private structure WordAcc where
  items : Array Item := #[]
  offsets : Std.HashMap Nat Sp := {}
  sources : Array (Nat × Nat) := #[]
  box : Array (Nat × Char × Sp) := #[]
  owners : Array Attribution := #[]
  sourceIds : Array Nat := #[]
  width : Sp := 0
  missing : Array (Nat × Char) := #[]
  substs : Array (Nat × Char × Nat) := #[]
  sites : GlyphOrigins := #[]

private def WordAcc.chars (st : WordAcc) : List Char :=
  st.items.toList.flatMap Item.boxChars ++ st.box.toList.map (·.2.1)

private def WordAcc.Clean (st : WordAcc) : Prop :=
  st.missing = #[] ∧ st.substs = #[]

private def WordAcc.flush (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (st : WordAcc) : WordAcc :=
  let (items, offsets, sources) := flushWord fontIdx color link size leading decorations ground attr
    st.items st.offsets st.sources st.box st.owners st.sourceIds st.width
  { st with items, offsets, sources, box := #[], owners := #[], sourceIds := #[], width := 0 }

private theorem WordAcc.flush_chars (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (st : WordAcc) :
    (st.flush fontIdx color link size leading decorations ground attr).chars = st.chars := by
  simpa [WordAcc.flush, WordAcc.chars] using
    flushWord_boxChars fontIdx color link size leading decorations ground attr
      st.items st.offsets st.sources st.box st.owners st.sourceIds st.width

private theorem WordAcc.flush_clean (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (st : WordAcc) :
    (st.flush fontIdx color link size leading decorations ground attr).Clean ↔ st.Clean := by
  rfl

/-- Append a glyph, keeping missing and substituted glyphs in the loss ledgers. -/
private def WordAcc.glyph (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (smallcaps : Bool)
    (fs : FontSet) (font : Font) (c : Char) (sourceId : Nat)
    (owner : Attribution) (origin : Option Span) (st : WordAcc) : WordAcc :=
  match glyphOfSc smallcaps size font c with
  | some g =>
    let ks := kernVal Ir.features size font st.box g.1
    { st with box := (kernApply st.box ks).push g, owners := st.owners.push owner
              sourceIds := st.sourceIds.push sourceId, width := st.width + ks + g.2.2 }
  | none =>
    match fs.fallbackFor c |>.bind fun fb =>
        (glyphOfSc smallcaps size (fs.get fb) c).map (fb, ·) with
    | some (fb, g) =>
      let st := st.flush fontIdx color link size leading decorations ground attr
      -- Read before the update, so the update writes `items` in place.
      let n := st.items.size
      let st := { st with sources := st.sources.push (sourceId, n),
                           items := st.items.push (.box g.2.2 fb color link #[g] size {leading}
                             decorations 0 ground owner) }
      if st.substs.any (fun e => e.1 == fontIdx && e.2.1 == c) then st
      else { st with substs := st.substs.push (fontIdx, c, fb)
                     sites := rememberGlyph st.sites .W0009 fontIdx c origin }
    | none =>
      if st.missing.contains (fontIdx, c) then st
      else { st with missing := st.missing.push (fontIdx, c)
                     sites := rememberGlyph st.sites .E0405 fontIdx c origin }

private theorem WordAcc.glyph_chars (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (smallcaps : Bool)
    (fs : FontSet) (font : Font) (c : Char) (sourceId : Nat)
    (owner : Attribution) (origin : Option Span) (st : WordAcc) :
    (st.glyph fontIdx color link size leading decorations ground attr smallcaps
      fs font c sourceId owner origin).Clean →
    st.Clean ∧
      (st.glyph fontIdx color link size leading decorations ground attr smallcaps
        fs font c sourceId owner origin).chars = st.chars ++ [c] := by
  unfold WordAcc.glyph
  split
  · rename_i g hg
    intro h
    refine ⟨h, ?_⟩
    simp only [WordAcc.chars, Array.toList_push, List.map_append, List.map_cons,
      List.map_nil, kernApply_sourceChars, glyphOfSc_char _ _ _ _ _ hg, List.append_assoc]
  · split
    · rename_i fb g _
      dsimp only
      split
      · rename_i h
        intro hc
        have he : st.substs = #[] := hc.2
        simp [WordAcc.flush, he] at h
      · intro hc
        have he := congrArg Array.size hc.2
        simp [WordAcc.flush] at he
    · split
      · rename_i h
        intro hc
        simp [hc.1] at h
      · intro hc
        have he := congrArg Array.size hc.1
        simp at he

private def WordAcc.letters (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (smallcaps : Bool)
    (fs : FontSet) (font : Font) (run : Array Char) (start : Nat)
    (owners : Array Attribution) (origins : Array (Option Span)) (breaks : Array Nat)
    (hyphW : Sp) (st : WordAcc) : WordAcc := Id.run do
  let mut st := st
  for (c, k) in run.zipIdx do
    if breaks.contains k then
      st := st.flush fontIdx color link size leading decorations ground attr
      st := { st with items := st.items.push (.pen hyphW hyphenPenalty true fontIdx color
        (hyphenGlyph size font)) }
    st := st.glyph fontIdx color link size leading decorations ground attr smallcaps fs font c
      (start + k) (owners[start + k]?.getD attr) (origins[start + k]?.getD none)
  return st

private theorem WordAcc.letters_chars (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (smallcaps : Bool)
    (fs : FontSet) (font : Font) (run : Array Char) (start : Nat)
    (owners : Array Attribution) (origins : Array (Option Span)) (hyphW : Sp) (st : WordAcc) :
    (st.letters fontIdx color link size leading decorations ground attr smallcaps fs font
      run start owners origins #[] hyphW).Clean →
    st.Clean ∧
      (st.letters fontIdx color link size leading decorations ground attr smallcaps fs font
        run start owners origins #[] hyphW).chars = st.chars ++ run.toList := by
  unfold WordAcc.letters
  simp only [Array.contains_empty, Bool.false_eq_true, ↓reduceIte, Id.run]
  have h := cleanLoop_array_census WordAcc.Clean WordAcc.chars
    (fun x : Char × Nat => [x.1])
    (fun x st => pure (.yield (st.glyph fontIdx color link size leading decorations ground attr
      smallcaps fs font x.1 (start + x.2) (owners[start + x.2]?.getD attr)
        (origins[start + x.2]?.getD none))))
    run.zipIdx st (by
      intro x _ st
      refine ⟨_, rfl, ?_⟩
      exact WordAcc.glyph_chars fontIdx color link size leading decorations ground attr
        smallcaps fs font x.1 (start + x.2) (owners[start + x.2]?.getD attr)
          (origins[start + x.2]?.getD none) st)
  simpa only [bind, pure, Id.run, Array.toList_zipIdx, ← List.map_eq_flatMap,
    List.zipIdx_map_fst] using h

private def wordItemChars (c : Char) : List Char :=
  if Nfc.isLetter c then [c]
  else if (fixedSpace c).isSome || c == '\u00a0' then [] else [c]

private theorem wordItemChars_letters (xs : List Char)
    (h : ∀ c ∈ xs, Nfc.isLetter c = true) :
    xs.flatMap wordItemChars = xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    have hcs := ih (fun x hx => h x (by simp [hx]))
    simp [wordItemChars, hc, hcs]

/-- One word into items: boxes split at hyphenation points and at the breaks `explicitBreak`
prices, a scalar the styled face lacks set from the fallback face or dropped. -/
private def wordItems (pats : Option Hyphen.Patterns) (langKey : String)
    (explicitBreak : Option Char → Char → Option Char → Option Nat)
    (size : Sp) (leading : Option Sp) (fontIdx : Nat)
    (color : Ir.Color) (ground : Option Ir.Color) (link : Option String)
    (decorations : Decorations) (smallcaps : Bool) (attr : Attribution)
    (fs : FontSet) (font : Font) (chars : Array Char) (missing : Array (Nat × Char))
    (substs : Array (Nat × Char × Nat)) (cache : Std.HashMap String (Array Nat))
    (owners : Array Attribution) (origins : Array (Option Span)) (sites : GlyphOrigins) :
    Array Item × Array (Nat × Char) × Array (Nat × Char × Nat) ×
      Std.HashMap String (Array Nat) × Std.HashMap Nat Sp × Array (Nat × Nat) × GlyphOrigins := Id.run do
  let mut st : WordAcc := { missing, substs, sites }
  let mut cache := cache
  let hyphW := (hyphenGlyph size font).foldl (fun w (_, _, adv) => w + adv) 0
  let mut i := 0
  for _ in [0:chars.size + 1] do
    if h : i < chars.size then
      let c := chars[i]
      if Nfc.isLetter c then
        let (j, run) := letterRun chars i
        let word := String.ofList run.toList
        -- The key carries the language: a word's breaks never answer for another language.
        let key := langKey ++ ":" ++ word
        let mut breaks : Array Nat := #[]
        match pats with
        | some p =>
          match cache[key]? with
          | some b => breaks := b
          | none =>
            let b := Hyphen.hyphenate p word
            cache := cache.insert key b
            breaks := b
        | none => pure ()
        st := st.letters fontIdx color link size leading decorations ground attr smallcaps fs font
          run i owners origins breaks hyphW
        i := j
      else
        match fixedSpace c with
        | some (num, den) =>
          -- A fixed space is a kern, never a breakpoint.
          st := st.flush fontIdx color link size leading decorations ground attr
          -- Read before the update, so the update writes `items` in place.
          let n := st.items.size
          st := { st with
            sources := st.sources.push (i, n)
            items := st.items.push (.box (size * num / den) fontIdx color link #[] size {leading}
              decorations 0 ground (owners[i]?.getD attr)) }
          i := i + 1
        | none =>
          if c == '\u00a0' then
            -- A no-break space is an interword space that is not glue.
            st := st.flush fontIdx color link size leading decorations ground attr
            let n := st.items.size
            st := { st with
              sources := st.sources.push (i, n)
              items := st.items.push (.box (scaledAt size font font.spaceAdvance) fontIdx color link #[] size {leading}
                  decorations 0 ground (owners[i]?.getD attr)) }
            i := i + 1
          else
            let brk := explicitBreak (if i == 0 then none else chars[i - 1]?) c chars[i + 1]?
            st := st.glyph fontIdx color link size leading decorations ground attr smallcaps fs font c i
              (owners[i]?.getD attr) (origins[i]?.getD none)
            i := i + 1
            if let some cost := brk then
              st := st.flush fontIdx color link size leading decorations ground attr
              st := { st with items := st.items.push (.pen 0 cost false fontIdx color #[]) }
    else
      break
  st := st.flush fontIdx color link size leading decorations ground attr
  return (st.items, st.missing, st.substs, cache, st.offsets, st.sources, st.sites)

private def WordAcc.Prefix (chars : Array Char) (missing : Array (Nat × Char))
    (substs : Array (Nat × Char × Nat)) (i : Nat) (st : WordAcc) : Prop :=
  i ≤ chars.size ∧ (st.Clean → missing = #[] ∧ substs = #[] ∧
    st.chars = (chars.toList.take i).flatMap wordItemChars)

private theorem wordItems_none_chars (langKey : String)
    (explicitBreak : Option Char → Char → Option Char → Option Nat)
    (size : Sp) (leading : Option Sp) (fontIdx : Nat)
    (color : Ir.Color) (ground : Option Ir.Color) (link : Option String)
    (decorations : Decorations) (smallcaps : Bool) (attr : Attribution)
    (fs : FontSet) (font : Font) (chars : Array Char) (missing : Array (Nat × Char))
    (substs : Array (Nat × Char × Nat)) (cache : Std.HashMap String (Array Nat))
    (owners : Array Attribution) (origins : Array (Option Span)) (sites : GlyphOrigins) :
    let out := wordItems none langKey explicitBreak size leading fontIdx color ground link
      decorations smallcaps attr fs font chars missing substs cache owners origins sites
    out.2.1 = #[] → out.2.2.1 = #[] →
      missing = #[] ∧ substs = #[] ∧
        out.1.toList.flatMap Item.boxChars = chars.toList.flatMap wordItemChars := by
  unfold wordItems
  dsimp only
  apply Loop.bind_of_inv
    (P := fun st : WordAcc × Std.HashMap String (Array Nat) × Nat =>
      st.1.Prefix chars missing substs st.2.2 ∧ chars.size ≤ st.2.2)
    (Q := fun out : Array Item × Array (Nat × Char) × Array (Nat × Char × Nat) ×
        Std.HashMap String (Array Nat) × Std.HashMap Nat Sp × Array (Nat × Nat) × GlyphOrigins =>
      out.2.1 = #[] → out.2.2.1 = #[] →
        missing = #[] ∧ substs = #[] ∧
          out.1.toList.flatMap Item.boxChars = chars.toList.flatMap wordItemChars)
  · apply cursorLoop_range_complete
      (P := fun st : WordAcc × Std.HashMap String (Array Nat) × Nat =>
        st.1.Prefix chars missing substs st.2.2)
      (pos := fun st => st.2.2) (n := chars.size)
    · refine ⟨Nat.zero_le _, ?_⟩
      intro hc
      exact ⟨hc.1, hc.2, by simp [WordAcc.chars]⟩
    · change chars.size ≤ 0 + (chars.size + 1)
      omega
    · intro k _ state hp
      rcases state with ⟨st, cache, i⟩
      rcases hp with ⟨hi, hp⟩
      dsimp only at hi hp
      dsimp only
      by_cases hin : i < chars.size
      · simp only [hin, ↓reduceDIte, Id.run]
        by_cases hl : Nfc.isLetter chars[i] = true
        · simp only [hl, ↓reduceIte]
          have ⟨_, hj, hrun, hletters⟩ := letterRun_prefix chars i hi
          refine ⟨⟨hj, ?_⟩, letterRun_advances chars i hin hl⟩
          intro hc
          obtain ⟨hcprev, hchars⟩ := WordAcc.letters_chars fontIdx color link size leading decorations
            ground attr smallcaps fs font (letterRun chars i).2 i owners origins _ st hc
          obtain ⟨hm, hs, hpchars⟩ := hp hcprev
          refine ⟨hm, hs, ?_⟩
          rw [hchars, hpchars, hrun, List.flatMap_append]
          have hcensus : (letterRun chars i).2.toList.flatMap wordItemChars =
              (letterRun chars i).2.toList := by
            exact wordItemChars_letters _ (fun c hc => hletters c (by simpa using hc))
          rw [hcensus]
        · simp only [hl]
          cases hf : fixedSpace chars[i] with
          | some nd =>
            rcases nd with ⟨num, den⟩
            refine ⟨⟨Nat.succ_le_of_lt hin, ?_⟩, Nat.lt_succ_self i⟩
            intro hc
            obtain ⟨hm, hs, hpchars⟩ := hp hc
            refine ⟨hm, hs, ?_⟩
            rw [List.take_succ_eq_append_getElem (l := chars.toList)
              (by simpa only [Array.length_toList] using hin)]
            simpa [WordAcc.chars, Item.boxChars, wordItemChars, hl, hf] using
              (WordAcc.flush_chars fontIdx color link size leading decorations ground attr st).trans hpchars
          | none =>
            by_cases hnb : (chars[i] == '\u00a0') = true
            · simp only [hnb, ↓reduceIte]
              refine ⟨⟨Nat.succ_le_of_lt hin, ?_⟩, Nat.lt_succ_self i⟩
              intro hc
              obtain ⟨hm, hs, hpchars⟩ := hp hc
              refine ⟨hm, hs, ?_⟩
              rw [List.take_succ_eq_append_getElem (l := chars.toList)
                (by simpa only [Array.length_toList] using hin)]
              simpa [WordAcc.chars, Item.boxChars, wordItemChars, hl, hf, hnb] using
                (WordAcc.flush_chars fontIdx color link size leading decorations ground attr st).trans hpchars
            · simp only [hnb]
              cases hh : explicitBreak (if i == 0 then none else chars[i - 1]?) chars[i]
                  chars[i + 1]? with
              | some cost =>
                simp only
                refine ⟨⟨Nat.succ_le_of_lt hin, ?_⟩, Nat.lt_succ_self i⟩
                intro hc
                have hg := WordAcc.glyph_chars fontIdx color link size leading decorations ground attr
                  smallcaps fs font chars[i] i (owners[i]?.getD attr) (origins[i]?.getD none) st hc
                obtain ⟨hm, hs, hpchars⟩ := hp hg.1
                refine ⟨hm, hs, ?_⟩
                rw [List.take_succ_eq_append_getElem (l := chars.toList)
                  (by simpa only [Array.length_toList] using hin)]
                simpa [WordAcc.chars, Item.boxChars, wordItemChars, hl, hf, hnb] using
                  (WordAcc.flush_chars fontIdx color link size leading decorations ground attr
                    (st.glyph fontIdx color link size leading decorations ground attr smallcaps fs font
                      chars[i] i (owners[i]?.getD attr) (origins[i]?.getD none))).trans
                    (hg.2.trans (congrArg (· ++ [chars[i]]) hpchars))
              | none =>
                simp only
                refine ⟨⟨Nat.succ_le_of_lt hin, ?_⟩, Nat.lt_succ_self i⟩
                intro hc
                have hg := WordAcc.glyph_chars fontIdx color link size leading decorations ground attr
                  smallcaps fs font chars[i] i (owners[i]?.getD attr) (origins[i]?.getD none) st hc
                obtain ⟨hm, hs, hpchars⟩ := hp hg.1
                refine ⟨hm, hs, ?_⟩
                rw [List.take_succ_eq_append_getElem (l := chars.toList)
                  (by simpa only [Array.length_toList] using hin)]
                simpa [wordItemChars, hl, hf, hnb, hpchars] using hg.2
      · simp only [hin, ↓reduceDIte, Id.run]
        exact ⟨⟨hi, hp⟩, Nat.le_of_not_gt hin⟩
  · intro state hs
    rcases state with ⟨st, cache, i⟩
    rcases hs with ⟨⟨hi, hp⟩, hdone⟩
    dsimp only at hi hp hdone
    have heq : i = chars.size := by omega
    intro hm hs
    have hc : st.Clean := ⟨hm, hs⟩
    have hprefix := hp hc
    refine ⟨hprefix.1, hprefix.2.1, ?_⟩
    simpa [heq, WordAcc.flush, WordAcc.chars, ← Array.length_toList] using
      (WordAcc.flush_chars fontIdx color link size leading decorations ground attr st).trans
        hprefix.2.2

/-- Interword glue: the face's space advance, stretching by half and shrinking
by a third, as TeX's plain fonts and LuaTeX's OpenType faces set it. -/
private def interword (size : Sp) (font : Font) : Glue :=
  let w := scaledAt size font font.spaceAdvance
  { width := w, stretch := w / 2, shrink := w / 3, word := true }

private theorem interword_word_exact (size : Sp) (font : Font) :
    (interword size font).word = true := rfl

/-- The engine's ragged setting as an item transform: interword glue keeps its
natural width, never shrinks, and gains finite stretch of six times its width. -/
public def raggedItems (items : Array Item) : Array Item :=
  items.map fun it =>
    match it with
    | .glue g =>
      if g.fil then it
      else .glue { width := g.width, stretch := g.width * 6, word := g.word }
    | .decoratedGlue g r =>
      if g.fil then it
      else
        let g' : Glue := { width := g.width, stretch := g.width * 6, word := g.word }
        .decoratedGlue g' r
    | .box .. | .pen .. | .img .. | .rule .. | .poly .. => it

/-- Ragged setting for display lines: interword glue gains finite stretch and
the closing parfill stretches by half the measure, balancing the lines. -/
public def displayItems (target : Sp) (items : Array Item) : Array Item :=
  items.map fun it =>
    match it with
    | .glue g =>
      if g.fil && !g.parfill then it
      else if g.parfill then .glue { width := g.width,
                                     stretch := max 0 (target / 2),
                                     parfill := true }
      else .glue { width := g.width, stretch := g.width * 6, word := g.word }
    | .decoratedGlue g r =>
      if g.fil && !g.parfill then it
      else
        let g' : Glue := if g.parfill then
          { width := g.width, stretch := max 0 (target / 2), parfill := true }
        else
          { width := g.width, stretch := g.width * 6, word := g.word }
        .decoratedGlue g' r
    | .box .. | .pen .. | .img .. | .rule .. | .poly .. => it

/-- The scalars a run's leaves ask a face for beyond its plain
text: formula scalars into `math`, icon glyphs into `icons`. -/
private def leafScalars (icons math : Array Char) (xs : Array Ir.Inline) :
    Array Char × Array Char :=
  Ir.foldInlines (fun acc x =>
    match x with
    | .formula _ _ body => (acc.1, Math.MList.scalarsList acc.2 body)
    | .icon c _ => (acc.1.push c, acc.2)
    | _ => acc) (icons, math) xs

/-- The census accumulator: the plain texts a document's faces
are asked for and, separately, its formulas' scalars. -/
private structure ScalarAcc where
  texts : Array String := #[]
  math : Array Char := #[]
  /-- The locale whose furniture words the census counts as shipped text. -/
  locale : Locale := Locale.en

/-- The plain text of a run and its formula and icon scalars. -/
private def textAndMath (out : ScalarAcc) (xs : Array Ir.Inline) : ScalarAcc :=
  let (icons, math) := leafScalars #[] out.math xs
  { out with
    texts := (out.texts.push (Ir.plainText xs)).push
      (String.ofList icons.toList)
    math }

mutual

private def scalarTextList (out : ScalarAcc) (itemD enumD : Nat) :
    List Block → ScalarAcc
  | [] => out
  | b :: rest => scalarTextList (scalarTextOne out itemD enumD b) itemD enumD rest

private def scalarTextOne (out : ScalarAcc) (itemD enumD : Nat) :
    Block → ScalarAcc
  | .para xs => textAndMath out xs
  | .equation num xs => textAndMath (textAndMath out num) xs
  | .section _ _ num title =>
    textAndMath { out with texts := out.texts.push (num.getD "") } title
  | .bibliography _ _ items =>
    items.foldl (fun out item => textAndMath out item.content) out
  | .list ordered items =>
    let (itemD, enumD) := if ordered then (itemD, enumD + 1) else (itemD + 1, enumD)
    let level := min (if ordered then enumD else itemD) 4
    scalarTextItems { out with texts := out.texts.push (ListMark.scalars ordered level) } itemD enumD items.toList
  | .center body => scalarTextList out itemD enumD body.toList
  | .ragged _ body => scalarTextList out itemD enumD body.toList
  | .quote body => scalarTextList out itemD enumD body.toList
  | .abstract body =>
    scalarTextList { out with texts := out.texts.push out.locale.abstract } itemD enumD body.toList
  | .titled _ title body => scalarTextList (textAndMath out title) itemD enumD body.toList
  | .disclosure summary _ body =>
    scalarTextList (textAndMath out (Ir.disclosureSummary summary)) itemD enumD body.toList
  | .role _ body => scalarTextList out itemD enumD body.toList
  | .link _ body => scalarTextList out itemD enumD body.toList
  | .spaced _ body => scalarTextList out itemD enumD body.toList
  | .columns cols => scalarTextCols out itemD enumD cols.toList
  | .onSteps _ body => scalarTextList out itemD enumD body.toList
  | .altSteps _ active otherwise =>
    scalarTextList (scalarTextList out itemD enumD active.toList) itemD enumD
      otherwise.toList
  | .only _ body => scalarTextList out itemD enumD body.toList
  | .nav _ body => scalarTextList out itemD enumD body.toList
  -- A note is set in neither backend's pages.
  | .note _ => out
  | .logo content => textAndMath out content
  | .verbatim _ s spec =>
    let out := { out with texts := out.texts.push s }
    let out := if spec.numbers then
        { out with texts := out.texts.push "0123456789\u00a0" } else out
    match spec.caption with
    | some (n, cap) =>
      textAndMath { out with texts := out.texts.push s!"{out.locale.listing} {n}: " } cap
    | none => out
  | .rule _ _ _ => out
  | .pagebreak => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .picture pic => pic.labelContents.foldl textAndMath out
  | .frame title _ _ _ body =>
    scalarTextList (textAndMath out title) itemD enumD body.toList
  | .framefoot content => textAndMath out content
  | .table _ _ _ rows _ _ => scalarTextTableRows out rows.toList
  | .algorithm numbered _ lines =>
    let words := Ir.algWords out.locale.tag
    let texts := (out.texts ++ (Ir.AlgWords.all words).toArray).push ":; /**/"
    let texts := if numbered then texts.push "0123456789" else texts
    scalarTextAlgLines { out with texts := texts } lines.toList
  | .float _ _ _ body caption =>
    scalarTextList (textAndMath out caption) itemD enumD body.toList

private def scalarTextAlgLines (out : ScalarAcc) : List Ir.AlgLine → ScalarAcc
  | [] => out
  | l :: rest =>
    scalarTextAlgLines (match l.comment with
      | some c => textAndMath (textAndMath out l.content) c
      | none => textAndMath out l.content) rest

private def scalarTextTableRows (out : ScalarAcc) :
    List (Array (Array Inline)) → ScalarAcc
  | [] => out
  | row :: rest => scalarTextTableRows (scalarTextTableCells out row.toList) rest

private def scalarTextTableCells (out : ScalarAcc) :
    List (Array Inline) → ScalarAcc
  | [] => out
  | cell :: rest => scalarTextTableCells (textAndMath out cell) rest

private def scalarTextCols (out : ScalarAcc) (itemD enumD : Nat) :
    List (BoxWidth × Array Block) → ScalarAcc
  | [] => out
  | (_, body) :: rest =>
    scalarTextCols (scalarTextList out itemD enumD body.toList) itemD enumD rest

private def scalarTextItems (out : ScalarAcc) (itemD enumD : Nat) :
    List (Array Block) → ScalarAcc
  | [] => out
  | bs :: rest =>
    scalarTextItems (scalarTextList out itemD enumD bs.toList) itemD enumD rest

end

/-- Every scalar the document's text can ask a face for, sorted,
so the driver can precompute `FontSet.fallback` before layout. -/
private def docScalarAcc (doc : Doc) : ScalarAcc := Id.run do
  let mut acc : ScalarAcc :=
    scalarTextList { locale := doc.info.locale } 0 0 doc.body.toList
  if let some h := doc.head then
    acc := textAndMath acc h |> fun a => { a with texts := a.texts.push "0123456789" }
  if let some f := doc.foot then
    acc := textAndMath acc f |> fun a => { a with texts := a.texts.push "0123456789" }
  else if doc.pageNumbersOn then
    -- The class-default foot ships undeclared digits.
    acc := { acc with texts := acc.texts.push "0123456789" }
  if doc.lineNumbersOn then
    -- Margin line numbers ship undeclared digits too.
    acc := { acc with texts := acc.texts.push "0123456789" }
  if let some hl := doc.headline then
    acc := textAndMath acc hl.title
    acc := textAndMath acc hl.author
    acc := textAndMath acc hl.institute
  for slot in [doc.logoLeft, doc.logoRight] do
    if let some content := slot then
      acc := textAndMath acc content
  for (_, st) in doc.styles.entries do
    if let some tpl := st.font then
      acc := { acc with texts := acc.texts.push (Ir.plainText tpl) }
    if let some m := st.marker then
      acc := { acc with texts := acc.texts.push (Ir.plainText m) }
  return acc

/-- The scalars the document's formulas ask the math face
for; nonempty exactly when a math face is needed. -/
public def docMathScalars (doc : Doc) : Array Char :=
  (docScalarAcc doc).math

public theorem resolveMathAlphas_layout_agree (coverage : Math.MathAlphabetCoverage)
    (body : Math.MList) :
    docMathScalars { body := #[.para
      #[.formula false "" (Math.resolveMathAlphas coverage body)]] } =
        Math.MList.scalarsList #[] (Math.resolveMathAlphas coverage body) := by
  rfl

public def docScalars (doc : Doc) : Array Char := Id.run do
  let acc := docScalarAcc doc
  let texts := acc.texts.push (String.ofList acc.math.toList)
  -- ASCII in a bitmap and the rest deduplicated after, cheaper than a hash insert per character.
  let skip (c : Char) : Bool :=
    c == ' ' || c == '\n' || c == '\t' || c == '\u00a0' || (fixedSpace c).isSome
  let mut ascii : Array Bool := Array.replicate 128 false
  let mut rest : Array Char := #[]
  for t in texts do
    ascii := t.foldl (init := ascii) fun a c =>
      if c.toNat < 128 && !skip c then
        let a := a.set! c.toNat true
        if c.isLower then a.set! c.toUpper.toNat true else a
      else a
    rest := t.foldl (init := rest) fun a c =>
      if c.toNat >= 128 && !skip c then a.push c else a
  let mut set : Std.HashSet Char := {}
  for c in rest do
    set := set.insert c
  let mut out : Array Char := #[]
  for n in [0:128] do
    if ascii[n]! then
      out := out.push (Char.ofNat n)
  return out ++ set.toArray.qsort (· < ·)

/-- Push the face key a styled context resolves to: every key when
`corners`, else only one off the regular and bold corners. -/
private def pushWeightKey (corners : Bool) (acc : Array (Nat × Nat × Bool)) (sty : TextStyle) :
    Array (Nat × Nat × Bool) :=
  let w := sty.weight.css
  if !corners && (w == 400 || w == 700) then acc
  else
    let key := (sty.slot, w, sty.italic)
    if acc.contains key then acc else acc.push key

private def setsText (s : String) : Bool := s.any fun c => !c.isWhitespace

mutual
-- conserves: none — a key census, no ink; hand-rolled, as the key reads the styled ancestry.
private def weightKeysInline (corners : Bool) (acc : Array (Nat × Nat × Bool)) (sty : TextStyle) :
    Ir.Inline → Array (Nat × Nat × Bool)
  | .styled st body =>
    -- The ladder never moves a weight (`weight_agree`), so the engine scale serves.
    let sty := applyStyle Ir.sizeScale sty st
    weightKeysInlineList corners (if corners then acc else pushWeightKey corners acc sty) sty
      body.toList
  | .located _ body => weightKeysInlineList corners acc sty body.toList
  | .colored _ _ body => weightKeysInlineList corners acc sty body.toList
  | .role _ body => weightKeysInlineList corners acc sty body.toList
  | .link _ body => weightKeysInlineList corners acc sty body.toList
  | .decorated _ body => weightKeysInlineList corners acc sty body.toList
  | .onSteps _ body => weightKeysInlineList corners acc sty body.toList
  | .altSteps _ active otherwise =>
    weightKeysInlineList corners (weightKeysInlineList corners acc sty active.toList) sty otherwise.toList
  -- A note body sets at the page foot in the base style, not the mark's.
  | .footnote _ body => weightKeysInlineList corners acc {} body.toList
  | .text s => if corners && setsText s then pushWeightKey true acc sty else acc
  | .ref _ _ _ _ => if corners then pushWeightKey true acc sty else acc
  | .cite _ _ => if corners then pushWeightKey true acc sty else acc
  | .pageNumber => if corners then pushWeightKey true acc sty else acc
  | .pageCount => if corners then pushWeightKey true acc sty else acc
  | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .linebreak _ => acc

private def weightKeysInlineList (corners : Bool) (acc : Array (Nat × Nat × Bool))
    (sty : TextStyle) : List Ir.Inline → Array (Nat × Nat × Bool)
  | [] => acc
  | x :: rest => weightKeysInlineList corners (weightKeysInline corners acc sty x) sty rest
end

/-- The content an element sets, as layout fills it: in its template
(`Ir.fillTemplate`) where one is declared, else as written. -/
private def templated (tpl : Option (Array Ir.Inline)) (content : Array Ir.Inline) :
    Array Ir.Inline :=
  match tpl with
  | some t => Ir.fillTemplate t content
  | none => content

/-- A heading's base style where no template sets it: bold. -/
private def headingBase (tpl : Option (Array Ir.Inline)) : TextStyle :=
  if tpl.isSome then {} else { weight := .b }

mutual
-- conserves: none — the key census over blocks, no ink.
private def weightKeysBlock (corners : Bool) (styles : Ir.Styles) (slides : Bool)
    (acc : Array (Nat × Nat × Bool)) : Ir.Block → Array (Nat × Nat × Bool)
  | .para content => weightKeysInlineList corners acc {} content.toList
  | .equation num content =>
    weightKeysInlineList corners (weightKeysInlineList corners acc {} content.toList) {} num.toList
  | .section level _ _ title =>
    if corners then
      let own := (styles.find? level.element).bind (·.font)
      let acc := weightKeysInlineList corners acc (headingBase own) (templated own title).toList
      -- A deck's top-level section may also stand on a section page, so both templates are read.
      if slides && level == 1 then
        let page := (styles.find? "sectionpage").bind (·.font)
        weightKeysInlineList corners acc (headingBase page) (templated page title).toList
      else acc
    else weightKeysInlineList corners acc {} title.toList
  | .list _ items => weightKeysBlockItems corners styles slides acc items.toList
  | .center body => weightKeysBlockList corners styles slides acc body.toList
  | .ragged _ body => weightKeysBlockList corners styles slides acc body.toList
  | .quote body => weightKeysBlockList corners styles slides acc body.toList
  | .abstract body =>
    -- The abstract heading is the locale's word, and any word stands for its face key.
    let acc := if corners then
        match (Ir.abstractHeadingStyle styles).font with
        | some tpl => weightKeysInlineList corners acc {} (Ir.fillTemplate tpl #[.text "Abstract"]).toList
        | none => acc
      else acc
    weightKeysBlockList corners styles slides acc body.toList
  | .titled kind title body =>
    let shown := if corners then templated (Ir.blockTitleFont styles kind) title else title
    weightKeysBlockList corners styles slides (weightKeysInlineList corners acc {} shown.toList)
      body.toList
  | .disclosure summary _ body =>
    weightKeysBlockList corners styles slides
      (weightKeysInlineList corners acc {} (Ir.disclosureSummary summary).toList) body.toList
  | .role _ body => weightKeysBlockList corners styles slides acc body.toList
  | .link _ body => weightKeysBlockList corners styles slides acc body.toList
  | .spaced _ body => weightKeysBlockList corners styles slides acc body.toList
  | .columns cols => weightKeysBlockCols corners styles slides acc cols.toList
  | .onSteps _ body => weightKeysBlockList corners styles slides acc body.toList
  | .altSteps _ active otherwise =>
    weightKeysBlockList corners styles slides
      (weightKeysBlockList corners styles slides acc active.toList) otherwise.toList
  | .only _ body => weightKeysBlockList corners styles slides acc body.toList
  | .nav _ body => weightKeysBlockList corners styles slides acc body.toList
  | .note body => weightKeysBlockList corners styles slides acc body.toList
  | .frame title standout _ _ body =>
    if corners then
      -- A frame title sets in its template under a themed bar, bold without one: both are read.
      let tpl := (styles.find? "frametitle").bind (·.font)
      let acc := weightKeysInlineList corners acc { weight := .b } title.toList
      let acc := match tpl with
        | some t => weightKeysInlineList corners acc {} (Ir.fillTemplate t title).toList
        | none => acc
      if standout then
        weightKeysStandout corners styles slides ((styles.find? "standout").bind (·.font)) acc
          body.toList
      else weightKeysBlockList corners styles slides acc body.toList
    else
      weightKeysBlockList corners styles slides (weightKeysInlineList corners acc {} title.toList)
        body.toList
  | .framefoot content => weightKeysInlineList corners acc {} content.toList
  | .float _ _ _ body caption =>
    weightKeysBlockList corners styles slides (weightKeysInlineList corners acc {} caption.toList)
      body.toList
  | .table _ _ _ rows _ _ => weightKeysTableRows corners acc rows.toList
  -- The generated keyword bold is a corner face, not an off-corner key.
  | .algorithm _ _ lines =>
    lines.foldl (fun a l =>
      let a := weightKeysInlineList corners a {} l.content.toList
      match l.comment with
      | some c => weightKeysInlineList corners a {} c.toList
      | none => a) acc
  | .logo content => weightKeysInlineList corners acc {} content.toList
  | .picture pic =>
    pic.labelContents.foldl (fun a c => weightKeysInlineList corners a {} c.toList) acc
  | .bibliography _ _ items =>
    items.foldl (fun a it => weightKeysInlineList corners a {} it.content.toList) acc
  -- A listing's token weights are all corners, so only the full census lexes it.
  | .verbatim _ s spec =>
    let acc := match spec.caption with
      | some (_, caption) => weightKeysInlineList corners acc {} caption.toList
      | none => acc
    if corners then
      let mono := applyStyle Ir.sizeScale {} .mono
      (spec.tokenLines s).foldl (fun a line => line.foldl (fun a t =>
        let (bold, italic) := t.kind.role.weights
        let sty := if bold then applyStyle Ir.sizeScale mono .bold else mono
        pushWeightKey true a (if italic then applyStyle Ir.sizeScale sty .italic else sty)) a) acc
    else acc
  | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ => acc

private def weightKeysBlockList (corners : Bool) (styles : Ir.Styles) (slides : Bool)
    (acc : Array (Nat × Nat × Bool)) : List Ir.Block → Array (Nat × Nat × Bool)
  | [] => acc
  | b :: rest =>
    weightKeysBlockList corners styles slides (weightKeysBlock corners styles slides acc b) rest

/-- A standout frame's body: each paragraph in the frame's template, any other block as anywhere. -/
private def weightKeysStandout (corners : Bool) (styles : Ir.Styles) (slides : Bool)
    (tpl : Option (Array Ir.Inline)) (acc : Array (Nat × Nat × Bool)) :
    List Ir.Block → Array (Nat × Nat × Bool)
  | [] => acc
  | b :: rest =>
    let acc := match b with
      | .para content =>
        weightKeysInlineList corners acc (headingBase tpl) (templated tpl content).toList
      | _ => weightKeysBlock corners styles slides acc b
    weightKeysStandout corners styles slides tpl acc rest

private def weightKeysBlockItems (corners : Bool) (styles : Ir.Styles) (slides : Bool)
    (acc : Array (Nat × Nat × Bool)) : List (Array Ir.Block) → Array (Nat × Nat × Bool)
  | [] => acc
  | item :: rest =>
    weightKeysBlockItems corners styles slides
      (weightKeysBlockList corners styles slides acc item.toList) rest

private def weightKeysBlockCols (corners : Bool) (styles : Ir.Styles) (slides : Bool)
    (acc : Array (Nat × Nat × Bool)) :
    List (Ir.BoxWidth × Array Ir.Block) → Array (Nat × Nat × Bool)
  | [] => acc
  | (_, body) :: rest =>
    weightKeysBlockCols corners styles slides
      (weightKeysBlockList corners styles slides acc body.toList) rest

private def weightKeysTableRows (corners : Bool) (acc : Array (Nat × Nat × Bool)) :
    List (Array (Array Ir.Inline)) → Array (Nat × Nat × Bool)
  | [] => acc
  | row :: rest =>
    weightKeysTableRows corners (row.foldl
      (fun a cell => weightKeysInlineList corners a {} cell.toList) acc) rest
end

/-- The face keys the document's runs ask: every key,
or only the off-corner ones (`pushWeightKey`). -/
private def docKeys (corners : Bool) (doc : Doc) : Array (Nat × Nat × Bool) := Id.run do
  let slides := doc.docClass.record.model == .frame
  let mut acc := weightKeysBlockList corners doc.styles slides #[] doc.body.toList
  if let some h := doc.head then
    acc := weightKeysInlineList corners acc {} h.toList
  if let some f := doc.foot then
    acc := weightKeysInlineList corners acc {} f.toList
  if corners then
    if let some hl := doc.headline then
      let tpl := (doc.styles.find? "titlepage").bind (·.font)
      acc := weightKeysInlineList corners acc (headingBase tpl) (templated tpl hl.title).toList
      acc := weightKeysInlineList corners acc {} hl.author.toList
      acc := weightKeysInlineList corners acc {} hl.institute.toList
  else
    for (_, st) in doc.styles.entries do
      if let some tpl := st.font then
        acc := weightKeysInlineList corners acc {} tpl.toList
      if let some tpl := st.authorFont then
        acc := weightKeysInlineList corners acc {} tpl.toList
  return acc

/-- Every off-corner face key the document's styles can ask
`FontSet.lookup` for, so the driver resolves each before layout. -/
public def docWeightKeys (doc : Doc) : Array (Nat × Nat × Bool) := docKeys false doc

/-- Every face key the document's text asks `FontSet.lookup` for, corners included. -/
public def docFaceKeys (doc : Doc) : Array (Nat × Nat × Bool) := docKeys true doc

/-- One mu: 1/18 of an em at the given size (TeXbook p. 168). -/
private def muAt (size : Sp) (mu : Int) : Sp :=
  size * mu / 18

/-- Everything measuring a formula needs: the math face and its constants,
the font set for per-scalar fallback, and the inherited run properties. -/
private structure MathEnv where
  idx : Nat
  font : Font
  consts : MathConsts
  fs : FontSet
  color : Ir.Color
  link : Option String
  decorations : Decorations
  leading : Option Sp
  base : Sp
  /-- Ambient text size, before matching the math face's x-height. -/
  textBase : Sp
  /-- The surrounding text's scaled vertical metrics, kept as the common strut even for scripts. -/
  textAscent : Sp
  textDescent : Sp
  ground : Option Ir.Color := none
  /-- The formula's attribution, its one `Struct` leaf, on every box the assembly builds. -/
  attr : Attribution
  /-- How many grids' cells hold what is laid; at 0 a display alignment sets its rows as lines. -/
  gridDepth : Nat := 0

/-- The font environment for measuring and placing a math
run, its em matching the surrounding face's x-height. -/
private def MathEnv.forRun (fs : FontSet) (idx : Nat) (font : Font)
    (consts : MathConsts) (around : Font) (runSize : Sp) : MathEnv :=
  { idx, font, consts, fs, color := Ir.Color.black, link := none
    decorations := {}, leading := none, attr := .unattributed
    textBase := runSize
    textAscent := scaledAt runSize around around.ascent.toNat
    textDescent := scaledAt runSize around (-around.descent).toNat
    base := (Math.mathSize runSize.toNat around.xHeightOptical
      around.unitsPerEm font.xHeightOptical font.unitsPerEm : Nat) }

/-- Font size at a style: the base for display and text,
the face's declared percentages for script styles. -/
private def MathEnv.sizeAt (e : MathEnv) (st : Math.MathStyle) : Sp :=
  Math.sizeFor e.consts.scales e.base st

/-- A text-sourced math alphabet's size: the surrounding text em on the same script ladder. -/
private def MathEnv.textSizeAt (e : MathEnv) (st : Math.MathStyle) : Sp :=
  Math.sizeFor e.consts.scales e.textBase st

/-- A MATH constant in font design units, scaled at a size. -/
private def MathEnv.constAt (e : MathEnv) (size : Sp) (v : Int) : Sp :=
  v * size / (e.font.unitsPerEm : Int)

/-- A glyph's vertical ink extent `(top, bottom)` at a size,
from its outline, else the cap height and baseline. -/
private def MathEnv.glyphExtent (e : MathEnv) (size : Sp) (g : Nat) : Sp × Sp :=
  match e.font.yExtent g with
  | some (lo, hi) =>
    (hi * size / (e.font.unitsPerEm : Int), lo * size / (e.font.unitsPerEm : Int))
  | none => (e.font.capHeight * size / (e.font.unitsPerEm : Int), 0)

/-- Reserve a formula's reach against its ambient strut, independent of the run's raise. -/
private def MathEnv.metrics (e : MathEnv) (top bottom : Sp) : RunMetrics :=
  { leading := e.leading, math := some {
      size := e.textBase, ascent := e.textAscent, descent := e.textDescent,
      top, bottom } }

/-- A math run's vertical hull, measured in its actual face;
an undecodable outline keeps the face's ascent and descent. -/
private def mathBox (e : MathEnv) (idx : Nat) (w : Sp)
    (glyphs : Array (Nat × Char × Sp)) (size raise : Sp) : Item :=
  let font := e.fs.get idx
  let (top, bottom) := glyphs.foldl (fun (top, bottom) (g, _, _) =>
    let (hi, lo) := match font.yExtent g with
      | some (lo, hi) =>
        (hi * size / (font.unitsPerEm : Int), lo * size / (font.unitsPerEm : Int))
      | none => (font.ascent * size / (font.unitsPerEm : Int),
          font.descent * size / (font.unitsPerEm : Int))
    (max top hi, min bottom lo)) (0, 0)
  .box w idx e.color e.link glyphs size (e.metrics top bottom)
    e.decorations raise e.ground e.attr

/-- A kern in the math stream: width, no glyphs, never a breakpoint. -/
private def mathKern (e : MathEnv) (size w : Sp) : Item :=
  .box w e.idx e.color e.link #[] size (e.metrics 0 0) e.decorations 0 e.ground e.attr

/-- Width of assembled math items, counting a nested construction's
rule before its rewind kern as line placement does. -/
public def mathItemsWidth (items : Array Item) : Sp :=
  items.foldl (fun w it => match it with
    | .box bw _ _ _ _ _ _ _ _ _ _ => w + bw
    | .rule bw _ _ _ => w + bw
    | _ => w) 0

private abbrev MAcc := Array Item × Array (Nat × Char)

/-- Ink bounds relative to the stream's origin and baseline, each glyph
by its own face's outline hull; `paintOnly` keeps only filled ink. -/
private def mathItemsBounds (fs : FontSet) (items : Array Item) (paintOnly : Bool) :
    Option Ink.Bounds := Id.run do
  let mut bounds : Option Ink.Bounds := none
  let mut pen : Sp := 0
  let add (bounds : Option Ink.Bounds) (b : Ink.Bounds) :=
    let b := if paintOnly then
        { left := min b.left b.right, bottom := min b.bottom b.top,
          right := max b.left b.right, top := max b.bottom b.top : Ink.Bounds }
      else b
    some (bounds.map (·.union b) |>.getD b)
  for it in items do
    match it with
    | .box w fi _ _ glyphs size metrics _ raise _ _ =>
      if !paintOnly then
        if let some m := metrics.math then
          bounds := add bounds ⟨pen, raise + m.bottom, pen + w, raise + m.top⟩
      let font := fs.get fi
      let upem : Int := font.unitsPerEm
      let mut gx := pen
      for (g, _, adv) in glyphs do
        match font.bounds g with
        | some b =>
          if !paintOnly || (b.left != b.right && b.bottom != b.top) then
            bounds := add bounds
              ⟨gx + b.left * size / upem, raise + b.bottom * size / upem,
                gx + b.right * size / upem, raise + b.top * size / upem⟩
        | none =>
          bounds := add bounds ⟨gx, raise, gx + adv, raise + font.capHeight * size / upem⟩
        gx := gx + adv
      pen := pen + w
    | .rule w t r _ =>
      if !paintOnly || (w != 0 && t != 0) then
        bounds := add bounds ⟨min pen (pen + w), r, max pen (pen + w), r + t⟩
      pen := pen + w
    | .poly pts _ =>
      -- A clipped polygon may repeat its first vertex, so a distinct one judges its area.
      let paints := pts[0]?.any fun a =>
        (pts.find? (· != a)).any fun b =>
          pts.any fun p =>
            (b.1 - a.1) * (p.2 - a.2) != (b.2 - a.2) * (p.1 - a.1)
      if !paintOnly || paints then
        for (x, y) in pts do
          bounds := add bounds ⟨pen + x, y, pen + x, y⟩
    | .glue _ | .decoratedGlue _ _ | .pen _ _ _ _ _ _ | .img _ _ _ _ => pure ()
  return bounds

/-- Measured attachment ink, without the baseline or nonpainting spacing items. -/
private def mathItemsInk (fs : FontSet) (items : Array Item) : Option Ink.Bounds :=
  mathItemsBounds fs items (paintOnly := true)

/-- The math line's extent, its baseline and spacing items included. -/
private def mathItemsExtent (fs : FontSet) (items : Array Item) : Sp × Sp :=
  match mathItemsBounds fs items (paintOnly := false) with
  | some b => (max 0 b.top, min 0 b.bottom)
  | none => (0, 0)

/-- The same items shifted vertically: every raise moves, no width does. -/
private def raiseItems (delta : Sp) (items : Array Item) : Array Item :=
  if delta == 0 then items else
  items.map fun it => match it with
    | .box w i c l g s ld u r gr a => .box w i c l g s ld u (r + delta) gr a
    | .rule w t r c => .rule w t (r + delta) c
    | .poly pts c => .poly (pts.map fun (x, y) => (x, y + delta)) c
    | .glue g => .glue g
    | .decoratedGlue g r => .decoratedGlue g r
    | .pen w c f i col g => .pen w c f i col g
    | .img s w h i => .img s w h i

/-- The zero-size rule a display alignment leaves at its
last row's baseline, which `LineOut.lastBase` reads. -/
private def alignRowMark (raise : Sp) (color : Ir.Color) : Item := .rule 0 0 raise color

/-- An invisible box reserving the declared reach exactly. -/
private def struts (e : MathEnv) (top bot : Sp) : Array Item :=
  #[.box 0 e.idx e.color e.link #[] 1 (e.metrics (max 0 top) (min 0 bot))
    {} 0 e.ground e.attr]

/-- The size ladder a glyph grows through: its vertical variants, or itself. -/
private def variantLadder (e : MathEnv) (g : Nat) : List (Nat × Int) :=
  let vs := e.font.vertVariants g
  if vs.isEmpty then
    match e.font.yExtent g with
    | some (lo, hi) => [(g, hi - lo)]
    | none => [(g, 0)]
  else vs.toList

/-- Assemble a laid body between delimiters grown to `target`, each centring its
ink on the axis; an empty side is a `\nulldelimiterspace` kern when `nullKern`. -/
private def delimAssembleTo (e : MathEnv) (size raise : Sp) (l r : Option Char)
    (target : Sp) (nullKern : Bool) (bItems : Array Item)
    (missing0 : Array (Nat × Char)) : Array Item × Array (Nat × Char) := Id.run do
  let axis := e.constAt size e.consts.axisHeight
  let (bTop, bBot) := mathItemsExtent e.fs bItems
  let targetDu := target * (e.font.unitsPerEm : Int) / size
  let nd := if nullKern then size * 12 / 100 else 0
  let mut items : Array Item := #[]
  let mut missing := missing0
  let mut top := bTop
  let mut bot := bBot
  let one := fun (c : Char) (items : Array Item) (missing : Array (Nat × Char)) =>
    match glyphOf size e.font c with
    | some (g, _, _) =>
      let (gv, _) := (Math.pickVariant targetDu (variantLadder e g)).getD (g, 0)
      let (vTop, vBot) := e.glyphExtent size gv
      let w := scaledAt size e.font (e.font.widths[gv]?.getD 0)
      let dRaise := raise + axis - (vTop + vBot) / 2
      (items.push (mathBox e e.idx w #[(gv, c, w)] size dRaise),
       missing, dRaise - raise + vTop, dRaise - raise + vBot)
    | none =>
      (items, if missing.contains (e.idx, c) then missing else missing.push (e.idx, c),
       bTop, bBot)
  match l with
  | some c =>
    let (its, m, t, b) := one c items missing
    items := its
    missing := m
    top := max top t
    bot := min bot b
  | none => items := items.push (mathKern e size nd)
  let raisedBody := raiseItems raise bItems
  items := items ++ raisedBody
  match r with
  | some c =>
    let (its, m, t, b) := one c items missing
    items := its
    missing := m
    top := max top t
    bot := min bot b
  | none => items := items.push (mathKern e size nd)
  items := items ++ struts e (raise + top) (raise + bot)
  return (items, missing)

/-- Assemble a laid `\left…\right` body between delimiters grown
to cover its reach from the axis (TeXbook Appendix G rule 19). -/
private def delimAssemble (e : MathEnv) (size raise : Sp) (l r : Option Char)
    (bItems : Array Item) (missing0 : Array (Nat × Char)) :
    Array Item × Array (Nat × Char) :=
  let axis := e.constAt size e.consts.axisHeight
  let (bTop, bBot) := mathItemsExtent e.fs bItems
  let δ := max (bTop - axis) (axis - bBot)
  delimAssembleTo e size raise l r (max (2 * δ * 901 / 1000) (2 * δ - size / 2)) true
    bItems missing0

/-- Assemble laid grid cells as `\halign` does: each column as wide as its widest
cell, rows a baselineskip plus `\jot` apart, the grid centred on the axis. -/
private def gridAssemble (e : MathEnv) (size raise : Sp) (kind : Math.GridKind)
    (cells : Array (Array (Array Item))) : Array Item := Id.run do
  let axis := e.constAt size e.consts.axisHeight
  let n := cells.foldl (fun m row => max m row.size) 0
  if n == 0 then
    return #[]
  let mut colW : Array Sp := Array.replicate n 0
  for row in cells do
    for k in [0:row.size] do
      colW := colW.set! k (max colW[k]! (mathItemsWidth row[k]!))
  let cols : List (Sp × Sp) := (List.range n).map fun k =>
    (colW[k]!, muAt size (kind.gapAfter k n : Int) + kind.pairSep k n)
  let total := Math.colOffset cols n
  let bl := leadingFor size
  -- plain.tex's `\lineskip`, size-relative; a `smallmatrix` declares its own (`GridKind.small`).
  let gridSkip := match kind with
    | .small => size * 15 / 100
    | .array _ _ | .align | .aligned _ | .gather => size / 10
  -- LaTeX's `\jot` (latex.ltx), size-relative; an `array` takes none.
  let jot := match kind with
    | .array _ _ | .small => 0
    | .align | .aligned _ | .gather => size * 3 / 10
  -- An array's rows stand `\arraystretch` baselines apart (latex.ltx, `\@arstrutbox`).
  let pitch := match kind with
    | .array _ s => bl * (s : Int) / 1000
    | .small => size * 6 / 10
    | .align | .aligned _ | .gather => bl
  let rowExtents := cells.map fun row =>
    row.foldl (fun (t, b) cell =>
      let (ct, cb) := mathItemsExtent e.fs cell
      (max t ct, min b cb)) ((0 : Sp), (0 : Sp))
  let mut ys : Array Sp := #[]
  let mut y : Sp := 0
  for i in [0:cells.size] do
    if i > 0 then
      let d := max (pitch + jot)
        ((-(rowExtents[i-1]!.2)) + rowExtents[i]!.1 + gridSkip)
      y := y - d
    ys := ys.push y
  let top := rowExtents[0]!.1
  let bot := y + (rowExtents[cells.size - 1]!).2
  let Δ := raise + axis - (top + bot) / 2
  let mut items : Array Item := #[]
  for i in [0:cells.size] do
    let row := cells[i]!
    let mut cur : Sp := 0
    for k in [0:row.size] do
      let cellItems := row[k]!
      let cw := mathItemsWidth cellItems
      let x := Math.colOffset cols k + (kind.colAlign k).pad colW[k]! cw
      items := items.push (mathKern e size (x - cur))
      items := items ++ raiseItems (Δ + ys[i]!) cellItems
      cur := x + cw
    items := items.push (mathKern e size (total - cur))
    items := items.push (mathKern e size (-total))
  items := items.push (mathKern e size total)
  items := items ++ struts e (Δ + top) (Δ + bot)
  match kind with
  | .small =>
    let thin := mathKern e size (muAt size 3)
    return (#[thin] ++ items).push thin
  | .align | .gather =>
    -- A display alignment's last row rides the line (`alignRowMark`), as TeX sets rows as lines.
    if e.gridDepth == 0 then return items.push (alignRowMark (Δ + ys[cells.size - 1]!) e.color)
    return items
  | .array _ _ | .aligned _ => return items

/-- Assemble a laid fraction (TeXbook Appendix G rule 15 over the MATH
constants), with `\nulldelimiterspace` on each side that carries no delimiter. -/
private def fracAssemble (e : MathEnv) (size : Sp) (display : Bool) (raise : Sp)
    (rule : Option Int) (ndLeft ndRight : Bool)
    (numItems denItems : Array Item) : Array Item :=
  let axis := e.constAt size e.consts.axisHeight
  let θ := max 0 (rule.getD (e.constAt size e.consts.fractionRuleThickness))
  let (numTop, numBot) := mathItemsExtent e.fs numItems
  let (denTop, denBot) := mathItemsExtent e.fs denItems
  let (u, v) :=
    if θ == 0 then
      let u0 := e.constAt size (if display then e.consts.stackTopDisplayStyleShiftUp
        else e.consts.stackTopShiftUp)
      let v0 := e.constAt size (if display then e.consts.stackBottomDisplayStyleShiftDown
        else e.consts.stackBottomShiftDown)
      let φ := e.constAt size (if display then e.consts.stackDisplayStyleGapMin
        else e.consts.stackGapMin)
      let short := φ - ((u0 + numBot) - (denTop - v0))
      if short > 0 then (u0 + short / 2, v0 + (short - short / 2)) else (u0, v0)
    else
      let u0 := e.constAt size (if display then e.consts.fractionNumeratorDisplayStyleShiftUp
        else e.consts.fractionNumeratorShiftUp)
      let v0 := e.constAt size (if display then e.consts.fractionDenominatorDisplayStyleShiftDown
        else e.consts.fractionDenominatorShiftDown)
      let gapN := e.constAt size (if display then e.consts.fractionNumDisplayStyleGapMin
        else e.consts.fractionNumeratorGapMin)
      let gapD := e.constAt size (if display then e.consts.fractionDenomDisplayStyleGapMin
        else e.consts.fractionDenominatorGapMin)
      (max u0 (axis + θ / 2 + gapN - numBot), max v0 (denTop + gapD - (axis - θ / 2)))
  let numW := mathItemsWidth numItems
  let denW := mathItemsWidth denItems
  let ruleW := max numW denW
  let nd := size * 12 / 100
  let numPad := Math.ColAlign.pad .center ruleW numW
  let denPad := Math.ColAlign.pad .center ruleW denW
  let bar : Array Item :=
    if θ == 0 then #[] else #[Item.rule ruleW θ (raise + axis - θ / 2) e.color, mathKern e size (-ruleW)]
  (#[mathKern e size (if ndLeft then nd else 0), mathKern e size numPad]
      ++ raiseItems (raise + u) numItems)
    ++ (#[mathKern e size (ruleW - numPad - numW), mathKern e size (-ruleW)] ++ bar ++
        #[mathKern e size denPad]
      ++ raiseItems (raise - v) denItems)
    ++ #[mathKern e size (ruleW - denPad - denW), mathKern e size (if ndRight then nd else 0)]
    ++ struts e (raise + u + numTop) (raise - v + denBot)

/-- Assemble a laid radical from the MATH radical constants. -/
private def radAssemble (e : MathEnv) (size : Sp) (display : Bool) (raise : Sp)
    (bItems degItems : Array Item) (missing0 : Array (Nat × Char)) :
    Array Item × Array (Nat × Char) :=
  let θ := e.constAt size e.consts.radicalRuleThickness
  let ψ := e.constAt size (if display then e.consts.radicalDisplayStyleVerticalGap
    else e.consts.radicalVerticalGap)
  let (bTop, bBot) := mathItemsExtent e.fs bItems
  let ruleBot := bTop + ψ
  let ruleTop := ruleBot + θ
  let bodyW := mathItemsWidth bItems
  let extraAsc := e.constAt size e.consts.radicalExtraAscender
  match glyphOf size e.font '\u221A' with
  | none =>
    let missing := if missing0.contains (e.idx, '\u221A') then missing0
      else missing0.push (e.idx, '\u221A')
    let raisedBody := raiseItems raise bItems
    let items := (#[(Item.rule bodyW θ (raise + ruleBot) e.color),
        mathKern e size (-bodyW)]
      ++ raisedBody)
      ++ struts e (raise + ruleTop + extraAsc) (raise + bBot)
    (items, missing)
  | some (g, _, _) =>
    -- Compare scaled ink heights: a variant's advance can exceed its outline.
    let ladder := (variantLadder e g).map fun (gid, _) =>
      let (top, bot) := e.glyphExtent size gid
      (gid, top - bot)
    let (gv, _) := (Math.pickVariant (ruleTop - min 0 bBot) ladder).getD (g, 0)
    let (vTop, vBot) := e.glyphExtent size gv
    let surdW := scaledAt size e.font (e.font.widths[gv]?.getD 0)
    let surdRaise := raise + ruleTop - vTop
    let raisedBody := raiseItems raise bItems
    let degPrefix :=
      if degItems.isEmpty then #[] else Id.run do
        let degRaise := surdRaise + vBot +
          (vTop - vBot) * e.consts.radicalDegreeBottomRaisePercent / 100
        let kernB := e.constAt size e.consts.radicalKernBeforeDegree
        let kernA := e.constAt size e.consts.radicalKernAfterDegree
        return (#[mathKern e size kernB] ++ raiseItems degRaise degItems).push
          (mathKern e size kernA)
    let items := (degPrefix.push
        (mathBox e e.idx surdW #[(gv, '\u221A', surdW)] size surdRaise)
      |>.push (Item.rule bodyW θ (raise + ruleBot) e.color)
      |>.push (mathKern e size (-bodyW)))
      ++ raisedBody
      ++ struts e (raise + ruleTop + extraAsc) (min (raise + bBot) (surdRaise + vBot))
    (items, missing0)

/-- Assemble a laid accent (TeXbook Appendix G rule 12 over
the MATH constants), its attachment point on the base's. -/
private def accentAssemble (e : MathEnv) (size raise : Sp) (mark : Char)
    (stretch : Bool) (bItems : Array Item) (missing0 : Array (Nat × Char)) :
    Array Item × Array (Nat × Char) := Id.run do
  let (bTop, bBot) := mathItemsExtent e.fs bItems
  let baseW := mathItemsWidth bItems
  let raisedBody := raiseItems raise bItems
  if mark == '\u0305' then
    let θ := e.constAt size e.consts.overbarRuleThickness
    let ψ := e.constAt size e.consts.overbarVerticalGap
    let extraAsc := e.constAt size e.consts.overbarExtraAscender
    let ruleBot := bTop + ψ
    let items := (raisedBody.push (mathKern e size (-baseW))).push
        (Item.rule baseW θ (raise + ruleBot) e.color)
      ++ struts e (raise + ruleBot + θ + extraAsc) (raise + bBot)
    return (items, missing0)
  match glyphOf size e.font mark with
  | none =>
    let missing := if missing0.contains (e.idx, mark) then missing0
      else missing0.push (e.idx, mark)
    return (raisedBody ++ struts e (raise + bTop) (raise + bBot), missing)
  | some (g, _, _) =>
    let baseTA :=
      match bItems.filter (fun it => match it with
        | .box _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
        | _ => false) with
      | #[.box _ fi _ _ #[(bg, _, _)] bsize _ _ _ _ _] =>
        if fi == e.idx then e.constAt bsize (e.font.topAccentX bg) else baseW / 2
      | _ => baseW / 2
    let gv :=
      if stretch then
        let ladder := (e.font.horizVariants g).toList
        let targetDu := baseW * (e.font.unitsPerEm : Int) / size
        ((Math.pickWidest targetDu (if ladder.isEmpty then [(g, 0)] else ladder)).getD
          (g, 0)).1
      else g
    let wAcc := scaledAt size e.font (e.font.widths[gv]?.getD 0)
    let shift := baseTA - e.constAt size (e.font.markAttachX gv)
    let accRaise := raise +
      max 0 (bTop - e.constAt size e.consts.accentBaseHeight)
    let (mTop, mBot) := e.glyphExtent size gv
    let items := ((raisedBody.push (mathKern e size (-baseW + shift))).push
        (mathBox e e.idx wAcc #[(gv, mark, wAcc)] size accRaise)
      |>.push (mathKern e size (baseW - shift - wAcc)))
      ++ struts e (max (raise + bTop) (accRaise + mTop))
        (min (raise + bBot) (accRaise + mBot))
    return (items, missing0)

/-- The one measured input to cancellation geometry in both backends. -/
private def cancelInput (e : MathEnv) (st : Math.MathStyle)
    (spec : Math.CancelSpec) (body value : Array Item) : Math.CancelIn :=
  let size := e.sizeAt st
  let (top, bot) := mathItemsExtent e.fs body
  let ink := (mathItemsInk e.fs value).getD {}
  let rule := e.constAt size e.consts.overbarRuleThickness
  { rule := if spec.thick then 2 * rule else rule
    gap := e.constAt size e.consts.overbarVerticalGap
    w := mathItemsWidth body, top, bot, vw := mathItemsWidth value
    vtop := ink.top, vbot := ink.bottom, vleft := ink.left, vright := ink.right
    space := e.constAt size e.consts.spaceAfterScript }

/-- Assemble a laid cancel mark, cancel.sty's four commands, by `Math.cancelGeom`. -/
private def cancelAssemble (e : MathEnv) (st : Math.MathStyle) (raise : Sp)
    (mark : Math.CancelMark) (spec : Math.CancelSpec) (ink : Ir.Color)
    (bItems vItems : Array Item) : Array Item :=
  let size := e.sizeAt st
  let input := cancelInput e st spec bItems vItems
  let w := input.w
  let vw := input.vw
  let g := Math.cancelGeom mark spec.room input
  let marks := g.polys.map fun pts => Item.poly (pts.map fun (x, y) => (x, y + raise)) ink
  let (mTop, mBot) := mathItemsExtent e.fs marks
  let raised := raiseItems raise bItems
  let body := #[mathKern e size g.shift] ++ raised
  -- Only measured target ink follows the arrow's ray; a glyphless kern is not raised.
  let vRaise := raise + if input.hasValueInk then g.valueY else 0
  let value := if vItems.isEmpty then #[] else
    let placed := raiseItems vRaise vItems
    #[mathKern e size (g.valueX - g.shift - w)] ++ placed
  let reached := if vItems.isEmpty then g.shift + w else g.valueX + vw
  let top := max mTop (max (raise + input.top) (if input.hasValueInk then vRaise + input.vtop else raise))
  let bot := min mBot (min (raise + input.bot) (if input.hasValueInk then vRaise + input.vbot else raise))
  let reach := struts e top bot
  let assembled := ((marks ++ body ++ value).push (mathKern e size (g.advance - reached))) ++ reach
  if !spec.room then assembled else
  -- Reserve both sides by translating the whole assembly, never its target alone.
  let bounds := (mathItemsInk e.fs assembled).getD {}
  let left := min bounds.left (min g.shift (g.shift + w))
  let right := max bounds.right (max g.shift (g.shift + w))
  let target := input.hasValueInk || vw != 0
  let left := if target then min left (min g.valueX (g.valueX + vw)) else left
  let right := if target then max right (max g.valueX (g.valueX + vw)) else right
  let (pad, width) := Math.inkRoom left right g.advance
  if pad == 0 && width == g.advance then assembled else
    #[mathKern e size pad] ++ assembled ++ #[mathKern e size (width - pad - g.advance)]

/-- A colour switch inside hidden content keeps the hidden paint. -/
private def keepHidden (cur c : Ir.Color) : Ir.Color :=
  if cur == hiddenPaint then cur else c

mutual

/-- Lay one math list, spacing directly adjacent atoms by their degraded classes. -/
private def layMathTail (e : MathEnv) (st : Math.MathStyle) (raise : Sp)
    (cls : List Math.MathClass) (prev : Option Math.MathClass) (acc : MAcc) :
    Math.MList → MAcc
  | .nil => acc
  | .cons (.ink c _) rest =>
    -- A colour switch is no atom, so the spacing walk keeps the atom before it.
    layMathTail { e with color := keepHidden e.color c } st raise cls prev acc rest
  | .cons x rest =>
    match x.classOf with
    | none =>
      let mu := match x with
        | .space m => m
        | _ => 0
      let size := e.sizeAt st
      let acc := ((acc.1.push (mathKern e size (muAt size mu))), acc.2)
      layMathTail e st raise cls none acc rest
    | some _ =>
      let (c, cs) := match cls with
        | c :: cs => (c, cs)
        | [] => (x.classOf.getD .ord, [])
      let size := e.sizeAt st
      let acc := match prev with
        | some p =>
          let mu := (Math.spacing p c st).mu
          if mu == 0 then acc
          else ((acc.1.push (mathKern e size (muAt size (mu : Int)))), acc.2)
        | none => acc
      let acc := layMathItem e st raise x acc
      layMathTail e st raise cs (some c) acc rest

/-- Lay one atom: its nucleus at the current style, then
its scripts, as limits for a display limit operator. -/
private def layMathItem (e : MathEnv) (st : Math.MathStyle) (raise : Sp)
    (x : Math.MItem) (acc : MAcc) : MAcc :=
  match x with
  | .space mu =>
    let size := e.sizeAt st
    ((acc.1.push (mathKern e size (muAt size mu))), acc.2)
  -- `layMathTail` reads a switch first; one met alone inks nothing.
  | .ink _ _ => acc
  | .atom cls nuc sup sub lim =>
    let size := e.sizeAt st
    let display := st.rank == 3
    let (nucItems, m0) :=
      match nuc, cls, display with
      | .sym c, .op, true =>
        match glyphOf size e.font c with
        | some (g, _, _) =>
          let (gv, _) := (Math.pickVariant e.consts.displayOperatorMinHeight
            (variantLadder e g)).getD (g, 0)
          let w := scaledAt size e.font (e.font.widths[gv]?.getD 0)
          let (vTop, vBot) := e.glyphExtent size gv
          let axis := e.constAt size e.consts.axisHeight
          let vRaise := raise + axis - (vTop + vBot) / 2
          (#[mathBox e e.idx w #[(gv, c, w)] size vRaise]
            ++ struts e (vRaise + vTop) (vRaise + vBot), acc.2)
        | none =>
          if acc.2.contains (e.idx, c) then (#[], acc.2)
          else (#[], acc.2.push (e.idx, c))
      | _, _, _ => layMathNucleus e st raise nuc (#[], acc.2)
    if lim && display && !(sup == .nil && sub == .nil) then
      let (supItems, m1) := layMathTail e st.sup 0
        (Math.degrade sup.classes) none (#[], m0) sup
      let (subItems, m2) := layMathTail e st.sub 0
        (Math.degrade sub.classes) none (#[], m1) sub
      let (opTop, opBot) := mathItemsExtent e.fs nucItems
      let (supTop, supBot) := mathItemsExtent e.fs supItems
      let (subTop, subBot) := mathItemsExtent e.fs subItems
      let opW := mathItemsWidth nucItems
      let supW := mathItemsWidth supItems
      let subW := mathItemsWidth subItems
      let w := max opW (max supW subW)
      let rise := max (opTop + e.constAt size e.consts.upperLimitBaselineRiseMin)
        (opTop + e.constAt size e.consts.upperLimitGapMin - supBot)
      let low := min (opBot - e.constAt size e.consts.lowerLimitBaselineDropMin)
        (opBot - e.constAt size e.consts.lowerLimitGapMin - subTop)
      let place (items : Array Item) (itemsW : Sp) (delta : Sp) : Array Item :=
        if items.isEmpty then #[] else
        let padK := Math.ColAlign.pad .center w itemsW
        let shifted := raiseItems delta items
        (#[mathKern e size padK] ++ shifted).push
          (mathKern e size (w - padK - itemsW)) |>.push (mathKern e size (-w))
      let placedNuc := place nucItems opW 0
      let placedSup := place supItems supW rise
      let placedSub := place subItems subW low
      let items := placedNuc ++ placedSup ++ placedSub
      let items := items.push (mathKern e size w)
      let items := items ++ struts e
        (if supItems.isEmpty then opTop else rise + supTop)
        (if subItems.isEmpty then opBot else low + subBot)
      (acc.1 ++ items, m2)
    else
    let acc := (acc.1 ++ nucItems, m0)
    let upShift := e.constAt size
      (if st.cramped then e.consts.superscriptShiftUpCramped
       else e.consts.superscriptShiftUp)
    let downShift := e.constAt size e.consts.subscriptShiftDown
    let (supItems, m1) := layMathTail e st.sup (raise + upShift)
      (Math.degrade sup.classes) none (#[], acc.2) sup
    let (subItems, m2) := layMathTail e st.sub (raise - downShift)
      (Math.degrade sub.classes) none (#[], m1) sub
    if supItems.isEmpty && subItems.isEmpty then
      (acc.1, m2)
    else
      let spaceAfter := e.constAt size e.consts.spaceAfterScript
      let supW := mathItemsWidth supItems
      let subW := mathItemsWidth subItems
      if supItems.isEmpty then
        ((acc.1 ++ subItems).push (mathKern e size spaceAfter), m2)
      else if subItems.isEmpty then
        ((acc.1 ++ supItems).push (mathKern e size spaceAfter), m2)
      else
        let items := (acc.1 ++ supItems).push (mathKern e size (-supW)) ++ subItems
        (items.push (mathKern e size (max supW subW - subW + spaceAfter)), m2)

private def layMathNucleus (e : MathEnv) (st : Math.MathStyle) (raise : Sp)
    (nuc : Math.MNucleus) (acc : MAcc) : MAcc :=
  match nuc with
  | .sym c =>
    let size := e.sizeAt st
    match glyphOf size e.font c with
    | some g =>
      (acc.1.push (mathBox e e.idx g.2.2 #[g] size raise), acc.2)
    | none =>
      match e.fs.fallbackFor c |>.bind fun fb =>
          (glyphOf size (e.fs.get fb) c).map (fb, ·) with
      | some (fb, g) =>
        (acc.1.push (mathBox e fb g.2.2 #[g] size raise), acc.2)
      | none =>
        -- An uncovered alphabet scalar sets its base letter (W0016), else goes missing (E0405).
        let synth : Option (Nat × (Nat × Char × Sp)) := do
          let (a, base) ← Math.MathAlphabet.unapply c
          let (bold, italic) := a.synthStyle
          let fi := if bold || italic then e.fs.lookup 0 (if bold then 700 else 400) italic else e.idx
          let g ← glyphOf size (e.fs.get fi) base
          return (fi, g)
        match synth with
        | some (fi, g) =>
          (acc.1.push (mathBox e fi g.2.2 #[g] size raise), acc.2)
        | none =>
          if acc.2.contains (e.idx, c) then acc
          else (acc.1, acc.2.push (e.idx, c))
  | .styled style c =>
    -- A text-sourced alphabet scalar sets its base letter in the projected text family.
    let size := e.textSizeAt st
    let fi := e.fs.lookup style.slot.toNat style.weight style.italic
    match glyphOf size (e.fs.get fi) c with
    | some g =>
      (acc.1.push (mathBox e fi g.2.2 #[g] size raise), acc.2)
    | none =>
      if acc.2.contains (fi, c) then acc
      else (acc.1, acc.2.push (fi, c))
  | .word s => Id.run do
    -- An upright word's boxes split only where the chain substitutes, as a box carries one face.
    let size := e.sizeAt st
    let mut items := acc.1
    let mut missing := acc.2
    let mut cur := e.idx
    let mut glyphs : Array (Nat × Char × Sp) := #[]
    let mut w : Sp := 0
    for c in s.toList do
      let hit := match glyphOf size e.font c with
        | some g => some (e.idx, g)
        | none => e.fs.fallbackFor c |>.bind fun fb =>
            (glyphOf size (e.fs.get fb) c).map (fb, ·)
      match hit with
      | some (fi, g) =>
        if fi != cur && !glyphs.isEmpty then
          items := items.push (mathBox e cur w glyphs size raise)
          glyphs := #[]
          w := 0
        cur := fi
        glyphs := glyphs.push g
        w := w + g.2.2
      | none =>
        unless missing.contains (e.idx, c) do
          missing := missing.push (e.idx, c)
    return (items.push (mathBox e cur w glyphs size raise), missing)
  | .list body =>
    layMathTail e st raise (Math.degrade body.classes) none acc body
  | .alpha _ _ body =>
    layMathTail e st raise (Math.degrade body.classes) none acc body
  | .frac spec num den =>
    -- `\genfrac`'s style sets the construct; delimiters grow to `\Umathfractiondelsize`.
    let fst := spec.style.getD st
    let size := e.sizeAt fst
    let display := fst.rank == 3
    let (numItems, m1) := layMathTail e fst.fracNum 0
      (Math.degrade num.classes) none (#[], acc.2) num
    let (denItems, m2) := layMathTail e fst.fracDen 0
      (Math.degrade den.classes) none (#[], m1) den
    if spec.left.isNone && spec.right.isNone then
      (acc.1 ++ fracAssemble e size display raise spec.rule true true numItems denItems, m2)
    else
      let bar := fracAssemble e size display 0 spec.rule spec.left.isNone spec.right.isNone
        numItems denItems
      let (items, missing) := delimAssembleTo e size raise spec.left spec.right
        (size * (if display then 240 else 101) / 100) false bar m2
      (acc.1 ++ items, missing)
  | .rad deg body =>
    let (bItems, m1) := layMathTail e st.cramp 0
      (Math.degrade body.classes) none (#[], acc.2) body
    let (degItems, m2) := layMathTail e (.scriptscript st.cramped) 0
      (Math.degrade deg.classes) none (#[], m1) deg
    let (items, missing) := radAssemble e (e.sizeAt st) (st.rank == 3) raise
      bItems degItems m2
    (acc.1 ++ items, missing)
  | .delim l r body =>
    let (bItems, m1) := layMathTail e st 0
      (Math.degrade body.classes) none (#[], acc.2) body
    let (items, missing) := delimAssemble e (e.sizeAt st) raise l r bItems m1
    (acc.1 ++ items, missing)
  | .big d step =>
    -- amsmath's `\bBigg@`, set at the text size in every style as lualatex sets it.
    let size := e.base
    let paren : Sp := match glyphOf size e.font '(' with
      | some (g, _, _) => let (t, b) := e.glyphExtent size g; t - b
      | none => size
    let axis := e.constAt size e.consts.axisHeight
    let half := Math.bigVcenter paren step / 2
    let (items, missing) := delimAssembleTo e size raise d none
      (Math.bigTarget paren size step) false (struts e (axis + half) (axis - half)) acc.2
    (acc.1 ++ items, missing)
  | .accent mark stretch body =>
    -- The base sets in the cramped current style (TeXbook Appendix G rule 12).
    let (bItems, m1) := layMathTail e st.cramp 0
      (Math.degrade body.classes) none (#[], acc.2) body
    let (items, missing) := accentAssemble e (e.sizeAt st) raise mark stretch
      bItems m1
    (acc.1 ++ items, missing)
  | .grid kind rows =>
    -- An `array` sets its cells in text style, amsmath's alignments in display style (amsmath.sty).
    let cellSt : Math.MathStyle := match kind with
      | .array _ _ => if st.rank > 2 then .text st.cramped else st
      | .small => .script false
      | .align | .aligned _ | .gather => .display false
    let (cells, missing) := layGridRows { e with gridDepth := e.gridDepth + 1 } cellSt (#[], acc.2) rows
    (acc.1 ++ gridAssemble e (e.sizeAt st) raise kind cells, missing)
  | .cancel mark spec value body =>
    -- cancel.sty boxes its argument in the current style (`\mathpalette`).
    let (bItems, m1) := layMathTail e st 0 (Math.degrade body.classes) none (#[], acc.2) body
    let ink := keepHidden e.color ((spec.color.map (·.1)).getD e.color)
    let (vItems, m2) := layMathTail { e with color := ink } (spec.size.style st) 0
      (Math.degrade value.classes) none (#[], m1) value
    (acc.1 ++ cancelAssemble e st raise mark spec ink bItems vItems, m2)

/-- The cells of one row, each laid into its own run. -/
private def layGridRow (e : MathEnv) (st : Math.MathStyle)
    (acc : Array (Array Item) × Array (Nat × Char)) :
    Math.MRow → Array (Array Item) × Array (Nat × Char)
  | .nil => acc
  | .cons cell rest =>
    let (items, m) := layMathTail e st 0
      (Math.degrade cell.classes) none (#[], acc.2) cell
    layGridRow e st (acc.1.push items, m) rest

private def layGridRows (e : MathEnv) (st : Math.MathStyle)
    (acc : Array (Array (Array Item)) × Array (Nat × Char)) :
    Math.MRows → Array (Array (Array Item)) × Array (Nat × Char)
  | .nil => acc
  | .cons row rest =>
    let (cells, m) := layGridRow e st (#[], acc.2) row
    layGridRows e st (acc.1.push cells, m) rest

end

/-- A formula's items: one unbreakable run of boxes and kerns, inline
math in text style and display math in display style (TeXbook ch. 17). -/
private def mathItems (e : MathEnv) (display : Bool) (body : Math.MList)
    (missing : Array (Nat × Char)) : Array Item × Array (Nat × Char) :=
  let st : Math.MathStyle := if display then .display false else .text false
  layMathTail e st 0 (Math.degrade body.classes) none (#[], missing) body

/-- The one pattern-selection site: an untagged run takes the main language's
table, a tagged run its own language's, and `main = none` turns hyphenation off. -/
public def patsOf (main : Option Hyphen.Patterns) (lang : Option String) :
    Option Hyphen.Patterns :=
  match lang with
  | none => main
  | some tag => if main.isNone then none else Hyphen.forTag tag

public theorem hyphenation_follows_language (main : Option Hyphen.Patterns)
    (tag : String) (h : main.isSome) :
    patsOf main (some tag) = Hyphen.forTag tag := by
  cases main with
  | none => simp at h
  | some _ => rfl

public theorem patsOf_off (lang : Option String) : patsOf none lang = none := by
  cases lang <;> rfl

/-- A footnote mark's box: its digits as one raised run at the
scriptsize step of `around`; digits the face lacks return beside it. -/
private def markBox (fs : FontSet) (sty : TextStyle) (around : Sp)
    (decorations : Decorations) (num : Nat) :
    Item × Array (Nat × Char) := Id.run do
  let attr : Attribution := .noteMark num
  let idx := fs.lookup sty.slot sty.weight.css sty.italic
  let font := fs.get idx
  let markSize := Ir.scaleStep around "scriptsize"
  let raise := around * Ir.markRaise / 1000
  let mut gs : Array (Nat × Char × Sp) := #[]
  let mut w : Sp := 0
  let mut miss : Array (Nat × Char) := #[]
  for c in (toString num).toList do
    match glyphOf markSize font c with
    | some g =>
      gs := gs.push g
      w := w + g.2.2
    | none => miss := miss.push (idx, c)
  return (.box w idx sty.paint sty.link gs markSize {} decorations raise sty.ground attr, miss)

/-- The token fold's state: what the walk has built and, in
`dropped`, `substs` and `unstyled`, what it lost or substituted. -/
private structure ItemsAcc where
  items : Array Item := #[]
  /-- Destinations indexed by the items their source position becomes. -/
  anchors : Array (String × Nat) := #[]
  /-- First source scalar carried by each located item. -/
  itemSources : Array (Nat × Span) := #[]
  /-- Each footnote met: its mark item's index, its number, its body and the body's first leaf. -/
  notes : Array (Nat × Nat × Array Inline × Option Nat) := #[]
  dropped : Array (Nat × Char) := #[]
  substs : Array (Nat × Char × Nat) := #[]
  unstyled : Array (Nat × Char × Math.MathAlphabet × Char) := #[]
  origins : GlyphOrigins := #[]
  extras : Std.HashMap Nat Sp := {}
  /-- Natural offsets of owner fragments within their original shaped boxes, keyed by item index. -/
  wordOffsets : Std.HashMap Nat Sp := {}
  cache : Std.HashMap String (Array Nat) := {}
  /-- The item count just after the last word's items: a space kerns
  against the glyph before it only while nothing has been set since. -/
  wordEnd : Nat := 0
  /-- The item count before the token being folded in,
  set by the caller so the fold writes in place. -/
  before : Nat := 0

/-- The pair kern a set glyph declares with its own face's space glyph (luaotfload's
space kerning), at the box's size; 0 for anything but a box of glyphs. -/
private def spaceKern (fs : FontSet) (after : Bool) : Option Item → Sp
  | some (.box _ fontIdx _ _ glyphs size _ _ _ _ _) =>
    match (if after then glyphs.back? else glyphs[0]?) with
    | some (g, _, _) => spacePairKern Ir.features size (fs.get fontIdx) after g
    | none => 0
  | _ => 0

/-- Whether an item is a box of glyphs: the character TeX's `\/` corrects. -/
private def glyphBox : Option Item → Bool
  | some (.box _ _ _ _ glyphs _ _ _ _ _ _) => !glyphs.isEmpty
  | _ => false

/-- The items with their final glue `w` wider: a space
taking the pair kern of the word that follows. -/
private def widenLast (items : Array Item) (w : Sp) : Array Item :=
  if w == 0 then items else
  match items.back? with
  | some (.glue g) => items.set! (items.size - 1) (.glue { g with width := g.width + w })
  | some (.decoratedGlue g r) =>
    items.set! (items.size - 1) (.decoratedGlue { g with width := g.width + w } r)
  | _ => items

/-- TeX's `\/` at the end of the items: a kern as wide as the last glyph's
italic correction, nothing when the items end in anything but a glyph. -/
private def italicKern (acc : ItemsAcc) : ItemsAcc :=
  if acc.wordEnd == acc.items.size && glyphBox acc.items.back? then { acc with wordEnd := 0 }
  else acc

/-- An italic correction under the style in force
(`Tk.corr`), made where ltfntcmd's `\maybe@ic` makes it. -/
private def correctItalic (fs : FontSet) (maybe : Bool) (sty : TextStyle)
    (acc : ItemsAcc) : ItemsAcc :=
  if !maybe then italicKern acc
  else if (fs.get (fs.lookup sty.slot sty.weight.css sty.italic)).italicAngle < 0 then acc
  else match acc.items.back? with
    | some (.glue g) =>
      let n := acc.items.size - 1
      if g.width == 0 || acc.wordEnd != n || !glyphBox acc.items[n - 1]? then acc
      else
        let bare : Item := .glue { g with width := g.width - spaceKern fs true acc.items[n - 1]? }
        { acc with items := acc.items.set! n bare, wordEnd := 0 }
    | some (.decoratedGlue g r) =>
      let n := acc.items.size - 1
      if g.width == 0 || acc.wordEnd != n || !glyphBox acc.items[n - 1]? then acc
      else
        let bare : Item := .decoratedGlue
          { g with width := g.width - spaceKern fs true acc.items[n - 1]? } r
        { acc with items := acc.items.set! n bare, wordEnd := 0 }
    | _ => italicKern acc

/-- Resolve the size and baseline skip in force at one token; `none`
uses the ordinary line-height rule, and `some 0` keeps a zero skip. -/
private def TextStyle.metricsIn (sty : TextStyle) (base xHeight : Sp)
    (values : MeasureValues) : Sp × Option Sp :=
  let basis := base * sty.scale / 1000
  let xBasis := xHeight * sty.scale / 1000
  let size := match sty.fontSize with
    | some e => max 1 (e.resolveWidth values basis xBasis)
    | none => basis
  let leading := sty.leading.map fun e => e.resolveWidth values basis xBasis
  (size, leading)

/-- Resolve a style's size and baseline skip against
the consuming paragraph's measure and text height. -/
private def TextStyle.metrics (sty : TextStyle) (base xHeight textW textH : Sp) :
    Sp × Option Sp :=
  sty.metricsIn base xHeight (MeasureValues.horizontal textW textH)

/-- Resolve one surrounding text style through the native run
resolver; an omitted local context keeps the page's text area. -/
private def MathEnv.forStyles (geom : Geom) (fs : FontSet)
    (styles : Array Ir.Style) (measures : Option MeasureValues) : Option MathEnv := do
  let (idx, font, consts) ← fs.mathFont?
  let sty := styles.foldl (applyStyle geom.scale) {}
  let xHeight := fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm
  let values := measures.getD (MeasureValues.horizontal geom.textWidth geom.textHeight)
  let (runSize, _) := sty.metricsIn geom.fontSize xHeight values
  let around := fs.get (fs.lookup sty.slot sty.weight.css sty.italic)
  pure (MathEnv.forRun fs idx font consts around runSize)

/-- A physical math length's current em, from the same font environment as native glyphs. -/
public def mathEm (geom : Geom) (fs : FontSet) (styles : Array Ir.Style)
    (st : Math.MathStyle) (measures : Option MeasureValues := none) : Option Int := do
  let e ← MathEnv.forStyles geom fs styles measures
  if e.sizeAt st ≤ 0 then none else some (e.sizeAt st)

/-- The em of native text-sourced math alphabets. -/
public def mathTextEm (geom : Geom) (fs : FontSet) (styles : Array Ir.Style)
    (st : Math.MathStyle) (measures : Option MeasureValues := none) : Option Int := do
  let e ← MathEnv.forStyles geom fs styles measures
  if e.textSizeAt st ≤ 0 then none else some (e.textSizeAt st)

/-- Font-measured cancellation for another backend, resolved through the same
text-style and math walks as native placement, style history outermost first. -/
public def cancelMetric (geom : Geom) (fs : FontSet) (styles : Array Ir.Style)
  (st : Math.MathStyle) (spec : Math.CancelSpec) (body value : Math.MList)
  (measures : Option MeasureValues := none) : Option Math.CancelMetric := do
  let e ← MathEnv.forStyles geom fs styles measures
  if e.sizeAt st ≤ 0 then none else
    let (bs, missing) := layMathTail e st 0
      (Math.degrade body.classes) none (#[], #[]) body
    let (vs, _) := layMathTail e (spec.size.style st) 0
      (Math.degrade value.classes) none (#[], missing) value
    let bounds := (mathItemsInk fs bs).getD {}
    some { em := e.sizeAt st, input := cancelInput e st spec bs vs
           bodyLeft := bounds.left, bodyRight := bounds.right }

public theorem cancelMetric_fontless_exact (geom : Geom) (fs : FontSet)
    (styles : Array Ir.Style) (st : Math.MathStyle) (spec : Math.CancelSpec)
    (body value : Math.MList) (h : fs.mathFont? = none)
    (measures : Option MeasureValues := none) :
    cancelMetric geom fs styles st spec body value measures = none := by
  simp [cancelMetric, MathEnv.forStyles, h]

public theorem cancelMetric_contract (geom : Geom) (fs : FontSet)
    (styles : Array Ir.Style) (st : Math.MathStyle) (spec : Math.CancelSpec)
    (body value : Math.MList) (metric : Math.CancelMetric)
    (measures : Option MeasureValues := none)
    (h : cancelMetric geom fs styles st spec body value measures = some metric) :
    0 < metric.em := by
  cases he : MathEnv.forStyles geom fs styles measures with
  | none => simp [cancelMetric, he] at h
  | some e =>
    simp only [cancelMetric, he, bind, Option.bind] at h
    split at h
    · contradiction
    · cases h
      exact Int.not_le.mp (by assumption)

/-- A font-boundary projection, not a rule about the IR's attachment geometry. -/
public theorem cancelMetric_em_agree (geom : Geom) (fs : FontSet)
    (styles : Array Ir.Style) (st : Math.MathStyle) (spec : Math.CancelSpec)
    (body value : Math.MList) (metric : Math.CancelMetric)
    (measures : Option MeasureValues := none)
    (h : cancelMetric geom fs styles st spec body value measures = some metric) :
    mathEm geom fs styles st measures = some metric.em := by
  cases he : MathEnv.forStyles geom fs styles measures with
  | none => simp [cancelMetric, he] at h
  | some e =>
    simp only [cancelMetric, he, bind, Option.bind] at h
    split at h
    · contradiction
    · cases h
      simp [mathEm, he, Int.not_le.mp (by assumption)]

public def lineThroughRaise (xHeight : Sp) : Sp := max 0 xHeight * 55 / 100

public theorem lineThroughRaise_exact (xHeight : Int) (h : 0 ≤ xHeight) :
    lineThroughRaise xHeight = xHeight * 55 / 100 := by
  unfold lineThroughRaise
  have hm : max 0 xHeight = xHeight := by omega
  rw [hm]

/-- Resolve a command-entry source against the selected face and local measure. -/
private def DecorationSource.rule (src : DecorationSource) (base xHeight textW textH : Sp)
    (fs : FontSet) : DecorationRule :=
  let basis := base * src.scale / 1000
  let xBasis := xHeight * src.scale / 1000
  let values := MeasureValues.horizontal textW textH
  let size := match src.fontSize with
    | some e => max 1 (e.resolveWidth values basis xBasis)
    | none => basis
  let font := fs.get (fs.lookup src.slot src.weight.css src.italic)
  let ex := scaledAt size font font.xHeight.toNat
  { color := src.color, thickness := lineThroughThickness,
    raise := lineThroughRaise ex }

/-- A mark's band at its command-entry face: descender to ascender, as a browser paints an inline
background. -/
private def DecorationSource.markRule (src : DecorationSource) (color : Ir.Color)
    (base xHeight textW textH : Sp) (fs : FontSet) : DecorationRule :=
  let basis := base * src.scale / 1000
  let xBasis := xHeight * src.scale / 1000
  let values := MeasureValues.horizontal textW textH
  let size := match src.fontSize with
    | some e => max 1 (e.resolveWidth values basis xBasis)
    | none => basis
  let font := fs.get (fs.lookup src.slot src.weight.css src.italic)
  let upem : Int := max 1 font.unitsPerEm
  { color, thickness := (font.ascent - font.descent) * size / upem,
    raise := font.descent * size / upem }

private def TextStyle.resolvedDecorations (sty : TextStyle)
    (base xHeight textW textH : Sp) (fs : FontSet) : Decorations :=
  { underline := sty.decorations.underline
    lineThrough := sty.decorations.lineThrough.map
      (·.rule base xHeight textW textH fs)
    highlight := sty.decorations.highlight.map fun (c, src) =>
      src.markRule c base xHeight textW textH fs }

/-- The per-face underline band for a glyph run or an
authored space, its bottom measured up from the baseline. -/
private def underlineRule (font : Font) (size : Sp) (color : Ir.Color) : DecorationRule :=
  let upem : Int := font.unitsPerEm
  let (pos, thick) := font.band
  let thickness := thick * size / upem
  { color, thickness, raise := pos * size / upem - thickness }

private def Decorations.resolve (d : Decorations) (font : Font) (size : Sp)
    (color : Ir.Color) : Decorations (Option DecorationRule) :=
  { underline := if d.underline then some (underlineRule font size color) else none
    lineThrough := d.lineThrough
    highlight := d.highlight }

private def Item.ofDecoratedGlue (g : Glue) (d : Decorations) (font : Font)
    (size : Sp) (color : Ir.Color) : Item :=
  if d.underline || d.lineThrough.isSome || d.highlight.isSome then
    .decoratedGlue g (d.resolve font size color)
  else .glue g

/-- One flatten token into the accumulator: its ink becomes
items, an entry in `dropped`, or a note body carried whole. -/
private def itemsOfTok (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (tk : Tk) (owners : Array Attribution)
    (anchors : Array (String × Nat)) (origins : Array (Option Span))
    (source : Option Span) : ItemsAcc :=
  match tk with
  | .origin _ => acc
  | .word sty chars attr =>
    let idx := fs.lookup sty.slot sty.weight.css sty.italic
    let font := fs.get idx
    -- Small caps: the face's own `smcp`+`c2sc` where it has them, uniform synthesis otherwise.
    let useGsub := sty.smallcaps && !font.smallCaps.isEmpty
    let (sty, chars) :=
      if sty.smallcaps && !useGsub then
        smallCapSynth (smallCapScaleFor font) sty chars
      else (sty, chars)
    let (sz, leading) := sty.metrics size xHeight textW textH
    let decorations := sty.resolvedDecorations size xHeight textW textH fs
    -- A typewriter run never hyphenates: LaTeX's typewriter `\hyphenchar` is −1 (t1cmtt.fd).
    let wordPats := if sty.slot == 2 then none else patsOf pats sty.lang
    let (ws, m, s, c', offsets, sources, sites) :=
      wordItems wordPats (sty.lang.getD "") sty.explicitBreak sz leading idx sty.paint
        sty.ground sty.link decorations useGsub attr fs font chars
        acc.dropped acc.substs acc.cache owners origins acc.origins
    -- Read first and written inside the one update, so the items array is written in place.
    let rk := match acc.items.back? with
      | some (.glue g) | some (.decoratedGlue g _) =>
        if g.word then spaceKern fs false ws[0]? else 0
      | _ => 0
    let n := acc.items.size
    let itemSources := sources.foldl (fun sites (src, item) =>
      match origins[src]?.getD none with
      | none => sites
      | some span =>
        if sites.back?.map (·.1) == some (n + item) then sites
        else sites.push (n + item, span)) acc.itemSources
    { acc with items := widenLast acc.items rk ++ ws, dropped := m, substs := s, cache := c'
               origins := sites, itemSources := itemSources
               wordOffsets := offsets.fold (fun os k v => os.insert (n + k) v) acc.wordOffsets
               anchors := acc.anchors ++ anchors.map (fun (name, k) =>
                 (name, n + ((sources.find? (fun (src, _) => k ≤ src)).map (·.2)).getD ws.size))
               wordEnd := if ws.isEmpty then acc.wordEnd else n + ws.size }
  | .anchor name => { acc with anchors := acc.anchors.push (name, acc.items.size) }
  | .icon sty c attr =>
    -- The styled face first, then the fallback chain; only total absence is a loss (E0405).
    let idx := fs.lookup sty.slot sty.weight.css sty.italic
    let (sz, leading) := sty.metrics size xHeight textW textH
    let decorations := sty.resolvedDecorations size xHeight textW textH fs
    let hit :=
      match glyphOf sz (fs.get idx) c with
      | some g => some (idx, g)
      | none =>
        fs.fallbackFor c |>.bind fun fb =>
          (glyphOf sz (fs.get fb) c).map (fb, ·)
    match hit with
    | some (fb, g) =>
      let box : Item := .box g.2.2 fb sty.paint sty.link #[g] sz {leading} decorations 0
        sty.ground attr
      { acc with items := acc.items.push box }
    | none =>
      if acc.dropped.contains (idx, c) then acc
      else { acc with dropped := acc.dropped.push (idx, c)
                      origins := rememberGlyph acc.origins .E0405 idx c source }
  | .note num sty body bodyLeaf =>
    let (around, _) := sty.metrics size xHeight textW textH
    let decorations := sty.resolvedDecorations size xHeight textW textH fs
    let (mk, miss) := markBox fs sty around decorations num
    let acc := miss.foldl (fun acc m =>
      if acc.dropped.contains m then acc
      else { acc with dropped := acc.dropped.push m
                      origins := rememberGlyph acc.origins .E0405 m.1 m.2 source }) acc
    let at_ := acc.items.size
    { acc with notes := acc.notes.push (at_, num, body, bodyLeaf)
               items := acc.items.push mk }
  | .formula display sty body attr =>
    -- `flatten` pushes a formula only when a math face with constants is present.
    match fs.mathFont? with
    | some (idx, font, consts) =>
      -- The math face sets at the size matching the text's x-height (fontspec's MatchLowercase).
      let around := fs.get (fs.lookup sty.slot sty.weight.css sty.italic)
      let (runSize, leading) := sty.metrics size xHeight textW textH
      let e := { MathEnv.forRun fs idx font consts around runSize with
        color := sty.paint
        link := sty.link
        decorations := sty.resolvedDecorations size xHeight textW textH fs
        leading := leading
        ground := sty.ground
        attr := attr }
      let (ms, m) := mathItems e display body acc.dropped
      let sites := m.foldl (fun sites (idx, c) =>
        if acc.dropped.contains (idx, c) then sites
        else rememberGlyph sites .E0405 idx c source) acc.origins
      let acc := { acc with origins := sites }
      -- Substitutions are named as text's (W0009), less scalars the assembly recorded missing.
      let acc := (Math.MList.mathScalarsList #[] body).foldl (fun acc c =>
        if (font.gid c).isNone && !m.contains (idx, c) then
          match fs.fallbackFor c with
          | some fb =>
            if ((fs.get fb).gid c).isSome && !acc.substs.contains (idx, c, fb) then
              { acc with substs := acc.substs.push (idx, c, fb)
                         origins := rememberGlyph acc.origins .W0009 idx c source }
            else acc
          | none =>
            match Math.MathAlphabet.unapply c with
            | some (a, base) =>
              if acc.unstyled.any (·.2.1 == c) then acc
              else { acc with unstyled := acc.unstyled.push (idx, c, a, base)
                              origins := rememberGlyph acc.origins .W0016 idx c source }
            | none => acc
        else acc) acc
      { acc with dropped := m, items := acc.items ++ ms }
    | none => acc
  | .space sty =>
    let idx := fs.lookup sty.slot sty.weight.css sty.italic
    let (sz, _) := sty.metrics size xHeight textW textH
    let decorations := sty.resolvedDecorations size xHeight textW textH fs
    let g := interword sz (fs.get idx)
    let after := if acc.wordEnd == acc.items.size then spaceKern fs true acc.items.back? else 0
    let g := { g with width := g.width + after }
    let item := Item.ofDecoratedGlue g decorations (fs.get idx) sz sty.paint
    { acc with items := acc.items.push item }
  | .fill =>
    -- Stretchable but not a legal breakpoint on its own.
    { acc with items := acc.items.push (.glue { fil := true }) }
  | .hskip sty e keep =>
    let values := MeasureValues.horizontal textW textH
    let g := e.eval values.find
    let (sz, _) := sty.metrics size xHeight textW textH
    let xh := xHeight * sz / max size 1
    let glue := g.resolve sz xh
    let items := if keep then
        (acc.items.push (.rule 0 0 0 Ir.Color.black)).push
          (.pen 0 10000 false 0 Ir.Color.black #[])
      else acc.items
    let decorations := sty.resolvedDecorations size xHeight textW textH fs
    let font := fs.get (fs.lookup sty.slot sty.weight.css sty.italic)
    let item := Item.ofDecoratedGlue glue decorations font sz sty.paint
    { acc with items := items.push item }
  | .rule sty width height raise =>
    let values := MeasureValues.horizontal textW textH
    let (fs, _) := sty.metrics size xHeight textW textH
    let xh := xHeight * fs / max size 1
    let w := width.resolveWidth values fs xh
    let h := height.resolveWidth values fs xh
    let r := raise.resolveWidth values fs xh
    let item : Item := .rule (max 0 w) (max 0 h) r sty.paint
    { acc with items := acc.items.push item }
  | .corr maybe sty => correctItalic fs maybe sty acc
  | .strut g =>
    let strut : Item := .rule 0 (max 0 (g.width.resolve size xHeight)) 0
      Ir.Color.black
    { acc with items := acc.items.push strut }
  | .img src spec ink =>
    -- An entry that failed to load keeps the requested size around a default square.
    let idx? := imgs.findRequest? (spec.request src)
    let (iW, iH) := match idx?.bind fun k => (imgs.get? k).bind (·.size?) with
      | some wh => wh
      | none => (Dim.inch 1, Dim.inch 1) -- the placeholder square, a stated default
    let (w, h) := Image.resolveSize spec.toSizeSpec iW iH textW textH
    -- A boundary picture with no declared size fits the measure; nothing else is resized.
    let (w, h) :=
      if src.startsWith Ir.picSrcPrefix && spec.width.isNone &&
          spec.height.isNone && w > textW && w > 0 then
        (textW, textW * h / w)
      else (w, h)
    { acc with items := acc.items.push (.img idx? (max 0 w) (max 0 h) ink) }
  | .brk extra =>
    let items := acc.items.push (.glue { fil := true, parfill := true })
    let extras :=
      let sp := extra.width.resolve size xHeight
      if sp != 0 then acc.extras.insert items.size sp else acc.extras
    { acc with items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
               extras := extras }

/-- Adjacent word tokens of one complete style shape and hyphenate
as one input; spaces and other tokens flush the word. -/
private def itemsOfToks (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (toks : Array Tk) : ItemsAcc := Id.run do
  let step (acc : ItemsAcc) (tk : Tk) (owners : Array Attribution)
      (anchors : Array (String × Nat)) (origins : Array (Option Span))
      (source : Option Span) : ItemsAcc :=
    let next := itemsOfTok pats size xHeight fs imgs textW textH
      { acc with before := acc.items.size } tk owners anchors origins source
    match source with
    | none => next
    | some span =>
      let sites := (Array.range (next.items.size - next.before)).map
        (fun i => (next.before + i, span))
      { next with itemSources := next.itemSources ++ sites }
  let mut acc := acc
  let mut pending : Option (TextStyle × Array Char × Attribution) := none
  let mut owners : Array Attribution := #[]
  let mut origins : Array (Option Span) := #[]
  let mut scope : List Span := []
  let mut anchors : Array (String × Nat) := #[]
  for tk in toks do
    match tk with
    | .origin source =>
      scope := match source with
        | some source => source :: scope
        | none => scope.tail
    | .anchor name =>
      match pending with
      | some (_, word, _) => anchors := anchors.push (name, word.size)
      | none => acc := step acc tk #[] #[] #[] scope.head?
    | .word sty chars attr =>
      match pending with
      | some (prev, word, first) =>
        if sty == prev then
          pending := some (prev, word ++ chars, first)
          owners := chars.foldl (fun os _ => os.push attr) owners
          origins := chars.foldl (fun os _ => os.push scope.head?) origins
        else
          acc := step acc (.word prev word first) owners anchors origins none
          pending := some (sty, chars, attr)
          owners := chars.map (fun _ => attr)
          origins := chars.map (fun _ => scope.head?)
          anchors := #[]
      | none =>
        pending := some (sty, chars, attr)
        owners := chars.map (fun _ => attr)
        origins := chars.map (fun _ => scope.head?)
    | _ =>
      if let some (sty, word, attr) := pending then
        acc := step acc (.word sty word attr) owners anchors origins none
      pending := none
      owners := #[]
      origins := #[]
      anchors := #[]
      acc := step acc tk #[] #[] #[] scope.head?
  if let some (sty, word, attr) := pending then
    acc := step acc (.word sty word attr) owners anchors origins none
  return acc

/-- Inlines to breakable items, with every loss the fold ledgered rendered as
its diagnostic and the extra space each forced break asks for (`\\[1ex]`). -/
private def itemsOfInlines (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (Array Nat)) (ctr : LeafCtr) (imgs : Image.Store := {})
    (textW : Sp := 0) (textH : Sp := 0) (noteOk : Bool := false)
    (ladder : List (String × Nat) := Ir.sizeScale) (step : Nat := 1)
    (roleMetrics : List (String × (Sp × Option Sp)) := []) (steps : Nat := 0) :
    Array Item × Array Diag × Std.HashMap String (Array Nat) ×
      Std.HashMap Nat Sp × Array (Nat × Nat × Array Inline × Option Nat) ×
      Std.HashMap Nat Sp × Array (String × Nat) × Array (Nat × Span) := Id.run do
  let st := flatten (fs.mathFont?.isSome) noteOk
    { ladder := ladder, roleMetrics := roleMetrics, ctr := ctr, step := step, steps := steps }
    baseStyle xs
  let acc := itemsOfToks pats size xHeight fs imgs textW textH { cache := cache } st.toks
  let mut items := acc.items
  -- A paragraph ending in a forced break takes no second one, or the breaker sets no lines.
  let endsInBreak := match items.back? with
    | some (.pen _ cost _ _ _ _) => cost ≤ forcedCost
    | _ => false
  if !endsInBreak then
    items := items.push (.glue { fil := true, parfill := true })
    items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
  let mut diags := st.diags
  -- Native shaping describes PDF ink; HTML and Markdown keep Unicode.
  for (idx, c) in acc.dropped do
    let source := glyphOrigin acc.origins .E0405 idx c
    diags := diags.push (Diag.of .E0405
      s!"'{(fs.get idx).family}' has no glyph for U+{Hex.scalar c.toNat}"
      (span := source) (output := some .pdf)
      (trigger := (source.bind (·.pos.command)).getD (String.singleton c))
      (recovery := some .skipped)
      (help := "declare a face that covers it in \\fonts, or accept the loss \
with \\allow{E0405}"))
  for (idx, c, fb) in acc.substs do
    let source := glyphOrigin acc.origins .W0009 idx c
    -- One loss per face and scalar, counted at every site it recurs.
    diags := diags.push (Diag.of .W0009
      s!"'{(fs.get idx).family}' has no glyph for U+{Hex.scalar c.toNat}"
      (span := source) (output := some .pdf)
      (trigger := (source.bind (·.pos.command)).getD (String.singleton c))
      (recovery := some (.replacedBy s!"a glyph from '{(fs.get fb).family}'"))
      (subject := some s!"glyph:{(fs.get idx).family}:U+{Hex.scalar c.toNat}"))
  for (idx, c, a, base) in acc.unstyled do
    let source := glyphOrigin acc.origins .W0016 idx c
    diags := diags.push (Diag.of .W0016
      s!"'{(fs.get idx).family}' has no {a.styleLabel} glyph for U+{Hex.scalar c.toNat}"
      (span := source) (output := some .pdf)
      (trigger := (source.bind (·.pos.command)).getD (String.singleton c))
      (recovery := some (.replacedBy s!"the base letter '{base}'"))
      (help := some "declare a math face that carries this alphabet: \\fonts{ math = ... }")
      (subject := some ("math-alpha:" ++ a.name)))
  return (items, diags, acc.cache, acc.extras, acc.notes, acc.wordOffsets,
    acc.anchors, acc.itemSources)

private def PlainInlines (xs : Array Inline) : Prop :=
  ∀ x ∈ xs, ∃ s, x = .text s

private def Tk.Plain : Tk → Prop
  | .word _ _ _ | .space _ => True
  | _ => False

private theorem pushWord_plain (st : FlattenSt) (sty : TextStyle) (cur : Array Char)
    (attr : Attribution) (h : ∀ tk ∈ st.toks, tk.Plain) :
    ∀ tk ∈ (pushWord st sty cur attr).toks, tk.Plain := by
  intro tk ht
  simp only [pushWord, Array.mem_push] at ht
  rcases ht with ht | rfl
  · exact h tk ht
  · trivial

private theorem pushChars_plain (sty : TextStyle) (attr : Attribution)
    (cs : List Char) : ∀ (st : FlattenSt) (cur : Array Char),
    (∀ tk ∈ st.toks, tk.Plain) →
      ∀ tk ∈ (pushChars sty attr st cur cs).toks, tk.Plain := by
  induction cs with
  | nil =>
    intro st cur h
    simp only [pushChars]
    split
    · exact h
    · exact pushWord_plain st sty cur attr h
  | cons c rest ih =>
    intro st cur h
    simp only [pushChars]
    split
    · apply ih
      intro tk ht
      simp only [Array.mem_push] at ht
      rcases ht with ht | rfl
      · split at ht
        · exact h tk ht
        · exact pushWord_plain st sty cur attr h tk ht
      · trivial
    · exact ih st (cur.push c) h

private theorem pushText_plain (st : FlattenSt) (sty : TextStyle) (s : String)
    (h : ∀ tk ∈ st.toks, tk.Plain) :
    ∀ tk ∈ (pushText st sty s).toks, tk.Plain :=
  pushChars_plain sty st.ctr.take.1 s.toList _ #[] h

private theorem flattenList_plain (mathOk noteOk : Bool) (sty : TextStyle)
    (xs : List Inline) : ∀ st,
    (∀ x ∈ xs, ∃ s, x = .text s) → (∀ tk ∈ st.toks, tk.Plain) →
    ∀ tk ∈ (flattenList mathOk noteOk st sty xs).toks, tk.Plain := by
  induction xs with
  | nil => intro st _ h; exact h
  | cons x xs ih =>
    intro st hp ht
    obtain ⟨s, rfl⟩ := hp x (by simp)
    exact ih _ (fun x hx => hp x (by simp [hx])) (pushText_plain st sty s ht)

private theorem flatten_plain (mathOk noteOk : Bool) (st : FlattenSt)
    (sty : TextStyle) (xs : Array Inline) (hp : PlainInlines xs)
    (ht : ∀ tk ∈ st.toks, tk.Plain) :
    ∀ tk ∈ (flatten mathOk noteOk st sty xs).toks, tk.Plain := by
  rw [flatten]
  exact flattenList_plain mathOk noteOk sty xs.toList st
    (fun x hx => hp x (by simpa using hx)) ht

private def Tk.sourceChars : Tk → List Char
  | .word _ cs _ => cs.toList
  | .space _ => [' ']
  | .origin _ | .anchor _ | .fill | .hskip _ _ _ | .rule _ _ _ _
    | .strut _ | .brk _ | .img _ _ _ | .formula _ _ _ _
    | .icon _ _ _ | .note _ _ _ _ | .corr _ _ => []

private theorem pushWord_sourceChars (st : FlattenSt) (sty : TextStyle)
    (cur : Array Char) (attr : Attribution) :
    (pushWord st sty cur attr).toks.toList.flatMap Tk.sourceChars =
      st.toks.toList.flatMap Tk.sourceChars ++ cur.toList := by
  simp [pushWord, Tk.sourceChars]

private theorem pushChars_sourceChars (sty : TextStyle) (attr : Attribution)
    (cs : List Char) : ∀ (st : FlattenSt) (cur : Array Char),
    (pushChars sty attr st cur cs).toks.toList.flatMap Tk.sourceChars =
      st.toks.toList.flatMap Tk.sourceChars ++ cur.toList ++ cs := by
  induction cs with
  | nil =>
    intro st cur
    simp only [pushChars]
    split
    · rename_i h
      have hc : cur = #[] := Array.isEmpty_iff.mp h
      simp [hc]
    · simp [pushWord_sourceChars]
  | cons c rest ih =>
    intro st cur
    simp only [pushChars]
    split
    · rename_i h
      have hc : c = ' ' := beq_iff_eq.mp h
      subst c
      rw [ih]
      simp only [List.append_nil, Array.toList_push,
        List.flatMap_append, List.flatMap_cons, Tk.sourceChars, List.flatMap_nil,
        List.append_nil]
      split
      · rename_i h
        have hc : cur = #[] := Array.isEmpty_iff.mp h
        simp [hc, List.append_assoc]
      · simp [pushWord_sourceChars, List.append_assoc]
    · rw [ih]
      simp [List.append_assoc]

private theorem pushText_sourceChars (st : FlattenSt) (sty : TextStyle)
    (s : String) :
    (pushText st sty s).toks.toList.flatMap Tk.sourceChars =
      st.toks.toList.flatMap Tk.sourceChars ++ s.toList := by
  simpa [pushText, pushTextAttr] using
    pushChars_sourceChars sty st.ctr.take.1 s.toList { st with ctr := st.ctr.take.2 } #[]

private theorem flattenList_sourceChars (mathOk noteOk : Bool) (sty : TextStyle)
    (xs : List Inline) : ∀ st,
    (∀ x ∈ xs, ∃ s, x = .text s) →
    (flattenList mathOk noteOk st sty xs).toks.toList.flatMap Tk.sourceChars =
      st.toks.toList.flatMap Tk.sourceChars ++ (Ir.plainTextList xs).toList := by
  induction xs with
  | nil => intro st _; simp [flattenList, Ir.plainTextList]
  | cons x xs ih =>
    intro st hp
    obtain ⟨s, rfl⟩ := hp x (by simp)
    simp only [flattenList, flattenOne]
    rw [ih _ (fun x hx => hp x (by simp [hx])), pushText_sourceChars]
    simp [Ir.plainTextList, Ir.plainTextOne, List.append_assoc]

private theorem flatten_sourceChars (mathOk noteOk : Bool) (st : FlattenSt)
    (sty : TextStyle) (xs : Array Inline) (hp : PlainInlines xs) :
    (flatten mathOk noteOk st sty xs).toks.toList.flatMap Tk.sourceChars =
      st.toks.toList.flatMap Tk.sourceChars ++ (Ir.plainText xs).toList := by
  simpa only [flatten, Ir.plainText] using
    flattenList_sourceChars mathOk noteOk sty xs.toList st
      (fun x hx => hp x (by simpa using hx))

private theorem itemsOfTok_plainNotes (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (tk : Tk) (owners : Array Attribution)
    (anchors : Array (String × Nat)) (origins : Array (Option Span))
    (source : Option Span) (h : tk.Plain) :
    (itemsOfTok pats size xHeight fs imgs textW textH acc tk owners anchors origins source).notes =
      acc.notes := by
  cases tk <;> simp only [Tk.Plain] at h
  all_goals first | contradiction | rfl

private theorem itemsOfToks_plainNotes (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (toks : Array Tk) (h : ∀ tk ∈ toks, tk.Plain) :
    (itemsOfToks pats size xHeight fs imgs textW textH acc toks).notes = acc.notes := by
  unfold itemsOfToks
  dsimp only
  apply Loop.bind_of_inv
    (P := fun st : ItemsAcc × Option (TextStyle × Array Char × Attribution) ×
        Array Attribution × Array (Option Span) × List Span × Array (String × Nat) =>
      st.1.notes = acc.notes)
    (Q := fun out : ItemsAcc => out.notes = acc.notes)
  · apply Loop.forIn_array_inv
      (P := fun st : ItemsAcc × Option (TextStyle × Array Char × Attribution) ×
          Array Attribution × Array (Option Span) × List Span × Array (String × Nat) =>
        st.1.notes = acc.notes)
    · rfl
    · intro tk htk st hst
      have hp := h tk htk
      rcases st with ⟨a, pending, owners, origins, scope, anchors⟩
      cases tk <;> simp only [Tk.Plain] at hp
      all_goals first | contradiction | skip
      case word sty chars attr =>
        cases pending with
        | none => exact hst
        | some prev =>
          rcases prev with ⟨prev, word, first⟩
          dsimp only
          split
          · exact hst
          · exact hst
      case space sty =>
        cases pending with
        | none =>
          cases scope.head? <;> exact hst
        | some prev =>
          rcases prev with ⟨prev, word, first⟩
          cases scope.head? <;> exact hst
  · rintro ⟨a, pending, owners, origins, scope, anchors⟩ hst
    cases pending with
    | none => exact hst
    | some prev => rcases prev with ⟨sty, word, attr⟩; exact hst

private theorem itemsOfInlines_plainNotes (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (Array Nat)) (ctr : LeafCtr) (imgs : Image.Store)
    (textW textH : Sp) (noteOk : Bool) (ladder : List (String × Nat)) (step : Nat)
    (roleMetrics : List (String × (Sp × Option Sp))) (steps : Nat) (hp : PlainInlines xs) :
    (itemsOfInlines pats size xHeight fs baseStyle xs cache ctr imgs textW textH
      noteOk ladder step roleMetrics steps).2.2.2.2.1 = #[] := by
  have ht := flatten_plain fs.mathFont?.isSome noteOk
    { ladder := ladder, roleMetrics := roleMetrics, ctr := ctr, step := step,
      steps := steps }
    baseStyle xs hp (by simp)
  have hn := itemsOfToks_plainNotes pats size xHeight fs imgs textW textH
    { cache := cache } _ ht
  simp only [itemsOfInlines]
  repeat first | exact hn | split

private theorem widenLast_boxChars (items : Array Item) (w : Sp) :
    (widenLast items w).toList.flatMap Item.boxChars =
      items.toList.flatMap Item.boxChars := by
  unfold widenLast
  split
  · rfl
  · split
    next g h =>
      obtain ⟨xs, rfl⟩ := Array.back?_eq_some_iff.mp h
      simp [Item.boxChars]
    next g r h =>
      obtain ⟨xs, rfl⟩ := Array.back?_eq_some_iff.mp h
      simp [Item.boxChars]
    next => rfl

private def Tk.TextSource : Tk → Prop
  | .word sty _ _ => sty.smallcaps = false
  | .space _ => True
  | _ => False

private def Tk.itemChars : Tk → List Char
  | .word _ cs _ => cs.toList.flatMap wordItemChars
  | _ => []

private def ItemsAcc.Clean (a : ItemsAcc) : Prop :=
  a.dropped = #[] ∧ a.substs = #[]

private def ItemsAcc.chars (a : ItemsAcc) : List Char :=
  a.items.toList.flatMap Item.boxChars

private theorem decoratedGlue_boxChars (g : Glue) (d : Decorations)
    (font : Font) (size : Sp) (color : Ir.Color) :
    (Item.ofDecoratedGlue g d font size color).boxChars = [] := by
  unfold Item.ofDecoratedGlue
  split <;> rfl

private theorem itemsOfTok_none_chars (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (tk : Tk) (owners : Array Attribution)
    (anchors : Array (String × Nat)) (origins : Array (Option Span))
    (source : Option Span) (ht : tk.TextSource) :
    let out := itemsOfTok none size xHeight fs imgs textW textH
      acc tk owners anchors origins source
    out.Clean → acc.Clean ∧ out.chars = acc.chars ++ tk.itemChars := by
  cases tk <;> simp only [Tk.TextSource] at ht
  all_goals first | contradiction | skip
  case word sty cs attr =>
    simp only [itemsOfTok, ht, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      patsOf_off, ite_self, ItemsAcc.Clean, ItemsAcc.chars, Tk.itemChars]
    intro hc
    have hw := wordItems_none_chars (sty.lang.getD "") sty.explicitBreak
      (sty.metrics size xHeight textW textH).1
      (sty.metrics size xHeight textW textH).2
      (fs.lookup sty.slot sty.weight.css sty.italic) sty.paint sty.ground sty.link
      (sty.resolvedDecorations size xHeight textW textH fs) false attr fs
      (fs.get (fs.lookup sty.slot sty.weight.css sty.italic)) cs
      acc.dropped acc.substs acc.cache owners origins acc.origins hc.1 hc.2
    refine ⟨⟨hw.1, hw.2.1⟩, ?_⟩
    simp only [Array.toList_append, List.flatMap_append, widenLast_boxChars, hw.2.2]
  case space sty =>
    dsimp only
    intro hc
    refine ⟨hc, ?_⟩
    simp [itemsOfTok, ItemsAcc.chars, Tk.itemChars, decoratedGlue_boxChars]

private theorem cleanLoop_inv_census {α β γ : Type} (Inv Clean : β → Prop)
    (read : β → List γ) (emit : α → List γ) (f : α → β → Id (ForInStep β)) :
    ∀ (xs : List α) (init : β), Inv init →
      (∀ x ∈ xs, ∀ st, Inv st → ∃ next, f x st = .yield next ∧ Inv next ∧
        (Clean next → Clean st ∧ read next = read st ++ emit x)) →
      Inv (forIn xs init f : Id β).run ∧
      (Clean (forIn xs init f : Id β).run →
        Clean init ∧ read (forIn xs init f : Id β).run = read init ++ xs.flatMap emit) := by
  intro xs
  induction xs with
  | nil =>
    intro init hi _
    exact ⟨hi, fun hc => ⟨hc, by simp⟩⟩
  | cons x xs ih =>
    intro init hi hs
    obtain ⟨next, hf, hn, hnext⟩ := hs x (by simp) init hi
    rw [List.forIn_cons, hf]
    have ⟨hinv, hrest⟩ := ih next hn (fun y hy => hs y (by simp [hy]))
    refine ⟨hinv, ?_⟩
    intro hc
    have ⟨hnc, hnr⟩ := hrest hc
    have ⟨hic, hir⟩ := hnext hnc
    refine ⟨hic, ?_⟩
    change read (forIn xs next f : Id β).run = _
    rw [hnr, hir]
    simp [List.append_assoc]

private theorem cleanLoop_array_inv_census {α β γ : Type} (Inv Clean : β → Prop)
    (read : β → List γ) (emit : α → List γ) (f : α → β → Id (ForInStep β))
    (xs : Array α) (init : β) (hi : Inv init)
    (step : ∀ x ∈ xs, ∀ st, Inv st → ∃ next, f x st = .yield next ∧ Inv next ∧
      (Clean next → Clean st ∧ read next = read st ++ emit x)) :
    Inv (forIn xs init f : Id β).run ∧
    (Clean (forIn xs init f : Id β).run →
      Clean init ∧ read (forIn xs init f : Id β).run = read init ++ xs.toList.flatMap emit) := by
  rw [← Array.forIn_toList]
  exact cleanLoop_inv_census Inv Clean read emit f xs.toList init hi
    (fun x hx => step x (by simpa using hx))

private def pendingTextSource : Option (TextStyle × Array Char × Attribution) → Prop
  | none => True
  | some (sty, _, _) => sty.smallcaps = false

private def pendingItemChars : Option (TextStyle × Array Char × Attribution) → List Char
  | none => []
  | some (_, chars, _) => chars.toList.flatMap wordItemChars

private abbrev TokenState :=
  ItemsAcc × Option (TextStyle × Array Char × Attribution) ×
    Array Attribution × Array (Option Span) × List Span × Array (String × Nat)

private theorem tokenLoop_census (toks : Array Tk) (acc : ItemsAcc)
    (f : Tk → TokenState → Id (ForInStep TokenState))
    (step : ∀ tk ∈ toks, ∀ st, pendingTextSource st.2.1 →
      ∃ next, f tk st = .yield next ∧ pendingTextSource next.2.1 ∧
        (next.1.Clean → st.1.Clean ∧
          next.1.chars ++ pendingItemChars next.2.1 =
            (st.1.chars ++ pendingItemChars st.2.1) ++ tk.itemChars)) :
    let out := (forIn toks (acc, none, #[], #[], [], #[]) f : Id TokenState).run
    pendingTextSource out.2.1 ∧
      (out.1.Clean → acc.Clean ∧
        out.1.chars ++ pendingItemChars out.2.1 =
          acc.chars ++ toks.toList.flatMap Tk.itemChars) := by
  simpa only [pendingItemChars, List.append_nil] using
    cleanLoop_array_inv_census
      (Inv := fun st : TokenState => pendingTextSource st.2.1)
      (Clean := fun st : TokenState => st.1.Clean)
      (read := fun st : TokenState => st.1.chars ++ pendingItemChars st.2.1)
      (emit := Tk.itemChars) f toks (acc, none, #[], #[], [], #[]) trivial step

private theorem itemsOfTok_none_chars_before (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (n : Nat) (tk : Tk) (owners : Array Attribution)
    (anchors : Array (String × Nat)) (origins : Array (Option Span))
    (source : Option Span) (ht : tk.TextSource) :
    let out := itemsOfTok none size xHeight fs imgs textW textH
      { acc with before := n } tk owners anchors origins source
    out.Clean → acc.Clean ∧ out.chars = acc.chars ++ tk.itemChars :=
  itemsOfTok_none_chars size xHeight fs imgs textW textH { acc with before := n } tk owners
    anchors origins source ht

private theorem itemsOfToks_none_chars (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (toks : Array Tk) (ht : ∀ tk ∈ toks, tk.TextSource) :
    let out := itemsOfToks none size xHeight fs imgs textW textH acc toks
    out.Clean → acc.Clean ∧
      out.chars = acc.chars ++ toks.toList.flatMap Tk.itemChars := by
  unfold itemsOfToks
  dsimp only
  apply Loop.bind_of_inv
    (P := fun st : TokenState =>
      pendingTextSource st.2.1 ∧
      (st.1.Clean → acc.Clean ∧
        st.1.chars ++ pendingItemChars st.2.1 =
          acc.chars ++ toks.toList.flatMap Tk.itemChars))
    (Q := fun out : ItemsAcc =>
      out.Clean → acc.Clean ∧
        out.chars = acc.chars ++ toks.toList.flatMap Tk.itemChars)
  · apply tokenLoop_census
    · intro tk htk state hp
      have htk' := ht tk htk
      rcases state with ⟨a, pending, owners, origins, scope, anchors⟩
      cases tk <;> simp only [Tk.TextSource] at htk'
      all_goals first | contradiction | skip
      case word sty chars attr =>
        cases pending with
        | none =>
          refine ⟨_, rfl, htk', ?_⟩
          intro hc
          exact ⟨hc, by simp [pendingItemChars, Tk.itemChars]⟩
        | some prev =>
          rcases prev with ⟨prev, word, first⟩
          dsimp only
          split
          · refine ⟨_, rfl, hp, ?_⟩
            intro hc
            exact ⟨hc, by simp [pendingItemChars, Tk.itemChars, List.append_assoc]⟩
          · refine ⟨_, rfl, htk', ?_⟩
            intro hc
            have hw := itemsOfTok_none_chars_before size xHeight fs imgs textW textH a
              a.items.size (.word prev word first) owners anchors origins none hp hc
            exact ⟨hw.1, by simp [pendingItemChars, Tk.itemChars, hw.2,
              List.append_assoc]⟩
      case space sty =>
        cases pending with
        | none =>
          cases hs : scope.head?
          all_goals
            refine ⟨_, rfl, trivial, ?_⟩
            intro hc
            have hw := itemsOfTok_none_chars_before size xHeight fs imgs textW textH a
              a.items.size (.space sty) #[] #[] #[] scope.head? trivial hc
            exact ⟨hw.1, by simpa [pendingItemChars, hs, ItemsAcc.chars] using hw.2⟩
        | some prev =>
          rcases prev with ⟨prev, word, first⟩
          cases hs : scope.head?
          all_goals
            refine ⟨_, rfl, trivial, ?_⟩
            intro hc
            have hw := itemsOfTok_none_chars_before size xHeight fs imgs textW textH
              (itemsOfTok none size xHeight fs imgs textW textH { a with before := a.items.size }
                (.word prev word first) owners anchors origins none)
              (itemsOfTok none size xHeight fs imgs textW textH { a with before := a.items.size }
                (.word prev word first) owners anchors origins none).items.size
              (.space sty) #[] #[] #[] scope.head? trivial hc
            have hpw := itemsOfTok_none_chars_before size xHeight fs imgs textW textH a
              a.items.size (.word prev word first) owners anchors origins none hp hw.1
            have heq := hw.2
            rw [hpw.2] at heq
            exact ⟨hpw.1, by simpa [pendingItemChars, Tk.itemChars, hs,
              ItemsAcc.chars, List.append_assoc] using heq⟩
  · rintro ⟨a, pending, owners, origins, scope, anchors⟩ ⟨hp, hc⟩
    cases pending with
    | none => simpa [pendingItemChars] using hc
    | some prev =>
      rcases prev with ⟨sty, word, attr⟩
      intro hout
      have hw := itemsOfTok_none_chars_before size xHeight fs imgs textW textH a
        a.items.size (.word sty word attr) owners anchors origins none hp hout
      obtain ⟨hacc, heq⟩ := hc hw.1
      exact ⟨hacc, hw.2.trans heq⟩


/-- Scalars represented by glyph ink, as opposed to fixed or word spacing. -/
public def inkScalar (c : Char) : Bool :=
  !(c.isWhitespace || (fixedSpace c).isSome || c == '\u00a0' || c == '\u00ad')

public def inkCensus (cs : List Char) : List Char := cs.filter inkScalar

private theorem pushWord_textSource (st : FlattenSt) (sty : TextStyle) (cur : Array Char)
    (attr : Attribution) (hs : sty.smallcaps = false) (h : ∀ tk ∈ st.toks, tk.TextSource) :
    ∀ tk ∈ (pushWord st sty cur attr).toks, tk.TextSource := by
  intro tk ht
  simp only [pushWord, Array.mem_push] at ht
  rcases ht with ht | rfl
  · exact h tk ht
  · exact hs

private theorem pushChars_textSource (sty : TextStyle) (attr : Attribution)
    (cs : List Char) (hs : sty.smallcaps = false) : ∀ (st : FlattenSt) (cur : Array Char),
    (∀ tk ∈ st.toks, tk.TextSource) →
      ∀ tk ∈ (pushChars sty attr st cur cs).toks, tk.TextSource := by
  induction cs with
  | nil =>
    intro st cur h
    simp only [pushChars]
    split
    · exact h
    · exact pushWord_textSource st sty cur attr hs h
  | cons c rest ih =>
    intro st cur h
    simp only [pushChars]
    split
    · apply ih
      intro tk ht
      simp only [Array.mem_push] at ht
      rcases ht with ht | rfl
      · split at ht
        · exact h tk ht
        · exact pushWord_textSource st sty cur attr hs h tk ht
      · trivial
    · exact ih st (cur.push c) h

private theorem pushText_textSource (st : FlattenSt) (sty : TextStyle) (s : String)
    (hs : sty.smallcaps = false) (h : ∀ tk ∈ st.toks, tk.TextSource) :
    ∀ tk ∈ (pushText st sty s).toks, tk.TextSource :=
  pushChars_textSource sty st.ctr.take.1 s.toList hs _ #[] h

private theorem flattenList_textSource (mathOk noteOk : Bool) (sty : TextStyle)
    (xs : List Inline) (hs : sty.smallcaps = false) : ∀ st,
    (∀ x ∈ xs, ∃ s, x = .text s) → (∀ tk ∈ st.toks, tk.TextSource) →
    ∀ tk ∈ (flattenList mathOk noteOk st sty xs).toks, tk.TextSource := by
  induction xs with
  | nil => intro st _ h; exact h
  | cons x xs ih =>
    intro st hp ht
    obtain ⟨s, rfl⟩ := hp x (by simp)
    exact ih _ (fun x hx => hp x (by simp [hx])) (pushText_textSource st sty s hs ht)

private theorem flatten_textSource (mathOk noteOk : Bool) (st : FlattenSt)
    (sty : TextStyle) (xs : Array Inline) (hp : PlainInlines xs)
    (hs : sty.smallcaps = false) (ht : ∀ tk ∈ st.toks, tk.TextSource) :
    ∀ tk ∈ (flatten mathOk noteOk st sty xs).toks, tk.TextSource := by
  rw [flatten]
  exact flattenList_textSource mathOk noteOk sty xs.toList hs st
    (fun x hx => hp x (by simpa using hx)) ht

private theorem wordItemChars_inkCensus (c : Char) :
    inkCensus (wordItemChars c) = inkCensus [c] := by
  unfold wordItemChars
  split
  · rfl
  · split
    · rename_i h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | rfl
      · simp [inkCensus, inkScalar, h]
      · simp [inkCensus, inkScalar]
    · rfl

private theorem flatMap_wordItemChars_inkCensus (cs : List Char) :
    inkCensus (cs.flatMap wordItemChars) = inkCensus cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change inkCensus (wordItemChars c ++ cs.flatMap wordItemChars) =
      inkCensus ([c] ++ cs)
    simp only [inkCensus, List.filter_append]
    rw [show (wordItemChars c).filter inkScalar = [c].filter inkScalar from
      wordItemChars_inkCensus c, show (cs.flatMap wordItemChars).filter inkScalar =
      cs.filter inkScalar from ih]

private theorem Tk.itemChars_inkCensus (tk : Tk) (ht : tk.TextSource) :
    inkCensus tk.itemChars = inkCensus tk.sourceChars := by
  cases tk <;> simp only [Tk.TextSource] at ht
  all_goals first | contradiction | skip
  · exact flatMap_wordItemChars_inkCensus _
  · simp [Tk.itemChars, Tk.sourceChars, inkCensus, inkScalar, fixedSpace]

private theorem toks_itemChars_inkCensus (ts : List Tk) (ht : ∀ tk ∈ ts, tk.TextSource) :
    inkCensus (ts.flatMap Tk.itemChars) = inkCensus (ts.flatMap Tk.sourceChars) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.flatMap_cons, inkCensus, List.filter_append]
    rw [show t.itemChars.filter inkScalar = t.sourceChars.filter inkScalar from
      Tk.itemChars_inkCensus t (ht t (by simp))]
    rw [show (ts.flatMap Tk.itemChars).filter inkScalar =
      (ts.flatMap Tk.sourceChars).filter inkScalar from
      ih (fun t h => ht t (by simp [h]))]

private theorem itemsOfToks_flatten_none_chars (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (cache : Std.HashMap String (Array Nat)) (ctr : LeafCtr)
    (baseStyle : TextStyle) (xs : Array Inline) (noteOk : Bool)
    (ladder : List (String × Nat)) (step : Nat)
    (roleMetrics : List (String × (Sp × Option Sp))) (steps : Nat)
    (hp : PlainInlines xs) (hs : baseStyle.smallcaps = false) :
    let st := flatten (fs.mathFont?.isSome) noteOk
      { ladder := ladder, roleMetrics := roleMetrics, ctr := ctr, step := step,
        steps := steps } baseStyle xs
    let out := itemsOfToks none size xHeight fs imgs textW textH { cache := cache } st.toks
    out.Clean → inkCensus out.chars = inkCensus (Ir.plainText xs).toList := by
  dsimp only
  intro hc
  have ht := flatten_textSource (fs.mathFont?.isSome) noteOk
    { ladder := ladder, roleMetrics := roleMetrics, ctr := ctr, step := step,
      steps := steps }
    baseStyle xs hp hs (by simp)
  have hitems := (itemsOfToks_none_chars size xHeight fs imgs textW textH
    { cache := cache } _ ht hc).2
  rw [hitems]
  simp only [ItemsAcc.chars, List.flatMap_nil, List.nil_append]
  rw [toks_itemChars_inkCensus _ (fun tk h => ht tk (by simpa using h))]
  rw [flatten_sourceChars _ _ _ _ _ hp]
  rfl

private theorem pushLoop_array {α β : Type} (xs : Array α) (init : Array β) (f : α → β) :
    (forIn xs init (fun x out => ForInStep.yield (out.push (f x))) : Id (Array β)) =
      init ++ xs.map f := by
  apply Array.toList_inj.mp
  rw [Array.toList_append, Array.toList_map, List.map_eq_flatMap]
  exact scalarLoop_array_census (fun out : Array β => out.toList)
    (fun x => [f x]) (fun x out => pure (.yield (out.push (f x)))) xs init (by
      intro x _ out
      exact ⟨_, rfl, by simp⟩)

private theorem clean_of_diagnostic_maps (acc : ItemsAcc) (ds : Array Diag)
    (dropped : Nat × Char → Diag) (substs : Nat × Char × Nat → Diag)
    (unstyled : Nat × Char × Math.MathAlphabet × Char → Diag)
    (hd : ∀ x, (dropped x).code = "E0405")
    (hs : ∀ x, (substs x).code = "W0009")
    (h : ∀ d ∈ ds ++ acc.dropped.map dropped ++ acc.substs.map substs ++
        acc.unstyled.map unstyled, d.code ≠ "E0405" ∧ d.code ≠ "W0009") :
    acc.Clean := by
  constructor
  · apply Array.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact (h (dropped x) (by
      simp only [Array.mem_append, Array.mem_map]
      exact Or.inl (Or.inl (Or.inr ⟨x, hx, rfl⟩)))).1 (hd x)
  · apply Array.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact (h (substs x) (by
      simp only [Array.mem_append, Array.mem_map]
      exact Or.inl (Or.inr ⟨x, hx, rfl⟩))).2 (hs x)

private theorem itemsOfInlines_noLoss_clean
    (size xHeight : Sp) (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (Array Nat)) (ctr : LeafCtr) (imgs : Image.Store)
    (textW textH : Sp) (noteOk : Bool) (ladder : List (String × Nat)) (step : Nat)
    (roleMetrics : List (String × (Sp × Option Sp))) (steps : Nat) :
    let st := flatten (fs.mathFont?.isSome) noteOk
      { ladder := ladder, roleMetrics := roleMetrics, ctr := ctr, step := step,
        steps := steps } baseStyle xs
    let out := itemsOfToks none size xHeight fs imgs textW textH { cache := cache } st.toks
    (∀ d ∈ (itemsOfInlines none size xHeight fs baseStyle xs cache ctr imgs textW textH
      noteOk ladder step roleMetrics steps).2.1, d.code ≠ "E0405" ∧ d.code ≠ "W0009") → out.Clean := by
  dsimp only
  simp only [itemsOfInlines, bind, pure, Id.run]
  split
  · split <;> simp only [pushLoop_array]
    all_goals
      intro h
      exact clean_of_diagnostic_maps _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) h
  · simp only [Bool.not_false, ite_true]
    simp only [pushLoop_array]
    intro h
    exact clean_of_diagnostic_maps _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) h

private theorem itemsOfInlines_itemChars
    (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (Array Nat)) (ctr : LeafCtr) (imgs : Image.Store)
    (textW textH : Sp) (noteOk : Bool) (ladder : List (String × Nat)) (step : Nat)
    (roleMetrics : List (String × (Sp × Option Sp))) (steps : Nat) :
    (itemsOfInlines pats size xHeight fs baseStyle xs cache ctr imgs textW textH
      noteOk ladder step roleMetrics steps).1.toList.flatMap Item.boxChars =
    (itemsOfToks pats size xHeight fs imgs textW textH { cache := cache }
      (flatten fs.mathFont?.isSome noteOk
        { ladder := ladder, roleMetrics := roleMetrics, ctr := ctr, step := step,
          steps := steps }
        baseStyle xs).toks).chars := by
  simp only [itemsOfInlines, bind, pure, Id.run]
  split
  · split <;> simp [ItemsAcc.chars, Item.boxChars]
  · simp [ItemsAcc.chars, Item.boxChars]

private theorem itemsOfInlines_none_chars (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (cache : Std.HashMap String (Array Nat)) (ctr : LeafCtr)
    (baseStyle : TextStyle) (xs : Array Inline) (noteOk : Bool)
    (ladder : List (String × Nat)) (step : Nat)
    (roleMetrics : List (String × (Sp × Option Sp))) (steps : Nat)
    (hp : PlainInlines xs) (hs : baseStyle.smallcaps = false)
    (hd : ∀ d ∈ (itemsOfInlines none size xHeight fs baseStyle xs cache ctr imgs
      textW textH noteOk ladder step roleMetrics steps).2.1,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") :
    inkCensus ((itemsOfInlines none size xHeight fs baseStyle xs cache ctr imgs
      textW textH noteOk ladder step roleMetrics steps).1.toList.flatMap Item.boxChars) =
      inkCensus (Ir.plainText xs).toList := by
  rw [itemsOfInlines_itemChars]
  exact itemsOfToks_flatten_none_chars size xHeight fs imgs textW textH cache ctr
    baseStyle xs noteOk ladder step roleMetrics steps hp hs
    (itemsOfInlines_noLoss_clean size xHeight fs baseStyle xs cache ctr imgs
      textW textH noteOk ladder step roleMetrics steps hd)

public def canBreakAt (items : Array Item) (j : Nat) : Bool :=
  match items[j]? with
  | some (.glue _) | some (.decoratedGlue _ _) =>
    match items[j-1]? with
    | some (.box _ _ _ _ _ _ _ _ _ _ _) => j > 0
    | some (.img _ _ _ _) => j > 0
    | some (.rule _ _ _ _) => j > 0
    | _ => false
  | some (.pen _ cost _ _ _ _) => cost < 10000
  | _ => false

public structure Measure where
  natural : Sp := 0
  stretch : Sp := 0
  shrink : Sp := 0
  fil : Bool := false
  /-- Total width of the line's font boxes and its hyphen, which font expansion may rescale. -/
  boxW : Sp := 0

/-- Font expansion bound, per mille of a glyph's width: microtype's
default `stretch = 20`, `shrink = 20` (microtype.sty). -/
public def expandLimit : Nat := 20

/-- Character protrusion factors `(left, right)` in per mille of
the glyph's width: microtype's `cmr-default` list (mt-cmr.cfg). -/
public def protrusionLR (c : Char) : Nat × Nat :=
  match c with
  | 'A' => (50, 50)
  | 'F' => (0, 50)
  | 'J' => (50, 0)
  | 'K' => (0, 50)
  | 'L' => (0, 50)
  | 'T' => (50, 50)
  | 'V' => (50, 50)
  | 'W' => (50, 50)
  | 'X' => (50, 50)
  | 'Y' => (50, 50)
  | 'k' => (0, 50)
  | 'r' => (0, 50)
  | 't' => (0, 70)
  | 'v' => (50, 50)
  | 'w' => (50, 50)
  | 'x' => (50, 50)
  | 'y' => (50, 70)
  | '0' => (0, 50)
  | '1' => (100, 200)
  | '2' => (50, 50)
  | '3' => (50, 50)
  | '4' => (70, 70)
  | '5' => (0, 50)
  | '6' => (0, 50)
  | '7' => (50, 100)
  | '8' => (0, 50)
  | '9' => (0, 50)
  | '.' => (0, 700)
  | ',' => (0, 500)
  | ':' => (0, 500)
  | ';' => (0, 500)
  | '!' => (0, 100)
  | '?' => (0, 200)
  | '@' => (50, 50)
  | '~' => (200, 250)
  | '%' => (50, 50)
  | '*' => (300, 300)
  | '+' => (250, 250)
  | '(' => (300, 0)
  | ')' => (0, 300)
  | '/' => (200, 300)
  | '-' => (400, 500)
  | '–' => (400, 300)
  | '—' => (300, 200)
  | '‘' => (500, 700)
  | '’' => (500, 600)
  | '“' => (500, 300)
  | '”' => (200, 600)
  | _ => (0, 0)

public theorem protrusionLR_covers (c : Char) :
    (protrusionLR c).1 ≤ 1000 ∧ (protrusionLR c).2 ≤ 1000 := by
  unfold protrusionLR
  split <;> decide

/-- How far the line `[a:j)` may hang left of the
measure: its first glyph's left protrusion, in sp. -/
public def protrudeLeft (items : Array Item) (a j : Nat) : Sp := Id.run do
  for k in [a:j] do
    match items[k]? with
    | some (.box _ _ _ _ glyphs _ _ _ _ _ _) =>
      if let some (_, c, adv) := glyphs[0]? then
        return adv * (protrusionLR c).1 / 1000
    | some (.img ..) | some (.rule ..) => return 0
    | _ => pure ()
  return 0

/-- How far the line breaking at `j` may hang right of the measure:
its last glyph's right protrusion, the break's own hyphen first. -/
public def protrudeRight (items : Array Item) (a j : Nat) : Sp := Id.run do
  if let some (.pen _ _ _ _ _ glyphs) := items[j]? then
    if let some (_, c, adv) := glyphs.back? then
      return adv * (protrusionLR c).2 / 1000
  for i in [0:j - a] do
    match items[j - 1 - i]? with
    | some (.box _ _ _ _ glyphs _ _ _ _ _ _) =>
      if let some (_, c, adv) := glyphs.back? then
        return adv * (protrusionLR c).2 / 1000
    | some (.img ..) | some (.rule ..) => return 0
    | _ => pure ()
  return 0

/-- The largest right overhang any break in `items` can grant,
by which `kp`'s deactivation slackens under protrusion. -/
public def maxProtrudeRight (items : Array Item) : Sp := Id.run do
  let mut best : Sp := 0
  for it in items do
    match it with
    | .box _ _ _ _ glyphs _ _ _ _ _ _ =>
      if let some (_, c, adv) := glyphs.back? then
        best := max best (adv * (protrusionLR c).2 / 1000)
    | .pen _ _ _ _ _ glyphs =>
      if let some (_, c, adv) := glyphs.back? then
        best := max best (adv * (protrusionLR c).2 / 1000)
    | _ => pure ()
  return best

/-- Where a line's content starts: past the glue and penalties a break
leaves, which TeX discards; a first line keeps its authored glue. -/
public def lineStart (items : Array Item) (start : Nat) : Nat := Id.run do
  let mut a := start
  for _ in [a:items.size] do
    match items[a]? with
    | some (.glue g) | some (.decoratedGlue g _) =>
      if start == 0 && !g.word && !g.parfill then break else a := a + 1
    | some (.pen _ cost _ _ _ _) => if cost ≥ 10000 then break else a := a + 1
    | _ => break
  return a

public def measure (items : Array Item) (a j : Nat) (protrude : Bool := false) :
    Measure := Id.run do
  let mut m : Measure := {}
  for k in [a:j] do
    match items[k]! with
    | .box w _ _ _ _ _ _ _ _ _ _ =>
      m := { m with natural := m.natural + w, boxW := m.boxW + w }
    | .img _ w _ _ => m := { m with natural := m.natural + w }
    | .rule w _ _ _ => m := { m with natural := m.natural + w }
    | .poly _ _ => pure ()
    | .glue g | .decoratedGlue g _ => m := { m with
        natural := m.natural + g.width
        stretch := m.stretch + g.stretch
        shrink := m.shrink + g.shrink
        fil := m.fil || g.fil }
    | .pen _ _ _ _ _ _ => pure ()
  if let some (.pen w _ _ _ _ _) := items[j]? then
    m := { m with natural := m.natural + w, boxW := m.boxW + w }
  -- The breaker measures a line as set, protrusion included; fil lines never protrude.
  if protrude && !m.fil then
    m := { m with natural := m.natural - protrudeLeft items a j - protrudeRight items a j }
  return m

/-- What a `Measure`'s font boxes may stretch or
shrink beyond the glue, in sp; zero on a fil line. -/
public def Measure.ex (m : Measure) (expand : Bool) : Sp :=
  if expand && !m.fil then m.boxW * expandLimit / 1000 else 0

public def overfullDemerits : Int := 100000000

/-- What an overfull line costs: `overfullDemerits` and as much again per whole point
it overhangs, so it ends at its first break past its unbreakable run (tex.web §854). -/
public def overfullCost (overhang : Sp) : Int :=
  overfullDemerits * (1 + overhang / Dim.pt 1) -- per point: TeX reports an overfull box in pt (tex.web §663)

/-- Demerits of one candidate line, the badness denominators grown by
font expansion (`Measure.ex`); under `fil` only shrink is priced. -/
public def lineDemerits (items : Array Item) (m : Measure) (target : Sp) (j : Nat)
    (expand : Bool := false) (fil : Bool := false) : Int :=
  let ex := m.ex expand
  let delta := target - m.natural
  let b : Int :=
    if delta == 0 then 0
    else if delta > 0 then
      if m.fil || fil then 0 else badness delta (m.stretch + ex)
    else
      if m.shrink + ex < -delta then -1  -- overfull marker
      else badness delta (m.shrink + ex)
  let base : Int :=
    if b < 0 then overfullCost (m.natural - target)
    else (10 + b) ^ 2
  let penTerm : Int :=
    match items[j]? with
    | some (.pen _ cost _ _ _ _) =>
      if cost ≤ forcedCost then 0
      else if cost > 0 then cost ^ 2
      else -(cost ^ 2)
    | _ => 0
  base + penTerm

public def isForced (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.pen _ cost _ _ _ _) => cost ≤ forcedCost
  | _ => false

public def isFlagged (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.pen _ _ flagged _ _ _) => flagged
  | _ => false

public def doubleHyphenDemerits : Int := 10000

/-- TeX's `\finalhyphendemerits`, plain and LaTeX's 5000 (TeXbook ch. 14). -/
public def finalHyphenDemerits : Int := 5000

/-- Demerits a centred paragraph's one-word last line adds: one, so
it decides only among break sequences TeX's `\centering` ties. -/
public def runtDemerits : Int := 1

/-- Whether the line from `a` to the break at `j` holds no interword glue. -/
public def oneWordLine (items : Array Item) (a j : Nat) : Bool :=
  !((List.range (j - a)).any fun i => match items[a + i]? with
    | some (.glue g) | some (.decoratedGlue g _) => g.word
    | some (.box ..) | some (.pen ..) | some (.img ..) | some (.rule ..) | some (.poly ..)
    | none => false)

/-- Prefix sums over item width, stretch, shrink, fil and forced counts, one slot past the end. -/
public structure KpSums where
  w : Array Sp
  s : Array Sp
  k : Array Sp
  f : Array Nat
  forced : Array Nat
  /-- Prefix sums of font-box widths, scaled once at the read. -/
  b : Array Sp
  /-- The stretch every line carries besides its own glue, TeX's
  background (tex.web §827); zero but in a narrowed table cell. -/
  bg : Sp := 0

public def kpSums (items : Array Item) : KpSums := Id.run do
  let n := items.size
  let mut pw : Array Sp := Array.mkEmpty (n + 1)
  let mut ps : Array Sp := Array.mkEmpty (n + 1)
  let mut pk : Array Sp := Array.mkEmpty (n + 1)
  let mut pf : Array Nat := Array.mkEmpty (n + 1)
  let mut pforced : Array Nat := Array.mkEmpty (n + 1)
  let mut pb : Array Sp := Array.mkEmpty (n + 1)
  let mut btot : Sp := 0
  pw := pw.push 0
  ps := ps.push 0
  pk := pk.push 0
  pf := pf.push 0
  pforced := pforced.push 0
  pb := pb.push 0
  for k in [0:n] do
    let (dw, dst, dsh, dfil, db) : Sp × Sp × Sp × Nat × Sp := match items[k]! with
      | .box w _ _ _ _ _ _ _ _ _ _ => (w, 0, 0, 0, w)
      | .img _ w _ _ => (w, 0, 0, 0, 0)
      | .rule w _ _ _ => (w, 0, 0, 0, 0)
      | .poly _ _ => (0, 0, 0, 0, 0)
      | .glue g | .decoratedGlue g _ =>
        (g.width, g.stretch, g.shrink, if g.fil then 1 else 0, 0)
      | .pen _ _ _ _ _ _ => (0, 0, 0, 0, 0)
    pw := pw.push (pw[k]! + dw)
    ps := ps.push (ps[k]! + dst)
    pk := pk.push (pk[k]! + dsh)
    pf := pf.push (pf[k]! + dfil)
    pforced := pforced.push (pforced[k]! + (if isForced items k then 1 else 0))
    btot := btot + db
    pb := pb.push btot
  return { w := pw, s := ps, k := pk, f := pf, forced := pforced, b := pb }

/-- The line measure `kp` uses: prefix-sum differences over `[a:j)`
plus the broken penalty's width, less the protrusion term. -/
public def kpMeasure (items : Array Item) (sums : KpSums) (a j : Nat)
    (protrude : Bool := false) : Measure :=
  let penW : Sp := match items[j]? with
    | some (.pen w _ _ _ _ _) => w
    | _ => 0
  let m : Measure :=
    { natural := sums.w[j]! - sums.w[a]! + penW
      stretch := sums.s[j]! - sums.s[a]!
      shrink := sums.k[j]! - sums.k[a]!
      fil := sums.f[j]! - sums.f[a]! > 0
      boxW := (sums.b[j]?.getD 0) - (sums.b[a]?.getD 0) + penW }
  if protrude && !m.fil then
    { m with natural := m.natural - protrudeLeft items a j - protrudeRight items a j }
  else m

private theorem arrayGetD_set_self {α : Type} (xs : Array α) (i : Nat) (x : α)
    (hi : i < xs.size) {d : α} : (xs.set! i x).getD i d = x := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt hi, Option.getD_some]

private theorem arrayGetD_set_ne {α : Type} (xs : Array α) (i j : Nat) (x : α)
    (hij : i ≠ j) {d : α} : (xs.set! i x).getD j d = xs.getD j d := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne hij]

private abbrev KpEntry := Int × Nat

/-- Whether break `p` stands after break `q` in a
paragraph of `n` items, whose start node is `n`. -/
private def kpLater (n p q : Nat) : Bool :=
  if q == n then p != n else p != n && q < p

/-- Choose between candidates by strict demerits, a tie going to the later
predecessor under `latest`, as TeX's breaker keeps the last (tex.web §855). -/
private def kpChoose (old : Option KpEntry) (candidate : KpEntry) (latest : Option Nat := none) :
    Option KpEntry :=
  match old with
  | some best =>
    if candidate.1 < best.1 ||
        (candidate.1 == best.1 && latest.any (kpLater · candidate.2 best.2)) then some candidate
    else old
  | none => some candidate

private structure KpCandidates where
  here : Option KpEntry := none
  survivors : Array Nat := #[]
  droppedPlain : Option KpEntry := none
  droppedFlagged : Option KpEntry := none

private structure KpState where
  best : Array (Option KpEntry)
  active : Array Nat

private def kpStart (items : Array Item) (p : Nat) : Nat :=
  lineStart items (if p == items.size then 0 else p + 1)

private def kpCandidate (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil runt : Bool)
    (best : Array (Option KpEntry)) (j p : Nat) (c : KpCandidates) : KpCandidates := Id.run do
  let n := items.size
  if p == n || p < j then
    let a := kpStart items p
    let spansForced := a < j && (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) > 0
    if !spansForced && a ≤ j then
      match (best.getD (p) none) with
      | some (d0, _) =>
        let m := kpMeasure items sums a j protrude
        let dbl := if p != n && isFlagged items p && isFlagged items j then
          doubleHyphenDemerits else 0
        let fin := if p != n && isFlagged items p && j == n - 1 then
          finalHyphenDemerits else 0
        let lone := if runt && j == n - 1 && oneWordLine items a j then runtDemerits else 0
        let d := d0 + lineDemerits items { m with stretch := m.stretch + sums.bg } target j expand
          fil + dbl + fin + lone
        let ties := if fil then some n else none
        let c := { c with here := kpChoose c.here (d, p) ties }
        if m.natural - (m.shrink + m.ex expand) > target + slack then
          if p != n && isFlagged items p then
            return { c with droppedFlagged := kpChoose c.droppedFlagged (d, p) ties }
          else
            return { c with droppedPlain := kpChoose c.droppedPlain (d, p) ties }
        else
          return { c with survivors := c.survivors.push p }
      | none => return c
    else if !spansForced then
      return { c with survivors := c.survivors.push p }
    else return c
  else return { c with survivors := c.survivors.push p }

private def KpEntry.Valid (items : Array Item) (best : Array (Option KpEntry))
    (j : Nat) (e : KpEntry) : Prop :=
  (e.2 = items.size ∨ e.2 < j) ∧ ((best.getD (e.2) none)).isSome = true ∧ kpStart items e.2 ≤ j

private def KpCandidates.Good (items : Array Item) (c : KpCandidates) : Prop :=
  (∃ p ∈ c.survivors, kpStart items p < items.size) ∨
    (∃ e, c.droppedPlain = some e ∧ kpStart items e.2 < items.size) ∨
    (∃ e, c.droppedFlagged = some e ∧ kpStart items e.2 < items.size)

private theorem kpChoose_all (P : KpEntry → Prop) (old : Option KpEntry) (candidate : KpEntry)
    {latest : Option Nat} (ho : ∀ e, old = some e → P e) (hc : P candidate) :
    ∀ e, kpChoose old candidate latest = some e → P e := by
  cases old with
  | none => intro e he; cases he; exact hc
  | some b =>
    simp only [kpChoose]
    split
    · intro e he; cases he; exact hc
    · exact ho

private theorem kpChoose_isSome (old : Option KpEntry) (candidate : KpEntry)
    {latest : Option Nat} :
    (kpChoose old candidate latest).isSome = true := by
  cases old <;> simp [kpChoose]
  split <;> rfl

private theorem kpChoose_eq_some (old : Option KpEntry) (candidate : KpEntry)
    {latest : Option Nat} :
    ∃ e, kpChoose old candidate latest = some e := by
  exact Option.isSome_iff_exists.mp (kpChoose_isSome old candidate)

private def KpCandidates.Valid (items : Array Item) (best : Array (Option KpEntry))
    (j : Nat) (c : KpCandidates) : Prop :=
  (∀ e, c.here = some e → e.Valid items best j) ∧
  (∀ e, c.droppedPlain = some e → e.Valid items best j) ∧
  (∀ e, c.droppedFlagged = some e → e.Valid items best j) ∧
  (∀ p ∈ c.survivors, (p = items.size ∨ p < j) ∧ ((best.getD (p) none)).isSome = true)

private theorem kpCandidate_valid (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (best : Array (Option KpEntry))
    (j p : Nat) (c : KpCandidates) (hc : c.Valid items best j)
    (hp : (p = items.size ∨ p < j) ∧ ((best.getD (p) none)).isSome = true) :
    (kpCandidate items sums target slack protrude expand fil runt best j p c).Valid items best j := by
  have hpj : (p == items.size || p < j) = true := by simpa using hp.1
  simp only [kpCandidate, hpj, ite_true, pure, Id.run]
  split
  · rename_i h
    have ha : kpStart items p ≤ j := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    split
    · have hv (d : Int) : KpEntry.Valid items best j (d, p) := ⟨hp.1, hp.2, ha⟩
      split
      · split
        · exact ⟨kpChoose_all _ _ _ hc.1 (hv _), hc.2.1,
            kpChoose_all _ _ _ hc.2.2.1 (hv _), hc.2.2.2⟩
        · exact ⟨kpChoose_all _ _ _ hc.1 (hv _), kpChoose_all _ _ _ hc.2.1 (hv _),
            hc.2.2.1, hc.2.2.2⟩
      · refine ⟨kpChoose_all _ _ _ hc.1 (hv _), hc.2.1, hc.2.2.1, ?_⟩
        intro q hq
        rcases Array.mem_push.mp hq with hq | rfl
        · exact hc.2.2.2 q hq
        · exact hp
    · exact hc
  · split
    · refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
      intro q hq
      rcases Array.mem_push.mp hq with hq | rfl
      · exact hc.2.2.2 q hq
      · exact hp
    · exact hc

private theorem kpCandidate_good (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (best : Array (Option KpEntry))
    (j p : Nat) (c : KpCandidates) (hj : j < items.size)
    (hc : c.Valid items best j)
    (hp : (p = items.size ∨ p < j) ∧ ((best.getD (p) none)).isSome = true)
    (hf : ∀ a, a < j → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (hg : c.Good items ∨ kpStart items p < items.size) :
    (kpCandidate items sums target slack protrude expand fil runt best j p c).Good items := by
  have hpj : (p == items.size || p < j) = true := by simpa using hp.1
  have hn : (kpStart items p < j && (sums.forced.getD (j) 0) - (sums.forced.getD (kpStart items p) 0) > 0) = false := by
    by_cases ha : kpStart items p < j
    · rw [hf _ ha]
      simp
    · simp [ha]
  simp only [kpCandidate, hpj, ite_true, hn, Bool.not_false, Bool.true_and,
    pure, Id.run]
  split
  · rename_i ha
    have hpg : kpStart items p < items.size := Nat.lt_of_le_of_lt (of_decide_eq_true ha) hj
    split
    · split
      · split
        · obtain ⟨e, he⟩ := kpChoose_eq_some c.droppedFlagged (_, p)
            (latest := if fil then some items.size else none)
          refine Or.inr (Or.inr ⟨e, he, ?_⟩)
          exact kpChoose_all (fun e => kpStart items e.2 < items.size) _ _
            (fun e he => Nat.lt_of_le_of_lt (hc.2.2.1 e he).2.2 hj) hpg e he
        · obtain ⟨e, he⟩ := kpChoose_eq_some c.droppedPlain (_, p)
            (latest := if fil then some items.size else none)
          refine Or.inr (Or.inl ⟨e, he, ?_⟩)
          exact kpChoose_all (fun e => kpStart items e.2 < items.size) _ _
            (fun e he => Nat.lt_of_le_of_lt (hc.2.1 e he).2.2 hj) hpg e he
      · exact Or.inl ⟨p, Array.mem_push_self, hpg⟩
    · rename_i he
      simp [he] at hp
  · rcases hg with (⟨q, hq, hqg⟩ | hg) | hpg
    · exact Or.inl ⟨q, Array.mem_push_of_mem p hq, hqg⟩
    · exact Or.inr hg
    · exact Or.inl ⟨p, Array.mem_push_self, hpg⟩

private theorem kpCandidate_here (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (best : Array (Option KpEntry))
    (j p : Nat) (c : KpCandidates)
    (hp : (p = items.size ∨ p < j) ∧ ((best.getD (p) none)).isSome = true)
    (hf : ∀ a, a < j → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (hg : c.here.isSome = true ∨ kpStart items p ≤ j) :
    (kpCandidate items sums target slack protrude expand fil runt best j p c).here.isSome = true := by
  have hpj : (p == items.size || p < j) = true := by simpa using hp.1
  have hn : (kpStart items p < j && (sums.forced.getD (j) 0) - (sums.forced.getD (kpStart items p) 0) > 0) = false := by
    by_cases ha : kpStart items p < j
    · rw [hf _ ha]
      simp
    · simp [ha]
  simp only [kpCandidate, hpj, ite_true, hn, Bool.not_false, Bool.true_and, pure, Id.run]
  split
  · split
    · split
      · split <;> exact kpChoose_isSome _ _
      · exact kpChoose_isSome _ _
    · rename_i he
      simp [he] at hp
  · rename_i ha
    rcases hg with hg | hg
    · exact hg
    · simp [hg] at ha

private theorem kpScan_valid (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (best : Array (Option KpEntry))
    (j : Nat) (ps : List Nat) : ∀ c,
    c.Valid items best j →
    (∀ p ∈ ps, (p = items.size ∨ p < j) ∧ ((best.getD (p) none)).isSome = true) →
    (forIn ps c (fun p c => pure (.yield
      (kpCandidate items sums target slack protrude expand fil runt best j p c))) : Id KpCandidates).Valid
        items best j := by
  induction ps with
  | nil => intro c hc _; exact hc
  | cons p ps ih =>
    intro c hc hp
    simp only [List.forIn_cons, bind, pure]
    exact ih _ (kpCandidate_valid _ _ _ _ _ _ _ _ _ _ _ hc (hp p (by simp)))
      (fun q hq => hp q (by simp [hq]))

private theorem kpScan_good (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (best : Array (Option KpEntry))
    (j : Nat) (hj : j < items.size)
    (hf : ∀ a, a < j → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (ps : List Nat) : ∀ c,
    c.Valid items best j →
    (∀ p ∈ ps, (p = items.size ∨ p < j) ∧ ((best.getD (p) none)).isSome = true) →
    (c.Good items ∨ ∃ p ∈ ps, kpStart items p < items.size) →
    (forIn ps c (fun p c => pure (.yield
      (kpCandidate items sums target slack protrude expand fil runt best j p c))) : Id KpCandidates).Good
        items := by
  induction ps with
  | nil =>
    intro c _ _ hg
    simpa [pure] using hg
  | cons p ps ih =>
    intro c hc hp hg
    simp only [List.forIn_cons, bind, pure]
    apply ih _ (kpCandidate_valid _ _ _ _ _ _ _ _ _ _ _ hc (hp p (by simp)))
      (fun q hq => hp q (by simp [hq]))
    rcases hg with hg | ⟨q, hq, hqg⟩
    · exact Or.inl (kpCandidate_good _ _ _ _ _ _ _ _ _ _ _ hj hc (hp p (by simp)) hf (Or.inl hg))
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl (kpCandidate_good _ _ _ _ _ _ _ _ _ _ _ hj hc (hp q (by simp)) hf (Or.inr hqg))
      · exact Or.inr ⟨q, hq, hqg⟩

private theorem kpScan_here (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (best : Array (Option KpEntry))
    (j : Nat) (hf : ∀ a, a < j → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (ps : List Nat) : ∀ c,
    (∀ p ∈ ps, (p = items.size ∨ p < j) ∧ ((best.getD (p) none)).isSome = true) →
    (c.here.isSome = true ∨ ∃ p ∈ ps, kpStart items p ≤ j) →
    (forIn ps c (fun p c => pure (.yield
      (kpCandidate items sums target slack protrude expand fil runt best j p c))) : Id KpCandidates).here.isSome = true := by
  induction ps with
  | nil =>
    intro c _ hg
    simpa [pure] using hg
  | cons p ps ih =>
    intro c hp hg
    simp only [List.forIn_cons, bind, pure]
    apply ih _ (fun q hq => hp q (by simp [hq]))
    rcases hg with hg | ⟨q, hq, hqg⟩
    · exact Or.inl (kpCandidate_here _ _ _ _ _ _ _ _ _ _ _ (hp p (by simp)) hf (Or.inl hg))
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl (kpCandidate_here _ _ _ _ _ _ _ _ _ _ _ (hp q (by simp)) hf (Or.inr hqg))
      · exact Or.inr ⟨q, hq, hqg⟩

private def KpTable (items : Array Item) (t : Nat) (best : Array (Option KpEntry)) : Prop :=
  best.size = items.size + 1 ∧
  ∀ k e, k < items.size → (best.getD (k) none) = some e →
    k < t ∧ canBreakAt items k = true ∧ e.Valid items best k

private def KpState.Valid (items : Array Item) (t : Nat) (st : KpState) : Prop :=
  KpTable items t st.best ∧
  ∀ p ∈ st.active, (p = items.size ∨ p < t) ∧ ((st.best.getD (p) none)).isSome = true

private theorem kpTable_mono (items : Array Item) (s t : Nat) (best : Array (Option KpEntry))
    (h : KpTable items s best) (hst : s ≤ t) : KpTable items t best := by
  refine ⟨h.1, ?_⟩
  intro k e hk he
  obtain ⟨hks, hb, hp⟩ := h.2 k e hk he
  exact ⟨Nat.lt_of_lt_of_le hks hst, hb, hp⟩

private theorem kpTable_set (items : Array Item) (j : Nat) (best : Array (Option KpEntry))
    (e : KpEntry) (hj : j < items.size) (ht : KpTable items j best)
    (hb : canBreakAt items j = true) (he : e.Valid items best j) :
    KpTable items (j+1) (best.set! j (some e)) := by
  have hsize := ht.1
  refine ⟨by simpa using ht.1, ?_⟩
  intro k d hk hd
  by_cases hkj : k = j
  · subst k
    rw [arrayGetD_set_self _ _ _ (by omega)] at hd
    cases hd
    refine ⟨by omega, hb, he.1, ?_, he.2.2⟩
    rw [arrayGetD_set_ne _ _ _ _ (by rcases he.1 with he | he <;> omega)]
    exact he.2.1
  · rw [arrayGetD_set_ne _ _ _ _ (Ne.symm hkj)] at hd
    obtain ⟨hkj', hbk, hp⟩ := ht.2 k d hk hd
    refine ⟨by omega, hbk, hp.1, ?_, hp.2.2⟩
    rw [arrayGetD_set_ne _ _ _ _ (by rcases hp.1 with hp | hp <;> omega)]
    exact hp.2.1

private def kpRetain (ps : Array Nat) : Option KpEntry → Array Nat
  | some (_, p) => ps.push p
  | none => ps

private def kpClose (j : Nat) (best : Array (Option KpEntry)) (c : KpCandidates) : KpState :=
  let chosen := if c.here.isSome then best.set! j c.here else best
  let survivors := if c.here.isSome then c.survivors.push j else c.survivors
  { best := chosen, active := kpRetain (kpRetain survivors c.droppedPlain) c.droppedFlagged }

private theorem kpRetain_mem (ps : Array Nat) (e : Option KpEntry) (p : Nat) :
    p ∈ kpRetain ps e ↔ p ∈ ps ∨ ∃ d, e = some d ∧ p = d.2 := by
  cases e with
  | none => simp [kpRetain]
  | some d => simp [kpRetain]

private theorem kpClose_valid (items : Array Item) (j : Nat) (best : Array (Option KpEntry))
    (c : KpCandidates) (hj : j < items.size) (ht : KpTable items j best)
    (hb : canBreakAt items j = true) (hc : c.Valid items best j) :
    (kpClose j best c).Valid items (j+1) := by
  have hsize := ht.1
  cases hh : c.here with
  | none =>
    simp only [kpClose, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    refine ⟨kpTable_mono _ _ _ _ ht (by omega), ?_⟩
    intro p hp
    simp only [kpRetain_mem] at hp
    rcases hp with (hp | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · obtain ⟨hp, hs⟩ := hc.2.2.2 p hp
      exact ⟨hp.imp_right (by omega), hs⟩
    · have h := hc.2.1 e he
      exact ⟨h.1.imp_right (by omega), h.2.1⟩
    · have h := hc.2.2.1 e he
      exact ⟨h.1.imp_right (by omega), h.2.1⟩
  | some e =>
    simp only [kpClose, hh, Option.isSome_some, ↓reduceIte]
    refine ⟨kpTable_set _ _ _ _ hj ht hb (hc.1 e hh), ?_⟩
    intro p hp
    simp only [kpRetain_mem, Array.mem_push] at hp
    rcases hp with ((hp | rfl) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
    · obtain ⟨hp, hs⟩ := hc.2.2.2 p hp
      refine ⟨hp.imp_right (by omega), ?_⟩
      rw [arrayGetD_set_ne _ _ _ _ (by rcases hp with hp | hp <;> omega)]
      exact hs
    · refine ⟨Or.inr (by omega), ?_⟩
      rw [arrayGetD_set_self _ _ _ (by omega)]
      rfl
    · have h := hc.2.1 d hd
      refine ⟨h.1.imp_right (by omega), ?_⟩
      rw [arrayGetD_set_ne _ _ _ _ (by rcases h.1 with h | h <;> omega)]
      exact h.2.1
    · have h := hc.2.2.1 d hd
      refine ⟨h.1.imp_right (by omega), ?_⟩
      rw [arrayGetD_set_ne _ _ _ _ (by rcases h.1 with h | h <;> omega)]
      exact h.2.1

private theorem kpClose_good (items : Array Item) (j : Nat) (best : Array (Option KpEntry))
    (c : KpCandidates) (hg : c.Good items) :
    ∃ p ∈ (kpClose j best c).active, kpStart items p < items.size := by
  simp only [kpClose, kpRetain_mem]
  rcases hg with ⟨p, hp, hg⟩ | ⟨e, he, hg⟩ | ⟨e, he, hg⟩
  · refine ⟨p, Or.inl (Or.inl ?_), hg⟩
    split
    · exact Array.mem_push_of_mem _ hp
    · exact hp
  · exact ⟨e.2, Or.inl (Or.inr ⟨e, he, rfl⟩), hg⟩
  · exact ⟨e.2, Or.inr ⟨e, he, rfl⟩, hg⟩

private theorem kpClose_here (j : Nat) (best : Array (Option KpEntry))
    (c : KpCandidates) (hj : j < best.size) (hh : c.here.isSome = true) :
    (((kpClose j best c).best.getD j none)).isSome = true := by
  simp only [kpClose, hh, ↓reduceIte]
  rw [arrayGetD_set_self _ _ _ hj]
  exact hh

private def kpPosition (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil runt : Bool) (j : Nat) (st : KpState) : KpState := Id.run do
  if !canBreakAt items j then return st
  let mut c : KpCandidates := {}
  for p in st.active do
    c := kpCandidate items sums target slack protrude expand fil runt st.best j p c
  return kpClose j st.best c

private theorem kpCandidates_empty (items : Array Item) (best : Array (Option KpEntry))
    (j : Nat) : ({} : KpCandidates).Valid items best j := by
  simp [KpCandidates.Valid]

private theorem kpPosition_valid (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (j : Nat) (st : KpState)
    (hj : j < items.size) (hs : st.Valid items j) :
    (kpPosition items sums target slack protrude expand fil runt j st).Valid items (j+1) := by
  by_cases hb : canBreakAt items j = true
  · simp only [kpPosition, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, pure, Id.run]
    apply kpClose_valid _ _ _ _ hj hs.1 hb
    rw [← Array.forIn_toList]
    exact kpScan_valid _ _ _ _ _ _ _ _ _ _ _ (kpCandidates_empty _ _ _) (by simpa using hs.2)
  · simp only [kpPosition, hb, Bool.not_eq_true', ↓reduceIte, pure, Id.run]
    exact ⟨kpTable_mono _ _ _ _ hs.1 (by omega),
      fun p hp => ⟨(hs.2 p hp).1.imp_right (by omega), (hs.2 p hp).2⟩⟩

private theorem kpPosition_good (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (j : Nat) (st : KpState)
    (hj : j < items.size) (hs : st.Valid items j)
    (hf : ∀ a, a < j → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (hg : ∃ p ∈ st.active, kpStart items p < items.size) :
    ∃ p ∈ (kpPosition items sums target slack protrude expand fil runt j st).active,
      kpStart items p < items.size := by
  by_cases hb : canBreakAt items j = true
  · simp only [kpPosition, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, pure, Id.run]
    apply kpClose_good
    rw [← Array.forIn_toList]
    apply kpScan_good _ _ _ _ _ _ _ _ _ hj hf _ _ (kpCandidates_empty _ _ _)
      (by simpa using hs.2)
    exact Or.inr (by simpa using hg)
  · simpa only [kpPosition, hb, Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte,
      pure, Id.run] using hg

private theorem kpPosition_here (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (j : Nat) (st : KpState)
    (hj : j < items.size) (hs : st.Valid items j)
    (hb : canBreakAt items j = true)
    (hf : ∀ a, a < j → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (hg : ∃ p ∈ st.active, kpStart items p ≤ j) :
    (((kpPosition items sums target slack protrude expand fil runt j st).best.getD j none)).isSome = true := by
  simp only [kpPosition, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind, pure, Id.run]
  apply kpClose_here _ _ _ (by rw [hs.1.1]; omega)
  rw [← Array.forIn_toList]
  apply kpScan_here _ _ _ _ _ _ _ _ _ hf _ _ (by simpa using hs.2)
  exact Or.inr (by simpa using hg)

private theorem kpRange_progress {β : Type} (P : Nat → β → Prop) (lo len : Nat)
    (f : Nat → β → β) (init : β) (h0 : P lo init)
    (step : ∀ i, lo ≤ i → i < lo + len → ∀ b, P i b → P (i+1) (f i b)) :
    P (lo+len) (forIn (List.range' lo len) init
      (fun i b => pure (.yield (f i b))) : Id β).run := by
  induction len generalizing lo init with
  | zero => simpa using h0
  | succ len ih =>
    simp only [List.range'_succ, List.forIn_cons, bind, pure, Id.run]
    have h := ih (lo+1) (f lo init) (step lo (by omega) (by omega) init h0)
      (fun i hlo hhi b hb => step i (by omega) (by omega) b hb)
    simpa only [Nat.add_assoc, Nat.add_comm 1 len, pure, Id.run] using h

private def kpInit (n : Nat) : KpState :=
  {best := (Array.replicate (n+1) none).set! n (some (0,n)), active := #[n]}

private theorem kpInit_valid (items : Array Item) :
    (kpInit items.size).Valid items 0 := by
  refine ⟨⟨by simp [kpInit], ?_⟩, ?_⟩
  · intro k e hk he
    change ((Array.replicate (items.size+1) (none : Option KpEntry)).set!
      items.size (some (0, items.size))).getD k none = some e at he
    rw [arrayGetD_set_ne _ _ _ _ (by omega)] at he
    simp [Nat.lt_succ_of_lt hk] at he
  · intro p hp
    have hp : p = items.size := by simpa [kpInit] using hp
    subst p
    refine ⟨Or.inl rfl, ?_⟩
    simp [kpInit]

private def kpForward (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil runt : Bool) (count : Nat) : KpState := Id.run do
  let mut st := kpInit items.size
  for j in [0:count] do
    st := kpPosition items sums target slack protrude expand fil runt j st
  return st

private theorem kpForward_valid (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (count : Nat) (hc : count ≤ items.size) :
    (kpForward items sums target slack protrude expand fil runt count).Valid items count := by
  simp only [kpForward, bind, pure, Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  simpa only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure, Id.run,
    Nat.zero_add] using
    kpRange_progress (KpState.Valid items) 0 count
      (kpPosition items sums target slack protrude expand fil runt) (kpInit items.size)
      (kpInit_valid items)
      (fun i _ hi st hs => kpPosition_valid _ _ _ _ _ _ _ _ _ (by omega) hs)

private theorem kpForward_good (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (count : Nat) (hc : count ≤ items.size)
    (hf : ∀ a j, a < j → j < items.size → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (hg : kpStart items items.size < items.size) :
    ∃ p ∈ (kpForward items sums target slack protrude expand fil runt count).active,
      kpStart items p < items.size := by
  let P := fun i (st : KpState) => st.Valid items i ∧ ∃ p ∈ st.active, kpStart items p < items.size
  have h0 : P 0 (kpInit items.size) :=
    ⟨kpInit_valid items, items.size, by simp [kpInit], hg⟩
  have h := kpRange_progress P 0 count
    (kpPosition items sums target slack protrude expand fil runt) (kpInit items.size) h0
    (fun i _ hi st hs => ⟨kpPosition_valid _ _ _ _ _ _ _ _ _ (by omega) hs.1,
      kpPosition_good _ _ _ _ _ _ _ _ _ (by omega) hs.1
        (fun a ha => hf a i ha (by omega)) hs.2⟩)
  simpa only [kpForward, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind, pure, Id.run] using h.2

private theorem kpForward_succ (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool} (count : Nat) :
    kpForward items sums target slack protrude expand fil runt (count+1) =
      kpPosition items sums target slack protrude expand fil runt count
        (kpForward items sums target slack protrude expand fil runt count) := by
  simp only [kpForward, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind, pure, Id.run]
  rw [List.range'_1_concat]
  change (forIn _ _ (fun j st => pure (.yield
    (kpPosition items sums target slack protrude expand fil runt j st))) : Id KpState) =
    kpPosition items sums target slack protrude expand fil runt count
      (forIn _ _ (fun j st => pure (.yield
        (kpPosition items sums target slack protrude expand fil runt j st))) : Id KpState)
  have h1 := List.forIn_pure_yield_eq_foldl (m := Id)
    (l := List.range' 0 count ++ [count])
    (kpPosition items sums target slack protrude expand fil runt) (kpInit items.size)
  have h2 := List.forIn_pure_yield_eq_foldl (m := Id)
    (l := List.range' 0 count)
    (kpPosition items sums target slack protrude expand fil runt) (kpInit items.size)
  simp only [Nat.zero_add] at *
  rw [h1, h2]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pure]

private theorem kpForward_last (items : Array Item) (sums : KpSums)
    (target slack : Sp) (protrude expand fil : Bool) {runt : Bool}
    (hn : 0 < items.size) (hb : canBreakAt items (items.size-1) = true)
    (hf : ∀ a j, a < j → j < items.size → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0)
    (hg : kpStart items items.size < items.size) :
    (((kpForward items sums target slack protrude expand fil runt items.size).best.getD (items.size-1) none)).isSome = true := by
  have h := kpPosition_here items sums target slack protrude expand fil (runt := runt) (items.size-1)
    (kpForward items sums target slack protrude expand fil runt (items.size-1)) (by omega)
    (kpForward_valid _ _ _ _ _ _ _ _ (by omega)) hb
    (fun a ha => hf a _ ha (by omega)) (by
      obtain ⟨p, hp, hg⟩ := kpForward_good items sums target slack protrude expand fil (runt := runt)
        (items.size-1) (by omega) hf hg
      exact ⟨p, hp, by omega⟩)
  rw [← kpForward_succ] at h
  simpa only [Nat.sub_add_cancel hn] using h

/-- The predecessor chain, in forward line order. -/
private inductive KpChain (items : Array Item) : Nat → List Nat → Prop
  | first {j} : j < items.size → canBreakAt items j = true →
      kpStart items items.size ≤ j → KpChain items j [j]
  | next {p j breaks} : KpChain items p breaks → p < j → j < items.size →
      canBreakAt items j = true → kpStart items p ≤ j →
      KpChain items j (breaks ++ [j])

private def kpBackStep (n : Nat) (best : Array (Option KpEntry))
    (st : Array Nat × Nat) : Id (ForInStep (Array Nat × Nat)) :=
  let breaks := st.1.push st.2
  match (best.getD (st.2) none) with
  | some (_, p) => if p == n then .done (breaks, st.2) else .yield (breaks, p)
  | none => .done (breaks, st.2)

private def kpBack (n : Nat) (best : Array (Option KpEntry)) (last : Nat) : Array Nat := Id.run do
  let st ← forIn [0:n+1] (#[], last) (fun _ => kpBackStep n best)
  return st.1.reverse

private theorem kpBack_trace (items : Array Item) (best : Array (Option KpEntry))
    (ht : KpTable items items.size best) :
    ∀ j, j < items.size → ((best.getD (j) none)).isSome = true →
      ∃ breaks, KpChain items j breaks ∧ ∀ acc : Array Nat,
        ∃ steps st, steps ≤ j+1 ∧ Loop.Stops (kpBackStep items.size best) (acc,j) steps st ∧
          st.1.toList.reverse = breaks ++ acc.toList.reverse := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj hr
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hr
    obtain ⟨_, hb, hp, hrp, ha⟩ := ht.2 j e hj he
    rcases hp with hp | hp
    · refine ⟨[j], .first hj hb (by simpa [hp] using ha), ?_⟩
      intro acc
      refine ⟨1, (acc.push j, j), by omega, ?_, ?_⟩
      · apply Loop.Stops.done
        simp [kpBackStep, he, hp, Id.run]
      · simp
    · obtain ⟨breaks, chain, trace⟩ := ih e.2 hp (by omega) hrp
      refine ⟨breaks ++ [j], .next chain hp hj hb ha, ?_⟩
      intro acc
      obtain ⟨steps, st, hsteps, hs, hchars⟩ := trace (acc.push j)
      refine ⟨steps+1, st, by omega, ?_, ?_⟩
      · apply Loop.Stops.yield (b := (acc.push j, e.2))
        · simp [kpBackStep, he, show e.2 ≠ items.size by omega, Id.run]
        · exact hs
      · simpa only [Array.toList_push, List.reverse_append, List.reverse_singleton,
          List.append_assoc] using hchars

private theorem kpBack_chain (items : Array Item) (best : Array (Option KpEntry))
    (ht : KpTable items items.size best) (j : Nat) (hj : j < items.size)
    (hr : ((best.getD (j) none)).isSome = true) :
    KpChain items j (kpBack items.size best j).toList := by
  obtain ⟨breaks, chain, trace⟩ := kpBack_trace items best ht j hj hr
  obtain ⟨steps, st, hsteps, hs, he⟩ := trace #[]
  have hf := Loop.forIn_range_stops_exact hs (items.size+1) (by omega)
  dsimp only [kpBack, bind, pure, Id.run]
  simp only [Id.run] at hf
  rw [hf, Array.toList_reverse, he]
  simpa using chain


private def lineStartStep (items : Array Item) (start a : Nat) : Id (ForInStep Nat) :=
  match items[a]? with
  | some (.glue g) | some (.decoratedGlue g _) =>
    if start == 0 && !g.word && !g.parfill then .done a else .yield (a+1)
  | some (.pen _ cost _ _ _ _) =>
    if cost ≥ 10000 then .done a else .yield (a+1)
  | _ => .done a

private theorem lineStart_loop (items : Array Item) (start : Nat) :
    lineStart items start =
      (forIn [start:items.size] start (fun _ => lineStartStep items start) : Id Nat).run := by
  rfl

private theorem lineStart_skip (items : Array Item) (start : Nat) (hs : start ≤ items.size) :
    start ≤ lineStart items start ∧ lineStart items start ≤ items.size ∧
      ∀ k, start ≤ k → k < lineStart items start → (items.getD k default).boxChars = [] := by
  rw [lineStart_loop]
  apply Loop.forIn_range_inv
    (fun a => start ≤ a ∧ a ≤ items.size ∧
      ∀ k, start ≤ k → k < a → (items.getD k default).boxChars = [])
  · exact ⟨Nat.le_refl _, hs, fun _ _ h => by omega⟩
  · intro _ _ _ a ha
    have next (it : Item) (hi : items[a]? = some it) (hc : it.boxChars = []) :
        start ≤ a+1 ∧ a+1 ≤ items.size ∧
          ∀ k, start ≤ k → k < a+1 → (items.getD k default).boxChars = [] := by
      have hb : a < items.size := (Array.getElem?_eq_some_iff.mp hi).1
      refine ⟨by omega, by omega, ?_⟩
      intro k hk hka
      by_cases h : k < a
      · exact ha.2.2 k hk h
      · have he : k = a := by omega
        subst k
        simpa only [Array.getD_eq_getD_getElem?, hi, Option.getD_some] using hc
    unfold lineStartStep
    split
    · rename_i g hi
      split
      · exact ha
      · exact next _ hi rfl
    · rename_i g ds hi
      split
      · exact ha
      · exact next _ hi rfl
    · rename_i w cost flagged fi color glyphs hi
      split
      · exact ha
      · exact next _ hi rfl
    · exact ha

private def itemSpan (items : Array Item) (a b : Nat) : List Char :=
  (List.range' a (b-a)).flatMap (fun k => (items.getD k default).boxChars)

private theorem itemSpan_self (items : Array Item) (a : Nat) :
    itemSpan items a a = [] := by simp [itemSpan]

private theorem itemSpan_append (items : Array Item) (a b c : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) :
    itemSpan items a c = itemSpan items a b ++ itemSpan items b c := by
  unfold itemSpan
  have hc : c-a = (b-a)+(c-b) := by omega
  rw [hc, ← List.range'_append_1]
  have he : a+(b-a) = b := by omega
  simp only [he, List.flatMap_append]

private theorem itemSpan_nil (items : Array Item) (a b : Nat)
    (h : ∀ k, a ≤ k → k < b → (items.getD k default).boxChars = []) :
    itemSpan items a b = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro k hk
  have hm := List.mem_range'_1.mp hk
  exact h k hm.1 (by omega)

private theorem itemSpan_lineStart (items : Array Item) (a b : Nat)
    (ha : a ≤ items.size) (hab : lineStart items a ≤ b) :
    itemSpan items a b = itemSpan items (lineStart items a) b := by
  obtain ⟨hla, _, hc⟩ := lineStart_skip items a ha
  rw [itemSpan_append items a (lineStart items a) b hla hab,
    itemSpan_nil items a (lineStart items a) hc, List.nil_append]

private theorem canBreakAt_boxChars (items : Array Item) (j : Nat)
    (hb : canBreakAt items j = true) :
    (items.getD j default).boxChars = [] := by
  unfold canBreakAt at hb
  split at hb
  · rename_i g he
    simp only [Array.getD_eq_getD_getElem?, he, Option.getD_some, Item.boxChars]
  · rename_i g d he
    simp only [Array.getD_eq_getD_getElem?, he, Option.getD_some, Item.boxChars]
  · rename_i w cost flag fi col gs he
    simp only [Array.getD_eq_getD_getElem?, he, Option.getD_some, Item.boxChars]
  · contradiction

private theorem itemSpan_break (items : Array Item) (a j : Nat)
    (ha : a ≤ j) (hb : canBreakAt items j = true) :
    itemSpan items a (j+1) = itemSpan items a j := by
  rw [itemSpan_append items a j (j+1) ha (by omega)]
  simp only [itemSpan, Nat.add_sub_cancel_left, List.range'_one, List.flatMap_cons,
    List.flatMap_nil, canBreakAt_boxChars items j hb, List.append_nil]

private theorem itemSpan_all (items : Array Item) :
    itemSpan items 0 items.size = items.toList.flatMap Item.boxChars := by
  have he : (List.range' 0 items.size).map (fun k => items.getD k default) = items.toList := by
    apply List.ext_getElem
    · simp
    · intro k hk hk'
      have h : k < items.size := by simpa using hk'
      simp [List.getElem_range', Array.getD, h]
  simpa only [itemSpan, Nat.sub_zero, List.flatMap_map, Function.comp_def] using
    congrArg (List.flatMap Item.boxChars) he

private theorem range_yields_progress {β : Type} (P : Nat → β → Prop)
    (f : Nat → β → Id (ForInStep β)) (lo len : Nat) (init : β) (h0 : P lo init)
    (step : ∀ i, lo ≤ i → i < lo+len → ∀ b, P i b →
      ∃ c, (f i b).run = .yield c ∧ P (i+1) c) :
    P (lo+len) (forIn (List.range' lo len) init f : Id β).run := by
  induction len generalizing lo init with
  | zero => simpa using h0
  | succ len ih =>
    obtain ⟨c, hc, hp⟩ := step lo (by omega) (by omega) init h0
    simp only [Id.run] at hc
    simp only [List.range'_succ, List.forIn_cons, bind, Id.run, hc]
    have h := ih (lo+1) c hp (fun i hl hi b hb => step i (by omega) (by omega) b hb)
    simpa only [Nat.add_assoc, Nat.add_comm 1 len, Id.run] using h

private theorem kpSums_forced_zero (items : Array Item)
    (hf : ∀ k, k+1 < items.size → isForced items k = false) :
    (kpSums items).forced.size = items.size+1 ∧
      ∀ j, j < items.size → ((kpSums items).forced.getD j 0) = 0 := by
  let P := fun t (st : Array Sp × Array Sp × Array Sp × Array Nat × Array Nat × Array Sp × Sp) =>
    st.2.2.2.2.1.size = t+1 ∧ ∀ j, j < st.2.2.2.2.1.size → j < items.size →
      (st.2.2.2.2.1.getD j 0) = 0
  unfold kpSums
  simp only [Array.getElem!_eq_getD]
  apply Loop.bind_of_inv
    (P := P items.size)
    (Q := fun sums : KpSums => sums.forced.size = items.size+1 ∧
      ∀ j, j < items.size → (sums.forced.getD (j) 0) = 0)
  · rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply (fun st (h : P (0+items.size) st) =>
      (show P items.size st from by simpa only [Nat.zero_add] using h))
    apply range_yields_progress P
    · simp [P]
    · intro i _ hi st hp
      rcases st with ⟨pw, ps, pk, pf, pforced, pb, btot⟩
      have hs : pforced.size = i+1 := hp.1
      have next : (pforced.push ((pforced.getD i 0) + if isForced items i then 1 else 0)).size = i+1+1 ∧
          ∀ j, j < (pforced.push ((pforced.getD i 0) + if isForced items i then 1 else 0)).size →
            j < items.size →
            (pforced.push ((pforced.getD i 0) + if isForced items i then 1 else 0)).getD j 0 = 0 := by
        refine ⟨by simp [hs], ?_⟩
        intro j hj hjn
        by_cases h : j < pforced.size
        · simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt h,
            Array.getElem?_eq_getElem h, Option.getD_some] using hp.2 j h hjn
        · have he : j = pforced.size := by simp only [Array.size_push] at hj; omega
          subst j
          have hz := hp.2 i (by dsimp only at *; omega) (by omega)
          have hforced := hf i (by omega)
          simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]
          simp only [Array.getD_eq_getD_getElem?] at hz
          simp only [hz, hforced, Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ⟨_, rfl, next⟩
  · intro st hst
    exact ⟨hst.1, fun j hj => hst.2 j (by rw [hst.1]; omega) hj⟩


/-- Ordered glyph intervals as paragraph placement consumes them. -/
private def breakSpans (items : Array Item) (breaks : List Nat) : List Char × Nat :=
  breaks.foldl (fun st j => (st.1 ++ itemSpan items (kpStart items st.2) j, j))
    ([], items.size)

private theorem KpChain.spans {items : Array Item} {last : Nat} {breaks : List Nat}
    (h : KpChain items last breaks) :
    breakSpans items breaks = (itemSpan items 0 (last+1), last) := by
  induction h with
  | @first j hj hb ha =>
    have ha' : lineStart items 0 ≤ j := by simpa [kpStart] using ha
    simp only [breakSpans, List.foldl_cons, List.foldl_nil, List.nil_append]
    rw [itemSpan_break items 0 j (by omega) hb,
      itemSpan_lineStart items 0 j (by omega) ha']
    simp [kpStart]
  | @next p j bs chain hpj hj hb ha ih =>
    have hp : p < items.size := by omega
    have ha' : lineStart items (p+1) ≤ j := by simpa [kpStart, Nat.ne_of_lt hp] using ha
    change List.foldl _ _ (bs ++ [j]) = _
    rw [List.foldl_append]
    change ((breakSpans items bs).1 ++
      itemSpan items (kpStart items (breakSpans items bs).2) j, j) = _
    rw [ih]
    dsimp only
    rw [itemSpan_break items 0 j (by omega) hb,
      itemSpan_append items 0 (p+1) j (by omega) (by omega),
      itemSpan_lineStart items (p+1) j (by omega) ha']
    simp [kpStart, Nat.ne_of_lt hp]


/-- Optimal breakpoints by dynamic programming over break
positions, with prefix-sum line measures and an active list. -/
public def kp (items : Array Item) (target : Sp) (protrude : Bool := false)
    (expand : Bool := false) (bg : Sp := 0) (fil : Bool := false) (runt : Bool := false) :
    Array Nat :=
  let sums := { kpSums items with bg := bg }
  let slack : Sp := if protrude then maxProtrudeRight items else 0
  let st := kpForward items sums target slack protrude expand fil runt items.size
  match (st.best.getD (items.size-1) none) with
  | none => #[]
  | some _ => kpBack items.size st.best (items.size-1)

private theorem kp_boxChars (items : Array Item) (target : Sp) (protrude expand : Bool)
    (bg : Sp) (fil : Bool) {runt : Bool}
    (hn : 0 < items.size) (hb : canBreakAt items (items.size-1) = true)
    (hf : ∀ k, k+1 < items.size → isForced items k = false) :
    (breakSpans items (kp items target protrude expand bg fil runt).toList).1 =
      items.toList.flatMap Item.boxChars := by
  let sums := { kpSums items with bg := bg }
  let slack : Sp := if protrude then maxProtrudeRight items else 0
  let st := kpForward items sums target slack protrude expand fil runt items.size
  have ht := (kpForward_valid items sums target slack protrude expand fil (runt := runt) items.size
    (Nat.le_refl _)).1
  have hz : ∀ a j, a < j → j < items.size → (sums.forced.getD (j) 0) - (sums.forced.getD (a) 0) = 0 := by
    intro a j haj hj
    rw [(kpSums_forced_zero items hf).2 j hj,
      (kpSums_forced_zero items hf).2 a (by omega)]
  change (breakSpans items (match (st.best.getD (items.size-1) none) with
    | none => #[] | some _ => kpBack items.size st.best (items.size-1)).toList).1 = _
  cases he : (st.best.getD (items.size-1) none) with
  | none =>
    have hg : ¬ kpStart items items.size < items.size := by
      intro hg
      have h := kpForward_last items sums target slack protrude expand fil (runt := runt) hn hb hz hg
      change ((st.best.getD (items.size-1) none)).isSome = true at h
      rw [he] at h
      contradiction
    have hs := lineStart_skip items 0 (Nat.zero_le _)
    have hstart : lineStart items 0 = items.size := by
      simp only [kpStart, beq_self_eq_true, ite_true] at hg
      omega
    have hc : itemSpan items 0 items.size = [] := by
      apply itemSpan_nil
      intro k hk hkn
      exact hs.2.2 k hk (by omega)
    simp only [breakSpans, List.foldl_nil, ← itemSpan_all, hc]
  | some e =>
    have chain := kpBack_chain items st.best ht (items.size-1) (by omega)
      (by rw [he]; rfl)
    rw [chain.spans]
    simpa only [Nat.sub_add_cancel hn] using itemSpan_all items

/-- TeX's `\pretolerance` (plain.tex sets 100). -/
public def pretolerance : Nat := 100

/-- Two-pass breaking as TeX's: a hyphenless pass whose breaks stand
when every line is within `pretolerance`, else the hyphenating pass. -/
public def kpTwoPass (items : Array Item) (target : Sp) (protrude : Bool := false)
    (expand : Bool := false) (bg : Sp := 0) (fil : Bool := false) (runt : Bool := false) :
    Array Nat := Id.run do
  let sealable : Item → Bool := fun it => match it with
    | .pen _ cost flagged _ _ _ => flagged && forcedCost < cost && cost < 10000
    | .box .. | .glue .. | .decoratedGlue .. | .img .. | .rule .. | .poly .. => false
  if !items.any sealable then return kp items target protrude expand bg fil runt
  let plain := items.map fun it => match it with
    | .pen w cost flagged f c g =>
      if flagged && forcedCost < cost && cost < 10000 then .pen w 10000 flagged f c g
      else .pen w cost flagged f c g
    | .box .. | .glue .. | .decoratedGlue .. | .img .. | .rule .. | .poly .. => it
  let breaks := kp plain target protrude expand bg fil runt
  if breaks.isEmpty then return kp items target protrude expand bg fil runt
  let mut prev := plain.size
  for j in breaks do
    let a := lineStart plain (if prev == plain.size then 0 else prev + 1)
    let m := measure plain a j protrude
    let ex := m.ex expand
    let delta := target - m.natural
    let bad : Int :=
      if delta == 0 then 0
      else if delta > 0 then (if m.fil || fil then 0 else badness delta (m.stretch + bg + ex))
      else if m.shrink + ex < -delta then (pretolerance : Int) + 1
      else badness delta (m.shrink + ex)
    if bad > (pretolerance : Int) then
      return kp items target protrude expand bg fil runt
    prev := j
  return breaks

/-- The uniform expansion factor a set line applies to its font boxes, in per
mille: fonts absorb the line's delta up to `expandLimit`, glue the rest. -/
public def expandFactor (delta boxW : Int) : Int :=
  if boxW > 0 && delta != 0 then
    min (max (delta * 1000 / boxW) (-(expandLimit : Int))) (expandLimit : Int)
  else 0

public theorem expandFactor_bounded (delta boxW : Int) :
    -(expandLimit : Int) ≤ expandFactor delta boxW ∧
      expandFactor delta boxW ≤ (expandLimit : Int) := by
  unfold expandFactor expandLimit
  split <;> omega

/-- A font box's coordinate under the line's per-mille expansion. -/
private def expandCoord (f x : Int) : Int := x + x * f / 1000

/-- Expansion of a fragment measured from its original shaping origin. -/
public def expandSpan (f offset width : Int) : Int :=
  expandCoord f (offset + width) - expandCoord f offset

public theorem expandSpan_add_exact (f offset a b : Int) :
    expandSpan f offset a + expandSpan f (offset + a) b =
      expandSpan f offset (a + b) := by
  unfold expandSpan
  simp only [Int.add_assoc]
  omega

/-- Set a word's box, split only where local rounding
would differ from the original shaping origin. -/
private def setWordBox (segs : Array Seg) (f offset w : Sp)
    (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (glyphs : Array (Nat × Char × Sp)) (size : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution) : Array Seg := Id.run do
  let width := expandSpan f offset w
  if f == 0 || offset == 0 || glyphs.isEmpty then
    return segs.push
      (.run fontIdx color link width glyphs size leading decorations raise ground attr)
  let mut segs := segs
  let mut run := #[]
  let mut dx := 0
  let mut startDx := 0
  let mut startX := 0
  for g in glyphs do
    let x := expandCoord f (offset + dx) - expandCoord f offset
    if !run.isEmpty && startX + expandCoord f (dx - startDx) != x then
      segs := segs.push
        (.run fontIdx color link (x - startX) run size leading decorations raise ground attr)
      run := #[]
      startDx := dx
      startX := x
    run := run.push g
    dx := dx + g.2.2
  return segs.push
    (.run fontIdx color link (width - startX) run size leading decorations raise ground attr)

private theorem setWordBox_glyphChars (segs : Array Seg) (f offset w : Sp)
    (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (glyphs : Array (Nat × Char × Sp)) (size : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution) :
    (setWordBox segs f offset w fontIdx color link glyphs size leading decorations raise ground attr).toList.flatMap
      Seg.glyphChars = segs.toList.flatMap Seg.glyphChars ++ glyphs.toList.map (·.2.1) := by
  unfold setWordBox
  dsimp only
  split
  · simp [Seg.glyphChars]
  · apply Loop.bind_of_inv
      (P := fun st : Array Seg × Array (Nat × Char × Sp) × Sp × Sp × Sp =>
        st.1.toList.flatMap Seg.glyphChars ++ st.2.1.toList.map (·.2.1) =
          segs.toList.flatMap Seg.glyphChars ++ glyphs.toList.map (·.2.1))
      (Q := fun out : Array Seg => out.toList.flatMap Seg.glyphChars =
        segs.toList.flatMap Seg.glyphChars ++ glyphs.toList.map (·.2.1))
    · simpa only [Array.toList_empty, List.map_nil, List.append_nil,
        ← List.map_eq_flatMap] using
        scalarLoop_array_census
          (fun st : Array Seg × Array (Nat × Char × Sp) × Sp × Sp × Sp =>
            st.1.toList.flatMap Seg.glyphChars ++ st.2.1.toList.map (·.2.1))
          (fun g : Nat × Char × Sp => [g.2.1]) _ glyphs (segs, #[], 0, 0, 0)
          (by
            intro g _ st
            rcases st with ⟨ss, run, dx, startDx, startX⟩
            dsimp only
            split <;> refine ⟨_, rfl, ?_⟩ <;> simp [Seg.glyphChars, List.append_assoc])
    · intro st hst
      simpa [Seg.glyphChars] using hst

/-- Whether a paragraph line sets to its measure: justified
text does, and so does any line carrying an author's fill. -/
private def setsToMeasure (justify : Bool) (items : Array Item) (a j : Nat) : Bool := Id.run do
  if justify then return true
  for k in [a:j] do
    match items[k]? with
    | some (.glue g) | some (.decoratedGlue g _) =>
      if g.fil && !g.parfill then return true
    | _ => pure ()
  return false

private def trimLineGaps (segs : Array Seg) (width : Sp) : Array Seg × Sp := Id.run do
  let mut segs := segs
  let mut width := width
  repeat
    match segs.back? with
    | some (.gap w _) | some (.decoratedGap w _ _) =>
      segs := segs.pop
      width := width - w
    | _ => break
  return (segs, width)

private theorem trimLineGaps_mem (segs : Array Seg) (width : Sp) :
    ∀ s ∈ (trimLineGaps segs width).1, s ∈ segs := by
  unfold trimLineGaps
  simp only [Id.run, bind, pure]
  dsimp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  dsimp only
  split
  · rename_i w word h
    intro s hs
    have hp := trimLineGaps_mem segs.pop (width - w) s hs
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hp
    exact Array.mem_of_getElem (by simpa only [Array.getElem_pop] using he)
  · rename_i w word decorations h
    intro s hs
    have hp := trimLineGaps_mem segs.pop (width - w) s hs
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hp
    exact Array.mem_of_getElem (by simpa only [Array.getElem_pop] using he)
  · intro s hs; exact hs
termination_by segs.size
decreasing_by
  all_goals
    have hn : segs.size ≠ 0 := by
      intro hz
      have he : segs = #[] := Array.eq_empty_of_size_eq_zero hz
      simp [he] at *
    simp only [Array.size_pop]
    omega

private theorem trimLineGaps_glyphChars (segs : Array Seg) (width : Sp) :
    (trimLineGaps segs width).1.toList.flatMap Seg.glyphChars =
      segs.toList.flatMap Seg.glyphChars := by
  unfold trimLineGaps
  simp only [Id.run, bind, pure]
  dsimp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  dsimp only
  split
  · rename_i w word h
    have hp := trimLineGaps_glyphChars segs.pop (width - w)
    have he := back?_pop_push segs (.gap w word) h
    have hc : segs.toList.flatMap Seg.glyphChars =
        segs.pop.toList.flatMap Seg.glyphChars := by
      exact (congrArg (fun ss : Array Seg => ss.toList.flatMap Seg.glyphChars) he).trans
        (by simp [Seg.glyphChars])
    exact hp.trans hc.symm
  · rename_i w word decorations h
    have hp := trimLineGaps_glyphChars segs.pop (width - w)
    have he := back?_pop_push segs (.decoratedGap w word decorations) h
    have hc : segs.toList.flatMap Seg.glyphChars =
        segs.pop.toList.flatMap Seg.glyphChars := by
      exact (congrArg (fun ss : Array Seg => ss.toList.flatMap Seg.glyphChars) he).trans
        (by simp [Seg.glyphChars])
    exact hp.trans hc.symm
  · rfl
termination_by segs.size
decreasing_by
  all_goals
    have hn : segs.size ≠ 0 := by
      intro hz
      have he : segs = #[] := Array.eq_empty_of_size_eq_zero hz
      simp [he] at *
    simp only [Array.size_pop]
    omega

/-- The width glue `g` sets at on a justified line whose natural width falls `delta` short of
its target (past it where negative): an equal share of `delta` on fil glue when the line has
any, else a share by stretch, or by shrink capped at the line's. -/
private def GlueSet.width (justify : Bool) (delta : Sp) (fils : Nat) (m : Measure) (g : Glue) : Sp :=
  if !justify || delta == 0 then g.width
  else if delta > 0 then
    if fils > 0 then
      if g.fil then g.width + delta / fils else g.width
    else if m.stretch > 0 then g.width + delta * g.stretch / m.stretch
    else g.width
  else if m.shrink > 0 then g.width + max delta (-m.shrink) * g.shrink / m.shrink
  else g.width

private def setLineSegments (items : Array Item) (a j : Nat) (m : Measure)
    (delta f : Sp) (justify : Bool) (fils : Nat) (wordOffsets : Std.HashMap Nat Sp) :
    Array Seg × Sp := Id.run do
  let mut segs : Array Seg := #[]
  let mut width : Sp := 0
  for k in [a:j] do
    match items[k]! with
    | .box w fontIdx color link glyphs size leading decorations raise ground attr =>
      -- The declared width is authoritative: a kern is a box with a width and no glyphs.
      let offset := wordOffsets[k]?.getD 0
      segs := setWordBox segs f offset w fontIdx color link glyphs size leading
        decorations raise ground attr
      width := width + expandSpan f offset w
    | .img idx w h ink =>
      segs := segs.push (.image idx w h ink)
      width := width + w
    | .rule w thickness raise color =>
      segs := segs.push (.rule w thickness raise color)
      width := width + w
    | .poly pts color =>
      segs := segs.push (.poly (pts.map fun (x, y) => (x + x * f / 1000, y)) color)
    | .glue g =>
      let setW := GlueSet.width justify delta fils m g
      -- Authored glue can pull as well as push; interword glue's shrink keeps it nonnegative.
      segs := segs.push (.gap setW g.word)
      width := width + setW
    | .decoratedGlue g rule =>
      let setW := GlueSet.width justify delta fils m g
      segs := segs.push (.decoratedGap setW g.word rule)
      width := width + setW
    | .pen _ _ _ _ _ _ => pure ()
  if let some (.pen w _ _ fontIdx color glyphs) := items[j]? then
    if !glyphs.isEmpty then
      let w := w + w * f / 1000
      let inherited := segs.foldl (fun acc s => match s with
        | .run _ _ _ _ _ sz ld decorations _ gr _ =>
          if sz != 0 then (sz, ld, decorations, gr) else acc
        | _ => acc)
        ((0 : Sp), ({} : RunMetrics), ({} : Decorations), (none : Option Ir.Color))
      segs := segs.push
        (.run fontIdx color none w glyphs inherited.1 inherited.2.1
          inherited.2.2.1 0 inherited.2.2.2 .hyphen)
      width := width + w
  return trimLineGaps segs width

private theorem setLineSegments_glyphChars (items : Array Item) (a j : Nat) (m : Measure)
    (delta f : Sp) (justify : Bool) (fils : Nat) (wordOffsets : Std.HashMap Nat Sp) :
    (setLineSegments items a j m delta f justify fils wordOffsets).1.toList.flatMap Seg.glyphChars =
      (List.range' a (j-a)).flatMap (fun k => (items.getD k default).boxChars) ++
      (match items[j]? with
        | some (.pen _ _ _ _ _ glyphs) => glyphs.toList.map (·.2.1)
        | _ => []) := by
  unfold setLineSegments
  dsimp only
  apply Loop.bind_of_inv
    (P := fun st : Array Seg × Sp =>
      st.1.toList.flatMap Seg.glyphChars =
        (List.range' a (j-a)).flatMap (fun k => (items.getD k default).boxChars))
    (Q := fun out : Array Seg × Sp => out.1.toList.flatMap Seg.glyphChars =
      (List.range' a (j-a)).flatMap (fun k => (items.getD k default).boxChars) ++
      (match items[j]? with
        | some (.pen _ _ _ _ _ glyphs) => glyphs.toList.map (·.2.1)
        | _ => []))
  · simpa only [Array.toList_empty, List.flatMap_nil, List.nil_append] using
      scalarLoop_range_census
        (fun st : Array Seg × Sp => st.1.toList.flatMap Seg.glyphChars)
        (fun k => (items.getD k default).boxChars) _ a j (#[], 0)
        (by
          intro k _ _ st
          rcases st with ⟨ss, w⟩
          simp only [Array.getElem!_eq_getD]
          cases hk : items.getD k default <;> dsimp only
          all_goals refine ⟨_, rfl, ?_⟩
          all_goals simp [Item.boxChars, setWordBox_glyphChars, Seg.glyphChars])
  · intro st hst
    split
    · rename_i w cost flagged fontIdx color glyphs hpen
      try simp only [hpen]
      split
      · simpa [trimLineGaps_glyphChars, Seg.glyphChars] using
          congrArg (fun cs => cs ++ glyphs.toList.map (·.2.1)) hst
      · rename_i h
        have he : glyphs = #[] := Array.isEmpty_iff.mp (by simpa using h)
        simp [trimLineGaps_glyphChars, he, hst]
    · simpa [trimLineGaps_glyphChars] using hst

private def Item.NoGlyph : Item → Prop
  | .box _ _ _ _ glyphs .. | .pen _ _ _ _ _ glyphs => glyphs = #[]
  | .glue _ | .decoratedGlue .. | .img .. | .rule .. | .poly .. => True

private def Seg.NoGlyph : Seg → Prop
  | .run _ _ _ _ glyphs .. => glyphs = #[]
  | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => True

private theorem noGlyph_getD (items : Array Item)
    (h : ∀ it ∈ items, it.NoGlyph) (k : Nat) : (items.getD k default).NoGlyph := by
  rw [← Array.getElem!_eq_getD]
  by_cases hk : k < items.size
  · simpa only [getElem!_pos items k hk] using
      h items[k] (Array.mem_of_getElem rfl)
  · simp only [getElem!_neg items k hk]
    rfl

private theorem setWordBox_noGlyph (segs : Array Seg) (f offset w : Sp)
    (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (glyphs : Array (Nat × Char × Sp)) (size : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution) (hg : glyphs = #[]) (hs : ∀ s ∈ segs, s.NoGlyph) :
    ∀ s ∈ setWordBox segs f offset w fontIdx color link glyphs size leading
      decorations raise ground attr, s.NoGlyph := by
  subst glyphs
  simp only [setWordBox, Array.isEmpty_empty, Bool.or_true, ite_true, Id.run_pure]
  intro s h
  rcases Array.mem_push.mp h with h | rfl
  · exact hs s h
  · rfl

private theorem setLineSegments_noGlyph (items : Array Item) (a j : Nat) (m : Measure)
    (delta f : Sp) (justify : Bool) (fils : Nat) (wordOffsets : Std.HashMap Nat Sp)
    (h : ∀ it ∈ items, it.NoGlyph) :
    ∀ s ∈ (setLineSegments items a j m delta f justify fils wordOffsets).1,
      s.NoGlyph := by
  unfold setLineSegments
  refine Loop.bind_of_inv (P := fun st : Array Seg × Sp => ∀ s ∈ st.1, s.NoGlyph)
    (Q := fun st : Array Seg × Sp => ∀ s ∈ st.1, s.NoGlyph) _ _ ?_ ?_
  · apply Loop.forIn_range_inv
      (P := fun st : Array Seg × Sp => ∀ s ∈ st.1, s.NoGlyph)
    · simp
    · intro k _ _ st hs
      have hi := noGlyph_getD items h k
      rw [← Array.getElem!_eq_getD] at hi
      cases he : items[k]! <;> simp only [he] at hi ⊢
      · exact setWordBox_noGlyph _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi hs
      all_goals
        first
        | exact hs
        | (intro s hh
           rcases Array.mem_push.mp hh with hh | rfl
           · exact hs s hh
           · trivial)
  · intro st hs
    have ht : ∀ s ∈ (trimLineGaps st.1 st.2).1, s.NoGlyph :=
      fun s hh => hs s (trimLineGaps_mem _ _ s hh)
    dsimp only
    split
    · rename_i w cost flagged fontIdx color glyphs he
      have hg : glyphs = #[] := h _ (Array.mem_of_getElem? he)
      simp only [hg, Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ite_false]
      exact ht
    · exact ht

private structure LineSetting where
  measured : Measure
  delta : Sp
  factor : Int
  fils : Nat
  overfull : Bool
  hang : Sp

private def lineSetting (items : Array Item) (a j : Nat) (target : Sp)
    (justify protrude expand : Bool) (wordOffsets : Std.HashMap Nat Sp) :
    LineSetting := Id.run do
  let m := measure items a j
  -- Protrusion: the line sets against the enlarged target; the caller shifts it by the hang.
  let doProt := protrude && justify && !m.fil
  let leftHang := if doProt then protrudeLeft items a j else 0
  let target := target + leftHang + (if doProt then protrudeRight items a j else 0)
  let delta := target - m.natural
  let f : Int := if expand && justify && !m.fil then expandFactor delta m.boxW else 0
  let mut boxTaken : Sp := 0
  if f != 0 then
    for k in [a:j] do
      if let some (.box w _ _ _ _ _ _ _ _ _ _) := items[k]? then
        boxTaken := boxTaken + expandSpan f (wordOffsets[k]?.getD 0) w - w
    if let some (.pen w _ _ _ _ _) := items[j]? then
      boxTaken := boxTaken + w * f / 1000
  let delta := delta - boxTaken
  -- Ragged text uses none of the available shrink, so its natural width must fit without it.
  let overfull := decide ((if justify then m.shrink else 0) < -delta)
  -- Beside an author's `\hfill`, a line-running fill takes no share of the slack.
  let mut explicitFils := 0
  let mut allFils := 0
  for k in [a:j] do
    match items[k]? with
    | some (.glue g) | some (.decoratedGlue g _) =>
      if g.fil then
        allFils := allFils + 1
        unless g.parfill do explicitFils := explicitFils + 1
    | _ => pure ()
  let fils := if explicitFils > 0 then explicitFils else allFils
  return { measured := m, delta, factor := f, fils, overfull, hang := leftHang }

private def setLine (items : Array Item) (a j : Nat) (target : Sp)
    (justify : Bool) (protrude : Bool := false) (expand : Bool := false)
    (wordOffsets : Std.HashMap Nat Sp := {}) :
    Array Seg × Sp × Bool × Sp × Int :=
  let setting := lineSetting items a j target justify protrude expand wordOffsets
  let (segs, width) := setLineSegments items a j setting.measured setting.delta
    setting.factor justify setting.fils wordOffsets
  (segs, width, setting.overfull, setting.hang, setting.factor)

private theorem setLine_noGlyph (items : Array Item) (a j : Nat) (target : Sp)
    (justify protrude expand : Bool) (wordOffsets : Std.HashMap Nat Sp)
    (h : ∀ it ∈ items, it.NoGlyph) :
    ∀ s ∈ (setLine items a j target justify protrude expand wordOffsets).1,
      s.NoGlyph := by
  exact setLineSegments_noGlyph _ _ _ _ _ _ _ _ _ h

/-- One set footnote: its lines with `y` from the note block's top, and the block's total height. -/
private structure NoteBlock where
  lines : Array LineOut
  height : Sp
  /-- The last line's ink below its baseline, which a frame's note box hangs below the floor. -/
  depth : Sp := 0
  deriving Repr, Inhabited

/-- A rule's reach about its box's lines, resolved in the title's
font: `height` above the box's last baseline and `depth` below it. -/
private structure EdgeReach where
  height : Sp
  depth : Sp
  continued : Bool := false

/-- A block link, or a painted colour box whose paint reaches
`pad` beyond its lines (beamer's `beamercolorbox`). -/
private inductive RegionKind where
  | link (target : String)
  | surface (color : Ir.Color) (pad x w : Sp) (anchored : Bool)
  /-- A rule a block template sets beside a box (`Ir.BlockEdge`), painted
  `x`..`x + w` from the box's top to its last line's bottom; it spaces nothing. -/
  | edge (color : Ir.Color) (x w inset : Sp) (reach : Option EdgeReach)
  /-- Invisible overlay content on a step it does not show: what it places keeps its place and
  ships nothing. -/
  | hidden

private structure RegionStart where
  kind : RegionKind
  depth : Nat
  /-- Whether the region is hidden or opened inside a hidden one. -/
  hidden : Bool := false
  begun : Bool := false
  /-- Whether the fragment holds the region's opening. -/
  first : Bool := true
  lines : Nat
  fills : Nat
  inks : Nat

/-- The baseline a list ends on, as TeX's `\prevdepth` reads it, tied to the
element beside which it was read so shrink and distribution carry it. -/
private inductive BaseAnchor where
  | line (i : Nat) (offset : Sp)
  | ink (i : Nat) (offset : Sp)

private def BaseAnchor.read (p : PageOut) (y : Sp) : Option BaseAnchor :=
  let inkBottom (k : InkOut) : Sp := k.claims.foldl (fun m b => max m b.2.2) k.place.dy
  -- The cursor on a line's baseline stands on its last row (`LineOut.lastBase`).
  let onLine (l : LineOut) : Sp := y - l.y + (if l.y == y then l.lastBase else 0)
  match p.lines.back?, p.inks.back? with
  | some l, some k =>
    if l.y != y && l.y < inkBottom k then some (.ink (p.inks.size - 1) (y - k.place.dy))
    else some (.line (p.lines.size - 1) (onLine l))
  | some l, none => some (.line (p.lines.size - 1) (onLine l))
  | none, some k => some (.ink (p.inks.size - 1) (y - k.place.dy))
  | none, none => none

private def BaseAnchor.afterPage (a : BaseAnchor) (p : PageOut) : BaseAnchor :=
  match a with
  | .line i o => .line (p.lines.size + i) o
  | .ink i o => .ink (p.inks.size + i) o

private def BaseAnchor.y (a : BaseAnchor) (lines : Array LineOut) (inks : Array InkOut) :
    Option Sp :=
  match a with
  | .line i o => (lines[i]?).map (·.y + o)
  | .ink i o => (inks[i]?).map (·.place.dy + o)

private structure RegionSpan where
  kind : RegionKind
  depth : Nat
  hidden : Bool := false
  first : Bool
  /-- Glue inside the box after its last line, which a TeX box keeps. -/
  tail : Sp := 0
  lineStart : Nat
  lineEnd : Nat
  fillStart : Nat
  fillEnd : Nat
  inkStart : Nat
  inkEnd : Nat
  /-- The baseline its list closed on, where it closed in the flow. -/
  base : Option BaseAnchor := none

private def RegionStart.close (s : RegionStart) (p : PageOut) (tail : Sp := 0)
    (base : Option Sp := none) : RegionSpan :=
  { kind := s.kind, depth := s.depth, hidden := s.hidden, first := s.first, tail := tail
    lineStart := s.lines, lineEnd := p.lines.size
    fillStart := s.fills, fillEnd := p.fills.size
    inkStart := s.inks, inkEnd := p.inks.size
    base := base.bind (BaseAnchor.read p) }

private def RegionStart.nextPage (s : RegionStart) : RegionStart :=
  { s with lines := 0, fills := 0, inks := 0, first := false, begun := false }

private structure RegionBox where
  x0 : Sp
  y0 : Sp
  x1 : Sp
  y1 : Sp

private def addRegionBox (box : Option RegionBox) (x0 y0 x1 y1 : Sp) : Option RegionBox :=
  match box with
  | none => some { x0 := min x0 x1, y0 := min y0 y1, x1 := max x0 x1, y1 := max y0 y1 }
  | some b => some { x0 := min b.x0 (min x0 x1), y0 := min b.y0 (min y0 y1),
                     x1 := max b.x1 (max x0 x1), y1 := max b.y1 (max y0 y1) }

private def lineRegionBox (box : Option RegionBox) (l : LineOut) : Option RegionBox := Id.run do
  let mut out := box
  let mut x := l.x
  for seg in l.segs do
    match seg with
    | .run _ _ _ w glyphs size _ _ raise _ _ =>
      unless glyphs.isEmpty do
        let size := if size == 0 then l.size else size
        out := addRegionBox out x (l.y - raise - size * 4 / 5) (x + w) (l.y - raise + size / 4)
      x := x + w
    | .gap w _ | .decoratedGap w _ _ => x := x + w
    | .rule w thickness raise _ | .decoration _ w thickness raise _ =>
      out := addRegionBox out x (l.y - raise - thickness) (x + w) (l.y - raise)
      x := x + w
    | .image _ w h _ =>
      out := addRegionBox out x (l.y - h) (x + w) l.y
      x := x + w
    | .poly pts _ =>
      -- A polygon advances no pen; its vertices stand at the pen x, `py` up from the baseline.
      for (px, py) in pts do
        out := addRegionBox out (x + px) (l.y - py) (x + px) (l.y - py)
  return out

private def inkRegionBox (box : Option RegionBox) (k : InkOut) : Option RegionBox :=
  k.claims.foldl (fun box b => addRegionBox box b.1.1 b.1.2 b.2.1 b.2.2) box

private def RegionSpan.box (s : RegionSpan) (lines : Array LineOut)
    (fills : Array Fill) (inks : Array InkOut) : Option RegionBox := Id.run do
  let mut box : Option RegionBox := none
  for l in lines.extract s.lineStart s.lineEnd do
    box := match s.kind, l.regionExtent with
      | .surface .., some (above, below) | .edge .., some (above, below) =>
        addRegionBox box l.x (l.y - above) (l.x + l.setWidth) (l.y + below)
      | _, _ => lineRegionBox box l
  for f in fills.extract s.fillStart s.fillEnd do
    box := addRegionBox box f.x f.y (f.x + f.w) (f.y + f.h)
  for k in inks.extract s.inkStart s.inkEnd do
    box := inkRegionBox box k
  return box

private def RegionSpan.linkRect (s : RegionSpan) (lines : Array LineOut)
    (fills : Array Fill) (inks : Array InkOut) : Option LinkRect :=
  match s.kind with
  | .link target => (s.box lines fills inks).map fun b =>
      { x := b.x0, y := b.y0, w := max 0 (b.x1 - b.x0), h := max 0 (b.y1 - b.y0),
        target := target }
  | .surface _ _ _ _ _ | .edge .. | .hidden => none

/-- Where a rule reaching by its box's lines stands, its
top and bottom; nothing where that leaves no room. -/
public def edgeLinesSpan (firstY firstAbove lastY lastBelow height depth : Int) :
    Option (Int × Int) :=
  let top := firstY - firstAbove - lastBelow - height
  let bottom := lastY + depth
  if bottom ≤ top then none else some (top, bottom)

public theorem edgeLinesSpan_centred_exact (firstY firstAbove lastY lastBelow height depth
    lead cap e : Int) (hs : firstAbove + lastBelow = lead + e) (hr : depth - height = lead - cap)
    (top bottom : Int)
    (hf : edgeLinesSpan firstY firstAbove lastY lastBelow height depth = some (top, bottom)) :
    top + bottom = (firstY - cap) + lastY - e := by
  unfold edgeLinesSpan at hf
  dsimp only at hf
  split at hf
  · cases hf
  · simp only [Option.some.injEq, Prod.mk.injEq] at hf
    omega

/-- Where the body's part of a rule beside the whole block stands, from `height` below the
title's last baseline to `depth` below the block's; nothing where that leaves no room. -/
public def edgeLinesFrom (aboveY lastY height depth : Int) : Option (Int × Int) :=
  let top := aboveY + height
  let bottom := lastY + depth
  if bottom ≤ top then none else some (top, bottom)

public theorem edgeLinesFrom_abuts_exact (firstY firstAbove titleY titleBelow lastY height depth
    t1 b1 t2 b2 : Int)
    (h1 : edgeLinesSpan firstY firstAbove titleY titleBelow height depth = some (t1, b1))
    (h2 : edgeLinesFrom titleY lastY depth depth = some (t2, b2)) :
    b1 = t2 ∧ b2 = lastY + depth := by
  unfold edgeLinesSpan at h1
  unfold edgeLinesFrom at h2
  dsimp only at h1 h2
  split at h1
  · cases h1
  · split at h2
    · cases h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
      omega

/-- Whether the span is the body's part of a rule beside the whole block (`EdgeReach.continued`). -/
private def RegionSpan.continuesRule (s : RegionSpan) : Bool :=
  match s.kind with
  | .edge _ _ _ _ (some r) => r.continued
  | _ => false

/-- The baseline a region's list ends on: where it closed in
the flow, or its lowest line's on a page it continues past. -/
private def RegionSpan.lastBaseline (s : RegionSpan) (lines : Array LineOut)
    (inks : Array InkOut) : Option Sp :=
  match s.base with
  | some a => a.y lines inks
  | none => (lines.extract s.lineStart s.lineEnd).foldl
      (fun m (l : LineOut) => some (max (m.getD l.y) l.y)) none

/-- The region's fill, read after placement: the box's lines,
its children's paint and its closing glue, `pad` beyond them. -/
private def RegionSpan.fill (s : RegionSpan) (lines : Array LineOut)
    (fills : Array Fill) (inks : Array InkOut)
    (children : Array (RegionSpan × Fill) := #[]) : Option Fill :=
  match s.kind with
  | .link _ | .hidden => none
  | .surface color pad x w anchored =>
    -- The body's part of a rule inside the box stands in a box of no size and grows it nowhere.
    let box := children.foldl (fun box (child, f) =>
      if s.depth < child.depth && !child.continuesRule &&
          s.lineStart ≤ child.lineStart && child.lineEnd ≤ s.lineEnd &&
          s.fillStart ≤ child.fillStart && child.fillEnd ≤ s.fillEnd &&
          s.inkStart ≤ child.inkStart && child.inkEnd ≤ s.inkEnd then
        addRegionBox box f.x f.y (f.x + f.w) (f.y + f.h)
      else box) (s.box lines fills inks)
    box.map fun b =>
      let y := if anchored && s.first then b.y0 else b.y0 - pad
      { x := x, y := y, w := w, h := max 0 (b.y1 + s.tail + pad - y), color := color }
  | .edge color x w _ (some r) =>
    if r.continued then
      let start : Option (Sp × Sp) :=
        if s.first && 0 < s.lineStart then (lines[s.lineStart - 1]?).map fun l => (l.y, r.height)
        else (lines.extract s.lineStart s.lineEnd)[0]?.map fun l =>
          (l.y - (l.regionExtent.getD (0, 0)).1, 0)
      match start, s.lastBaseline lines inks with
      | some (y, height), some last =>
        (edgeLinesFrom y last height r.depth).map fun (top, bottom) =>
          { x := x, y := top, w := w, h := bottom - top, color := color }
      | _, _ => none
    else
    let lines := lines.extract s.lineStart s.lineEnd
    match lines[0]?, lines.back? with
    | some first, some last =>
      (edgeLinesSpan first.y (first.regionExtent.getD (0, 0)).1 last.y
          (last.regionExtent.getD (0, 0)).2 r.height r.depth).map fun (top, bottom) =>
        { x := x, y := top, w := w, h := bottom - top, color := color }
    | _, _ => none
  | .edge color x w inset none =>
    -- Another rule beside the same box stands beside it, not in it.
    let box := children.foldl (fun box (child, f) =>
      if !(child.kind matches .edge ..) && s.depth < child.depth &&
          s.lineStart ≤ child.lineStart && child.lineEnd ≤ s.lineEnd &&
          s.fillStart ≤ child.fillStart && child.fillEnd ≤ s.fillEnd &&
          s.inkStart ≤ child.inkStart && child.inkEnd ≤ s.inkEnd then
        addRegionBox box f.x f.y (f.x + f.w) (f.y + f.h)
      else box) (s.box lines fills inks)
    -- A box of no height draws its rule nowhere, as TeX's rule of no height paints nothing.
    box.bind fun b =>
      let y := if s.first then b.y0 - inset else b.y0
      let h := b.y1 + s.tail - y
      if h ≤ 0 then none else some { x := x, y := y, w := w, h := h, color := color }

/-- Measure children before their parents so every surface owns its
inset outside its children's paint; the caller paints parents first. -/
private def regionFills (spans : Array RegionSpan) (lines : Array LineOut)
    (fills : Array Fill) (inks : Array InkOut) : Array (RegionSpan × Fill) :=
  let order := spans.zipIdx.qsort fun (a, i) (b, j) =>
    b.depth < a.depth || (b.depth == a.depth && j < i)
  order.foldl (fun out (span, _) =>
    match span.fill lines fills inks out with
    | some fill => out.push (span, fill)
    | none => out) #[]

/-- Whether `s` is the body's part of the rule whose title's part is `t`. -/
private def RegionSpan.continues (s t : RegionSpan) : Bool :=
  s.depth == t.depth && t.lineEnd == s.lineStart && match s.kind, t.kind with
  | .edge c x w _ (some r), .edge c' x' w' _ (some r') =>
    r.continued && !r'.continued && c == c' && x == x' && w == w'
  | _, _ => false

/-- Join a rule's body part to the title part it continues, so the page paints one rectangle. -/
private def joinRuleParts (fills : Array (RegionSpan × Fill)) : Array (RegionSpan × Fill) :=
  fills.filterMap fun (s, f) =>
    if s.continuesRule && fills.any (fun (t, g) => s.continues t && g.y + g.h == f.y) then none
    else match fills.find? (fun (b, g) => b.continues s && f.y + f.h == g.y) with
      | some (_, g) => some (s, { f with h := g.y + g.h - f.y })
      | none => some (s, f)

/-- The lowest y body ink may reach on a page carrying `h` of note ink: the
note block and the `\skip\footins` gap, less `hang`, come out of `bottom`. -/
private def noteFloor (bottom footins h : Sp) (hang : Sp := 0) : Sp :=
  if h == 0 then bottom else bottom + hang - h - footins


/-- A display's placement where its first line is set: TeX's two skips above it (tex.web
§1203), whether amsmath's `$$` sets an empty line first, and where it stands. -/
private structure DisplayJob where
  ctx : Ir.DisplayCtx
  above : Glue
  aboveShort : Glue
  emptyLine : Bool
  lead : Nat := 0
  deriving Inhabited

/-- The preceding band's spacing reference: a text
baseline, a rule's ink edge, or a box's painted extent. -/
public inductive Spacing.Band where
  | text
  | rule
  | box
  deriving Inhabited, Repr, DecidableEq

/-- A column's final baseline and the lower bounds spacing
reads: clearance, leading and measured box depth. -/
public structure Spacing.Tail where
  y : Sp
  depth : Sp
  below : Sp
  boxDepth : Sp
  band : Spacing.Band

/-- The common tail of neighbouring columns; a mixed row is
a box, whose next rule clears its full painted depth. -/
public def Spacing.Tail.join (a b : Spacing.Tail) : Spacing.Tail :=
  let y := max a.y b.y
  { y := y
    depth := max (a.y + a.depth) (b.y + b.depth) - y
    below := max (a.y + a.below) (b.y + b.below) - y
    boxDepth := max (a.y + a.boxDepth) (b.y + b.boxDepth) - y
    band := if a.band = b.band then a.band else .box }

public theorem Spacing.Tail.join_covers (a b : Spacing.Tail) :
    a.y + a.depth ≤ (a.join b).y + (a.join b).depth ∧
    b.y + b.depth ≤ (a.join b).y + (a.join b).depth ∧
    a.y + a.below ≤ (a.join b).y + (a.join b).below ∧
    b.y + b.below ≤ (a.join b).y + (a.join b).below ∧
    a.y + a.boxDepth ≤ (a.join b).y + (a.join b).boxDepth ∧
    b.y + b.boxDepth ≤ (a.join b).y + (a.join b).boxDepth := by
  simp only [Spacing.Tail.join, Sp]
  omega

public theorem Spacing.Tail.join_boxDepth_exact (a b : Spacing.Tail) :
    (a.join b).y + (a.join b).boxDepth =
      max (a.y + a.boxDepth) (b.y + b.boxDepth) := by
  simp only [Spacing.Tail.join, Sp]
  omega

public theorem Spacing.Tail.join_box_exact (a b : Spacing.Tail)
    (h : a.band = .box ∨ b.band = .box) :
    (a.join b).band = .box := by
  simp only [Spacing.Tail.join]
  split
  · rcases h with h | h
    · exact h
    · rename_i he
      exact he.trans h
  · rfl

public theorem Spacing.Tail.join_comm (a b : Spacing.Tail) :
    a.join b = b.join a := by
  simp only [Spacing.Tail.join]
  congr 1
  · simp only [Sp]; omega
  · simp only [Sp]; omega
  · simp only [Sp]; omega
  · simp only [Sp]; omega
  · split <;> split <;> simp_all

public theorem Spacing.Tail.join_id (a : Spacing.Tail) : a.join a = a := by
  cases a
  simp only [Spacing.Tail.join, ↓reduceIte]
  congr 1 <;> simp only [Sp] <;> omega

public theorem Spacing.Tail.join_assoc (a b c : Spacing.Tail) :
    (a.join b).join c = a.join (b.join c) := by
  rcases a with ⟨ay, ad, al, ai, ab⟩
  rcases b with ⟨byy, bd, bl, bi, bb⟩
  rcases c with ⟨cy, cd, cl, ci, cb⟩
  simp only [Spacing.Tail.join]
  congr 1
  · simp only [Sp]; omega
  · simp only [Sp]; omega
  · simp only [Sp]; omega
  · simp only [Sp]; omega
  · cases ab <;> cases bb <;> cases cb <;> decide

/-- Repeated furniture and the spacing reference below it. -/
private structure Spacing.Chrome where
  lines : Array LineOut
  fills : Array Fill
  y : Sp
  depth : Sp
  below : Sp
  band : Spacing.Band
  header : Option Sp

/-- Page assembly state, set as a line is: lines are boxes,
skips are glue, and `y` is the last baseline at natural glue. -/
public structure Spacing.Page where
  private mk ::
  private geom : Geom
  private ascent : Sp
  private descent : Sp
  /-- Body cap height in sp, a line's height as TeX measures it from its glyphs. -/
  private capHeight : Sp
  /-- Body x-height in sp, so `ex` tokens resolve against the real font. -/
  private xHeight : Sp := 0
  /-- Authored picture openings keyed by the PDF structure leaf. -/
  private pictureSpans : Array (Nat × Span) := #[]
  private pages : Array PageOut := #[]
  private cur : PageOut := {}
  /-- Page-local lifecycle declarations, recorded and advanced once by `finishPage`. -/
  private pageState : Ir.PageState := {}
  /-- Baseline of the last line placed, at natural glue. -/
  private y : Sp := 0
  /-- Ink depth of the last line placed (metric descent per run). -/
  private prevDepth : Sp := 0
  /-- The last set line's depth as TeX's box has it, keyed by the baseline
  and `prevDepth` it was committed with (`Spacing.Page.boxDepth`). -/
  private lastInk : Option (Sp × Sp × Sp) := none
  /-- Leaded below of the last line placed (`LineBox.below`). -/
  private prevBelow : Sp := 0
  /-- The preceding band's spacing reference, surviving column and slot restoration. -/
  private prevBand : Spacing.Band := .text
  /-- Where the last text line's content ends, from the left margin:
  TeX's `\predisplaysize` (tex.web §1146); `none` after anything else. -/
  private lineEnd : Option Sp := none
  /-- The band at `y` is display math, so the next interline glue is TeX's (`texBaselineGap`). -/
  private texAfter : Bool := false
  /-- The band at `y` is a frame content's opening `\vbox{}`, so the
  next text line's interline glue is TeX's from a box of depth zero. -/
  private opening : Bool := false
  /-- The last display set took TeX's short skips (`Op.skipAlt`). -/
  private dispShort : Bool := false
  /-- Vertical glue since the last line, not yet laid. -/
  private skip : Glue := {}
  /-- Per line of the current page: total shrink in the glue above it. -/
  private shrinkAbove : Array Sp := #[]
  /-- Per fill and path: the shrink of the glue preceding it. -/
  private fillShrinkAbove : Array Sp := #[]
  private inkShrinkAbove : Array Sp := #[]
  private fillStretchAbove : Array Sp := #[]
  private inkStretchAbove : Array Sp := #[]
  private fillFilsAbove : Array Nat := #[]
  private inkFilsAbove : Array Nat := #[]
  /-- Total shrink in the glue laid on the current page. -/
  private pageShrink : Sp := 0
  /-- Per line of the current page: total finite stretch in
  the glue above it, which a `\flushbottom` page spends. -/
  private stretchAbove : Array Sp := #[]
  /-- Total finite stretch in the glue laid on the current page. -/
  private pageStretch : Sp := 0
  /-- How far the current page overflows at natural glue. -/
  private needed : Sp := 0
  /-- The box that last strictly increased `needed`. -/
  private neededSource : Option Span := none
  /-- Source of the line awaiting the fit and commit door. -/
  private pendingSource : Option Span := none
  /-- Source at the current cursor, saved and restored with column boxes. -/
  private lastSource : Option Span := none
  /-- The next line opens at the page top though lines already
  stand there: a later column rewound to a fresh page's start. -/
  private freshStart : Bool := false
  /-- `\vspace*`'s zero rule stands on the page with no box below it
  yet, so the glue after it stays and `\topskip` stands above it. -/
  private anchored : Bool := false
  /-- `\nointerlineskip` stands before the next box, which takes no interline glue. -/
  private ignoreDepth : Bool := false
  /-- The extra space the first box below an anchor takes when it is a
  row of columns: `\lineskip`, or nothing after `\nointerlineskip`. -/
  private colAnchor : Option Sp := none
  /-- A float group is being replayed on the page that holds it whole
  (`runFloat`): a line that does not fit commits instead of breaking. -/
  private noBreak : Bool := false
  /-- Background of the page being built, from `.pageStyle`. -/
  private pageBg : Option Ir.Color := none
  /-- Persistent background from the current palette; `.pageGround` replaces it even with `none`. -/
  private docBg : Option Ir.Color := none
  /-- How the page being built distributes its leftover vertical space. -/
  private vdist : VDist := .top
  /-- Fil units seen on this page so far, which own the leftover when any exist (`filShare`). -/
  private pageFils : Nat := 0
  /-- Per placed line, the fil units above it — parallel to `shrinkAbove`. -/
  private filsAbove : Array Nat := #[]
  /-- The chrome footer for pages closed from this frame opening. -/
  private curFoot : Option (Array Ir.BandSlot) := none
  private curFootLook : Option Ir.TitledLook := none
  /-- The bottom edge of the open page's `.titleBar` fill, for `PageOut.band`. -/
  private curBand : Option Sp := none
  /-- The displayed counter of the frame opened by `.frameOpen`. -/
  private curFrame : Option Nat := none
  /-- The label of the frame opened by `.frameOpen` (`FrameOpening.label`). -/
  private curFrameLabel : Option String := none
  /-- The source frame and overlay opened by `.frameOpen`. -/
  private curFrameOrigin : Option FrameOrigin := none
  /-- The footline band's box for pages closed from here on, the one
  value the text-area floor and the band's baseline both read. -/
  private footBox : Option (Sp × Sp) := none
  /-- The text area of the open frame (`FrameOpening.area`),
  from its `.frameOpen` to its `.frameClose`. -/
  private frameArea : FrameArea := .margins
  /-- The declared gap between the footline's ink and the
  text area, else beamer's 4 pt (`Ir.footline.sep`). -/
  private footGap : Sp := Ir.footline.sep
  /-- A frame opened its body on this page (`openBody`), so
  the next band is spaced as below a box of depth zero. -/
  private opened : Bool := false
  /-- Inside a frame, whether the author declared `[allowframebreaks]`; `none` outside a frame. -/
  private frameBreak : Option Bool := none
  /-- Opening environment of the current logical frame. -/
  private frameSource : Option Span := none
  /-- The open frame has already been reported once (W0384). -/
  private spillWarned : Bool := false
  /-- The overflow ladder's records (`Out.overruns`), per overlay step of a frame it marked. -/
  private overruns : Array (FrameOrigin × Sp × Sp) := #[]
  private needs : Array (FrameOrigin × Sp) := #[]
  private spilled : Array FrameOrigin := #[]
  /-- The open frame's overflow policy (`FrameOpening.fit`). -/
  private curFit : FrameFitMode := .spill
  /-- Lines and fills on the page when `.pin` arrived:
  page-top chrome the distribution never moves. -/
  private pinnedLines : Nat := 0
  private pinnedFills : Nat := 0
  private pinnedInks : Nat := 0
  /-- The frame's page-top chrome, snapshotted at `.pin` and repeated on every
  continuation page (`spillPage`), as beamer repeats a broken frame's title. -/
  private chrome : Option Spacing.Chrome := none
  /-- Block links open on the current page. -/
  private openRegions : Array RegionStart := #[]
  private closedRegions : Array RegionSpan := #[]
  /-- Anchors owed to the next committed line. -/
  private pendingAnchors : Array String := #[]
  /-- The resolved `\skip\footins` gap for this run. -/
  private footins : Sp := 0
  /-- The footnote rule's ink colour: the design's `fg`. -/
  private noteInk : Ir.Color := Ir.Color.black
  /-- The last pending note's ink below its last baseline (`NoteBlock.depth`). -/
  private notesDepth : Sp := 0
  /-- Footnote lines committed to the open page, y relative to the
  note block's top; a note enters only through `attachNotes`. -/
  private pendingNotes : Array LineOut := #[]
  /-- Total height of the pending note block, which the
  fit test in `placeLine` reserves above `bodyBottom`. -/
  private notesH : Sp := 0
  private diags : Array Diag := #[]
  private paragraphBreaks : Array ParagraphBreaks := #[]

private abbrev B := Spacing.Page

/-- Insets belong to the enclosing regions, not to a
line's font; a fresh fragment owes its top inset once. -/
private def Spacing.Page.surfaceTop (b : B) : Sp :=
  b.openRegions.foldl (fun total s => match s.kind with
    | .surface _ pad _ _ _ => total + if s.begun then 0 else pad
    | .link _ | .edge .. | .hidden => total) 0

private def Spacing.Page.surfaceBottom (b : B) : Sp :=
  b.openRegions.foldl (fun total s => match s.kind with
    | .surface _ pad _ _ _ => total + pad
    | .link _ | .edge .. | .hidden => total) 0

/-- The floor of the text area on the page being built: beamer's `\footheight` floor in its
text area or above a footline, the paper's edge on a plain frame, else `Geom.bodyBottom`. -/
private def Spacing.Page.bottom (b : B) : Sp :=
  match b.frameArea with
  | .text => frameFloor b.geom.pageH b.footGap b.footBox
  | .paper => b.geom.pageH
  | .margins => match b.footBox with
    | some (h, d) => footFloor b.geom.pageH b.footGap h d
    | none => b.geom.bodyBottom

/-- The gap above a page's note block: LaTeX's `\skip\footins`,
none in beamer's text area (beamerbaseframesize.sty). -/
private def Spacing.Page.noteGap (b : B) : Sp :=
  if b.frameArea == .margins then b.footins else 0

/-- How far a page's note block hangs below its floor: nothing
on LaTeX's page, the notes' last depth in beamer's text area. -/
private def Spacing.Page.noteHang (b : B) (depth : Option Sp := none) : Sp :=
  if b.frameArea == .margins then 0 else depth.getD b.notesDepth

/-- Nothing stands on the page that the next band must be spaced below. -/
private def Spacing.Page.fresh (b : B) : Bool :=
  (b.cur.blank && !b.opened) || b.freshStart

/-- Attach a committed line's notes to the open page, each note whole. -/
private def Spacing.Page.attachNotes (b : B) (notes : Array NoteBlock) : B :=
  if notes.isEmpty then b
  else notes.foldl (fun b nb =>
    { b with pendingNotes := b.pendingNotes
               ++ nb.lines.map (fun l => { l with y := l.y + b.notesH })
             notesH := b.notesH + nb.height
             notesDepth := nb.depth }) b

/-- W0372: the note block and its mark's line reach below the floor even
on a fresh page, so the note ships whole and the page is overrun. -/
private def Spacing.Page.warnNoteOverrun (b : B) (y inkBelow : Sp) : B :=
  let over := y + inkBelow - noteFloor b.bottom b.noteGap b.notesH b.noteHang
  if b.notesH > 0 && over > 0 then
    { b with diags := b.diags.push (Diag.of .W0372
        "a footnote is taller than the text block; it overruns its page"
        (help := "shorten the note, or raise the text height (\\page{ vmargin = ... })")
        (detail := some s!"{over.toPtString}pt taller")) }
  else b

@[simp] private theorem attachNotes_pages (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).pages = b.pages := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.pages = b.pages)
      rfl (fun _ _ h => h)

@[simp] private theorem attachNotes_noBreak (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).noBreak = b.noBreak := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.noBreak = b.noBreak)
      rfl (fun _ _ h => h)

@[simp] private theorem attachNotes_cur (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).cur = b.cur := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.cur = b.cur)
      rfl (fun _ _ h => h)

private theorem attachNotes_mem (b : B) (ns : Array NoteBlock)
    (nb : NoteBlock) (hnb : nb ∈ ns) (l : LineOut) (hl : l ∈ nb.lines) :
    ∃ l' ∈ (b.attachNotes ns).pendingNotes, l'.segs = l.segs := by
  unfold Spacing.Page.attachNotes
  split
  · next hemp =>
    rw [Array.isEmpty_iff] at hemp
    subst hemp
    simp at hnb
  · obtain ⟨j, hj, hje⟩ := Array.mem_iff_getElem.mp hnb
    exact Array.foldl_induction
      (motive := fun n (acc : B) => j < n →
        ∃ l' ∈ acc.pendingNotes, l'.segs = l.segs)
      (fun h => absurd h (Nat.not_lt_zero j))
      (fun i acc ih hji => by
        rcases Nat.lt_or_ge j i.val with hlt | hge
        · obtain ⟨l', hl', hseg⟩ := ih hlt
          exact ⟨l', Array.mem_append.mpr (Or.inl hl'), hseg⟩
        · have hji' : j = i.val := Nat.le_antisymm (Nat.lt_succ_iff.mp hji) hge
          refine ⟨{ l with y := l.y + acc.notesH },
            Array.mem_append.mpr (Or.inr (Array.mem_map.mpr ⟨l, ?_, rfl⟩)), rfl⟩
          subst hji'
          exact hje ▸ hl) hj

@[simp] private theorem warnNoteOverrun_pages (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).pages = b.pages := by
  simp only [Spacing.Page.warnNoteOverrun]
  split <;> rfl

@[simp] private theorem warnNoteOverrun_noBreak (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).noBreak = b.noBreak := by
  simp only [Spacing.Page.warnNoteOverrun]
  split <;> rfl

@[simp] private theorem warnNoteOverrun_cur (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).cur = b.cur := by
  simp only [Spacing.Page.warnNoteOverrun]
  split <;> rfl

@[simp] private theorem warnNoteOverrun_pendingNotes (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).pendingNotes = b.pendingNotes := by
  simp only [Spacing.Page.warnNoteOverrun]
  split <;> rfl

/-- The note block as it ships: the footnote rule, then every pending note line, bottom-anchored
at `bodyBottom`; the rule is `\footnoterule` (ltmiscen.dtx) scaled with the body size. -/
private def Spacing.Page.noteLines (b : B) : Array LineOut :=
  if b.pendingNotes.isEmpty then #[] else
    let top := b.bottom + b.noteHang - b.notesH
    let thick := b.geom.fontSize * 4 / 100
    let ruleW := b.geom.textWidth * 2 / 5
    let rule : LineOut := { x := b.geom.hmargin
                            y := top - b.geom.fontSize * 26 / 100
                            size := 0
                            segs := #[.rule ruleW thick 0 b.noteInk]
                            setWidth := ruleW
                            note := true }
    #[rule] ++ b.pendingNotes.map (fun l => { l with y := top + l.y, note := true })

private theorem note_whole (b : B) :
    ∀ l ∈ b.pendingNotes, ∃ l' ∈ b.noteLines, l'.segs = l.segs ∧ l'.note = true := by
  intro l hl
  unfold Spacing.Page.noteLines
  split
  · next hemp =>
    rw [Array.isEmpty_iff] at hemp
    rw [hemp] at hl
    simp at hl
  · exact ⟨_, Array.mem_append.mpr (Or.inr (Array.mem_map.mpr ⟨l, hl, rfl⟩)),
      rfl, rfl⟩

/-- The depth of the band at `y` as TeX's box has it: the last set line's
deepest glyph while that line is the band, else the band's own depth. -/
private def Spacing.Page.boxDepth (b : B) : Sp :=
  match b.lastInk with
  | some (y, d, ink) => if y == b.y && d == b.prevDepth then ink else b.prevDepth
  | none => b.prevDepth

/-- Record the band just committed as a set line whose box is `ink` deep. -/
private def Spacing.Page.keepInk (b : B) (ink : Sp) : B :=
  { b with lastInk := some (b.y, b.prevDepth, ink) }

@[simp] private theorem keepInk_cur (b : B) (d : Sp) : (b.keepInk d).cur = b.cur := rfl
@[simp] private theorem keepInk_pages (b : B) (d : Sp) : (b.keepInk d).pages = b.pages := rfl
@[simp] private theorem keepInk_noBreak (b : B) (d : Sp) :
    (b.keepInk d).noBreak = b.noBreak := rfl
@[simp] private theorem keepInk_pendingNotes (b : B) (d : Sp) :
    (b.keepInk d).pendingNotes = b.pendingNotes := rfl

/-- Record what the line just set leaves the next one: `texAfter`, `dispShort` and `lineEnd`. -/
private def Spacing.Page.displayState (b : B) (tex : Bool) (lineEnd : Option Sp) : B :=
  { b with texAfter := tex, lineEnd := lineEnd }

@[simp] private theorem displayState_cur (b : B) (t : Bool) (e : Option Sp) :
    (b.displayState t e).cur = b.cur := rfl
@[simp] private theorem displayState_pages (b : B) (t : Bool) (e : Option Sp) :
    (b.displayState t e).pages = b.pages := rfl
@[simp] private theorem displayState_noBreak (b : B) (t : Bool) (e : Option Sp) :
    (b.displayState t e).noBreak = b.noBreak := rfl
@[simp] private theorem displayState_pendingNotes (b : B) (t : Bool) (e : Option Sp) :
    (b.displayState t e).pendingNotes = b.pendingNotes := rfl
@[simp] private theorem displayState_boxDepth (b : B) (t : Bool) (e : Option Sp) :
    (b.displayState t e).boxDepth = b.boxDepth := rfl

/-- TeX's choice of skip above a display (tex.web §1203), joined
to the pending glue and remembered for the skip below. -/
private def Spacing.Page.displaySkip (b : B) (dj : DisplayJob) (left size : Sp) : B :=
  let long := dj.ctx.align ||
    (if dj.ctx.inPar then (b.lineEnd.map fun e => decide (left ≤ e + 2 * size)).getD true
     else dj.emptyLine && decide (left ≤ 2 * size))
  { b with skip := b.skip.add (if long then dj.above else dj.aboveShort), dispShort := !long }

@[simp] private theorem displaySkip_pages (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).pages = b.pages := rfl
@[simp] private theorem displaySkip_noBreak (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).noBreak = b.noBreak := rfl
@[simp] private theorem displaySkip_geom (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).geom = b.geom := rfl
@[simp] private theorem displaySkip_docBg (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).docBg = b.docBg := rfl
@[simp] private theorem displaySkip_curFrameOrigin (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).curFrameOrigin = b.curFrameOrigin := rfl
@[simp] private theorem displaySkip_curFrame (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).curFrame = b.curFrame := rfl
@[simp] private theorem displaySkip_curFoot (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).curFoot = b.curFoot := rfl
@[simp] private theorem displaySkip_paragraphBreaks (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).paragraphBreaks = b.paragraphBreaks := rfl
@[simp] private theorem displaySkip_diags (b : B) (dj : DisplayJob) (l s : Sp) :
    (b.displaySkip dj l s).diags = b.diags := rfl

private theorem keepInk_boxDepth_exact (b : B) (d : Sp) : (b.keepInk d).boxDepth = d := by
  simp [Spacing.Page.keepInk, Spacing.Page.boxDepth]

/-- Where the page's content ends, the one site the vertical distribution reads:
the last box's bottom, its depth and `owed`, less the shrink the page gave. -/
private def Spacing.Page.contentEnd (b : B) (owed : Sp) : Sp :=
  b.y + (if b.geom.topskip.isSome || (b.opened && b.pinnedLines == 0) then b.boxDepth
    else b.prevDepth) + owed -
    (if b.needed > 0 && b.pageShrink > 0 then b.needed else 0)

/-- What the content keeps below its last box at a declared page boundary: the pending
glue, or on a TeX page with none, the last box's cancelled depth (latex.ltx). -/
private def Spacing.Page.closingOwed (b : B) : Sp :=
  if b.geom.topskip.isSome && b.skip.width == 0 && b.skip.stretch == 0 && !b.skip.fil
  then -b.boxDepth else b.skip.width

private theorem closingOwed_cancel_exact (b : B) (ht : b.geom.topskip.isSome = true)
    (hw : b.skip.width = 0) (hs : b.skip.stretch = 0) (hf : b.skip.fil = false) :
    b.contentEnd b.closingOwed =
      b.y - (if b.needed > 0 && b.pageShrink > 0 then b.needed else 0) := by
  simp only [Spacing.Page.contentEnd, Spacing.Page.closingOwed, ht, hw, hs, hf]
  simp
  omega

/-- The end a PDF page's distribution must clear:
its ordinary box end and any painted surface end. -/
public def regionContentEnd (ordinary : Sp) (painted : Option Sp) : Sp :=
  max ordinary (painted.getD ordinary)

public theorem regionContentEnd_none_exact (ordinary : Sp) :
    regionContentEnd ordinary none = ordinary := by
  simp [regionContentEnd]

public theorem regionContentEnd_covers (ordinary painted : Sp) :
    ordinary ≤ regionContentEnd ordinary (some painted) ∧
      painted ≤ regionContentEnd ordinary (some painted) :=
  ⟨Int.le_max_left .., Int.le_max_right ..⟩

/-- The painted surface end of the page's open and closed
fragments, measured after shrink and before distribution. -/
private def Spacing.Page.surfaceEnd (b : B) (lines : Array LineOut)
    (fills : Array Fill) (inks : Array InkOut) : Option Sp :=
  let spans := b.closedRegions ++ b.openRegions.map (fun start => start.close b.cur)
  -- The body's part of a rule beside the whole block holds no room of the page's.
  (regionFills spans lines fills inks).foldl (fun edge (s, f) =>
    if s.continuesRule then edge else some (max (edge.getD (f.y + f.h)) (f.y + f.h))) none

/-- How a frame names itself in a diagnostic: by its label, else as a frame. -/
private def frameWho (label : Option String) : String :=
  match label with
  | some l => s!"frame {l}"
  | none => "a frame"

/-- W0384: the frame is `o` taller than its page and continues
on the next; `also` adds another step's overhang. -/
public def continuedDiag (label : Option String) (span : Option Span) (o : Sp)
    (also : Option Sp := none) : Diag :=
  Diag.of .W0384
    ("a frame is taller than its page; it continues on the next page" ++
      match also with
      | some _ => ", and on another overlay step stands past its text area, in the gap below it"
      | none => "")
    (span := span)
    (help := "shorten the frame, or declare `[allowframebreaks]` on it to accept the break")
    (subject := label)
    (detail := some (s!"{frameWho label}: {o.toPtString}pt taller" ++
      match also with
      | some p => s!", {p.toPtString}pt past on another step"
      | none => ""))

/-- W0400: the frame stands `o` past its text area, in the gap below it. -/
public def overfullDiag (label : Option String) (span : Option Span) (o : Sp) : Diag :=
  Diag.of .W0400 (subject := label)
    "a frame stands past its text area, in the gap below it"
    (span := span)
    (help := "shorten the frame, or declare `[allowframebreaks]` on it to accept a break")
    (detail := some s!"{frameWho label}: {o.toPtString}pt past")

/-- The overflow ladder's account of a frame (`Ir.frameFit`): W0400 where
it stood overfull, W0384 where it continued, nothing where it fit. -/
public def fitDiag (fit : Ir.FrameFit) (label : Option String) (span : Option Span)
    (also : Option Sp := none) : Option Diag :=
  match fit with
  | .overfull o => some (overfullDiag label span o)
  | .continued o => some (continuedDiag label span o also)
  | .natural | .shrunk => none

public theorem frameFit_accounts (fit : Ir.FrameFit) (label : Option String)
    (span : Option Span) (also : Option Sp) :
    (fitDiag fit label span also).map (·.kind) =
      match fit with
      | .overfull _ => some .W0400
      | .continued _ => some .W0384
      | .natural | .shrunk => none := by
  cases fit <;> rfl

/-- Whether the open page's frame is one the overflow ladder marked (`FrameFitMode`). -/
private def Spacing.Page.ladder (b : B) : Bool :=
  b.frameBreak == some false && b.curFit != .spill

/-- The ladder's record of a marked frame step whose page could not
set it at natural glue: how far its content stood past the floor. -/
private def Spacing.Page.neededOverrun (b : B) : Array (FrameOrigin × Sp) :=
  match b.ladder, b.curFrameOrigin with
  | true, some origin =>
    if 0 < b.needed then
      match b.needs.findIdx? (·.1 == origin) with
      | some i => b.needs.modify i fun (k, o) => (k, max o b.needed)
      | none => b.needs.push (origin, b.needed)
    else b.needs
  | _, _ => b.needs

/-- The page indices hidden regions own: their body fills and pictures, and the links and surface
fills of every region inside one, `fillBase` fills standing before the surfaces. -/
private def pageHidden (spans : Array RegionSpan) (lines : Array LineOut) (bodyFills : Array Fill)
    (inks : Array InkOut) (fillBase : Nat) : PageHidden := Id.run do
  if !spans.any (·.hidden) then return {}
  let surfaces := (joinRuleParts (regionFills spans lines bodyFills inks)).reverse
  let mut out : PageHidden := {}
  for ((s, _), i) in surfaces.zipIdx do
    if s.hidden then out := { out with fills := out.fills.push (fillBase + i) }
  let mut link := 0
  for s in spans do
    if (s.linkRect lines bodyFills inks).isSome then
      if s.hidden then out := { out with links := out.links.push link }
      link := link + 1
  for s in spans do
    if s.kind matches .hidden then
      for i in [s.fillStart:s.fillEnd] do
        out := { out with fills := out.fills.push (fillBase + surfaces.size + i) }
      for i in [s.inkStart:s.inkEnd] do out := { out with inks := out.inks.push i }
  return out

/-- Close the current page: an overflow within shrink is set to fit, the leftover is distributed,
`owed` is the pending glue the content keeps, and `flush` sets a `\flushbottom` break. -/
private def Spacing.Page.finishPage (b : B) (owed : Sp := 0) (flush : Bool := false) : B :=
  let lines := if b.needed > 0 && b.pageShrink > 0 then
      (b.cur.lines.zip b.shrinkAbove).map fun (l, above) =>
        { l with y := l.y - above * b.needed / b.pageShrink }
    else b.cur.lines
  let fills := if b.needed > 0 && b.pageShrink > 0 then
      b.cur.fills.mapIdx fun i f =>
        { f with y := f.y - b.fillShrinkAbove.getD i 0 * b.needed / b.pageShrink }
    else b.cur.fills
  let inks := if b.needed > 0 && b.pageShrink > 0 then
      b.cur.inks.mapIdx fun i k =>
        k.shiftY (-(b.inkShrinkAbove.getD i 0 * b.needed / b.pageShrink))
    else b.cur.inks
  let diags := if b.needed > 0 then b.diags.push (Diag.of .N0200
      "a page set short of its height: its skips gave part of their shrink"
      (span := b.neededSource)
      (detail := some (s!"page {b.pages.size + 1}: {b.needed / 65536}pt short, its skips gave " ++
        s!"{b.needed * 100 / b.pageShrink}% of their {b.pageShrink / 65536}pt of shrink")))
    else b.diags
  -- Fil glue owns the leftover where any stands (`filShare`); else the ratio (`VDist`) splits it.
  let pageFils := b.pageFils + (if b.skip.fil then 1 else 0)
  let paintedEnd := b.surfaceEnd lines fills inks
  let leftover := if lines.size > b.pinnedLines || inks.size > b.pinnedInks then
      -- The distribution fills down to the note block's top, so it never moves a note.
      noteFloor b.bottom b.noteGap b.notesH b.noteHang - regionContentEnd (b.contentEnd owed) paintedEnd
    else 0
  -- `\flushbottom`: with no fil and no shrink, finite stretch takes the leftover (latex.ltx).
  let lo := noteFloor b.bottom b.noteGap b.notesH b.noteHang - regionContentEnd b.y paintedEnd
  let (lines, delta) := if pageFils > 0 then
      (lines.mapIdx fun i l =>
        if i < b.pinnedLines then l
        else { l with y := l.y + filShare leftover (b.vdist.filAbove (b.filsAbove.getD i 0))
                                   (b.vdist.filTotal pageFils) },
       filShare leftover (b.vdist.filAbove (b.filsAbove.back?.getD 0)) (b.vdist.filTotal pageFils))
    else if flush && !(b.needed > 0) && 0 < b.pageStretch && 0 < lo
        && (lines.size > b.pinnedLines || inks.size > b.pinnedInks) then
      (lines.mapIdx fun i l =>
        if i < b.pinnedLines then l
        else { l with y := l.y + b.stretchAbove.getD i 0 * lo / b.pageStretch },
       b.stretchAbove.back?.getD 0 * lo / b.pageStretch)
    else
      let d := b.vdist.aboveShare leftover
      (if d == 0 then lines else
        lines.mapIdx fun i l => if i < b.pinnedLines then l else { l with y := l.y + d },
       d)
  let riderShift (stretch : Sp) (fils : Nat) : Sp :=
    if pageFils > 0 then filShare leftover (b.vdist.filAbove fils) (b.vdist.filTotal pageFils)
    else if flush && !(b.needed > 0) && 0 < b.pageStretch && 0 < lo
        && (lines.size > b.pinnedLines || inks.size > b.pinnedInks) then stretch * lo / b.pageStretch
    else delta
  let bodyFills := fills.mapIdx fun i f =>
    if i < b.pinnedFills then f
    else { f with
      y := f.y + riderShift (b.fillStretchAbove.getD i 0) (b.fillFilsAbove.getD i 0) }
  -- The footer background is page furniture and never joins the body's distribution.
  let footerFills := match b.curFoot, b.footBox, b.curFootLook.bind (·.bar) with
    | some _, some (h, d), some c =>
      let y := footBaseline b.geom.pageH d - h
      #[{ x := 0, y := y, w := b.geom.pageW, h := b.geom.pageH - y, color := c : Fill }]
    | _, _, _ => #[]
  -- Picture ink carries the picture's shares; title-slot ink is pinned with its lines.
  let inks := inks.mapIdx fun i k =>
    if i < b.pinnedInks then k
    else k.shiftY (riderShift (b.inkStretchAbove.getD i 0) (b.inkFilsAbove.getD i 0))
  let openSpans := b.openRegions.map fun start => start.close b.cur
  let spans := b.closedRegions ++ openSpans
  let links := spans.filterMap fun span => span.linkRect lines bodyFills inks
  -- Outer grounds precede inner ones; all precede the content they enclose.
  let surfaces := (joinRuleParts (regionFills spans lines bodyFills inks)).reverse.map (·.2)
  let hidden := pageHidden spans lines bodyFills inks
    (if (effectivePageGround b.pageBg b.docBg).isSome then 1 else 0)
  let fills := surfaces ++ bodyFills ++ footerFills
  let fills := match effectivePageGround b.pageBg b.docBg with
    | some c => #[b.geom.ground c] ++ fills
    | none => fills
  -- The notes join after the distribution moved the body lines, so it can never move a note.
  { b with pages := b.pages.push { pageState := b.pageState,
                                   lines := lines ++ b.noteLines, fills := fills,
                                   links := links, inks := inks, foot := b.curFoot,
                                   footBox := b.footBox,
                                   frameArea := b.frameArea,
                                   footLook := b.curFootLook,
                                   frame := b.curFrame, frameOrigin := b.curFrameOrigin,
                                   fils := pageFils, band := b.curBand, hidden := hidden },
           cur := {}, curBand := none, pageState := b.pageState.ship,
           shrinkAbove := #[], fillShrinkAbove := #[], inkShrinkAbove := #[],
           fillStretchAbove := #[], inkStretchAbove := #[],
           fillFilsAbove := #[], inkFilsAbove := #[],
           pageShrink := 0, stretchAbove := #[], pageStretch := 0,
           needed := 0, neededSource := none, lastSource := none, skip := {},
           pageBg := none, vdist := .top, pageFils := 0, filsAbove := #[],
           pinnedLines := 0, pinnedFills := 0, pinnedInks := 0, anchored := false,
           openRegions := b.openRegions.map RegionStart.nextPage, closedRegions := #[],
           pendingNotes := #[], notesH := 0, notesDepth := 0, opened := false, freshStart := false,
           diags := diags, needs := b.neededOverrun }

private theorem finishPage_lifecycle_projects (b : B) (owed : Sp) (flush : Bool) :
    ((b.finishPage owed flush).pages.back?.map (·.pageState)) = some b.pageState ∧
      (b.finishPage owed flush).pageState = b.pageState.ship := by
  constructor
  · simp [Spacing.Page.finishPage]
  · rfl

private theorem finishPage_frame_projects (b : B) (owed : Sp) (flush : Bool) :
    ((b.finishPage owed flush).pages.back?.map
      (fun p => (p.frameOrigin, p.frame, p.foot))) =
        some (b.curFrameOrigin, b.curFrame, b.curFoot) ∧
    (b.finishPage owed flush).curFrameOrigin = b.curFrameOrigin ∧
    (b.finishPage owed flush).curFrame = b.curFrame ∧
    (b.finishPage owed flush).curFoot = b.curFoot := by
  exact ⟨by simp [Spacing.Page.finishPage], rfl, rfl, rfl⟩

private theorem map_segs_mapIdx (xs : Array LineOut) (f : Nat → LineOut → LineOut)
    (hf : ∀ i l, (f i l).segs = l.segs) :
    (xs.mapIdx f).map (·.segs) = xs.map (·.segs) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [hf]

private theorem map_segs_zip (xs : Array LineOut) (sh : Array Sp)
    (hsz : sh.size = xs.size) (f : LineOut × Sp → LineOut)
    (hf : ∀ p, (f p).segs = p.1.segs) :
    ((xs.zip sh).map f).map (·.segs) = xs.map (·.segs) := by
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    simp [hf]

private theorem footnote_with_mark (b : B) (owed : Sp) (flush : Bool)
    (hs : b.shrinkAbove.size = b.cur.lines.size) :
    ((b.finishPage owed flush).pages.back?.map fun p => p.lines.map (·.segs)) =
      some (b.cur.lines.map (·.segs) ++ b.noteLines.map (·.segs)) := by
  simp only [Spacing.Page.finishPage, Array.back?_push, Option.map_some, Option.some.injEq,
    Array.map_append]
  congr 1
  repeat' split
  all_goals
    first
    | rfl
    | (exact map_segs_zip _ _ hs _ (fun p => rfl))
    | (refine map_segs_mapIdx _ _ ?_
       intro i l
       split <;> rfl)
    | (refine (map_segs_mapIdx _ _ ?_).trans
        (map_segs_zip _ _ hs _ (fun p => rfl))
       intro i l
       split <;> rfl)

/-- A line's source assignment and its emitted segments, which move together. -/
private def LineOut.sourceSegs (l : LineOut) : Option Nat × Array Seg :=
  (l.leaf, l.segs)

private def LineOut.SourceBound (n : Nat) (l : LineOut) : Prop :=
  (∃ k, l.leaf = some k ∧ k < n) ∨ ∀ s ∈ l.segs, s.NoGlyph

private theorem sourceBound_of_sourceSegs {n : Nat} {l l' : LineOut}
    (he : l.sourceSegs = l'.sourceSegs) (h : l'.SourceBound n) :
    l.SourceBound n := by
  have hl := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  simpa only [LineOut.SourceBound, LineOut.sourceSegs] using
    (show (∃ k, l.leaf = some k ∧ k < n) ∨ ∀ s ∈ l.segs, s.NoGlyph from by
      rw [show l.leaf = l'.leaf from hl, show l.segs = l'.segs from hs]
      exact h)

private theorem map_sourceSegs_mapIdx (xs : Array LineOut)
    (f : Nat → LineOut → LineOut)
    (hf : ∀ i l, (f i l).sourceSegs = l.sourceSegs) :
    (xs.mapIdx f).map LineOut.sourceSegs = xs.map LineOut.sourceSegs := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [hf]

private theorem map_sourceSegs_zip (xs : Array LineOut) (sh : Array Sp)
    (hsz : sh.size = xs.size) (f : LineOut × Sp → LineOut)
    (hf : ∀ p, (f p).sourceSegs = p.1.sourceSegs) :
    ((xs.zip sh).map f).map LineOut.sourceSegs = xs.map LineOut.sourceSegs := by
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    simp [hf]

private theorem finishPage_sourceSegs (b : B) (owed : Sp) (flush : Bool)
    (hs : b.shrinkAbove.size = b.cur.lines.size) :
    ((b.finishPage owed flush).pages.back?.map fun p => p.lines.map LineOut.sourceSegs) =
      some (b.cur.lines.map LineOut.sourceSegs ++ b.noteLines.map LineOut.sourceSegs) := by
  simp only [Spacing.Page.finishPage, Array.back?_push, Option.map_some, Option.some.injEq,
    Array.map_append]
  congr 1
  repeat' split
  all_goals
    first
    | rfl
    | (exact map_sourceSegs_zip _ _ hs _ (fun p => rfl))
    | (refine map_sourceSegs_mapIdx _ _ ?_
       intro i l
       split <;> rfl)
    | (refine (map_sourceSegs_mapIdx _ _ ?_).trans
        (map_sourceSegs_zip _ _ hs _ (fun p => rfl))
       intro i l
       split <;> rfl)

/-- Plain paragraphs have no note or repeated-chrome
producer; the ledger length is part of the invariant. -/
private structure Spacing.Page.SourceBound (n : Nat) (b : B) : Prop where
  current : ∀ l ∈ b.cur.lines, l.SourceBound n
  pages : ∀ p ∈ b.pages, ∀ l ∈ p.lines, l.SourceBound n
  notes : b.pendingNotes = #[]
  chrome : b.chrome = none
  ledger : b.shrinkAbove.size = b.cur.lines.size

private theorem Spacing.Page.SourceBound.of_eq {n : Nat} {b b' : B} (hb : b.SourceBound n)
    (hc : b'.cur.lines = b.cur.lines) (hp : b'.pages = b.pages)
    (hn : b'.pendingNotes = b.pendingNotes) (ht : b'.chrome = b.chrome)
    (hs : b'.shrinkAbove.size = b.shrinkAbove.size) : b'.SourceBound n := by
  refine ⟨?_, ?_, hn.trans hb.notes, ht.trans hb.chrome, ?_⟩
  · simpa only [hc] using hb.current
  · simpa only [hp] using hb.pages
  · simpa only [hc] using hs.trans hb.ledger

private theorem sourceBound_finishPage {n : Nat} (b : B) (owed : Sp) (flush : Bool)
    (hb : b.SourceBound n) : (b.finishPage owed flush).SourceBound n := by
  refine ⟨by simp [Spacing.Page.finishPage], ?_, rfl, hb.chrome, rfl⟩
  intro p hp l hl
  change p ∈ b.pages.push _ at hp
  rcases Array.mem_push.mp hp with hp | rfl
  · exact hb.pages p hp l hl
  · have he := finishPage_sourceSegs b owed flush hb.ledger
    change ((b.pages.push _).back?.map fun p => p.lines.map LineOut.sourceSegs) = _ at he
    simp only [Array.back?_push, Option.map_some, Option.some.injEq] at he
    have hm := (Array.mem_map (f := LineOut.sourceSegs)).mpr ⟨l, hl, rfl⟩
    rw [he] at hm
    have hn : b.noteLines = #[] := by simp [Spacing.Page.noteLines, hb.notes]
    simp only [hn, Array.map_empty, Array.append_empty] at hm
    obtain ⟨l', hl', hk⟩ := Array.mem_map.mp hm
    exact sourceBound_of_sourceSegs hk.symm (hb.current l' hl')

/-- Reopen the frame's page-top chrome on a fresh page: the pinned
title lines and bar fills repeat, and content resumes below them. -/
private def Spacing.Page.reopenChrome (b : B) : B :=
  match b.chrome with
  | some c =>
    { b with cur := { lines := c.lines, fills := c.fills }
             openRegions := b.openRegions.map fun s =>
               { s with lines := c.lines.size, fills := c.fills.size, inks := 0, first := false }
             pinnedLines := c.lines.size
             pinnedFills := c.fills.size
             pinnedInks := 0
             shrinkAbove := .replicate c.lines.size 0
             fillShrinkAbove := .replicate c.fills.size 0
             inkShrinkAbove := #[]
             fillStretchAbove := .replicate c.fills.size 0
             inkStretchAbove := #[]
             fillFilsAbove := .replicate c.fills.size 0
             inkFilsAbove := #[]
             stretchAbove := .replicate c.lines.size 0
             filsAbove := .replicate c.lines.size 0
             y := c.y
             prevDepth := c.depth
             prevBelow := c.below
             prevBand := c.band
             curBand := c.header }
  | none => b

/-- moloch's frametitle box height: the last title baseline plus the padding
below it, or the title's own depth where deeper (beamerouterthememoloch.dtx). -/
public def frameBarHeight (pad lastBaseline depth : Int) : Int :=
  lastBaseline + max pad depth

public theorem frameBar_exact (pad strut depth : Int) (h : depth ≤ pad) :
    frameBarHeight pad (pad + strut) depth = 2 * pad + strut := by
  simp only [frameBarHeight]
  omega

/-- How far below its text area a frame's ink may reach before the footline's:
beamer's `\footheight` gap in its text area with no notes pending, else nothing. -/
private def Spacing.Page.clearance (b : B) : Sp :=
  if b.notesH > 0 || !b.pendingNotes.isEmpty then 0 else
  match b.frameArea with
  | .text => b.footGap
  | .margins | .paper => 0

/-- Whether the open frame stands a line `beyond` past its text
area overfull on its page, as the ladder's fit mode allows. -/
private def Spacing.Page.overhangs (b : B) (beyond : Sp) : Bool :=
  b.frameBreak == some false &&
    match b.curFit with
    | .measure => true
    | .overhang => decide (beyond ≤ b.clearance)
    | .continues | .spill => false

/-- The ladder's record of how far a marked frame step's content
reached past its text area, and the least clearance its pages left. -/
private def Spacing.Page.noteOverrun (b : B) (over : Sp) : B :=
  if over ≤ 0 then b else
  match b.ladder, b.curFrameOrigin with
  | true, some origin =>
    match b.overruns.findIdx? (·.1 == origin) with
    | some i => { b with overruns := b.overruns.modify i fun (k, o, c) =>
        (k, max o over, min c b.clearance) }
    | none => { b with overruns := b.overruns.push (origin, over, b.clearance) }
  | _, _ => b

/-- W0384: a frame not declared `[allowframebreaks]` is `over` taller than its page
and continues; a marked frame records its step instead, and flow is silent. -/
private def Spacing.Page.warnSpill (b : B) (over : Sp) : B :=
  match b.frameBreak, b.spillWarned with
  | some false, false =>
    match b.curFit, b.curFrameOrigin with
    | .spill, _ | _, none =>
      { b with diags := b.diags.push (continuedDiag b.curFrameLabel b.frameSource over)
               spillWarned := true }
    -- premise: runFitted_accounts — the ladder names every recorded frame step.
    | _, some o => { b with spilled := b.spilled.push o, spillWarned := true }
  | _, _ => b

@[simp] private theorem noteOverrun_curFrameOrigin (b : B) (o : Sp) :
    (b.noteOverrun o).curFrameOrigin = b.curFrameOrigin := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_curFrame (b : B) (o : Sp) :
    (b.noteOverrun o).curFrame = b.curFrame := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_curFoot (b : B) (o : Sp) :
    (b.noteOverrun o).curFoot = b.curFoot := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_pages (b : B) (o : Sp) :
    (b.noteOverrun o).pages = b.pages := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_cur (b : B) (o : Sp) :
    (b.noteOverrun o).cur = b.cur := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_noBreak (b : B) (o : Sp) :
    (b.noteOverrun o).noBreak = b.noBreak := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_geom (b : B) (o : Sp) :
    (b.noteOverrun o).geom = b.geom := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_docBg (b : B) (o : Sp) :
    (b.noteOverrun o).docBg = b.docBg := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_pendingNotes (b : B) (o : Sp) :
    (b.noteOverrun o).pendingNotes = b.pendingNotes := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_diags (b : B) (o : Sp) :
    (b.noteOverrun o).diags = b.diags := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem noteOverrun_paragraphBreaks (b : B) (o : Sp) :
    (b.noteOverrun o).paragraphBreaks = b.paragraphBreaks := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals rfl

@[simp] private theorem warnSpill_pages (b : B) (o : Sp) :
    (b.warnSpill o).pages = b.pages := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals rfl

@[simp] private theorem warnSpill_geom (b : B) (o : Sp) :
    (b.warnSpill o).geom = b.geom := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals rfl

@[simp] private theorem warnSpill_docBg (b : B) (o : Sp) :
    (b.warnSpill o).docBg = b.docBg := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals rfl

@[simp] private theorem warnSpill_cur (b : B) (o : Sp) :
    (b.warnSpill o).cur = b.cur := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals rfl

@[simp] private theorem warnSpill_noBreak (b : B) (o : Sp) :
    (b.warnSpill o).noBreak = b.noBreak := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals rfl

private theorem warnSpill_accounts (b : B) (o : Sp) :
    (b.warnSpill o).diags.size + (b.warnSpill o).spilled.size =
      b.diags.size + b.spilled.size +
        (if b.frameBreak = some false ∧ b.spillWarned = false then 1 else 0) := by
  unfold Spacing.Page.warnSpill
  rcases h : b.frameBreak with _ | (_ | _) <;> rcases hw : b.spillWarned
  all_goals first
    | (simp; done)
    | (simp only [and_self, ite_true]; split <;> simp only [Array.size_push] <;> omega)

/-- Whether a page the builder breaks is set flush:
`\flushbottom` declared on a TeX page outside a frame. -/
private def Spacing.Page.flushes (b : B) : Bool :=
  b.geom.flushBottom && b.geom.topskip.isSome && b.frameBreak.isNone

/-- Close an overfull page mid-frame and repeat the frame's chrome and
ground on the next; `over` is how far the band that did not fit reached. -/
private def Spacing.Page.spillPage (b : B) (over : Sp := 0) : B :=
  { (b.finishPage (flush := b.flushes)).reopenChrome.warnSpill over with pageBg := b.pageBg }

@[simp] private theorem reopenChrome_pages (b : B) :
    b.reopenChrome.pages = b.pages := by
  unfold Spacing.Page.reopenChrome
  split <;> rfl

@[simp] private theorem spillPage_pages (b : B) (o : Sp) :
    (b.spillPage o).pages = (b.finishPage 0 b.flushes).pages := by
  unfold Spacing.Page.spillPage
  simp

private theorem spillPage_frame_projects (b : B) (over : Sp) :
    ((b.spillPage over).pages.back?.map
      (fun p => (p.frameOrigin, p.frame, p.foot))) =
        some (b.curFrameOrigin, b.curFrame, b.curFoot) ∧
    (b.spillPage over).curFrameOrigin = b.curFrameOrigin ∧
    (b.spillPage over).curFrame = b.curFrame ∧
    (b.spillPage over).curFoot = b.curFoot := by
  refine ⟨?_, ?_⟩
  · simpa only [spillPage_pages] using (finishPage_frame_projects b 0 b.flushes).1
  · simp only [Spacing.Page.spillPage, Spacing.Page.warnSpill, Spacing.Page.reopenChrome]
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl⟩

/-- Whether a hidden region is open on the page being built. -/
private def Spacing.Page.hiding (b : B) : Bool := b.openRegions.any (·.kind matches .hidden)

/-- The rider door: content joining the open page with no vertical negotiation,
a line sharing the last baseline, and fills and inks painting behind. -/
private def Spacing.Page.pushSibling (b : B) (line : Option LineOut := none)
    (fills : Array Fill := #[]) (inks : Array InkOut := #[])
    (shrink : Option Sp := none) (fils : Option Nat := none) : B :=
  let b := match line with
    | some l =>
      { b with cur := { b.cur with lines := b.cur.lines.push { l with hidden := l.hidden || b.hiding } },
               shrinkAbove := b.shrinkAbove.push
                 (shrink.getD (b.shrinkAbove.back?.getD 0))
               stretchAbove := b.stretchAbove.push b.pageStretch
               filsAbove := b.filsAbove.push (fils.getD (b.filsAbove.back?.getD 0))
               lastInk := none }
    | none => b
  if fills.isEmpty && inks.isEmpty then b
  else { b with cur := { b.cur with fills := b.cur.fills ++ fills,
                                    inks := b.cur.inks ++ inks }
                fillShrinkAbove := b.fillShrinkAbove ++
                  .replicate fills.size (shrink.getD b.pageShrink)
                inkShrinkAbove := b.inkShrinkAbove ++
                  .replicate inks.size (shrink.getD b.pageShrink)
                fillStretchAbove := b.fillStretchAbove ++ .replicate fills.size b.pageStretch
                inkStretchAbove := b.inkStretchAbove ++ .replicate inks.size b.pageStretch
                fillFilsAbove := b.fillFilsAbove ++ .replicate fills.size (fils.getD b.pageFils)
                inkFilsAbove := b.inkFilsAbove ++ .replicate inks.size (fils.getD b.pageFils) }

/-- Push a picture's label lines as riders on the picture's own shrink and fils. -/
private def Spacing.Page.pushLabels (b : B) (ls : Array LineOut) (shrink : Sp) (fils : Nat) : B :=
  ls.foldl (fun b l => b.pushSibling (some l) (shrink := some shrink) (fils := some fils)) b

private def Spacing.Page.commit (b : B) (line : LineOut) (depth below : Sp)
    (ruleLine : Bool) (consume : Bool) (overflow : Sp) : B :=
  -- The page's shrink ledger is kept here alone; a line opening a page owes none.
  let above := if consume then b.pageShrink + b.skip.shrink else 0
  let stretch := if consume then b.pageStretch + b.skip.stretch else 0
  -- A consumed skip's fil counts at the page top too: `\vspace*{\fill}` survives the break.
  let fils := b.pageFils + (if b.skip.fil then 1 else 0)
  let line := { line with anchors := b.pendingAnchors ++ line.anchors
                          hidden := line.hidden || b.hiding }
  { b with cur := { b.cur with lines := b.cur.lines.push line }
           openRegions := b.openRegions.map fun s => { s with begun := true }
           pendingAnchors := #[]
           shrinkAbove := b.shrinkAbove.push above
           stretchAbove := b.stretchAbove.push stretch
           pageStretch := stretch
           pageFils := fils
           filsAbove := b.filsAbove.push fils
           pageShrink := above
           needed := max b.needed overflow
           neededSource := if b.needed < overflow then b.pendingSource else b.neededSource
           lastSource := b.pendingSource
           pendingSource := none
           y := line.y
           freshStart := false
           anchored := false
           ignoreDepth := false
           prevDepth := depth
           prevBelow := below
           prevBand := if ruleLine then .rule else .text
           lineEnd := none
           texAfter := false
           opening := false
           skip := {} }

private theorem doc_geometry_uniform (b : B) (l line : LineOut)
    (depth below : Sp) (ruleLine consume : Bool) (overflow : Sp) :
    b.finishPage.geom = b.geom ∧ (b.pushSibling (some l)).geom = b.geom ∧
      (b.commit line depth below ruleLine consume overflow).geom = b.geom :=
  ⟨rfl, rfl, rfl⟩

public def Seg.advance : Seg → Sp
  | .run _ _ _ w .. => w
  | .gap w _ => w
  | .decoratedGap w _ _ => w
  | .decoration _ w _ _ _ => w
  | .rule w .. => w
  | .image _ w _ _ => w
  | .poly _ _ => 0

/-- Shipping keeps a segment's advance: hidden ink a gap as wide, a hidden polygon none. -/
public theorem Seg.shipped_advance_exact (s : Seg) :
    ((Seg.shipped s).map Seg.advance).getD 0 = s.advance := by
  cases h : s.hides
  · simp [Seg.shipped, h]
  · cases s with
    | decoratedGap w word d =>
      simp only [Seg.shipped, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_some,
        Option.getD_some]
      exact (apply_ite Seg.advance _ _ _).trans (ite_self w)
    | _ => simp_all [Seg.shipped, Seg.advance, Seg.hides]

/-- No segment ships hidden ink. -/
public theorem Seg.shipped_hides_exact (s s' : Seg) (h : Seg.shipped s = some s') :
    s'.hides = false := by
  cases hh : s.hides
  · simp only [Seg.shipped, hh, Bool.not_false, ↓reduceIte, Option.some.injEq] at h
    exact h ▸ hh
  · cases s with
    | decoratedGap w word d =>
      simp only [Seg.shipped, hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq] at h
      subst h
      rw [apply_ite Seg.hides]
      have hu : hiddenRule (if hiddenRule d.underline then none else d.underline) = false := by
        cases hd : hiddenRule d.underline <;> simp_all [hiddenRule]
      have hl : hiddenRule (if hiddenRule d.lineThrough then none else d.lineThrough) = false := by
        cases hd : hiddenRule d.lineThrough <;> simp_all [hiddenRule]
      simp only [Seg.hides, hu, hl, Bool.or_false, ite_self]
    | _ =>
      simp only [Seg.shipped, hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq, reduceCtorEq] at h
      all_goals (subst h; rfl)

/-- A segment carrying no hidden ink ships as it stands. -/
public theorem Seg.shipped_id (s : Seg) (h : s.hides = false) : Seg.shipped s = some s := by
  simp [Seg.shipped, h]

/-- Repainting keeps a segment's advance. -/
public theorem Seg.hide_advance_exact (s : Seg) : s.hide.advance = s.advance := by
  cases s <;> rfl

private theorem shipped_advance_sum (segs : List Seg) :
    ((segs.filterMap Seg.shipped).map Seg.advance).sum = (segs.map Seg.advance).sum := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
    have h := Seg.shipped_advance_exact s
    cases hs : Seg.shipped s with
    | none =>
      simp only [hs, Option.map_none, Option.getD_none] at h
      simp [hs, ih, ← h]
    | some s' =>
      simp only [hs, Option.map_some, Option.getD_some] at h
      simp [hs, ih, h]

/-- A shipped page stands every line where it stood, its segments as wide in all. -/
public theorem PageOut.shipped_lines_exact (p : PageOut) :
    p.shipped.lines.map (fun l => (l.x, l.y, l.size, l.setWidth, (l.segs.toList.map Seg.advance).sum)) =
      p.lines.map (fun l => (l.x, l.y, l.size, l.setWidth, (l.segs.toList.map Seg.advance).sum)) := by
  simp only [PageOut.shipped, Array.map_map]
  congr 1
  funext l
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  rw [Array.toList_filterMap, shipped_advance_sum]
  split
  · simp [Array.toList_map, List.map_map, Function.comp_def, Seg.hide_advance_exact]
  · rfl

/-- No line of a shipped page carries hidden ink. -/
public theorem PageOut.shipped_hides_exact (p : PageOut) :
    ∀ l ∈ p.shipped.lines, ∀ s ∈ l.segs, s.hides = false := by
  intro l hl s hs
  simp only [PageOut.shipped, Array.mem_map] at hl
  obtain ⟨l0, _, rfl⟩ := hl
  obtain ⟨s0, _, h⟩ := Array.mem_filterMap.mp hs
  exact Seg.shipped_hides_exact s0 s h

/-- A run emptied of its glyph payload, every metric field kept. -/
public def Seg.stripGlyphs : Seg → Seg
  | .run idx color link w _ size leading decorations raise ground attr =>
    .run idx color link w #[] size leading decorations raise ground attr
  | .gap w word => .gap w word
  | .decoratedGap w word paint => .decoratedGap w word paint
  | .decoration kind w t r c => .decoration kind w t r c
  | .rule w t r c => .rule w t r c
  | .image s w h i => .image s w h i
  | .poly pts c => .poly pts c

/-- Whether a segment contributes a text strut. -/
public def Seg.isRun : Seg → Bool
  | .run .. => true
  | _ => false

/-- Whether a segment carries an explicit line height. -/
public def Seg.hasLeading : Seg → Bool
  | .run _ _ _ _ _ _ metrics _ _ _ _ => metrics.leading.isSome
  | _ => false

/-- Whether a segment carries math geometry, kept even on glyph-free construction struts. -/
public def Seg.isMath : Seg → Bool
  | .run _ _ _ _ _ _ metrics _ _ _ _ => metrics.math.isSome
  | _ => false

/-- A line's font-relative extent above and below the baseline
(CSS 2.1 §10.8.1), enlarged by math construction bounds. -/
public structure LineBox where
  /-- Box top above the baseline: leaded metric ascent. -/
  above : Sp
  /-- Box bottom below the baseline: leaded metric descent. -/
  below : Sp
  /-- Ink above the baseline (cap height per run). -/
  inkAbove : Sp
  /-- Ink below the baseline (descent per run). -/
  inkBelow : Sp
  deriving Repr

/-- A line's glyph box raised to a table row's strut, whichever reaches further above and below. -/
public def strutInk (ink : Sp × Sp) (s : Sp × Sp) : Sp × Sp :=
  (max ink.1 s.1, max ink.2 s.2)

/-- TeX's box of a table row: latex.ltx's `\@arstrut` or
the glyphs, whichever reaches further, with no leading. -/
public def strutBox (ink : Sp × Sp) (s : Sp × Sp) : LineBox :=
  let k := strutInk ink s
  { above := k.1, below := k.2, inkAbove := k.1, inkBelow := k.2 }

public theorem strutBox_exact (ink : Sp × Sp) (h d : Sp)
    (hh : ink.1 ≤ h) (hd : ink.2 ≤ d) :
    strutBox ink (h, d) = { above := h, below := d, inkAbove := h, inkBelow := d } := by
  simp only [strutBox, strutInk]
  rw [Int.max_eq_right hh, Int.max_eq_right hd]

/-- CSS 2.1 §10.8.1's half-leading over one (ascent, descent, leading): the leading
less the metric extent, split into integer halves that sum back exactly. -/
public def leadedBox (ascent descent leading : Sp) : Sp × Sp :=
  (ascent + (leading - (ascent + descent)) / 2,
   leading - ascent - (leading - (ascent + descent)) / 2)

public theorem baselines_on_grid (ascent descent leading : Int) :
    (leadedBox ascent descent leading).1 + (leadedBox ascent descent leading).2
      = leading := by
  show ascent + (leading - (ascent + descent)) / 2
    + (leading - ascent - (leading - (ascent + descent)) / 2) = leading
  omega

private def mergeLineBox (acc : Option LineBox) (box : LineBox) : Option LineBox :=
  match acc with
  | none => some box
  | some a => some ⟨max a.above box.above, max a.below box.below,
      max a.inkAbove box.inkAbove, max a.inkBelow box.inkBelow⟩

private def lineBoxStep (fs : FontSet) (nominal : Sp) (leadFactor : Nat) (lead : Option Sp)
    (acc : Option LineBox) : Seg → Option LineBox
  | .run idx _ _ _ _ sz metrics _ raise _ _ =>
    match metrics.math with
    | some m =>
      let lineHeight := metrics.leading.getD (Ir.runLead lead nominal m.size leadFactor)
      let strut := leadedBox m.ascent m.descent lineHeight
      let top := max 0 (m.top + raise)
      let below := max 0 (-m.bottom - raise)
      mergeLineBox acc ⟨max strut.1 top, max strut.2 below, top, below⟩
    | none =>
      let font := fs.get idx
      let sz := if sz == 0 then nominal else sz
      let lineHeight := metrics.leading.getD (Ir.runLead lead nominal sz leadFactor)
      let box := leadedBox (scaledAt sz font font.ascent.toNat)
        (scaledAt sz font (-font.descent).toNat) lineHeight
      mergeLineBox acc ⟨box.1 + max 0 raise, box.2 + max 0 (-raise),
        scaledAt sz font font.inkAscent.toNat + max 0 raise,
        scaledAt sz font (-font.descent).toNat + max 0 (-raise)⟩
  | .image _ _ h _ => mergeLineBox acc ⟨h, 0, h, 0⟩
  | .rule _ t r _ | .decoration _ _ t r _ =>
    mergeLineBox acc ⟨r + t, -r, r + t, -r⟩
  | .poly pts _ =>
    let (above, below) := pts.foldl
      (fun (a, b) (_, y) => (max a y, max b (-y))) (0, 0)
    mergeLineBox acc ⟨above, below, above, below⟩
  | .gap _ _ | .decoratedGap _ _ _ => acc

/-- A line's vertical extent: each run's leaded metric box at its paragraph's leading in
its size's proportion (`Ir.runLead`), plus the paragraph's strut on a line of text. -/
public def lineExtent (fs : FontSet) (fontSize bodyAscent bodyCap bodyDescent : Sp)
    (leadFactor : Nat) (size : Sp) (segs : Array Seg) (lead : Option Sp := none) :
    LineBox :=
  let nominal := if size == 0 then fontSize else size
  let customLeading := segs.any Seg.hasLeading
  let init : Option LineBox :=
    if customLeading then none
    else if segs.isEmpty || segs.any Seg.isRun then
      let strut := leadedBox (bodyAscent * nominal / fontSize)
        (bodyDescent * nominal / fontSize) (Ir.stepSkip lead nominal leadFactor)
      some ⟨strut.1, strut.2, bodyCap * nominal / fontSize,
        bodyDescent * nominal / fontSize⟩
    else none
  let measured := segs.foldl (lineBoxStep fs nominal leadFactor lead) init
  measured.getD ⟨0, 0, 0, 0⟩

public theorem line_box_glyph_free (fs : FontSet)
    (fontSize bodyAscent bodyCap bodyDescent : Sp) (leadFactor : Nat)
    (size : Sp) (segs : Array Seg) (lead : Option Sp := none) :
    lineExtent fs fontSize bodyAscent bodyCap bodyDescent leadFactor size
        (segs.map Seg.stripGlyphs) lead =
      lineExtent fs fontSize bodyAscent bodyCap bodyDescent leadFactor size segs lead := by
  unfold lineExtent
  have hrun : (segs.map Seg.stripGlyphs).any Seg.isRun
      = segs.any Seg.isRun := by
    rw [Array.any_map]
    congr 1
    funext s
    cases s <;> rfl
  have hlead : (segs.map Seg.stripGlyphs).any Seg.hasLeading =
      segs.any Seg.hasLeading := by
    rw [Array.any_map]
    congr 1
    funext s
    cases s <;> rfl
  have hemp : (segs.map Seg.stripGlyphs).isEmpty = segs.isEmpty := by
    unfold Array.isEmpty
    rw [Array.size_map]
  rw [hrun, hlead, hemp]
  simp only [Array.foldl_map]
  congr 1
  apply Array.foldl_congr rfl
  · funext acc s
    cases s <;> rfl
  · rfl
  · rfl
  · rfl

/-- The box TeX builds around a set line, read from the glyphs' outlines:
the tallest glyph above the baseline and the deepest below it. -/
public def segsInk (fs : FontSet) (segs : Array Seg) : Sp × Sp :=
  segs.foldl (fun (acc : Sp × Sp) s => match s with
    | .run idx _ _ _ glyphs sz _ _ raise _ _ =>
      let font := fs.get idx
      let sc (v : Int) : Sp := v * sz / (font.unitsPerEm : Int)
      glyphs.foldl (fun (acc : Sp × Sp) (g, _) =>
        let (lo, hi) := (font.yExtent g).getD (font.descent, font.ascent)
        (max acc.1 (sc hi + raise), max acc.2 (-(sc lo) - raise))) acc
    | .image _ _ h _ => (max acc.1 h, acc.2)
    | .rule _ t r _ | .decoration _ _ t r _ =>
      (max acc.1 (r + t), max acc.2 (-r))
    | .poly pts _ =>
      pts.foldl (fun (above, below) (_, y) =>
        (max above y, max below (-y))) acc
    | .gap .. | .decoratedGap .. => acc) (0, 0)

/-- A line of bare rule ink: at least one segment, every segment a rule. -/
public def ruleOnly (segs : Array Seg) : Bool :=
  !segs.isEmpty && segs.all fun s =>
    s matches .rule .. | .decoration ..

/-- The metric interline rule: the previous line's leaded below plus this line's
leaded above (CSS 2.1 §10.8.1), measured to a rule-only neighbour's ink edges. -/
public def interlineFor (prev : Spacing.Band) (prevDepth prevBelow : Sp)
    (ruleLine : Bool) (box : LineBox) : Sp :=
  match prev, ruleLine with
  | .text, false | .box, false => prevBelow + box.above
  | .text, true => box.inkAbove
  | .rule, _ | .box, true => prevDepth + box.inkAbove

/-- Inline math keeps the leading while the measured outlines fit, else
reserves their combined reach as TeX's interline test does (tex.web §679). -/
public def inlineMathGap (math : Bool) (normal depth height : Sp) : Sp :=
  if math then max normal (depth + height) else normal

private def Spacing.Page.previousMath (b : B) : Bool :=
  b.cur.lines.back?.any fun l => l.segs.any Seg.isMath

/-- Ordinary text keeps its metric rhythm; at a boundary
touching inline math, the neighbouring ink also clears. -/
private def Spacing.Page.textGap (b : B) (box : LineBox)
    (math : Bool) (height : Sp) : Sp :=
  inlineMathGap (math || b.previousMath) (b.prevBelow + box.above) b.boxDepth height

private def Spacing.Page.peerGap (b : B) (box : LineBox)
    (ruleLine math : Bool) (height : Sp) : Sp :=
  match b.prevBand, ruleLine with
  | .text, false => b.textGap box math height
  | _, _ => interlineFor b.prevBand b.prevDepth b.prevBelow ruleLine box

/-- Reserve painted reach below a baseline in both the ink and leaded depths. -/
public def reserveBelow (depth below reach : Sp) : Sp × Sp :=
  (max depth reach, max below reach)

/-- A placement-coordinate fact of the artifact. -/
public theorem reserveBelow_covers (depth below reach : Sp) :
    depth ≤ (reserveBelow depth below reach).1 ∧
    below ≤ (reserveBelow depth below reach).2 ∧
    reach ≤ (reserveBelow depth below reach).1 ∧
    reach ≤ (reserveBelow depth below reach).2 :=
  ⟨Int.le_max_left .., Int.le_max_left .., Int.le_max_right .., Int.le_max_right ..⟩

/-- A placement-coordinate contract of the artifact: a rule
after a completed box clears its whole painted reach. -/
public theorem closed_box_rule_covers (y depth below reach skip : Int)
    (box : LineBox) (hskip : 0 ≤ skip) :
    y + reach ≤ y + skip +
      interlineFor .box (reserveBelow depth below reach).1
        (reserveBelow depth below reach).2 true box - box.inkAbove := by
  simp only [interlineFor, reserveBelow]
  omega

/-- TeX's baseline distance between two boxes (tex.web §679): `\baselineskip` when the
boxes stay `\lineskiplimit` apart, else their extents with `\lineskip` between. -/
public def texBaselineGap (bs pd h : Sp) : Sp :=
  if pd + h ≤ bs then bs else pd + inkClearance + h

public theorem texBaselineGap_between (bs pd h : Int) :
    bs ≤ texBaselineGap bs pd h ∧ pd + h ≤ texBaselineGap bs pd h := by
  unfold texBaselineGap
  split
  · have hle : pd + h ≤ bs := ‹_›
    exact ⟨Int.le_refl bs, hle⟩
  · have hgt : ¬ (pd + h ≤ bs) := ‹_›
    show bs ≤ pd + 65536 + h ∧ pd + h ≤ pd + 65536 + h
    omega

/-- TeX's interline rule for a box `h` tall below a box of depth `pd`,
as the distance from the upper baseline to the lower box's top. -/
public def texBoxTop (bs pd h : Sp) : Sp := texBaselineGap bs pd h - h

public theorem texBoxTop_between (bs pd h : Int) :
    pd ≤ texBoxTop bs pd h ∧ bs - h ≤ texBoxTop bs pd h := by
  have := texBaselineGap_between bs pd h
  unfold texBoxTop
  omega

/-- A placement-coordinate bound of the artifact, over
the additive placement and distribution steps. -/
public theorem frame_opening_paint_covers (header origin pd bs h size leftover : Int)
    (keys : Ir.FrameKeys) (valign : VAlign) (hheader : header ≤ origin) (hpd : 0 ≤ pd) :
    header + frameBodySkip true valign size ≤
      origin + frameBodySkip true valign size + texBoxTop bs pd h +
        (VDist.of keys valign).aboveShare leftover := by
  have hbox := (texBoxTop_between bs pd h).1
  have hshare : (0 : Int) ≤ (VDist.of keys valign).aboveShare leftover :=
    (VDist.split_exact (VDist.of keys valign) leftover).1
  omega

public theorem title_bars_symmetric (skip prevDepth prevBelow : Int)
    (above below inkAbove inkBelow : Int) :
    skip + interlineFor .rule prevDepth prevBelow false
        ⟨above, below, inkAbove, inkBelow⟩ - inkAbove - prevDepth = skip ∧
    skip + interlineFor .text prevDepth prevBelow true
        ⟨above, below, inkAbove, inkBelow⟩ - inkAbove = skip := by
  simp only [interlineFor]
  constructor <;> omega

public theorem bars_clear_descenders (body descMilli : Int)
    (hb : Dim.pt 1 ≤ body) -- 1 pt: the rhythm family's floor hypothesis, not a design value
    (hm : descMilli ≤ 1000) :
    Ir.scaleStep body "LARGE" * descMilli / 1000
      < 3 * Ir.rhythmQuantum body := by
  have hb' : (65536 : Int) ≤ body := hb
  have hL : ((Ir.sizeScale.lookup "LARGE").getD 1000 : Int) = 1728 := by decide
  have hstep : Ir.scaleStep body "LARGE" = body * 1728 / 1000 := by
    unfold Ir.scaleStep Ir.scaleStepIn
    rw [hL]
  rw [hstep]
  have ht : (0 : Int) ≤ body * 1728 / 1000 := by omega
  have h1 : body * 1728 / 1000 * descMilli ≤ body * 1728 / 1000 * 1000 :=
    Int.mul_le_mul_of_nonneg_left hm ht
  have h2 : body * 1728 / 1000 * descMilli / 1000
      ≤ body * 1728 / 1000 * 1000 / 1000 :=
    Int.ediv_le_ediv (by decide) h1
  have h3 : body * 1728 / 1000 * 1000 / 1000 = body * 1728 / 1000 :=
    Int.mul_ediv_cancel _ (by decide)
  calc body * 1728 / 1000 * descMilli / 1000
      ≤ body * 1728 / 1000 * 1000 / 1000 := h2
    _ = body * 1728 / 1000 := h3
    _ < 3 * Ir.rhythmQuantum body := by
        simp only [Ir.rhythmQuantum, Ir.leadingFor, Ir.leadingMilli]
        omega

/-- The body strut's leaded depth at the body size, which a box on a baseline leaves pending. -/
private def Spacing.Page.strutBelow (fs : FontSet) (b : B) : Sp :=
  (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent b.geom.leading
    b.geom.fontSize #[]).below

/-- An empty box at `y`, TeX's `\vbox{}`: the next band
is spaced below it as below a box of depth zero. -/
private def Spacing.Page.anchorAt (fs : FontSet) (b : B) (y : Sp) : B :=
  { b with y := y, prevDepth := 0, prevBelow := b.strutBelow fs, prevBand := .text,
           lastInk := some (y, 0, 0) }

/-- Open a frame's content as beamer's `\vskip-\parskip\vbox{}` does: an
empty box below the title box or bar, the declared skip `g` pending. -/
private def Spacing.Page.openBody (b : B) (fs : FontSet) (g : Glue) (box : Option Sp) : B :=
  let barBottom := (b.cur.fills.back?.map fun f => f.y + f.h).getD 0
  let opened := { b with y := if b.cur.lines.isEmpty then barBottom
                             else max (b.y + box.getD b.prevDepth) barBottom
                         prevDepth := 0
                         prevBelow := b.strutBelow fs
                         prevBand := .text
                         lastInk := none
                         opening := true
                         skip := b.skip.add g
                         opened := true }
  -- A spill discards pending glue, so the frame's opening skip is kept in the resume origin.
  { opened with chrome := b.chrome.map fun c =>
      { c with y := opened.y + opened.skip.width
               depth := opened.prevDepth
               below := opened.prevBelow
               band := opened.prevBand
               header := opened.curBand } }

private theorem Spacing.Page.openBody_resume_agree (b : B) (fs : FontSet) (g : Glue)
    (box : Option Sp) (c : Spacing.Chrome) (hc : b.chrome = some c) (owed : Sp) (flush : Bool) :
    let opened := b.openBody fs g box
    let resumed := (opened.finishPage owed flush).reopenChrome
    resumed.y = opened.y + opened.skip.width ∧
    resumed.prevDepth = opened.prevDepth ∧
    resumed.prevBelow = opened.prevBelow ∧
    resumed.prevBand = opened.prevBand ∧
    resumed.curBand = opened.curBand := by
  simp [Spacing.Page.openBody, Spacing.Page.reopenChrome, Spacing.Page.finishPage, hc]

/-- The pending skip a fresh page keeps: all of it after `\vspace*`'s
zero rule or a fil, else none, as TeX discards glue at a page top. -/
private def Spacing.Page.topKept (b : B) : Sp := if b.anchored || b.skip.fil then b.skip.width else 0

/-- The fit-or-spill skeleton bands take: `place b y consume over` sets one at `y` on a fresh
page, within the page's shrink, under `noBreak`, or on a blank opened page where `holdsBlank`;
else overfull where the ladder allows, else after a break, `settle` judging what stands unfitted. -/
private def Spacing.Page.fitWith (b : B) (place : B → Sp → Bool → Sp → B)
    (settle : B → Sp → Sp → B) (firstY stepY retryY : B → Sp) (inkBelow bottom : Sp)
    (holdsBlank : Bool) : B :=
  if b.fresh then
    settle (place b (firstY b + b.surfaceTop) false 0) (firstY b + b.surfaceTop)
      (inkBelow + b.surfaceBottom)
  else
    let y := stepY b + b.surfaceTop
    let overflow := y + inkBelow + b.surfaceBottom - bottom
    let above := b.pageShrink + b.skip.shrink
    -- An opened page with nothing on it holds a line: a break would ship an empty frame page.
    if overflow ≤ above ∨ b.noBreak ∨ (holdsBlank && b.cur.blank) then
      place b y true (min overflow above)
    -- A frame the ladder stands overfull, as beamer sets it on its one page.
    else if b.overhangs (overflow - above) then
      (place b y true above).noteOverrun (overflow - above)
    else
      let s := b.spillPage (overflow - above)
      (if s.cur.blank then
        settle (place s (firstY s + s.surfaceTop) false 0) (firstY s + s.surfaceTop)
          (inkBelow + s.surfaceBottom)
      else
        settle (place s (retryY s + s.surfaceTop) false 0) (retryY s + s.surfaceTop)
          (inkBelow + s.surfaceBottom)).noteOverrun (overflow - above)

/-- A line committed by `fitWith`, its notes attached where it lands. -/
private def Spacing.Page.fitCommit (b : B) (mk : Sp → LineOut) (firstY stepY retryY : B → Sp)
    (depth below : Sp) (rl : Bool) (inkBelow bottom : Sp)
    (notes : Array NoteBlock := #[]) : B :=
  b.fitWith (fun b y consume over => (b.commit (mk y) depth below rl consume over).attachNotes notes)
    Spacing.Page.warnNoteOverrun firstY stepY retryY inkBelow bottom true

/-- TeX's interline rule for the first box below `\vspace*`'s zero
rule, from the depth saved before the rule (latex.ltx `\@vspacer`). -/
public def anchorRise (ignore : Bool) (lead depth h : Sp) : Sp :=
  if ignore then h else if 0 ≤ lead - depth - h then lead - depth else h + inkClearance

/-- The first baseline of a fresh page below the text area's top: TeX's `\topskip`
rule on a TeX page, the engine's metric rule on a frame page, past the skip kept. -/
private def Spacing.Page.freshBaseline (b : B) (ink : Sp) (box : LineBox) (lead : Sp) : Sp :=
  b.geom.bodyTop + (match b.geom.topskip with
    | some t => if b.anchored || b.skip.fil then
        t + (match b.colAnchor with
          | some e => ink + e
          | none => anchorRise b.ignoreDepth lead b.boxDepth ink)
      else max t ink
    | none => max b.ascent box.above) + b.topKept

/-- A line's TeX box: its glyphs', and at least its `\strutbox` of `\baselineskip` `s`. -/
private def lineStrutInk (strut : Option Sp) (ink : Sp × Sp) : Sp × Sp :=
  match strut with
  | some s => strutInk ink (s * 7 / 10, s * 3 / 10)
  | none => ink

/-- Place one line: its box follows the tallest run on it, its baseline distance the
interline rule, and a line that does not fit opens the next page (`fitCommit`). -/
private def Spacing.Page.placeLine (fs : FontSet) (b : B) (x : Sp) (size : Sp) (segs : Array Seg)
    (w : Sp) (hang : Sp := 0) (expand : Int := 0)
    (notes : Array NoteBlock := #[]) (counted : Bool := false)
    (leaf : Option Nat := none) (firstBaseline : Option Sp := none)
    (display : Option DisplayJob := none) (opens : Bool := false)
    (anchors : Array String := #[]) (paintPadding : Option Sp := none)
    (stepLead : Option Sp := none) (rowStrut : Option (Sp × Sp) := none) (strut : Option Sp := none) : B :=
  let box := lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs stepLead
  -- A zero-width strut counts in TeX's box, so the ink is read before the filter below.
  let ink := segsInk fs segs
  -- A table row is TeX's row box, strut and glyphs, with no leading.
  let box := match rowStrut with
    | some s => strutBox ink s
    | none => box
  let ink := match rowStrut with
    | some s => strutInk ink s
    | none => ink
  let peer (b : B) := b.peerGap box (ruleOnly segs) (segs.any Seg.isMath) ink.1
  -- A display's box is TeX's (tex.web §1199), an alignment row standing on amsmath's `\strut@`.
  let bs := Ir.stepSkip stepLead size b.geom.leading
  let strut := match display with
    | some dj => if dj.ctx.align then some bs else strut
    | none => strut
  let tex := lineStrutInk strut ink
  let rl := ruleOnly segs
  let lastBase : Sp := match display with
    | some dj =>
      if !dj.ctx.align then 0 else
      segs.foldl (fun m s => match s with
        | .rule 0 0 raise _ => max m (-raise)
        | _ => m) 0
    | none => 0
  -- A zero-width rule is dropped: some viewers rasterize a degenerate rectangle as a hairline.
  let segs := segs.filter fun s => match s with
    | .rule w _ _ _ => w != 0
    | _ => true
  -- The fit test reserves this line's notes too, so a line that does not fit spills with its notes.
  let need := if notes.isEmpty then 0
    else notes.foldl (fun s nb => s + nb.height) 0
  let bottom := noteFloor b.bottom b.noteGap (b.notesH + need) (b.noteHang (notes.back?.map (·.depth)))
  let mk (y : Sp) : LineOut :=
    { x := x, y := y, size := size, segs := segs, setWidth := w
      regionExtent := some tex
      hang := hang, expand := expand, counted := counted, leaf := leaf, anchors := anchors
      lastBase := lastBase }
  let lead := Ir.stepSkip stepLead (if size == 0 then b.geom.fontSize else size)
    b.geom.leading
  -- TeX's interline glue around display math and below a colour box's top; else the metric rule.
  let gap (b : B) : Sp := match paintPadding, display, opens with
    | some pad, _, _ =>
      texBoxTop (Ir.leadingFor b.geom.fontSize b.geom.leading) b.boxDepth
        (ink.1 + ink.2 + 2 * pad) + ink.1
    | none, some dj, true =>
      if dj.emptyLine then texBaselineGap bs b.boxDepth 0 + texBaselineGap bs 0 tex.1
      else texBaselineGap bs b.boxDepth tex.1
    | none, _, _ =>
      if b.texAfter || display.isSome then texBaselineGap bs b.boxDepth tex.1
      -- Below a frame's opening box the line takes TeX's interline glue at its `\baselineskip`.
      else if b.opening then
        texBaselineGap (if segs.any (· matches .run ..) then box.above + box.below else lead)
          b.boxDepth tex.1
      else peer b
  ((b.fitCommit mk
    (fun b => b.freshBaseline ink.1 box lead)
    (fun b => b.y + b.skip.width
      + firstBaseline.getD
        (if b.ignoreDepth then b.boxDepth + ink.1
         else gap b))
    (fun b => b.y + peer b)
    box.inkBelow box.below rl box.inkBelow bottom notes).keepInk tex.2).displayState
      display.isSome (if display.isSome then none else some (x + w - b.geom.hmargin))

private theorem sourceBound_warnSpill {n : Nat} (b : B) (over : Sp)
    (hb : b.SourceBound n) : (b.warnSpill over).SourceBound n := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals exact hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_spillPage {n : Nat} (b : B) (over : Sp)
    (hb : b.SourceBound n) : (b.spillPage over).SourceBound n := by
  have hf := sourceBound_finishPage b 0 b.flushes hb
  have hr : (b.finishPage 0 b.flushes).reopenChrome.SourceBound n := by
    simpa only [Spacing.Page.reopenChrome, hf.chrome] using hf
  exact (sourceBound_warnSpill _ over hr).of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_commit {n : Nat} (b : B) (l : LineOut)
    (depth below : Sp) (rl consume : Bool) (over : Sp)
    (hb : b.SourceBound n) (hl : l.SourceBound n) :
    (b.commit l depth below rl consume over).SourceBound n := by
  refine ⟨?_, hb.pages, hb.notes, hb.chrome, ?_⟩
  · intro l' hm
    change l' ∈ b.cur.lines.push _ at hm
    rcases Array.mem_push.mp hm with hm | rfl
    · exact hb.current l' hm
    · exact hl
  · simpa only [Spacing.Page.commit, Array.size_push] using congrArg (· + 1) hb.ledger

private theorem sourceBound_warnNoteOverrun {n : Nat} (b : B) (y d : Sp)
    (hb : b.SourceBound n) : (b.warnNoteOverrun y d).SourceBound n := by
  simp only [Spacing.Page.warnNoteOverrun]
  split <;> exact hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_noteOverrun {n : Nat} (b : B) (o : Sp)
    (hb : b.SourceBound n) : (b.noteOverrun o).SourceBound n := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals exact hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_fitCommit {n : Nat} (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (hb : b.SourceBound n) (hl : ∀ y, (mk y).SourceBound n) :
    (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom #[]).SourceBound n := by
  simp only [Spacing.Page.fitCommit, Spacing.Page.fitWith, Spacing.Page.attachNotes, Array.isEmpty_empty, ite_true]
  split
  · exact sourceBound_warnNoteOverrun _ _ _ (sourceBound_commit b _ _ _ _ _ _ hb (hl _))
  · split
    · exact sourceBound_commit b _ _ _ _ _ _ hb (hl _)
    · split
      · exact sourceBound_noteOverrun _ _ (sourceBound_commit b _ _ _ _ _ _ hb (hl _))
      · have hs := sourceBound_spillPage b
          (stepY b + b.surfaceTop + inkBelow + b.surfaceBottom - bottom -
            (b.pageShrink + b.skip.shrink)) hb
        apply sourceBound_noteOverrun
        split
        · exact sourceBound_warnNoteOverrun _ _ _
            (sourceBound_commit _ _ _ _ _ _ _ hs (hl _))
        · exact sourceBound_warnNoteOverrun _ _ _
            (sourceBound_commit _ _ _ _ _ _ _ hs (hl _))

private theorem sourceBound_keepInk {n : Nat} (b : B) (d : Sp)
    (hb : b.SourceBound n) : (b.keepInk d).SourceBound n :=
  hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_displayState {n : Nat} (b : B) (tex : Bool)
    (lineEnd : Option Sp) (hb : b.SourceBound n) :
    (b.displayState tex lineEnd).SourceBound n :=
  hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_placeLine {n : Nat} (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (counted : Bool)
    (leaf : Option Nat) (firstBaseline : Option Sp) (display : Option DisplayJob)
    (opens : Bool) (anchors : Array String) (paintPadding : Option Sp)
    (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp) (hb : b.SourceBound n)
    (hl : (∃ k, leaf = some k ∧ k < n) ∨ ∀ s ∈ segs, s.NoGlyph) :
    (b.placeLine fs x size segs w hang ex #[] counted leaf firstBaseline display opens
      anchors paintPadding step rs strut).SourceBound n := by
  simp only [Spacing.Page.placeLine]
  apply sourceBound_displayState
  apply sourceBound_keepInk
  apply sourceBound_fitCommit
  · exact hb
  · intro y
    rcases hl with hl | hl
    · exact Or.inl hl
    · exact Or.inr fun s hs => hl s (Array.mem_of_mem_filter hs)

private theorem placeLine_gap_exact (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (firstBaseline : Option Sp)
    (hcur : b.cur.lines.isEmpty = false) (hfresh : b.freshStart = false)
    (hpr : b.prevBand = .text) (hrl : ruleOnly segs = false)
    (hnn : b.notesH = 0) (hid : b.ignoreDepth = false) (htx : b.texAfter = false)
    (hop : b.opening = false)
    (hfit : b.y + b.skip.width
        + firstBaseline.getD
          (b.textGap (lineExtent fs b.geom.fontSize b.ascent b.capHeight
            b.descent b.geom.leading size segs) (segs.any Seg.isMath) (segsInk fs segs).1)
        + b.surfaceTop
        + (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
            b.geom.leading size segs).inkBelow + b.surfaceBottom - b.bottom
        ≤ b.pageShrink + b.skip.shrink) :
    (b.placeLine fs x size segs w hang ex #[] false none firstBaseline).cur.lines.back?.map (·.y) =
      some (b.y + b.skip.width
        + firstBaseline.getD
          (b.textGap (lineExtent fs b.geom.fontSize b.ascent b.capHeight
            b.descent b.geom.leading size segs) (segs.any Seg.isMath) (segsInk fs segs).1) + b.surfaceTop) := by
  rcases hle : lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs with ⟨ht, bl, ia, dp⟩
  rw [hle] at hfit
  dsimp only at hfit
  unfold Spacing.Page.placeLine Spacing.Page.fitCommit Spacing.Page.fitWith
  rw [hle]
  dsimp only
  simp only [displayState_cur, keepInk_cur]
  simp only [Spacing.Page.fresh, PageOut.blank, hcur, hfresh, Bool.false_and, hpr, hrl, hid, Spacing.Page.peerGap, hnn, noteFloor,
    htx, hop, Option.isSome_none, Array.isEmpty_empty, Bool.or_self, Bool.false_eq_true, ite_false,
    ite_true, Int.add_zero, beq_self_eq_true]
  simp only [hfit, true_or, ite_true, Spacing.Page.commit, Spacing.Page.attachNotes,
    Array.isEmpty_empty, ite_true]
  simp [Array.back?_push]

private theorem first_baseline_declared (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w : Sp) (hf : b.fresh = true) :
    (b.placeLine fs x size segs w).cur.lines.back?.map (·.y) =
      some (b.freshBaseline (segsInk fs segs).1
        (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
          b.geom.leading size segs)
        (Ir.leadingFor (if size == 0 then b.geom.fontSize else size) b.geom.leading)
        + b.surfaceTop) := by
  rcases hle : lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs with ⟨ht, bl, ia, dp⟩
  unfold Spacing.Page.placeLine Spacing.Page.fitCommit Spacing.Page.fitWith
  rw [hle]
  dsimp only
  simp only [displayState_cur, keepInk_cur]
  simp [hf, Spacing.Page.commit, Spacing.Page.attachNotes, Array.back?_push]

private theorem placeLine_leaf_exact (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w : Sp) (lf : Option Nat) (hf : b.fresh = true) :
    (b.placeLine fs x size segs w (leaf := lf)).cur.lines.back?.map (·.leaf) = some lf := by
  rcases hle : lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs with ⟨ht, bl, ia, dp⟩
  unfold Spacing.Page.placeLine Spacing.Page.fitCommit Spacing.Page.fitWith
  rw [hle]
  dsimp only
  simp only [displayState_cur, keepInk_cur]
  simp [hf, Spacing.Page.commit, Spacing.Page.attachNotes, Array.back?_push]

private theorem placeLine_boxDepth_exact (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (step : Option Sp := none) :
    (b.placeLine fs x size segs w hang ex ns c lf (stepLead := step)).boxDepth =
      (segsInk fs segs).2 := by
  simp only [Spacing.Page.placeLine]
  exact keepInk_boxDepth_exact ..

private theorem finishPage_shift_uniform (b : B) (owed : Sp)
    (hsh : b.needed ≤ 0 ∨ b.pageShrink ≤ 0)
    (hfil : b.pageFils = 0) (hsf : b.skip.fil = false)
    (hpn : b.pendingNotes.isEmpty = true) :
    ∃ d, ∀ i, b.pinnedLines ≤ i →
      ((b.finishPage owed).pages.back?.bind fun p => p.lines[i]?.map (·.y)) =
        (b.cur.lines[i]?.map fun l => l.y + d) := by
  have hcond : (decide (b.needed > 0) && decide (b.pageShrink > 0)) = false := by
    rcases hsh with h | h <;> simp [Int.not_lt.mpr h]
  unfold Spacing.Page.finishPage Spacing.Page.noteLines
  simp only [hcond, hsf, hfil, hpn, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
    Array.append_empty, Nat.add_zero,
    Nat.lt_irrefl, Array.back?_push, Option.bind_some]
  refine ⟨b.vdist.aboveShare (if b.cur.lines.size > b.pinnedLines || b.cur.inks.size > b.pinnedInks then
      noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)
    else 0), fun i hi => ?_⟩
  split <;> split <;>
    simp_all [Array.getElem?_mapIdx, Option.map_map, Function.comp_def,
      Nat.not_lt.mpr hi]

private theorem finishPage_center_exact (b : B) (owed : Sp)
    (hv : b.vdist = .center) (hsh : b.needed ≤ 0 ∨ b.pageShrink ≤ 0)
    (hfil : b.pageFils = 0) (hsf : b.skip.fil = false)
    (hpn : b.pendingNotes.isEmpty = true) (hc : b.pinnedLines < b.cur.lines.size)
    (hl : 0 ≤ noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) :
    (∀ i, b.pinnedLines ≤ i →
      ((b.finishPage owed).pages.back?.bind fun p => p.lines[i]?.map (·.y)) =
        (b.cur.lines[i]?.map fun l => l.y +
          VDist.center.aboveShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)))) ∧
    VDist.center.aboveShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks))
      ≤ (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks))
        - VDist.center.aboveShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) ∧
    (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks))
        - VDist.center.aboveShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks))
      ≤ VDist.center.aboveShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks))
        + 1 := by
  refine ⟨fun i hi => ?_, VDist.center_split_exact _ hl⟩
  have hcond : (decide (b.needed > 0) && decide (b.pageShrink > 0)) = false := by
    rcases hsh with h | h <;> simp [Int.not_lt.mpr h]
  unfold Spacing.Page.finishPage Spacing.Page.noteLines
  simp only [hcond, hsf, hfil, hpn, hv, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
    Array.append_empty, Nat.add_zero,
    Nat.lt_irrefl, Array.back?_push, Option.bind_some]
  split <;> split <;>
    simp_all [Array.getElem?_mapIdx, Option.map_map, Function.comp_def,
      Nat.not_lt.mpr hi]

private theorem finishPage_fill_centre_exact (b : B) (owed : Sp)
    (hsh : b.needed ≤ 0 ∨ b.pageShrink ≤ 0) (hj : b.vdist.joins = false)
    (h2 : b.pageFils + (if b.skip.fil then 1 else 0) = 2)
    (h1 : ∀ i, b.pinnedLines ≤ i → b.filsAbove.getD i 0 = 1)
    (hpn : b.pendingNotes.isEmpty = true) (hc : b.pinnedLines < b.cur.lines.size)
    (hl : 0 ≤ noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) :
    (∀ i, b.pinnedLines ≤ i →
      ((b.finishPage owed).pages.back?.bind fun p => p.lines[i]?.map (·.y)) =
        (b.cur.lines[i]?.map fun l => l.y +
          filShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) 1 2)) ∧
    filShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) 1 2
      ≤ (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks))
        - filShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) 1 2 ∧
    (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks))
        - filShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) 1 2
      ≤ filShare (noteFloor b.bottom b.noteGap b.notesH b.noteHang -
        regionContentEnd (b.contentEnd owed) (b.surfaceEnd b.cur.lines b.cur.fills b.cur.inks)) 1 2 + 1 := by
  refine ⟨fun i hi => ?_, by rw [filShare_half_exact]; exact VDist.center_split_exact _ hl⟩
  have hcond : (decide (b.needed > 0) && decide (b.pageShrink > 0)) = false := by
    rcases hsh with h | h <;> simp [Int.not_lt.mpr h]
  unfold Spacing.Page.finishPage Spacing.Page.noteLines
  simp only [hcond, hpn, h2, hj, VDist.filAbove, VDist.filTotal, Bool.false_eq_true, ite_false,
    ite_true, Array.append_empty, Array.back?_push, Option.bind_some]
  simp_all [Array.getElem?_mapIdx, Option.map_map, Function.comp_def,
    Nat.not_lt.mpr hi]

/-- The census key of an overfull line: the source position of its first located item. -/
def overfullSubject : Option Span → String
  | some s => s!"overfull:{s.file}:{s.pos.line}:{s.pos.col}"
  | none => "overfull:unlocated"

private def Spacing.Page.warnOverfull (b : B) (source : Option Span) : B :=
  { b with
    diags := b.diags.push
      (Diag.of .W0005 "overfull line; no feasible break" (span := source)
        (subject := some (overfullSubject source)) (output := some .pdf)) }

/-- First located item of the line actually set, found by halving over the sites in item order. -/
private def lineSource (sources : Array (Nat × Span)) (first last : Nat) : Option Span := Id.run do
  let mut lo := 0
  let mut hi := sources.size
  for _ in [0:sources.size + 1] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if ((sources[mid]?.map (·.1)).getD 0) < first then lo := mid + 1 else hi := mid
    else break
  return sources[lo]?.bind fun (i, span) => if i ≤ last then some span else none

/-- A heading's declared rule as the line builder reads
it: weight, position against the baseline, and colour. -/
public structure HeadingRule where
  thickness : Sp
  position : Ir.RulePosition
  color : Ir.Color
  deriving Repr, Inhabited

/-- A paragraph that opens a TeX box: its first line stands `inset` below
the box's top, and TeX's interline rule places the box and its lines. -/
public structure TexBox where
  inset : Sp
  more : Bool
  leading : Sp
  boxed : Bool := true
  /-- A rule beside the box reaching by its lines: how far past the
  box's lines it reaches above and below the box's baseline. -/
  reach : Option (Sp × Sp) := none
  /-- The box's last line's depth, its strut's or its ink's. -/
  lastDepth : Sp := 0
  deriving Repr, Inhabited, DecidableEq

/-- One paragraph, measured and ready to break: everything `kp` and line placement need. -/
public structure Spacing.Paragraph where
  private mk ::
  private items : Array Item
  private extras : Std.HashMap Nat Sp
  private wordOffsets : Std.HashMap Nat Sp := {}
  private anchors : Array (String × Nat) := #[]
  private itemSources : Array (Nat × Span) := #[]
  private diags : Array Diag
  private target : Sp
  private indent : Sp
  private center : Bool
  private size : Sp
  /-- The leading of the named size step the paragraph is set
  in (`Ir.paraStep?`), `size` then being that step's size. -/
  private lead : Option Sp := none
  /-- TeX's baseline skip for a title part that opens a new line. -/
  private firstBaseline : Option Sp := none
  /-- The line hangs from the right edge of the measure (`Geom.flushRight`). -/
  private flushRight : Bool := false
  /-- Justified or ragged, from the page. -/
  private justify : Bool := true
  /-- The ragged edge is LaTeX's `\@flushglue`: every
  line ends in `0pt plus 1fil` and fills first. -/
  private rightFil : Bool := false
  /-- Whether boundary glyphs protrude into the margin, from the page. -/
  private protrude : Bool := true
  /-- Whether font boxes may expand within ±`expandLimit`, from the page. -/
  private expand : Bool := true
  /-- Marker content set as its own items and placed before the first line. -/
  private markerSegs : Option (Array Seg × Sp) := none
  /-- Where the marker's column stands, right-aligned against
  this offset from the margin; `none` hangs it off the indent. -/
  private markerIndent : Option Sp := none
  /-- Where a flush-left marker starts, as an offset from the
  margin (`Ir.BibItem.labelFlush`); read before `markerIndent`. -/
  private markerLeft : Option Sp := none
  /-- TeX's `\hangindent`, the list's `\itemindent` negated:
  every line but the first stands this far in from `indent`. -/
  private hangIndent : Sp := 0
  /-- A rule filling the first line after the content. -/
  private rule : Option HeadingRule := none
  /-- The paragraph's pre-broken footnotes, each with its mark's item index. -/
  private notes : Array (Nat × NoteBlock) := #[]
  /-- The paragraph stands inside a float, so its lines are not counted galley lines. -/
  private inFloat : Bool := false
  /-- The breaks ending a line of a declared line that re-flowed, whose overrun its W0386 names. -/
  private carried : Array Bool := #[]
  /-- The first `Struct` leaf of the block this paragraph sets; `none` for generated ink. -/
  private leaf : Option Nat := none
  /-- The space the text after this paragraph needs on its page: nonzero
  for a heading, which TeX never lets end a page (`\@xsect`). -/
  private keepNext : Sp := 0
  /-- The paragraph is display math, set as TeX sets a display. -/
  private display : Option DisplayJob := none
  /-- The paragraph opens a painted colour box with this inset (`Ir.titledPadding`). -/
  private paintPadding : Option Sp := none
  /-- A table row's strut, height and depth (`tableStrut`); `none` off a table. -/
  private rowStrut : Option (Sp × Sp) := none
  /-- Every line carries a strut of this `\baselineskip`, as fancyvrb's code lines do. -/
  private strut : Option Sp := none
  /-- Whether the paragraph's forced line ends declare its lines,
  as a tex `\\` does and a markdown hard break does not. -/
  private declaresLines : Bool := true
  /-- The stretch every line carries besides its own glue (`KpSums.bg`): plain
  TeX's `\rightskip 0pt plus 2em` in a narrowed table cell, else zero. -/
  private background : Sp := 0
  /-- The paragraph opens a TeX box (`TexBox`). -/
  private texBox : Option TexBox := none

private abbrev ParaJob := Spacing.Paragraph

/-- The breaks placement sets a paragraph's lines at. -/
private def Spacing.Paragraph.breaks (j : ParaJob) : Array Nat :=
  kpTwoPass j.items j.target (j.protrude && j.justify && !j.center)
    (j.expand && j.justify && !j.center) j.background j.rightFil (j.center && j.rightFil)

private structure Spacing.Paragraph.SourceBound (n : Nat) (j : ParaJob) : Prop where
  source : (∃ k, j.leaf = some k ∧ k < n) ∨ ∀ it ∈ j.items, it.NoGlyph
  notes : j.notes = #[]
  marker : j.markerSegs = none
  rule : j.rule = none

/-- A title slot's placement resolved to the page: which point of its box stands at
which point of the page, the shifts, the inner and outer seps, and a declared width. -/
public structure SlotSpec where
  anchor : Ir.BoxPoint
  pagePoint : Ir.BoxPoint
  dx : Int
  dy : Int
  sep : Int
  outerSep : Int
  box : Option (Int × Int)
  deriving Repr, Inhabited

/-- Where a slot's box goes: its expanded anchor point onto the
page point, plus the declared shifts (pgf manual §17.2). -/
public def slotShift (spec : SlotSpec) (pageW pageH left w top h : Int) : Int × Int :=
  let inset := spec.sep + spec.outerSep
  let bw := w + 2 * inset
  let bh := h + 2 * inset
  let px := Ir.shareOf spec.pagePoint.hshares pageW + spec.dx
  let py := Ir.shareOf spec.pagePoint.vshares pageH + spec.dy
  (px - (left - inset + Ir.shareOf spec.anchor.hshares bw),
   py - (top - inset + Ir.shareOf spec.anchor.vshares bh))

public theorem slotShift_exact (spec : SlotSpec) (pageW pageH left w top h : Int) :
    left + (slotShift spec pageW pageH left w top h).1 - spec.sep - spec.outerSep
        + Ir.shareOf spec.anchor.hshares (w + 2 * (spec.sep + spec.outerSep))
      = Ir.shareOf spec.pagePoint.hshares pageW + spec.dx ∧
    top + (slotShift spec pageW pageH left w top h).2 - spec.sep - spec.outerSep
        + Ir.shareOf spec.anchor.vshares (h + 2 * (spec.sep + spec.outerSep))
      = Ir.shareOf spec.pagePoint.vshares pageH + spec.dy := by
  unfold slotShift
  dsimp only
  constructor <;> omega

/-- Where an empty box (`Op.boxAnchor`) stands below the band above. -/
private inductive AnchorRule where
  /-- TeX's interline rule for a box `h` tall (`texBoxTop`). -/
  | tex (h : Sp)
  /-- `\nointerlineskip`: on the band's bottom. -/
  | flush
  /-- tcolorbox's balanced skip `s` (tcolorbox.sty, `before skip balanced`). -/
  | balanced (s : Sp)
  deriving Inhabited

/-- Block-walk output replayed in document order by
placement, so the page builder stays sequential. -/
private inductive Op where
  | skip (g : Glue)
  /-- Glue owed after a display: the long and the short
  skip, of which the display's line chose one. -/
  | skipAlt (long short : Glue)
  /-- A titled frame's content opens here, below the title box, with the
  frame's own top skip pending; `box` is where a title template's box ends. -/
  | bodyOpen (g : Glue) (box : Option Sp)
  /-- A paragraph and the task computing its breaks (`Op.ofPara`). -/
  | para (job : ParaJob) (breaks : Task (Array Nat))
  /-- The placed extent of a block link or painted surface. -/
  | regionOpen (kind : RegionKind)
  | regionClose
  /-- A page boundary: a frame is a page of the handout, whatever fits it. -/
  | brk
  /-- The folio and running style declared at a boundary. -/
  | pageOpening (opening : Ir.PageOpening)
  /-- Column markers: `colOpen` saves the vertical position, `colNext`
  rewinds to it, `colClose` resumes below the tallest column. -/
  | colOpen (pos : Array Ir.BoxPos)
  | colNext
  | colClose
  /-- Style for the page being opened: a background fill and
  its vertical distribution, reset when the page closes. -/
  | pageStyle (bg : Option Ir.Color) (vdist : VDist)
  /-- Persistent page ground from a palette epoch, surviving a page close. -/
  | pageGround (bg : Option Ir.Color)
  /-- A colour bar behind the line just placed, the frame title;
  with a `strut`, moloch's frametitle box (`frameBar_exact`). -/
  | titleBar (color : Ir.Color) (pad : Sp) (strut : Option Sp)
  /-- A frame opens, with whether its author declared `[allowframebreaks]`. -/
  | frameOpen (breakable : Bool) (source : Option Span) (opening : FrameOpening)
  /-- Close source ownership after the frame's final page boundary. -/
  | frameClose
  /-- beamer's `\vbox{}` opening a block's colour box, or a
  tcolorbox's edge: an empty box the next band is spaced below. -/
  | boxAnchor (rule : AnchorRule) (shift : Sp) (paints : Bool)
  /-- A full-measure horizontal rule as its own line, placed through `placeLine`. -/
  | hrule (color : Ir.Color) (thickness : Sp)
  /-- A table rule row, already set: placed at the pending skip
  below the previous ink and committed with zero depth. -/
  | tableRule (thickness : Sp) (x w : Sp) (segs : Array Seg)
  /-- Content placed so far on the open page is chrome pinned
  to the page top, which the distribution never moves. -/
  | pin
  /-- A progress bar under the line just placed: `bg`
  across `w` from `x`, `fg` over `num/den` of it. -/
  | progress (num den : Nat) (fg bg : Ir.Color) (thick x w : Sp)
  /-- The logo the pages from here carry; empty clears it. -/
  | setLogo (content : Array Ir.Inline)
  /-- An elaborated picture placed with its left edge at page x; `leaf` is its `.picture` leaf,
  `origin` its ordinal among the collected pictures. -/
  | picture (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat)
  /-- A float's extent up to its `floatClose`: one
  unbreakable box, placed whole or moved to the next page. -/
  | floatOpen
  | floatClose
  /-- An in-document anchor, attached to the page the next committed line lands on. -/
  | anchor (slug : String)
  /-- A title slot opens (`Ir.TitleSlot`), saving where it starts. -/
  | slotOpen
  /-- The slot closes: its lines and fills move as one
  box to the page point it is pinned to (`slotShift`). -/
  | slotClose (spec : SlotSpec)
  /-- `\vspace*`'s zero rule (`Ir.pageAnchorRole`), which keeps the glue after it at a page top. -/
  | anchorRule (parskip : Glue)
  /-- `\nointerlineskip` (`Ir.noInterlineRole`). -/
  | noInterline
  /-- A display a picture stands for opens here (`Ir.displayPicture?`),
  its skip above chosen as a display line's. -/
  | displayOpen (dj : DisplayJob) (left size : Sp)

/-- A paragraph's op, its breaks computed in parallel from collection on. -/
private def Op.ofPara (j : ParaJob) : Op := .para j (Task.spawn fun _ => j.breaks)

/-- The block walk's read-only context: geometry, faces,
styles, and the class and deck settings in force. -/
public structure Spacing.Context where
  private mk ::
  private geom : Geom
  private xHeight : Sp
  /-- The font the class's preamble set, in which a table's
  undeclared rule weights and seps resolve (`Ir.PreambleFace`). -/
  private preamble : Ir.PreambleFace
  /-- Hyphenation patterns; display type and verbatim walk with `none`. -/
  private pats : Option Hyphen.Patterns := none
  private fs : FontSet
  private styles : Ir.Styles := {}
  /-- The caption positions the document declares. -/
  private captionPos : Array (String × Ir.CaptionPos) := #[]
  /-- The document's main locale, in which generated class furniture is worded. -/
  private locale : Locale := Locale.en
  /-- The `slides` class: frames and out-of-frame sections open fresh pages. -/
  private slides : Bool := false
  /-- A frame body owns its headings: they neither open section dividers
  nor replace the enclosing top-level section or its footer. -/
  private inFrame : Bool := false
  /-- Where the class's list spacing comes from (`Ir.listSkips`). -/
  private lists : Ir.ListLineage := .sizeFile
  /-- The deck's frame-alignment keys (`Ir.Doc.frameKeys`). -/
  private frameKeys : Ir.FrameKeys := .beamer
  /-- Every frame's label at its body index (`Ir.Doc.frameLabels`). -/
  private frameLabels : Array (Option String) := #[]
  /-- The walk is inside a frame whose lists set with
  beamer's squeezed spacing (`Ir.frameSqueeze`). -/
  private squeeze : Bool := false
  /-- The walk is inside a frame declared `[allowframebreaks]`. -/
  private breakableFrame : Bool := false
  /-- The walk is inside a box (`Ir.Block.listScope`), where
  a fill stretches nothing the page's leftover reaches. -/
  private boxed : Bool := false
  /-- The list or quote being collected opened inside an open paragraph
  (`Ir.inParagraphRole`), so its `\topsep` takes no `\partopsep`. -/
  private inPar : Bool := false
  /-- The document's loaded images, which layout measures and places. -/
  private imgs : Image.Store := {}
  /-- Native-picture source openings, on the structure leaves the collector allocates. -/
  private pictureSpans : Array (Nat × Span) := #[]
  /-- The walk is inside a float, whose paragraphs are uncounted box content. -/
  private inFloat : Bool := false
  /-- The headline band a headline class draws on each frame page (`Doc.headline`). -/
  private headline : Option Ir.Headline := none
  /-- The overlay step the page being collected is (`Ir.altShowsFirst`); 1 with no overlay. -/
  private step : Nat := 1
  /-- The steps of the frame being collected (`Ir.frameSteps`); zero outside a frame. -/
  private steps : Nat := 0
  /-- Inside a declared title slot (`Ir.TitleSlot`),
  whose part templates already wrap what they set. -/
  private slotTitle : Bool := false
  /-- Exact title-part size and optional baseline skip, resolved at the
  slot boundary and scoped to that slot. -/
  private roleMetrics : List (String × (Sp × Option Sp)) := []
  /-- For each part that opens a later line, TeX's baseline skip in force on that line. -/
  private roleBaselines : List (String × Sp) := []
  /-- The gap above the footline band: the document's
  furniture gap, else beamer's 4 pt (`Ir.footline.sep`). -/
  private footGap : Sp := Ir.footline.sep
  /-- A centred scope sets this block as one box of its line (`collectCentered`),
  so a lone box row takes the centre's share of its slack. -/
  private centreBoxes : Bool := false
  /-- Where the display being collected stands in its paragraph (`Ir.DisplayCtx`). -/
  private display : Ir.DisplayCtx := {}
  /-- The document's cover (`Ir.Design.cover`), from `run`. -/
  private cover : Option Ir.Cover := none
  /-- Inside an overlay step this page does not show, the cover a colour resolved
  here takes, as beamer's `\opaqueness` covers a covered step's colours. -/
  private covering : Option Ir.Cover := none
  /-- The surface the document was written in (`Ir.Doc.surface`). -/
  private surface : Ir.Surface := .tex

private abbrev Rd := Spacing.Context

/-- The threaded state of the block walk: only what
it writes, everything it reads riding in `Rd`. -/
public structure Spacing.Pending where
  private mk ::
  /-- The right edge paragraphs break against, from the page's
  left margin: the text width unless a column narrows it. -/
  private measure : Option Sp := none
  /-- The document's palette, whose semantic keys drive the themed furniture. -/
  private pal : Ir.Palette := {}
  private paletteEpoch : Nat := 0
  private tokens : Ir.Tokens := {}
  /-- Default text colour: the palette's `fg` when declared, else black. -/
  private fg : Ir.Color := Ir.Color.black
  /-- The surface content collected here stands on: the palette
  epoch's `bg`, overridden where a bar or an inversion resolves. -/
  private ground : Option Ir.Color := none
  /-- The enclosing painted body's ground, surviving a palette declaration. -/
  private bodyGround : Option Ir.Color := none
  private bodyInk : Option (Ir.ColorRef × Ir.Color) := none
  /-- The number of the frame being collected, from `Ir.frameNumbers`; `none` for a title frame. -/
  private frameNum : Option Nat := none
  /-- The frame's label, from `Ir.Doc.frameLabels` by the same driver. -/
  private frameLabel : Option String := none
  /-- The open frame's overflow policy (`FrameOpening.fit`). -/
  private frameFit : FrameFitMode := .spill
  /-- Source frame and overlay from the top-level driver. -/
  private frameOrigin : Option FrameOrigin := none
  /-- Source declaration, before an overlay makes several collected frames. -/
  private frameSource : Option Span := none
  /-- Countable frames elapsed at this point, the deck
  position a section page's progress bar shows. -/
  private framesDone : Nat := 0
  /-- The numbering's denominator, `Ir.frameCount`. -/
  private frameCount : Nat := 0
  /-- Nesting depth of the list being walked, one counter per list
  kind as LaTeX counts them (`\@itemdepth`, `\@enumdepth`). -/
  private itemDepth : Nat := 0
  private enumDepth : Nat := 0
  /-- The marker of the list item a disclosure opens, until its summary line takes it. -/
  private itemMarker : Option (Array Ir.Inline) := none
  /-- Quotations open around the walk, which LaTeX's `\@listdepth` counts beside the lists. -/
  private quoteDepth : Nat := 0
  /-- Diagnostics the block walk itself raises, joined into the placement diagnostics by `run`. -/
  private diags : Array Diag := #[]
  /-- The chrome footer's slots when a themed deck draws one; both `none` turns the footer off. -/
  private chromeL : Option Ir.ChromeSlot := none
  private chromeR : Option Ir.ChromeSlot := none
  private standoutNote : Option Bool := none
  /-- Whether the document's pages may carry a chrome footer: slides without a `\runningfoot`. -/
  private footAllowed : Bool := false
  /-- The `\framefoot` note in force, which takes the
  footer's left slot until an empty one clears it. -/
  private frameFoot : Option (Array Inline) := none
  /-- Title of the section in force: what a `\sectiontitle` slot shows. -/
  private curSection : Array Inline := #[]
  private wantDefault : Bool := false
  /-- A document `\vskip` stands in the owed glue, so it adds to the
  peer gap rather than replacing it (`Spacing.Pending.gapGlue`). -/
  private declaredSkip : Bool := false
  /-- A list's `\topsep` or `\itemsep` stands in the owed glue,
  so the paragraph after it adds TeX's `\parskip` on top. -/
  private trivOwed : Bool := false
  /-- A display heading was the last thing set, so a list's first `\item`
  spends `\@nbitem` (latex.ltx); cleared by the next line's gap. -/
  private afterHeading : Bool := false
  /-- A frame's body just opened (`Op.bodyOpen`), so beamer's `\vskip-\parskip`
  cancels the first paragraph's peer gap; cleared by the next line's gap. -/
  private frameTop : Bool := false
  /-- Where `\vspace*`'s rule stands in the owed glue, before `owed[k]` (`Ir.pageAnchorRole`). -/
  private anchorAt : Option Nat := none
  private owed : Array Glue := #[]
  /-- The glue owed after a display under TeX's short skip below it,
  beside `owed`'s long one; `none` while no display's skip is owed. -/
  private dispAlt : Option (Array Glue) := none
  private ops : Array Op := #[]
  private hyphCache : Std.HashMap String (Array Nat) := {}
  /-- Links of the unpinned navigation landmarks met
  so far, as (text, target), in document order. -/
  private navEntries : Array (String × String) := #[]
  /-- The next structure leaf the walk attributes, advanced through
  `leafRange` at exactly the sites `Struct.blockRaw` enumerates leaves. -/
  private leafNext : Nat := 0
  /-- The pictures collected so far, the next one's ordinal. -/
  private pictures : Nat := 0
  /-- The next paragraph opens a TeX box (`TexBox`), an
  untitled block's body opening its template's box. -/
  private boxOpener : Option TexBox := none

private abbrev Acc := Spacing.Pending

/-- Claim the next `n` leaves for one block of set text: its first
leaf, `none` when it owns none, and the counter past them. -/
private def Spacing.Pending.leafRange (a : Acc) (n : Nat) : Acc × Option Nat :=
  ({ a with leafNext := a.leafNext + n }, if n == 0 then none else some a.leafNext)

/-- A declared length with its rubber, all three parts kept. -/
private def Spacing.Context.resolve (r : Rd) (g : SymGlue) : Glue :=
  g.resolve r.geom.fontSize r.xHeight

private def Spacing.Context.parskip (r : Rd) : Glue := r.resolve r.geom.parskip

/-- A colour resolved at layout, as the step being collected shows it. -/
private def Spacing.Context.shown (r : Rd) (c : Ir.Color) : Ir.Color :=
  match r.covering with
  | some cover => cover.of c
  | none => c

/-- Whether an overlay carrier's content is invisible on the step being collected. -/
private def Spacing.Context.hides (r : Rd) (spec : Ir.OverlaySpec) : Bool :=
  spec.hidesAt r.step r.steps

/-- The context a pending overlay step's content is collected in: covered unless it hides. -/
private def Spacing.Context.pendingStep (r : Rd) (spec : Ir.OverlaySpec) : Rd :=
  if spec.pending r.step && !spec.invisible then { r with covering := r.cover } else r

/-- Open a hidden region: what the walk collects until it closes keeps its place and ships nothing. -/
private def Spacing.Pending.openHidden (a : Acc) : Acc := { a with ops := a.ops.push (.regionOpen .hidden) }

private def Spacing.Pending.closeHidden (a : Acc) : Acc := { a with ops := a.ops.push .regionClose }

/-- A list level's `\leftmargin` at `\@listdepth` `lv`: the
document's own, else the class's, else the engine's indent. -/
private def Spacing.Context.leftMargin (r : Rd) (lv : Nat) (tokens : Ir.Tokens) : Sp :=
  match tokens.find? (Ir.leftMarginName lv) with
  | some g => (r.resolve g).width
  | none => (Ir.leftMargin r.lists r.geom.fontSize lv).getD r.geom.listIndent

/-- The next line is a peer of the last: the default gap, unless something
is declared. -/
private def Spacing.Pending.wantGap (a : Acc) : Acc := { a with wantDefault := true }

/-- `\vskip`: glue the document asked for, on top of whatever is owed. -/
private def Spacing.Pending.vskip (a : Acc) (g : Glue) : Acc :=
  { a with owed := a.owed.push g, declaredSkip := true, dispAlt := a.dispAlt.map (·.push g) }

/-- `\vspace`: latex.ltx's `\@vspace`, `\vskip #1` then
`\vskip\z@skip`, so the next `\addvspace` adds to it. -/
private def Spacing.Pending.vspace (a : Acc) (g : Glue) : Acc :=
  { a with owed := (a.owed.push g).push {}, declaredSkip := true
           dispAlt := a.dispAlt.map fun o => (o.push g).push {} }

/-- `Spacing.Pending.addvspace` on owed glue alone. -/
private def addvOwed (owed : Array Glue) (g : Glue) : Array Glue :=
  match owed.back? with
  | some last =>
    if last.width == 0 then owed.push g
    else if last.width < g.width then owed.pop.push g else owed
  | none => #[g]

/-- `\addvspace`: an element's own space, the larger by natural width
against glue already owed, or added where that is zero (ltspace.dtx). -/
private def Spacing.Pending.addvspace (a : Acc) (g : Glue) : Acc :=
  let a := { a with dispAlt := a.dispAlt.map (addvOwed · g) }
  match a.owed.back? with
  | some last =>
    if last.width == 0 then { a with owed := a.owed.push g, declaredSkip := false }
    else if last.width < g.width then { a with owed := a.owed.pop.push g } else a
  | none => { a with owed := #[g] }

private theorem addvspace_zero_adds_exact (a : Acc) (g last : Glue)
    (hl : a.owed.back? = some last) (h0 : last.width = 0) :
    (a.addvspace g).owed = a.owed.push g := by
  simp [Spacing.Pending.addvspace, hl, h0]

/-- A trivlist's own space (`\topsep`): an `\addvspace`,
paid on top of the peer gap (ltlists.dtx `\@trivlist`). -/
private def Spacing.Pending.trivSpace (a : Acc) (g : Glue) : Acc :=
  { a.addvspace g with declaredSkip := true }

/-- A list's own space (`\topsep`, `\itemsep`): the
trivlist's `\addvspace` with TeX's own `\parskip` on top. -/
private def Spacing.Pending.listSpace (a : Acc) (g : Glue) : Acc :=
  { a.addvspace g with declaredSkip := true, trivOwed := true }

/-- A list's opening space: the trivlist's `\addvspace`, except under
beamer, whose colour push makes `\addvspace` add the `\topsep`. -/
private def Spacing.Pending.listOpen (a : Acc) (r : Rd) (g : Glue) : Acc :=
  match r.lists with
  | .beamer => { a.vskip g with trivOwed := true }
  | .sizeFile | .web => a.listSpace g

private theorem listOpen_beamer_adds_exact (a : Acc) (r : Rd) (g : Glue)
    (h : r.lists = .beamer) : (a.listOpen r g).owed = a.owed.push g := by
  simp [Spacing.Pending.listOpen, Spacing.Pending.vskip, h]

private theorem addvspace_after_vspace_exact (a : Acc) (v g : Glue) :
    ((a.vspace v).addvspace g).owed = (a.vspace v).owed.push g ∧
    ((a.vspace v).trivSpace g).owed = (a.vspace v).owed.push g ∧
    ((a.vspace v).listSpace g).owed = (a.vspace v).owed.push g := by
  have h := addvspace_zero_adds_exact (a.vspace v) g {} (by simp [Spacing.Pending.vspace]) rfl
  exact ⟨h, h, h⟩

/-- After a primitive `\vskip`, an `\addvspace` compares with
the skip itself, as latex.ltx's `\@xaddvskip` takes it. -/
private def Spacing.Pending.primitiveSkip (a : Acc) : Acc :=
  let drop (o : Array Glue) : Array Glue := if o.back? = some {} then o.pop else o
  { a with owed := drop a.owed, dispAlt := a.dispAlt.map drop }

private theorem addvspace_after_vskip_exact (a : Acc) (v g : Glue) (hv : v.width ≠ 0)
    (hg : ¬ v.width < g.width) :
    (((a.vspace v).primitiveSkip).addvspace g).owed = a.owed.push v := by
  simp [Spacing.Pending.primitiveSkip, Spacing.Pending.vspace, Spacing.Pending.addvspace,
    hv, hg]

/-- The glue one boundary pays: the declared glue owed, with the page's
parskip on top where a document skip stands at a peer boundary. -/
private def Spacing.Pending.gapGlue (a : Acc) (r : Rd) : Glue :=
  let declared := a.owed.foldl Glue.add {}
  let par := if a.trivOwed then r.resolve r.geom.texParskip else r.parskip
  if a.wantDefault && a.declaredSkip then par.add declared else declared

/-- The boundary around `\vspace*`'s rule: the peer mark and the glue before
the rule, then the rule with TeX's `\parskip`, then the glue after it. -/
private def Spacing.Pending.flushAnchored (a : Acc) (r : Rd) (k : Nat) : Acc :=
  let par := if a.trivOwed then r.resolve r.geom.texParskip else r.parskip
  let lead := if a.wantDefault && a.declaredSkip then #[Op.skip par] else #[]
  { a with ops := a.ops ++ lead ++
      #[.skip ((a.owed.extract 0 k).foldl Glue.add {}),
        .anchorRule (r.resolve r.geom.texParskip),
        .skip ((a.owed.extract k a.owed.size).foldl Glue.add {})] }

/-- The op the owed glue `g` ships as, beside its
short-skip twin while a display's skip below is owed. -/
private def Spacing.Pending.owedOp (a : Acc) (g : Glue) : Op :=
  match a.dispAlt with
  | none => .skip g
  | some alt => .skipAlt g (alt.foldl Glue.add {})

/-- Emit the gap owed, just before a line is placed; a stacked
boundary ships the peer mark first and the declared glue after it. -/
private def Spacing.Pending.flushGap (a : Acc) (r : Rd) : Acc :=
  let par := if a.trivOwed then r.resolve r.geom.texParskip else r.parskip
  let a := match a.anchorAt with
    | some k => a.flushAnchored r k
    | none =>
      if a.owed.isEmpty then
        (if a.wantDefault then { a with ops := a.ops.push (.skip r.parskip) } else a)
      else if a.wantDefault && a.declaredSkip then
        { a with ops := (a.ops.push (.skip par)).push (a.owedOp (a.owed.foldl Glue.add {})) }
      else { a with ops := a.ops.push (a.owedOp (a.gapGlue r)) }
  { a with wantDefault := false, owed := #[], declaredSkip := false, trivOwed := false,
           afterHeading := false, frameTop := false, anchorAt := none, dispAlt := none }

private theorem flushGap_items_exact (a : Acc) (r : Rd) (ho : a.owed.isEmpty = false)
    (hs : (a.wantDefault && a.declaredSkip) = true) (hk : a.anchorAt = none)
    (hd : a.dispAlt = none) :
    let par := if a.trivOwed then r.resolve r.geom.texParskip else r.parskip
    (a.flushGap r).ops = (a.ops.push (.skip par)).push (.skip (a.owed.foldl Glue.add {})) ∧
      par.add (a.owed.foldl Glue.add {}) = a.gapGlue r := by
  intro par
  exact ⟨by simp [Spacing.Pending.flushGap, Spacing.Pending.owedOp, ho, hs, hk, hd, par], by simp [Spacing.Pending.gapGlue, hs, par]⟩

private theorem glue_width_le_add (x y : Glue) (hy : (0 : Int) ≤ y.width) :
    x.width ≤ (x.add y).width := by
  simpa [Glue.add] using Int.add_le_add_left hy x.width

private theorem glue_width_le_add_left (x y : Glue) (hx : (0 : Int) ≤ x.width) :
    y.width ≤ (x.add y).width := by
  simpa [Glue.add] using Int.add_le_add_right hx y.width

private theorem skip_monotone (a : Acc) (r : Rd) (g : Glue)
    (hg : (0 : Int) ≤ g.width) (hp : (0 : Int) ≤ r.parskip.width)
    (hq : (0 : Int) ≤ (r.resolve r.geom.texParskip).width) :
    (a.gapGlue r).width ≤ ((a.vspace g).gapGlue r).width := by
  have hf : ((a.vspace g).owed.foldl Glue.add {}) = (a.owed.foldl Glue.add {}).add g := by
    simp [Spacing.Pending.vspace, Glue.add]
  have hd : (a.vspace g).declaredSkip = true := rfl
  have hw : (a.vspace g).wantDefault = a.wantDefault := rfl
  have ht : (a.vspace g).trivOwed = a.trivOwed := rfl
  have hpar : (0 : Int) ≤ (if a.trivOwed then r.resolve r.geom.texParskip else r.parskip).width := by
    split <;> assumption
  simp only [Spacing.Pending.gapGlue, hf, hd, hw, ht, Bool.and_true]
  generalize (if a.trivOwed then r.resolve r.geom.texParskip else r.parskip) = par at hpar ⊢
  cases hwd : a.wantDefault
  · simpa [hwd] using glue_width_le_add (a.owed.foldl Glue.add {}) g hg
  · cases hds : a.declaredSkip
    · simpa [hwd, hds] using Int.le_trans (glue_width_le_add (a.owed.foldl Glue.add {}) g hg)
        (glue_width_le_add_left par ((a.owed.foldl Glue.add {}).add g) hpar)
    · simpa [hwd, hds, Glue.add] using
        Int.add_le_add_left (glue_width_le_add (a.owed.foldl Glue.add {}) g hg) par.width

private theorem flushGap_default_exact (a : Acc) (r : Rd)
    (howed : a.owed.isEmpty = true) (hw : a.wantDefault = true) (hk : a.anchorAt = none) :
    (a.flushGap r).ops = a.ops.push (.skip r.parskip) := by
  simp [Spacing.Pending.flushGap, howed, hw, hk]

private theorem heading_default_before_exact (r : Rd) :
    ((r.parskip).add (r.parskip)).width = 2 * r.parskip.width := by
  simp [Glue.add, Int.two_mul]

/-- A page boundary: the gap owed stands before the break
and is the old page's own, and the new page starts clean. -/
private def Spacing.Pending.pageBreak (a : Acc) : Acc :=
  let a := if a.owed.isEmpty then a
    else { a with ops := a.ops.push (a.owedOp (a.owed.foldl Glue.add {})) }
  { a with ops := a.ops.push .brk, wantDefault := false, owed := #[], declaredSkip := false,
           trivOwed := false, afterHeading := false, frameTop := false, anchorAt := none,
           dispAlt := none }

private def Spacing.Pending.pushOp (a : Acc) (op : Op) : Acc :=
  { a with ops := a.ops.push op }

private def Spacing.Context.style (r : Rd) (element : String) : Ir.ElementStyle :=
  (r.styles.find? element).getD {}

/-- The default ink a palette implies: its `fg` when declared, else black. -/
private def fgOf (pal : Ir.Palette) : Ir.Color :=
  (Ir.Design.at pal .print .ink).getD Ir.Color.black

/-- `.setPalette` on the accumulator: the palette, default ink and
surface change together, and the page ground rides as a state op. -/
private def Spacing.Pending.setPalette (a : Acc) (p : Ir.Palette) : Acc :=
  { a with pal := p, paletteEpoch := a.paletteEpoch + 1
           fg := fgOf p, bodyInk := none, ground := a.bodyGround.or (Ir.Design.declared? p .page)
           ops := a.ops.push (.pageGround (Ir.Design.declared? p .page)) }

private def Spacing.Pending.setTokens (a : Acc) (tk : Ir.Tokens) : Acc :=
  { a with tokens := tk }

private theorem Spacing.Pending.setPalette_emits_no_content (a : Acc) (p : Ir.Palette) :
    (a.setPalette p).ops = a.ops.push (.pageGround (Ir.Design.declared? p .page)) ∧
      (a.setPalette p).owed = a.owed ∧
      (a.setPalette p).wantDefault = a.wantDefault ∧
      (a.setPalette p).diags = a.diags :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem Spacing.Pending.setTokens_emits_nothing (a : Acc) (tk : Ir.Tokens) :
    (a.setTokens tk).ops = a.ops ∧ (a.setTokens tk).owed = a.owed ∧
      (a.setTokens tk).wantDefault = a.wantDefault ∧
      (a.setTokens tk).diags = a.diags :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Capture the frame's source and policy inputs together. -/
private def Spacing.Pending.frameOpening (a : Acc) (standout : Bool)
    (area : FrameArea := .margins) :
    FrameOpening :=
  { origin := a.frameOrigin, number := a.frameNum, label := a.frameLabel, fit := a.frameFit
    chrome := { footerLeft := a.chromeL, footerRight := a.chromeR,
                standoutNote := a.standoutNote }
    note := a.frameFoot, sectionTitle := a.curSection, count := a.frameCount
    standout := standout, allowed := a.footAllowed, palette := a.pal, area }

/-- The one footer decision collection and body measurement
read; an authored running footer suppresses chrome. -/
private def Spacing.Pending.selectedFoot (a : Acc) (standout : Bool) :
    Option (Array Ir.BandSlot) :=
  (a.frameOpening standout).footer

/-- Zero-ink targets follow the line carrying their
next item; trailing targets stay on the last line. -/
private def lineAnchors (anchors : Array (String × Nat)) (prev brk : Nat)
    (first last : Bool) : Array String :=
  (anchors.filter fun (_, i) => (first || prev ≤ i) && (i < brk || last)).map (·.1)

private def collectPara (r : Rd) (a : Acc)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (marker : Option (Array Inline) := none)
    (markerIndent : Option Sp := none)
    (markerLeft : Option Sp := none)
    (rule : Option HeadingRule := none)
    (display : Bool := false)
    (leaf : Option Nat := none) (span : Nat := 0) (keepNext : Sp := 0)
    (hangIndent : Sp := 0) (literalLines : Bool := false)
    (dispJob : Option DisplayJob := none) (paintPadding : Option Sp := none)
    (rowStrut : Option (Sp × Sp) := none) (strut : Option Sp := none)
    (inserted : Bool := false) (background : Sp := 0)
    (urlBreaks : Bool := r.surface == .markdown)
    (texBox : Option TexBox := none) : Acc :=
  let texBox := texBox.orElse fun _ => a.boxOpener
  let a := { a.flushGap r with boxOpener := none }
  let indent := indent + hangIndent
  -- Inside a column the measure is the column's, as a minipage's `\textwidth` is (latex.ltx).
  let measure := (a.measure.getD r.geom.textWidth) - indent
  let firstBaseline := match inlines[0]? with
    | some (.role n _) => r.roleBaselines.lookup n
    | _ => none
  -- The page's text colour is the default; content that declared its own keeps it.
  let baseStyle := if baseStyle.color == Ir.Color.black then
      { baseStyle with color := a.fg } else baseStyle
  let baseStyle := { baseStyle with ground := a.ground, urlBreaks := urlBreaks }
  let (items, ds, cache, extras, rawNotes, wordOffsets, anchors, itemSources) :=
    itemsOfInlines r.pats size r.xHeight r.fs baseStyle inlines a.hyphCache
      (LeafCtr.of leaf span inlines) r.imgs measure r.geom.textHeight (noteOk := true)
      (ladder := r.geom.scale) (step := r.step) (roleMetrics := r.roleMetrics)
      (steps := r.steps)
  -- Listings break only at declared whitespace, never at an identifier's hyphen.
  let items := if literalLines then items.map (fun item => match item with
    | .pen w cost flag f c gs =>
      .pen w (if cost ≤ forcedCost then cost else 10000) flag f c gs
    | item => item) else items
  -- LaTeX's ragged settings leave every line's slack free (`kp`'s `fil`); displays stay balanced.
  let rightFil := !display && !literalLines && ((!r.geom.justify && r.geom.raggedFil) || center)
  let items :=
    if r.geom.justify || rightFil then items
    else if display then
      displayItems measure items
    else raggedItems items
  -- Each footnote is a pre-broken block on the full measure, its mark abutting the text.
  let (noteBlocks, ds, cache) : Array (Nat × NoteBlock) × Array Diag ×
      Std.HashMap String (Array Nat) := Id.run do
    if rawNotes.isEmpty then return (#[], ds, cache)
    let mut out : Array (Nat × NoteBlock) := #[]
    let mut ds := ds
    let mut cache := cache
    -- The note sets in the body's `\footnotesize`, as `\@footnotetext` declares.
    let noteStyle := applyStyle r.geom.scale { color := a.fg, ground := a.ground }
      (.size "footnotesize")
    let noteSize := Ir.scaleStepIn r.geom.scale r.geom.fontSize "footnotesize"
    let noteLead := Ir.stepLead r.geom.skips "footnotesize" r.geom.fontSize
    let sep := r.geom.fontSize * 665 / 1000
    let bodyFont := r.fs.get (r.fs.lookup 0 400 false)
    let scaleB (v : Int) : Sp := v * r.geom.fontSize / bodyFont.unitsPerEm
    let target := r.geom.textWidth
    for (markIdx, num, body, noteLeaf) in rawNotes do
      let (nitems0, nds, cache2, _, _, _, nanchors, nsources) :=
        itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs noteStyle body
          cache (LeafCtr.of noteLeaf (Struct.leafCountInlines body) body) r.imgs r.geom.textWidth
          r.geom.textHeight (ladder := r.geom.scale) (step := r.step) (steps := r.steps)
      ds := ds ++ nds
      cache := cache2
      let (mk, miss) :=
        markBox r.fs { color := a.fg, ground := a.ground } noteSize {} num
      for (idx, c) in miss do
        ds := ds.push (Diag.of .E0405
          s!"'{(r.fs.get idx).family}' has no glyph for '{c}'"
          (trigger := String.singleton c) (recovery := some .skipped) (output := some .pdf))
      let nitems := #[mk] ++ nitems0
      let nsources := nsources.map (fun (i, span) => (i + 1, span))
      let nitems := if r.geom.justify then nitems else raggedItems nitems
      let breaks := kpTwoPass nitems target
      let mut lines : Array LineOut := #[]
      let mut yPrev : Sp := 0
      let mut belowPrev : Sp := 0
      let mut hgt : Sp := 0
      let mut depth : Sp := 0
      let mut prev := 0
      let mut first := true
      for brk in breaks do
        let s := if first then lineStart nitems 0 else lineStart nitems (prev + 1)
        let (lsegs, lw, overfull, _, _) :=
          setLine nitems s brk target (setsToMeasure r.geom.justify nitems s brk) false false
        if overfull then
          ds := ds.push (Diag.of .W0005 "overfull line; no feasible break"
            (span := lineSource nsources s brk)
            (subject := some (overfullSubject (lineSource nsources s brk)))
            (output := some .pdf))
        let box := lineExtent r.fs r.geom.fontSize (scaleB bodyFont.ascent)
          (scaleB bodyFont.capHeight) (scaleB (-bodyFont.descent))
          r.geom.leading noteSize lsegs noteLead
        let y := if first then max box.above sep else yPrev + belowPrev + box.above
        lines := lines.push { x := r.geom.hmargin, y := y, size := noteSize,
                              segs := lsegs, setWidth := lw, note := true, leaf := noteLeaf,
                              anchors := lineAnchors (nanchors.map (fun (n, i) => (n, i + 1)))
                                prev brk first (brk == breaks.back?.getD 0) }
        hgt := y + box.inkBelow
        depth := box.inkBelow
        yPrev := y
        belowPrev := box.below
        prev := brk
        first := false
      out := out.push (markIdx, { lines := lines, height := hgt, depth := depth })
    return (out, ds, cache)
  -- A marker is content set as its own unjustified line; its diagnostics ride with the paragraph's.
  let (markerSegs, ds, cache) := match marker with
    | some m =>
      let (mi, mds, cache, _, _) :=
        itemsOfInlines r.pats size r.xHeight r.fs { color := a.fg, ground := a.ground } m cache
          (.fixed .label) r.imgs measure r.geom.textHeight (ladder := r.geom.scale)
          (step := r.step) (steps := r.steps)
      let (segs, w, _, _) := setLine mi (lineStart mi 0) (mi.size - 1) r.geom.textWidth false
      (some (segs, w), ds ++ mds, cache)
    | none => (none, ds, cache)
  -- A hanging indent opens the items with its kern; item-indexed data moves with them.
  let (items, extras, noteBlocks, wordOffsets, anchors, itemSources) :=
    if hangIndent == 0 then (items, extras, noteBlocks, wordOffsets, anchors, itemSources)
    else (#[Item.box (-hangIndent) 0 a.fg none #[] size {} {} 0 a.ground .unattributed] ++ items,
      extras.fold (fun m k v => m.insert (k + 1) v) {},
      noteBlocks.map (fun (i, nb) => (i + 1, nb)),
      wordOffsets.fold (fun m k v => m.insert (k + 1) v) {},
      anchors.map (fun (n, i) => (n, i + 1)),
      itemSources.map (fun (i, span) => (i + 1, span)))
  -- A paragraph set wholly in one named size stands on that step's strut (`Ir.paraStep?`).
  let step := if inserted then Ir.insertedStep? r.geom.scale inlines else Ir.paraStep? inlines
  let strutSize := match step with
    | some n => Ir.scaleStepIn r.geom.scale size n
    | none => size
  { a with
    hyphCache := cache
    ops := a.ops.push (Op.ofPara {
      items := items, extras := extras, wordOffsets := wordOffsets, anchors := anchors
      itemSources := itemSources, diags := ds
      target := measure
      indent := indent, center := center, size := strutSize
      lead := step.bind (Ir.stepLead r.geom.skips · size)
      firstBaseline := firstBaseline
      paintPadding := paintPadding
      strut := strut
      texBox := texBox
      flushRight := r.geom.flushRight
      justify := r.geom.justify
      rightFil := rightFil
      protrude := r.geom.protrude
      expand := r.geom.expand
      markerSegs := markerSegs, markerIndent := markerIndent, markerLeft := markerLeft
      hangIndent := hangIndent
      rule := rule
      notes := noteBlocks
      inFloat := r.inFloat
      leaf := leaf
      keepNext := keepNext
      display := dispJob
      rowStrut := rowStrut
      background := background
      -- premise: markdownWarningChecks — a markdown hard break declares no line (no W0386).
      declaresLines := r.surface != .markdown }) }

/-- The weight of a heading's declared rule: 0.06 em of the base,
relating to the stroke weight of the text it cuts (Hochuli). -/
private def headingRuleWeight (base : Sp) : Sp := base * 6 / 100

/-- Heading display sizes at the page's body size, the type scale's steps (`Ir.headingSize`). -/
@[expose] public def sectionSize (geom : Geom) : Ir.HeadingLevel → Sp :=
  Ir.headingSize geom.fontSize

public theorem scaleStep_monotone (base : Int)
    (hb : pt 1 ≤ base) : -- 1 pt floor: what strictness costs under integer division
    ∀ q ∈ Ir.sizeScale.zip Ir.sizeScale.tail,
      Ir.scaleStep base q.1.1 < Ir.scaleStep base q.2.1 := by
  have hb' : (65536 : Int) ≤ base := hb
  intro q hq
  simp only [Ir.sizeScale, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h|h|h|h|h|h|h|h|h <;> subst h <;>
    first
    | (show base * 500 / 1000 < base * 700 / 1000; omega)
    | (show base * 700 / 1000 < base * 800 / 1000; omega)
    | (show base * 800 / 1000 < base * 900 / 1000; omega)
    | (show base * 900 / 1000 < base * 1000 / 1000; omega)
    | (show base * 1000 / 1000 < base * 1200 / 1000; omega)
    | (show base * 1200 / 1000 < base * 1440 / 1000; omega)
    | (show base * 1440 / 1000 < base * 1728 / 1000; omega)
    | (show base * 1728 / 1000 < base * 2074 / 1000; omega)
    | (show base * 2074 / 1000 < base * 2488 / 1000; omega)

public theorem titleSize_monotone (base : Int)
    (hb : pt 1 ≤ base) : -- 1 pt floor: what strictness costs under integer division (scaleStep_monotone)
    Ir.titleSize base true < Ir.titleSize base false :=
  scaleStep_monotone base hb (("Large", 1440), ("LARGE", 1728)) (by decide)

public theorem heading_hierarchy (g : Geom)
    (hfs : pt 1 ≤ g.fontSize) : -- 1 pt floor: what strictness costs under integer division (scaleStep_monotone)
    sectionSize g 1 > sectionSize g 2 ∧ sectionSize g 2 ≥ g.fontSize := by
  have h12 := scaleStep_monotone g.fontSize hfs
    (("large", 1200), ("Large", 1440)) (by decide)
  have h01 := scaleStep_monotone g.fontSize hfs
    (("normalsize", 1000), ("large", 1200)) (by decide)
  have e0 : Ir.scaleStep g.fontSize "normalsize" = g.fontSize := by
    show g.fontSize * 1000 / 1000 = g.fontSize
    exact Int.mul_ediv_cancel _ (by decide)
  rw [e0] at h01
  exact ⟨h12, Int.le_of_lt h01⟩

/-- Display type: headings, frame titles, section-page and standout
text, walked with no hyphenation patterns and ragged setting. -/
private def collectDisplay (r : Rd) (a : Acc)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (rule : Option HeadingRule := none)
    (leaf : Option Nat := none) (span : Nat := 0) (keepNext : Sp := 0)
    (paintPadding : Option Sp := none) (inserted : Bool := false)
    (strut : Option Sp := none) (texBox : Option TexBox := none) : Acc :=
  collectPara { r with pats := none, geom := { r.geom with justify := false } }
    a inlines indent center size (baseStyle := baseStyle) (rule := rule)
    (display := true) (leaf := leaf) (span := span) (keepNext := keepNext)
    (paintPadding := paintPadding) (inserted := inserted) (strut := strut)
    (texBox := texBox)

/-- The natural width of a set of items, penalties adding nothing. -/
private def itemsNaturalWidth (items : Array Item) : Sp :=
  items.foldl (fun w it => match it with
    | .box bw .. => w + bw
    | .glue g | .decoratedGlue g _ => w + g.width
    | .pen .. => w
    | .img _ bw _ _ => w + bw
    | .rule bw .. => w + bw
    | .poly .. => w) 0

/-- The natural width of `content` set at `size` on a line `avail` wide, measured and never
shipped, with the hyphenation cache the measuring warmed. -/
private def Spacing.Pending.naturalWidth (a : Acc) (r : Rd) (size : Sp) (content : Array Inline)
    (avail : Sp) : Sp × Acc :=
  let (items, _, cache, _) :=
    itemsOfInlines r.pats size r.xHeight r.fs { color := a.fg, ground := a.ground } content
      a.hyphCache (.fixed .unattributed) r.imgs avail r.geom.textHeight
      (ladder := r.geom.scale) (step := r.step) (steps := r.steps)
  (itemsNaturalWidth items, { a with hyphCache := cache })

/-- Whether a forced break stands among the items before their
last, making a natural cell lines rather than one line. -/
private def itemsBreak (items : Array Item) : Bool :=
  items.pop.any fun it => match it with
    | .pen _ cost .. => cost ≤ forcedCost
    | _ => false

/-- A natural cell's width as lines: the widest run between forced breaks (CSS Sizing 3, §5.1). -/
private def itemsLinesWidth (items : Array Item) : Sp := Id.run do
  let mut widest : Sp := 0
  let mut run : Sp := 0
  for it in items do
    match it with
    | .box bw .. | .img _ bw _ _ | .rule bw .. => run := run + bw
    | .glue g | .decoratedGlue g _ => run := run + g.width
    | .pen _ cost .. =>
      if cost ≤ forcedCost then
        widest := max widest run
        run := 0
    | .poly .. => pure ()
  return max widest run

/-- The one door the document title renders through: a declared `titlepage`
template wraps it, else it takes display type in bold at its page model's step. -/
private def collectTitle (r : Rd) (a : Acc) (title : Array Inline)
    (indent : Sp) (center : Bool) : Acc :=
  let (a, leaf) := a.leafRange (Struct.leafCountInlines title)
  if r.slotTitle then
    collectDisplay r a title indent center r.geom.fontSize
      (leaf := leaf) (span := Struct.leafCountInlines title)
  else
  match (Ir.titleHeadingStyle (r.style "titlepage")).font with
  | some tpl =>
    collectDisplay r a (Ir.fillTemplate tpl title) indent center r.geom.fontSize
      (leaf := leaf) (span := Struct.leafCountInlines title)
  | none =>
    collectDisplay r a title indent center
      (Ir.titleSize r.geom.fontSize r.slides)
      (baseStyle := { weight := .b }) (leaf := leaf) (span := Struct.leafCountInlines title)

/-- Whether cell `(i, j)` lies inside a `\multicolumn`, which enters no single column's maximum. -/
public def inSpan (spans : Array Ir.ColSpan) (i j : Nat) : Bool :=
  spans.any fun s => s.row == i && s.col ≤ j && j < s.col + s.n

/-- A column's width before spans: an `l`/`c`/`r` column's widest unspanned
cell, a `p{f\linewidth}` its fraction of the measure, a `p{len}` its length. -/
public def colBase (total : Sp) (spans : Array Ir.ColSpan) (nats : Array (Array Sp))
    (j : Nat) (spec : Ir.ColSpec) : Sp :=
  match spec.width with
  | .natural => nats.zipIdx.foldl (init := 0) fun m (r, i) =>
      if inSpan spans i j then m else max m ((r[j]?).getD 0)
  | .sized e => e.resolveWidth (MeasureValues.horizontal total 0)
  | .flex _ => 0

/-- What a span needs across its columns: its text's natural width, or its own `p{…}` width. -/
public def spanNeed (total : Sp) (nats : Array (Array Sp)) (s : Ir.ColSpan) : Sp :=
  match s.spec.width with
  | .natural => ((nats[s.row]?).bind (·[s.col]?)).getD 0
  | .sized e => e.resolveWidth (MeasureValues.horizontal total 0)
  | .flex target => target.resolve total

/-- The box a span sets in: the columns it covers and the `2·colsep` gaps
between them. -/
public def spanBox (colsep : Sp) (widths : Array Sp) (s : Ir.ColSpan) : Sp :=
  let last := min (s.col + s.n) widths.size
  (widths.extract s.col last).foldl (· + ·) 0 + 2 * colsep * ((last : Int) - (s.col : Int) - 1)

/-- Column `j` widened by every span ending at it,
by TeX's rule for a spanned entry (tex.web §801). -/
public def widenAt (colsep total : Sp) (nats : Array (Array Sp)) (spans : Array Ir.ColSpan)
    (widths : Array Sp) (j : Nat) : Array Sp :=
  spans.foldl (init := widths) fun ws s =>
    if 0 < s.n && s.col + s.n == j + 1 && j < ws.size then
      let before := (ws.extract s.col j).foldl (· + ·) 0 + 2 * colsep * ((s.n : Int) - 1)
      ws.set! j (max ws[j]! (spanNeed total nats s - before))
    else ws

public def tableFlexTarget (cols : Array Ir.ColSpec) : Option Ir.TableTarget :=
  cols.findSome? fun c => match c.width with
    | .flex target => some target
    | .natural | .sized _ => none

public def tablePadding (colsep : Sp) (count : Nat) (padL padR : Bool) : Sp :=
  (if padL then colsep else 0) + (if padR then colsep else 0) +
    2 * colsep * ((count : Int) - 1)

/-- Give every flexible column an equal share of what the
target leaves, as tabularx's trial arithmetic (`TX@arith`). -/
public def tableFlexWidths (colsep total fontSize : Sp) (cols : Array Ir.ColSpec)
    (bases : Array Sp) (padL padR : Bool) : Array Sp :=
  let count := cols.foldl (fun n c => if c.width matches .flex _ then n + 1 else n) 0
  match tableFlexTarget cols with
  | none => bases
  | some target =>
    let fixed := cols.zipIdx.foldl (fun sum (c, j) => match c.width with
      | .flex _ => sum
      | .natural | .sized _ => sum + bases[j]?.getD 0) 0
    let remaining := target.resolve total - fixed - tablePadding colsep cols.size padL padR
    -- tabularx.sty: TX@error@width is 1em when the fixed columns exceed the target.
    let share := if remaining < 0 then max 0 fontSize else remaining / max count 1
    cols.mapIdx fun j c => match c.width with
      | .flex _ => share
      | .natural | .sized _ => bases[j]?.getD 0

public theorem tableFlexWidths_flex_contract (colsep total fontSize : Sp) (cols : Array Ir.ColSpec)
    (bases : Array Sp) (padL padR : Bool) (i j : Nat) (ci cj : Ir.ColSpec)
    (ti tj : Ir.TableTarget) (hi : cols[i]? = some ci) (hj : cols[j]? = some cj)
    (hwi : ci.width = .flex ti) (hwj : cj.width = .flex tj) :
    (tableFlexWidths colsep total fontSize cols bases padL padR)[i]? =
      (tableFlexWidths colsep total fontSize cols bases padL padR)[j]? := by
  unfold tableFlexWidths tableFlexTarget
  split
  ·
    rename_i hnone
    exact absurd ((Array.findSome?_eq_none_iff.mp hnone) ci (Array.mem_of_getElem? hi))
      (by rw [hwi]; simp)
  · simp [hi, hj, hwi, hwj]

/-- Bisect a trial interval, keeping a fitting lower endpoint. -/
public def fitTableShare (fits : Nat → Bool) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi + 1) / 2
    if fits mid then fitTableShare fits mid hi
    else fitTableShare fits lo (mid - 1)
  else lo
termination_by hi - lo
decreasing_by all_goals omega

public theorem fitTableShare_contract (fits : Nat → Bool) (lo hi : Nat)
    (h : fits lo = true) : fits (fitTableShare fits lo hi) = true := by
  induction lo, hi using fitTableShare.induct fits with
  | case1 lo hi hlt mid hm ih =>
    rw [fitTableShare, ite_eq_left hlt]
    exact (ite_eq_left hm ▸ ih hm)
  | case2 lo hi hlt mid hm ih =>
    rw [fitTableShare, ite_eq_left hlt]
    exact (ite_eq_right hm ▸ ih h)
  | case3 lo hi hlt =>
    rw [fitTableShare, ite_eq_right hlt]
    exact h

/-- One tabularx trial: equal X widths followed by TeX's span constraints. -/
public def tableFlexTrial (colsep total : Sp) (cols : Array Ir.ColSpec)
    (nats : Array (Array Sp)) (spans : Array Ir.ColSpan) (share : Nat) : Array Sp :=
  let bases := cols.mapIdx fun j c => match c.width with
    | .flex _ => (share : Int)
    | .natural | .sized _ => colBase total spans nats j c
  (List.range cols.size).foldl (widenAt colsep total nats spans) bases

/-- Fit the final span-expanded widths, each X column keeping
the one-em fallback when the span minimums exceed the target. -/
public def tableSpanFlexWidths (colsep total fontSize : Sp) (cols : Array Ir.ColSpec)
    (nats : Array (Array Sp)) (spans : Array Ir.ColSpan) (allocated : Array Sp)
    (budget : Sp) : Array Sp :=
  let trial := tableFlexTrial colsep total cols nats spans
  let fits := fun share => decide ((trial share).foldl (· + ·) 0 ≤ budget)
  let upper := cols.zipIdx.foldl (fun m (c, j) =>
    if c.width matches .flex _ then max m (allocated[j]?.getD 0) else m) 0
  trial (if fits 0 then fitTableShare fits 0 upper.toNat else fontSize.toNat)

/-- A table's column widths: natural tables enforce the
span minimums, flexible ones fit them inside the target. -/
public def tableColWidths (colsep total fontSize : Sp) (cols : Array Ir.ColSpec)
    (nats : Array (Array Sp)) (spans : Array Ir.ColSpan)
    (padL : Bool := true) (padR : Bool := true) : Array Sp :=
  let bases := cols.mapIdx fun j spec => colBase total spans nats j spec
  let bases := tableFlexWidths colsep total fontSize cols bases padL padR
  if spans.isEmpty then bases
  else match tableFlexTarget cols with
    | none => (List.range cols.size).foldl (widenAt colsep total nats spans) bases
    | some target => tableSpanFlexWidths colsep total fontSize cols nats spans bases
        (target.resolve total - tablePadding colsep cols.size padL padR)

/-- Artifact geometry: nonempty spans stay inside the table's
declared target whenever their minimum widths fit. -/
public theorem table_flex_span_width_contract (colsep total fontSize : Int) (cols : Array Ir.ColSpec)
    (nats : Array (Array Sp)) (spans : Array Ir.ColSpan) (padL padR : Bool)
    (target : Ir.TableTarget) (hs : spans.isEmpty = false)
    (ht : tableFlexTarget cols = some target)
    (hf : (tableFlexTrial colsep total cols nats spans 0).foldl (· + ·) 0 ≤
      target.resolve total - tablePadding colsep cols.size padL padR) :
    (tableColWidths colsep total fontSize cols nats spans padL padR).foldl (· + ·) 0 +
      tablePadding colsep cols.size padL padR ≤ target.resolve total := by
  simp only [tableColWidths, hs, Bool.false_eq_true, ↓reduceIte, ht, tableSpanFlexWidths]
  have fit (hi : Nat) := fitTableShare_contract
    (fun share => decide ((tableFlexTrial colsep total cols nats spans share).foldl
      (· + ·) 0 ≤ target.resolve total - tablePadding colsep cols.size padL padR))
    0 hi (by simpa using hf)
  simp only [show decide ((tableFlexTrial colsep total cols nats spans 0).foldl
    (· + ·) 0 ≤ target.resolve total - tablePadding colsep cols.size padL padR) = true
      from by simpa using hf, ↓reduceIte]
  exact Int.add_le_of_le_sub_right (of_decide_eq_true (fit _))

public theorem widenAt_nil (colsep total : Sp) (nats : Array (Array Sp)) (ws : Array Sp)
    (j : Nat) : widenAt colsep total nats #[] ws j = ws := by
  simp [widenAt]

public theorem inSpan_nil (i j : Nat) : inSpan #[] i j = false := by
  simp [inSpan]

public theorem table_natural_width_exact (colsep total fontSize : Sp) (cols : Array Ir.ColSpec)
    (nats : Array (Array Sp)) (padL padR : Bool) :
    tableColWidths colsep total fontSize cols nats #[] padL padR =
      tableFlexWidths colsep total fontSize cols
        (cols.mapIdx fun j spec => colBase total #[] nats j spec) padL padR := by
  simp [tableColWidths]

/-- The side a cell's lines set on in its column box, from its
spec (`Ir.cellSpec`) whatever scope the table stands in. -/
@[expose] public def cellSide (cols : Array Ir.ColSpec) (spans : Array Ir.ColSpan) (i j : Nat) :
    Ir.HAlign :=
  (Ir.cellSpec cols spans i j).align

/-- How a wrapping cell's paragraph sets, `(justify, flushRight, center)`,
from its spec alone: a bare `p` justifies, a ragged modifier sets its side. -/
@[expose] public def cellParagraph (spec : Ir.ColSpec) : Bool × Bool × Bool :=
  (!spec.ragged, spec.ragged && spec.align == .right, spec.ragged && spec.align == .center)

/-- How a natural cell sets when its narrowed column cannot hold it
on one line, `(flushRight, center)`: ragged on the cell's side. -/
@[expose] public def narrowedCell (side : Ir.HAlign) : Bool × Bool :=
  (side == .right, side == .center)

/-- The stretch every line of a narrowed cell carries: plain TeX's
`\raggedright` `\rightskip 0pt plus 2em` at the cell's size. -/
@[expose] public def narrowedSkip (size : Sp) : Sp := 2 * size

/-- The strut every table row stands on: latex.ltx's `\@arstrutbox`,
0.7 and 0.3 of the `\baselineskip` in force where the table opens. -/
@[expose] public def tableStrut (size : Sp) (leading : Nat) : Sp × Sp :=
  let bs := Ir.leadingFor size leading
  (bs * 7 / 10, bs - bs * 7 / 10)

public theorem tableStrut_exact (size : Int) (leading : Nat) :
    (tableStrut size leading).1 + (tableStrut size leading).2 = Ir.leadingFor size leading := by
  simp only [tableStrut]
  have h : ∀ a b : Int, a + (b - a) = b := by intro a b; omega
  exact h _ _

/-- The strut a table cell stands on: `tableStrut` cut from the
`\baselineskip` of the size step over the cell (`Ir.paraStep?`). -/
private def cellStrut (skips ladder : List (String × Nat)) (size : Sp) (leading : Nat)
    (cell : Array Inline) : Sp × Sp :=
  match Ir.paraStep? cell with
  | some n =>
    let bs := Ir.stepSkip (Ir.stepLead skips n size) (Ir.scaleStepIn ladder size n) leading
    (bs * 7 / 10, bs - bs * 7 / 10)
  | none => tableStrut size leading

/-- A table length as the page sets it: the declared token, else the name's
default fixed in the preamble's font (`Ir.PreambleFace.resolve`). -/
@[expose] public def tableLength (declared : Option Sp) (face : Ir.PreambleFace)
    (name : String) : Sp :=
  declared.getD (face.resolve (Ir.tableLengthDefault name))

/-- A cell's min-content width: the widest run of its items between two
legal breaks, a hyphenation point or a formula's break reading as none. -/
private def itemsMinWidth (items : Array Item) : Sp := Id.run do
  let mut widest : Sp := 0
  let mut run : Sp := 0
  for it in items do
    match it with
    | .box w .. => run := run + w
    | .img _ w _ _ => run := run + w
    | .rule w .. => run := run + w
    | .glue _ | .decoratedGlue _ _ =>
      widest := max widest run
      run := 0
    | .pen _ cost flagged _ _ _ =>
      if !flagged && cost < 10000 && cost != (binopPenalty : Int) && cost != (relPenalty : Int) then
        widest := max widest run
        run := 0
    | .poly .. => pure ()
  return max widest run

/-- One narrowed column: its widest unbreakable run `mn` and its `k`-of-`d` share
of the leftover room, in proportion to how much wider its widest line `w` is. -/
public def fitWidth (mn w k d : Int) : Int :=
  if d ≤ 0 then w else mn + (w - mn) * k / d

public theorem fitWidth_between (mn w k d : Int) (hmw : mn ≤ w) (hk : 0 ≤ k)
    (hkd : k ≤ d) : mn ≤ fitWidth mn w k d ∧ fitWidth mn w k d ≤ w := by
  unfold fitWidth
  split
  · exact ⟨hmw, Int.le_refl w⟩
  · rename_i hd
    have hd : 0 < d := by omega
    have h0 : 0 ≤ (w - mn) * k / d := Int.ediv_nonneg (Int.mul_nonneg (by omega) hk) (by omega)
    have h1 : (w - mn) * k / d ≤ w - mn := by
      apply Int.ediv_le_of_le_mul hd
      exact Int.mul_le_mul_of_nonneg_left hkd (by omega)
    omega

/-- Share a measure too narrow for a table's narrowing columns as
a browser's automatic table layout does (HTML 4.01 §B.5.2). -/
public def fitColumns (cols : Array Ir.ColSpec) (avail : Sp) (natural mins : Array Sp) :
    Array Sp :=
  let isNat (j : Nat) : Bool :=
    (cols[j]?.map fun c => c.narrows && (c.width matches .natural)).getD false
  let lo (j : Nat) (w : Sp) : Sp := min ((mins[j]?).getD w) w
  let sums := natural.zipIdx.foldl (fun (fx, mx, mn) (w, j) =>
    if isNat j then (fx, mx + w, mn + lo j w) else (fx + w, mx, mn)) ((0 : Sp), (0 : Sp), (0 : Sp))
  let (fixed, maxSum, minSum) := sums
  let room := avail - fixed
  if maxSum ≤ room then natural
  else natural.mapIdx fun j w =>
    if !isNat j then w
    else if room ≤ minSum then lo j w
    else fitWidth (lo j w) w (room - minSum) (maxSum - minSum)

/-- The sizes a markdown table too wide for the text
block steps down through, largest first (size10.clo). -/
public def tableSteps : List String := ["small", "footnotesize", "scriptsize"]

/-- The step a markdown table takes only when it is wider than the paper at the floor: `\tiny`. -/
public def tableLastStep : String := "tiny"

/-- How a narrowing table fits its text block: the size step it sets at
(`none`: its body size) and how far it still passes the block there. -/
public structure TableFit where
  step : Option String := none
  overhang : Sp := 0
  deriving Repr, BEq, Inhabited

/-- What a table's narrowing columns need at a size: each column's
widest unbreakable run, unhyphenated, with the gaps and pads. -/
private def tableNeed (fs : FontSet) (geom : Geom) (xHeight : Sp) (imgs : Image.Store)
    (cols : Array Ir.ColSpec) (padL padR : Bool) (rows : Array (Array (Array Ir.Inline)))
    (spans : Array Ir.ColSpan) (colsep size : Sp) : Sp := Id.run do
  let mut widths : Array Sp := cols.map fun _ => 0
  let mut cache : Std.HashMap String (Array Nat) := {}
  for (row, i) in rows.zipIdx do
    for (cell, j) in row.zipIdx do
      unless inSpan spans i j do
        let (items, _, c, _) :=
          itemsOfInlines none size xHeight fs { cellCode := true } cell cache (.fixed .unattributed)
            imgs geom.textWidth geom.textHeight (ladder := geom.scale)
        cache := c
        let narrows := (cols[j]?.map (·.narrows)).getD false
        let w := if narrows then itemsMinWidth items else itemsLinesWidth items
        widths := widths.modify j (max · w)
  return widths.foldl (· + ·) 0 + tablePadding colsep cols.size padL padR

/-- The size a markdown table sets at: its body size when its narrowing columns fit
`avail`, else the largest of `tableSteps` that fits, else the floor or `tableLastStep`. -/
public def tableFit (geom : Geom) (fs : FontSet) (imgs : Image.Store) (colsep avail : Sp)
    (cols : Array Ir.ColSpec) (padL padR : Bool) (rows : Array (Array (Array Ir.Inline)))
    (spans : Array Ir.ColSpan) : TableFit := Id.run do
  unless cols.any (·.narrows) do return {}
  let xHeight := fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm
  let need (step : Option String) : Sp :=
    tableNeed fs geom xHeight imgs cols padL padR rows spans colsep
      (match step with
        | some s => Ir.scaleStepIn geom.scale geom.fontSize s
        | none => geom.fontSize)
  if need none ≤ avail then return {}
  for s in tableSteps do
    if need (some s) ≤ avail then return { step := some s }
  let floor := tableSteps.getLast?
  -- At the floor, an overhang stands in the margins while the table fits the paper.
  if need floor ≤ geom.pageW then return { step := floor, overhang := need floor - avail }
  let last := some tableLastStep
  return { step := last, overhang := max 0 (need last - avail) }

/-- Lay out a `.table`, booktabs' formal table: columns at their declared fraction
or widest cell, `2·tabcolsep` apart, rules padded by their declared seps. -/
private def collectTable (r : Rd) (a0 : Acc)
    (cols : Array Ir.ColSpec) (padL padR : Bool)
    (rows : Array (Array (Array Inline))) (rules : Array (Nat × Ir.TableRule))
    (spans : Array Ir.ColSpan) (indent : Sp) (center : Bool) : Acc := Id.run do
  if cols.isEmpty then
    return a0
  let mut a := a0.flushGap r
  let tok (name : String) : Sp :=
    tableLength ((a.tokens.find? name).map fun g => (r.resolve g).width) r.preamble name
  let colsep := tok "tabcolsep"
  let total := (a.measure.getD r.geom.textWidth) - indent
  -- A markdown table too wide for its measure steps down (`tableFit`), cells unhyphenated.
  let web := cols.any (·.narrows)
  let cellPats := if web then none else r.pats
  let fit := tableFit r.geom r.fs r.imgs colsep total cols padL padR rows spans
  let size := match fit.step with
    | some s => Ir.scaleStepIn r.geom.scale r.geom.fontSize s
    | none => r.geom.fontSize
  -- The measuring pass drops its diagnostics; the setting pass emits them once.
  let mut nats : Array (Array Sp) := #[]
  let mut breaks : Array (Array Bool) := #[]
  let mut mins : Array Sp := cols.map fun _ => 0
  let mut cache := a.hyphCache
  for (row, i) in rows.zipIdx do
    let mut rowNats : Array Sp := #[]
    let mut rowBreaks : Array Bool := #[]
    for (cell, j) in row.zipIdx do
      let (items, _, c, _) :=
        itemsOfInlines cellPats size r.xHeight r.fs
          { color := a.fg, ground := a.ground, cellCode := web } cell cache
          (.fixed .unattributed) r.imgs r.geom.textWidth r.geom.textHeight
          (ladder := r.geom.scale) (step := r.step) (steps := r.steps)
      cache := c
      rowNats := rowNats.push (itemsLinesWidth items)
      rowBreaks := rowBreaks.push (itemsBreak items)
      unless inSpan spans i j do
        mins := mins.modify j (max · (itemsMinWidth items))
    nats := nats.push rowNats
    breaks := breaks.push rowBreaks
  a := { a with hyphCache := cache }
  let natural := tableColWidths colsep total size cols nats spans padL padR
  let widths := if web then
      fitColumns cols (total - tablePadding colsep cols.size padL padR) natural mins
    else natural
  let lead : Sp := if padL then colsep else 0
  let trail : Sp := if padR then colsep else 0
  let innerGaps : Sp := 2 * colsep * ((cols.size : Int) - 1)
  let tableW : Sp := lead + widths.foldl (· + ·) 0 + innerGaps + trail
  -- A tex table wider than the measure keeps its width and is named, as TeX sets it overfull.
  let offPaper := tableW > r.geom.pageW
  if tableW > total then
    a := { a with diags := a.diags.push (Diag.of .W0338
      (if web && fit.overhang > 0 then
          "the table's words alone are wider than the measure at its smallest size; it " ++
            (if offPaper then "runs past the edges of the paper" else "overhangs the margins")
        else "the table is wider than the measure")
      (detail := some s!"{(tableW - total).toPtString}pt wider")
      (span := rows.findSome? fun row => row.findSome? Ir.inlineSource)
      (help := if web then
          "shorten the longest word in each column, or split the table into narrower ones"
        else "narrow the p{...} column widths, or widen the text block")) }
  let side : Ir.HAlign := if center then .center else if r.geom.flushRight then .right else .left
  let x0 : Sp := if web && tableW > total then
      if offPaper then (r.geom.pageW - tableW) / 2 - r.geom.hmargin
      else max (-r.geom.hmargin)
        (min (indent - (tableW - total) / 2) (r.geom.pageW - r.geom.hmargin - tableW))
    else indent + side.boxOffset (max 0 (total - tableW))
  -- A cell sets by its own spec: `\@arrayparboxrestore` zeroes the scope's skips (latex.ltx).
  let rc := { r with centreBoxes := false, pats := cellPats
                     geom := { r.geom with flushRight := false, justify := true } }
  let colX (j : Nat) : Sp := Id.run do
    let mut x := x0 + lead
    for i in [0:j] do
      x := x + widths[i]! + 2 * colsep
    return x
  let fg := a.fg
  let heavy := tok "heavyrulewidth"
  let light := tok "lightrulewidth"
  let cmidW := tok "cmidrulewidth"
  let aboveSep := tok "aboverulesep"
  let belowSep := tok "belowrulesep"
  let aboveTop := tok "abovetopsep"
  let belowBottom := tok "belowbottomsep"
  let kern := tok "cmidrulekern"
  let dbl := tok "doublerulesep"
  -- A `\cmidrule{a-b}` spans the cells' pads, as LaTeX's `\multispan` draws it.
  let cmidSeg (ca cb : Nat) (tl tr : Bool) : Sp × Sp :=
    let ca := min (max ca 1) cols.size
    let cb := min (max cb ca) cols.size
    let left := colX (ca - 1) - (if ca == 1 then lead else colsep)
      + (if tl then kern else 0)
    let right := colX (cb - 1) + widths[cb - 1]!
      + (if cb == cols.size then trail else colsep) - (if tr then kern else 0)
    (left, max 0 (right - left))
  -- booktabs' seps: `doublerulesep` between two rules; `\addlinespace` replaces the seps.
  let mut pendBelow : Option Sp := none
  -- 0 = content (or table start), 1 = a drawn rule, 2 = an \addlinespace
  let mut prev : Nat := 0
  for i in [0:rows.size + 1] do
    let mut here : Array Ir.TableRule := #[]
    for (k, tr) in rules do
      if k == i then here := here.push tr
    let mut hi := 0
    for _ in [0:here.size] do
      if h : hi < here.size then
        match here[hi] with
        | .gap g =>
          pendBelow := none
          a := { a with ops := a.ops.push (.skip { width := (r.resolve g).width }) }
          prev := 2
          hi := hi + 1
        | .cmid _ _ _ _ =>
          -- a run of consecutive cmids is one rule row
          let mut segs : Array Seg := #[]
          let mut x : Sp := 0
          let mut lineX : Sp := 0
          let mut first := true
          for _ in [hi:here.size] do
            if h' : hi < here.size then
              match here[hi] with
              | .cmid ca cb tl tr =>
                let (l, w) := cmidSeg ca cb tl tr
                let l' := r.geom.hmargin + l
                if first then
                  lineX := l'
                  x := l'
                  first := false
                if l' > x then segs := segs.push (.gap (l' - x) false)
                segs := segs.push (.rule w cmidW 0 fg)
                x := max x (l' + w)
                hi := hi + 1
              | _ => break
          let sep := match prev with
            | 1 => dbl
            | 2 => 0
            | _ => aboveSep
          let ops := (a.ops.push (.skip { width := sep })).push
            (.tableRule cmidW lineX (x - lineX) segs)
          a := { a with ops := ops }
          pendBelow := some belowSep
          prev := 1
        | tr =>
          let (th, ab, be) := match tr with
            | .top => (heavy, aboveTop, belowSep)
            | .bottom => (heavy, aboveSep, belowBottom)
            | _ => (light, aboveSep, belowSep)
          let sep := match prev with
            | 1 => dbl
            | 2 => 0
            | _ => ab
          let ops := (a.ops.push (.skip { width := sep })).push
            (.tableRule th (r.geom.hmargin + x0) tableW #[.rule tableW th 0 fg])
          a := { a with ops := ops }
          pendBelow := some be
          prev := 1
          hi := hi + 1
    if h : i < rows.size then
      if let some pb := pendBelow then
        a := { a with ops := a.ops.push (.skip { width := pb }) }
        pendBelow := none
      prev := 0
      let row := rows[i]
      -- Every cell stands on the row's baseline by its first line, as an `\halign` entry does.
      a := { a with ops := a.ops.push (.colOpen (Array.replicate row.size .first)) }
      for j in [0:row.size] do
        let sp := Ir.cellSpan? spans i j
        let spec := Ir.cellSpec cols spans i j
        let wj := match sp with
          | some s => spanBox colsep widths s
          | none => widths[j]?.getD 0
        let measureW := match sp, spec.width with
          | some s, .sized _ => spanNeed total nats s
          | _, _ => wj
        let x := colX j
        let cell := row[j]!
        let strut := some (cellStrut r.geom.skips r.geom.scale size r.geom.leading cell)
        unless cell.isEmpty do
          let sub := { a with
            measure := some (x + measureW)
            ops := #[]
            wantDefault := false
            owed := #[]
            anchorAt := none
            dispAlt := none }
          let (sub, leaf) := sub.leafRange (Struct.leafCountInlines cell)
          let span := Struct.leafCountInlines cell
          -- A natural cell its narrowed column cannot hold wraps as a browser's does.
          let nat := ((nats[i]?).bind (·[j]?)).getD 0
          let broken := ((breaks[i]?).bind (·[j]?)).getD false
          let sub := if !(spec.width matches .natural) then
              let (justify, flushRight, center) := cellParagraph spec
              collectPara { rc with geom := { rc.geom with justify, flushRight } } sub cell x
                center size (baseStyle := { cellCode := web }) (leaf := leaf) (span := span)
                (rowStrut := strut) (urlBreaks := false)
            else if spec.narrows && nat > measureW then
              let (flushRight, center) := narrowedCell (cellSide cols spans i j)
              collectPara
                { rc with pats := none, geom := { rc.geom with justify := false, flushRight } }
                sub cell x center size (baseStyle := { cellCode := web }) (leaf := leaf)
                (span := span) (rowStrut := strut) (background := narrowedSkip size)
                (urlBreaks := false)
            else if broken then
              let (flushRight, center) := narrowedCell (cellSide cols spans i j)
              collectPara { rc with geom := { rc.geom with justify := false, flushRight } }
                sub cell x center size (baseStyle := { cellCode := web }) (leaf := leaf)
                (span := span) (rowStrut := strut) (urlBreaks := false)
            else match cellSide cols spans i j with
            | .center =>
              collectPara rc sub cell x true size (baseStyle := { cellCode := web }) (leaf := leaf)
                (span := span) (rowStrut := strut) (urlBreaks := false)
            | .right =>
              collectPara rc sub cell (x + max 0 (wj - nat)) false size
                (baseStyle := { cellCode := web }) (leaf := leaf) (span := span) (rowStrut := strut)
                (urlBreaks := false)
            | .left =>
              collectPara rc sub cell x false size (baseStyle := { cellCode := web }) (leaf := leaf)
                (span := span) (rowStrut := strut) (urlBreaks := false)
          a := { a with
            ops := a.ops ++ sub.ops
            hyphCache := sub.hyphCache
            diags := sub.diags
            leafNext := sub.leafNext
            pictures := sub.pictures }
        let closer : Op := if j + 1 == row.size then .colClose else .colNext
        a := { a with ops := a.ops.push closer }
      if row.isEmpty then
        a := { a with ops := a.ops.push .colClose }
  -- A trailing sep below the last rule joins the gap after the table.
  if let some pb := pendBelow then
    if pb > 0 then
      a := a.vskip { width := pb }
  return a

/-- How many pairs of a picture's node labels have overlapping
ink boxes, the loss relative placement cannot prevent. -/
private def labelCollisions (pic : Ir.Pic.Picture) (boxes : Array Ir.Pic.Box) :
    Nat := Id.run do
  -- A label's own box; a fill, an outline and an edge overlap by design.
  let mut ls : Array Ir.Pic.Box := #[]
  for i in [0:pic.shapes.size] do
    if let (some s, some b) := (pic.shapes[i]?, boxes[i]?) then
      if s matches .label _ _ _ _ _ _ then
        if b.1.1 < b.2.1 then ls := ls.push b
  let mut n := 0
  for i in [0:ls.size] do
    for j in [i + 1:ls.size] do
      if let (some p, some q) := (ls[i]?, ls[j]?) then
        if p.1.1 < q.2.1 && q.1.1 < p.2.1 && p.1.2 < q.2.2 && q.1.2 < p.2.2 then
          n := n + 1
  return n

/-- One run's contribution to a label line's vertical extent: the face's capitals-to-descent
band, its middle half an x-height above the baseline (pgf's `mid` anchor). -/
public def labelVStep (fs : FontSet) (size : Sp) (acc : Sp × Sp) (seg : Seg) : Sp × Sp :=
  match seg with
  | .run idx _ _ _ _ sz _ _ raise _ _ =>
    let font := fs.get idx
    let sz := if sz == 0 then size else sz
    let span := font.capHeight.toNat + (-font.descent).toNat
    let up := (span + font.xHeightOptical) / 2
    (max acc.1 (scaledAt sz font up + max 0 raise),
     max acc.2 (scaledAt sz font (span - up) + max 0 (-raise)))
  | _ => acc

/-- How far a label line's ink reaches above and below its
baseline: the componentwise maximum of its runs' bands. -/
public def labelVExtent (fs : FontSet) (size : Sp) (segs : Array Seg) : Sp × Sp :=
  segs.foldl (labelVStep fs size) (0, 0)

/-- A glyph's vertical reach in the run that paints it, from its face, size and raise. -/
public def glyphVExtent (font : Font) (size raise : Sp) (g : Nat) : Sp × Sp :=
  match font.yExtent g with
  | some (lo, hi) =>
    (hi * size / (font.unitsPerEm : Int) + raise,
     (-lo) * size / (font.unitsPerEm : Int) - raise)
  | none =>
    (scaledAt size font font.capHeight.toNat + raise,
     scaledAt size font (-font.descent).toNat - raise)

private def growExtent (acc extent : Sp × Sp) : Sp × Sp :=
  (max acc.1 extent.1, max acc.2 extent.2)

private def ExtentLe (a b : Sp × Sp) : Prop := a.1 ≤ b.1 ∧ a.2 ≤ b.2

private theorem extentLe_trans {a b c : Sp × Sp} (hab : ExtentLe a b)
    (hbc : ExtentLe b c) : ExtentLe a c :=
  ⟨Int.le_trans hab.1 hbc.1, Int.le_trans hab.2 hbc.2⟩

private theorem growExtent_left (a b : Sp × Sp) : ExtentLe a (growExtent a b) :=
  ⟨Int.le_max_left _ _, Int.le_max_left _ _⟩

private theorem growExtent_right (a b : Sp × Sp) : ExtentLe b (growExtent a b) :=
  ⟨Int.le_max_right _ _, Int.le_max_right _ _⟩

private theorem foldExtent_preserves {α : Type} (f : (Sp × Sp) → α → Sp × Sp)
    (hf : ∀ a x, ExtentLe a (f a x)) (xs : Array α) (a : Sp × Sp) :
    ExtentLe a (xs.foldl f a) :=
  Array.foldl_induction (motive := fun _ b => ExtentLe a b)
    ⟨Int.le_refl _, Int.le_refl _⟩
    (fun i b h => extentLe_trans h (hf b xs[i]))

private theorem foldExtent_covers {α : Type} (f : (Sp × Sp) → α → Sp × Sp)
    (hf : ∀ a x, ExtentLe a (f a x)) (xs : Array α) (a e : Sp × Sp)
    (x : α) (hx : x ∈ xs) (he : ∀ b, ExtentLe e (f b x)) :
    ExtentLe e (xs.foldl f a) := by
  obtain ⟨j, hj, hget⟩ := Array.mem_iff_getElem.mp hx
  have h : j < xs.size → ExtentLe e (xs.foldl f a) := by
    refine Array.foldl_induction (motive := fun n b => j < n → ExtentLe e b) ?_ ?_
    · omega
    · intro i b ih hnext
      by_cases hprev : j < i.val
      · exact extentLe_trans (ih hprev) (hf b xs[i])
      · have hij : i.val = j := by omega
        simpa [hij, hget] using he b
  exact h hj

/-- One segment's measured contribution, which only grows the accumulator. -/
public def labelGlyphStep (fs : FontSet) (size : Sp) (acc : Sp × Sp) (seg : Seg) : Sp × Sp :=
  match seg with
    | .run idx _ _ _ glyphs sz _ _ raise _ _ =>
      let font := fs.get idx
      let sz := if sz == 0 then size else sz
      glyphs.foldl (fun acc (g, _) => growExtent acc (glyphVExtent font sz raise g)) acc
    | .image _ _ h _ => (max acc.1 h, acc.2)
    | .rule _ t raise _ | .decoration _ _ t raise _ =>
      growExtent acc (raise + t, -raise)
    | .poly pts _ => pts.foldl (fun acc (_, y) => growExtent acc (y, -y)) acc
    | .gap _ _ | .decoratedGap _ _ _ => acc

/-- How far a label line's glyphs reach above and
below its baseline, the box that reserves its ink. -/
public def labelGlyphExtent (fs : FontSet) (size : Sp) (segs : Array Seg) : Sp × Sp :=
  segs.foldl (labelGlyphStep fs size) (0, 0)

private theorem labelGlyphStep_grows (fs : FontSet) (size : Sp)
    (a : Sp × Sp) (seg : Seg) : ExtentLe a (labelGlyphStep fs size a seg) := by
  cases seg with
  | run =>
    exact foldExtent_preserves _ (fun _ _ => growExtent_left _ _) _ _
  | image => exact ⟨Int.le_max_left _ _, Int.le_refl _⟩
  | rule | decoration => exact growExtent_left _ _
  | poly => exact foldExtent_preserves _ (fun _ _ => growExtent_left _ _) _ _
  | gap | decoratedGap => exact ⟨Int.le_refl _, Int.le_refl _⟩

public theorem labelGlyphExtent_covers (fs : FontSet) (size : Sp) (segs : Array Seg)
    (idx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution)
    (hrun : Seg.run idx color link width glyphs sz leading decorations raise ground attr ∈ segs)
    (g : Nat × Char × Sp) (hg : g ∈ glyphs) :
    let e := glyphVExtent (fs.get idx) (if sz == 0 then size else sz) raise g.1
    e.1 ≤ (labelGlyphExtent fs size segs).1 ∧
      e.2 ≤ (labelGlyphExtent fs size segs).2 := by
  apply foldExtent_covers _ (labelGlyphStep_grows fs size) segs (0, 0) _
    _ hrun
  intro a
  exact foldExtent_covers _ (fun _ _ => growExtent_left _ _) glyphs a _
    g hg (fun _ => growExtent_right _ _)

public theorem labelVStep_glyph_id (fs : FontSet) (size : Sp) (acc : Sp × Sp) (seg : Seg) :
    labelVStep fs size acc (Seg.stripGlyphs seg) = labelVStep fs size acc seg := by
  cases seg <;> rfl

public theorem labelVStep_idem (fs : FontSet) (size : Sp) (acc : Sp × Sp) (seg : Seg) :
    labelVStep fs size (labelVStep fs size acc seg) seg = labelVStep fs size acc seg := by
  cases seg with
  | run =>
    have idem : ∀ a v : Int, max (max a v) v = max a v := by intro a v; omega
    show (max (max acc.1 _) _, max (max acc.2 _) _) = (max acc.1 _, max acc.2 _)
    rw [idem, idem]
  | gap => rfl
  | decoratedGap => rfl
  | decoration => rfl
  | rule => rfl
  | image => rfl
  | poly => rfl

public theorem label_centre_glyph_free (fs : FontSet) (size : Sp) (segs : Array Seg) :
    labelVExtent fs size (segs.map Seg.stripGlyphs) = labelVExtent fs size segs := by
  unfold labelVExtent
  rw [Array.foldl_map]
  congr 1
  funext acc s
  exact labelVStep_glyph_id fs size acc s

public theorem vphantom_absorbed (fs : FontSet) (size : Sp) (segs : Array Seg) (r : Seg) :
    labelVExtent fs size ((segs.push r).push (Seg.stripGlyphs r))
      = labelVExtent fs size (segs.push r) := by
  unfold labelVExtent
  rw [Array.foldl_push, labelVStep_glyph_id, Array.foldl_push, labelVStep_idem]

/-- Resolve a set label line once: the font band places its
baseline and the measured glyph extent reserves its ink. -/
public def measureLabelLine (fs : FontSet) (size width ex : Sp) (segs : Array Seg) :
    Ir.Pic.LabelInk :=
  let band := labelVExtent fs size segs
  let ink := labelGlyphExtent fs size segs
  let (axis, rule, script) : Sp × Sp × Nat := match fs.mathFont? with
    | some (_, f, c) =>
      let base : Int := (Math.mathSize size.toNat fs.body.xHeightOptical fs.body.unitsPerEm
        f.xHeightOptical f.unitsPerEm : Nat)
      (c.axisHeight * base / (f.unitsPerEm : Int),
       c.fractionRuleThickness * base / (f.unitsPerEm : Int), c.scales.script * 10)
    | none => (0, 0, 0)
  { w := width, height := band.1, depth := band.2
    boxHeight := ink.1, boxDepth := ink.2, ex := ex, axis, rule, script }

/-- The backend projection of the two extent fields of `Ir.Pic.LabelInk`. -/
public theorem measureLabelLine_projects (fs : FontSet) (size width ex : Sp)
    (segs : Array Seg) :
    let m := measureLabelLine fs size width ex segs
    (m.height, m.depth) = labelVExtent fs size segs ∧
      (m.boxHeight, m.boxDepth) = labelGlyphExtent fs size segs :=
  ⟨rfl, rfl⟩

/-- The inline producer's and line breaker's result for one picture label. -/
public structure LabelResult where
  line? : Option (Array Seg × Sp × Ir.Pic.LabelInk)
  diags : Array Diag
  lineCount : Nat
  source : Option Span

/-- Shape, break and measure a picture label once. -/
public def labelResult (fs : FontSet) (imgs : Image.Store) (geom : Geom) (xHeight : Sp)
    (leaf : Option Nat) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat) :
    LabelResult :=
  let size := geom.fontSize * (scale : Int) / 1000
  let produced := itemsOfInlines none size xHeight fs {}
    #[.colored color none content] {} (.fixed ((leaf.map .block).getD .unattributed)) imgs
    geom.textWidth geom.textHeight (ladder := geom.scale)
  let items := produced.1
  let breaks := kp items geom.textWidth
  let line := breaks[0]?.map fun brk =>
    let line := setLine items (lineStart items 0) brk geom.textWidth false
    (line.1, size,
      measureLabelLine fs size line.2.1 (xHeight * (scale : Int) / 1000) line.1)
  let sources := produced.2.2.2.2.2.2.2
  let source := match breaks[0]? with
    | some brk => lineSource sources (lineStart items 0) brk
    | none => lineSource sources 0 items.size
  { line? := line, diags := produced.2.1, lineCount := breaks.size, source := source }

public theorem labelResult_projects (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (segs : Array Seg) (size : Sp)
    (ink : Ir.Pic.LabelInk)
    (h : (labelResult fs imgs geom xHeight leaf content color scale).line? = some (segs, size, ink)) :
    ink = measureLabelLine fs size ink.w ink.ex segs := by
  simp only [labelResult, Option.map_eq_some_iff] at h
  obtain ⟨brk, _, heq⟩ := h
  cases heq
  rfl

/-- Place a measured label by the IR's baseline and horizontal anchor. -/
public def labelLine (place : Ir.Pic.Place) (x y : Sp) (align : Ir.Pic.LabelAlign)
    (ink : Ir.Pic.LabelInk) (segs : Array Seg) (size : Sp) (leaf : Option Nat) : LineOut :=
  { x := (place.toPage (Ir.Pic.labelInkBox x y align ink).1).1
    y := (place.toPage (x, Ir.Pic.labelBaseline y align ink)).2
    size := size, segs := segs, setWidth := ink.w, leaf := leaf }

public theorem labelLine_projects (place : Ir.Pic.Place) (x y : Sp) (align : Ir.Pic.LabelAlign)
    (ink : Ir.Pic.LabelInk) (segs : Array Seg) (size : Sp) (leaf : Option Nat) :
    (labelLine place x y align ink segs size leaf).y =
      (place.toPage (x, Ir.Pic.labelBaseline y align ink)).2 := by rfl

public theorem labelLine_covers (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (segs : Array Seg) (size : Sp)
    (ink : Ir.Pic.LabelInk)
    (h : (labelResult fs imgs geom xHeight leaf content color scale).line? = some (segs, size, ink))
    (idx : Nat) (runColor : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution)
    (hrun : Seg.run idx runColor link width glyphs sz leading decorations raise ground attr ∈ segs)
    (g : Nat × Char × Sp) (hg : g ∈ glyphs)
    (place : Ir.Pic.Place) (x y : Sp) (align : Ir.Pic.LabelAlign) :
    let e := glyphVExtent (fs.get idx) (if sz == 0 then size else sz) raise g.1
    let line := labelLine place x y align ink segs size leaf
    let box := Ir.Pic.labelGlyphBox x y align ink
    (place.toPage box.2).2 ≤ line.y - e.1 ∧
      line.y + e.2 ≤ (place.toPage box.1).2 := by
  have hm := labelResult_projects fs imgs geom xHeight leaf content color scale segs size ink h
  have he := labelGlyphExtent_covers fs size segs idx runColor link width glyphs sz leading
    decorations raise ground attr hrun g hg
  have hhi : (glyphVExtent (fs.get idx) (if sz == 0 then size else sz) raise g.1).1 ≤
      ink.boxHeight := by
    have hheight := congrArg Ir.Pic.LabelInk.boxHeight hm
    simp only [measureLabelLine] at hheight
    rw [hheight]
    exact he.1
  have hlo : (glyphVExtent (fs.get idx) (if sz == 0 then size else sz) raise g.1).2 ≤
      ink.boxDepth := by
    have hdepth := congrArg Ir.Pic.LabelInk.boxDepth hm
    simp only [measureLabelLine] at hdepth
    rw [hdepth]
    exact he.2
  have hb := Ir.Pic.labelGlyphBox_covers_extent x y align ink _ _ hhi hlo
  have reflect : ∀ t m baseline hi lo bottom top : Int,
      bottom ≤ baseline - lo → baseline + hi ≤ top →
      t + (m - top) ≤ t + (m - baseline) - hi ∧
        t + (m - baseline) + lo ≤ t + (m - bottom) := by
    intro t m baseline hi lo bottom top hbottom htop
    omega
  exact reflect place.yTop place.ymax _ _ _ _ _ hb.1 hb.2

/-- The measurement a picture's box is computed with: `labelResult`'s
line as an `Ir.Pic.LabelMetric` over alphabet-resolved content. -/
private def picMetric (fs : FontSet) (imgs : Image.Store) (geom : Geom) (xHeight : Sp) :
    Ir.Pic.LabelMetric := fun content scale =>
  match (labelResult fs imgs geom xHeight none
      (Ir.mapInlines (Ir.resolveMathAlphaInline fs.mathAlphabets) content) Ir.Color.black
      scale).line? with
  | some (_, _, ink) => ink
  | none => {}

/-- The glyph reserve the picture layout uses. -/
public def pictureLabelBox (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight x y : Sp) (content : Array Ir.Inline) (scale : Nat)
    (align : Ir.Pic.LabelAlign) : Ir.Pic.Box :=
  Ir.Pic.labelGlyphBox x y align (picMetric fs imgs geom xHeight content scale)

/-- Whether a painted run lacks outline evidence; only the font reader's `none` is unresolved. -/
public def labelGlyphUnknown (fs : FontSet) (size : Sp) (segs : Array Seg) : Bool :=
  segs.any fun seg => match seg with
  | .run idx _ _ _ glyphs sz _ _ raise _ _ =>
    glyphs.any fun g =>
      (GlyphBounds.glyph (fs.get idx) (if sz == 0 then size else sz) raise g.1).unresolved
  | .image _ _ _ _ | .rule _ _ _ _ | .decoration _ _ _ _ _
    | .poly _ _ | .gap _ _ | .decoratedGap _ _ _ => false

/-- Read each painted run in its own face, size and raise against the producer's reserve. -/
public def observeLabel (fs : FontSet) (line : LineOut) (stamp : LabelAudit.Stamp) :
    LabelAudit.Observation :=
  { stamp := stamp
    known := !labelGlyphUnknown fs line.size line.segs
    bounded := line.segs.all fun seg => match seg with
      | .run idx _ _ _ glyphs sz _ _ raise _ _ =>
        let font := fs.get idx
        let size := if sz == 0 then line.size else sz
        glyphs.all fun g => match font.yExtent g.1 with
          | none => true
          | some (lo, hi) =>
            decide (hi * size / (font.unitsPerEm : Int) + raise ≤ stamp.above ∧
              (-lo) * size / (font.unitsPerEm : Int) - raise ≤ stamp.below)
      | .image _ _ _ _ | .rule _ _ _ _ | .decoration _ _ _ _ _
        | .poly _ _ | .gap _ _ | .decoratedGap _ _ _ => true }

/-- The label census over the final page lines, after placement and furniture. -/
public def labelObservations (fs : FontSet) (pages : Array PageOut) :
    Array LabelAudit.Observation :=
  pages.flatMap fun page =>
    page.lines.filterMap fun line => line.pictureLabel.map (observeLabel fs line)

/-- Reconcile the pre-placement label request census
with the page lines, adding diagnostics only. -/
public def auditLabelInk (fs : FontSet) (requests : Array LabelAudit.Request) (out : Out) : Out :=
  { out with diags := LabelAudit.finish requests (labelObservations fs out.pages) out.diags }

/-- The first line emitted for a label and its diagnostic account. -/
public structure LabelEmission where
  line? : Option LineOut := none
  diags : Array Diag := #[]
  source : Option Span := none
  lineCount : Nat := 0
  reserved : Ir.Pic.Box := ((0, 0), (0, 0))

/-- Add the label key as the diagnostic's subject unless the producer named one. -/
public def nameLabelDiag (key : String) (d : Diag) : Diag :=
  { d with subject := d.subject.orElse (fun _ => some key) }

/-- A label without visible text may legitimately produce no line. -/
public def labelTextBlank (content : Array Ir.Inline) : Bool :=
  (Ir.plainText content).toList.all Char.isWhitespace

/-- A producer's keyed refusal already accounts for an absent label. -/
public def labelFailureNamed (content : Array Ir.Inline) (diags : Array Diag) : Bool :=
  diags.any fun d =>
    d.subject == some (Ir.plainText content) &&
      (d.kind.loss == .dropped || d.kind.loss == .pending)

/-- The measured glyph box lies inside the reserved glyph box. -/
@[expose] public def labelReserveCovers (actual reserved : Ir.Pic.Box) : Prop :=
  reserved.1.2 ≤ actual.1.2 ∧ actual.2.2 ≤ reserved.2.2

public instance (a r : Ir.Pic.Box) :
    Decidable (labelReserveCovers a r) := by
  unfold labelReserveCovers
  infer_instance

/-- Check and place the producer's measured line against the picture's reserved glyph box. -/
public def finishLabel (fs : FontSet) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (align : Ir.Pic.LabelAlign)
    (result : LabelResult) (reserved : Ir.Pic.Box) : LabelEmission :=
  let key := Ir.plainText content
  let ds := result.diags.map (nameLabelDiag key)
  let ds := if 1 < result.lineCount then
      ds.push {
        kind := .W0328
        message := "picture label spans multiple lines; only its first line is kept"
        span := result.source
        subject := some key }
    else ds
  match result.line? with
  | none =>
    { source := result.source, lineCount := result.lineCount, reserved := reserved
      diags := if labelTextBlank content || labelFailureNamed content ds then ds else
        ds.push {
          kind := .E0395
          message := "picture label produced no line",
          span := result.source
          subject := some key } }
  | some (segs, size, ink) =>
    let ds := if labelGlyphUnknown fs size segs then
        ds.push {
          kind := .W0394
          message := "picture label has glyphs without measured outline bounds",
          span := result.source
          subject := some key }
      else ds
    let ds := if labelReserveCovers (Ir.Pic.labelGlyphBox x y align ink) reserved then ds else
        ds.push {
          kind := .W0396
          message := "picture label extends beyond its reserved glyph box",
          span := result.source
          subject := some key }
    { line? := some (labelLine place x y align ink segs size leaf), diags := ds
      source := result.source, lineCount := result.lineCount, reserved := reserved }

/-- Emit the line the producer selected, checked against the canonical reservation. -/
public def emitLabel (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) : LabelEmission :=
  finishLabel fs leaf place x y content align
    (labelResult fs imgs geom xHeight leaf content color scale)
    (pictureLabelBox fs imgs geom xHeight x y content scale align)

/-- The label measurement for a caller that needs it before
layout: the one function placement and elaboration both read. -/
public def labelMetric (geom : Geom) (fs : FontSet) (imgs : Image.Store := {}) :
    Ir.Pic.LabelMetric :=
  let font := fs.body
  picMetric fs imgs geom (font.xHeight * geom.fontSize / font.unitsPerEm)

/-- The box a picture occupies on the page:
`Ir.Pic.Picture.box` under layout's label measurement. -/
public def pictureBox (geom : Geom) (fs : FontSet) (imgs : Image.Store) (xHeight : Sp)
    (pic : Ir.Pic.Picture) : Ir.Pic.Box :=
  pic.box (picMetric fs imgs geom xHeight)

public theorem labelMetric_resolve_id (geom : Geom) (fs : FontSet) (imgs : Image.Store)
    (content : Array Ir.Inline) (scale : Nat) :
    labelMetric geom fs imgs
        (Ir.mapInlines (Ir.resolveMathAlphaInline fs.mathAlphabets) content) scale =
      labelMetric geom fs imgs content scale := by
  simp only [labelMetric, picMetric, Ir.mapMathInlines_fixed_point]

public theorem resolveMathAlphaPicture_box_id (geom : Geom) (fs : FontSet)
    (imgs : Image.Store) (pic : Ir.Pic.Picture) :
    (Ir.resolveMathAlphaPicture fs.mathAlphabets pic).box (labelMetric geom fs imgs) =
      pic.box (labelMetric geom fs imgs) :=
  Ir.Pic.Picture.mapLabels_box_id _ _ (labelMetric_resolve_id geom fs imgs) pic

public theorem pictureBox_projects (geom : Geom) (fs : FontSet)
    (imgs : Image.Store) (pic : Ir.Pic.Picture) :
    pictureBox geom fs imgs (fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm) pic =
      pic.box (labelMetric geom fs imgs) := by
  rfl

/-- Stage one picture at its `pictureBox`, placed even
when it cannot fit, with W0335 naming the overrun. -/
private def collectPicture (r : Rd) (a : Acc) (pic : Ir.Pic.Picture)
    (indent : Sp) (center : Bool) (display : Option DisplayJob := none) : Acc :=
  let metric := picMetric r.fs r.imgs r.geom r.xHeight
  let boxes := pic.inkBoxes metric
  let bb := pictureBox r.geom r.fs r.imgs r.xHeight pic
  let ((px0, py0), (px1, py1)) := bb
  let w := px1 - px0
  let h := py1 - py0
  let avail := (a.measure.getD r.geom.textWidth) - indent
  let source := (r.pictureSpans.find? (·.1 == a.leafNext)).map (·.2)
  let a := if w > avail || h > r.geom.textHeight then
      { a with diags := a.diags.push (Diag.of .W0335
        "the picture is larger than the text area; it may overrun the page"
        (span := source) (trigger := source.bind (·.pos.command))
        (detail := some (s!"{w.toPtString}pt × {h.toPtString}pt against " ++
          s!"{avail.toPtString}pt × {r.geom.textHeight.toPtString}pt"))
        (help := "shrink the picture ([scale=...]) or widen the text area \
(\\page{ margin = ... })")) }
    else a
  -- Two labels colliding inside one box are named, not fixed: node extents are declared minimums.
  let a := match labelCollisions pic boxes with
    | 0 => a
    | n =>
      { a with diags := a.diags.push (Diag.of .W0336
        "node labels overlap: a relative placement parts node centres, not the text they set"
        (help := "declare the extent ([minimum width = ...]) or widen the \
separation ([node distance = ...])")
        (detail := some s!"{n} {if n == 1 then "pair" else "pairs"} of labels")) }
  let side : Ir.HAlign := if center then .center else if r.geom.flushRight then .right else .left
  let x := indent + side.boxOffset (max 0 (avail - w))
  let a := a.flushGap r
  let a := match display with
    | some dj => { a with ops := a.ops.push (.displayOpen dj x r.geom.fontSize) }
    | none => a
  let (a, leaf) := a.leafRange 1
  { a with ops := a.ops.push (.picture (r.geom.hmargin + x) pic leaf a.pictures)
           pictures := a.pictures + 1 }

/-- What a captioned float stacks, top to bottom. -/
private inductive FloatSlot where
  | gap (g : Glue)
  | caption
  | object

/-- The float's vertical plan top to bottom: a text-side gap, the caption
and its object with the object-side skip between, a text-side gap. -/
private def floatPlan (capAbove hasCaption : Bool) (floatSep capSep farSep : Glue) :
    List FloatSlot :=
  if !hasCaption then [.gap floatSep, .object, .gap floatSep]
  else if capAbove then
    [.gap (floatSep.add farSep), .caption, .gap capSep, .object, .gap floatSep]
  else
    [.gap floatSep, .object, .gap capSep, .caption, .gap (floatSep.add farSep)]

/-- The gaps a plan pays, in order. -/
private def FloatSlot.gaps (plan : List FloatSlot) : List Glue :=
  plan.filterMap fun s => match s with
    | .gap g => some g
    | _ => none

private theorem floatPlan_gaps_exact (capAbove : Bool) (floatSep capSep farSep : Glue) :
    FloatSlot.gaps (floatPlan capAbove true floatSep capSep farSep)
      = if capAbove then [floatSep.add farSep, capSep, floatSep]
        else [floatSep, capSep, floatSep.add farSep] := by
  cases capAbove <;> rfl

private theorem floatPlan_bare_gaps (capAbove : Bool) (floatSep capSep farSep : Glue) :
    FloatSlot.gaps (floatPlan capAbove false floatSep capSep farSep)
      = [floatSep, floatSep] := by
  cases capAbove <;> rfl

/-- Blocks that are pure state changes, which pay no
peer gap and count as no scope's first content. -/
private def statefulBlock : Block → Bool
  | .setPalette _ | .setTokens _ => true
  | b => Ir.pageMarkerBlock b

/-- What a display's line needs from the walk: its two skips above
(`Ir.displaySkipsFor`) and whether TeX sets an empty line first (tex.web §1145). -/
private def Spacing.Pending.displayJob (a : Acc) (r : Rd) (lead : Nat := 0) : DisplayJob :=
  let s := Ir.displaySkipsFor a.tokens r.geom.fontSize
  { ctx := r.display, above := r.resolve s.above, aboveShort := r.resolve s.aboveShort
    emptyLine := !r.display.inPar && !a.afterHeading && !r.display.afterEnv, lead := lead }

/-- Opening a display: the walk pays only what the boundary
owes, TeX's `\parskip` where the display opens a paragraph. -/
private def Spacing.Pending.openDisplay (a : Acc) (r : Rd) (dj : DisplayJob) : Acc :=
  if r.display.inPar then { a with wantDefault := false }.flushGap r
  else if dj.emptyLine && a.wantDefault then
    { a with wantDefault := false
             ops := a.ops.push (.skip (r.resolve r.geom.texParskip)) }.flushGap r
  else a.flushGap r

/-- Closing a display: the skip below is owed to what follows under both of TeX's choices. -/
private def Spacing.Pending.closeDisplay (a : Acc) (r : Rd) : Acc :=
  let s := Ir.displaySkipsFor a.tokens r.geom.fontSize
  let short := a.addvspace (r.resolve s.belowShort)
  let a := a.addvspace (r.resolve s.below)
  { a with dispAlt := some short.owed, declaredSkip := a.declaredSkip || r.display.parEnd
           trivOwed := a.trivOwed || r.display.parEnd }

/-- The unnumbered display: the formula's paragraph
centred on the measure, placed as TeX places a display. -/
private def collectDisplayFormula (r : Rd) (a : Acc)
    (content : Array Inline) (indent : Sp) : Acc :=
  let dj := a.displayJob r
  let a := a.openDisplay r dj
  let (a, leaf) := a.leafRange (Struct.leafCountInlines content)
  let a := collectPara r a content indent true r.geom.fontSize
    (leaf := leaf) (span := Struct.leafCountInlines content) (dispJob := some dj)
  a.closeDisplay r

/-- A display a picture stands for (`Ir.displayPicture?`), placed as a display formula's line. -/
private def collectDisplayPicture (r : Rd) (a : Acc) (anchors : Array Inline)
    (pic : Ir.Pic.Picture) (indent : Sp) : Acc :=
  let dj := a.displayJob r
  let a := a.openDisplay r dj
  let a := { a with ops := a.ops ++ anchors.filterMap fun x => match x with
    | .label name => some (.anchor name)
    | _ => none }
  (collectPicture r a pic indent true (display := some dj)).closeDisplay r

private theorem openDisplay_inPar_exact (a : Acc) (r : Rd) (dj : DisplayJob) (howed : a.owed = #[])
    (hk : a.anchorAt = none) (hin : r.display.inPar = true) :
    (a.openDisplay r dj).ops = a.ops := by
  simp [Spacing.Pending.openDisplay, Spacing.Pending.flushGap, hin, howed, hk]

private def collectParaBlock (r : Rd) (a : Acc) (content : Array Inline) (indent : Sp) : Acc :=
  -- A paragraph of label anchors alone ships no line and no gap.
  if !content.isEmpty && content.all (fun x => x matches .label _) then
    { a with ops := a.ops ++ content.filterMap (fun x => match x with
        | .label name => some (.anchor name)
        | _ => none) }
  else
    let (a, leaf) := a.leafRange (Struct.leafCountInlines content)
    collectPara r a content indent false r.geom.fontSize
      (leaf := leaf) (span := Struct.leafCountInlines content)

private def collectEquation (r : Rd) (a : Acc) (num : Array Inline) (content : Array Inline) (indent : Sp) : Acc := Id.run do
  -- A numbered display sets [mirror box, fil, formula, fil, tag], amsmath's equation shape.
  let dj := a.displayJob r (lead := 2)
  let a := a.openDisplay r dj
  let (a, leaf) := a.leafRange (Struct.leafCountInlines content + Struct.leafCountInlines num)
  let baseStyle : TextStyle := { color := a.fg, ground := a.ground }
  let target := (a.measure.getD r.geom.textWidth) - indent
  let (citems, ds1, cache1, extras, _, cOffsets, cAnchors, cSources) :=
    itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs baseStyle content
      a.hyphCache (LeafCtr.of leaf (Struct.leafCountInlines content) content) r.imgs target
      r.geom.textHeight (ladder := r.geom.scale) (step := r.step) (steps := r.steps)
  let numLeaf := leaf.map (· + Struct.leafCountInlines content)
  let (nitems, ds2, cache2, _, _, nOffsets, nAnchors, nSources) :=
    itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs baseStyle num
      cache1 (LeafCtr.of numLeaf (Struct.leafCountInlines num) num) r.imgs target r.geom.textHeight
      (ladder := r.geom.scale)
  -- Both walks close with parfill glue and a forced pen, which the assembled line replaces.
  let strip (xs : Array Item) : Array Item :=
    if xs.size ≥ 2 then xs.extract 0 (xs.size - 2) else xs
  let citems := strip citems
  let nitems := strip nitems
  let wordOffsets := cOffsets.fold (fun m k v => m.insert (k + 2) v) {}
  let wordOffsets := nOffsets.fold
    (fun m k v => m.insert (k + citems.size + 3) v) wordOffsets
  let anchors := cAnchors.map (fun (n, i) => (n, i + 2)) ++
    nAnchors.map (fun (n, i) => (n, i + citems.size + 3))
  let itemSources := (cSources.filter (·.1 < citems.size)).map (fun (i, s) => (i + 2, s)) ++
    (nSources.filter (·.1 < nitems.size)).map (fun (i, s) => (i + citems.size + 3, s))
  let numW := (measure nitems 0 nitems.size).natural
  let mirrorAttr : Attribution := (leaf.map .block).getD .unattributed
  let mut items : Array Item :=
    #[.box numW 0 a.fg none #[] r.geom.fontSize {} {} 0 a.ground mirrorAttr,
      .glue { fil := true }]
  items := items ++ citems
  items := items.push (.glue { fil := true })
  items := items ++ nitems
  items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
  return ({ a with
    hyphCache := cache2
    ops := a.ops.push (Op.ofPara {
      items := items, extras := extras, wordOffsets := wordOffsets, anchors := anchors,
      itemSources := itemSources
      diags := ds1 ++ ds2
      target := target
      indent := indent, center := false, size := r.geom.fontSize
      justify := true
      markerSegs := none, rule := none
      leaf := leaf, display := some dj }) } : Acc).closeDisplay r

/-- A frame in beamer's text area opens its body where beamer's content
box opens (beamerbaseframe.sty), past the frame's fixed top skip. -/
private def openFrameBody (r : Rd) (a : Acc) (hasTitle : Bool) (valign : VAlign)
    (area : FrameArea) : Acc :=
  let g : Glue := { width := frameBodySkip hasTitle valign r.geom.fontSize }
  match area with
  | .margins => a
  | .text => { a with ops := a.ops.push (.bodyOpen g none), wantDefault := false, frameTop := true }
  | .paper => { a with ops := (a.ops.push (.bodyOpen g none)).push .noInterline, wantDefault := false,
                       frameTop := true }

private def collectSection (r : Rd) (a : Acc) (level : Ir.HeadingLevel) (num : Option String) (title : Array Inline) (indent : Sp) : Acc :=
  if level == 0 then
    -- The document title opens no page of its own, even in slides.
    collectTitle r a title indent false
  else
  -- The top-level section in force, for the footer's `\sectiontitle` slot.
  let a := if level == 1 then
      { a with curSection := if r.inFrame then a.curSection else title
               ops := a.ops.push (.anchor (Ir.slug title)) }
    else a
  -- The number the walk sets before the title is generated ink.
  let span := Struct.leafCountInlines title
  let (a, leaf) := a.leafRange span
  let design := Ir.Design.ofPalette a.pal
  let divider := r.slides && !r.inFrame
  if divider && level == 1 && design.sectionProgress.isSome then
    let a := a.pageBreak
    -- A divider is moloch's `\frame[plain,c,noframenumbering]`: a plain frame's text area.
    let area : FrameArea := if a.footAllowed then .paper else .margins
    let opening := { a.frameOpening false area with
      origin := none, number := none, label := none, allowed := false }
    let a := { a with ops := (a.ops.push .frameClose).push (.frameOpen false none opening) }
    let ground := Ir.frameGroundOf a.pal false .center
    let a := { a with ops := a.ops.push (.pageStyle ground VDist.center) }
    let a := openFrameBody r a false .center area
    let mp : Sp := Ir.sectionPageMeasure r.geom.textWidth
    let indent : Sp := (r.geom.textWidth - mp) / 2
    let st := r.style "sectionpage"
    let saved := (a.fg, a.ground)
    let a := { a with fg := design.sectionTitle, ground := ground }
    let a := match st.font with
      | some tpl =>
        collectDisplay r a (Ir.fillTemplate tpl title) indent false r.geom.fontSize
          (leaf := leaf) (span := span)
      | none =>
        collectDisplay r a title indent false (Ir.scaleStep r.geom.fontSize "Large")
          (baseStyle := { weight := .b }) (leaf := leaf) (span := span)
    let a := { a with fg := saved.1, ground := saved.2 }
    let thick := ((a.tokens.find? "progressheight").map
      fun g => (r.resolve g).width).getD (pt 1) -- moloch's default progressbar linewidth=1pt
    -- No clamp: every threaded position is at most the denominator (`frameNumbers_le_count`).
    let a := match design.sectionProgress with
      | some bar => if a.frameCount == 0 then a else
        { a with ops := a.ops.push (.progress
          a.framesDone a.frameCount bar.fg bar.bg thick
          (r.geom.hmargin + indent) mp) }
      | none => a
    -- The subsection title's strut ends the content box beamer centres (`Ir.sectionPageStrut`).
    let a := if area == .paper then
        { a with ops := a.ops.push (.skip
          { width := Ir.sectionPageStrut r.geom.fontSize r.geom.leading - thick }) }
      else a
    (a.pageBreak).pushOp .frameClose
  else
  -- Only a section outside a frame opens a divider.
  let a := if divider then a.pageBreak else a
  let a := if !r.inFrame && a.footAllowed then
      { a with ops := a.ops.push .frameClose } else a
  let st := r.style level.element
  -- The number stands before the title with a `\quad` kern (classes.dtx `\@seccntformat`).
  let marked := markContent title
  let title := match num with
    | some n => #[Ir.Inline.text (n ++ "\u2003")] ++ marked
    | none => title
  -- Undeclared, a heading stands a rhythm unit above its body and half below.
  let hb := r.resolve (Ir.headingBeforeDefault r.geom.fontSize)
  let two := r.parskip.add r.parskip
  let a := a.addvspace ((st.before.map r.resolve).getD
    (if two.width > hb.width then two else hb))
  let rule : Option HeadingRule := st.rule.map fun (rc : Ir.Color × Option Ir.ColorRef) =>
    { thickness := (st.ruleThickness.map fun g => (r.resolve g).width).getD
        (headingRuleWeight r.geom.fontSize)
      position := st.rulePosition.getD .xHeight
      color := rc.1 }
  let ha := r.resolve (Ir.headingAfterDefault r.geom.fontSize)
  let after := (st.after.map r.resolve).getD
    (if r.parskip.width > ha.width then r.parskip else ha)
  -- A heading keeps its after-skip and two body lines with it, or opens the next page.
  let keep := after.width + 2 * Ir.leadingFor r.geom.fontSize r.geom.leading
  let savedFg := a.fg
  let a := if r.slides && level == 1 then { a with fg := design.sectionTitle } else a
  let a := match st.font with
    | some tpl =>
      collectDisplay r a (Ir.fillTemplate tpl title) indent false r.geom.fontSize
        (rule := rule) (leaf := leaf) (span := span) (keepNext := keep)
    | none =>
      collectDisplay r a title indent false (sectionSize r.geom level)
        (baseStyle := { weight := .b }) (rule := rule)
        (leaf := leaf) (span := span) (keepNext := keep)
  let a := { a.vskip after with afterHeading := true, fg := savedFg }
  if divider then a.pageBreak else a

private def collectBibliography (r : Rd) (a : Acc) (items : Array Ir.BibItem) (indent : Sp) : Acc :=
  -- natbib's `thebibliography`: labels right-aligned in a column as wide as the widest.
  let size := r.geom.fontSize
  let numbered := items.any (·.marker.isSome)
  let (labelW, a) : Sp × Acc := if !numbered then (0, a) else
    items.foldl (init := ((0 : Sp), a)) fun (w, a) item =>
      match item.marker with
      | none => (w, a)
      | some m =>
        let (lw, a) := a.naturalWidth r size #[.text s!"[{m}]"] r.geom.textWidth
        (max w lw, a)
  let hang := if numbered then 0 else (r.resolve (Ir.bibHang a.tokens)).width
  let textIndent := if numbered then indent + labelW + size / 2 else indent
  let sep := r.resolve (Ir.bibSep a.tokens size)
  items.zipIdx.foldl (init := a) fun a (item, i) =>
    let marker := item.marker.map fun m => #[Ir.Inline.text s!"[{m}]"]
    -- The entry's leaves are its inline content's; the label is generated marker ink.
    let (a, leaf) := a.leafRange (Struct.leafCountInlines item.content)
    let a := collectPara r a item.content textIndent false size (marker := marker)
      (markerLeft := if item.labelFlush then some indent else none)
      (leaf := leaf) (span := Struct.leafCountInlines item.content) (hangIndent := hang)
    if i + 1 == items.size then a.wantGap else a.addvspace sep

private def collectNav (a : Acc) (spec : Ir.NavSpec) (body : Array Block) : Acc :=
  -- An unpinned nav ships no ink; its links become the outline and its leaves are skipped.
  let a := (a.leafRange (Struct.leafCountBlocks body)).1
  if spec.pin.isSome then a
  else { a with navEntries := a.navEntries ++ Ir.navLinks body }

private def collectNote (a : Acc) (body : Array Block) : Acc :=
  -- A speaker note is not handout content; its leaves are stepped over.
  (a.leafRange (Struct.leafCountBlocks body)).1

private def collectLogo (a : Acc) (content : Array Inline) : Acc :=
  -- A stateful logo declaration: no lines, no gap; its leaves are stepped over.
  let a := (a.leafRange (Struct.leafCountInlines content)).1
  { a with ops := a.ops.push (.setLogo content) }

/-- One display column of a listing line as the layout sets it: the character, its
token, its run, its fallback token, its source column and whether it is white space. -/
private structure CodeUnit where
  c : Char
  token : Nat
  lex : Nat
  fb : Nat
  sourceCol : Nat
  space : Bool
  deriving Inhabited

/-- A source line as display units, each read as both
backends' wraps read it (`Listing.codeMarks`). -/
private def codeUnits (spec : Ir.ListingSpec) (line : Array ListingHighlight.Token) :
    Array CodeUnit := Id.run do
  let mut out : Array CodeUnit := #[]
  let mut col := 0
  let mut src := 0
  for m in Listing.codeMarks spec.wrapAt line do
    let (kept, next) := spec.layoutText col (String.singleton m.c)
    for d in kept.toList do
      out := out.push { c := d, token := m.token, lex := m.lex, fb := m.fb, sourceCol := src
                        space := m.space }
    col := next
    src := src + 1
  return out

/-- How a wrap before unit `b` ranks, read off the
units on either side under the listing's wrap rule. -/
private def CodeUnit.rank (wrap : Ir.ListingWrap) (wide : Nat → Bool) (us : Array CodeUnit)
    (b : Nat) : Nat :=
  match us[b - 1]?, us[b]? with
  | some p, some q =>
    if p.space then 0
    else match wrap with
      | .units => if q.space || p.lex != q.lex then 1 else 0
      | .whitespaceFirst =>
        if q.space then 2
        else if p.fb != q.fb && (p.lex != q.lex || wide (b - 1)) then 1
        else 0
  | _, _ => 0

private theorem CodeUnit.rank_mem (wrap : Ir.ListingWrap) (wide : Nat → Bool)
    (us : Array CodeUnit) (b : Nat) (h : CodeUnit.rank wrap wide us b ≠ 0) :
    ∃ p q, us[b - 1]? = some p ∧ us[b]? = some q ∧ p.space = false ∧
      ((wrap = .units ∧ (q.space = true ∨ p.lex ≠ q.lex)) ∨
        (wrap = .whitespaceFirst ∧ (q.space = true ∨
          (p.fb ≠ q.fb ∧ (p.lex ≠ q.lex ∨ wide (b - 1) = true))))) := by
  unfold CodeUnit.rank at h
  split at h
  · rename_i p q hp hq
    refine ⟨p, q, hp, hq, ?_⟩
    cases hs : p.space
    · refine ⟨rfl, ?_⟩
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      cases wrap with
      | units =>
        refine Or.inl ⟨rfl, ?_⟩
        by_cases hu : (q.space || p.lex != q.lex) = true
        · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hu
          exact hu
        · simp [hu] at h
      | whitespaceFirst =>
        refine Or.inr ⟨rfl, ?_⟩
        cases hqs : q.space
        · simp only [hqs, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hw : (p.fb != q.fb && (p.lex != q.lex || wide (b - 1))) = true
          · simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hw
            exact Or.inr hw
          · simp [hw] at h
        · exact Or.inl rfl
    · simp [hs] at h
  · simp at h

/-- A segment's scan from `b` while `fit` holds: the last first-rank
wrap, the last wrap of any rank, and where it stopped. -/
private def codeScan (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat) (top any : Option Nat) :
    Option Nat × Option Nat × Nat :=
  if b < n then
    if fit b then
      codeScan rank fit n (b + 1) (if rank b == 2 then some b else top)
        (if rank b != 0 then some b else any)
    else (top, any, b)
  else (top, any, b)
termination_by n - b

private theorem codeScan_top_mem (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat) (top any : Option Nat)
    (t : Nat) (h : (codeScan rank fit n b top any).1 = some t) :
    top = some t ∨ (b ≤ t ∧ t < n ∧ rank t = 2) := by
  revert h
  induction b, top, any using codeScan.induct rank fit n with
  | case1 b top any hb hf ih =>
    intro h
    rw [codeScan] at h
    simp only [hb, hf, ↓reduceIte] at h
    rcases ih h with h' | ⟨h1, h2, h3⟩
    · by_cases hr : (rank b == 2) = true
      · simp only [hr, ↓reduceDIte, Option.some.injEq] at h'
        subst h'
        exact Or.inr ⟨Nat.le_refl _, hb, by simpa using hr⟩
      · simp only [hr] at h'
        exact Or.inl h'
    · exact Or.inr ⟨by omega, h2, h3⟩
  | case2 b top any hb hf =>
    intro h
    rw [codeScan] at h
    simp only [hb, hf, ↓reduceIte] at h
    exact Or.inl h
  | case3 b top any hb =>
    intro h
    rw [codeScan] at h
    simp only [hb, ↓reduceIte] at h
    exact Or.inl h

private theorem codeScan_any_mem (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat) (top any : Option Nat)
    (t : Nat) (h : (codeScan rank fit n b top any).2.1 = some t) :
    any = some t ∨ (b ≤ t ∧ t < n ∧ rank t ≠ 0) := by
  revert h
  induction b, top, any using codeScan.induct rank fit n with
  | case1 b top any hb hf ih =>
    intro h
    rw [codeScan] at h
    simp only [hb, hf, ↓reduceIte] at h
    rcases ih h with h' | ⟨h1, h2, h3⟩
    · by_cases hr : (rank b != 0) = true
      · simp only [hr, ↓reduceDIte, Option.some.injEq] at h'
        subst h'
        exact Or.inr ⟨Nat.le_refl _, hb, by simpa using hr⟩
      · simp only [hr] at h'
        exact Or.inl h'
    · exact Or.inr ⟨by omega, h2, h3⟩
  | case2 b top any hb hf =>
    intro h
    rw [codeScan] at h
    simp only [hb, hf, ↓reduceIte] at h
    exact Or.inl h
  | case3 b top any hb =>
    intro h
    rw [codeScan] at h
    simp only [hb, ↓reduceIte] at h
    exact Or.inl h

private theorem codeScan_stop_between (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat) (top any : Option Nat)
    (h : b ≤ n) : b ≤ (codeScan rank fit n b top any).2.2 ∧
      (codeScan rank fit n b top any).2.2 ≤ n := by
  revert h
  induction b, top, any using codeScan.induct rank fit n with
  | case1 b top any hb hf ih =>
    intro _
    rw [codeScan]
    simp only [hb, hf, ↓reduceIte]
    simp only [dite_eq_ite] at ih
    have := ih (by omega)
    omega
  | case2 b top any hb hf =>
    intro _
    rw [codeScan]
    simp only [hb, hf, Bool.false_eq_true, ↓reduceIte]
    omega
  | case3 b top any hb =>
    intro _
    rw [codeScan]
    simp only [hb, ↓reduceIte]
    omega

private theorem codeScan_any_monotone (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat)
    (top any : Option Nat) (a : Nat) (h : any = some a) (ha : a ≤ b) (han : a < n) :
    ∃ t, (codeScan rank fit n b top any).2.1 = some t ∧ a ≤ t ∧ t < n := by
  revert a
  induction b, top, any using codeScan.induct rank fit n with
  | case1 b top any hb hf ih =>
    intro a h ha han
    rw [codeScan]
    simp only [hb, hf, ↓reduceIte]
    simp only [dite_eq_ite] at ih
    by_cases hr : (rank b != 0) = true
    · simp only [hr, ↓reduceIte] at ih ⊢
      obtain ⟨t, ht, hle, hlt⟩ := ih b rfl (by omega) hb
      exact ⟨t, ht, by omega, hlt⟩
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      exact ih a h (by omega) han
  | case2 b top any hb hf =>
    intro a h _ han
    rw [codeScan]
    simp only [hb, hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨a, h, Nat.le_refl _, han⟩
  | case3 b top any hb =>
    intro a h _ han
    rw [codeScan]
    simp only [hb, ↓reduceIte]
    exact ⟨a, h, Nat.le_refl _, han⟩

private theorem codeScan_top_monotone (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat)
    (top any : Option Nat) (a : Nat) (h : top = some a) (ha : a ≤ b) (han : a < n) :
    ∃ t, (codeScan rank fit n b top any).1 = some t ∧ a ≤ t ∧ t < n := by
  revert a
  induction b, top, any using codeScan.induct rank fit n with
  | case1 b top any hb hf ih =>
    intro a h ha han
    rw [codeScan]
    simp only [hb, hf, ↓reduceIte]
    simp only [dite_eq_ite] at ih
    by_cases hr : (rank b == 2) = true
    · simp only [hr, ↓reduceIte] at ih ⊢
      obtain ⟨t, ht, hle, hlt⟩ := ih b rfl (by omega) hb
      exact ⟨t, ht, by omega, hlt⟩
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      exact ih a h (by omega) han
  | case2 b top any hb hf =>
    intro a h _ han
    rw [codeScan]
    simp only [hb, hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨a, h, Nat.le_refl _, han⟩
  | case3 b top any hb =>
    intro a h _ han
    rw [codeScan]
    simp only [hb, ↓reduceIte]
    exact ⟨a, h, Nat.le_refl _, han⟩


private theorem codeScan_any_between (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat)
    (top any : Option Nat) (c : Nat) (hbc : b ≤ c) (hc : c < n) (hr : rank c ≠ 0)
    (hfit : ∀ k, b ≤ k → k ≤ c → fit k = true) :
    ∃ t, (codeScan rank fit n b top any).2.1 = some t ∧ c ≤ t ∧ t < n := by
  revert hbc hfit
  induction b, top, any using codeScan.induct rank fit n with
  | case1 b top any hb hf ih =>
    intro hbc hfit
    rw [codeScan]
    simp only [hb, hf, ↓reduceIte]
    by_cases hbc' : b = c
    · subst hbc'
      have hr' : (rank b != 0) = true := by simpa using hr
      simp only [hr', ↓reduceIte]
      exact codeScan_any_monotone rank fit n (b + 1) _ _ b rfl (by omega) hb
    · simp only [dite_eq_ite] at ih
      exact ih (by omega) (fun k hk hkc => hfit k (by omega) hkc)
  | case2 b top any hb hf =>
    intro hbc hfit
    exact absurd (hfit b (Nat.le_refl _) hbc) hf
  | case3 b top any hb =>
    intro hbc _
    omega


private theorem codeScan_top_between (rank : Nat → Nat) (fit : Nat → Bool) (n b : Nat)
    (top any : Option Nat) (c : Nat) (hbc : b ≤ c) (hc : c < n) (hr : rank c = 2)
    (hfit : ∀ k, b ≤ k → k ≤ c → fit k = true) :
    ∃ t, (codeScan rank fit n b top any).1 = some t ∧ c ≤ t ∧ t < n := by
  revert hbc hfit
  induction b, top, any using codeScan.induct rank fit n with
  | case1 b top any hb hf ih =>
    intro hbc hfit
    rw [codeScan]
    simp only [hb, hf, ↓reduceIte]
    by_cases hbc' : b = c
    · subst hbc'
      have hr' : (rank b == 2) = true := by simpa using hr
      simp only [hr', ↓reduceIte]
      exact codeScan_top_monotone rank fit n (b + 1) _ _ b rfl (by omega) hb
    · simp only [dite_eq_ite] at ih
      exact ih (by omega) (fun k hk hkc => hfit k (by omega) hkc)
  | case2 b top any hb hf =>
    intro hbc hfit
    exact absurd (hfit b (Nat.le_refl _) hbc) hf
  | case3 b top any hb =>
    intro hbc _
    omega

/-- The first wrap at or past `b`, or the line's end. -/
private def codeNext (rank : Nat → Nat) (n b : Nat) : Nat :=
  if b < n then if rank b != 0 then b else codeNext rank n (b + 1) else n
termination_by n - b

private theorem codeNext_mem (rank : Nat → Nat) (n b : Nat) (h : b ≤ n) :
    (b ≤ codeNext rank n b ∧ codeNext rank n b ≤ n) ∧
      (codeNext rank n b = n ∨ rank (codeNext rank n b) ≠ 0) := by
  revert h
  induction b using codeNext.induct rank n with
  | case1 b hb hr =>
    intro _
    rw [codeNext]
    simp only [hb, hr, ↓reduceIte]
    exact ⟨⟨Nat.le_refl _, by omega⟩, Or.inr (by simpa using hr)⟩
  | case2 b hb hr ih =>
    intro _
    rw [codeNext]
    simp only [hb, hr, Bool.false_eq_true, ↓reduceIte]
    have := ih (by omega)
    exact ⟨⟨by omega, this.1.2⟩, this.2⟩
  | case3 b hb =>
    intro _
    rw [codeNext]
    simp only [hb, ↓reduceIte]
    exact ⟨⟨by omega, Nat.le_refl _⟩, by simp⟩

private def codeChoose (rank : Nat → Nat) (n : Nat) : Option Nat × Option Nat × Nat → Nat
  | (some b, _, _) => b
  | (none, some b, _) => b
  | (none, none, stop) => codeNext rank n stop

/-- Where a segment from `s` ends: the whole rest where it fits, else its last first-rank
wrap that fits, else its last wrap of any rank, else the first wrap past it. -/
private def codeCut (rank : Nat → Nat) (width : Nat → Nat → Sp) (limit : Sp) (s n : Nat) : Nat :=
  if width s n ≤ limit then n
  else codeChoose rank n (codeScan rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none)

private theorem codeCut_mem (rank : Nat → Nat) (width : Nat → Nat → Sp) (limit : Sp)
    (s n : Nat) (h : s < n) :
    (s < codeCut rank width limit s n ∧ codeCut rank width limit s n ≤ n) ∧
      (codeCut rank width limit s n = n ∨ rank (codeCut rank width limit s n) ≠ 0) := by
  unfold codeCut
  by_cases hw : width s n ≤ limit
  · simp only [hw, ↓reduceIte]
    exact ⟨⟨h, Nat.le_refl n⟩, by simp⟩
  · simp only [hw, ↓reduceIte]
    have htop := codeScan_top_mem rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none
    have hany := codeScan_any_mem rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none
    have hstop := codeScan_stop_between rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none
      (by omega)
    generalize codeScan rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none = r
      at htop hany hstop
    obtain ⟨t, a, st⟩ := r
    dsimp only at hstop
    cases t with
    | some b =>
      rcases htop b rfl with h' | ⟨h1, h2, h3⟩
      · simp at h'
      · exact ⟨⟨by simp only [codeChoose]; omega, by simp only [codeChoose]; omega⟩,
          Or.inr (by simp only [codeChoose]; omega)⟩
    | none =>
      cases a with
      | some b =>
        rcases hany b rfl with h' | ⟨h1, h2, h3⟩
        · simp at h'
        · exact ⟨⟨by simp only [codeChoose]; omega, by simp only [codeChoose]; omega⟩,
            Or.inr (by simpa only [codeChoose] using h3)⟩
      | none =>
        have := codeNext_mem rank n st hstop.2
        simp only [codeChoose]
        exact ⟨⟨by omega, this.1.2⟩, this.2⟩


private theorem codeCut_space_mem (rank : Nat → Nat) (width : Nat → Nat → Sp) (limit : Sp)
    (s n c : Nat) (hc : s < c) (hcn : c < n) (hr : rank c = 2)
    (hfit : ∀ k, s < k → k ≤ c → width s k ≤ limit) (hwide : ¬ width s n ≤ limit) :
    rank (codeCut rank width limit s n) = 2 := by
  unfold codeCut
  simp only [hwide, ↓reduceIte]
  obtain ⟨t, ht, _, _⟩ := codeScan_top_between rank (fun b => decide (width s b ≤ limit)) n
    (s + 1) none none c (by omega) hcn hr (fun k hk hkc => by simpa using hfit k (by omega) hkc)
  have htop := codeScan_top_mem rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none
  generalize codeScan rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none = r
    at ht htop ⊢
  obtain ⟨t', a, st⟩ := r
  simp only at ht
  subst ht
  rcases htop t rfl with h' | ⟨_, _, h3⟩
  · simp at h'
  · simpa only [codeChoose] using h3


private theorem codeCut_between (rank : Nat → Nat) (width : Nat → Nat → Sp) (limit : Sp)
    (s n c : Nat) (hc : s < c) (hcn : c < n) (hr : rank c ≠ 0)
    (hfit : ∀ k, s < k → k ≤ c → width s k ≤ limit) (hwide : ¬ width s n ≤ limit)
    (hrank : rank c = 2 ∨ rank (codeCut rank width limit s n) ≠ 2) :
    c ≤ codeCut rank width limit s n ∧ codeCut rank width limit s n ≤ n := by
  have hle := (codeCut_mem rank width limit s n (by omega)).1.2
  refine ⟨?_, hle⟩
  have hf : ∀ k, s + 1 ≤ k → k ≤ c → (fun b => decide (width s b ≤ limit)) k = true :=
    fun k hk hkc => by simpa using hfit k (by omega) hkc
  have hany := codeScan_any_between rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none
    c (by omega) hcn hr hf
  have htopmem := codeScan_top_mem rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none
  unfold codeCut at hrank ⊢
  simp only [hwide, ↓reduceIte] at hrank ⊢
  rcases hrank with h2 | hcut
  · obtain ⟨t, ht, hle', _⟩ := codeScan_top_between rank (fun b => decide (width s b ≤ limit)) n
      (s + 1) none none c (by omega) hcn h2 hf
    generalize codeScan rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none = r at ht ⊢
    obtain ⟨t', a, st⟩ := r
    simp only at ht
    subst ht
    simpa only [codeChoose] using hle'
  · obtain ⟨t, ht, hle', _⟩ := hany
    generalize codeScan rank (fun b => decide (width s b ≤ limit)) n (s + 1) none none = r
      at ht hcut htopmem ⊢
    obtain ⟨t', a, st⟩ := r
    simp only at ht
    subst ht
    cases t' with
    | none => simpa only [codeChoose] using hle'
    | some b =>
      rcases htopmem b rfl with h' | ⟨_, _, h3⟩
      · simp at h'
      · simp only [codeChoose] at hcut
        exact absurd h3 hcut

/-- The segment's cut with the bounds a recursion's measure reads. -/
private def codeCutIn (rank : Nat → Nat) (width : Nat → Nat → Sp) (limit : Sp) (s n : Nat)
    (h : s < n) : {b : Nat // s < b ∧ b ≤ n} :=
  ⟨codeCut rank width limit s n, (codeCut_mem rank width limit s n h).1⟩

/-- The unit after a wrap: its spaces dropped, scanned in place. -/
private def skipSpaces (us : Array CodeUnit) (n b : Nat) : Nat :=
  if b < n then
    if (us[b]?.map (·.space)).getD false then skipSpaces us n (b + 1) else b
  else b
termination_by n - b

private theorem skipSpaces_between (us : Array CodeUnit) (n b : Nat) (h : b ≤ n) :
    b ≤ skipSpaces us n b ∧ skipSpaces us n b ≤ n := by
  revert h
  induction b using skipSpaces.induct us n with
  | case1 b hb hs ih =>
    intro _
    rw [skipSpaces]
    simp only [hb, hs, ↓reduceIte]
    have := ih (by omega)
    omega
  | case2 b hb hs =>
    intro _
    rw [skipSpaces]
    simp only [hb, hs, Bool.false_eq_true, ↓reduceIte]
    omega
  | case3 b hb =>
    intro h
    rw [skipSpaces]
    simp only [hb, ↓reduceIte]
    omega

/-- The segments a source line wraps into from `s`, each cut by
`codeCut` against `first` or `cont`, the spaces at each wrap dropped. -/
private def codeSegments (rank : Nat → Nat) (width : Nat → Nat → Sp) (us : Array CodeUnit)
    (first cont : Sp) (n s : Nat) (out : Array (Nat × Nat)) : Array (Nat × Nat) :=
  if h : s < n then
    match codeCutIn rank width (if out.isEmpty then first else cont) s n h with
    | ⟨b, hb⟩ =>
      have : n - skipSpaces us n b < n - s := by
        have := skipSpaces_between us n b hb.2
        omega
      codeSegments rank width us first cont n (skipSpaces us n b) (out.push (s, b))
  else out
termination_by n - s

private theorem codeSegments_breaks_mem (rank : Nat → Nat) (width : Nat → Nat → Sp)
    (us : Array CodeUnit) (first cont : Sp) (n s : Nat) (out : Array (Nat × Nat)) :
    ∀ seg ∈ codeSegments rank width us first cont n s out,
      seg ∈ out ∨ seg.2 = n ∨ rank seg.2 ≠ 0 := by
  induction s, out using codeSegments.induct rank width us first cont n with
  | case1 s out h b hb hcut _ ih =>
    intro seg hseg
    have hval : codeCut rank width (if out.isEmpty then first else cont) s n = b := by
      have := congrArg Subtype.val hcut
      simpa [codeCutIn] using this
    unfold codeSegments at hseg
    simp only [h, ↓reduceDIte, codeCutIn, hval] at hseg
    rcases ih seg hseg with hin | hrest
    · rcases Array.mem_push.mp hin with hold | rfl
      · exact Or.inl hold
      · have hm := (codeCut_mem rank width (if out.isEmpty then first else cont) s n h).2
        rw [hval] at hm
        exact Or.inr hm
    · exact Or.inr hrest
  | case2 s out h =>
    intro seg hseg
    unfold codeSegments at hseg
    simp only [h, ↓reduceDIte] at hseg
    exact Or.inl hseg

/-- Which units stand in a run wider than a continuation line `cont` wide. -/
private def codeWide (us : Array CodeUnit) (widths : Array Sp) (cont : Sp) : Array Bool := Id.run do
  let mut flags : Array Bool := Array.replicate us.size false
  let mut start := 0
  let mut w : Sp := 0
  for i in [0:us.size + 1] do
    let ends := i == us.size || (i > 0 && (us[i]?.map (·.lex)) != (us[i - 1]?.map (·.lex)))
    if ends && start < i then
      if w > cont then
        for j in [start:i] do
          flags := flags.set! j true
      start := i
      w := 0
    w := w + widths.getD i 0
  return flags

/-- Where a source line wraps (`Ir.ListingWrap`): each segment filled to its last
unit that fits under listings' rule, or to its last space under whitespace first. -/
private def codeWraps (wrap : Ir.ListingWrap) (us : Array CodeUnit) (widths : Array Sp)
    (first cont : Sp) : Array (Nat × Nat) :=
  let pre : Array Sp := widths.foldl (fun acc w => acc.push ((acc.back?.getD 0) + w)) #[0]
  let wide := codeWide us widths cont
  codeSegments (CodeUnit.rank wrap (fun i => wide.getD i false) us)
    (fun a b => (pre[b]?.getD 0) - (pre[a]?.getD 0)) us first cont us.size 0 #[]

private theorem codeWraps_breaks_mem (wrap : Ir.ListingWrap) (us : Array CodeUnit)
    (widths : Array Sp) (first cont : Sp) :
    ∀ seg ∈ codeWraps wrap us widths first cont, seg.2 = us.size ∨
      ∃ p q, us[seg.2 - 1]? = some p ∧ us[seg.2]? = some q ∧ p.space = false ∧
        ((wrap = .units ∧ (q.space = true ∨ p.lex ≠ q.lex)) ∨
          (wrap = .whitespaceFirst ∧ (q.space = true ∨
            (p.fb ≠ q.fb ∧ (p.lex ≠ q.lex ∨
              (codeWide us widths cont).getD (seg.2 - 1) false = true))))) := by
  intro seg hseg
  rcases codeSegments_breaks_mem _ _ us first cont us.size 0 #[] seg hseg with h | h | h
  · simp at h
  · exact Or.inl h
  · exact Or.inr (CodeUnit.rank_mem wrap _ us seg.2 h)

/-- A caption as classes.dtx's `\@makecaption` sets it: centred when it fits one
line, else a paragraph, `cmargin` in from either side of the measure. -/
private def collectCaption (r rf : Rd) (a : Acc) (caption : Array Inline) (cmargin : Sp)
    (leaf : Option Nat) (span : Nat) (indent : Sp) : Acc :=
  let avail := (a.measure.getD r.geom.textWidth) - indent - 2 * cmargin
  let (w, a) := a.naturalWidth r r.geom.fontSize caption avail
  let saved := a.measure
  let a := { a with measure := some ((a.measure.getD r.geom.textWidth) - cmargin) }
  let a := collectPara rf a caption (indent + cmargin) (w ≤ avail) r.geom.fontSize
    (leaf := leaf) (span := span)
  { a with measure := saved }

private def collectVerbatim (r : Rd) (a : Acc) (covered : Option Ir.Color) (s : String) (spec : Ir.ListingSpec) (indent : Sp) : Acc :=
  let a0 := a
  -- Code never hyphenates; a declared caption sets above it (listings.sty `captionpos`).
  let a := match spec.caption with
    | some (n, cap) =>
      let (a, leaf) := a.leafRange 1
      let a := collectCaption r r a (Ir.listingCaption r.locale n cap) 0 leaf 1 indent
      a.addvspace (r.resolve ((a.tokens.find? "captionsep").getD
        (Ir.captionSepDefault r.geom.fontSize)))
    | none => a
  -- A listing's own ground and its package's space after each line (`Ir.ListingSpec.lineOverlap`).
  let own := spec.groundIn a.pal .print
  let ground := (own.map (·.1)).or a.ground
  let sty := applyStyle r.geom.scale {} spec.fontSize
  let overlap := if sty.leading.isSome then 0 else spec.lineOverlap
  -- A listing owns its line box, given an explicit size and skip rather than the body's strut.
  let avail := (a.measure.getD r.geom.textWidth) - indent
  let (size, leading) := sty.metrics r.geom.fontSize r.xHeight avail r.geom.textHeight
  let leading := leading.getD
    (Ir.stepSkip (sty.stepLead r.geom.skips r.geom.fontSize) size r.geom.leading)
  -- A `breakIndent` listing breaks here where its wrap allows (`codeWraps`), so none re-flows.
  let wrap := if spec.breakLines then spec.breakIndent else none
  let mono := r.fs.get (r.fs.lookup 2 400 false)
  let advance (c : Char) : Sp :=
    match glyphOf size mono c with
    | some g => g.2.2
    | none =>
      match (r.fs.fallbackFor c).bind fun fb => glyphOf size (r.fs.get fb) c with
      | some g => g.2.2
      | none => 0
  -- Code is no markup, so a code line's site names no written construct (`Diag.Spelling`).
  let codeSource (i sourceColumn : Nat) : Option Span :=
    spec.source.map fun source =>
      let line := source.pos.line + i - 1 +
        (if s.startsWith "\n" || s.startsWith "\r\n" then 1 else 0)
      let col := (if line == source.pos.line then source.pos.col else 1) + sourceColumn
      { source with pos := { source.pos with line := line, col := col, command := none } }
  -- Line numbers are generated furniture: right-aligned mono digits held by no-break spaces.
  let inner : Array Ir.Inline := Id.run do
      let lines := spec.tokenLines s
      let brushes := Listing.brushes a.pal ground covered spec.style lines
      let w := (toString lines.size).length
      let mut out : Array Ir.Inline := #[]
      let mut i := 0
      for line in lines do
        i := i + 1
        unless out.isEmpty do
          let taken := if i == 2 then 2 * overlap else overlap
          out := out.push (.linebreak { width := Dim.Length.ofSp (-taken) })
        let numbered := if spec.numbers then
            let numStr := toString i
            String.ofList (List.replicate (w - numStr.length) '\u00a0') ++ numStr ++ "\u00a0\u00a0"
          else ""
        unless numbered.isEmpty do
          out := out.push (.text numbered)
        if (ListingHighlight.lineText line).isEmpty then
          out := out.push (.text "\u00a0")
        else
          -- Source columns count authored scalars; display columns expand tabs.
          let (physical, hang) : Array (Array (ListingHighlight.Token × Nat)) × Sp :=
            match wrap with
            | none => Id.run do
              let mut column := 0
              let mut sourceColumn := 0
              let mut pieces := #[]
              for token in line do
                let (kept, nextColumn) := spec.layoutText column token.text
                column := nextColumn
                pieces := pieces.push ({ token with text := kept }, sourceColumn)
                sourceColumn := sourceColumn + token.text.length
              return (#[pieces], 0)
            | some breakIndent => Id.run do
              let us := codeUnits { spec with breakLines := false } line
              let ws := us.map (advance ·.c)
              let prefixW := (numbered.toList.map advance).sum
              let lead : Sp := Id.run do
                let mut w : Sp := 0
                for u in us do
                  if u.space then w := w + advance u.c else break
                return w
              let hang := prefixW + lead + breakIndent
              let mut physical := #[]
              for (a0, b0) in codeWraps spec.wrapAt us ws (avail - prefixW) (avail - hang) do
                let mut pieces := #[]
                let mut k := a0
                for _ in [a0:b0] do
                  if k ≥ b0 then break
                  let some first := us[k]? | break
                  let mut chars : Array Char := #[]
                  for _ in [k:b0] do
                    match us[k]? with
                    | some u =>
                      if k < b0 && u.token == first.token then
                        chars := chars.push u.c
                        k := k + 1
                      else break
                    | none => break
                  let some token := line[first.token]? | break
                  pieces := pieces.push
                    ({ token with text := String.ofList chars.toList }, first.sourceCol)
                physical := physical.push pieces
              return (physical, hang)
          let mut j := 0
          for pieces in physical do
            if j > 0 then
              out := out.push (.linebreak {})
              out := out.push (.hspace (.lit { width := .ofSp hang }) true)
            j := j + 1
            let mut k := 0
            for run in Listing.paintLine a.pal ground covered spec.style brushes
                (pieces.map (·.1)) do
              let mut body : Array Ir.Inline := #[]
              for piece in run.tokens do
                let sourceColumn := (pieces[k]?.map (·.2)).getD 0
                k := k + 1
                -- A line's site is a scalar that lays down ink.
                let source := if piece.text.all Listing.blank then none
                  else codeSource i sourceColumn
                body := body.push
                  (source.map (fun span => .located span #[.text piece.text]) |>.getD (.text piece.text))
              let painted := Listing.paintRun run body
              out := out ++ painted
      pure #[.styled .mono out]
  let inner := match covered with
    | some c => #[.colored c none inner]
    | none => inner
  let (a, leaf) := a.leafRange 1
  -- Plain text on the listing's own ground is fitted to it (`Listing.groundInk`), as the HTML's is.
  let a := match own with
    | some (g, _) =>
      { a.pushOp (.regionOpen (.surface (r.shown g) 0 (r.geom.hmargin + indent) avail false))
        with ground := some g, fg := Listing.groundInk a.pal g a.fg }
    | none => a
  let done := collectPara { r with pats := none, geom := { r.geom with justify := false } }
    a inner indent false size
    (baseStyle := { leading := some (.lit { width := .ofSp leading }) })
    (leaf := leaf) (span := 1) (literalLines := true)
    (strut := if spec.lineStrut then some leading else none)
  match own with
  | some _ => { done.pushOp .regionClose with ground := a0.ground, fg := a0.fg }
  | none => done

/-- A listing with the space its environment sets around it where
the class frames it as TeX does (`Ir.ListingFrame.onPage`). -/
private def collectListing (r : Rd) (a : Acc) (covered : Option Ir.Color) (s : String)
    (spec : Ir.ListingSpec) (indent : Sp) : Acc :=
  let trivlist (a : Acc) : Glue := r.resolve (Ir.trivlistSkipFor r.lists a.tokens r.geom.fontSize
    (a.itemDepth + a.enumDepth + a.quoteDepth))
  match spec.frame with
  | .trivlist =>
    let g := trivlist a
    (collectVerbatim r (a.trivSpace g) covered s spec indent).trivSpace g
  | .list =>
    let lv := a.itemDepth + a.enumDepth + a.quoteDepth + 1
    match Ir.listSkips r.lists r.geom.fontSize lv with
    | some sk =>
      let g := (r.resolve sk.topsep).add (r.resolve (Ir.partopsepFor r.lists r.geom.fontSize lv a.tokens))
      let top := if a.afterHeading then a.flushGap r else (a.listSpace g).flushGap r
      (collectVerbatim r top covered s spec indent).listSpace g
    | none => collectVerbatim r a covered s spec indent
  | .none => collectVerbatim r a covered s spec indent

private def collectAlgorithm (r : Rd) (a : Acc) (numbered semis : Bool) (lines : Array Ir.AlgLine) (indent : Sp) : Acc :=
  -- Pseudocode: unhyphenated, unjustified display lines, one `algindent` per depth (algorithm2e).
  let words := Ir.algWords r.locale.tag
  let muted := Ir.mutedOf a.pal
  let stepInd := (r.resolve ((a.tokens.find? "algindent").getD
    { width := { em := 1500 } })).width
  -- The number column stands inside the algorithm's box, at least as wide as its widest number.
  let numCol :=
    if numbered then
      let face := r.fs.get 0
      let digit := (List.range 10).foldl (fun m k =>
        max m (scaledAt r.geom.fontSize face (face.advance (Char.ofNat (48 + k))))) 0
      max (r.resolve ((a.tokens.find? "algnumindent").getD
          { width := { em := 2000 } })).width
        (digit * (toString lines.size).length + r.geom.fontSize / 2)
    else 0
  let indent := indent + numCol
  let rAlg := { r with pats := none, geom := { r.geom with justify := false } }
  -- One `.code` node holds every line's leaves; a keyword-only line rides the first leaf.
  let codeLeaf : Option Nat :=
    if lines.any (fun l => Struct.leafCountInlines l.content + Struct.leafCountInlines (l.comment.getD #[]) > 0)
    then some a.leafNext else none
  (lines.foldl (fun (ai : Acc × Nat) l =>
    let (a, i) := ai
    -- The content is wrapped only around a non-anchor, so `rendered` reads it the same.
    let l := { l with
      content := if l.content.all (· matches Inline.label _) then l.content
        else markContent l.content
      comment := l.comment.map fun c => if Struct.leafCountInlines c == 0 then c else markContent c }
    let content := Ir.AlgLine.rendered words semis muted l
    let marker : Option (Array Ir.Inline) := if numbered then
        some #[Ir.Inline.colored muted (some (.role .muted)) #[.text s!"{i}"]]
      else none
    let span := Struct.leafCountInlines l.content + Struct.leafCountInlines (l.comment.getD #[])
    let (a, leaf) := a.leafRange span
    (collectPara rAlg a content (indent + stepInd * (l.depth : Int)) false
      r.geom.fontSize (marker := marker) (markerIndent := some indent)
      (leaf := leaf <|> codeLeaf) (span := span),
      i + 1)) (a, 1)).1

private def collectFramefoot (a : Acc) (content : Array Inline) : Acc :=
  -- A `\framefoot` state change: no line; empty clears back to the chrome default.
  let a := (a.leafRange (Struct.leafCountInlines content)).1
  { a with frameFoot := if content.isEmpty then none else some content }

private def collectRuleBlock (r : Rd) (a : Acc) (color : Ir.Color) (thickness : SymGlue) : Acc :=
  -- The title page's separator: palette `separator`, token `separatorheight`, the text width.
  let a := a.flushGap r
  { a with ops := a.ops.push (.hrule color (r.resolve thickness).width) }

/-- Resolve the shared block inset in the body's measured font units. -/
@[expose] public def titledPadding (fontSize xHeight : Sp) : Sp :=
  Ir.titledPadding.resolve fontSize xHeight

public theorem titledPadding_projects (fontSize xHeight : Sp) :
    titledPadding fontSize xHeight = 3 * xHeight / 4 :=
  Ir.titledPadding_contract fontSize xHeight

/-- The inset a font set's body face resolves at the page's body size. -/
public def titledPaddingOf (fs : FontSet) (geom : Geom) : Sp :=
  titledPadding geom.fontSize (fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm)

/-- A block title's `\baselineskip` under its font template
(`Ir.blockTitleLeading`), resolved in the body's font. -/
private def titleLeading (r : Rd) (font : Option (Array Inline)) : Sp :=
  (Ir.blockTitleLeading r.geom.scale r.geom.fontSize r.geom.leading
    (MeasureValues.horizontal r.geom.textWidth r.geom.textHeight) font).resolve
    r.geom.fontSize r.xHeight

/-- The face and size a block title's template sets its content in. -/
private def titleFaceIn (geom : Geom) (fs : FontSet) (xHeight : Sp)
    (font : Option (Array Inline)) : Font × Sp :=
  let axes := (font.bind Ir.fontAxesOf).getD {}
  let sty := ([axes.size, axes.shape, axes.series, axes.family].filterMap id).foldl
    (applyStyle geom.scale) ({ weight := .b } : TextStyle)
  let size := (sty.metrics geom.fontSize xHeight geom.textWidth geom.textHeight).1
  (fs.get (fs.lookup sty.slot sty.weight.css sty.italic), size)

/-- A block title's `\baselineskip` and its cap height,
which a rule reaching by the title's lines reads. -/
private def titleMetricsIn (geom : Geom) (fs : FontSet) (xHeight : Sp)
    (font : Option (Array Inline)) : Sp × Sp :=
  let lead := (Ir.blockTitleLeading geom.scale geom.fontSize geom.leading
    (MeasureValues.horizontal geom.textWidth geom.textHeight) font).resolve geom.fontSize xHeight
  let (face, size) := titleFaceIn geom fs xHeight font
  (lead, scaledAt size face (face.charHeight 'H').toNat)

/-- Where the web page stands a rule reaching by a block title's lines,
from CSS 2.1 §10.8.1 line boxes read as TeX's strut-bounded box. -/
public def blockTitleRule (geom : Geom) (fs : FontSet) (styles : Ir.Styles) (kind : TitledKind)
    (reach : Ir.BlockReach) : Option Ir.BlockTitlePlace :=
  match reach with
  | .box => none
  | .lines height depth =>
    let font := Ir.blockTitleFont styles kind
    let xHeight := fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm
    let (lead, cap) := titleMetricsIn geom fs xHeight font
    let (face, size) := titleFaceIn geom fs xHeight font
    let leaded (f : Font) (sz : Sp) : Sp × Sp :=
      leadedBox (scaledAt sz f f.ascent.toNat) (scaledAt sz f (-f.descent).toNat)
        (Ir.leadingFor sz geom.leading)
    let strut := leaded (fs.get (fs.lookup 0 700 false)) geom.fontSize
    let runs := leaded face size
    let b := max strut.1 runs.1
    let box := b + max strut.2 runs.2
    let h := height.resolve lead cap
    let d := depth.resolve lead cap
    let body := fs.get (fs.lookup 0 400 false)
    let next := scaledAt geom.fontSize body
      ((['b', 'd', 'f', 'h', 'k', 'l', 'H'].map body.charHeight).foldl max 0).toNat
    let prev := scaledAt geom.fontSize body
      ((['g', 'j', 'p', 'q', 'y'].map body.charDepth).foldl max 0).toNat
    let bs := Ir.leadingFor geom.fontSize geom.leading
    let dn := lead * 3 / 10
    let inset := match Ir.blockShapeOf styles kind with
      | some sh => if sh.title.parskip then (geom.parskip.resolve geom.fontSize xHeight).width else 0
      | none => 0
    let rise := max 0 (h + dn - inset)
    let line := inset + lead * 7 / 10
    let room := texBaselineGap bs (max dn d) next - texBaselineGap bs dn next
    some { top := b - lead - h, bottom := box - b - d
           rise := texBaselineGap bs prev (line + rise) - texBaselineGap bs prev line
           riseMany := texBaselineGap bs prev (line + lead + rise) - texBaselineGap bs prev (line + lead)
           room := room, depth := d
           bodyBelow := (leaded body geom.fontSize).2 }

/-- The part below its baseline of a web block's last line box when
that line is a listing's (CSS 2.1 §10.8.1); `none` otherwise. -/
public def blockLastBelow (geom : Geom) (fs : FontSet) (b : Option Ir.Block) : Option Sp :=
  match b with
  | some (.verbatim _ _ spec) =>
    match spec.fontSize with
    | .size n =>
      let size := Ir.scaleStepIn geom.scale geom.fontSize n
      let pitch := Ir.stepSkip (Ir.stepLead geom.skips n geom.fontSize) geom.fontSize
        geom.leading - spec.lineOverlap
      let mono := fs.get (fs.lookup 2 400 false)
      some (leadedBox (scaledAt size mono mono.ascent.toNat) (scaledAt size mono (-mono.descent).toNat)
        (pitch * 1000 / max size 1 * size / 1000)).2
    | _ => none
  | _ => none

/-- A titled block's title colour box (beamerinnerthemedefault.sty `block begin`) at
the block's epoch: painted around its lines, or the box TeX's interline rule places. -/
private def collectTitledTitle (r : Rd) (a : Acc) (kind : TitledKind)
    (title : Array Inline) (indent pad x w : Sp) : Acc :=
  let look := Ir.titledLook a.pal kind
  let a := a.flushGap r
  match look.bar, title.isEmpty with
  | none, true => a.pushOp (.boxAnchor (.tex 0) 0 false)
  | some bar, true =>
    ((a.pushOp (.regionOpen (.surface (r.shown bar) pad x w false))).pushOp
      (.boxAnchor (.tex (2 * pad)) 0 true)).pushOp .regionClose
  | bar, false =>
    let saved := (a.fg, a.ground)
    let a := match bar with
      | some c => a.pushOp (.regionOpen (.surface (r.shown c) pad x w false))
      | none => a
    let a := { a with fg := r.shown look.fg, ground := bar.orElse fun _ => a.ground }
    let (a, leaf) := a.leafRange (Struct.leafCountInlines title)
    let font := Ir.blockTitleFont r.styles kind
    let shown := match font with
      | some tpl => Ir.fillTemplate tpl title
      | none => title
    -- In a breakable frame a block's title keeps its body's first lines: beamer's block is one box.
    let a := collectDisplay r a shown indent false r.geom.fontSize
      (baseStyle := { weight := .b }) (leaf := leaf) (span := Struct.leafCountInlines title)
      (keepNext := if r.breakableFrame then 2 * Ir.leadingFor r.geom.fontSize r.geom.leading
        else 0)
      (paintPadding := bar.map fun _ => pad)
      (texBox := if bar.isSome then none
        else some { inset := 0, more := false, leading := titleLeading r font })
    let a := if bar.isSome then a.pushOp .regionClose else a
    { a with fg := saved.1, ground := saved.2 }

/-- tcolorbox's box opening (`size=normal`): the box `\linewidth` wide, its top the
balanced skip below the band above, its title segment and body inset by `Ir.tcbInset`. -/
private def collectBoxOpen (r : Rd) (a : Acc) (title : Array Inline) (indent : Sp)
    (bodyBg : Option Ir.Color) : Acc × Sp :=
  let look := Ir.titledLook a.pal .box
  let x := r.geom.hmargin + indent
  let measure := a.measure.getD r.geom.textWidth
  let w := measure - indent
  let s := Ir.leadingFor r.geom.fontSize r.geom.leading / 2
  let bodyOpen (a : Acc) (rule : AnchorRule) (shift above : Sp) : Acc :=
    let a := match bodyBg with
      | some c => a.pushOp (.regionOpen (.surface (r.shown c)
          (Ir.tcbBottom + Ir.tcbBoxsep + Ir.tcbRule) x w true))
      | none => a
    ((a.pushOp (.boxAnchor rule shift bodyBg.isSome)).pushOp .noInterline).vskip { width := above }
  let a := { a with wantDefault := false }.flushGap r
  let a := if title.isEmpty then
      bodyOpen a (.balanced s) 0 (Ir.tcbRule + Ir.tcbBoxsep + Ir.tcbTop)
    else
      let a := match look.bar with
        | some c => a.pushOp (.regionOpen (.surface (r.shown c) (Ir.tcbBoxsep + Ir.tcbRule) x w true))
        | none => a
      let a := ((a.pushOp (.boxAnchor (.balanced s) 0 look.bar.isSome)).pushOp .noInterline).vskip
        { width := Ir.tcbRule + Ir.tcbBoxsep }
      let saved := (a.fg, a.ground)
      let a := { a with fg := r.shown look.fg, ground := look.bar.orElse fun _ => a.ground
                        measure := some (measure - Ir.tcbInset) }
      let (a, leaf) := a.leafRange (Struct.leafCountInlines title)
      let a := collectDisplay r a title (indent + Ir.tcbInset) false r.geom.fontSize
        (leaf := leaf) (span := Struct.leafCountInlines title)
      let a := { a with fg := saved.1, ground := saved.2, measure := some measure }
      let a := if look.bar.isSome then a.pushOp .regionClose else a
      bodyOpen a .flush (if look.bar.isSome then 0 else Ir.tcbBoxsep + Ir.tcbRule)
        (Ir.tcbBoxsep + Ir.tcbTop)
  ({ a with measure := some (measure - Ir.tcbInset) }, indent + Ir.tcbInset)

/-- Whether a block in its template sets its title's paragraph: a title it
shows, or an empty one its box or struts hold. -/
private def shapedSetsTitle (shape : Ir.BlockShape) (titled : Bool) : Bool :=
  shape.showsTitle titled && (titled || shape.title.boxed || shape.title.strut)

/-- A block in its kind's template (`Ir.BlockShape`), opened: the skips above,
the rules beside the box, the title in its box, and the body's opening. -/
private def collectShapedOpen (r : Rd) (a : Acc) (kind : TitledKind) (shape : Ir.BlockShape)
    (title : Array Inline) (body : Array Block) (indent : Sp) : Acc × Sp × Sp :=
  let measure := a.measure.getD r.geom.textWidth
  let len (g : SymGlue) : Sp := (r.resolve g).width
  let parskip := (r.resolve r.geom.texParskip).width
  let wholeL := len (shape.inset .whole .left)
  let wholeR := len (shape.inset .whole .right)
  let titleL := len (shape.inset .title .left)
  let titleR := len (shape.inset .title .right)
  let titled := !title.isEmpty
  let setsTitle := shapedSetsTitle shape titled
  let font := Ir.blockTitleFont r.styles kind
  let titleLeading := titleLeading r font
  let titleCap := (titleMetricsIn r.geom r.fs r.xHeight font).2
  let reachOf (e : Ir.BlockEdge) : Option EdgeReach := match e.reach with
    | .lines height depth =>
      some { height := height.resolve titleLeading titleCap
             depth := depth.resolve titleLeading titleCap }
    | .box => none
  let titleReach : Option (Sp × Sp) :=
    (shape.edges.filter (·.besideTitle)).foldl (fun acc e =>
      match reachOf e, acc with
      | some q, some (u, d) => some (max u q.height, max d q.depth)
      | some q, none => some (q.height, q.depth)
      | none, acc => acc) none
  let titleInset := if shape.title.parskip && (titled || shape.title.strut) then parskip else 0
  let between := r.resolve (Ir.blockSkipSum a.tokens (shape.skipsBetween titled))
  let wholeInset := if setsTitle then titleInset
    else between.width + (if shape.whole == some true then parskip else 0)
  let wx0 := r.geom.hmargin + indent + wholeL
  let wx1 := r.geom.hmargin + measure - wholeR
  let tx0 := wx0 + titleL
  let tx1 := wx1 - titleR
  let ruleX (e : Ir.BlockEdge) (x0 x1 : Sp) : Sp :=
    if e.side == .left then x0 - len e.sep - len e.width else x1 + len e.sep
  let opens (a : Acc) (beside : Ir.BlockEdge → Bool) (x0 x1 inset : Sp) : Acc :=
    shape.edges.foldl (fun a e =>
      if beside e then
        a.pushOp (.regionOpen (.edge (r.shown (e.ink a.pal)) (ruleX e x0 x1) (len e.width) inset
          (reachOf e)))
      else a) a
  let closes (a : Acc) (beside : Ir.BlockEdge → Bool) : Acc :=
    shape.edges.foldl (fun a e => if beside e then a.pushOp .regionClose else a) a
  let besideWhole (e : Ir.BlockEdge) : Bool := e.span == .whole && !e.besideTitle
  let above := r.resolve (Ir.blockSkipSum a.tokens (shape.skipsAbove titled))
  let a := { a.vskip above with wantDefault := !a.frameTop }
  let a := if shape.whole.isSome then opens (a.flushGap r) besideWhole wx0 wx1 wholeInset else a
  let a := if !setsTitle then a else
    let look := Ir.titledLook a.pal kind
    let titleInk := look.fg
    let saved := a.fg
    let a := if shape.title.boxed then opens (a.flushGap r) (·.besideTitle) tx0 tx1 titleInset
      else a
    let (ti, tm) := if shape.title.boxed then (tx0, tx1) else (wx0, wx1)
    let a := { a with fg := r.shown titleInk, measure := some (tm - r.geom.hmargin) }
    let (a, leaf) := a.leafRange (Struct.leafCountInlines title)
    let shown := if !titled then #[Inline.strut {}] else match font with
      | some tpl => Ir.fillTemplate tpl title
      | none => title
    let texBox : Option TexBox :=
      if shape.title.boxed then
        some { inset := titleInset, more := false, leading := titleLeading, reach := titleReach }
      else if shape.whole.isSome then
        some { inset := titleInset, more := true, leading := titleLeading }
      else some { inset := 0, more := false, leading := titleLeading, boxed := false }
    let strut := if shape.title.strut then some titleLeading else none
    let a := collectDisplay r a shown (ti - r.geom.hmargin) false r.geom.fontSize
      (baseStyle := { weight := .b }) (leaf := leaf) (span := Struct.leafCountInlines title)
      (strut := strut) (texBox := texBox)
    let a := if shape.title.boxed then closes a (·.besideTitle) else a
    let a := shape.edges.foldl (fun a e => match e.span, reachOf e with
      | .whole, some q =>
        a.pushOp (.regionOpen (.edge (r.shown (e.ink a.pal)) (ruleX e tx0 tx1) (len e.width) 0
          (some { height := q.depth, depth := q.depth, continued := true })))
      | _, _ => a) a
    ({ a with fg := saved, measure := some measure } : Acc).wantGap
  -- An untitled body opens its template's box below the arm's skips and the box's `\parskip`.
  let a := if shape.whole.isSome && !setsTitle then
      let more := !(body.size == 1 && body[0]? matches some (Ir.Block.para _))
      { a with boxOpener := some { inset := wholeInset, more := more
                                   leading := Ir.leadingFor r.geom.fontSize r.geom.leading } }
    else if !setsTitle then a.vskip between
    else (a.vskip between).wantGap
  (a, wx0 - r.geom.hmargin, wx1 - r.geom.hmargin)

/-- The template's close: the body's part of a whole-block rule closes on the
body's last baseline, the box's rules after its glue, then the skips below. -/
private def collectShapedClose (r : Rd) (done : Acc) (shape : Ir.BlockShape) (titled : Bool) :
    Acc :=
  let done := { done with boxOpener := none }
  let done := if !shapedSetsTitle shape titled then done else
    shape.edges.foldl (fun d e =>
      if e.span == .whole && e.reach matches .lines .. then d.pushOp .regionClose else d) done
  let done := if shape.whole.isNone then done else
    shape.edges.foldl (fun d e => if e.span == .whole && !e.besideTitle then d.pushOp .regionClose else d)
      ({ done with wantDefault := false }.flushGap r)
  done.vskip (r.resolve (Ir.blockSkipSum done.tokens shape.after))

/-- tcolorbox's box closing: the frame below the
body's last line, then its `after skip balanced`. -/
private def collectBoxClose (r : Rd) (done : Acc) (bodyBg : Option Ir.Color) : Acc :=
  let bs := Ir.leadingFor r.geom.fontSize r.geom.leading
  let done := { done with wantDefault := false }.flushGap r
  let done := match bodyBg with
    | some _ => (done.pushOp .regionClose).pushOp (.boxAnchor .flush (-(bs * 3 / 10)) false)
    | none => done.pushOp (.boxAnchor .flush
        (Ir.tcbBottom + Ir.tcbBoxsep + Ir.tcbRule - bs * 3 / 10) false)
  { done.vskip { width := bs / 2 - r.parskip.width } with wantDefault := true }

/-- The abstract's heading word, generated as the HTML's `<h2>` is, in
the section heading's style centred (`Ir.abstractHeadingStyle`). -/
private def collectAbstractHead (r : Rd) (a : Acc) (indent : Sp) : Acc :=
  let small := Ir.scaleStep r.geom.fontSize "small"
  let hst := Ir.abstractHeadingStyle r.styles
  let hcenter := hst.align != some .left && hst.align != some .right
  let rh := if hst.align == some .right
    then { r with geom := { r.geom with flushRight := true } } else r
  let a := match hst.font with
    | some tpl =>
      collectDisplay rh a (Ir.fillTemplate tpl #[.text r.locale.abstract]) indent
        hcenter r.geom.fontSize
    | none =>
      collectDisplay rh a #[.text r.locale.abstract] indent hcenter small
        (baseStyle := { weight := .b })
  a.wantGap

/-- A float's caption within its declared caption margin (`collectCaption`). -/
private def collectFloatCaption (r rf : Rd) (a : Acc) (kind : Ir.FloatKind) (caption : Array Inline)
    (capLeaf : Option Nat) (capSpan : Nat) (indent : Sp) : Acc :=
  if caption.isEmpty then a else
  let cmargin := ((Ir.captionTokenOf a.tokens kind "captionmargin").map
    (fun g => (r.resolve g).width)).getD 0
  collectCaption r rf a caption cmargin capLeaf capSpan indent

/-- The headline band: a headline class's `\title` family as page-top furniture
in the `frametitle` roles (beamerthemegemini.sty), pinned above the body. -/
private def collectHeadlineBand (r : Rd) (a : Acc) : Acc :=
  match r.headline with
  | some hl =>
    let band := (Ir.Design.ofPalette a.pal).frametitle
    let bar := band.map (·.bg)
    let saved := (a.fg, a.ground)
    let a := match band with
      | some pair => { a with fg := pair.fg, ground := some pair.bg }
      | none => a
    let tps := r.style "titlepage"
    -- Three-way, as the declaration's vocabulary: `left`, `right`, else centred.
    let center := tps.align != some .left && tps.align != some .right
    let rt := if tps.align == some .right
      then { r with geom := { r.geom with flushRight := true } } else r
    let a := match tps.font with
      | some tpl =>
        collectDisplay rt a (Ir.fillTemplate tpl hl.title) 0 center r.geom.fontSize
      | none =>
        collectDisplay rt a hl.title 0 center
          (Ir.scaleStep r.geom.fontSize "Huge") (baseStyle := { weight := .b })
    let a := if hl.author.isEmpty then a else
      collectDisplay rt a hl.author 0 center (Ir.scaleStep r.geom.fontSize "Large")
    let a := if hl.institute.isEmpty then a else
      collectDisplay rt a hl.institute 0 center r.geom.fontSize
    let a := match bar with
      | some barBg =>
        { a with fg := saved.1, ground := saved.2
                 ops := a.ops.push (.titleBar barBg (r.geom.fontSize / 2) none) }
      | none => a
    -- The band-to-body gap is the frame title's own (`wantDefault`).
    { a with ops := a.ops.push .pin, wantDefault := true }
  | none => a

/-- A frame title's lines on the measure its box gives them: the
paper less the inset on either side, else the text block. -/
private def frameTitleLine (r : Rd) (a : Acc) (inset : Option Sp)
    (set : Acc → Sp → Acc) : Acc :=
  match inset with
  | none => set a 0
  | some i =>
    let saved := a.measure
    let a := set { a with measure := some (r.geom.pageW - i - r.geom.hmargin) } (i - r.geom.hmargin)
    { a with measure := saved }

/-- A frame's title line: a themed colour bar across the page (`frametitlebg`),
moloch's box where `frametitlepadding` is declared, else the section-size bold line. -/
private def collectFrameTitle (r : Rd) (a : Acc) (title : Array Inline)
    (titleLeaf : Option Nat) (titleSpan : Nat) : Acc :=
  if title.isEmpty then a else
  match (Ir.Design.ofPalette a.pal).frametitle with
  | some bar =>
    let barBg := bar.bg
    let saved := (a.fg, a.ground)
    let a := { a with fg := bar.fg, ground := some barBg }
    let st := r.style "frametitle"
    let titleSize := match st.font with
      | some tpl => Ir.templateSize r.geom.fontSize tpl
      | none => sectionSize r.geom 1
    -- moloch's bar spans the paper, the title inset from either edge (`Ir.frameTitleInset`).
    let inset := if (a.tokens.find? "frametitlepadding").isSome then
        some (Ir.frameTitleInset titleSize) else none
    let a := frameTitleLine r a inset fun a indent =>
      match st.font with
      | some tpl =>
        collectDisplay r a (Ir.fillTemplate tpl title) indent false r.geom.fontSize
          (leaf := titleLeaf) (span := titleSpan)
      | none =>
        collectDisplay r a title indent false titleSize
          (baseStyle := { weight := .b }) (leaf := titleLeaf) (span := titleSpan)
          (inserted := true)
    let (pad, strut) := match a.tokens.find? "frametitlepadding" with
      | some g => (g.width.resolve titleSize r.xHeight,
                   some (Ir.frameTitleStrut titleSize))
      | none => (r.geom.fontSize / 2, none)
    -- The title is inline content with no `.setPalette`, so the saved ink is the epoch's own.
    let a := { a with fg := saved.1
                      ground := saved.2
                      ops := a.ops.push (.titleBar barBg pad strut) }
    { a with wantDefault := true }
  | none =>
    let savedFg := a.fg
    let a := { a with fg := (Ir.Design.ofPalette a.pal).frameTitleFg }
    let a := collectDisplay r a title 0 false (Ir.scaleStep r.geom.fontSize Ir.plainFrameTitleStep)
      (baseStyle := { weight := .b }) (leaf := titleLeaf) (span := titleSpan)
      (inserted := true)
    { a with wantDefault := true, fg := savedFg }

/-- The one rewrite of the physical pass: `\pagenumber` and `\pagecount`
become literal text, both known once the body is laid out. -/
private def substPageLeaf (n total : Nat)
    (x : Ir.Inline) : Ir.Inline :=
  match x with
  | .pageNumber => .text (toString n)
  | .pageCount => .text (toString total)
  | _ => x

/-- Replace `\pagenumber` and `\pagecount` with literal text over `Ir.mapInline`. -/
public def substPage (n total : Nat) (xs : Array Ir.Inline) : Array Ir.Inline :=
  Ir.mapInlines (substPageLeaf n total) xs

/-- A chrome band slot set as one line at its natural width at the footline's
step, the setting both the page's floor and the furniture pass read. -/
private def setBandSlot (pats : Option Hyphen.Patterns) (fs : FontSet)
    (imgs : Image.Store) (geom : Geom) (xHeight : Sp) (style : TextStyle)
    (content : Array Inline) (cache : Std.HashMap String (Array Nat)) :
    Option (Array Seg × Sp) × Bool × Array Diag × Std.HashMap String (Array Nat) :=
  -- A named size inside a slot is the body's step, as TeX's size commands are absolute.
  let (items, ds, cache, _) :=
    itemsOfInlines pats geom.fontSize xHeight fs
      { style with scale := (Ir.scaleStep 1000 Ir.footline.step).toNat }
      content cache (.fixed .unattributed) imgs geom.textWidth geom.textHeight
      (ladder := geom.scale)
  let breaks := kp items geom.textWidth
  match breaks[0]? with
  | none => (none, breaks.size > 1, ds, cache)
  | some brk =>
    let (segs, w, _) := setLine items (lineStart items 0) brk geom.textWidth false
    (some (segs, w), breaks.size > 1, ds, cache)

/-- The footline band's box on page `n`: the tallest and deepest
ink of its slots, beamer's `\ht` and `\dp` of the footline. -/
private def bandBox (fs : FontSet) (imgs : Image.Store) (geom : Geom) (xHeight : Sp)
    (n : Nat) (band : Array Ir.BandSlot) : Sp × Sp :=
  band.foldl (fun (acc : Sp × Sp) slot =>
    match (setBandSlot none fs imgs geom xHeight {} (substPage n 0 slot.content) {}).1 with
    | some (segs, _) =>
      let (h, d) := segsInk fs segs
      (max acc.1 h, max acc.2 d)
    | none => acc) (0, 0)

/-- `bandBox` at the document's resolved body x-height,
for the web deck (`HtmlDoc.Config.footBox`). -/
public def footBandBox (geom : Geom) (fs : FontSet) (imgs : Image.Store) (n : Nat)
    (band : Array Ir.BandSlot) : Sp × Sp :=
  bandBox fs imgs geom (fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm) n band

/-- A frame opens a page: the boundary, the `frameOpen` marker, and the frame's
footer; title and standout pages carry none (beamerinnerthememoloch.dtx). -/
private def collectFrameOpen (a : Acc) (standout breakable : Bool) (area : FrameArea) : Acc :=
  let a := a.pageBreak
  let opening := a.frameOpening standout area
  { a with ops := a.ops.push (.frameOpen breakable a.frameSource opening) }

private theorem collectFrameOpen_frame_exact (a : Acc) (standout breakable : Bool)
    (area : FrameArea) :
    (collectFrameOpen a standout breakable area).ops =
      a.pageBreak.ops.push
        (.frameOpen breakable a.frameSource (a.frameOpening standout area)) := by
  unfold collectFrameOpen Spacing.Pending.pageBreak
  split <;> rfl

/-- The reader a frame's body is walked with: headings belong to
the frame, and in beamer's text area `\textheight` is beamer's. -/
private def frameReader (r : Rd) (a : Acc) (standout : Bool) (area : FrameArea) : Rd :=
  let r := { r with inFrame := true }
  if area == .margins then r
  else
    { r with geom := { r.geom with
        frameTextHeight := some (frameFloor r.geom.pageH r.footGap
          ((a.selectedFoot standout).map (bandBox r.fs r.imgs r.geom r.xHeight 1))) } }

private theorem frameReader_foot_agree (r : Rd) (a : Acc) (standout : Bool) (area : FrameArea) :
    (frameReader r a standout area).geom.frameTextHeight =
      if area == .margins then r.geom.frameTextHeight
      else
        some (frameFloor r.geom.pageH r.footGap
          ((a.selectedFoot standout).map (bandBox r.fs r.imgs r.geom r.xHeight 1))) := by
  unfold frameReader
  split <;> rfl

/-- The reader inside `blk`: boxed where the block is a box (`Ir.Block.listScope`). -/
private def Spacing.Context.within (r : Rd) (blk : Block) : Rd :=
  match blk.listScope r.lists r.styles with
  | .box => { r with boxed := true }
  | .onList | .aside => r

mutual

-- The block walk recurses through `List` companions, so every call is structural.
/-- The declared title slot a block shows, if it is one (`Ir.titleSlotOf`). -/
private def slotOfBlock (slots : Array Ir.TitleSlot) :
    Block → Option (Ir.TitleSlot × Nat)
  | .role n _ => slots.zipIdx.find? fun (_, i) => Ir.titleSlotRole i == n
  | _ => none

/-- A rule standing on its own is furniture, not a
paragraph, so a gap declared beside it is the whole gap. -/
private def ruleBlock : Block → Bool
  | .rule .. => true
  | _ => false

/-- Walk a block sequence, spacing peers by `parskip`. -/
private def collectBlocks (r : Rd) (a : Acc)
    (blocks : Array Block) (indent : Sp) : Acc :=
  collectBlockList r a blocks.toList indent true false

private def collectBlockList (r : Rd) (a : Acc)
    (blocks : List Block) (indent : Sp) (first prevRule : Bool) : Acc :=
  match blocks with
  | [] => a
  | blk :: rest =>
    if statefulBlock blk then
      collectBlockList r (collectBlock r a blk indent) rest indent first prevRule
    else
    -- Until a frame's body sets its first line no peer gap is owed (`Spacing.Pending.frameTop`).
    let a := if first || a.frameTop then a else a.wantGap
    let a := if ruleBlock blk then { a with declaredSkip := false } else a
    let a := collectBlock r a blk indent
    let a := if prevRule then { a with declaredSkip := false } else a
    collectBlockList r a rest indent false (ruleBlock blk)

/-- The title frame's body when the title page declares slots: each
slot set as one box from the shared start and pinned where declared. -/
private def collectSlots (r : Rd) (a : Acc) (slots : Array Ir.TitleSlot)
    (blocks : List Block) (indent : Sp) : Acc :=
  match blocks with
  | [] => a
  | blk :: rest =>
    let a := match slotOfBlock slots blk with
      | some (sl, i) =>
        let partSize (p : Ir.TitlePart) : Sp :=
          let explicit := p.size.map fun g => (r.resolve g).width
          let templated := p.font.map fun tpl => Ir.templateSize r.geom.fontSize tpl
          max 1 ((explicit <|> templated).getD r.geom.fontSize)
        let roleMetrics := sl.parts.zipIdx.toList.filterMap fun (p, k) =>
          p.size.map fun g =>
            let size := max 1 (r.resolve g).width
            let leading := p.leading.map fun l => (r.resolve l).width
            (Ir.titlePartRole i k, (size, leading))
        let roleBaselines := sl.parts.zipIdx.toList.filterMap fun (p, k) =>
          if p.newLine then
            let size := partSize p
            let leading := (p.leading.map fun g => (r.resolve g).width).getD
              (Ir.leadingFor size r.geom.leading)
            some (Ir.titlePartRole i k, leading)
          else none
        let rs : Rd :=
          { r with slotTitle := true, roleMetrics := roleMetrics, roleBaselines := roleBaselines }
        let (width, place) := sl.box
        match place with
        | some pl =>
          let w := width.map fun g => (r.resolve g).width
          let saved := a.measure
          let a := a.pushOp .slotOpen
          let a := match w with
            | some w => { a with measure := some (indent + w) }
            | none => a
          let a := collectBlock rs a blk indent
          let spec : SlotSpec :=
            { anchor := pl.anchor, pagePoint := pl.pagePoint
              dx := (pl.xshift.map fun g => (r.resolve g).width).getD 0
              dy := -((pl.yshift.map fun g => (r.resolve g).width).getD 0)
              sep := (pl.innerSep.map fun g => (r.resolve g).width).getD
                (Ir.pgfInnerSep r.geom.fontSize)
              outerSep := Ir.pgfOuterSep
              box := w.map fun w => (r.geom.hmargin + indent, w) }
          { a.pushOp (.slotClose spec) with measure := saved }
        | none => collectBlock rs a blk indent
      | none => collectBlock r a blk indent
    collectSlots r a slots rest indent

/-- One list item: its leading paragraph carries the marker, or a
description list's label runs in; `hang` is the list's indent step. -/
private def collectItem (r : Rd) (a : Acc)
    (item : List Block) (indent : Sp) (first : Bool) (marker : Array Inline)
    (hang : Sp) : Acc :=
  match item with
  | [] => a
  | blk :: rest =>
    if statefulBlock blk then
      collectItem r (collectBlock r a blk indent) rest indent first marker hang
    else
    let a := if first then a else a.wantGap
    let a := match blk, first with
      | .para content, true =>
        if (Ir.descLabel? content).isSome then
          -- latex.ltx `description`: the label runs in at the outer margin.
          let (a, leaf) := a.leafRange (Struct.leafCountInlines content)
          collectPara r a content (indent - hang) false r.geom.fontSize
            (leaf := leaf) (span := Struct.leafCountInlines content) (hangIndent := hang)
        else
        -- A covered item is one colour wrapper; its marker dims with it, as beamer's cover.
        let marker := match content with
          | #[.colored c none _] => #[Ir.Inline.colored c none marker]
          | _ => marker
        let (a, leaf) := a.leafRange (Struct.leafCountInlines content)
        collectPara r a content indent false r.geom.fontSize
          (marker := some marker) (leaf := leaf) (span := Struct.leafCountInlines content)
      -- A disclosure opening its item sets its summary as the first paragraph, by the marker.
      | .disclosure .., true => collectBlock r { a with itemMarker := some marker } blk indent
      | _, _ => collectBlock r a blk indent
    collectItem r a rest indent false marker hang

private def collectItems (r : Rd) (a : Acc)
    (items : List (Array Block)) (indent : Sp) (st : Ir.ElementStyle)
    (ordered : Bool) (level : Nat) (idx : Nat) (itemsep : Option Glue) (hang : Sp) : Acc :=
  match items with
  | [] => a
  | item :: rest =>
    -- Items are peers: `\@item` spends `\addvspace\itemsep` and the paragraph its `\parskip`.
    let a := match idx == 1, st.gap, itemsep with
      | true, _, _ => a
      | false, some g, _ => a.addvspace (r.resolve g)
      | false, none, some i => a.wantGap.listSpace i
      | false, none, none => a
    -- The class glyph is checked against the loaded faces, so it degrades to its stand-in.
    let covered := fun c =>
      (r.fs.body.gid c).isSome || (r.fs.fallbackFor c).isSome
    let marker := st.marker.getD (ListMark.marker ordered level idx covered)
    let a := collectItem r a item.toList indent true marker hang
    collectItems r a rest indent st ordered level (idx + 1) itemsep hang

/-- Centered content: paragraphs center, anything else nests unchanged. -/
private def collectCentered (r : Rd) (a : Acc)
    (body : List Block) (indent : Sp) (prevRule : Bool) : Acc :=
  match body with
  | [] => a
  -- An overlay carrier is grouping, as `collectBlock` reads it: what it
  -- shows on this step centres as the scope's own blocks do.
  | .onSteps spec inner :: rest =>
    let a := if r.hides spec then
        (collectCentered r a.openHidden inner.toList indent false).closeHidden
      else collectCentered (r.pendingStep spec) a inner.toList indent false
    collectCentered r (if rest.isEmpty then a else a.wantGap) rest indent false
  | .altSteps spec firstPage otherPage :: rest =>
    let a := if spec.showsFirst r.step then
        (collectCentered r a firstPage.toList indent false).leafRange (Struct.leafCountBlocks otherPage) |>.1
      else collectCentered r (a.leafRange (Struct.leafCountBlocks firstPage)).1 otherPage.toList indent false
    collectCentered r (if rest.isEmpty then a else a.wantGap) rest indent false
  | blk :: rest =>
    let a := if ruleBlock blk then { a with declaredSkip := false } else a
    let a := match blk with
      | .para content =>
        let (a, leaf) := a.leafRange (Struct.leafCountInlines content)
        collectPara r a content indent true r.geom.fontSize
          (leaf := leaf) (span := Struct.leafCountInlines content)
      | .section 0 _ _ title => collectTitle r a title indent true
      | .picture pic => collectPicture r a pic indent true
      -- A table under `\centering` centres as one box; its cells keep their own alignment.
      | .table cols pl pr rows rules spans =>
        collectTable r a cols pl pr rows rules spans indent true
      | .columns _ => collectBlock { r with centreBoxes := true } a blk indent
      | _ => collectBlock r a blk indent
    let a := if prevRule then { a with declaredSkip := false } else a
    collectCentered r (if rest.isEmpty || statefulBlock blk then a else a.wantGap)
      rest indent (ruleBlock blk)

/-- One column after another, each against its own measure
at its own offset, a `colNext` marker between two. -/
private def collectColumns (r : Rd) (a : Acc)
    (cols : List (BoxWidth × Array Block)) (x0 shareW gutter total : Sp) : Acc :=
  match cols with
  | [] => a
  | (w, body) :: rest =>
    let wi := (w.resolve total).getD shareW
    let sub := { a with
      measure := some (x0 + wi)
      ops := #[]
      wantDefault := false
      owed := #[]
      anchorAt := none
      dispAlt := none }
    let sub := collectBlocks r sub body x0
    let a := { a with
      ops := a.ops ++ sub.ops ++ (if rest.isEmpty then #[] else #[Op.colNext])
      hyphCache := sub.hyphCache
      leafNext := sub.leafNext
      pictures := sub.pictures }
    collectColumns r a rest (x0 + wi + gutter) shareW gutter total

/-- A standout frame's content: paragraphs centre and
set Large bold in the page's inverted text colour. -/
private def collectStandout (r : Rd) (a : Acc)
    (body : List Block) (indent : Sp) : Acc :=
  match body with
  | [] => a
  | blk :: rest =>
    let a := match blk with
      | .para content =>
        let (a, leaf) := a.leafRange (Struct.leafCountInlines content)
        match (r.style "standout").font with
        | some tpl =>
          collectDisplay r a (Ir.fillTemplate tpl content) indent true r.geom.fontSize
            (leaf := leaf) (span := Struct.leafCountInlines content)
        | none =>
          collectDisplay r a content indent true (Ir.scaleStep r.geom.fontSize "Large")
            (baseStyle := { weight := .b }) (leaf := leaf) (span := Struct.leafCountInlines content)
      | _ => collectBlock r a blk indent
    collectStandout r (if rest.isEmpty || statefulBlock blk then a else a.wantGap)
      rest indent

private def collectBlock (r : Rd) (a : Acc)
    (blk : Block) (indent : Sp) : Acc :=
  match blk with
  | .para content => collectParaBlock r a content indent
  | .equation num content => collectEquation r a num content indent
  | .section level _ num title => collectSection r a level num title indent
  | .list ordered items =>
    -- Past the class's four levels, where LaTeX errors, the fourth level is reused and named.
    let depth := (if ordered then a.enumDepth else a.itemDepth) + 1
    let level := min depth 4
    let a := if depth > 4 then { a with diags := a.diags.push (
        Diag.of .W0010
          "lists nest more than four levels; a deeper level reuses the fourth's marker"
          (help := "LaTeX errors here ('Too deeply nested'); flatten the nesting")
          (detail := some s!"level {depth}")) }
      else a
    let element := if ordered then "enumerate" else "itemize"
    let st := if level == 1 then r.style element
      else (r.styles.find? s!"{element}{level}").getD (r.style element)
    -- The level's spacing, LaTeX's `\@list⟨n⟩` (`Ir.listSkips`), at the depth `\@listdepth` counts.
    let lv := a.itemDepth + a.enumDepth + a.quoteDepth + 1
    let sk := Ir.listSkips r.lists r.geom.fontSize lv
    -- `\@trivlist`'s `\@topsepadd`: `\topsep`, plus `\partopsep` where the list opens a paragraph.
    let top := sk.map fun s => if r.inPar then r.resolve s.topsep
      else (r.resolve s.topsep).add (r.resolve (Ir.partopsepFor r.lists r.geom.fontSize lv a.tokens))
    -- `\topsep` with TeX's `\parskip` on top; after a heading the first item spends `\@nbitem`.
    let a := match st.before, top with
      | some g, _ => a.addvspace (r.resolve g)
      | none, some t => if a.afterHeading then a.flushGap r else (a.listOpen r t).flushGap r
      | none, none => a
    let step := (st.indent.map fun g => (r.resolve g).width).getD (r.leftMargin lv a.tokens)
    let indent := indent + step
    let a := if ordered then { a with enumDepth := depth } else { a with itemDepth := depth }
    let ri := match sk with
      | some s => { r with inPar := false,
                           geom := { r.geom with parskip := s.parsep, texParskip := s.parsep } }
      | none => { r with inPar := false }
    -- beamer's squeeze (`\beamer@cramped`): `\itemsep0pt` in every list.
    let a := collectItems ri a items.toList indent st ordered level 1
      (sk.map fun s => if r.squeeze then {} else r.resolve s.itemsep) step
    let a := if ordered then { a with enumDepth := depth - 1 }
      else { a with itemDepth := depth - 1 }
    match st.before, top with
    | some g, _ => a.addvspace (r.resolve g)
    | none, some t => a.listSpace t
    | none, none => a
  | .center body =>
    match Ir.displayContent? body with
    | some content => collectDisplayFormula r a content indent
    | none => collectCentered r a body.toList indent false
  -- A ragged scope reads justification off; its side picks the origin (`Geom.flushRight`).
  | .ragged flush body =>
    let g := { r.geom with justify := false, flushRight := flush.flushRight, raggedFil := true }
    collectBlocks { r with geom := g } a body indent
  -- An undeclared role collects as unwrapped; a declared `\style{<role>}` spaces around it.
  | .role n body =>
    if let some opening := Ir.pageOpeningOfRole? n then
      { a with ops := a.ops.push (.pageOpening opening) }
    else
    if let some c := Ir.DisplayCtx.ofRole? n then collectBlocks { r with display := c } a body indent
    else
    if let some (anchors, pic) := Ir.displayPicture? (.role n body) then
      collectDisplayPicture r a anchors pic indent
    else
    if n == Ir.trivlistRole then
      -- Inside a squeezed frame's list item a trivlist takes beamer's `\topsep0.5pt`.
      let depth := a.itemDepth + a.enumDepth + a.quoteDepth
      let g := if r.squeeze && depth > 0 then r.resolve Ir.squeezedTopsep
        else r.resolve (Ir.trivlistSkipFor r.lists a.tokens r.geom.fontSize depth)
      (collectBlocks r (a.trivSpace g) body indent).trivSpace g
    else if n == Ir.inParagraphRole then collectBlocks { r with inPar := true } a body indent
    -- A theorem-like block (`Ir.thmSkips`): its own space above, the `\topsep` in force below.
    else if let some k := Ir.thmSpaceOf? n then
      match Ir.thmSkips r.lists r.geom.fontSize (max 1 (a.itemDepth + a.enumDepth)) a.tokens k
          (!r.inPar) with
      | some sk =>
        let above := r.resolve sk.above
        let a := if a.afterHeading then a
          else if sk.parskipAbove then a.listSpace above else a.addvspace above
        (collectBlocks { r with inPar := false } a body indent).listSpace (r.resolve sk.below)
      | none =>
        let g := r.resolve (Ir.trivlistSkipFor r.lists a.tokens r.geom.fontSize
            (a.itemDepth + a.enumDepth + a.quoteDepth))
        (collectBlocks r (a.trivSpace g) body indent).trivSpace g
    else if n == Ir.pageAnchorRole then { a with anchorAt := some a.owed.size }
    else if n == Ir.noInterlineRole then { a with ops := a.ops.push .noInterline }
    else if n == Ir.primitiveSkipRole then a.primitiveSkip
    else
    let st := r.style n
    let a := match st.before with
      | some g => a.addvspace (r.resolve g)
      | none => a
    let a := collectBlocks r a body indent
    match st.after with
    | some g => a.addvspace (r.resolve g)
    | none => a
  | .link target body =>
    let a := { a with ops := a.ops.push (.regionOpen (.link target)) }
    let a := collectBlocks r a body indent
    { a with ops := a.ops.push .regionClose }
  | .quote body =>
    -- A quotation is classes.dtx's `\list{}{\rightmargin\leftmargin}`, one `\@listdepth` level.
    let saved := a.measure
    let lv := a.itemDepth + a.enumDepth + a.quoteDepth + 1
    let lm := r.leftMargin lv a.tokens
    let narrow := some ((a.measure.getD r.geom.textWidth) - lm)
    match Ir.listSkips r.lists r.geom.fontSize lv with
    | some sk =>
      let g := if r.inPar then r.resolve sk.topsep
        else (r.resolve sk.topsep).add (r.resolve (Ir.partopsepFor r.lists r.geom.fontSize lv a.tokens))
      let top := if a.afterHeading then a.flushGap r else (a.listSpace g).flushGap r
      let sub := { top with measure := narrow, quoteDepth := a.quoteDepth + 1 }
      let ri := { (r.within blk) with
        inPar := false, geom := { r.geom with parskip := sk.parsep, texParskip := sk.parsep } }
      let sub := collectBlocks ri sub body (indent + lm)
      { sub.listSpace g with measure := saved, quoteDepth := a.quoteDepth }
    | none =>
      let g := r.resolve (Ir.trivlistSkipFor r.lists a.tokens r.geom.fontSize
          (a.itemDepth + a.enumDepth + a.quoteDepth))
      let sub := collectBlocks { r with inPar := false }
        { a.trivSpace g with measure := narrow, quoteDepth := a.quoteDepth + 1 } body (indent + lm)
      { sub.trivSpace g with measure := saved, quoteDepth := a.quoteDepth }
  -- Paper has no collapse: a disclosure sets its summary and its whole body, open or not.
  | .disclosure summary _ body =>
    let content := Ir.disclosureSummary summary
    let a := match a.itemMarker with
      | some marker =>
        let (a, leaf) := ({ a with itemMarker := none } : Acc).leafRange (Struct.leafCountInlines content)
        collectPara r a content indent false r.geom.fontSize
          (marker := some marker) (leaf := leaf) (span := Struct.leafCountInlines content)
      | none => collectParaBlock r a content indent
    collectBlockList r a body.toList indent false false
  | .titled kind title body =>
    let d := Ir.Design.ofPalette a.pal
    let look := d.titledBody kind
    let inherited := a.bodyInk.getD (.role .ink, a.fg)
    let parent : Ir.ColorPair := { fg := inherited.2, bg := a.ground.getD d.bg }
    let paint := d.titledBodyPaint kind parent
    let role := if look.fg.isSome then .role (Ir.Role.bodyInk kind) else inherited.1
    let restore (done : Acc) : Acc :=
      { done with measure := a.measure, bodyGround := a.bodyGround
                  bodyInk := if done.paletteEpoch == a.paletteEpoch then a.bodyInk else none
                  fg := if done.paletteEpoch == a.paletteEpoch then a.fg else fgOf done.pal
                  ground := if done.paletteEpoch == a.paletteEpoch then a.ground
                    else a.bodyGround.or (Ir.Design.declared? done.pal .page) }
    -- `\@arrayparboxrestore`, as both boxes' bodies run: no `\parskip`.
    let rb := { (r.within blk) with geom := { r.geom with parskip := {}, texParskip := {} } }
    if kind == .box then
      let (opened, bodyIndent) := collectBoxOpen r a title indent (look.bg.map r.shown)
      let inner := { opened with
        fg := r.shown paint.fg
        ground := look.bg.or a.ground
        bodyGround := look.bg.or a.bodyGround
        bodyInk := some (role, (look.resolve parent).fg) }
      restore (collectBoxClose r (collectBlocks rb inner body bodyIndent) (look.bg.map r.shown))
    else
    match Ir.blockShapeOf r.styles kind with
    | some shape =>
      let (opened, bodyIndent, bodyMeasure) := collectShapedOpen r a kind shape title body indent
      let ink := look.fg.getD inherited.2
      let inner := { opened with
        fg := r.shown ink, measure := some bodyMeasure
        bodyInk := some (role, look.fg.getD inherited.2) }
      let done := collectBlocks r inner body bodyIndent
      (restore (collectShapedClose r done shape !title.isEmpty))
    | none =>
    -- beamer's `block begin`/`block end`: two colour boxes, painted `pad` beyond the text.
    let pad := titledPadding r.geom.fontSize r.xHeight
    let x := r.geom.hmargin + indent - pad
    let w := (a.measure.getD r.geom.textWidth) - indent + 2 * pad
    let bs := Ir.leadingFor r.geom.fontSize r.geom.leading
    -- `\par\vskip\medskipamount`: a box spends no `\parskip`.
    let above := r.resolve (Ir.skipAmount a.tokens "medskipamount")
    let above := if a.frameTop then
        { above with width := above.width - (r.resolve r.geom.texParskip).width }
      else above
    let opened := collectTitledTitle r { a.vskip above with wantDefault := false }
      kind title indent pad x w
    -- The body box opens on its `\vbox{}`, by `\nointerlineskip\vskip-0.5pt` below a painted title.
    let raise := Ir.blockBodyRaise.resolve r.geom.fontSize r.xHeight
    let opened := match look.bg with
      | some bg =>
        (opened.pushOp (.regionOpen (.surface (r.shown bg) pad x w true))).pushOp
          (if (Ir.titledLook a.pal kind).bar.isSome then .boxAnchor .flush (-Ir.blockSeam) true
           else .boxAnchor (.tex (bs + pad)) 0 true)
      | none => opened.pushOp (.boxAnchor (.tex (bs - raise)) (-raise) false)
    let inner := { opened with
      fg := r.shown paint.fg
      ground := look.bg.or a.ground
      bodyGround := look.bg.or a.bodyGround
      bodyInk := some (role, (look.resolve parent).fg) }
    let done := collectBlocks rb inner body indent
    -- A painted box keeps the glue its list ends on.
    let done := if look.bg.isSome then
        ({ done with wantDefault := false }.flushGap r).pushOp .regionClose
      else done
    -- `\vskip\smallskipamount`; a paragraph after it spends its own `\parskip`.
    (restore done).vskip (r.resolve (Ir.skipAmount done.tokens "smallskipamount"))
  | .abstract body =>
    -- article.cls's abstract: `\small`, a centred bold heading, then the body on quotation margins.
    let small := Ir.scaleStepIn r.geom.scale r.geom.fontSize (Ir.abstractBodySize r.styles)
    let a := collectAbstractHead r a indent
    let saved := a.measure
    let lm := r.leftMargin (a.itemDepth + a.enumDepth + a.quoteDepth + 1) a.tokens
    let sub := { a with
      measure := some ((a.measure.getD r.geom.textWidth) - lm), quoteDepth := a.quoteDepth + 1 }
    let sub := collectBlocks { (r.within blk) with geom := { r.geom with fontSize := small } }
      sub body (indent + lm)
    { sub with measure := saved, quoteDepth := a.quoteDepth }
  | .columns cols =>
    -- Declared widths resolve against the measure; the rest goes to widthless boxes or gutters.
    let a := a.flushGap r
    let total := (a.measure.getD r.geom.textWidth) - indent
    let declared := cols.foldl (fun s (c : BoxWidth × Array Block) =>
      s + ((c.1.resolve total).getD 0)) 0
    let unspecified := cols.foldl (fun c (col : BoxWidth × Array Block) =>
      if col.1.declared then c else c + 1) 0
    let rem := max 0 (total - declared)
    let shareW := if unspecified > 0 then rem / unspecified else 0
    let gutter := if unspecified == 0 && cols.size > 1 then rem / (cols.size - 1) else 0
    -- A lone declared box leaves its slack to its scope's side; several spend it on gutters.
    let side : Ir.HAlign := if r.centreBoxes then .center
      else if r.geom.flushRight then .right else .left
    let off := if cols.size == 1 && unspecified == 0 then side.boxOffset rem else 0
    let a := { a with ops := a.ops.push (.colOpen (cols.map (·.1.pos))) }
    -- `\@parboxrestore` (latex.ltx) zeroes the side skips inside every minipage and `\parbox`.
    let inner := { (r.within blk) with
      centreBoxes := false, geom := { r.geom with flushRight := false } }
    let a := collectColumns inner a cols.toList (indent + off) shareW gutter total
    { a with ops := a.ops.push .colClose }
  | .bibliography _ _ items => collectBibliography r a items indent
  | .spaced before body =>
    -- Alone, the space is a `\vspace`; carrying a body, it is the element's `\addvspace`.
    let g := r.resolve before.value
    let g := if r.boxed then { g with fil := false } else g
    let a := if body.isEmpty then a.vspace g
      else { a.vskip g with declaredSkip := false }
    collectBlocks r a body indent
  | .onSteps spec body =>
    -- Dimming was painted into the colours before layout; what resolves here takes the cover.
    if r.hides spec then (collectBlocks r a.openHidden body indent).closeHidden
    else collectBlocks (r.pendingStep spec) a body indent
  | .altSteps spec firstPage otherPage =>
    -- The counter steps over the group this page does not ink, so the inked one keeps its tree id.
    if spec.showsFirst r.step then
      let a := collectBlocks r a firstPage indent
      (a.leafRange (Struct.leafCountBlocks otherPage)).1
    else
      let a := (a.leafRange (Struct.leafCountBlocks firstPage)).1
      collectBlocks r a otherPage indent
  | .only _ body =>
    -- `run` already kept this node for the PDF (`Ir.keepFor`), so it is pure grouping here.
    collectBlocks r a body indent
  | .nav spec body => collectNav a spec body
  | .note body => collectNote a body
  | .pagebreak =>
    -- The builder closes only pages holding something, so adjacent breaks never make a blank page.
    a.pageBreak
  | .logo content => collectLogo a content
  | .verbatim covered s spec => collectListing r a covered s spec indent
  | .algorithm numbered semis lines => collectAlgorithm r a numbered semis lines indent
  | .framefoot content => collectFramefoot a content
  | .setPalette p =>
    -- The palette in force from here on, in flow order past the enclosing block's end.
    a.setPalette p

  | .setTokens tk =>
    -- Tokens resolve against the state in force where the element stands.
    a.setTokens tk
  | .rule color _ thickness => collectRuleBlock r a color thickness.value
  | .picture pic =>
    -- Left on the current indent, as LaTeX places the box where it stands.
    collectPicture r a pic indent false
  | .table cols padL padR rows rules spans =>
    collectTable r a cols padL padR rows rules spans indent false
  | .float kind num capAbove body caption =>
    -- A float is one unbreakable box (`runFloat`); its caption's leaves come first.
    let capSpan := Struct.leafCountInlines caption
    let (a, capLeaf) := a.leafRange capSpan
    -- The declared caption is marked as content, so the number prefix is the caption's `.block`.
    let caption := Ir.numberedCaption r.locale kind num (markContent caption)
    let (floatSep, floatTriv) := Ir.floatSpaceFor r.lists a.tokens r.geom.fontSize
      (a.itemDepth + a.enumDepth + a.quoteDepth)
    let floatSep := r.resolve floatSep
    let skip (s : Ir.CaptionSkip) : Glue :=
      r.resolve ((s.find? a.tokens kind).getD (s.defaultFor r.lists r.geom.fontSize))
    let (objSkip, farSkip) := Ir.captionSides (Ir.captionPosFor r.lists r.captionPos kind) capAbove
    let capSep := skip objSkip
    let farSep := skip farSkip
    let a := a.pushOp .floatOpen
    let rf := { (r.within blk) with inFloat := true }
    -- In beamer's lineage the text-side gaps are the trivlist's (`Ir.floatSpaceFor`).
    let plan := floatPlan capAbove (!caption.isEmpty) floatSep capSep farSep
    let a := plan.zipIdx.foldl
      (fun a (slot, i) => match slot with
        | .gap g =>
          if floatTriv && (i == 0 || i + 1 == plan.length) then a.trivSpace g else a.addvspace g
        | .caption => collectFloatCaption r rf a kind caption capLeaf capSpan indent
        | .object => collectCentered rf a body.toList indent false) a
    a.pushOp .floatClose
  | .frame title standout valign breakable body =>
    let marks := Ir.frameMarks body
    let squeeze := Ir.frameSqueeze body
    -- Only a declared squeeze changes the page; the ladder's stands in for the web deck's shrink.
    let r := { r with squeeze := squeeze == .declared, breakableFrame := breakable }
    let step := (a.frameOrigin.map (·.step)).getD 1
    let fit : FrameFitMode := if breakable then .spill
      else if marks.contains Ir.fitMeasureRole then .measure
      else if marks.contains (Ir.fitOverhangRole step) then .overhang
      else if marks.contains (Ir.fitContinuesRole step) then .continues
      else .spill
    let a := { a with frameFit := fit }
    -- With chrome allowed, every frame but the title page takes beamer's text area.
    let area := frameAreaFor a.footAllowed valign
    let a := collectFrameOpen a standout breakable area
    let r := frameReader r a standout area
    -- A standout frame shows its body alone, so its title's leaves are stepped over.
    let titleSpan := Struct.leafCountInlines title
    let (a, titleLeaf) := a.leafRange titleSpan
    -- Recompute from the palette in force: a `.setPalette` in the frame must reach what follows.
    let close (a : Acc) (reground : Bool) : Acc :=
      let a := if reground then { a with fg := fgOf a.pal, ground := Ir.Design.declared? a.pal .page }
        else a
      a.pageBreak.pushOp .frameClose
    if standout then
      let so := (Ir.Design.ofPalette a.pal).standout
      let ground := Ir.frameGroundOf a.pal true valign
      let dist := VDist.of (Ir.frameKeysOf r.frameKeys true) valign breakable
      let a := { a with ops := a.ops.push (.pageStyle ground dist) }
      let a := openFrameBody r a false valign area
      close (collectStandout r { a with fg := so.fg, ground := some so.bg } body.toList indent) true
    else
    -- The frame's own ground (`Ir.frameGroundOf`), through the standout's `.pageStyle` door.
    let pageGround := Ir.frameGroundOf a.pal false valign
    let dist := VDist.of (Ir.frameKeysOf r.frameKeys false) valign breakable
    let a := { a with ops := a.ops.push (.pageStyle pageGround dist) }
    let a := match titleInk a.pal valign with
      | some ink => { a with fg := ink, ground := pageGround }
      | none => a
    let a := collectHeadlineBand r a
    let a := collectFrameTitle r a title titleLeaf titleSpan
    -- The title is pinned chrome; the content opens below its box with no peer gap.
    let a := if title.isEmpty then
        openFrameBody r a false valign area
      else
      let g : Glue := { width := frameBodySkip true valign r.geom.fontSize }
      -- A title with no bar stands in beamer's default frametitle box.
      let box := if (Ir.Design.ofPalette a.pal).frametitle.isSome then none
        else
          let size := Ir.scaleStep r.geom.fontSize Ir.plainFrameTitleStep
          some (Ir.defaultFrameTitleBelow size r.geom.leading (r.xHeight * size / r.geom.fontSize))
      { a with ops := (a.ops.push .pin).push (.bodyOpen g box), wantDefault := false,
               frameTop := true }
    -- A golden frame is the title page, all display furniture: never hyphenated or justified.
    let a := if valign matches .golden then
        let rd := { r with pats := none, geom := { r.geom with justify := false } }
        let slots := (r.style "titlepage").slots
        if slots.isEmpty then collectBlocks rd a body indent
        else collectSlots rd a slots body.toList indent
      else collectBlocks r a body indent
    close a pageGround.isSome

end

private theorem role_transparent_collect (r : Rd) (a : Acc) (n : String)
    (body : Array Block) (indent : Sp) (hst : r.styles.find? n = none)
    (htl : n ≠ Ir.trivlistRole) (hip : n ≠ Ir.inParagraphRole)
    (hth : Ir.thmSpaceOf? n = none) (hpm : Ir.pageMarkerRole n = false)
    (hdc : Ir.DisplayCtx.ofRole? n = none) (hdp : n ≠ Ir.displayPictureRole) :
    collectBlock r a (.role n body) indent = collectBlocks r a body indent := by
  have hpic := Ir.displayPicture?_role_exact n body hdp
  have h : (n == Ir.trivlistRole) = false := by simpa using htl
  have h' : (n == Ir.inParagraphRole) = false := by simpa using hip
  simp only [Ir.pageMarkerRole, Bool.or_eq_false_iff] at hpm
  obtain ⟨⟨⟨⟨⟨⟨hpa, hni⟩, hps⟩, hos⟩, -⟩, -⟩, -⟩ := hpm
  have hop : Ir.pageOpeningOfRole? n = none :=
    Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp hos)
  simp only [collectBlock, Spacing.Context.style, hst, Option.getD, h, h', hth, hpa, hni, hps,
    hdc, hop, hpic, Bool.false_eq_true, ite_false]

private theorem pageOpening_collect_projects (r : Rd) (a : Acc) (n : String)
    (opening : Ir.PageOpening) (indent : Sp)
    (h : Ir.pageOpeningOfRole? n = some opening) :
    collectBlock r a (.role n #[]) indent =
      { a with ops := a.ops.push (.pageOpening opening) } := by
  simp only [collectBlock, h]

/-- Sorted, pairwise disjoint, nonempty half-open intervals. -/
public def Chained : List (Int × Int) → Prop
  | [] => True
  | (lo, hi) :: rest => lo ≤ hi ∧ (∀ o ∈ rest, hi ≤ o.1) ∧ Chained rest

/-- The sub-intervals of `[cur, hi)` not covered by a chained obstruction list. -/
public def subtract (cur hi : Int) : List (Int × Int) → List (Int × Int)
  | [] => if cur < hi then [(cur, hi)] else []
  | (olo, ohi) :: rest =>
    if cur < min olo hi then (cur, min olo hi) :: subtract (max cur ohi) hi rest
    else subtract (max cur ohi) hi rest

public theorem subtract_bounds (obs : List (Int × Int)) (cur hi : Int) :
    ∀ s ∈ subtract cur hi obs, cur ≤ s.1 ∧ s.1 < s.2 ∧ s.2 ≤ hi := by
  induction obs generalizing cur with
  | nil =>
    intro s hs
    simp only [subtract] at hs
    split at hs <;> simp_all <;> omega
  | cons o rest ih =>
    intro s hs
    simp only [subtract] at hs
    split at hs
    · rcases List.mem_cons.mp hs with rfl | hs'
      · dsimp only
        omega
      · have := ih (max cur o.2) s hs'
        omega
    · have := ih (max cur o.2) s hs
      omega

public theorem underline_skips_ink (obs : List (Int × Int)) (cur hi : Int)
    (hch : Chained obs) :
    ∀ s ∈ subtract cur hi obs, ∀ o ∈ obs, s.2 ≤ o.1 ∨ o.2 ≤ s.1 := by
  induction obs generalizing cur with
  | nil => intro s _ o ho; cases ho
  | cons a rest ih =>
    obtain ⟨hne, hsep, hrest⟩ := hch
    intro s hs o ho
    simp only [subtract] at hs
    split at hs
    · rcases List.mem_cons.mp hs with rfl | hs'
      · rcases List.mem_cons.mp ho with rfl | ho'
        · left
          dsimp only
          omega
        · have := hsep o ho'
          left
          dsimp only
          omega
      · have hb := subtract_bounds rest (max cur a.2) hi s hs'
        rcases List.mem_cons.mp ho with rfl | ho'
        · right
          omega
        · exact ih (max cur a.2) hrest s hs' o ho'
    · have hb := subtract_bounds rest (max cur a.2) hi s hs
      rcases List.mem_cons.mp ho with rfl | ho'
      · right
        omega
      · exact ih (max cur a.2) hrest s hs o ho'

public theorem underline_covers_gaps (obs : List (Int × Int)) (cur hi x : Int)
    (hch : Chained obs) (hx : cur ≤ x ∧ x < hi)
    (hout : ∀ o ∈ obs, x < o.1 ∨ o.2 ≤ x) :
    ∃ s ∈ subtract cur hi obs, s.1 ≤ x ∧ x < s.2 := by
  induction obs generalizing cur with
  | nil =>
    refine ⟨(cur, hi), ?_, by omega⟩
    simp only [subtract]
    split
    · simp
    · exfalso
      omega
  | cons a rest ih =>
    obtain ⟨hne, hsep, hrest⟩ := hch
    rcases hout a (List.mem_cons_self ..) with hlt | hge
    · refine ⟨(cur, min a.1 hi), ?_, by dsimp only; omega⟩
      simp only [subtract]
      split
      · exact List.mem_cons_self ..
      · exact absurd (by omega : cur < min a.1 hi) ‹¬_›
    · obtain ⟨s, hs, hcov⟩ := ih (max cur a.2) hrest ⟨by omega, hx.2⟩
        (fun o ho => hout o (List.mem_cons_of_mem _ ho))
      refine ⟨s, ?_, hcov⟩
      simp only [subtract]
      split
      · exact List.mem_cons_of_mem _ hs
      · exact hs

/-- Merge a sorted run of intervals into a chained list, fusing
an input that reaches back into the growing interval `cur`. -/
public def mergeChained (cur : Int × Int) : List (Int × Int) → List (Int × Int)
  | [] => [cur]
  | (lo, hi) :: rest =>
    if lo ≤ cur.2 then mergeChained (cur.1, max cur.2 hi) rest
    else cur :: mergeChained (lo, hi) rest

public theorem mergeChained_lb (cur : Int × Int) (l : List (Int × Int))
    (hs : l.Pairwise (fun a b => a.1 ≤ b.1)) (hcl : ∀ o ∈ l, cur.1 ≤ o.1) :
    ∀ s ∈ mergeChained cur l, cur.1 ≤ s.1 := by
  induction l generalizing cur with
  | nil =>
    intro s hs'
    simp only [mergeChained, List.mem_singleton] at hs'
    subst hs'
    omega
  | cons a rest ih =>
    obtain ⟨hhd, hrest⟩ := List.pairwise_cons.mp hs
    intro s hmem
    simp only [mergeChained] at hmem
    split at hmem
    · exact ih (cur.1, max cur.2 a.2) hrest
        (fun o ho => by have := hcl o (List.mem_cons_of_mem _ ho); exact this) s hmem
    · rcases List.mem_cons.mp hmem with rfl | hmem'
      · omega
      · have ha := hcl a (List.mem_cons_self ..)
        have := ih a hrest (fun o ho => hhd o ho) s hmem'
        omega

public theorem mergeChained_chained (cur : Int × Int) (l : List (Int × Int))
    (hc : cur.1 ≤ cur.2) (hne : ∀ o ∈ l, o.1 ≤ o.2)
    (hs : l.Pairwise (fun a b => a.1 ≤ b.1)) (hcl : ∀ o ∈ l, cur.1 ≤ o.1) :
    Chained (mergeChained cur l) := by
  induction l generalizing cur with
  | nil =>
    simp [mergeChained, Chained, hc]
  | cons a rest ih =>
    obtain ⟨hhd, hrest⟩ := List.pairwise_cons.mp hs
    simp only [mergeChained]
    split
    · exact ih (cur.1, max cur.2 a.2) (by dsimp only; omega)
        (fun o ho => hne o (List.mem_cons_of_mem _ ho)) hrest
        (fun o ho => hcl o (List.mem_cons_of_mem _ ho))
    · refine ⟨hc, fun o ho => ?_, ?_⟩
      · have := mergeChained_lb a rest hrest (fun o ho => hhd o ho) o ho
        omega
      · exact ih a (hne a (List.mem_cons_self ..))
          (fun o ho => hne o (List.mem_cons_of_mem _ ho)) hrest
          (fun o ho => hhd o ho)

/-- Sort obstructions by their low bound and fuse
overlapping and touching intervals into a chained list. -/
public def mergeIntervals (obs : Array (Int × Int)) : List (Int × Int) :=
  match (obs.mergeSort fun a b => decide (a.1 ≤ b.1)).toList with
  | [] => []
  | x :: rest => mergeChained x rest

public theorem mergeIntervals_chained (obs : Array (Int × Int))
    (hne : ∀ o ∈ obs, o.1 ≤ o.2) : Chained (mergeIntervals obs) := by
  unfold mergeIntervals
  split
  · trivial
  · rename_i x rest heq
    have hp : ((obs.mergeSort fun a b => decide (a.1 ≤ b.1)).toList).Pairwise
        (fun a b => a.1 ≤ b.1) := by
      have := Array.pairwise_mergeSort (le := fun a b => decide (a.1 ≤ b.1))
        (xs := obs) (fun a b c hab hbc => by
          simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      exact this.imp (by simp)
    have hmem : ∀ o ∈ (obs.mergeSort fun a b => decide (a.1 ≤ b.1)).toList,
        o.1 ≤ o.2 := by
      intro o ho
      exact hne o (by simpa [Array.mem_mergeSort] using ho)
    rw [heq] at hp hmem
    obtain ⟨hhd, hrest⟩ := List.pairwise_cons.mp hp
    exact mergeChained_chained x rest (hmem x (List.mem_cons_self ..))
      (fun o ho => hmem o (List.mem_cons_of_mem _ ho)) hrest
      (fun o ho => hhd o ho)

/-- Horizontal placement and resolved bands of a line's
decoration segments, the pen advancing by the set widths. -/
public def decorationSpans (x : Int) : List Seg → List (Int × Int × Ir.Decoration × DecorationRule)
  | [] => []
  | .decoration k w t r c :: rest =>
    (x, x + w, k, { color := c, thickness := t, raise := r }) :: decorationSpans (x + w) rest
  | s :: rest => decorationSpans (x + s.advance) rest

private theorem decorationSpans_append (a b : List Seg) (x : Int) :
    decorationSpans x (a ++ b) = decorationSpans x a ++
      decorationSpans (x + (a.map Seg.advance).sum) b := by
  induction a generalizing x with
  | nil => simp [decorationSpans]
  | cons s rest ih =>
    cases s <;> simp [decorationSpans, Seg.advance, ih, Int.add_assoc]

private def underlinePieces (paint : DecorationRule) (hi : Int) :
    List (Int × Int) → Int → Array Seg → Array Seg
  | [], cur, out => out.push (.gap (hi - cur) false)
  | (lo, stop) :: rest, cur, out =>
    underlinePieces paint hi rest stop
      ((out.push (.gap (lo - cur) false)).push
        (.decoration .underline (stop - lo) paint.thickness paint.raise paint.color))

private theorem underlinePieces_placement (paint : DecorationRule) (hi x cur : Int)
    (spans : List (Int × Int)) (out : Array Seg)
    (hx : x + (out.toList.map Seg.advance).sum = cur) :
    x + ((underlinePieces paint hi spans cur out).toList.map Seg.advance).sum = hi ∧
    decorationSpans x (underlinePieces paint hi spans cur out).toList =
      decorationSpans x out.toList ++ spans.map (fun (lo, stop) => (lo, stop, Ir.Decoration.underline, paint)) := by
  induction spans generalizing cur out with
  | nil =>
    simp [underlinePieces, decorationSpans_append, decorationSpans, Seg.advance]
    omega
  | cons span rest ih =>
    let next := (out.push (.gap (span.1 - cur) false)).push
      (.decoration .underline (span.2 - span.1) paint.thickness paint.raise paint.color)
    have hn : x + (next.toList.map Seg.advance).sum = span.2 := by
      simp [next, Seg.advance]
      omega
    have hit := ih span.2 next hn
    constructor
    · exact hit.1
    · simp only [underlinePieces]
      rw [hit.2]
      simp [next, decorationSpans_append, decorationSpans, Seg.advance]
      constructor <;> omega

/-- A segment's underline band: a run resolves its face here, an authored space carries its band. -/
public def Seg.underlineRule (fs : FontSet) (lineSize : Sp) : Seg → Option DecorationRule
  | .run fontIdx color _ _ _ size _ decorations _ _ _ =>
    (decorations.resolve (fs.get fontIdx) (if size == 0 then lineSize else size) color).underline
  | .decoratedGap _ _ decorations => decorations.underline
  | .gap _ _ | .rule _ _ _ _ | .decoration _ _ _ _ _ | .image _ _ _ _ | .poly _ _ => none

/-- Append a segment's skip-ink paint, its full advance kept as gaps between the surviving spans. -/
public def appendUnderline (fs : FontSet) (size : Sp) (obs : List (Int × Int))
    (x : Sp) (seg : Seg) (out : Array Seg) : Array Seg :=
  match seg.underlineRule fs size with
  | none => out.push (.gap seg.advance false)
  | some paint => underlinePieces paint (x + seg.advance)
      (subtract x (x + seg.advance) obs) x out

/-- Native artifact geometry of the run and space painter, not a second reading of IR decoration. -/
public theorem appendUnderline_exact (fs : FontSet) (size : Sp) (obs : List (Int × Int))
    (origin x : Int) (seg : Seg) (out : Array Seg)
    (hx : origin + (out.toList.map Seg.advance).sum = x) :
    origin + ((appendUnderline fs size obs x seg out).toList.map Seg.advance).sum =
        x + seg.advance ∧
    decorationSpans origin (appendUnderline fs size obs x seg out).toList =
      decorationSpans origin out.toList ++
        ((seg.underlineRule fs size).toList.flatMap fun paint =>
          (subtract x (x + seg.advance) obs).map fun (lo, hi) =>
            (lo, hi, Ir.Decoration.underline, paint)) := by
  cases hp : seg.underlineRule fs size with
  | none =>
    simp [appendUnderline, hp, decorationSpans_append, decorationSpans, Seg.advance]
    omega
  | some paint =>
    simpa [appendUnderline, hp] using underlinePieces_placement paint
      (x + seg.advance) origin x (subtract x (x + seg.advance) obs) out hx

public theorem appendUnderline_covers (fs : FontSet) (size : Sp) (obs : List (Int × Int))
    (origin x point : Int) (seg : Seg) (out : Array Seg) (paint : DecorationRule)
    (hpen : origin + (out.toList.map Seg.advance).sum = x)
    (hpaint : seg.underlineRule fs size = some paint) (hch : Chained obs)
    (hx : x ≤ point ∧ point < x + seg.advance)
    (hout : ∀ o ∈ obs, point < o.1 ∨ o.2 ≤ point) :
    ∃ lo hi, (lo, hi, Ir.Decoration.underline, paint) ∈
      decorationSpans origin (appendUnderline fs size obs x seg out).toList ∧
      lo ≤ point ∧ point < hi := by
  obtain ⟨span, hs, hcov⟩ := underline_covers_gaps obs x (x + seg.advance) point hch hx hout
  refine ⟨span.1, span.2, ?_, hcov⟩
  rw [(appendUnderline_exact fs size obs origin x seg out hpen).2]
  apply List.mem_append_right
  simp only [hpaint, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_map]
  exact ⟨span, hs, rfl⟩

/-- Underline rules for one set line, interrupted where glyph ink crosses the band
with a gap of twice the run's rule thickness (CSS Text Decoration 4 §2.10.5). -/
private def underlineSegs (fs : FontSet) (lineSize : Sp) (segs : Array Seg) :
    Array Seg := Id.run do
  unless segs.any (fun s => match s with
      | .run _ _ _ _ _ _ _ decorations _ _ _ => decorations.underline
      | .decoratedGap _ _ decorations => decorations.underline.isSome
      | _ => false) do
    return #[]
  -- Pass 1: obstruction intervals in line coordinates, each glyph's in-band ink plus clearance.
  let mut obs : Array (Sp × Sp) := #[]
  let mut x : Sp := 0
  for seg in segs do
    match seg with
    | .gap w _ | .decoratedGap w _ _ => x := x + w
    | .rule w _ _ _ | .decoration _ w _ _ _ => x := x + w
    | .image _ w _ _ => x := x + w
    | .poly _ _ => pure ()
    | .run fontIdx _ _ w glyphs size _ _ _ _ _ =>
      let font := fs.get fontIdx
      let sz := if size == 0 then lineSize else size
      let upem : Int := font.unitsPerEm
      let thick := (font.band).2 * sz / upem
      let mut gx : Sp := x
      for (g, _, adv) in glyphs do
        for (ilo, ihi) in font.inkAt g do
          obs := obs.push (gx + ilo * sz / upem - 2 * thick,
            gx + ihi * sz / upem + 2 * thick)
        gx := gx + adv
      x := x + w
  let merged := mergeIntervals obs
  -- Pass 2: the span painter for words and spaces.
  let mut out : Array Seg := #[]
  x := 0
  for seg in segs do
    out := appendUnderline fs lineSize merged x seg out
    x := x + seg.advance
  return out

private def lineThroughSegs (segs : Array Seg) : Array Seg := Id.run do
  unless segs.any (fun s => match s with
      | .run _ _ _ _ _ _ _ decorations _ _ _ => decorations.lineThrough.isSome
      | .decoratedGap _ _ decorations => decorations.lineThrough.isSome
      | _ => false) do
    return #[]
  let mut out : Array Seg := #[]
  for seg in segs do
    match seg with
    | .run _ _ _ w _ _ _ decorations _ _ _ =>
      match decorations.lineThrough with
      | some paint =>
        out := out.push (Seg.decoration .lineThrough w paint.thickness paint.raise paint.color)
      | none => out := out.push (Seg.gap w false)
    | .decoratedGap w _ decorations =>
      match decorations.lineThrough with
      | some paint =>
        out := out.push (Seg.decoration .lineThrough w paint.thickness paint.raise paint.color)
      | none => out := out.push (.gap w false)
    | .gap w _ => out := out.push (.gap w false)
    | .rule w _ _ _ | .decoration _ w _ _ _ => out := out.push (.gap w false)
    | .image _ w _ _ => out := out.push (.gap w false)
    | .poly _ _ => pure ()
  return out

/-- A mark pushed onto a line's marks, joined to the one before it where one paint sets both, so a
stretch of a mark is one rectangle and no seam shows between its runs. -/
private def pushMark (out : Array Seg) (c : Color) (w t r : Sp) : Array Seg :=
  match out.back? with
  | some (.decoration (.highlight c' none) w' t' r' p') =>
    if c' == c && t' == t && r' == r && p' == c then
      out.pop.push (.decoration (.highlight c none) (w' + w) t r c)
    else out.push (.decoration (.highlight c none) w t r c)
  | _ => out.push (.decoration (.highlight c none) w t r c)

/-- A placed line's marks: a `.decoration` seg under each marked stretch, a gap elsewhere. -/
private def markSegs (segs : Array Seg) : Array Seg := Id.run do
  unless segs.any (fun s => match s with
      | .run _ _ _ _ _ _ _ decorations _ _ _ => decorations.highlight.isSome
      | .decoratedGap _ _ decorations => decorations.highlight.isSome
      | _ => false) do
    return #[]
  let mut out : Array Seg := #[]
  for seg in segs do
    match seg with
    | .run _ _ _ w _ _ _ decorations _ _ _ =>
      match decorations.highlight with
      | some paint => out := pushMark out paint.color w paint.thickness paint.raise
      | none => out := out.push (Seg.gap w false)
    | .decoratedGap w _ decorations =>
      match decorations.highlight with
      | some paint => out := pushMark out paint.color w paint.thickness paint.raise
      | none => out := out.push (.gap w false)
    | .gap w _ => out := out.push (.gap w false)
    | .rule w _ _ _ | .decoration _ w _ _ _ => out := out.push (.gap w false)
    | .image _ w _ _ => out := out.push (.gap w false)
    | .poly _ _ => pure ()
  return out

/-- The drawn-decoration riders of a placed line, underline then line-through, each an
overlay at the line's origin; the one site turning a line's decorations into paint. -/
public def decorationRiders (fs : FontSet) (l : LineOut) : Array LineOut :=
  #[underlineSegs fs l.size l.segs, lineThroughSegs l.segs].filterMap fun paint =>
    if paint.isEmpty then none
    else some { x := l.x, y := l.y, size := l.size, segs := paint, setWidth := 0,
                note := l.note, furniture := l.furniture, hidden := l.hidden }

/-- A placed line's mark rider, painted under it, banded as the decoration riders are; a picture's
label sets none, as the web page's SVG label sets none. -/
public def markRiders (l : LineOut) : Array LineOut :=
  #[if l.pictureLabel.isSome then #[] else markSegs l.segs].filterMap fun paint =>
    if paint.isEmpty then none
    else some { x := l.x, y := l.y, size := l.size, segs := paint, setWidth := 0,
                note := l.note, furniture := l.furniture, hidden := l.hidden }

@[simp] public theorem markRiders_uncounted (l : LineOut) :
    ∀ r ∈ markRiders l, r.counted = false := by
  intro r hr
  simp only [markRiders, Array.mem_filterMap] at hr
  obtain ⟨paint, _, hr⟩ := hr
  split at hr
  · exact absurd hr (by simp)
  · simp only [Option.some.injEq] at hr; simp [← hr]

@[simp] public theorem markRiders_band (l : LineOut) :
    ∀ r ∈ markRiders l, r.furniture = l.furniture ∧ r.note = l.note := by
  intro r hr
  simp only [markRiders, Array.mem_filterMap] at hr
  obtain ⟨paint, _, hr⟩ := hr
  split at hr
  · exact absurd hr (by simp)
  · simp only [Option.some.injEq] at hr; simp [← hr]

@[simp] public theorem markRiders_unattributed (l : LineOut) :
    ∀ r ∈ markRiders l, r.leaf = none := by
  intro r hr
  simp only [markRiders, Array.mem_filterMap] at hr
  obtain ⟨paint, _, hr⟩ := hr
  split at hr
  · exact absurd hr (by simp)
  · simp only [Option.some.injEq] at hr; simp [← hr]

@[simp] public theorem decorationRiders_uncounted (fs : FontSet) (l : LineOut) :
    ∀ r ∈ decorationRiders fs l, r.counted = false := by
  intro r hr
  simp only [decorationRiders, Array.mem_filterMap] at hr
  obtain ⟨paint, _, hr⟩ := hr
  split at hr
  · exact absurd hr (by simp)
  · simp only [Option.some.injEq] at hr; simp [← hr]

@[simp] public theorem decorationRiders_band (fs : FontSet) (l : LineOut) :
    ∀ r ∈ decorationRiders fs l, r.furniture = l.furniture ∧ r.note = l.note := by
  intro r hr
  simp only [decorationRiders, Array.mem_filterMap] at hr
  obtain ⟨paint, _, hr⟩ := hr
  split at hr
  · exact absurd hr (by simp)
  · simp only [Option.some.injEq] at hr; simp [← hr]

@[simp] public theorem decorationRiders_unattributed (fs : FontSet) (l : LineOut) :
    ∀ r ∈ decorationRiders fs l, r.leaf = none := by
  intro r hr
  simp only [decorationRiders, Array.mem_filterMap] at hr
  obtain ⟨paint, _, hr⟩ := hr
  split at hr
  · exact absurd hr (by simp)
  · simp only [Option.some.injEq] at hr; simp [← hr]

private def appendRiders (fs : FontSet) (l : LineOut) (lines : Array LineOut) :
    Array LineOut := Id.run do
  let mut out := lines
  for r in decorationRiders fs l do
    out := out.push r
  return out

private theorem appendRiders_selected (fs : FontSet) (l : LineOut) (lines : Array LineOut)
    (select : LineOut → Bool) (hselect : ∀ r ∈ decorationRiders fs l, select r = false) :
    (appendRiders fs l lines).filter select = lines.filter select := by
  unfold appendRiders
  dsimp only [Id.run, bind, pure, Id]
  apply Loop.forIn_array_inv (fun out : Array LineOut => out.filter select = lines.filter select)
    (fun r out => pure (.yield (out.push r))) (decorationRiders fs l) lines
  · rfl
  · intro r hr out hout
    simpa only [Id.run, pure, ForInStep.value, Array.filter_push, hselect r hr, Bool.false_eq_true,
      reduceIte] using hout

private def appendMarks (l : LineOut) (lines : Array LineOut) : Array LineOut := Id.run do
  let mut out := lines
  for r in markRiders l do
    out := out.push r
  return out

private theorem appendMarks_selected (l : LineOut) (lines : Array LineOut)
    (select : LineOut → Bool) (hselect : ∀ r ∈ markRiders l, select r = false) :
    (appendMarks l lines).filter select = lines.filter select := by
  unfold appendMarks
  dsimp only [Id.run, bind, pure, Id]
  apply Loop.forIn_array_inv (fun out : Array LineOut => out.filter select = lines.filter select)
    (fun r out => pure (.yield (out.push r))) (markRiders l) lines
  · rfl
  · intro r hr out hout
    simpa only [Id.run, pure, ForInStep.value, Array.filter_push, hselect r hr, Bool.false_eq_true,
      reduceIte] using hout

/-- The final decoration pass: each line after its marks and before its drawn riders. -/
public def paintLines (fs : FontSet) (lines : Array LineOut) : Array LineOut := Id.run do
  let mut out : Array LineOut := Array.mkEmpty lines.size
  for l in lines do
    out := appendMarks l out
    out := out.push l
    out := appendRiders fs l out
  return out

private theorem paintLines_selected (fs : FontSet) (lines : Array LineOut)
    (select : LineOut → Bool) (hselect : ∀ l r, r ∈ decorationRiders fs l → select r = false)
    (hmarks : ∀ l r, r ∈ markRiders l → select r = false) :
    (paintLines fs lines).filter select = lines.filter select := by
  unfold paintLines
  simp only [Array.forIn_pure_yield_eq_foldl]
  apply Array.toList_inj.mp
  have h := Array.foldl_induction
    (as := lines)
    (motive := fun i (out : Array LineOut) =>
      (out.filter select).toList = (lines.toList.take i).filter select)
    (init := Array.mkEmpty lines.size)
    (f := fun out l => appendRiders fs l ((appendMarks l out).push l))
    (by simp)
    (by
      intro i out hout
      rw [appendRiders_selected fs _ _ select (hselect _)]
      rw [Array.filter_push, appendMarks_selected _ _ select (hmarks _)]
      rw [List.take_succ_eq_append_getElem (by simp)]
      simp only [List.filter_append, List.filter_cons, List.filter_nil]
      split <;> simp_all)
  have ht : lines.toList.take lines.toList.length = lines.toList := List.take_length
  simp only [Array.length_toList] at ht
  simpa [ht] using h

public theorem paintLines_attributed_projects (fs : FontSet) (lines : Array LineOut) :
    (paintLines fs lines).filter (fun l => l.leaf.isSome) =
      lines.filter (fun l => l.leaf.isSome) := by
  apply paintLines_selected
  · intro l r hr
    simp [decorationRiders_unattributed fs l r hr]
  · intro l r hr
    simp [markRiders_unattributed l r hr]

public theorem paintLines_counted_projects (fs : FontSet) (lines : Array LineOut) :
    (paintLines fs lines).filter (·.counted) = lines.filter (·.counted) := by
  apply paintLines_selected
  · exact fun l r hr => decorationRiders_uncounted fs l r hr
  · exact fun l r hr => markRiders_uncounted l r hr

private theorem underlinePieces_noGlyph (paint : DecorationRule) (hi cur : Int)
    (spans : List (Int × Int)) (out : Array Seg)
    (h : ∀ s ∈ out, s.NoGlyph) :
    ∀ s ∈ underlinePieces paint hi spans cur out, s.NoGlyph := by
  induction spans generalizing cur out with
  | nil =>
    intro s hs
    rcases Array.mem_push.mp hs with hs | rfl
    · exact h s hs
    · trivial
  | cons span rest ih =>
    apply ih
    intro s hs
    rcases Array.mem_push.mp hs with hs | rfl
    · rcases Array.mem_push.mp hs with hs | rfl
      · exact h s hs
      · trivial
    · trivial

private theorem appendUnderline_noGlyph (fs : FontSet) (size : Sp)
    (obs : List (Int × Int)) (x : Sp) (seg : Seg) (out : Array Seg)
    (h : ∀ s ∈ out, s.NoGlyph) :
    ∀ s ∈ appendUnderline fs size obs x seg out, s.NoGlyph := by
  unfold appendUnderline
  split
  · intro s hs
    rcases Array.mem_push.mp hs with hs | rfl
    · exact h s hs
    · trivial
  · exact underlinePieces_noGlyph _ _ _ _ _ h

private theorem underlineSegs_noGlyph (fs : FontSet) (size : Sp) (segs : Array Seg) :
    ∀ s ∈ underlineSegs fs size segs, s.NoGlyph := by
  unfold underlineSegs
  dsimp only [Id.run, bind, pure, Id]
  split
  · apply Loop.forIn_array_inv (fun st : Sp × Array Seg => ∀ s ∈ st.2, s.NoGlyph)
    · simp
    · intro seg hseg st hst
      exact appendUnderline_noGlyph _ _ _ _ _ _ hst
  · simp

private theorem lineThroughSegs_noGlyph (segs : Array Seg) :
    ∀ s ∈ lineThroughSegs segs, s.NoGlyph := by
  unfold lineThroughSegs
  dsimp only [Id.run, bind, pure, Id]
  split
  · apply Loop.forIn_array_inv (fun out : Array Seg => ∀ s ∈ out, s.NoGlyph)
    · simp
    · intro seg hseg out hout
      have push (t : Seg) (ht : t.NoGlyph) : ∀ s ∈ out.push t, s.NoGlyph := by
        intro s hs
        rcases Array.mem_push.mp hs with hs | rfl
        · exact hout s hs
        · exact ht
      cases seg with
      | run fi c link w glyphs sz leading decorations raise ground attr =>
        cases hp : decorations.lineThrough <;>
          simp only [hp, Id.run, ForInStep.value] <;> exact push _ True.intro
      | decoratedGap w word decorations =>
        cases hp : decorations.lineThrough <;>
          simp only [hp, Id.run, ForInStep.value] <;> exact push _ True.intro
      | gap w word | decoration kind w thickness raise color | rule w thickness raise color
        | image store w height => exact push _ True.intro
      | poly pts color => exact hout
  · simp

private theorem decorationRiders_noGlyph (fs : FontSet) (l : LineOut) :
    ∀ r ∈ decorationRiders fs l, ∀ s ∈ r.segs, s.NoGlyph := by
  intro r hr
  obtain ⟨paint, hp, hr⟩ := Array.mem_filterMap.mp hr
  have hg : ∀ s ∈ paint, s.NoGlyph := by
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact underlineSegs_noGlyph fs l.size l.segs
    · exact lineThroughSegs_noGlyph l.segs
  split at hr
  · simp at hr
  · cases Option.some.inj hr
    exact hg

private theorem pushMark_noGlyph (out : Array Seg) (c : Color) (w t r : Sp)
    (hout : ∀ s ∈ out, s.NoGlyph) : ∀ s ∈ pushMark out c w t r, s.NoGlyph := by
  have push (t : Seg) (ht : t.NoGlyph) (xs : Array Seg) (hxs : ∀ s ∈ xs, s.NoGlyph) :
      ∀ s ∈ xs.push t, s.NoGlyph := by
    intro s hs
    rcases Array.mem_push.mp hs with hs | rfl
    · exact hxs s hs
    · exact ht
  have popped : ∀ s ∈ out.pop, s.NoGlyph := fun s hs =>
    hout s (Array.mem_def.mpr (List.dropLast_subset _ (by simpa using Array.mem_def.mp hs)))
  unfold pushMark
  split
  · split
    · exact push _ (by trivial) _ popped
    · exact push _ (by trivial) _ hout
  · exact push _ (by trivial) _ hout

private theorem markSegs_noGlyph (segs : Array Seg) :
    ∀ s ∈ markSegs segs, s.NoGlyph := by
  unfold markSegs
  dsimp only [Id.run, bind, pure, Id]
  split
  · apply Loop.forIn_array_inv (fun out : Array Seg => ∀ s ∈ out, s.NoGlyph)
    · simp
    · intro seg hseg out hout
      have push (t : Seg) (ht : t.NoGlyph) : ∀ s ∈ out.push t, s.NoGlyph := by
        intro s hs
        rcases Array.mem_push.mp hs with hs | rfl
        · exact hout s hs
        · exact ht
      cases seg with
      | run fi c link w glyphs sz leading decorations raise ground attr =>
        cases hp : decorations.highlight with
        | none => simp only [hp, Id.run, ForInStep.value]; exact push _ True.intro
        | some paint => simp only [hp, Id.run, ForInStep.value]; exact pushMark_noGlyph out _ _ _ _ hout
      | decoratedGap w word decorations =>
        cases hp : decorations.highlight with
        | none => simp only [hp, Id.run, ForInStep.value]; exact push _ True.intro
        | some paint => simp only [hp, Id.run, ForInStep.value]; exact pushMark_noGlyph out _ _ _ _ hout
      | gap w word | decoration kind w thickness raise color | rule w thickness raise color
        | image store w height => exact push _ True.intro
      | poly pts color => exact hout
  · simp

private theorem markRiders_noGlyph (l : LineOut) :
    ∀ r ∈ markRiders l, ∀ s ∈ r.segs, s.NoGlyph := by
  intro r hr
  obtain ⟨paint, hp, hr⟩ := Array.mem_filterMap.mp hr
  have hg : ∀ s ∈ paint, s.NoGlyph := by
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    split
    · simp
    · exact markSegs_noGlyph l.segs
  split at hr
  · simp at hr
  · cases Option.some.inj hr
    exact hg

private theorem sourceBound_appendMarks {n : Nat} (l : LineOut) (lines : Array LineOut)
    (h : ∀ l ∈ lines, l.furniture = false → l.SourceBound n) :
    ∀ r ∈ appendMarks l lines, r.furniture = false → r.SourceBound n := by
  unfold appendMarks
  dsimp only [Id.run, bind, pure, Id]
  apply Loop.forIn_array_inv
    (fun out : Array LineOut => ∀ r ∈ out, r.furniture = false → r.SourceBound n)
  · exact h
  · intro rider hr out hout r hm hf
    rcases Array.mem_push.mp hm with hm | rfl
    · exact hout r hm hf
    · exact Or.inr (markRiders_noGlyph l r hr)

private theorem sourceBound_appendRiders {n : Nat} (fs : FontSet) (l : LineOut)
    (lines : Array LineOut)
    (h : ∀ l ∈ lines, l.furniture = false → l.SourceBound n) :
    ∀ r ∈ appendRiders fs l lines, r.furniture = false → r.SourceBound n := by
  unfold appendRiders
  dsimp only [Id.run, bind, pure, Id]
  apply Loop.forIn_array_inv
    (fun out : Array LineOut => ∀ r ∈ out, r.furniture = false → r.SourceBound n)
  · exact h
  · intro rider hr out hout r hm hf
    rcases Array.mem_push.mp hm with hm | rfl
    · exact hout r hm hf
    · exact Or.inr (decorationRiders_noGlyph fs l r hr)

private theorem sourceBound_paintLines {n : Nat} (fs : FontSet) (lines : Array LineOut)
    (h : ∀ l ∈ lines, l.furniture = false → l.SourceBound n) :
    ∀ r ∈ paintLines fs lines, r.furniture = false → r.SourceBound n := by
  unfold paintLines
  dsimp only [Id.run, bind, pure, Id]
  apply Loop.forIn_array_inv
    (fun out : Array LineOut => ∀ r ∈ out, r.furniture = false → r.SourceBound n)
  · simp
  · intro l hl out hout
    apply sourceBound_appendRiders
    intro r hr hf
    rcases Array.mem_push.mp hr with hr | rfl
    · exact sourceBound_appendMarks l out hout r hr hf
    · exact h r hl hf

private def Spacing.Paragraph.lineStart (j : ParaJob) (first : Bool) (prev : Nat) : Nat :=
  if first then Layout.lineStart j.items (if j.hangIndent == 0 then 0 else 1)
  else Layout.lineStart j.items (prev + 1)

/-- The geometry of one paragraph line: its segs, x, set
width, overfull flag, protrusion hang and expansion factor. -/
private def paraLineGeom (fs : FontSet) (j : ParaJob) (b : B) (first : Bool)
    (prev brk : Nat) : Array Seg × Sp × Sp × Bool × Sp × Int :=
  -- A hanging first line starts past its kern, as the breaker priced it.
  let lead := if first then j.hangIndent else 0
  let width := j.target + lead
  let a := j.lineStart first prev
  -- A `\@flushglue` line wider than the measure takes its glue's shrink, as TeX's does.
  let shrinks := j.rightFil && width < (measure j.items a brk).natural
  let (segs0, w0, overfull, hang, exf) :=
    setLine j.items a brk width
      (setsToMeasure (!j.center && !j.flushRight && j.justify) j.items a brk || shrinks)
      (j.protrude && !shrinks) (j.expand && !shrinks) j.wordOffsets
  -- A flush-right line is never justified unless an author's fill spans it.
  let x0 := if j.center then b.geom.hmargin + j.indent + (width - w0) / 2
    else if j.flushRight then b.geom.hmargin + j.indent + (width - w0)
    else b.geom.hmargin + j.indent - lead - hang
  -- `\labelsep`: half an em (classes.dtx `\setlength\labelsep{.5em}`).
  let sep := b.geom.fontSize / 2
  let (segs1, x1, w1) :=
    if first then
      match j.markerSegs with
      | some (ms, mw) =>
        match j.markerLeft, j.markerIndent with
        | some ml, _ =>
          let x1 := b.geom.hmargin + ml
          (ms ++ #[Seg.gap (x0 - x1 - mw) false] ++ segs0, x1, w0 + (x0 - x1))
        | none, some mi =>
          let base := b.geom.hmargin + mi
          let x1 := base - mw - sep
          (ms ++ #[Seg.gap (x0 - base + sep) false] ++ segs0, x1, w0 + (x0 - x1))
        | none, none => (ms ++ #[Seg.gap sep false] ++ segs0, x0 - mw - sep, w0 + mw + sep)
      | none => (segs0, x0, w0)
    else (segs0, x0, w0)
  -- The rule fills the heading's line a word space from the text (`Ir.RulePosition.raise`).
  let (segs2, w2) :=
    if first then
      match j.rule with
      | some rule =>
        let gap := j.size / 2
        let ruleW := width - w1 - gap
        if ruleW > 0 then
          let xHeight := match segs1.find? (fun s => match s with
            | .run .. => true
            | _ => false) with
            | some (.run idx _ _ _ _ sz _ _ _ _ _) =>
              let font := fs.get idx
              let sz := if sz == 0 then j.size else sz
              scaledAt sz font font.xHeightOptical
            | _ => b.xHeight
          let raise := rule.position.raise xHeight
          (segs1 ++ #[Seg.gap gap false, Seg.rule ruleW rule.thickness raise rule.color], width)
        else (segs1, w1)
      | none => (segs1, w1)
    else (segs1, w1)
  (segs2, x1, w2, overfull, hang, exf)

/-- A display's first line takes TeX's skip above
(`Spacing.Page.displaySkip`), measured to the formula's box. -/
private def Spacing.Page.openDisplayAt (b : B) (j : ParaJob) (first : Bool) (x : Sp) (segs : Array Seg) :
    B :=
  match j.display, first with
  | some dj, true =>
    b.displaySkip dj
      (x - b.geom.hmargin + (segs.extract 0 dj.lead).foldl (fun acc sg => acc + sg.advance) 0)
      j.size
  | _, _ => b

@[simp] private theorem openDisplayAt_pages (b : B) (j : ParaJob) (f : Bool) (x : Sp)
    (segs : Array Seg) : (b.openDisplayAt j f x segs).pages = b.pages := by
  unfold Spacing.Page.openDisplayAt; split <;> rfl
@[simp] private theorem openDisplayAt_noBreak (b : B) (j : ParaJob) (f : Bool) (x : Sp)
    (segs : Array Seg) : (b.openDisplayAt j f x segs).noBreak = b.noBreak := by
  unfold Spacing.Page.openDisplayAt; split <;> rfl
@[simp] private theorem openDisplayAt_geom (b : B) (j : ParaJob) (f : Bool) (x : Sp)
    (segs : Array Seg) : (b.openDisplayAt j f x segs).geom = b.geom := by
  unfold Spacing.Page.openDisplayAt; split <;> rfl
@[simp] private theorem openDisplayAt_docBg (b : B) (j : ParaJob) (f : Bool) (x : Sp)
    (segs : Array Seg) : (b.openDisplayAt j f x segs).docBg = b.docBg := by
  unfold Spacing.Page.openDisplayAt; split <;> rfl

/-- A rule reaching past a TeX box's last line makes the line holding them as deep as the rule. -/
private def reachDepth (j : ParaJob) (brk : Nat) (b : B) : B :=
  match j.texBox.bind (·.reach) with
  | some (_, below) => if brk + 1 == j.items.size then b.keepInk (max b.boxDepth below) else b
  | none => b

/-- What follows a placed paragraph line: a forced break's
extra skip and the depth a box's rule leaves (`reachDepth`). -/
private def placeParaTrailer (_fs : FontSet) (j : ParaJob) (brk : Nat)
    (_segs : Array Seg) (b : B) : B :=
  let tex := j.texBox.isSome || b.texAfter
  let b := reachDepth j brk b
  match j.extras[brk]? with
  | some extra => { b with skip := { b.skip with width := b.skip.width + extra }, texAfter := tex }
  | none => { b with texAfter := tex }

@[simp] private theorem placeParaTrailer_pages (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).pages = b.pages := by
  simp only [placeParaTrailer, reachDepth]
  repeat' split
  all_goals first | rfl | simp

@[simp] private theorem placeParaTrailer_noBreak (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).noBreak = b.noBreak := by
  simp only [placeParaTrailer, reachDepth]
  repeat' split
  all_goals first | rfl | simp

private theorem decoration_no_growth (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).y = b.y ∧
      (placeParaTrailer fs j brk segs b).prevDepth = b.prevDepth ∧
      (placeParaTrailer fs j brk segs b).prevBelow = b.prevBelow ∧
      (placeParaTrailer fs j brk segs b).needed = b.needed := by
  simp only [placeParaTrailer, reachDepth]
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

private def Spacing.Page.withPendingSource (b : B) (source : Option Span) : B :=
  { b with pendingSource := source }

/-- Where a box-opening paragraph's first baseline stands below the band above:
TeX's interline rule for the box, then its inset and first line's height. -/
private def texBoxBaseline (fs : FontSet) (b : B) (j : ParaJob) (tb : TexBox) (segs : Array Seg)
    (last : Bool) : Sp :=
  let h1 := (lineStrutInk j.strut (segsInk fs segs)).1
  let bsIn := tb.leading
  let bsOut := Ir.leadingFor b.geom.fontSize b.geom.leading
  -- A rule reaching past the box's top makes the line holding both that much taller.
  let rise := match tb.reach with
    | some (height, _) => max 0 (height + tb.lastDepth - tb.inset)
    | none => 0
  let height := rise + tb.inset + h1 + (if last then 0 else bsIn)
  let top := if tb.more then b.boxDepth + inkClearance else texBoxTop bsOut b.boxDepth height
  top + rise + tb.inset + h1

/-- One break of a paragraph placed, the fold step `placePara` runs over its breaks. -/
private def placeParaLine (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) : B × Nat × Bool :=
  let b0 := st.1
  let g := paraLineGeom fs j b0 st.2.2 st.2.1 brk
  -- premise: reflowAccountChecks — every overrun line is named once, by W0005 or its re-flow.
  let b1 := if g.2.2.2.1 && !(j.carried[brk]?.getD false) then
      b0.warnOverfull (lineSource j.itemSources (j.lineStart st.2.2 st.2.1) brk)
    else b0
  -- The notes whose marks this line carries ride with it through fit and spill.
  let ns := if j.notes.isEmpty then #[] else
    (j.notes.filter fun n => (st.2.2 || st.2.1 < n.1) && n.1 < brk).map (·.2)
  -- A TeX box's later lines, and a boxless paragraph's first, stand by TeX's interline rule.
  let firstBaseline := match j.texBox with
    | some tb =>
      if st.2.2 && tb.boxed then some (texBoxBaseline fs b0 j tb g.1 (brk + 1 == j.items.size))
      else some (texBaselineGap tb.leading b0.boxDepth (lineStrutInk j.strut (segsInk fs g.1)).1)
    | none => if st.2.2 then j.firstBaseline else none
  let b1 := b1.openDisplayAt j st.2.2 g.2.1 g.1
  let b1 := b1.withPendingSource (lineSource j.itemSources (j.lineStart st.2.2 st.2.1) brk)
  (placeParaTrailer fs j brk g.1
    (b1.placeLine fs g.2.1 j.size g.1 g.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 ns
      (counted := !j.inFloat) (leaf := j.leaf) (firstBaseline := firstBaseline)
      (display := j.display) (opens := st.2.2)
      (anchors := lineAnchors j.anchors st.2.1 brk st.2.2 (brk + 1 == j.items.size))
      (paintPadding := if st.2.2 then j.paintPadding else none)
      (stepLead := j.lead) (rowStrut := j.rowStrut) (strut := j.strut)),
    brk, false)

/-- Whether item `k` is the end-fill before a forced
newline, a break that ends the same source segment. -/
-- premise: mintedSettingsChecks — a split declared line still raises W0386.
public def isEndFill (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.glue g) => g.parfill && isForced items (k + 1)
  | _ => false

/-- Read the item boundaries and the breaking task's result once, at
paragraph placement; an undeclaring paragraph records its own end alone. -/
public def paragraphBreaksOf (site : Nat) (leaf : Option Nat) (frame : Option FrameOrigin)
    (declares : Bool) (items : Array Item) (breaks : Array Nat) : ParagraphBreaks :=
  let forced := (Array.range items.size).filter (isForced items)
  { site := site, leaf := leaf, frame := frame
    forced := if declares then forced else forced.extract (forced.size - 1) forced.size
    chosen := breaks
    endFills := breaks.filter (isEndFill items) }

public theorem paragraphBreaksOf_forced_mem (site : Nat) (leaf : Option Nat)
    (frame : Option FrameOrigin) (items : Array Item) (breaks : Array Nat) (k : Nat) :
    k ∈ (paragraphBreaksOf site leaf frame true items breaks).forced ↔
      k < items.size ∧ isForced items k = true := by
  simp only [paragraphBreaksOf, ↓reduceIte, Array.mem_filter, Array.mem_range]

public theorem paragraphBreaksOf_endFills_mem (site : Nat) (leaf : Option Nat)
    (frame : Option FrameOrigin) (declares : Bool) (items : Array Item) (breaks : Array Nat)
    (k : Nat) :
    k ∈ (paragraphBreaksOf site leaf frame declares items breaks).endFills ↔
      k ∈ breaks ∧ isEndFill items k = true := by
  simp [paragraphBreaksOf]

public theorem paragraphBreaksOf_undeclared_exact (site : Nat) (leaf : Option Nat)
    (frame : Option FrameOrigin) (items : Array Item) (breaks : Array Nat) :
    (paragraphBreaksOf site leaf frame false items breaks).reflows = #[] := by
  simp only [ParagraphBreaks.reflows, paragraphBreaksOf, Bool.false_eq_true, ↓reduceIte]
  generalize (Array.range items.size).filter (isForced items) = forced
  have hpop : (forced.extract (forced.size - 1) forced.size).pop = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    simp only [Array.size_pop, Array.size_extract]
    omega
  simp [ParagraphBreaks.splitAt, hpop]

/-- The places a re-flow's detail names: line and column, the
file where it differs, the first three and how many more. -/
private def placesSaid (file : Option String) (sites : Array Span) : String :=
  let said := (sites.extract 0 3).toList.map fun s =>
    if file == some s.file then s!"{s.pos.line}:{s.pos.col}"
    else s!"{s.file}:{s.pos.line}:{s.pos.col}"
  match said.reverse with
  | [] => ""
  | [one] => one
  | last :: rest =>
    if sites.size > 3 then String.intercalate ", " said ++ s!" and {sites.size - 3} more"
    else String.intercalate ", " rest.reverse ++ " and " ++ last

/-- A paragraph's re-flow diagnostic (W0386) from its re-flowed
declared lines, the one maker placement and the postlude share. -/
private def reflowRecord (subject : String) (frame : Option Nat) (lines : Array ReflowedLine) :
    Diag :=
  let site := lines.findSome? (·.site)
  let over := lines.foldl (fun acc l => acc ++ l.over) #[]
  let ships := lines.foldl (fun n l => n + l.ships) 0
  let loc := match frame with
    | some n => s!"in frame {n}: "
    | none => ""
  let shape := if lines.size == 1 then s!"it ships as {ships} lines"
    else s!"{lines.size} declared lines ship as {ships} lines"
  let widest := over.foldl (fun m o => max m o.excess) 0
  let places := placesSaid (site.map (·.file)) (over.filterMap (·.site))
  let past := if over.isEmpty then "" else
    s!"; {over.size} {if over.size == 1 then "line runs" else "lines run"} past the measure, \
by up to {widest.toPtString}pt" ++ (if places.isEmpty then "" else s!", at {places}")
  Diag.of .W0386 (subject := some subject)
    (if over.isEmpty then "a declared line did not fit the measure and re-flowed"
      else "a declared line did not fit the measure and re-flowed, and a line of it \
still runs past the measure") site
    (help := "shorten the declared line, reduce \\page{ hmargin = ... } \
to widen the measure, or declare a narrower face")
    (detail := some (loc ++ shape ++ past)) (output := some .pdf)
    (carries := if over.isEmpty then [] else [.W0005])

/-- W0386: a declared line ended where the author meant it and re-flowed,
named rather than refused; silent where nothing was declared. -/
private def Spacing.Page.warnReflow (b : B) (p : ParagraphBreaks) (reflowed : Bool) : B :=
  if reflowed then
    { b with diags := b.diags.push (reflowRecord p.subject p.frameNumber p.lines) }
  else b

@[simp] private theorem warnReflow_pages (b : B) (q : ParagraphBreaks) (r : Bool) :
    (b.warnReflow q r).pages = b.pages := by
  simp only [Spacing.Page.warnReflow]
  split <;> rfl

@[simp] private theorem warnReflow_geom (b : B) (q : ParagraphBreaks) (r : Bool) :
    (b.warnReflow q r).geom = b.geom := by
  simp only [Spacing.Page.warnReflow]
  split <;> rfl

@[simp] private theorem warnReflow_docBg (b : B) (q : ParagraphBreaks) (r : Bool) :
    (b.warnReflow q r).docBg = b.docBg := by
  simp only [Spacing.Page.warnReflow]
  split <;> rfl

@[simp] private theorem warnReflow_cur (b : B) (q : ParagraphBreaks) (r : Bool) :
    (b.warnReflow q r).cur = b.cur := by
  simp only [Spacing.Page.warnReflow]
  split <;> rfl

@[simp] private theorem warnReflow_noBreak (b : B) (q : ParagraphBreaks) (r : Bool) :
    (b.warnReflow q r).noBreak = b.noBreak := by
  simp only [Spacing.Page.warnReflow]
  split <;> rfl

private theorem warnReflow_accounts (b : B) (q : ParagraphBreaks) (reflowed : Bool) :
    (b.warnReflow q reflowed).diags.size =
      b.diags.size + (if reflowed then 1 else 0) := by
  unfold Spacing.Page.warnReflow
  split <;> simp_all

/-- How far a paragraph's line sets past its measure, where its overrun flag is set. -/
private def lineOverrunBy (j : ParaJob) (first : Bool) (prev brk : Nat) : Option Sp :=
  let lead := if first then j.hangIndent else 0
  let width := j.target + lead
  let a := j.lineStart first prev
  let shrinks := j.rightFil && width < (measure j.items a brk).natural
  let set := setLine j.items a brk width
      (setsToMeasure (!j.center && !j.flushRight && j.justify) j.items a brk || shrinks)
      (j.protrude && !shrinks) (j.expand && !shrinks) j.wordOffsets
  if set.2.2.1 then some (set.2.1 - width) else none

private theorem paraLineGeom_overruns (fs : FontSet) (j : ParaJob) (b : B) (first : Bool)
    (prev brk : Nat) :
    (paraLineGeom fs j b first prev brk).2.2.2.1 = (lineOverrunBy j first prev brk).isSome := by
  unfold paraLineGeom lineOverrunBy
  dsimp only
  repeat' split
  all_goals simp_all

/-- Which breaks end a line of a re-flowed declared line, and
each such line with its rank, first item, lines and overruns. -/
private def reflowWalk (j : ParaJob) (p : ParagraphBreaks) : Array Bool × Array ReflowedLine :=
  Id.run do
  let split := p.splitAt
  let ends : Std.HashSet Nat := Std.HashSet.ofList (p.forced.toList ++ p.endFills.toList)
  let mut marks : Array Bool := Array.replicate (j.items.size + 1) false
  let mut out : Array ReflowedLine := #[]
  let mut cur : Option ReflowedLine := none
  let mut ordinal := 0
  let mut prev := 0
  let mut first := true
  for brk in p.chosen do
    if split brk || (!first && split prev) then
      marks := marks.set! brk true
      let start := j.lineStart first prev
      let line := cur.getD { ordinal := ordinal }
      let rank := line.ships
      let line := { line with
        site := line.site.orElse fun _ => lineSource j.itemSources start brk
        ships := rank + 1 }
      let line := match lineOverrunBy j first prev brk with
        | some excess =>
          let o : Overrun := { rank := rank, site := lineSource j.itemSources start brk,
                               excess := excess }
          { line with over := line.over.push o }
        | none => line
      if split brk then cur := some line
      else
        out := out.push line
        cur := none
    if ends.contains brk then ordinal := ordinal + 1
    prev := brk
    first := false
  if let some line := cur then out := out.push line
  return (marks, out)

/-- The breaks ending a line of a re-flowed declared line, by item index. -/
private def carriedBreaks (j : ParaJob) (breaks : Array Nat) : Array Bool :=
  let p := paragraphBreaksOf 0 none none j.declaresLines j.items breaks
  if p.reflows.isEmpty then #[] else (reflowWalk j p).1

/-- The paragraph's record of its breaks, with its
re-flowed declared lines and the frame its page shows. -/
private def paragraphRecord (b : B) (j : ParaJob) (breaks : Array Nat) : ParagraphBreaks :=
  let p := paragraphBreaksOf b.paragraphBreaks.size j.leaf b.curFrameOrigin j.declaresLines j.items breaks
  if p.reflows.isEmpty then p else
    let lines := (reflowWalk j p).2
    { p with key := lines.findSome? (·.site), lines := lines, frameNumber := b.curFrame }

/-- The job as its lines are placed: a reaching TeX box learns
its last line's depth first, and re-flowed lines are marked. -/
private def placedJob (fs : FontSet) (b : B) (j : ParaJob) (breaks : Array Nat) : ParaJob :=
  { j with carried := carriedBreaks j breaks, texBox := j.texBox.map fun tb =>
      if tb.reach.isNone then tb else
      match breaks.back? with
      | none => tb
      | some last =>
        let prev := (breaks[breaks.size - 2]?).getD 0
        let segs := (paraLineGeom fs j b (breaks.size == 1) prev last).1
        { tb with lastDepth := (lineStrutInk j.strut (segsInk fs segs)).2 } }

private def placePara (fs : FontSet) (b : B) (j : ParaJob) (breaks : Array Nat) : B :=
  let p := paragraphRecord b j breaks
  let start := ({ b with diags := b.diags ++ j.diags }).warnReflow p (!p.reflows.isEmpty)
  (breaks.foldl (placeParaLine fs (placedJob fs b j breaks))
    ({ start with paragraphBreaks := b.paragraphBreaks.push p }, 0, true)).1

private theorem sourceBound_placedJob {n : Nat} {fs : FontSet} {b : B} {j : ParaJob}
    {breaks : Array Nat} (hj : j.SourceBound n) : (placedJob fs b j breaks).SourceBound n :=
  ⟨hj.source, hj.notes, hj.marker, hj.rule⟩

private theorem sourceBound_paraLineGeom {n : Nat} (fs : FontSet) (j : ParaJob)
    (b : B) (first : Bool) (prev brk : Nat) (hj : j.SourceBound n) :
    (∃ k, j.leaf = some k ∧ k < n) ∨
      ∀ s ∈ (paraLineGeom fs j b first prev brk).1, s.NoGlyph := by
  rcases hj.source with h | h
  · exact Or.inl h
  · apply Or.inr
    cases first <;>
      simpa only [paraLineGeom, Bool.false_eq_true,
        ite_false, ite_true, hj.marker, hj.rule] using
        setLine_noGlyph j.items (j.lineStart _ prev) brk _ _ _
          _ j.wordOffsets h

private theorem sourceBound_openDisplayAt {n : Nat} (b : B) (j : ParaJob)
    (first : Bool) (x : Sp) (segs : Array Seg) (hb : b.SourceBound n) :
    (b.openDisplayAt j first x segs).SourceBound n := by
  unfold Spacing.Page.openDisplayAt
  split <;> exact hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_placeParaTrailer {n : Nat} (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) (hb : b.SourceBound n) :
    (placeParaTrailer fs j brk segs b).SourceBound n := by
  unfold placeParaTrailer reachDepth
  repeat' split
  all_goals exact hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_withPendingSource {n : Nat} (b : B) (source : Option Span)
    (hb : b.SourceBound n) : (b.withPendingSource source).SourceBound n :=
  hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_placeParaLine {n : Nat} (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat)
    (hj : j.SourceBound n) (hb : st.1.SourceBound n) :
    (placeParaLine fs j st brk).1.SourceBound n := by
  have hg := sourceBound_paraLineGeom fs j st.1 st.2.2 st.2.1 brk hj
  simp only [placeParaLine, hj.notes, Array.isEmpty_empty, ite_true]
  apply sourceBound_placeParaTrailer
  apply sourceBound_placeLine
  · apply sourceBound_withPendingSource
    apply sourceBound_openDisplayAt
    split
    · exact hb.of_eq rfl rfl rfl rfl rfl
    · exact hb
  · exact hg

private theorem sourceBound_placePara {n : Nat} (fs : FontSet) (b : B)
    (j : ParaJob) (breaks : Array Nat) (hj : j.SourceBound n)
    (hb : b.SourceBound n) : (placePara fs b j breaks).SourceBound n := by
  unfold placePara
  refine Array.foldl_induction
    (motive := fun _ (st : B × Nat × Bool) => st.1.SourceBound n) ?_ ?_
  · simp only [Spacing.Page.warnReflow]
    split <;> exact hb.of_eq rfl rfl rfl rfl rfl
  · intro i st h
    exact sourceBound_placeParaLine fs _ st breaks[i] (sourceBound_placedJob hj) h

/-- Plain-text items: discretionary spacing penalties, but no authored break or hyphen glyph. -/
private def Item.Prose : Item → Prop
  | .pen _ cost flagged _ _ glyphs =>
    forcedCost < cost ∧ flagged = false ∧ glyphs = #[]
  | .box .. | .glue .. | .decoratedGlue .. | .img .. | .rule .. | .poly .. => True

private def ItemsProse (items : Array Item) : Prop :=
  ∀ it ∈ items, it.Prose

@[simp] private theorem itemsProse_empty : ItemsProse #[] := by
  simp [ItemsProse]

@[simp] private theorem itemsProse_push (items : Array Item) (it : Item) :
    ItemsProse (items.push it) ↔ ItemsProse items ∧ it.Prose := by
  simp only [ItemsProse, Array.mem_push, or_imp, forall_and, forall_eq]

@[simp] private theorem itemsProse_append (xs ys : Array Item) :
    ItemsProse (xs ++ ys) ↔ ItemsProse xs ∧ ItemsProse ys := by
  simp [ItemsProse, or_imp, forall_and]

private theorem flushWord_prose (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (items : Array Item) (offsets : Std.HashMap Nat Sp)
    (sources : Array (Nat × Nat)) (box : Array (Nat × Char × Sp))
    (boxOwners : Array Attribution) (boxSources : Array Nat) (w : Sp)
    (hi : ItemsProse items) :
    ItemsProse (flushWord fontIdx color link size leading decorations ground attr items offsets
      sources box boxOwners boxSources w).1 := by
  unfold flushWord
  dsimp only
  split
  · exact hi
  · split
    · exact (itemsProse_push _ _).mpr ⟨hi, trivial⟩
    · apply Loop.bind_of_inv
        (P := fun st : Array Item × Std.HashMap Nat Sp × Array (Nat × Nat) ×
          Sp × Array (Nat × Char × Sp) × Sp × Attribution => ItemsProse st.1)
        (Q := fun out : Array Item × Std.HashMap Nat Sp × Array (Nat × Nat) =>
          ItemsProse out.1)
      · apply Loop.forIn_array_inv
          (P := fun st : Array Item × Std.HashMap Nat Sp × Array (Nat × Nat) ×
            Sp × Array (Nat × Char × Sp) × Sp × Attribution => ItemsProse st.1)
        · exact hi
        · rintro x _ ⟨is, os, ss, off, run, rw, owner⟩ hs
          dsimp only
          split
          · split <;> exact (itemsProse_push _ _).mpr ⟨hs, trivial⟩
          · exact hs
      · intro st hs
        split <;> exact (itemsProse_push _ _).mpr ⟨hs, trivial⟩

private theorem WordAcc.flush_prose (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (st : WordAcc)
    (hs : ItemsProse (WordAcc.items st)) :
    ItemsProse (WordAcc.items (st.flush fontIdx color link size leading decorations ground attr)) :=
  flushWord_prose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs

private theorem WordAcc.glyph_prose (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (smallcaps : Bool)
    (fs : FontSet) (font : Font) (c : Char) (sourceId : Nat)
    (owner : Attribution) (origin : Option Span) (st : WordAcc)
    (hs : ItemsProse (WordAcc.items st)) :
    ItemsProse (WordAcc.items (st.glyph fontIdx color link size leading decorations ground attr smallcaps
      fs font c sourceId owner origin)) := by
  unfold WordAcc.glyph
  split
  · exact hs
  · split
    · dsimp only
      split <;> exact (itemsProse_push _ _).mpr
        ⟨WordAcc.flush_prose _ _ _ _ _ _ _ _ st hs, trivial⟩
    · split <;> exact hs

private theorem WordAcc.letters_prose (fontIdx : Nat) (color : Ir.Color) (link : Option String)
    (size : Sp) (leading : Option Sp) (decorations : Decorations)
    (ground : Option Ir.Color) (attr : Attribution) (smallcaps : Bool)
    (fs : FontSet) (font : Font) (run : Array Char) (start : Nat)
    (owners : Array Attribution) (origins : Array (Option Span)) (hyphW : Sp) (st : WordAcc)
    (hs : ItemsProse (WordAcc.items st)) :
    ItemsProse (WordAcc.items (st.letters fontIdx color link size leading decorations ground attr smallcaps
      fs font run start owners origins #[] hyphW)) := by
  unfold WordAcc.letters
  simp only [Array.contains_empty, Bool.false_eq_true, ↓reduceIte, Id.run]
  apply Loop.forIn_array_inv (P := fun st : WordAcc => ItemsProse (WordAcc.items st))
  · exact hs
  · intro x _ st hs
    exact WordAcc.glyph_prose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st hs

private theorem wordItems_none_prose (langKey : String)
    (explicitBreak : Option Char → Char → Option Char → Option Nat)
    (size : Sp) (leading : Option Sp) (fontIdx : Nat)
    (color : Ir.Color) (ground : Option Ir.Color) (link : Option String)
    (decorations : Decorations) (smallcaps : Bool) (attr : Attribution)
    (fs : FontSet) (font : Font) (chars : Array Char) (missing : Array (Nat × Char))
    (substs : Array (Nat × Char × Nat)) (cache : Std.HashMap String (Array Nat))
    (owners : Array Attribution) (origins : Array (Option Span)) (sites : GlyphOrigins) :
    ItemsProse (wordItems none langKey explicitBreak size leading fontIdx color ground link
      decorations smallcaps attr fs font chars missing substs cache owners origins sites).1 := by
  unfold wordItems
  dsimp only
  apply Loop.bind_of_inv
    (P := fun st : WordAcc × Std.HashMap String (Array Nat) × Nat => ItemsProse (WordAcc.items st.1))
    (Q := fun out : Array Item × Array (Nat × Char) × Array (Nat × Char × Nat) ×
      Std.HashMap String (Array Nat) × Std.HashMap Nat Sp × Array (Nat × Nat) × GlyphOrigins =>
      ItemsProse out.1)
  · apply Loop.forIn_range_inv
      (P := fun st : WordAcc × Std.HashMap String (Array Nat) × Nat =>
        ItemsProse (WordAcc.items st.1))
    · exact itemsProse_empty
    · rintro k _ _ ⟨st, cache, i⟩ hs
      dsimp only
      split
      · split
        · exact WordAcc.letters_prose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st hs
        · split
          · exact (itemsProse_push _ _).mpr ⟨WordAcc.flush_prose _ _ _ _ _ _ _ _ st hs, trivial⟩
          · split
            · exact (itemsProse_push _ _).mpr ⟨WordAcc.flush_prose _ _ _ _ _ _ _ _ st hs, trivial⟩
            · have hg := WordAcc.glyph_prose fontIdx color link size leading decorations ground
                attr smallcaps fs font chars[i] i (owners[i]?.getD attr)
                (origins[i]?.getD none) st hs
              split
              · exact (itemsProse_push _ _).mpr
                  ⟨WordAcc.flush_prose _ _ _ _ _ _ _ _ _ hg, by
                    unfold Item.Prose; exact ⟨by unfold forcedCost; omega, rfl, rfl⟩⟩
              · exact hg
      · exact hs
  · intro st hs
    exact WordAcc.flush_prose _ _ _ _ _ _ _ _ st.1 hs

private theorem widenLast_prose (items : Array Item) (w : Sp)
    (hi : ItemsProse items) : ItemsProse (widenLast items w) := by
  unfold widenLast
  split
  · exact hi
  · split
    next g h =>
      obtain ⟨xs, rfl⟩ := Array.back?_eq_some_iff.mp h
      simpa [Array.setIfInBounds, Array.set_push, Item.Prose] using hi
    next g r h =>
      obtain ⟨xs, rfl⟩ := Array.back?_eq_some_iff.mp h
      simpa [Array.setIfInBounds, Array.set_push, Item.Prose] using hi
    next => exact hi

private theorem decoratedGlue_prose (g : Glue) (d : Decorations)
    (font : Font) (size : Sp) (color : Ir.Color) :
    (Item.ofDecoratedGlue g d font size color).Prose := by
  unfold Item.ofDecoratedGlue
  split <;> trivial

private theorem itemsOfTok_none_prose (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (tk : Tk) (owners : Array Attribution)
    (anchors : Array (String × Nat)) (origins : Array (Option Span))
    (source : Option Span) (ht : Tk.TextSource tk)
    (hi : ItemsProse (ItemsAcc.items acc)) :
    ItemsProse (ItemsAcc.items
      (itemsOfTok none size xHeight fs imgs textW textH
        acc tk owners anchors origins source)) := by
  cases tk <;> simp only [Tk.TextSource] at ht
  all_goals first | contradiction | skip
  case word sty cs attr =>
    simp only [itemsOfTok, ht, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      patsOf_off, ite_self]
    exact (itemsProse_append _ _).mpr ⟨widenLast_prose _ _ hi,
      wordItems_none_prose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  case space sty =>
    exact (itemsProse_push _ _).mpr ⟨hi, decoratedGlue_prose _ _ _ _ _⟩

private theorem itemsOfToks_none_prose (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (toks : Array Tk) (ht : ∀ tk ∈ toks, Tk.TextSource tk)
    (hi : ItemsProse (ItemsAcc.items acc)) :
    ItemsProse (ItemsAcc.items
      (itemsOfToks none size xHeight fs imgs textW textH acc toks)) := by
  unfold itemsOfToks
  dsimp only
  apply Loop.bind_of_inv
    (P := fun st : TokenState =>
      pendingTextSource st.2.1 ∧ ItemsProse (ItemsAcc.items st.1))
    (Q := fun out : ItemsAcc => ItemsProse (ItemsAcc.items out))
  · apply Loop.forIn_array_inv
      (P := fun st : TokenState =>
        pendingTextSource st.2.1 ∧ ItemsProse (ItemsAcc.items st.1))
    · exact ⟨trivial, hi⟩
    · intro tk htk state hs
      have hp := ht tk htk
      rcases state with ⟨a, pending, owners, origins, scope, anchors⟩
      rcases hs with ⟨hpending, ha⟩
      cases tk <;> simp only [Tk.TextSource] at hp
      all_goals first | contradiction | skip
      case word sty chars attr =>
        cases pending with
        | none => exact ⟨hp, ha⟩
        | some prev =>
          rcases prev with ⟨prev, word, first⟩
          dsimp only
          split
          · exact ⟨hpending, ha⟩
          · exact ⟨hp, itemsOfTok_none_prose _ _ _ _ _ _ _ _ _ _ _ _ hpending ha⟩
      case space sty =>
        cases pending with
        | none =>
          cases scope.head? <;>
            exact ⟨trivial, itemsOfTok_none_prose _ _ _ _ _ _ _ _ _ _ _ _ trivial ha⟩
        | some prev =>
          rcases prev with ⟨prev, word, first⟩
          have hw := itemsOfTok_none_prose size xHeight fs imgs textW textH a
            (Tk.word prev word first) owners anchors origins none hpending ha
          cases scope.head? <;>
            exact ⟨trivial, itemsOfTok_none_prose _ _ _ _ _ _ _ _ _ _ _ _ trivial hw⟩
  · rintro ⟨a, pending, owners, origins, scope, anchors⟩ ⟨hp, ha⟩
    cases pending with
    | none => exact ha
    | some prev =>
      rcases prev with ⟨sty, word, attr⟩
      exact itemsOfTok_none_prose size xHeight fs imgs textW textH a
        (Tk.word sty word attr) owners anchors origins none hp ha

private def paraItems (items : Array Item) : Array Item :=
  items.push (.glue { fil := true, parfill := true }) |>.push
    (.pen 0 forcedCost false 0 Ir.Color.black #[])

private theorem itemsOfInlines_none_prose (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (Array Nat)) (ctr : LeafCtr) (imgs : Image.Store)
    (textW textH : Sp) (noteOk : Bool) (ladder : List (String × Nat)) (step : Nat)
    (roleMetrics : List (String × (Sp × Option Sp))) (steps : Nat)
    (hp : PlainInlines xs) (hs : baseStyle.smallcaps = false) :
    ∃ items, ItemsProse items ∧
      (itemsOfInlines none size xHeight fs baseStyle xs cache ctr imgs textW textH
        noteOk ladder step roleMetrics steps).1 = paraItems items := by
  let st := flatten fs.mathFont?.isSome noteOk
    (FlattenSt.mk #[] false #[] ladder roleMetrics ctr step steps) baseStyle xs
  let acc := itemsOfToks none size xHeight fs imgs textW textH
    (ItemsAcc.mk #[] #[] #[] #[] #[] #[] #[] #[] {} {} cache 0 0) (FlattenSt.toks st)
  have ht := flatten_textSource fs.mathFont?.isSome noteOk
    (FlattenSt.mk #[] false #[] ladder roleMetrics ctr step steps)
    baseStyle xs hp hs (by simp)
  have ha : ItemsProse (ItemsAcc.items acc) :=
    itemsOfToks_none_prose _ _ _ _ _ _ _ _ ht itemsProse_empty
  refine ⟨ItemsAcc.items acc, ha, ?_⟩
  simp only [itemsOfInlines, bind, pure, Id.run]
  split
  next w cost flagged font color glyphs he =>
    have hh := ha _ (Array.mem_of_back? (show (ItemsAcc.items acc).back? =
      some (.pen w cost flagged font color glyphs) from he))
    simp only [Item.Prose] at hh
    have hc : ¬ cost ≤ forcedCost := by omega
    simp only [hc, decide_false, Bool.not_false, ↓reduceIte]
    rfl
  next =>
    simp only [Bool.not_false, ↓reduceIte]
    rfl

private theorem paraItems_size (items : Array Item) :
    (paraItems items).size = items.size + 2 := by simp [paraItems, Nat.add_assoc]

private theorem paraItems_end (items : Array Item) :
    canBreakAt (paraItems items) ((paraItems items).size-1) = true := by
  rw [paraItems_size]
  have he : items.size + 2 - 1 =
      (items.push (.glue { fil := true, parfill := true })).size := by simp
  rw [he]
  simp only [paraItems, canBreakAt, Array.getElem?_push_size]
  rfl

private theorem itemsProse_isForced (items : Array Item) (hp : ItemsProse items) (k : Nat) :
    isForced items k = false := by
  unfold isForced
  split
  next w cost flagged font color glyphs he =>
    have hi := hp _ (Array.mem_of_getElem? he)
    simp only [Item.Prose] at hi
    simp [show ¬ cost ≤ forcedCost by omega]
  next => rfl

private theorem paraItems_noEarlierForced (items : Array Item) (hp : ItemsProse items)
    (k : Nat) (hk : k+1 < (paraItems items).size) :
    isForced (paraItems items) k = false := by
  have hk' : k < items.size+1 := by rw [paraItems_size] at hk; omega
  unfold isForced paraItems
  rw [Array.getElem?_push_lt (by simpa using hk')]
  by_cases h : k < items.size
  · rw [Array.getElem_push_lt h]
    simpa only [isForced, Array.getElem?_eq_getElem h] using itemsProse_isForced items hp k
  · have he : k = items.size := by omega
    subst k
    simp

private def Item.UnflaggedEmpty : Item → Prop
  | .pen _ _ flagged _ _ glyphs => flagged = false ∧ glyphs = #[]
  | .box .. | .glue .. | .decoratedGlue .. | .img .. | .rule .. | .poly .. => True

private theorem itemsProse_unflagged (items : Array Item) (hp : ItemsProse items) :
    ∀ it ∈ paraItems items, it.UnflaggedEmpty := by
  intro it hi
  simp only [paraItems, Array.mem_push] at hi
  rcases hi with (hi | rfl) | rfl
  · have hh := hp it hi
    cases it <;> simp_all [Item.Prose, Item.UnflaggedEmpty]
  · trivial
  · exact ⟨rfl, rfl⟩

private theorem raggedItems_prose (items : Array Item) (hp : ItemsProse items) :
    ItemsProse (raggedItems items) := by
  intro it hi
  obtain ⟨src, hs, rfl⟩ := Array.mem_map.mp hi
  have hh := hp src hs
  cases src <;> dsimp only
  all_goals first | exact hh | (split <;> trivial)

private theorem raggedItems_paraItems (items : Array Item) :
    raggedItems (paraItems items) = paraItems (raggedItems items) := by
  simp [raggedItems, paraItems]

private theorem kpTwoPass_unflagged (items : Array Item) (target : Sp) (protrude expand : Bool)
    (bg : Sp) (fil : Bool) {runt : Bool} (hp : ∀ it ∈ items, it.UnflaggedEmpty) :
    kpTwoPass items target protrude expand bg fil runt =
      kp items target protrude expand bg fil runt := by
  unfold kpTwoPass
  dsimp only
  split
  · rfl
  · rename_i hn
    exfalso
    apply hn
    simp only [Bool.not_eq_true', Array.any_eq_false']
    intro it hi
    have hh := hp it hi
    cases it <;> simp_all [Item.UnflaggedEmpty]

private theorem kpTwoPass_paraItems_chars (items : Array Item) (target : Sp)
    (protrude expand : Bool) (bg : Sp) (fil : Bool) {runt : Bool} (hp : ItemsProse items) :
    (breakSpans (paraItems items)
        (kpTwoPass (paraItems items) target protrude expand bg fil runt).toList).1 =
      (paraItems items).toList.flatMap Item.boxChars := by
  rw [kpTwoPass_unflagged _ _ _ _ _ _ (itemsProse_unflagged items hp)]
  exact kp_boxChars _ _ _ _ _ _ (by simp [paraItems_size]) (paraItems_end items)
    (paraItems_noEarlierForced items hp)

private theorem setLine_unflagged_chars (items : Array Item) (a j : Nat) (target : Sp)
    (justify protrude expand : Bool) (wordOffsets : Std.HashMap Nat Sp)
    (hp : ∀ it ∈ items, it.UnflaggedEmpty) :
    (setLine items a j target justify protrude expand wordOffsets).1.toList.flatMap Seg.glyphChars =
      itemSpan items a j := by
  have hh := setLineSegments_glyphChars items a j
    (LineSetting.measured (lineSetting items a j target justify protrude expand wordOffsets))
    (LineSetting.delta (lineSetting items a j target justify protrude expand wordOffsets))
    (LineSetting.factor (lineSetting items a j target justify protrude expand wordOffsets))
    justify (LineSetting.fils (lineSetting items a j target justify protrude expand wordOffsets)) wordOffsets
  change (setLineSegments items a j _ _ _ justify _ wordOffsets).1.toList.flatMap Seg.glyphChars = _
  rw [hh]
  split
  next w cost flagged font color glyphs he =>
    have hg : glyphs = #[] := (hp _ (Array.mem_of_getElem? he)).2
    simp [hg, itemSpan]
  next => simp [itemSpan]

/-- A line's census scalars, furniture included only when `pick` asks. -/
private def lineCensus (pick : Option Nat → Bool → Bool) (l : LineOut) : List Char :=
  if pick l.leaf l.counted then l.segs.toList.flatMap Seg.glyphChars else []

private def pageCensus (pick : Option Nat → Bool → Bool) (p : PageOut) : List Char :=
  p.lines.toList.flatMap (lineCensus pick)

private def Spacing.Page.census (pick : Option Nat → Bool → Bool) (b : B) : List Char :=
  (Spacing.Page.pages b).toList.flatMap (pageCensus pick) ++ pageCensus pick (Spacing.Page.cur b)

private theorem census_of_eq (pick : Option Nat → Bool → Bool) (b b' : B)
    (hc : (Spacing.Page.cur b').lines = (Spacing.Page.cur b).lines) (hp : Spacing.Page.pages b' = Spacing.Page.pages b) :
    Spacing.Page.census pick b' = Spacing.Page.census pick b := by
  simp only [Spacing.Page.census, pageCensus, hc, hp]

private theorem map_lineCensus_mapIdx (pick : Option Nat → Bool → Bool)
    (xs : Array LineOut) (f : Nat → LineOut → LineOut)
    (hf : ∀ i l, lineCensus pick (f i l) = lineCensus pick l) :
    (xs.mapIdx f).map (lineCensus pick) = xs.map (lineCensus pick) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [hf]

private theorem map_lineCensus_zip (pick : Option Nat → Bool → Bool)
    (xs : Array LineOut) (sh : Array Sp) (hsz : sh.size = xs.size)
    (f : LineOut × Sp → LineOut)
    (hf : ∀ p, lineCensus pick (f p) = lineCensus pick p.1) :
    ((xs.zip sh).map f).map (lineCensus pick) = xs.map (lineCensus pick) := by
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    simp [hf]

private theorem finishPage_lineCensus (pick : Option Nat → Bool → Bool)
    (b : B) (owed : Sp) (flush : Bool)
    (hs : (Spacing.Page.shrinkAbove b).size = (Spacing.Page.cur b).lines.size) :
    ((Spacing.Page.pages (Spacing.Page.finishPage b owed flush)).back?.map
      fun p => p.lines.map (lineCensus pick)) =
      some ((Spacing.Page.cur b).lines.map (lineCensus pick) ++
        (Spacing.Page.noteLines b).map (lineCensus pick)) := by
  simp only [Spacing.Page.finishPage, Array.back?_push, Option.map_some, Option.some.injEq,
    Array.map_append]
  congr 1
  repeat' split
  all_goals
    first
    | rfl
    | (exact map_lineCensus_zip pick _ _ hs _ (fun p => rfl))
    | (refine map_lineCensus_mapIdx pick _ _ ?_
       intro i l
       split <;> rfl)
    | (refine (map_lineCensus_mapIdx pick _ _ ?_).trans
        (map_lineCensus_zip pick _ _ hs _ (fun p => rfl))
       intro i l
       split <;> rfl)

private theorem census_finishPage {n : Nat} (pick : Option Nat → Bool → Bool)
    (b : B) (owed : Sp) (flush : Bool) (hb : Spacing.Page.SourceBound n b) :
    Spacing.Page.census pick (Spacing.Page.finishPage b owed flush) = Spacing.Page.census pick b := by
  have he := finishPage_lineCensus pick b owed flush (Spacing.Page.SourceBound.ledger hb)
  change ((Spacing.Page.pages b).push _).back?.map _ = _ at he
  simp only [Array.back?_push, Option.map_some, Option.some.injEq] at he
  have hn : Spacing.Page.noteLines b = #[] := by
    simp [Spacing.Page.noteLines, Spacing.Page.SourceBound.notes hb]
  simp only [hn, Array.map_empty, Array.append_empty] at he
  have ht := congrArg (fun ls : Array (List Char) => ls.toList.flatten) he
  simp only [Array.toList_map, ← List.flatMap_def] at ht
  change ((Spacing.Page.pages b).push _).toList.flatMap (pageCensus pick) ++ [] = _
  simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  change _ ++ _ = _ ++ _
  simpa only [pageCensus, Array.toList_append, hn, Array.toList_empty,
    List.flatMap_append, List.flatMap_nil, List.append_nil] using
    congrArg ((Spacing.Page.pages b).toList.flatMap (pageCensus pick) ++ ·) ht

private theorem census_warnSpill (pick : Option Nat → Bool → Bool) (b : B) (over : Sp) :
    Spacing.Page.census pick (Spacing.Page.warnSpill b over) = Spacing.Page.census pick b := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals exact census_of_eq pick b _ rfl rfl

private theorem census_spillPage {n : Nat} (pick : Option Nat → Bool → Bool)
    (b : B) (over : Sp) (hb : Spacing.Page.SourceBound n b) :
    Spacing.Page.census pick (Spacing.Page.spillPage b over) = Spacing.Page.census pick b := by
  have hc : Spacing.Page.chrome (Spacing.Page.finishPage b 0 (Spacing.Page.flushes b)) = none := by
    simpa only [Spacing.Page.finishPage] using Spacing.Page.SourceBound.chrome hb
  change Spacing.Page.census pick (Spacing.Page.warnSpill (Spacing.Page.reopenChrome (Spacing.Page.finishPage b 0 (Spacing.Page.flushes b))) over) = _
  rw [census_warnSpill]
  simpa only [Spacing.Page.reopenChrome, hc] using census_finishPage pick b 0 (Spacing.Page.flushes b) hb

private theorem census_commit (pick : Option Nat → Bool → Bool) (b : B) (l : LineOut)
    (depth below : Sp) (rl consume : Bool) (over : Sp) :
    Spacing.Page.census pick (Spacing.Page.commit b l depth below rl consume over) =
      Spacing.Page.census pick b ++ lineCensus pick l := by
  simp [Spacing.Page.census, pageCensus, Spacing.Page.commit, lineCensus, List.append_assoc]

private theorem census_warnNoteOverrun (pick : Option Nat → Bool → Bool)
    (b : B) (y d : Sp) :
    Spacing.Page.census pick (Spacing.Page.warnNoteOverrun b y d) = Spacing.Page.census pick b := by
  unfold Spacing.Page.warnNoteOverrun
  dsimp only
  split <;> exact census_of_eq pick b _ rfl rfl

private theorem census_noteOverrun (pick : Option Nat → Bool → Bool) (b : B) (o : Sp) :
    Spacing.Page.census pick (Spacing.Page.noteOverrun b o) = Spacing.Page.census pick b := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals exact census_of_eq pick b _ rfl rfl

private theorem census_fitCommit {n : Nat} (pick : Option Nat → Bool → Bool)
    (b : B) (mk : Sp → LineOut) (firstY stepY retryY : B → Sp)
    (depth below : Sp) (rl : Bool) (inkBelow bottom : Sp)
    (cs : List Char) (hb : Spacing.Page.SourceBound n b) (hm : ∀ y, lineCensus pick (mk y) = cs) :
    Spacing.Page.census pick (Spacing.Page.fitCommit b mk firstY stepY retryY depth below rl inkBelow bottom #[]) =
      Spacing.Page.census pick b ++ cs := by
  simp only [Spacing.Page.fitCommit, Spacing.Page.fitWith, Spacing.Page.attachNotes, Array.isEmpty_empty, ite_true]
  split
  · rw [census_warnNoteOverrun, census_commit, hm]
  · split
    · rw [census_commit, hm]
    · split
      · rw [census_noteOverrun, census_commit, hm]
      · rw [census_noteOverrun]
        split <;> rw [census_warnNoteOverrun, census_commit, hm,
          census_spillPage pick b _ hb]

private theorem filter_zeroRule_chars (segs : Array Seg) :
    (segs.filter fun s => match s with | .rule w _ _ _ => w != 0 | _ => true).toList.flatMap
      Seg.glyphChars = segs.toList.flatMap Seg.glyphChars := by
  rw [Array.toList_filter]
  induction segs.toList with
  | nil => rfl
  | cons s ss ih =>
    cases s <;> simp_all [List.filter_cons, Seg.glyphChars]
    split <;> simp_all [Seg.glyphChars]

private theorem census_keepInk (pick : Option Nat → Bool → Bool) (b : B) (ink : Sp) :
    Spacing.Page.census pick (Spacing.Page.keepInk b ink) = Spacing.Page.census pick b := rfl

private theorem census_displayState (pick : Option Nat → Bool → Bool)
    (b : B) (tex : Bool) (e : Option Sp) :
    Spacing.Page.census pick (Spacing.Page.displayState b tex e) = Spacing.Page.census pick b := rfl

private theorem census_placeLine {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (b : B) (x size : Sp) (segs : Array Seg) (w hang : Sp) (ex : Int)
    (counted : Bool) (leaf : Option Nat) (firstBaseline : Option Sp)
    (display : Option DisplayJob) (opens : Bool) (anchors : Array String)
    (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp)
    (hb : Spacing.Page.SourceBound n b) :
    Spacing.Page.census pick (Spacing.Page.placeLine fs b x size segs w hang ex #[] counted leaf
      firstBaseline display opens anchors paintPadding step rs strut) =
      Spacing.Page.census pick b ++ (if pick leaf counted then segs.toList.flatMap Seg.glyphChars else []) := by
  simp only [Spacing.Page.placeLine]
  rw [census_displayState, census_keepInk]
  apply census_fitCommit
  · exact hb
  · intro y
    simp only [lineCensus]
    split
    · exact filter_zeroRule_chars segs
    · rfl

private theorem KpChain.members_lt {items : Array Item} {last : Nat} {breaks : List Nat}
    (h : KpChain items last breaks) : ∀ k ∈ breaks, k < items.size := by
  induction h with
  | first hj _ _ => simpa using hj
  | next chain _ hj _ _ ih =>
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact ih k hk
    · rcases List.mem_singleton.mp hk with rfl
      exact hj

private theorem kp_members_lt (items : Array Item) (target : Sp) (protrude expand : Bool)
    (bg : Sp) (fil : Bool) {runt : Bool} (hn : 0 < items.size) :
    ∀ k ∈ kp items target protrude expand bg fil runt, k < items.size := by
  let sums := { kpSums items with bg := bg }
  let slack : Sp := if protrude then maxProtrudeRight items else 0
  let st := kpForward items sums target slack protrude expand fil runt items.size
  have ht := (kpForward_valid items sums target slack protrude expand fil (runt := runt) items.size
    (Nat.le_refl _)).1
  unfold kp
  change ∀ k ∈ (match (KpState.best st).getD (items.size-1) none with
    | none => #[] | some _ => kpBack items.size (KpState.best st) (items.size-1)), k < items.size
  cases he : (KpState.best st).getD (items.size-1) none with
  | none => simp
  | some e =>
    have hc := kpBack_chain items (KpState.best st) ht (items.size-1) (by omega)
      (by rw [he]; rfl)
    simpa only [Array.mem_toList_iff] using hc.members_lt

private theorem paraLineGeom_chars {n : Nat} (fs : FontSet) (j : ParaJob)
    (b : B) (first : Bool) (prev brk : Nat) (hj : j.SourceBound n)
    (hp : ∀ it ∈ (Spacing.Paragraph.items j), it.UnflaggedEmpty) :
    (paraLineGeom fs j b first prev brk).1.toList.flatMap Seg.glyphChars =
      itemSpan (Spacing.Paragraph.items j) (j.lineStart first prev) brk := by
  cases first <;>
    simpa only [paraLineGeom, Bool.false_eq_true, ite_false, ite_true, (Spacing.Paragraph.SourceBound.marker hj), (Spacing.Paragraph.SourceBound.rule hj)] using
      setLine_unflagged_chars (Spacing.Paragraph.items j) (j.lineStart _ prev) brk _ _ _ _
        (Spacing.Paragraph.wordOffsets j) hp

private theorem census_warnOverfull (pick : Option Nat → Bool → Bool) (b : B)
    (source : Option Span) : Spacing.Page.census pick (Spacing.Page.warnOverfull b source) = Spacing.Page.census pick b := rfl

private theorem census_openDisplayAt (pick : Option Nat → Bool → Bool) (b : B) (j : ParaJob)
    (first : Bool) (x : Sp) (segs : Array Seg) :
    Spacing.Page.census pick (Spacing.Page.openDisplayAt b j first x segs) = Spacing.Page.census pick b := by
  unfold Spacing.Page.openDisplayAt
  split <;> rfl

private theorem census_placeParaTrailer (pick : Option Nat → Bool → Bool) (fs : FontSet)
    (j : ParaJob) (brk : Nat) (segs : Array Seg) (b : B) :
    Spacing.Page.census pick (placeParaTrailer fs j brk segs b) = Spacing.Page.census pick b := by
  unfold placeParaTrailer reachDepth
  repeat' split
  all_goals rfl

private theorem census_withPendingSource (pick : Option Nat → Bool → Bool) (b : B)
    (source : Option Span) :
    Spacing.Page.census pick (b.withPendingSource source) = Spacing.Page.census pick b := rfl

private theorem census_placeParaLine {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (j : ParaJob) (st : B × Nat × Bool) (brk : Nat)
    (hj : j.SourceBound n) (hb : st.1.SourceBound n)
    (hp : ∀ it ∈ (Spacing.Paragraph.items j), it.UnflaggedEmpty) :
    Spacing.Page.census pick (placeParaLine fs j st brk).1 = Spacing.Page.census pick st.1 ++
      (if pick (Spacing.Paragraph.leaf j) (!(Spacing.Paragraph.inFloat j)) then itemSpan (Spacing.Paragraph.items j) (j.lineStart st.2.2 st.2.1) brk
       else []) := by
  simp only [placeParaLine, (Spacing.Paragraph.SourceBound.notes hj), Array.isEmpty_empty, ite_true]
  rw [census_placeParaTrailer, census_placeLine]
  · rw [census_withPendingSource, census_openDisplayAt]
    split <;> simp only [census_warnOverfull, paraLineGeom_chars fs j st.1 _ _ _ hj hp]
  · apply sourceBound_withPendingSource
    apply sourceBound_openDisplayAt
    split
    · exact hb.of_eq rfl rfl rfl rfl rfl
    · exact hb

private theorem paraStart_cursor (j : ParaJob) (first : Bool) (prev : Nat)
    (hh : (Spacing.Paragraph.hangIndent j) = 0) (hp : first = true ∨ prev < (Spacing.Paragraph.items j).size) :
    j.lineStart first prev = kpStart (Spacing.Paragraph.items j) (if first then (Spacing.Paragraph.items j).size else prev) := by
  cases first
  · simp only [Bool.false_eq_true, false_or] at hp
    simp [Spacing.Paragraph.lineStart, kpStart, Nat.ne_of_lt hp]
  · simp [Spacing.Paragraph.lineStart, kpStart, hh]

private theorem spanFold_prefix (items : Array Item) (breaks : List Nat) (cs : List Char) (prev : Nat) :
    breaks.foldl (fun st j => (st.1 ++ itemSpan items (kpStart items st.2) j, j)) (cs, prev) =
      let out := breaks.foldl (fun st j => (st.1 ++ itemSpan items (kpStart items st.2) j, j))
        ([], prev)
      (cs ++ out.1, out.2) := by
  induction breaks generalizing cs prev with
  | nil => simp
  | cons brk breaks ih =>
    simp only [List.foldl_cons, List.nil_append]
    rw [ih (cs ++ _) brk, ih (itemSpan items (kpStart items prev) brk) brk]
    simp only [List.append_assoc]

private theorem census_paraFold {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (j : ParaJob) (breaks : List Nat) (st : B × Nat × Bool)
    (hj : j.SourceBound n) (hb : st.1.SourceBound n) (hh : (Spacing.Paragraph.hangIndent j) = 0)
    (hp : ∀ it ∈ (Spacing.Paragraph.items j), it.UnflaggedEmpty)
    (hk : ∀ k ∈ breaks, k < (Spacing.Paragraph.items j).size)
    (hc : st.2.2 = true ∨ st.2.1 < (Spacing.Paragraph.items j).size) :
    Spacing.Page.census pick (breaks.foldl (placeParaLine fs j) st).1 = Spacing.Page.census pick st.1 ++
      (if pick (Spacing.Paragraph.leaf j) (!(Spacing.Paragraph.inFloat j)) then
        (breaks.foldl (fun acc brk =>
          (acc.1 ++ itemSpan (Spacing.Paragraph.items j) (kpStart (Spacing.Paragraph.items j) acc.2) brk, brk))
            ([], if st.2.2 then (Spacing.Paragraph.items j).size else st.2.1)).1 else []) := by
  induction breaks generalizing st with
  | nil => simp
  | cons brk breaks ih =>
    simp only [List.foldl_cons, List.nil_append]
    rw [ih (placeParaLine fs j st brk) (sourceBound_placeParaLine fs j st brk hj hb)
      (fun k hm => hk k (List.mem_cons_of_mem _ hm))
      (Or.inr (hk brk (List.mem_cons_self))) ]
    rw [census_placeParaLine pick fs j st brk hj hb hp, paraStart_cursor j _ _ hh hc]
    rw [spanFold_prefix (Spacing.Paragraph.items j) breaks (itemSpan (Spacing.Paragraph.items j) _ brk) brk]
    change _ = _ ++ if pick (Spacing.Paragraph.leaf j) (!(Spacing.Paragraph.inFloat j)) then _ else []
    dsimp only [placeParaLine]
    split <;> simp only [Bool.false_eq_true, ite_false, List.append_assoc, List.append_nil]

private theorem census_placePara {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (b : B) (j : ParaJob) (breaks : Array Nat)
    (hj : j.SourceBound n) (hb : b.SourceBound n) (hh : Spacing.Paragraph.hangIndent j = 0)
    (hp : ∀ it ∈ Spacing.Paragraph.items j, it.UnflaggedEmpty)
    (hk : ∀ k ∈ breaks, k < (Spacing.Paragraph.items j).size) :
    Spacing.Page.census pick (placePara fs b j breaks) = Spacing.Page.census pick b ++
      (if pick (Spacing.Paragraph.leaf j) (!(Spacing.Paragraph.inFloat j)) then
        (breakSpans (Spacing.Paragraph.items j) breaks.toList).1 else []) := by
  unfold placePara
  dsimp only
  rw [← Array.foldl_toList]
  rw [census_paraFold pick fs (placedJob fs b j breaks) breaks.toList _
    (sourceBound_placedJob hj)]
  · simp only [breakSpans, ite_true, Spacing.Page.warnReflow]
    split <;> rfl
  · unfold Spacing.Page.warnReflow
    split <;> exact hb.of_eq rfl rfl rfl rfl rfl
  · exact hh
  · exact hp
  · exact fun k hm => hk k (Array.mem_toList_iff.mp hm)
  · exact Or.inl rfl

private theorem census_placePara_prose {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (b : B) (j : ParaJob) (items : Array Item) (protrude expand fil : Bool) {runt : Bool}
    (hj : j.SourceBound n) (hb : b.SourceBound n) (hh : Spacing.Paragraph.hangIndent j = 0)
    (hp : ItemsProse items) (he : Spacing.Paragraph.items j = paraItems items) :
    Spacing.Page.census pick (placePara fs b j
      (kpTwoPass (Spacing.Paragraph.items j) (Spacing.Paragraph.target j) protrude expand
        (Spacing.Paragraph.background j) fil runt)) =
      Spacing.Page.census pick b ++ (if pick (Spacing.Paragraph.leaf j) (!(Spacing.Paragraph.inFloat j)) then
        (Spacing.Paragraph.items j).toList.flatMap Item.boxChars else []) := by
  rw [census_placePara pick fs b j _ hj hb hh]
  · rw [he, kpTwoPass_paraItems_chars _ _ _ _ _ _ hp]
  · rw [he]
    exact itemsProse_unflagged items hp
  · rw [he, kpTwoPass_unflagged _ _ _ _ _ _ (itemsProse_unflagged items hp)]
    exact kp_members_lt _ _ _ _ _ _ (by simp [paraItems_size])


public theorem substPage_id (n total : Nat) (xs : Array Ir.Inline)
    (h : Ir.hasPhysicalPage xs = false) : substPage n total xs = xs :=
  Ir.mapInlines_id (substPageLeaf n total) Ir.isPhysicalPage
    (fun x hx => by cases x <;> simp_all [Ir.isPhysicalPage, substPageLeaf]) xs h

public theorem substPage_leaves_frame_slot (n total k tot : Nat) (s : Ir.ChromeSlot)
    (sec : Array Inline) (hs : s.isFrameSequence = true) :
    substPage n total (s.render sec k tot) = s.render sec k tot :=
  substPage_id n total _ (Ir.frame_sequence_carries_no_physical s sec k tot hs)

/-- The ops a plain source paragraph and its boundary
emit, the source bound belonging to the paragraph job. -/
private def Op.SourceBound (n : Nat) : Op → Prop
  | .para j _ => j.SourceBound n
  | .skip _ | .skipAlt _ _ | .anchorRule _ | .anchor _ => True
  | _ => False

/-- A selected picture's label occurrences, indexed before placement. -/
public def pictureLabelRequests (origin : Nat) (pic : Ir.Pic.Picture) :
    Array LabelAudit.Request :=
  (pic.shapes.mapIdx fun i shape => match shape with
    | .label _ _ content _ _ _ =>
      some ({ origin := (origin, i)
              key := Ir.plainText content
              source := Ir.inlineSource content
              blank := labelTextBlank content } : LabelAudit.Request)
    | .ink _ => none).filterMap id

private def stagedLabelRequests (ops : Array Op) : Array LabelAudit.Request :=
  ops.flatMap fun op => match op with
    | .picture _ pic _ origin => pictureLabelRequests origin pic
    | .skip _ | .skipAlt _ _ | .bodyOpen _ _ | .brk | .pageOpening _
      | .pageStyle _ _ | .pageGround _ | .titleBar _ _ _ | .frameOpen _ _ _
      | .frameClose | .boxAnchor _ _ _ | .hrule _ _ | .tableRule _ _ _ _
      | .pin | .progress _ _ _ _ _ _ _ | .para _ _ | .regionOpen _
      | .regionClose | .colOpen _ | .colNext | .colClose | .setLogo _
      | .floatOpen | .floatClose | .anchor _ | .slotOpen | .slotClose _
      | .anchorRule _ | .noInterline | .displayOpen _ _ _ => #[]

/-- One column of a row as placed: where its ink starts, its first baseline
when a picture opened it, and where the builder stood at its end. -/
private structure ColMark where
  lines : Nat
  fills : Nat
  inks : Nat
  /-- Whether the column produced a box or moved the cursor. -/
  contributes : Bool := false
  first : Option Sp := none
  y : Sp := 0
  depth : Sp := 0
  below : Sp := 0
  boxDepth : Sp := 0
  band : Spacing.Band := .text
  source : Option Span := none

/-- A column's end, its diagnostic provenance following
the column that supplies the painted lower bound. -/
private structure ColEnd where
  tail : Spacing.Tail
  source : Option Span

private def ColEnd.join (a b : ColEnd) : ColEnd :=
  { tail := a.tail.join b.tail
    source := if a.tail.y + a.tail.depth < b.tail.y + b.tail.depth
      then b.source else a.source }

/-- Both ordinary and aligned rows join only measured contributions. -/
private def ColEnd.remember (acc : Option ColEnd) (last : ColEnd)
    (contributes : Bool) : Option ColEnd :=
  if contributes then some ((acc.map (·.join last)).getD last) else acc

private theorem ColEnd.remember_empty_id (acc : Option ColEnd) (last : ColEnd) :
    ColEnd.remember acc last false = acc := rfl

private def Spacing.Page.colEnd (b : B) : ColEnd :=
  { tail := { y := b.y, depth := b.prevDepth, below := b.prevBelow,
              boxDepth := b.boxDepth, band := b.prevBand }
    source := b.lastSource }

/-- Placement state saved at a `colOpen`: where the columns
start, the lowest bottom so far, and the row's alignment. -/
private structure ColSave where
  y : Sp
  prevDepth : Sp
  prevBelow : Sp
  boxDepth : Sp
  prevBand : Spacing.Band
  skip : Glue
  fresh : Bool
  /-- The completed columns' joined end. -/
  bottom : Option ColEnd := none
  source : Option Span := none
  pos : Array Ir.BoxPos := #[]
  page : Nat := 0
  marks : Array ColMark := #[]

private def ColSave.opening (save : ColSave) : ColEnd :=
  { tail := { y := save.y, depth := save.prevDepth, below := save.prevBelow,
              boxDepth := save.boxDepth, band := save.prevBand }
    source := save.source }

/-- The placement walk's whole state, one structure so
a float group can be replayed through the same step. -/
private structure StepSt where
  b : B
  colSaves : Array ColSave := #[]
  /-- Open title slots: where each started and the first line, fill and ink it placed. -/
  slotSaves : Array (ColSave × Nat × Nat × Nat) := #[]
  logoSpans : Array (Nat × Array Ir.Inline) := #[]
  prose : Nat := 0

/-- Close the page before a heading whose lines and kept reserve cannot stand within the
page's shrink, in flow or a breakable frame, outside a float replay and off a fresh page. -/
private def Spacing.Page.keepHeading (b : B) (j : ParaJob) (n : Nat) : B :=
  if 0 < j.keepNext && b.frameBreak != some false && !b.noBreak &&
      !b.fresh &&
      noteFloor b.bottom b.noteGap b.notesH b.noteHang + b.pageShrink + b.skip.shrink
        < b.y + b.prevDepth + b.skip.width
          + (n : Int) * Ir.stepSkip j.lead j.size b.geom.leading
          + j.keepNext then
    b.spillPage
  else b

/-- The label lines and diagnostics of a picture's shape fold. -/
public structure PictureEmission where
  lines : Array LineOut := #[]
  diags : Array Diag := #[]

/-- One shape step: a label sets its line through `emitLabel`;
every other shape is ink in the picture's one `InkOut`. -/
public def emitPictureShape (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (out : PictureEmission) (shape : Ir.Pic.Shape)
    (origin : Option (Nat × Nat) := none) : PictureEmission :=
  match shape with
  | .ink _ => out
  | .label lx ly content color scale align =>
    let label := emitLabel fs imgs geom xHeight leaf place lx ly content color scale align
    let lines := match label.line? with
      | none => out.lines
      | some line =>
        let line := match origin with
          | none => line
          | some id => { line with pictureLabel := some {
              origin := id
              key := Ir.plainText content
              source := label.source
              above := line.y - (place.toPage label.reserved.2).2
              below := (place.toPage label.reserved.1).2 - line.y
              lineCount := label.lineCount } }
        out.lines.push line
    { out with lines := lines, diags := out.diags ++ label.diags }

/-- A picture's ink: its lowered figure (`Gfx.ofPictureKeyed`) placed by the
picture's isometry and stamped with its leaf; `none` for labels only. -/
public def pictureInk (box : Gfx.Box) (pic : Ir.Pic.Picture) (place : Ir.Pic.Place)
    (leaf : Option Nat) (origin : Nat) : Option InkOut :=
  if pic.shapes.all (· matches .label ..) then none
  else some { fig := Gfx.ofPictureKeyed origin box pic, place := place.toIso, leaf := leaf }

/-- The picture emitter in source-shape order. -/
public def emitPicture (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (pic : Ir.Pic.Picture) (origin : Option Nat := none) : PictureEmission :=
  match origin with
  | none => pic.shapes.foldl (fun out shape =>
      emitPictureShape fs imgs geom xHeight leaf place out shape) {}
  | some id =>
    (pic.shapes.foldl (fun (state : Nat × PictureEmission) shape =>
      (state.1 + 1, emitPictureShape fs imgs geom xHeight leaf place state.2 shape
        (some (id, state.1)))) (0, {})).2

/-- Fit and place one picture as a box of its height,
then every shape through one affine transform. -/
private def placePicture (fs : FontSet) (imgs : Image.Store) (b0 : B)
    (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat) : B :=
  -- The picture's bottom is a baseline (TikZ's default): the next line stands a leading below.
  let strut := b0.strutBelow fs
  let source := leaf.bind fun id => (b0.pictureSpans.find? (·.1 == id)).map (·.2)
  let box := pictureBox b0.geom fs imgs b0.xHeight pic
  let ((px0, py0), (_px1, py1)) := box
  let h := py1 - py0
  -- A declared baseline (`Ir.Pic.Picture.rise`) makes the part below it the line's depth.
  let rise := pic.rise (picMetric fs imgs b0.geom b0.xHeight)
  let lead := Ir.leadingFor b0.geom.fontSize b0.geom.leading
  let set (b : B) (yTop : Sp) (consume : Bool) (overflow : Sp) : B :=
    let above := if consume then b.pageShrink + b.skip.shrink else 0
    let stretch := if consume then b.pageStretch + b.skip.stretch else 0
    -- The consumed skip's fil counts as for a line, so the distribution moves the picture by it.
    let fils := b.pageFils + (if b.skip.fil then 1 else 0)
    let place : Ir.Pic.Place := { x0 := x, yTop := yTop, xmin := px0, ymax := py1 }
    let emitted := emitPicture fs imgs b.geom b.xHeight leaf place pic (some origin)
    let ink := pictureInk box pic place leaf origin
    -- Anchors pending above the picture land on its first line.
    let labelLines := emitted.lines.modify 0 fun l =>
      { l with anchors := b.pendingAnchors ++ l.anchors }
    let pending := if emitted.lines.isEmpty then b.pendingAnchors else #[]
    let b := ({ b with pageStretch := stretch
                       diags := b.diags ++ emitted.diags
                       pendingAnchors := pending }.pushSibling
      (inks := ink.toArray)
      (shrink := some above) (fils := some fils)).pushLabels labelLines above fils
    { b with
      openRegions := b.openRegions.map fun s => { s with begun := true }
      pageShrink := above
      pageFils := fils
      needed := max b.needed overflow
      neededSource := if b.needed < overflow then source else b.neededSource
      lastSource := source
      pendingSource := none
      y := yTop + h - rise
      prevDepth := rise
      prevBelow := max strut rise
      prevBand := .box
      skip := {}
      freshStart := false
      anchored := false
      ignoreDepth := false }
  -- On a fresh TeX page the picture stands by the first line's rule.
  b0.fitWith set (fun b _ _ => b)
    (fun b => match b.geom.topskip with
      | some _ => b.freshBaseline (h - rise) ⟨h - rise, rise, h - rise, rise⟩ lead - (h - rise)
      | none => b.geom.vmargin)
    (fun b => b.y + b.prevDepth + b.skip.width + inkClearance)
    (fun b => b.y + b.prevDepth + inkClearance) h b0.bottom false

/-- Close a title slot: its lines and fills move by `slotShift` as one
box measured by glyph ink, and the next slot starts where it did. -/
private def Spacing.Page.placeSlot (fs : FontSet) (b : B) (save : ColSave × Nat × Nat × Nat)
    (spec : SlotSpec) : B :=
  let (col, l0, f0, k0) := save
  let group := b.cur.lines.extract l0 b.cur.lines.size
  let restored := { b with y := col.y, prevDepth := col.prevDepth
                           prevBelow := col.prevBelow, prevBand := col.prevBand
                           lastInk := some (col.y, col.prevDepth, col.boxDepth)
                           lastSource := col.source
                           skip := col.skip, freshStart := col.fresh }
  match group[0]? with
  | none => restored
  | some first =>
    let extent (l : LineOut) := segsInk fs l.segs
    let top := group.foldl (fun m l => min m (l.y - (extent l).1))
      (first.y - (extent first).1)
    let bot := group.foldl (fun m l => max m (l.y + (extent l).2))
      (first.y + (extent first).2)
    let lo := group.foldl (fun m l => min m l.x) first.x
    let hi := group.foldl (fun m l => max m (l.x + l.setWidth)) (first.x + first.setWidth)
    let (left, w) := spec.box.getD (lo, hi - lo)
    let (dx, dy) := slotShift spec b.geom.pageW b.geom.pageH left w top (bot - top)
    let lines := b.cur.lines.mapIdx fun i l =>
      if i < l0 then l else { l with x := l.x + dx, y := l.y + dy }
    let fills := b.cur.fills.mapIdx fun i f =>
      if i < f0 then f else { f with x := f.x + dx, y := f.y + dy }
    let inks := b.cur.inks.mapIdx fun i k => if i < k0 then k else (k.shiftX dx).shiftY dy
    { restored with cur := { b.cur with lines := lines, fills := fills, inks := inks }
                    pinnedLines := lines.size, pinnedFills := fills.size, pinnedInks := inks.size }

private theorem placeSlot_keeps (fs : FontSet) (b : B) (save : ColSave × Nat × Nat × Nat)
    (spec : SlotSpec) :
    (b.placeSlot fs save spec).pages = b.pages ∧
    (b.placeSlot fs save spec).geom = b.geom ∧
    (b.placeSlot fs save spec).docBg = b.docBg ∧
    (b.placeSlot fs save spec).noBreak = b.noBreak := by
  obtain ⟨col, l0, f0, k0⟩ := save
  simp only [Spacing.Page.placeSlot]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Where the next column's ink starts: the page's arrays as they stand. -/
private def Spacing.Page.colMark (b : B) : ColMark :=
  { lines := b.cur.lines.size, fills := b.cur.fills.size, inks := b.cur.inks.size }

/-- A column ends where the builder stands; a zero-width strut still owns its height. -/
private def ColMark.finish (m : ColMark) (save : ColSave) (b : B) : ColMark :=
  { m with y := b.y, depth := b.prevDepth, below := b.prevBelow, band := b.prevBand
           boxDepth := b.boxDepth
           contributes := b.pages.size != save.page ||
             m.lines != b.cur.lines.size || m.fills != b.cur.fills.size ||
             m.inks != b.cur.inks.size || b.y != save.y ||
             b.prevDepth != save.prevDepth || b.prevBelow != save.prevBelow ||
             b.boxDepth != save.boxDepth
           source := b.lastSource }

private theorem ColMark.finish_unchanged (m : ColMark) (save : ColSave) (b : B)
    (hp : b.pages.size = save.page)
    (hl : m.lines = b.cur.lines.size) (hf : m.fills = b.cur.fills.size)
    (hs : m.inks = b.cur.inks.size) (hy : b.y = save.y)
    (hd : b.prevDepth = save.prevDepth) (hb : b.prevBelow = save.prevBelow)
    (hi : b.boxDepth = save.boxDepth) :
    (m.finish save b).contributes = false := by
  simp [ColMark.finish, hp, hl, hf, hs, hy, hd, hb, hi]

private def ColSave.finish (save : ColSave) (b : B) : ColSave :=
  let marks := save.marks.modify (save.marks.size - 1) (·.finish save b)
  { save with marks := marks
              bottom := ColEnd.remember save.bottom b.colEnd
                (marks.back?.any (·.contributes)) }

/-- A row stands its boxes on one baseline, each by the
reference point its `[pos]` names (latex.ltx `\@iiiparbox`). -/
private def Spacing.Page.alignRow (b : B) (save : ColSave) : B :=
  let refOf (k : Nat) (m : ColMark) : Sp :=
    if !m.contributes then save.y else
    let lineEnd := (save.marks[k + 1]?.map (·.lines)).getD b.cur.lines.size
    let firstLine := if m.lines < lineEnd then (b.cur.lines[m.lines]?.map (·.y)).getD m.y
      else m.y
    match save.pos[k]?.getD .top with
    | .top => save.y
    | .first => m.first.getD firstLine
    | .last => m.y
    | .center => (save.y + m.y + m.depth) / 2
  let refs := save.marks.mapIdx refOf
  let target := refs.foldl max save.y
  let dyAt (start : ColMark → Nat) (i : Nat) : Sp := Id.run do
    let mut d : Sp := 0
    for k in [0:save.marks.size] do
      if let some m := save.marks[k]? then
        if m.contributes && start m ≤ i then d := target - refs[k]!
    return d
  let lines := b.cur.lines.mapIdx fun i l => { l with y := l.y + dyAt (·.lines) i }
  let fills := b.cur.fills.mapIdx fun i f => { f with y := f.y + dyAt (·.fills) i }
  let inks := b.cur.inks.mapIdx fun i k => k.shiftY (dyAt (·.inks) i)
  let ending := (save.marks.zip refs).foldl
    (fun (acc : Option ColEnd) (m, r) =>
      let last : ColEnd := {
        tail := { y := m.y + (target - r), depth := m.depth, below := m.below,
                  boxDepth := m.boxDepth, band := m.band }
        source := m.source }
      ColEnd.remember acc last m.contributes) none
  let contributed := ending.isSome
  let ending := ending.getD save.opening
  let tail := ending.tail
  { b with cur := { b.cur with lines := lines, fills := fills, inks := inks }
           y := tail.y, prevDepth := tail.depth, prevBelow := tail.below, prevBand := tail.band
           lastSource := ending.source, lastInk := some (tail.y, tail.depth, tail.boxDepth)
           skip := if contributed then {} else save.skip
           freshStart := if contributed then false else save.fresh
           needed := max b.needed (tail.y + tail.depth - b.geom.bodyBottom)
           neededSource := if b.needed < tail.y + tail.depth - b.geom.bodyBottom then ending.source
             else b.neededSource }

private theorem alignRow_shipped_id (b : B) (save : ColSave) :
    (b.alignRow save).pages = b.pages ∧ (b.alignRow save).geom = b.geom ∧
    (b.alignRow save).docBg = b.docBg ∧ (b.alignRow save).noBreak = b.noBreak := by
  simp [Spacing.Page.alignRow]

/-- Place `Op.boxAnchor` where its rule puts it below the band above, then the shift. -/
private def Spacing.Page.placeAnchor (fs : FontSet) (b : B) (rule : AnchorRule)
    (shift : Sp) (paints : Bool) : B :=
  let bs (b : B) : Sp := Ir.leadingFor b.geom.fontSize b.geom.leading
  let rise (b : B) : Sp := match rule with
    | .tex h => texBoxTop (bs b) b.boxDepth h
    | .flush => b.boxDepth
    | .balanced s => max b.boxDepth (bs b * 3 / 10) + max 0 (s - b.skip.width)
  let mk (y : Sp) : LineOut :=
    { x := b.geom.hmargin, y := y, size := 0, segs := #[], setWidth := 0
      regionExtent := some (0, 0) }
  if paints then
    (b.fitCommit mk (fun b => b.geom.bodyTop + b.topKept)
      (fun b => b.y + b.skip.width + rise b + shift) (fun b => b.y + rise b + shift)
      0 (b.strutBelow fs) false 0 b.bottom).keepInk 0
  else b.anchorAt fs (b.y + rise b + shift)

/-- Close a region; a painted box is TeX's box of depth zero, keeping the glue its list ends on. -/
private def Spacing.Page.closeRegion (fs : FontSet) (b : B) : B :=
  let closing := b.openRegions.back?.map fun start =>
    let span := start.close b.cur b.skip.width b.y
    let empty := span.lineStart == span.lineEnd && span.fillStart == span.fillEnd &&
      span.inkStart == span.inkEnd
    let regions := if empty then b.closedRegions else b.closedRegions.push span
    let children := regionFills regions b.cur.lines b.cur.fills b.cur.inks
    -- A rule beside a box spaces nothing; a painted box's bottom does.
    let bottom := if span.kind matches .edge .. then none
      else (span.fill b.cur.lines b.cur.fills b.cur.inks children).map (fun f => f.y + f.h)
    (regions, bottom)
  let closed := { b with
    openRegions := b.openRegions.pop
    closedRegions := (closing.map (·.1)).getD b.closedRegions }
  match closing.bind (·.2) with
  | some edge => { closed.anchorAt fs edge with skip := {} }
  | none => closed

/-- Place one op; `floatOpen` and `floatClose` are inert
here, the driver consuming the outermost pair (`runFloat`). -/
private def stepStaged (fs : FontSet) (imgs : Image.Store) (st : StepSt)
    (s : Op) : StepSt := Id.run do
  let mut b := st.b
  let mut colSaves := st.colSaves
  let mut slotSaves := st.slotSaves
  let mut logoSpans := st.logoSpans
  let mut prose := st.prose
  match s with
  | .floatOpen | .floatClose => pure ()
  | .regionOpen kind =>
    -- An anchored box owes no inset above its opening fragment.
    let start : RegionStart :=
      { kind := kind, depth := b.openRegions.size
        hidden := kind matches .hidden || b.openRegions.any (·.hidden)
        begun := kind matches .surface _ _ _ _ true
        lines := b.cur.lines.size,
        fills := b.cur.fills.size, inks := b.cur.inks.size }
    b := { b with openRegions := b.openRegions.push start }
  | .regionClose => b := b.closeRegion fs
  | .setLogo c =>
    -- The page being built and everything after carry this content; a later span overrides.
    logoSpans := logoSpans.push (b.pages.size, c)
  | .skip g =>
    -- An empty page discards glue, as TeX's page builder does, until an anchor stands.
    unless b.fresh && !(b.anchored || b.skip.fil || g.fil) do
      b := { b with skip := b.skip.add g }
  | .anchorRule g =>
    -- `\vspace*`'s zero rule is a page's first item, below `\topskip`; mid-page it holds nothing.
    if b.fresh then b := { b with anchored := true, skip := g }
  | .noInterline => b := { b with ignoreDepth := true }
  | .displayOpen dj left size =>
    -- TeX's skip above, over the empty line `$$` sets where the display opens a paragraph.
    let b1 := b.displaySkip dj left size
    let empty := if dj.emptyLine then
        texBaselineGap (Ir.leadingFor size b1.geom.leading) b1.boxDepth 0 - b1.prevDepth
      else 0
    b := { b1 with skip := { b1.skip with width := b1.skip.width + empty },
                   texAfter := true, lineEnd := none }
  | .skipAlt long short =>
    let g := if b.dispShort then short else long
    unless b.fresh && !(b.skip.fil || g.fil) do
      b := { b with skip := b.skip.add g }
  | .bodyOpen g box => b := b.openBody fs g box
  | .anchor sl => b := { b with pendingAnchors := b.pendingAnchors.push sl }
  | .brk =>
    -- A boundary closes only a page that holds something, so adjacent frames share one.
    if !b.cur.blank then
      b := { b.finishPage b.closingOwed with
               chrome := none, frameBreak := none, frameSource := none, spillWarned := false,
               curFit := .spill }
    else
      b := { b with pageBg := none, vdist := .top, pageFils := 0, filsAbove := #[],
                    pinnedLines := 0, pinnedFills := 0, pinnedInks := 0, chrome := none,
                    openRegions := b.openRegions.map RegionStart.nextPage, closedRegions := #[],
                    frameBreak := none, frameSource := none, spillWarned := false, opened := false,
                    curFit := .spill,
                    freshStart := false }
  | .frameOpen br source opening =>
    b := { b with frameBreak := some br, frameSource := source, spillWarned := false,
                  curFit := opening.fit,
                  curFrame := opening.number, curFrameLabel := opening.label
                  curFrameOrigin := opening.origin
                  curFoot := opening.footer, curFootLook := some opening.look
                  footBox := opening.footer.map
                    (bandBox fs imgs b.geom b.xHeight (b.pages.size + 1))
                  frameArea := opening.area }
  | .frameClose =>
    b := { b with curFrame := none, curFrameLabel := none, curFrameOrigin := none,
                  curFoot := none, footBox := none, curFootLook := none,
                  frameArea := .margins }
  | .pageOpening opening => b := { b with pageState := b.pageState.applyOpening opening }
  | .pageStyle bg d => b := { b with pageBg := bg, vdist := d }
  | .pageGround bg => b := { b with docBg := bg, pageBg := none }
  | .pin =>
    -- The resume depth clears the chrome: a spill page's first line spaces off the bar.
    let barBottom := (b.cur.fills.back?.map fun f => f.y + f.h).getD 0
    let (depth, below) := reserveBelow b.prevDepth b.prevBelow (barBottom - b.y)
    b := { b with
      pinnedLines := b.cur.lines.size
      pinnedFills := b.cur.fills.size
      pinnedInks := b.cur.inks.size
      chrome := some {
        lines := b.cur.lines
        fills := b.cur.fills
        y := b.y
        depth := depth
        below := below
        band := .rule
        header := b.curBand } }
  | .colOpen pos =>
    -- On a fresh page the columns' bottom starts at the body top, not the last page's line.
    let fresh := b.fresh
    -- Below an anchor the row is TeX's first box (`Spacing.Page.colAnchor`).
    if fresh && (b.anchored || b.skip.fil) && b.colAnchor.isNone then
      b := { b with colAnchor := some (if b.ignoreDepth then 0 else inkClearance) }
    colSaves := colSaves.push {
      y := b.y, prevDepth := b.prevDepth, prevBelow := b.prevBelow
      boxDepth := b.boxDepth
      prevBand := b.prevBand, skip := b.skip
      fresh := fresh
      source := b.lastSource
      pos := pos, page := b.pages.size, marks := #[b.colMark] }
  | .colNext =>
    if let some save := colSaves.back? then
      let save := save.finish b
      colSaves := colSaves.pop.push { save with
        marks := save.marks.push b.colMark }
      b := { b with y := save.y, prevDepth := save.prevDepth
                    prevBelow := save.prevBelow, prevBand := save.prevBand
                    lastSource := save.source
                    lastInk := some (save.y, save.prevDepth, save.boxDepth)
                    skip := save.skip
                    freshStart := save.fresh }
  | .colClose =>
    if let some save := colSaves.back? then
      colSaves := colSaves.pop
      if colSaves.isEmpty then b := { b with colAnchor := none }
      let save := save.finish b
      if save.pos.any (· != .top) && save.marks.size == save.pos.size &&
          b.pages.size == save.page then
        b := b.alignRow save
      else
        let ending := save.bottom.getD save.opening
        b := { b with y := ending.tail.y, prevDepth := ending.tail.depth
                      prevBelow := ending.tail.below, prevBand := ending.tail.band
                      lastSource := ending.source
                      lastInk := some (ending.tail.y, ending.tail.depth, ending.tail.boxDepth)
                      skip := if save.bottom.isSome then {} else save.skip
                      freshStart := if save.bottom.isSome then false else save.fresh }
  | .titleBar color pad strut =>
    -- The bar behind the title, page top to `pad` below its depth; with a strut, moloch's box.
    b := match b.cur.lines.back?, b.cur.lines[0]? with
      | some l, some first =>
        match strut with
        | none =>
          let h := l.y + b.prevDepth + pad
          { b.pushSibling (fills := #[{ x := 0, y := 0, w := b.geom.pageW,
                                        h := h, color := color }]) with
            curBand := some (max h (b.curBand.getD 0)) }
        | some s =>
          let delta := pad + s - first.y
          let h := frameBarHeight pad (l.y + delta) b.prevDepth
          let b := { b with cur := { b.cur with lines := b.cur.lines.map fun (l : LineOut) =>
                                       { l with y := l.y + delta } }
                            y := b.y + delta }
          { b.pushSibling (fills := #[{ x := 0, y := 0, w := b.geom.pageW,
                                        h := h, color := color }]) with
            curBand := some (max h (b.curBand.getD 0)) }
      | _, _ => b
  | .boxAnchor rule shift paints => b := b.placeAnchor fs rule shift paints
  | .hrule color th =>
    -- A rule line takes the full line machinery, so it spaces, breaks and distributes as text does.
    b := b.placeLine fs b.geom.hmargin 0 #[.rule b.geom.textWidth th 0 color]
      b.geom.textWidth
  | .tableRule th x w segs =>
    -- Exactly the pending sep below the previous ink, with zero depth, as after TeX's `\hrule`.
    let mk (y : Sp) : LineOut :=
      { x := x, y := y, size := 0, segs := segs, setWidth := w, regionExtent := some (th, 0) }
    b := b.fitCommit mk
      (fun b => b.geom.vmargin + th)
      (fun b => b.y + b.prevDepth + b.skip.width + th)
      (fun b => b.y + b.prevDepth + th)
      0 0 true 0 b.bottom
  | .progress num den fg bg thick x w =>
    -- Half a line under the last baseline: the track, then the elapsed share over it.
    let gap := b.geom.fontSize / 2
    let y := b.y + b.prevDepth + gap
    let track : Fill := { x := x, y := y, w := w, h := thick, color := bg }
    let fills := if num == 0 then #[track] else
      #[track, { x := x, y := y, w := w * (num : Int) / (den : Int), h := thick,
                 color := fg }]
    b := { b.pushSibling (fills := fills) with
                  prevDepth := b.prevDepth + gap + thick
                  prevBelow := b.prevBelow + gap + thick
                  prevBand := .box }
  | .para j t =>
    let breaks := t.get
    -- A plain full-measure text paragraph is the continuous reading the measure band judges.
    if j.target == b.geom.textWidth && !j.center && j.size == b.geom.fontSize &&
        j.markerSegs.isNone && j.rule.isNone then
      prose := max prose breaks.size
    b := placePara fs (b.keepHeading j breaks.size) j breaks
  | .picture x pic leaf origin =>
    let before := b.cur.lines.size
    b := placePicture fs imgs b x pic leaf origin
    -- A picture that opens a column is the column's first baseline; its label lines are not.
    if let some save := colSaves.back? then
      if let some m := save.marks.back? then
        if m.first.isNone && m.lines == before then
          colSaves := colSaves.pop.push
            { save with marks := save.marks.pop.push { m with first := some b.y } }
  | .slotOpen =>
    slotSaves := slotSaves.push ({
      y := b.y, prevDepth := b.prevDepth, prevBelow := b.prevBelow
      boxDepth := b.boxDepth
      prevBand := b.prevBand, skip := b.skip
      fresh := b.fresh, source := b.lastSource }, b.cur.lines.size, b.cur.fills.size,
      b.cur.inks.size)
  | .slotClose spec =>
    if let some save := slotSaves.back? then
      slotSaves := slotSaves.pop
      b := b.placeSlot fs save spec
  return { b := b, colSaves := colSaves, slotSaves := slotSaves, logoSpans := logoSpans,
           prose := prose }

private theorem stepStaged_hrule_b (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (color : Ir.Color) (th : Sp) :
    (stepStaged fs imgs st (.hrule color th)).b =
      st.b.placeLine fs st.b.geom.hmargin 0
        #[.rule st.b.geom.textWidth th 0 color] st.b.geom.textWidth := rfl

private theorem stepStaged_regionClose_b (fs : FontSet) (imgs : Image.Store) (st : StepSt) :
    (stepStaged fs imgs st .regionClose).b = st.b.closeRegion fs := rfl

private theorem stepStaged_boxAnchor_b (fs : FontSet) (imgs : Image.Store) (st : StepSt)
    (h : AnchorRule) (shift : Sp) (paints : Bool) :
    (stepStaged fs imgs st (.boxAnchor h shift paints)).b = st.b.placeAnchor fs h shift paints :=
  rfl

private theorem closeRegion_shipped_id (fs : FontSet) (b : B) :
    (b.closeRegion fs).pages = b.pages ∧ (b.closeRegion fs).noBreak = b.noBreak ∧
      (b.closeRegion fs).geom = b.geom ∧ (b.closeRegion fs).docBg = b.docBg ∧
      ((b.closeRegion fs).curFrameOrigin, (b.closeRegion fs).curFrame,
        (b.closeRegion fs).curFoot) = (b.curFrameOrigin, b.curFrame, b.curFoot) ∧
      (b.closeRegion fs).paragraphBreaks = b.paragraphBreaks ∧
      (b.closeRegion fs).diags = b.diags := by
  simp only [Spacing.Page.closeRegion]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem stepStaged_tableRule_b (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (th x w : Sp) (segs : Array Seg) :
    (stepStaged fs imgs st (.tableRule th x w segs)).b =
      st.b.fitCommit
        (fun y =>
          { x := x, y := y, size := 0, segs := segs, setWidth := w
            regionExtent := some (th, 0) })
        (fun b => b.geom.vmargin + th)
        (fun b => b.y + b.prevDepth + b.skip.width + th)
        (fun b => b.y + b.prevDepth + th) 0 0 true 0 st.b.bottom := rfl

private theorem stepStaged_para_b (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (j : ParaJob) (task : Task (Array Nat)) :
    (stepStaged fs imgs st (.para j task)).b =
      placePara fs (st.b.keepHeading j task.get.size) j task.get := by
  simp only [stepStaged, Id.run, Id, pure]
  split <;> rfl

private theorem stepStaged_picture_b (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat) :
    (stepStaged fs imgs st (.picture x pic leaf origin)).b =
      placePicture fs imgs st.b x pic leaf origin := by
  simp only [stepStaged, Id.run, Id, pure]
  repeat' split
  all_goals rfl

private theorem pageOpening_step_projects (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (opening : Ir.PageOpening) :
    (stepStaged fs imgs st (.pageOpening opening)).b.pageState =
      st.b.pageState.applyOpening opening ∧
    (stepStaged fs imgs st (.pageOpening opening)).b.pages = st.b.pages := by
  exact ⟨rfl, rfl⟩

private theorem frameOpen_step_projects (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (br : Bool) (source : Option Span)
    (opening : FrameOpening) :
    let next := (stepStaged fs imgs st (.frameOpen br source opening)).b
    next.curFrameOrigin = opening.origin ∧ next.curFrame = opening.number ∧
      next.frameSource = source ∧ next.pages = st.b.pages :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem frameOpen_footer_projects (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (br : Bool) (source : Option Span) (opening : FrameOpening) :
    let next := (stepStaged fs imgs st (.frameOpen br source opening)).b
    next.curFoot = opening.footer ∧ next.curFrameOrigin = opening.origin ∧
      next.curFrame = opening.number ∧
      next.footBox = opening.footer.map
        (bandBox fs imgs st.b.geom st.b.xHeight (st.b.pages.size + 1)) :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem break_frame_projects (fs : FontSet) (imgs : Image.Store) (st : StepSt) :
    let next := (stepStaged fs imgs st .brk).b
    next.curFrameOrigin = st.b.curFrameOrigin ∧
      next.curFrame = st.b.curFrame ∧ next.curFoot = st.b.curFoot := by
  simp only [stepStaged, Id.run, pure]
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem frameClose_step_projects (fs : FontSet) (imgs : Image.Store) (st : StepSt) :
    let next := (stepStaged fs imgs st .frameClose).b
    next.curFrameOrigin = none ∧ next.curFrame = none ∧ next.curFoot = none ∧
      next.pages = st.b.pages :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem emptyBreak_pageState (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (hb : st.b.cur.blank = true) :
    (stepStaged fs imgs st .brk).b.pageState = st.b.pageState := by
  simp [stepStaged, hb]

private theorem brk_ships_exact (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (hb : st.b.cur.blank = false) :
    (stepStaged fs imgs st .brk).b.pages.size = st.b.pages.size + 1 ∧
      ((stepStaged fs imgs st .brk).b.pages.back?.map (·.inks.size)) = some st.b.cur.inks.size := by
  constructor
  · simp [stepStaged, hb, Spacing.Page.finishPage]
  · simp [stepStaged, hb, Spacing.Page.finishPage]
    split <;> simp

/-- Place a float group whole: tried where it stands, else replayed on a fresh page
under `noBreak`; a group taller than the text block ships alone, named (W0358). -/
private def runFloat (fs : FontSet) (imgs : Image.Store) (st : StepSt)
    (group : Array Op) : StepSt :=
  let attempt := group.foldl (stepStaged fs imgs) st
  if attempt.b.pages.size == st.b.pages.size then attempt
  else
    -- Close the page and give the group the next one whole; the pending glue dies with it.
    let b := if st.b.cur.blank then st.b
      else st.b.finishPage
    let st2 := group.foldl (stepStaged fs imgs)
      { st with b := { b with noBreak := true } }
    let b2 := st2.b
    let overrun := b2.y + b2.prevDepth - noteFloor b2.bottom b2.noteGap b2.notesH b2.noteHang
    let b2 := if overrun > b2.pageShrink then
        { b2 with diags := b2.diags.push (Diag.of .W0358
          "a figure or table is taller than the text block; it overruns its page"
          (help := "shrink the float's content, or raise the text height \
(\\page{ vmargin = ... })")
          (detail := some s!"{(overrun - b2.pageShrink).toPtString}pt taller")) }
      else b2
    { st2 with b := { b2 with noBreak := false } }

/-- The shipped pages only grow from `b` to `b'`. -/
private def PagesExtend (b b' : B) : Prop := ∃ s, b'.pages = b.pages ++ s

private theorem pagesExtend_refl (b : B) : PagesExtend b b :=
  ⟨#[], by simp⟩

private theorem pagesExtend_of_eq {b c : B} (h : c.pages = b.pages) :
    PagesExtend b c := ⟨#[], by simp [h]⟩

private theorem pagesExtend_trans {a b c : B} :
    PagesExtend a b → PagesExtend b c → PagesExtend a c
  | ⟨s1, h1⟩, ⟨s2, h2⟩ => ⟨s1 ++ s2, by rw [h2, h1, Array.append_assoc]⟩

private theorem pagesExtend_congr {b b' c : B} (h : c.pages = b'.pages)
    (he : PagesExtend b b') : PagesExtend b c :=
  he.imp fun _ hs => h ▸ hs

@[simp] private theorem commit_pages (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) :
    (b.commit l d bl r c o).pages = b.pages := rfl
@[simp] private theorem commit_noBreak (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) :
    (b.commit l d bl r c o).noBreak = b.noBreak := rfl
@[simp] private theorem warnOverfull_pages (b : B) (source : Option Span) :
    (b.warnOverfull source).pages = b.pages := rfl
@[simp] private theorem warnOverfull_noBreak (b : B) (source : Option Span) :
    (b.warnOverfull source).noBreak = b.noBreak := rfl
@[simp] private theorem pushSibling_pages (b : B) (l? : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp)
    (fl : Option Nat) :
    (b.pushSibling l? fills inks shrink fl).pages = b.pages := by
  cases l? <;> simp only [Spacing.Page.pushSibling] <;> split <;> rfl
@[simp] private theorem pushSibling_noBreak (b : B) (l? : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp)
    (fl : Option Nat) :
    (b.pushSibling l? fills inks shrink fl).noBreak = b.noBreak := by
  cases l? <;> simp only [Spacing.Page.pushSibling] <;> split <;> rfl
@[simp] private theorem pushLabels_pages (b : B) (ls : Array LineOut) (sh : Sp) (fl : Nat) :
    (b.pushLabels ls sh fl).pages = b.pages := by
  unfold Spacing.Page.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.pages = b.pages)
    rfl (fun _ acc h => by rw [pushSibling_pages]; exact h)
@[simp] private theorem pushLabels_noBreak (b : B) (ls : Array LineOut) (sh : Sp) (fl : Nat) :
    (b.pushLabels ls sh fl).noBreak = b.noBreak := by
  unfold Spacing.Page.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.noBreak = b.noBreak)
    rfl (fun _ acc h => by rw [pushSibling_noBreak]; exact h)

@[simp] private theorem commit_geom (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) : (b.commit l d bl r c o).geom = b.geom := rfl
@[simp] private theorem commit_docBg (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) : (b.commit l d bl r c o).docBg = b.docBg := rfl
@[simp] private theorem pushSibling_geom (b : B) (l? : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp)
    (fl : Option Nat) :
    (b.pushSibling l? fills inks shrink fl).geom = b.geom := by
  cases l? <;> simp only [Spacing.Page.pushSibling] <;> split <;> rfl
@[simp] private theorem pushSibling_docBg (b : B) (l? : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp)
    (fl : Option Nat) :
    (b.pushSibling l? fills inks shrink fl).docBg = b.docBg := by
  cases l? <;> simp only [Spacing.Page.pushSibling] <;> split <;> rfl
@[simp] private theorem pushLabels_geom (b : B) (ls : Array LineOut) (sh : Sp) (fl : Nat) :
    (b.pushLabels ls sh fl).geom = b.geom := by
  unfold Spacing.Page.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.geom = b.geom)
    rfl (fun _ acc h => by rw [pushSibling_geom]; exact h)
@[simp] private theorem pushLabels_docBg (b : B) (ls : Array LineOut) (sh : Sp) (fl : Nat) :
    (b.pushLabels ls sh fl).docBg = b.docBg := by
  unfold Spacing.Page.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.docBg = b.docBg)
    rfl (fun _ acc h => by rw [pushSibling_docBg]; exact h)
@[simp] private theorem attachNotes_geom (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).geom = b.geom := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.geom = b.geom)
      rfl (fun _ _ h => h)
@[simp] private theorem attachNotes_docBg (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).docBg = b.docBg := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.docBg = b.docBg)
      rfl (fun _ _ h => h)
@[simp] private theorem warnNoteOverrun_geom (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).geom = b.geom := by
  simp only [Spacing.Page.warnNoteOverrun]; split <;> rfl
@[simp] private theorem warnNoteOverrun_docBg (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).docBg = b.docBg := by
  simp only [Spacing.Page.warnNoteOverrun]; split <;> rfl
@[simp] private theorem warnOverfull_geom (b : B) (source : Option Span) :
    (b.warnOverfull source).geom = b.geom := rfl
@[simp] private theorem warnOverfull_docBg (b : B) (source : Option Span) :
    (b.warnOverfull source).docBg = b.docBg := rfl
@[simp] private theorem finishPage_geom (b : B) (o : Sp) (f : Bool) :
    (b.finishPage o f).geom = b.geom := rfl
@[simp] private theorem finishPage_docBg (b : B) (o : Sp) (f : Bool) :
    (b.finishPage o f).docBg = b.docBg := rfl
@[simp] private theorem reopenChrome_geom (b : B) : b.reopenChrome.geom = b.geom := by
  unfold Spacing.Page.reopenChrome; split <;> rfl
@[simp] private theorem reopenChrome_docBg (b : B) :
    b.reopenChrome.docBg = b.docBg := by
  unfold Spacing.Page.reopenChrome; split <;> rfl
@[simp] private theorem spillPage_geom (b : B) (o : Sp) : (b.spillPage o).geom = b.geom := by
  simp [Spacing.Page.spillPage]
@[simp] private theorem spillPage_docBg (b : B) (o : Sp) :
    (b.spillPage o).docBg = b.docBg := by
  simp [Spacing.Page.spillPage]
@[simp] private theorem placeParaTrailer_geom (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).geom = b.geom := by
  simp only [placeParaTrailer, reachDepth]
  repeat' split
  all_goals first | rfl | simp
@[simp] private theorem placeParaTrailer_docBg (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).docBg = b.docBg := by
  simp only [placeParaTrailer, reachDepth]
  repeat' split
  all_goals first | rfl | simp

private theorem finishPage_extends (b : B) {o : Sp} {f : Bool} :
    PagesExtend b (b.finishPage o f) :=
  ⟨#[_], rfl⟩

private theorem fitWith_extends (b : B) (place : B → Sp → Bool → Sp → B)
    (settle : B → Sp → Sp → B) (firstY stepY retryY : B → Sp) (inkBelow bottom : Sp)
    (holdsBlank : Bool) (hp : ∀ b y c o, (place b y c o).pages = b.pages)
    (hs : ∀ b y d, (settle b y d).pages = b.pages) :
    PagesExtend b (b.fitWith place settle firstY stepY retryY inkBelow bottom holdsBlank) := by
  simp only [Spacing.Page.fitWith]
  repeat' split
  all_goals first
    | (refine pagesExtend_of_eq ?_; simp [hp, hs]; done)
    | (refine pagesExtend_trans (finishPage_extends b (o := 0) (f := b.flushes)) (pagesExtend_of_eq ?_);
       simp [hp, hs]; done)

private theorem fitCommit_extends (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) :
    PagesExtend b
      (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns) :=
  fitWith_extends b _ _ firstY stepY retryY inkBelow bottom true (fun _ _ _ _ => by simp)
    fun _ _ _ => by simp

private theorem placeAnchor_extends (fs : FontSet) (b : B) (h : AnchorRule) (shift : Sp)
    (paints : Bool) : PagesExtend b (b.placeAnchor fs h shift paints) := by
  simp only [Spacing.Page.placeAnchor]
  split
  · simp only [PagesExtend, keepInk_pages]
    exact fitCommit_extends ..
  · exact pagesExtend_of_eq rfl

private theorem fitWith_noBreak (b : B) (place : B → Sp → Bool → Sp → B)
    (settle : B → Sp → Sp → B) (firstY stepY retryY : B → Sp) (inkBelow bottom : Sp)
    (holdsBlank : Bool)
    (hp : ∀ b y c o, (place b y c o).pages = b.pages ∧ (place b y c o).noBreak = b.noBreak)
    (hs : ∀ b y d, (settle b y d).pages = b.pages ∧ (settle b y d).noBreak = b.noBreak)
    (h : b.noBreak = true) :
    (b.fitWith place settle firstY stepY retryY inkBelow bottom holdsBlank).pages = b.pages ∧
      (b.fitWith place settle firstY stepY retryY inkBelow bottom holdsBlank).noBreak = true := by
  simp only [Spacing.Page.fitWith]
  repeat' split
  all_goals first
    | (simp [hp, hs, h]; done)
    | (exfalso; exact ‹¬(_ ∨ _ = true ∨ _)› (Or.inr (Or.inl h)))

private theorem fitCommit_noBreak (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) (h : b.noBreak = true) :
    (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns).pages = b.pages ∧
    (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns).noBreak = true :=
  fitWith_noBreak b _ _ firstY stepY retryY inkBelow bottom true (fun _ _ _ _ => by simp)
    (fun _ _ _ => by simp) h

private theorem fitCommit_note_with_mark (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock)
    (nb : NoteBlock) (hnb : nb ∈ ns) (l : LineOut) (hl : l ∈ nb.lines) :
    ∃ l' ∈ (b.fitCommit mk firstY stepY retryY depth below rl inkBelow
        bottom ns).pendingNotes,
      l'.segs = l.segs := by
  simp only [Spacing.Page.fitCommit, Spacing.Page.fitWith]
  repeat' split
  all_goals
    first
    | (rw [warnNoteOverrun_pendingNotes]
       exact attachNotes_mem _ ns nb hnb l hl)
    | exact attachNotes_mem _ ns nb hnb l hl
    | (rw [noteOverrun_pendingNotes, warnNoteOverrun_pendingNotes]
       exact attachNotes_mem _ ns nb hnb l hl)
    | (rw [noteOverrun_pendingNotes]
       exact attachNotes_mem _ ns nb hnb l hl)

private theorem placePicture_extends (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat) :
    PagesExtend b (placePicture fs imgs b x pic leaf origin) := by
  simp only [placePicture]
  exact fitWith_extends b _ _ _ _ _ _ _ _ (fun _ _ _ _ => by simp) fun _ _ _ => rfl

private theorem placePicture_noBreak (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat)
    (h : b.noBreak = true) :
    (placePicture fs imgs b x pic leaf origin).pages = b.pages ∧
      (placePicture fs imgs b x pic leaf origin).noBreak = true := by
  simp only [placePicture]
  exact fitWith_noBreak b _ _ _ _ _ _ _ _ (fun _ _ _ _ => by simp) (fun _ _ _ => ⟨rfl, rfl⟩) h

private theorem placeLine_extends (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (anchors : Array String) (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp) :
    PagesExtend b
      (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
        step rs strut) := by
  simp only [Spacing.Page.placeLine, PagesExtend, displayState_pages, keepInk_pages]
  exact fitCommit_extends ..

private theorem placeLine_pages_noBreak (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (anchors : Array String) (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp)
    (h : b.noBreak = true) :
    (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
      step rs strut).pages = b.pages := by
  simp only [Spacing.Page.placeLine, displayState_pages, keepInk_pages]
  exact (fitCommit_noBreak (h := h) ..).1

private theorem placeLine_keeps_noBreak (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (anchors : Array String) (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp)
    (h : b.noBreak = true) :
    (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
      step rs strut).noBreak = true := by
  simp only [Spacing.Page.placeLine, displayState_noBreak, keepInk_noBreak]
  exact (fitCommit_noBreak (h := h) ..).2

private theorem placeLine_note_with_mark (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (nb : NoteBlock) (hnb : nb ∈ ns)
    (l : LineOut) (hl : l ∈ nb.lines) (step : Option Sp := none) :
    ∃ l' ∈ (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op
        (stepLead := step)).pendingNotes,
      l'.segs = l.segs := by
  simp only [Spacing.Page.placeLine, displayState_pendingNotes, keepInk_pendingNotes]
  exact fitCommit_note_with_mark (hnb := hnb) (hl := hl) ..

private theorem placeLine_extends' (fs : FontSet) (b0 b1 : B)
    (hp : b1.pages = b0.pages) (x size : Sp) (segs : Array Seg) (w hang : Sp)
    (ex : Int) (ns : Array NoteBlock) (c : Bool) (lf : Option Nat)
    (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool) (anchors : Array String)
    (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp) :
    PagesExtend b0
      (b1.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
        step rs strut) :=
  pagesExtend_trans (pagesExtend_of_eq hp) (placeLine_extends ..)

private theorem placeParaLine_extends (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) :
    PagesExtend st.1 (placeParaLine fs j st brk).1 := by
  simp only [placeParaLine, Spacing.Page.withPendingSource]
  exact pagesExtend_congr (placeParaTrailer_pages ..)
    (placeLine_extends' fs st.1 _ (by split <;> simp) ..)

private theorem placeParaLine_noBreak (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) (h : st.1.noBreak = true) :
    (placeParaLine fs j st brk).1.pages = st.1.pages ∧
    (placeParaLine fs j st brk).1.noBreak = true := by
  simp only [placeParaLine, Spacing.Page.withPendingSource]
  constructor
  · rw [placeParaTrailer_pages]
    split <;> rw [placeLine_pages_noBreak] <;> simp [h]
  · rw [placeParaTrailer_noBreak]
    split <;> rw [placeLine_keeps_noBreak] <;> simp [h]

private theorem placePara_extends (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) : PagesExtend b (placePara fs b j breaks) := by
  unfold placePara
  exact Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) => PagesExtend b acc.1)
    (pagesExtend_of_eq (by simp))
    (fun _ acc hacc => pagesExtend_trans hacc (placeParaLine_extends ..))

private theorem placePara_noBreak (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) (h : b.noBreak = true) :
    (placePara fs b j breaks).pages = b.pages ∧
    (placePara fs b j breaks).noBreak = true := by
  unfold placePara
  exact Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) =>
      acc.1.pages = b.pages ∧ acc.1.noBreak = true)
    ⟨by simp, by simp [h]⟩
    (fun _ acc hacc =>
      have step := placeParaLine_noBreak fs (placedJob fs b j breaks) acc _ hacc.2
      ⟨step.1.trans hacc.1, step.2⟩)

private theorem keepHeading_extends (b : B) (j : ParaJob) (n : Nat) :
    PagesExtend b (b.keepHeading j n) := by
  unfold Spacing.Page.keepHeading
  split
  · obtain ⟨s, hs⟩ := finishPage_extends b (o := 0) (f := b.flushes)
    exact ⟨s, by rw [spillPage_pages]; exact hs⟩
  · exact pagesExtend_refl b

private theorem keepHeading_noBreak (b : B) (j : ParaJob) (n : Nat) (h : b.noBreak = true) :
    b.keepHeading j n = b := by
  unfold Spacing.Page.keepHeading
  simp [h]

private theorem stepStaged_extends (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (s : Op) : PagesExtend st.b (stepStaged fs imgs st s).b := by
  cases s
  case skipAlt long short =>
    simp only [stepStaged, Id.run, Id, pure]
    repeat' split
    all_goals (refine pagesExtend_of_eq ?_; simp; done)
  case regionOpen target =>
    refine pagesExtend_of_eq ?_
    simp [stepStaged]
  case regionClose =>
    rw [stepStaged_regionClose_b]
    exact pagesExtend_of_eq (closeRegion_shipped_id fs st.b).1
  case boxAnchor h shift paints =>
    rw [stepStaged_boxAnchor_b]
    exact placeAnchor_extends ..
  case hrule color th =>
    rw [stepStaged_hrule_b]
    exact placeLine_extends ..
  case tableRule th x w segs =>
    rw [stepStaged_tableRule_b]
    exact fitCommit_extends ..
  case para j task =>
    rw [stepStaged_para_b]
    exact pagesExtend_trans (keepHeading_extends ..) (placePara_extends ..)
  case picture x pic leaf origin =>
    rw [stepStaged_picture_b]
    exact placePicture_extends ..
  all_goals (simp only [stepStaged, Id.run, Id, pure, Spacing.Page.openBody] <;> repeat' split)
  all_goals first
    | (refine pagesExtend_of_eq ?_; simp; done)
    | exact pagesExtend_of_eq (placeSlot_keeps ..).1
    | exact pagesExtend_of_eq (alignRow_shipped_id ..).1
    | (refine pagesExtend_congr ?_ (finishPage_extends _ (o := st.b.closingOwed) (f := false)); simp; done)
    | (refine pagesExtend_congr ?_
        (pagesExtend_trans (finishPage_extends _ (o := st.b.closingOwed) (f := false)) (pagesExtend_of_eq ?_)) <;> simp <;> done)

private theorem placeAnchor_noBreak (fs : FontSet) (b : B) (h' : AnchorRule) (shift : Sp)
    (paints : Bool) (h : b.noBreak = true) :
    (b.placeAnchor fs h' shift paints).pages = b.pages ∧
      (b.placeAnchor fs h' shift paints).noBreak = true := by
  simp only [Spacing.Page.placeAnchor]
  split
  · simp only [keepInk_pages, keepInk_noBreak]
    exact fitCommit_noBreak (h := h) ..
  · exact ⟨rfl, h⟩

private theorem placeLine_noBreak (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (anchors : Array String) (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp)
    (h : b.noBreak = true) :
    (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
      step rs strut).pages = b.pages ∧
    (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
      step rs strut).noBreak = true :=
  ⟨placeLine_pages_noBreak fs b x size segs w hang ex ns c lf firstBaseline dj op anchors
      paintPadding step rs strut h,
   placeLine_keeps_noBreak fs b x size segs w hang ex ns c lf firstBaseline dj op anchors
      paintPadding step rs strut h⟩

private theorem alignRow_pages_noBreak (b : B) (save : ColSave) (h : b.noBreak = true) :
    (b.alignRow save).pages = b.pages ∧ (b.alignRow save).noBreak = true :=
  let p := alignRow_shipped_id b save
  ⟨p.1, p.2.2.2.trans h⟩

private theorem placeSlot_noBreak (fs : FontSet) (b : B) (save : ColSave × Nat × Nat × Nat)
    (spec : SlotSpec) (h : b.noBreak = true) :
    (b.placeSlot fs save spec).pages = b.pages ∧ (b.placeSlot fs save spec).noBreak = true :=
  let p := placeSlot_keeps fs b save spec
  ⟨p.1, p.2.2.2.trans h⟩

private theorem stepStaged_noBreak (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (s : Op) (h : st.b.noBreak = true) (hs : s ≠ .brk) :
    (stepStaged fs imgs st s).b.pages = st.b.pages ∧
    (stepStaged fs imgs st s).b.noBreak = true := by
  cases s
  case skipAlt long short =>
    simp only [stepStaged, Id.run, Id, pure]
    repeat' split
    all_goals (refine ⟨?_, ?_⟩ <;> simp [h]; done)
  case regionOpen target =>
    refine ⟨?_, ?_⟩ <;> simp [stepStaged, h]
  case regionClose =>
    rw [stepStaged_regionClose_b]
    exact ⟨(closeRegion_shipped_id fs st.b).1, (closeRegion_shipped_id fs st.b).2.1.trans h⟩
  case boxAnchor h' shift paints =>
    rw [stepStaged_boxAnchor_b]
    exact placeAnchor_noBreak (h := h) ..
  case hrule color th =>
    rw [stepStaged_hrule_b]
    exact placeLine_noBreak (h := h) ..
  case tableRule th x w segs =>
    rw [stepStaged_tableRule_b]
    exact fitCommit_noBreak (h := h) ..
  case para j task =>
    rw [stepStaged_para_b, keepHeading_noBreak _ _ _ h]
    exact placePara_noBreak _ _ _ _ h
  case picture x pic leaf origin =>
    rw [stepStaged_picture_b]
    exact placePicture_noBreak _ _ _ _ _ _ _ h
  all_goals (simp only [stepStaged, Id.run, Id, pure, Spacing.Page.openBody] <;> repeat' split)
  all_goals first
    | exact absurd rfl hs
    | (exfalso; exact ‹¬(_ ∨ _ = true ∨ _)› (Or.inr (Or.inl h)))
    | (exfalso; exact ‹¬(_ ∨ _ = true)› (Or.inr h))
    | exact placeSlot_noBreak (h := h) ..
    | exact alignRow_pages_noBreak (h := h) ..
    | (refine ⟨?_, ?_⟩ <;> simp [h]; done)

private theorem foldSteps_extends (fs : FontSet) (imgs : Image.Store)
    (group : Array Op) (st : StepSt) :
    PagesExtend st.b (group.foldl (stepStaged fs imgs) st).b :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => PagesExtend st.b acc.b)
    (pagesExtend_refl st.b)
    (fun _ _acc hacc => pagesExtend_trans hacc (stepStaged_extends ..))

private theorem foldSteps_noBreak (fs : FontSet) (imgs : Image.Store)
    (group : Array Op) (st : StepSt) (h : st.b.noBreak = true)
    (hg : ∀ s ∈ group, s ≠ Op.brk) :
    (group.foldl (stepStaged fs imgs) st).b.pages = st.b.pages ∧
    (group.foldl (stepStaged fs imgs) st).b.noBreak = true :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => acc.b.pages = st.b.pages ∧ acc.b.noBreak = true)
    ⟨rfl, h⟩
    (fun i acc hacc =>
      have step := stepStaged_noBreak fs imgs acc group[i] hacc.2
        (hg group[i] (Array.getElem_mem i.2))
      ⟨step.1.trans hacc.1, step.2⟩)

/-- The full-page background fill `finishPage` prepends when a background is declared. -/
private def bgFilled (g : Geom) (p : PageOut) : Prop :=
  ∃ f ∈ p.fills.toList, f.x = -g.bleed ∧ f.y = -g.bleed ∧
    f.w = g.pageW + 2 * g.bleed ∧ f.h = g.pageH + 2 * g.bleed

/-- One placement step keeping a declared background: geometry
unchanged, the ground still declared, and every new page filled. -/
private def BgStep (b b' : B) : Prop :=
  b'.geom = b.geom ∧ (b.docBg.isSome = true → b'.docBg.isSome = true) ∧
    (b.docBg.isSome = true → ∀ p ∈ b'.pages, p ∈ b.pages ∨ bgFilled b.geom p)

private theorem BgStep.refl (b : B) : BgStep b b :=
  ⟨rfl, id, fun _ _p hp => Or.inl hp⟩

private theorem BgStep.of_eq {b c : B} (hg : c.geom = b.geom)
    (hd : c.docBg = b.docBg) (hp : c.pages = b.pages) : BgStep b c :=
  ⟨hg, fun hs => hd ▸ hs, fun _ _p hpp => Or.inl (hp ▸ hpp)⟩

private theorem BgStep.trans {a b c : B} (h1 : BgStep a b) (h2 : BgStep b c) :
    BgStep a c := by
  obtain ⟨hg1, hd1, hp1⟩ := h1
  obtain ⟨hg2, hd2, hp2⟩ := h2
  refine ⟨hg2.trans hg1, fun hs => hd2 (hd1 hs), fun hs p hp => ?_⟩
  rcases hp2 (hd1 hs) p hp with h | h
  · exact hp1 hs p h
  · exact Or.inr (hg1 ▸ h)

private theorem BgStep.keepInk {a b : B} (h : BgStep a b) (d : Sp) :
    BgStep a (b.keepInk d) :=
  h.trans (BgStep.of_eq rfl rfl rfl)

private theorem BgStep.displayState {a b : B} (h : BgStep a b)
    (tex : Bool) (e : Option Sp) : BgStep a (b.displayState tex e) :=
  h.trans (BgStep.of_eq rfl rfl rfl)

private theorem finishPage_bg (b : B) {o : Sp} {f : Bool} :
    b.docBg.isSome = true → ∀ p ∈ (b.finishPage o f).pages,
      p ∈ b.pages ∨ bgFilled b.geom p := by
  intro hd p hp
  simp only [Spacing.Page.finishPage, Array.mem_push] at hp
  rcases hp with hp | rfl
  · exact Or.inl hp
  · right
    unfold bgFilled
    dsimp only
    rcases hpb : b.pageBg with _ | c
    · rcases hdb : b.docBg with _ | c'
      · rw [hdb] at hd; simp at hd
      · refine ⟨b.geom.ground c', ?_, rfl, rfl, rfl, rfl⟩
        simp [effectivePageGround]
    · refine ⟨b.geom.ground c, ?_, rfl, rfl, rfl, rfl⟩
      simp [effectivePageGround]

private theorem bgStep_finishPage (b : B) {o : Sp} {f : Bool} :
    BgStep b (b.finishPage o f) :=
  ⟨rfl, id, finishPage_bg b⟩

/-- The full-page fill in colour `c`. -/
private def bgFilledWith (g : Geom) (c : Ir.Color) (p : PageOut) : Prop :=
  ∃ f ∈ p.fills.toList, f.x = -g.bleed ∧ f.y = -g.bleed ∧
    f.w = g.pageW + 2 * g.bleed ∧ f.h = g.pageH + 2 * g.bleed ∧
    f.color = c

private theorem finishPage_pageBg_exact (b : B) (c : Ir.Color) {o : Sp} {f : Bool}
    (h : b.pageBg = some c) : ∀ p ∈ (b.finishPage o f).pages,
      p ∈ b.pages ∨ bgFilledWith b.geom c p := by
  intro p hp
  simp only [Spacing.Page.finishPage, Array.mem_push] at hp
  rcases hp with hp | rfl
  · exact Or.inl hp
  · right
    unfold bgFilledWith
    dsimp only
    refine ⟨b.geom.ground c, ?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [h]
    simp [effectivePageGround]

private theorem bgStep_spillPage (b : B) (o : Sp) : BgStep b (b.spillPage o) :=
  (bgStep_finishPage b (o := 0) (f := b.flushes)).trans
    (BgStep.of_eq (by simp [Spacing.Page.spillPage]) (by simp [Spacing.Page.spillPage]) (by simp [Spacing.Page.spillPage]))

private theorem bgStep_fitWith (b : B) (place : B → Sp → Bool → Sp → B)
    (settle : B → Sp → Sp → B) (firstY stepY retryY : B → Sp) (inkBelow bottom : Sp)
    (holdsBlank : Bool)
    (hp : ∀ b y c o, (place b y c o).geom = b.geom ∧ (place b y c o).docBg = b.docBg ∧
      (place b y c o).pages = b.pages)
    (hs : ∀ b y d, (settle b y d).geom = b.geom ∧ (settle b y d).docBg = b.docBg ∧
      (settle b y d).pages = b.pages) :
    BgStep b (b.fitWith place settle firstY stepY retryY inkBelow bottom holdsBlank) := by
  simp only [Spacing.Page.fitWith]
  repeat' split
  all_goals first
    | (refine BgStep.of_eq ?_ ?_ ?_ <;> simp [hp, hs]
       done)
    | (refine (bgStep_finishPage b (o := 0) (f := b.flushes)).trans (BgStep.of_eq ?_ ?_ ?_) <;>
         simp [hp, hs]
       done)

private theorem bgStep_fitCommit (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) :
    BgStep b (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns) :=
  bgStep_fitWith b _ _ firstY stepY retryY inkBelow bottom true (fun _ _ _ _ => by simp)
    fun _ _ _ => by simp

private theorem bgStep_placeAnchor (fs : FontSet) (b : B) (h : AnchorRule) (shift : Sp)
    (paints : Bool) : BgStep b (b.placeAnchor fs h shift paints) := by
  simp only [Spacing.Page.placeAnchor]
  split
  · apply BgStep.keepInk
    exact bgStep_fitCommit ..
  · exact BgStep.of_eq rfl rfl rfl

private theorem bgStep_placeLine (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (anchors : Array String) (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp) :
    BgStep b
      (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
        step rs strut) := by
  simp only [Spacing.Page.placeLine]
  apply BgStep.displayState
  apply BgStep.keepInk
  exact bgStep_fitCommit ..

private theorem bgStep_placePicture (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat) :
    BgStep b (placePicture fs imgs b x pic leaf origin) := by
  simp only [placePicture]
  exact bgStep_fitWith b _ _ _ _ _ _ _ _ (fun _ _ _ _ => by simp) fun _ _ _ => ⟨rfl, rfl, rfl⟩

private theorem bgStep_placeParaLine (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) :
    BgStep st.1 (placeParaLine fs j st brk).1 := by
  simp only [placeParaLine, Spacing.Page.withPendingSource]
  refine BgStep.trans (BgStep.trans ?_ (bgStep_placeLine ..))
    (BgStep.of_eq (placeParaTrailer_geom ..) (placeParaTrailer_docBg ..)
      (placeParaTrailer_pages ..))
  split <;> exact BgStep.of_eq (by simp) (by simp) (by simp)

private theorem bgStep_placePara (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) : BgStep b (placePara fs b j breaks) := by
  unfold placePara
  exact Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) => BgStep b acc.1)
    (BgStep.of_eq (by simp) (by simp) (by simp))
    (fun _ acc hacc => hacc.trans (bgStep_placeParaLine ..))

private theorem bgStep_keepHeading (b : B) (j : ParaJob) (n : Nat) :
    BgStep b (b.keepHeading j n) := by
  unfold Spacing.Page.keepHeading
  split
  · exact bgStep_spillPage b 0
  · exact BgStep.refl b

/-- Whether an op leaves a declared persistent ground
declared, a proof premise and no emission gate. -/
private def Op.preservesGround : Op → Bool
  | .pageGround bg => bg.isSome
  | _ => true

private theorem bgStep_stepStaged (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (op : Op) (h : op.preservesGround = true) :
    BgStep st.b (stepStaged fs imgs st op).b := by
  cases op
  case regionClose =>
    rw [stepStaged_regionClose_b]
    exact BgStep.of_eq (closeRegion_shipped_id fs st.b).2.2.1 (closeRegion_shipped_id fs st.b).2.2.2.1
      (closeRegion_shipped_id fs st.b).1
  case boxAnchor h' shift paints =>
    rw [stepStaged_boxAnchor_b]
    exact bgStep_placeAnchor ..
  case hrule color th =>
    rw [stepStaged_hrule_b]
    exact bgStep_placeLine ..
  case tableRule th x w segs =>
    rw [stepStaged_tableRule_b]
    exact bgStep_fitCommit ..
  case para j task =>
    rw [stepStaged_para_b]
    exact (bgStep_keepHeading ..).trans (bgStep_placePara ..)
  case picture x pic leaf origin =>
    rw [stepStaged_picture_b]
    exact bgStep_placePicture ..
  all_goals simp only [stepStaged, Id.run, Id, pure, Spacing.Page.openBody] <;> repeat' split
  all_goals first
    | (refine BgStep.of_eq ?_ ?_ ?_ <;> simp
       done)
    | exact ⟨rfl, fun _ => h, fun _ _p hp => Or.inl hp⟩
    | exact BgStep.of_eq (placeSlot_keeps ..).2.1 (placeSlot_keeps ..).2.2.1
        (placeSlot_keeps ..).1
    | exact BgStep.of_eq (alignRow_shipped_id ..).2.1 (alignRow_shipped_id ..).2.2.1
        (alignRow_shipped_id ..).1
    | (refine (bgStep_finishPage _ (o := st.b.closingOwed) (f := false)).trans (BgStep.of_eq ?_ ?_ ?_) <;> simp
       done)

private theorem bgStep_foldSteps (fs : FontSet) (imgs : Image.Store)
    (group : Array Op) (st : StepSt)
    (hg : ∀ op ∈ group, op.preservesGround = true) :
    BgStep st.b (group.foldl (stepStaged fs imgs) st).b :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => BgStep st.b acc.b)
    (BgStep.refl st.b)
    (fun i acc hacc => hacc.trans
      (bgStep_stepStaged fs imgs acc group[i] (hg _ (Array.getElem_mem i.2))))

private theorem bgStep_runFloat (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (group : Array Op)
    (hg : ∀ op ∈ group, op.preservesGround = true) :
    BgStep st.b (runFloat fs imgs st group).b := by
  simp only [LeanTex.Core.Layout.runFloat]
  split
  · exact bgStep_foldSteps fs imgs group st hg
  · have h1 : BgStep st.b (if st.b.cur.blank
        then st.b else st.b.finishPage) := by
      split
      · exact BgStep.refl _
      · exact bgStep_finishPage _
    have h2 := bgStep_foldSteps fs imgs group
      { st with b :=
        { (if st.b.cur.blank then st.b
           else st.b.finishPage) with noBreak := true } } hg
    refine (h1.trans ((BgStep.of_eq rfl rfl rfl).trans
      (h2.trans (BgStep.of_eq ?_ ?_ ?_))))
    all_goals repeat' split
    all_goals simp

/-- The index just past the float group opening before `j`,
or `staged.size` when no close stands; never below `j`. -/
private def matchingClose (staged : Array Op) (j : Nat) (depth : Nat) : Nat :=
  if h : j < staged.size then
    match staged[j] with
    | .floatOpen => matchingClose staged (j + 1) (depth + 1)
    | .floatClose =>
      if depth == 1 then j else matchingClose staged (j + 1) (depth - 1)
    | _ => matchingClose staged (j + 1) depth
  else j
termination_by staged.size - j

private theorem matchingClose_ge (staged : Array Op) (j depth : Nat) :
    j ≤ matchingClose staged j depth := by
  induction j, depth using matchingClose.induct staged with
  | _ =>
    unfold matchingClose
    simp_all only [dite_true, dite_false, ite_true]
    try split
    all_goals omega

/-- What a heading keeps of the paragraph after it: its first two
lines as placement sets them (latex.ltx `\@afterheading`). -/
private def keptHead (fs : FontSet) (b : B) (j : ParaJob) (breaks : Array Nat) : Sp :=
  let box (first : Bool) (prev brk : Nat) : LineBox :=
    lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent b.geom.leading j.size
      (paraLineGeom fs j b first prev brk).1 j.lead
  match breaks[0]?, breaks[1]? with
  | some k0, some k1 =>
    let l0 := box true 0 k0
    let l1 := box false k0 k1
    l0.above + l0.below + l1.above + l1.inkBelow
  | some k0, none =>
    let l0 := box true 0 k0
    l0.above + l0.inkBelow
  | none, _ => 0

/-- A heading's reserve: the next block's first box and the glue before
it, a run of headings keeping as one chain (latex.ltx `\@xsect`). -/
private def keepExt (b : B) (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (k : Nat) (glue : Sp) : Sp :=
  if h : k < staged.size then
    match staged[k] with
    | .skip g => keepExt b fs imgs staged (k + 1) (glue + g.width)
    | .skipAlt g _ => keepExt b fs imgs staged (k + 1) (glue + g.width)
    | .anchor _ => keepExt b fs imgs staged (k + 1) glue
    | .picture _ pic _ _ =>
      let ((_, py0), (_, py1)) := pictureBox b.geom fs imgs b.xHeight pic
      glue + inkClearance + (py1 - py0)
    | .para j t =>
      if 0 < j.keepNext then
        glue + (t.get.size : Int) * Ir.stepSkip j.lead j.size b.geom.leading
          + max j.keepNext (keepExt b fs imgs staged (k + 1) 0)
      else glue + keptHead fs b j t.get
    | _ => 0
  else 0
termination_by staged.size - k

/-- The op placement steps: a heading's reserve
reaching the box after it, every other op as collected. -/
private def keepAt (b : B) (fs : FontSet) (imgs : Image.Store) (staged : Array Op)
    (si : Nat) (s : Op) : Op :=
  match s with
  | .para j t =>
    if 0 < j.keepNext then
      let reserve := max j.keepNext (keepExt b fs imgs staged (si + 1) 0)
      .para { j with keepNext := reserve } t
    else s
  | _ => s

private theorem keepAt_preservesGround (b : B) (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (si : Nat) (s : Op) :
    (keepAt b fs imgs staged si s).preservesGround = s.preservesGround := by
  cases s <;> simp only [keepAt] <;> first | rfl | (split <;> rfl)

/-- A column row's opening cursor and its completed flows, for a row that overflows its page. -/
private structure ColumnFlow where
  start : B
  completed : Option B := none

private structure FlowSt where
  placed : StepSt
  columns : List ColumnFlow := []

/-- The next column owns new ink, starting at the row's original cursor. -/
private def restartColumn (start latest : B) : B :=
  { start with cur := {}, shrinkAbove := #[], fillShrinkAbove := #[], inkShrinkAbove := #[]
               fillStretchAbove := #[], inkStretchAbove := #[]
               fillFilsAbove := #[], inkFilsAbove := #[]
               stretchAbove := #[], filsAbove := #[]
               pinnedLines := 0, pinnedFills := 0, pinnedInks := 0, pendingNotes := #[]
               opened := !start.fresh, freshStart := start.fresh
               openRegions := start.openRegions.map RegionStart.nextPage, closedRegions := #[]
               diags := latest.diags
               paragraphBreaks := latest.paragraphBreaks
               pendingAnchors := latest.pendingAnchors }

/-- Join ink on a physical page, a second flow's ground preceding both flows' ink. -/
private def mergeColumnPage (g : Geom) (a b : PageOut) : PageOut :=
  let ground := match b.fills[0]? with
    | some f => if f.x == -g.bleed && f.y == -g.bleed &&
        f.w == g.pageW + 2 * g.bleed && f.h == g.pageH + 2 * g.bleed then 1 else 0
    | none => 0
  { a with lines := a.lines ++ b.lines, inks := a.inks ++ b.inks
           links := a.links ++ b.links
           fills := b.fills.extract 0 ground ++ a.fills ++ b.fills.extract ground b.fills.size
           hidden :=
             { fills := a.hidden.fills.map (ground + ·) ++
                 b.hidden.fills.map fun i => if i < ground then i else a.fills.size + i
               inks := a.hidden.inks ++ b.hidden.inks.map (a.inks.size + ·)
               links := a.hidden.links ++ b.hidden.links.map (a.links.size + ·) } }

private def mergeColumnPages (g : Geom) (first : Nat)
    (a b : Array PageOut) : Array PageOut :=
  (Array.range (max a.size b.size)).filterMap fun i =>
    match a[i]?, b[i]? with
    | some p, some q => some (if i < first then p else mergeColumnPage g p q)
    | some p, none => some p
    | none, some q => some q
    | none, none => none

private def RegionSpan.afterPage (s : RegionSpan) (p : PageOut) : RegionSpan :=
  { s with lineStart := p.lines.size + s.lineStart, lineEnd := p.lines.size + s.lineEnd
           fillStart := p.fills.size + s.fillStart, fillEnd := p.fills.size + s.fillEnd
           inkStart := p.inks.size + s.inkStart, inkEnd := p.inks.size + s.inkEnd
           base := s.base.map (·.afterPage p) }

/-- Join two unfinished columns on one page, keeping their line ledgers, link ranges and bounds. -/
private def joinColumnCurrent (a b : B) : B :=
  let endCursor := if a.y + a.prevDepth > b.y + b.prevDepth then a else b
  let ending := a.colEnd.join b.colEnd
  let cur := { a.cur with
    lines := a.cur.lines ++ b.cur.lines
    fills := a.cur.fills ++ b.cur.fills
    inks := a.cur.inks ++ b.cur.inks }
  { endCursor with
    cur := cur
    y := ending.tail.y, prevDepth := ending.tail.depth
    prevBelow := ending.tail.below, prevBand := ending.tail.band
    lastSource := ending.source
    lastInk := some (ending.tail.y, ending.tail.depth, ending.tail.boxDepth)
    shrinkAbove := a.shrinkAbove ++ b.shrinkAbove, pageShrink := max a.pageShrink b.pageShrink
    fillShrinkAbove := a.fillShrinkAbove ++ b.fillShrinkAbove
    inkShrinkAbove := a.inkShrinkAbove ++ b.inkShrinkAbove
    fillStretchAbove := a.fillStretchAbove ++ b.fillStretchAbove
    inkStretchAbove := a.inkStretchAbove ++ b.inkStretchAbove
    fillFilsAbove := a.fillFilsAbove ++ b.fillFilsAbove
    inkFilsAbove := a.inkFilsAbove ++ b.inkFilsAbove
    stretchAbove := a.stretchAbove ++ b.stretchAbove, pageStretch := max a.pageStretch b.pageStretch
    filsAbove := a.filsAbove ++ b.filsAbove, pageFils := max a.pageFils b.pageFils
    needed := max a.needed b.needed
    neededSource := if a.needed < b.needed then b.neededSource else a.neededSource
    pendingNotes := a.pendingNotes ++ b.pendingNotes.map (fun l => { l with y := l.y + a.notesH })
    notesH := a.notesH + b.notesH
    notesDepth := if b.notesH == 0 then a.notesDepth else b.notesDepth
    closedRegions := a.closedRegions ++ a.openRegions.map (·.close a.cur) ++
      (b.closedRegions ++ b.openRegions.map (·.close b.cur)).map (·.afterPage a.cur)
    openRegions := b.openRegions.map (fun s =>
      { s with lines := cur.lines.size, fills := cur.fills.size, inks := cur.inks.size,
               first := false }) }

/-- Join completed pages by physical index, the last page left open for the furthest column. -/
private def joinColumn (first : Nat) (a b : B) : B :=
  let left := if a.pages.size < b.pages.size then a.finishPage else a
  let right := if b.pages.size < a.pages.size then b.finishPage else b
  let endCursor := if a.pages.size < b.pages.size then b
    else if b.pages.size < a.pages.size then
      { a with closedRegions := a.closedRegions ++ a.openRegions.map (·.close a.cur)
               openRegions := b.openRegions.map (fun s =>
                 { s with lines := a.cur.lines.size, fills := a.cur.fills.size,
                          inks := a.cur.inks.size, first := false }) }
    else joinColumnCurrent a b
  { endCursor with
    pages := mergeColumnPages b.geom first left.pages right.pages
    geom := b.geom, docBg := b.docBg
    pendingAnchors := b.pendingAnchors
    paragraphBreaks := b.paragraphBreaks
    diags := b.diags ++ left.diags.extract a.diags.size left.diags.size ++
      right.diags.extract b.diags.size right.diags.size }

private def ColumnFlow.add (save : ColumnFlow) (b : B) : B :=
  match save.completed with
  | none => b
  | some previous => joinColumn save.start.pages.size previous b

/-- End a row that spans pages at the joined cursor's page and box. -/
private def columnEnd (save : ColumnFlow) (st : StepSt) : StepSt :=
  let b := save.add st.b
  let colSaves := if b.pages.size == save.start.pages.size then st.colSaves
    else st.colSaves.modify (st.colSaves.size - 1) fun s =>
      { s with bottom := some b.colEnd }
  { st with b := b, colSaves := colSaves }

/-- One flow step: page switching belongs to the flow
driver, `stepStaged` placing a single cursor. -/
private def stepFlow (fs : FontSet) (imgs : Image.Store) (st : FlowSt)
    (op : Op) : FlowSt :=
  match op, st.columns with
  | .colOpen pos, _ =>
    let placed := stepStaged fs imgs st.placed (.colOpen pos)
    { placed := placed, columns := { start := placed.b } :: st.columns }
  | .colNext, save :: rest =>
    let placed := stepStaged fs imgs st.placed .colNext
    if save.completed.isNone && st.placed.b.pages.size == save.start.pages.size then
      { st with placed := placed }
    else
      { placed := { placed with b := restartColumn save.start st.placed.b }
        columns := { save with completed := some (save.add st.placed.b) } :: rest }
  | .colClose, save :: rest =>
    { placed := stepStaged fs imgs (columnEnd save st.placed) .colClose, columns := rest }
  | _, _ => { st with placed := stepStaged fs imgs st.placed op }

/-- The page fact both the active cursor and every
saved flow carry, as column rewind revisits pages. -/
private def Grounded (g : Geom) (declared : Bool) (b : B) : Prop :=
  b.geom = g ∧ (declared = true →
    b.docBg.isSome = true ∧ ∀ p ∈ b.pages, bgFilled g p)

private theorem Grounded.step {g : Geom} {d : Bool} {a b : B}
    (h : Grounded g d a) (hs : BgStep a b) : Grounded g d b := by
  refine ⟨hs.1.trans h.1, fun hd => ?_⟩
  obtain ⟨hb, hp⟩ := h.2 hd
  refine ⟨hs.2.1 hb, fun p hpp => ?_⟩
  rcases hs.2.2 hb p hpp with old | new
  · exact hp p old
  · exact h.1 ▸ new

private theorem mergeColumnPage_ground (g : Geom) (a b : PageOut)
    (ha : bgFilled g a) : bgFilled g (mergeColumnPage g a b) := by
  obtain ⟨f, hf, shape⟩ := ha
  refine ⟨f, ?_, shape⟩
  simp only [mergeColumnPage, Array.toList_append, List.mem_append]
  exact Or.inl (Or.inr hf)

private theorem mergeColumnPages_ground (g : Geom) (first : Nat) (a b : Array PageOut)
    (ha : ∀ p ∈ a, bgFilled g p) (hb : ∀ p ∈ b, bgFilled g p) :
    ∀ p ∈ mergeColumnPages g first a b, bgFilled g p := by
  intro p hp
  obtain ⟨i, _, hp⟩ := Array.mem_filterMap.mp hp
  cases ea : a[i]? with
  | none =>
    cases eb : b[i]? with
    | none => simp [ea, eb] at hp
    | some q =>
      simp only [ea, eb, Option.some.injEq] at hp
      subst p
      exact hb q (Array.mem_of_getElem? eb)
  | some q =>
    cases eb : b[i]? with
    | none =>
      simp only [ea, eb, Option.some.injEq] at hp
      subst p
      exact ha q (Array.mem_of_getElem? ea)
    | some r =>
      simp only [ea, eb, Option.some.injEq] at hp
      subst p
      split
      · exact ha q (Array.mem_of_getElem? ea)
      · exact mergeColumnPage_ground g q r (ha q (Array.mem_of_getElem? ea))

private theorem joinColumn_ground {g : Geom} {d : Bool} (first : Nat) (a b : B)
    (ha : Grounded g d a) (hb : Grounded g d b) :
    Grounded g d (joinColumn first a b) := by
  refine ⟨hb.1, fun hd => ⟨(hb.2 hd).1, ?_⟩⟩
  have hl : Grounded g d (if a.pages.size < b.pages.size then a.finishPage else a) := by
    split
    · exact ha.step (bgStep_finishPage a)
    · exact ha
  have hr : Grounded g d (if b.pages.size < a.pages.size then b.finishPage else b) := by
    split
    · exact hb.step (bgStep_finishPage b)
    · exact hb
  change ∀ p ∈ mergeColumnPages b.geom first _ _, bgFilled g p
  rw [hb.1]
  exact mergeColumnPages_ground g first _ _ (hl.2 hd).2 (hr.2 hd).2

private def ColumnFlow.grounded (g : Geom) (d : Bool) (save : ColumnFlow) : Prop :=
  Grounded g d save.start ∧ ∀ b ∈ save.completed, Grounded g d b

private theorem ColumnFlow.add_ground {g : Geom} {d : Bool} (save : ColumnFlow) (b : B)
    (hs : save.grounded g d) (hb : Grounded g d b) : Grounded g d (save.add b) := by
  unfold ColumnFlow.add
  split
  · exact hb
  · next previous he =>
    exact joinColumn_ground _ _ _ (hs.2 previous he) hb

private def FlowGround (g : Geom) (d : Bool) (st : FlowSt) : Prop :=
  Grounded g d st.placed.b ∧ ∀ save ∈ st.columns, save.grounded g d

private theorem stepFlow_ground (fs : FontSet) (imgs : Image.Store)
    (st : FlowSt) (op : Op) {g : Geom} {d : Bool}
    (h : FlowGround g d st) (hg : op.preservesGround = true) :
    FlowGround g d (stepFlow fs imgs st op) := by
  cases op with
  | colOpen pos =>
    have hp := h.1.step (bgStep_stepStaged fs imgs st.placed (.colOpen pos) hg)
    refine ⟨hp, ?_⟩
    simp only [stepFlow, List.forall_mem_cons]
    exact ⟨⟨hp, by simp⟩, h.2⟩
  | colNext =>
    cases hc : st.columns with
    | nil =>
      simp only [stepFlow, hc, FlowGround]
      exact ⟨h.1.step (bgStep_stepStaged fs imgs st.placed .colNext hg),
        by simp⟩
    | cons save rest =>
      have hs := h.2 save (hc ▸ List.mem_cons_self)
      have hr : ∀ s ∈ rest, s.grounded g d := fun s hm =>
        h.2 s (hc ▸ List.mem_cons_of_mem _ hm)
      simp only [stepFlow, hc]
      split
      · exact ⟨h.1.step (bgStep_stepStaged fs imgs st.placed .colNext hg),
          by simpa only [hc] using h.2⟩
      · refine ⟨hs.1, ?_⟩
        simp only [List.forall_mem_cons, ColumnFlow.grounded, Option.mem_some]
        exact ⟨⟨hs.1, fun _ he => he ▸ save.add_ground st.placed.b hs h.1⟩, hr⟩
  | colClose =>
    cases hc : st.columns with
    | nil =>
      simp only [stepFlow, hc, FlowGround]
      exact ⟨h.1.step (bgStep_stepStaged fs imgs st.placed .colClose hg),
        by simp⟩
    | cons save rest =>
      have hs := h.2 save (hc ▸ List.mem_cons_self)
      have hb : Grounded g d (columnEnd save st.placed).b :=
        save.add_ground st.placed.b hs h.1
      simp only [stepFlow, hc, FlowGround]
      refine ⟨hb.step (bgStep_stepStaged fs imgs (columnEnd save st.placed) .colClose hg), ?_⟩
      exact fun s hm => h.2 s (hc ▸ List.mem_cons_of_mem _ hm)
  | _ => exact ⟨h.1.step (bgStep_stepStaged fs imgs st.placed _ hg), h.2⟩

/-- Placement one op at a time (`stepStaged`), a
float's ops as one unbreakable group (`runFloat`). -/
private def placeFlowFrom (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : FlowSt) (si : Nat) : FlowSt :=
  if h : si < staged.size then
    match staged[si] with
    | .floatOpen =>
      let j := matchingClose staged (si + 1) 1
      have hj : si + 1 ≤ j := matchingClose_ge staged (si + 1) 1
      placeFlowFrom fs imgs staged
        { st with placed := runFloat fs imgs st.placed (staged.extract (si + 1) j) }
        (j + 1)
    | s => placeFlowFrom fs imgs staged
        (stepFlow fs imgs st (keepAt st.placed.b fs imgs staged si s)) (si + 1)
  else st
termination_by staged.size - si
decreasing_by all_goals omega

private def placeFrom (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : StepSt) (si : Nat) : StepSt :=
  (placeFlowFrom fs imgs staged { placed := st } si).placed

private theorem sourceBound_keepHeading {n : Nat} (b : B) (j : ParaJob)
    (lines : Nat) (hb : b.SourceBound n) :
    (b.keepHeading j lines).SourceBound n := by
  unfold Spacing.Page.keepHeading
  split
  · exact sourceBound_spillPage b 0 hb
  · exact hb

private theorem sourceBound_stepStaged {n : Nat} (fs : FontSet)
    (imgs : Image.Store) (st : StepSt) (op : Op)
    (hb : st.b.SourceBound n) (ho : op.SourceBound n) :
    (stepStaged fs imgs st op).b.SourceBound n := by
  cases op <;> simp only [Op.SourceBound] at ho
  all_goals try contradiction
  case para j t =>
    simp only [stepStaged, Id.run, Id, pure]
    split <;> exact sourceBound_placePara fs _ j t.get ho
      (sourceBound_keepHeading st.b j t.get.size hb)
  all_goals
    simp only [stepStaged, Id.run, Id, pure]
    repeat' split
    all_goals exact hb.of_eq rfl rfl rfl rfl rfl

private theorem sourceBound_keepAt {n : Nat} (b : B) (fs : FontSet)
    (imgs : Image.Store) (staged : Array Op) (si : Nat) (op : Op)
    (ho : op.SourceBound n) :
    (keepAt b fs imgs staged si op).SourceBound n := by
  cases op with
  | para j t =>
    simp only [keepAt]
    split
    · exact ⟨ho.source, ho.notes, ho.marker, ho.rule⟩
    · exact ho
  | _ => exact ho

private theorem sourceBound_stepFlow {n : Nat} (fs : FontSet)
    (imgs : Image.Store) (st : FlowSt) (op : Op)
    (hb : st.placed.b.SourceBound n) (ho : op.SourceBound n) :
    (stepFlow fs imgs st op).placed.b.SourceBound n := by
  cases op <;> simp only [Op.SourceBound] at ho
  all_goals try contradiction
  all_goals exact sourceBound_stepStaged fs imgs st.placed _ hb ho

private theorem sourceBound_placeFlowFrom {n : Nat} (fs : FontSet)
    (imgs : Image.Store) (staged : Array Op) (st : FlowSt) (si : Nat)
    (ho : ∀ op ∈ staged, op.SourceBound n) (hb : st.placed.b.SourceBound n) :
    (placeFlowFrom fs imgs staged st si).placed.b.SourceBound n := by
  rw [placeFlowFrom]
  split
  · rename_i hi
    have hop := ho _ (Array.getElem_mem hi)
    split
    · rename_i he
      simp only [he, Op.SourceBound] at hop
    · exact sourceBound_placeFlowFrom fs imgs staged _ (si + 1) ho
        (sourceBound_stepFlow fs imgs st _ hb
          (sourceBound_keepAt st.placed.b fs imgs staged si _ hop))
  · exact hb
termination_by staged.size - si
decreasing_by omega

private theorem sourceBound_placeFrom {n : Nat} (fs : FontSet)
    (imgs : Image.Store) (staged : Array Op) (st : StepSt) (si : Nat)
    (ho : ∀ op ∈ staged, op.SourceBound n) (hb : st.b.SourceBound n) :
    (placeFrom fs imgs staged st si).b.SourceBound n :=
  sourceBound_placeFlowFrom fs imgs staged { placed := st } si ho hb

private def Spacing.Page.frameStamp (b : B) : FrameStamp :=
  (b.curFrameOrigin, b.curFrame, b.curFoot)

private def FrameStep (a b : B) : Prop :=
  b.frameStamp = a.frameStamp ∧
    ∀ p ∈ b.pages, p ∈ a.pages ∨ p.frameStamp = a.frameStamp

private theorem FrameStep.refl (b : B) : FrameStep b b :=
  ⟨rfl, fun _ h => Or.inl h⟩

private theorem FrameStep.of_eq {a b : B}
    (hs : b.frameStamp = a.frameStamp) (hp : b.pages = a.pages) :
    FrameStep a b :=
  ⟨hs, fun _ h => Or.inl (hp ▸ h)⟩

private theorem FrameStep.trans {a b c : B}
    (hab : FrameStep a b) (hbc : FrameStep b c) : FrameStep a c := by
  refine ⟨hbc.1.trans hab.1, fun p hp => ?_⟩
  rcases hbc.2 p hp with old | new
  · exact hab.2 p old
  · exact Or.inr (new.trans hab.1)

private theorem FrameStep.keepInk {a b : B} (h : FrameStep a b) (d : Sp) :
    FrameStep a (b.keepInk d) :=
  h.trans (FrameStep.of_eq rfl rfl)

private theorem FrameStep.displayState {a b : B} (h : FrameStep a b)
    (tex : Bool) (e : Option Sp) : FrameStep a (b.displayState tex e) :=
  h.trans (FrameStep.of_eq rfl rfl)

private def FramesFooted (openings : Array FrameOpening) (b : B) : Prop :=
  SelectedFrame openings b.frameStamp ∧
    ∀ p ∈ b.pages, SelectedFrame openings p.frameStamp

private theorem FramesFooted.step {openings : Array FrameOpening} {a b : B}
    (ha : FramesFooted openings a) (h : FrameStep a b) :
    FramesFooted openings b := by
  refine ⟨h.1 ▸ ha.1, fun p hp => ?_⟩
  rcases h.2 p hp with old | new
  · exact ha.2 p old
  · exact new ▸ ha.1

private theorem frameStep_finishPage (b : B) (owed : Sp) (flush : Bool) :
    FrameStep b (b.finishPage owed flush) := by
  refine ⟨rfl, fun p hp => ?_⟩
  simp only [Spacing.Page.finishPage, Array.mem_push] at hp
  rcases hp with hp | rfl
  · exact Or.inl hp
  · exact Or.inr rfl

@[simp] private theorem reopenChrome_frameStamp (b : B) :
    b.reopenChrome.frameStamp = b.frameStamp := by
  unfold Spacing.Page.reopenChrome
  split <;> rfl

@[simp] private theorem warnSpill_frameStamp (b : B) (over : Sp) :
    (b.warnSpill over).frameStamp = b.frameStamp := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals rfl

private theorem frameStep_spillPage (b : B) (over : Sp) :
    FrameStep b (b.spillPage over) :=
  (frameStep_finishPage b 0 b.flushes).trans
    ((FrameStep.of_eq (reopenChrome_frameStamp ..) (reopenChrome_pages ..)).trans
      ((FrameStep.of_eq (warnSpill_frameStamp ..) (warnSpill_pages ..)).trans
        (FrameStep.of_eq rfl rfl)))

@[simp] private theorem attachNotes_frameStamp (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).frameStamp = b.frameStamp := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction
      (motive := fun _ (acc : B) => acc.frameStamp = b.frameStamp)
      rfl (fun _ _ h => h)

@[simp] private theorem pushSibling_frameStamp (b : B) (l : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp) (fils : Option Nat) :
    (b.pushSibling l fills inks shrink fils).frameStamp = b.frameStamp := by
  cases l <;> simp only [Spacing.Page.pushSibling] <;> split <;> rfl

@[simp] private theorem pushLabels_frameStamp (b : B) (ls : Array LineOut)
    (shrink : Sp) (fils : Nat) :
    (b.pushLabels ls shrink fils).frameStamp = b.frameStamp := by
  unfold Spacing.Page.pushLabels
  exact Array.foldl_induction
    (motive := fun _ (acc : B) => acc.frameStamp = b.frameStamp)
    rfl (fun _ _ h => by rw [pushSibling_frameStamp]; exact h)

@[simp] private theorem pushSibling_frame_fields (b : B) (l : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp) (fils : Option Nat) :
    (b.pushSibling l fills inks shrink fils).curFrameOrigin = b.curFrameOrigin ∧
    (b.pushSibling l fills inks shrink fils).curFrame = b.curFrame ∧
    (b.pushSibling l fills inks shrink fils).curFoot = b.curFoot := by
  have h := pushSibling_frameStamp b l fills inks shrink fils
  simpa only [Spacing.Page.frameStamp, Prod.mk.injEq] using h

@[simp] private theorem pushLabels_frame_fields (b : B) (ls : Array LineOut)
    (shrink : Sp) (fils : Nat) :
    (b.pushLabels ls shrink fils).curFrameOrigin = b.curFrameOrigin ∧
    (b.pushLabels ls shrink fils).curFrame = b.curFrame ∧
    (b.pushLabels ls shrink fils).curFoot = b.curFoot := by
  have h := pushLabels_frameStamp b ls shrink fils
  simpa only [Spacing.Page.frameStamp, Prod.mk.injEq] using h

private theorem frameStep_attachNotes (b : B) (ns : Array NoteBlock) :
    FrameStep b (b.attachNotes ns) :=
  FrameStep.of_eq (attachNotes_frameStamp ..) (attachNotes_pages ..)

private theorem frameStep_commit (b : B) (l : LineOut) (depth below : Sp)
    (ruleLine consume : Bool) (overflow : Sp) :
    FrameStep b (b.commit l depth below ruleLine consume overflow) :=
  FrameStep.of_eq rfl rfl

private theorem frameStep_warnNoteOverrun (b : B) (y depth : Sp) :
    FrameStep b (b.warnNoteOverrun y depth) := by
  simp only [Spacing.Page.warnNoteOverrun]
  split <;> exact FrameStep.of_eq rfl rfl

private theorem frameStep_noteOverrun (b : B) (o : Sp) : FrameStep b (b.noteOverrun o) := by
  unfold Spacing.Page.noteOverrun
  repeat' split
  all_goals exact FrameStep.of_eq rfl rfl

private theorem frameStep_fitWith (b : B) (place : B → Sp → Bool → Sp → B)
    (settle : B → Sp → Sp → B) (firstY stepY retryY : B → Sp) (inkBelow bottom : Sp)
    (holdsBlank : Bool) (hp : ∀ b y c o, FrameStep b (place b y c o))
    (hs : ∀ b y d, FrameStep b (settle b y d)) :
    FrameStep b (b.fitWith place settle firstY stepY retryY inkBelow bottom holdsBlank) := by
  simp only [Spacing.Page.fitWith]
  split
  · exact (hp ..).trans (hs ..)
  · split
    · exact hp ..
    · split
      · exact (hp ..).trans (frameStep_noteOverrun ..)
      · refine FrameStep.trans ?_ (frameStep_noteOverrun ..)
        split <;> exact (frameStep_spillPage b _).trans ((hp ..).trans (hs ..))

private theorem frameStep_fitCommit (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) :
    FrameStep b (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns) :=
  frameStep_fitWith b _ _ firstY stepY retryY inkBelow bottom true
    (fun _ _ _ _ => (frameStep_commit ..).trans (frameStep_attachNotes ..))
    fun _ _ _ => frameStep_warnNoteOverrun ..

private theorem frameStep_placeAnchor (fs : FontSet) (b : B) (h : AnchorRule) (shift : Sp)
    (paints : Bool) : FrameStep b (b.placeAnchor fs h shift paints) := by
  simp only [Spacing.Page.placeAnchor]
  split
  · apply FrameStep.keepInk
    exact frameStep_fitCommit ..
  · exact FrameStep.of_eq rfl rfl

private theorem frameStep_placeLine (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (anchors : Array String) (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp) :
    FrameStep b
      (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
        step rs strut) := by
  simp only [Spacing.Page.placeLine]
  apply FrameStep.displayState
  apply FrameStep.keepInk
  exact frameStep_fitCommit ..

private theorem frameStep_openDisplayAt (b : B) (j : ParaJob) (first : Bool)
    (x : Sp) (segs : Array Seg) :
    FrameStep b (b.openDisplayAt j first x segs) := by
  unfold Spacing.Page.openDisplayAt
  split <;> exact FrameStep.of_eq rfl rfl

private theorem frameStep_placeParaTrailer (fs : FontSet) (j : ParaJob) (k : Nat)
    (segs : Array Seg) (b : B) : FrameStep b (placeParaTrailer fs j k segs b) := by
  unfold placeParaTrailer reachDepth
  repeat' split
  all_goals exact FrameStep.of_eq rfl rfl

private theorem frameStep_withPendingSource (b : B) (source : Option Span) :
    FrameStep b (b.withPendingSource source) := FrameStep.of_eq rfl rfl

private theorem frameStep_placeParaLine (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) :
    FrameStep st.1 (placeParaLine fs j st brk).1 := by
  simp only [placeParaLine]
  refine FrameStep.trans (FrameStep.trans (FrameStep.trans (FrameStep.trans ?_
    (frameStep_openDisplayAt ..)) (frameStep_withPendingSource ..))
    (frameStep_placeLine ..)) (frameStep_placeParaTrailer ..)
  split <;> exact FrameStep.of_eq rfl rfl

private theorem frameStep_placePara (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) : FrameStep b (placePara fs b j breaks) := by
  unfold placePara
  refine Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) => FrameStep b acc.1)
    ?_ (fun _ _ h => h.trans (frameStep_placeParaLine ..))
  unfold Spacing.Page.warnReflow
  split <;> exact FrameStep.of_eq rfl rfl

private theorem frameStep_placePicture (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat) :
    FrameStep b (placePicture fs imgs b x pic leaf origin) := by
  simp only [placePicture]
  exact frameStep_fitWith b _ _ _ _ _ _ _ _
    (fun _ _ _ _ => FrameStep.of_eq (by simp [Spacing.Page.frameStamp]) (by simp))
    fun _ _ _ => FrameStep.refl _

private theorem frameStep_keepHeading (b : B) (j : ParaJob) (n : Nat) :
    FrameStep b (b.keepHeading j n) := by
  unfold Spacing.Page.keepHeading
  split
  · exact frameStep_spillPage b 0
  · exact FrameStep.refl b

private theorem frameStep_placeSlot (fs : FontSet) (b : B) (save : ColSave × Nat × Nat × Nat)
    (spec : SlotSpec) : FrameStep b (b.placeSlot fs save spec) := by
  obtain ⟨col, l0, f0, k0⟩ := save
  simp only [Spacing.Page.placeSlot]
  split <;> exact FrameStep.of_eq rfl rfl

private theorem frameStep_alignRow (b : B) (save : ColSave) :
    FrameStep b (b.alignRow save) := by
  refine FrameStep.of_eq ?_ ?_ <;> simp [Spacing.Page.alignRow, Spacing.Page.frameStamp]

private def Op.frameOpening? : Op → Option FrameOpening
  | .frameOpen _ _ opening => some opening
  | _ => none

private theorem keepAt_frameOpening (b : B) (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (si : Nat) (op : Op) :
    (keepAt b fs imgs staged si op).frameOpening? = op.frameOpening? := by
  cases op <;> simp only [keepAt] <;> first | rfl | (split <;> rfl)

private theorem stepStaged_frames (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (op : Op) (openings : Array FrameOpening)
    (hb : FramesFooted openings st.b)
    (ho : ∀ f ∈ op.frameOpening?, f ∈ openings) :
    FramesFooted openings (stepStaged fs imgs st op).b := by
  cases op with
  | frameOpen br source opening =>
    exact ⟨Or.inr ⟨opening, ho opening rfl, rfl⟩, hb.2⟩
  | frameClose =>
    exact ⟨Or.inl rfl, hb.2⟩
  | regionClose =>
    rw [stepStaged_regionClose_b]
    exact hb.step (FrameStep.of_eq (closeRegion_shipped_id fs st.b).2.2.2.2.1
      (closeRegion_shipped_id fs st.b).1)
  | boxAnchor h shift paints =>
    rw [stepStaged_boxAnchor_b]
    exact hb.step (frameStep_placeAnchor ..)
  | hrule color th =>
    rw [stepStaged_hrule_b]
    exact hb.step (frameStep_placeLine ..)
  | tableRule th x w segs =>
    rw [stepStaged_tableRule_b]
    exact hb.step (frameStep_fitCommit ..)
  | para j task =>
    rw [stepStaged_para_b]
    exact hb.step ((frameStep_keepHeading ..).trans (frameStep_placePara ..))
  | picture x pic leaf origin =>
    rw [stepStaged_picture_b]
    exact hb.step (frameStep_placePicture ..)
  | slotClose spec =>
    simp only [stepStaged, Id.run, Id, pure]
    split
    · exact hb.step (frameStep_placeSlot ..)
    · exact hb
  | brk =>
    simp only [stepStaged, Id.run, Id, pure]
    split
    · exact hb.step ((frameStep_finishPage _ st.b.closingOwed false).trans
        (FrameStep.of_eq rfl rfl))
    · exact hb.step (FrameStep.of_eq rfl rfl)
  | colClose =>
    simp only [stepStaged, Id.run, Id, pure]
    repeat' split
    all_goals first
      | exact hb.step ((FrameStep.of_eq rfl rfl).trans (frameStep_alignRow ..))
      | exact hb.step (FrameStep.of_eq rfl rfl)
  | _ =>
    simp only [stepStaged, Id.run, Id, pure, Spacing.Page.openBody]
    repeat' split
    all_goals refine hb.step (FrameStep.of_eq ?_ ?_) <;> simp [Spacing.Page.frameStamp]

private theorem foldSteps_frames (fs : FontSet) (imgs : Image.Store)
    (group : Array Op) (st : StepSt) (openings : Array FrameOpening)
    (hb : FramesFooted openings st.b)
    (ho : ∀ op ∈ group, ∀ f ∈ op.frameOpening?, f ∈ openings) :
    FramesFooted openings (group.foldl (stepStaged fs imgs) st).b :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => FramesFooted openings acc.b)
    hb (fun i _ h => stepStaged_frames _ _ _ _ openings h
      (ho _ (Array.getElem_mem i.2)))

private theorem runFloat_frames (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (group : Array Op) (openings : Array FrameOpening)
    (hb : FramesFooted openings st.b)
    (ho : ∀ op ∈ group, ∀ f ∈ op.frameOpening?, f ∈ openings) :
    FramesFooted openings (runFloat fs imgs st group).b := by
  have finish : ∀ (b : B) (c : Prop) [Decidable c] (d : Diag),
      FramesFooted openings b →
      FramesFooted openings
        ({ (if c then { b with diags := b.diags.push d } else b) with
          noBreak := false } : B) := by
    intro b c inst d h
    split <;> exact h.step (FrameStep.of_eq rfl rfl)
  simp only [LeanTex.Core.Layout.runFloat]
  split
  · exact foldSteps_frames fs imgs group st openings hb ho
  · have hc : FramesFooted openings
        (if st.b.cur.blank
          then st.b else st.b.finishPage) := by
      split
      · exact hb
      · exact hb.step (frameStep_finishPage ..)
    have hr := foldSteps_frames fs imgs group
      { st with b :=
        { (if st.b.cur.blank then st.b
           else st.b.finishPage) with noBreak := true } } openings
      (hc.step (FrameStep.of_eq rfl rfl)) ho
    exact finish _ _ _ hr

private theorem frameStep_restartColumn (start latest : B) :
    FrameStep start (restartColumn start latest) :=
  FrameStep.of_eq rfl rfl

private theorem mergeColumnPages_frames (g : Geom) (first : Nat) (a b : Array PageOut)
    (openings : Array FrameOpening)
    (ha : ∀ p ∈ a, SelectedFrame openings p.frameStamp)
    (hb : ∀ p ∈ b, SelectedFrame openings p.frameStamp) :
    ∀ p ∈ mergeColumnPages g first a b, SelectedFrame openings p.frameStamp := by
  intro p hp
  obtain ⟨i, _, hp⟩ := Array.mem_filterMap.mp hp
  cases ea : a[i]? with
  | none =>
    cases eb : b[i]? with
    | none => simp [ea, eb] at hp
    | some q =>
      simp only [ea, eb, Option.some.injEq] at hp
      subst p
      exact hb q (Array.mem_of_getElem? eb)
  | some q =>
    cases eb : b[i]? with
    | none =>
      simp only [ea, eb, Option.some.injEq] at hp
      subst p
      exact ha q (Array.mem_of_getElem? ea)
    | some r =>
      simp only [ea, eb, Option.some.injEq] at hp
      subst p
      split <;> exact ha q (Array.mem_of_getElem? ea)

private theorem joinColumn_frames (first : Nat) (a b : B)
    (openings : Array FrameOpening) (ha : FramesFooted openings a)
    (hb : FramesFooted openings b) : FramesFooted openings (joinColumn first a b) := by
  have hl : FramesFooted openings
      (if a.pages.size < b.pages.size then a.finishPage else a) := by
    split
    · exact ha.step (frameStep_finishPage ..)
    · exact ha
  have hr : FramesFooted openings
      (if b.pages.size < a.pages.size then b.finishPage else b) := by
    split
    · exact hb.step (frameStep_finishPage ..)
    · exact hb
  refine ⟨?_, mergeColumnPages_frames b.geom first _ _ openings hl.2 hr.2⟩
  simp only [joinColumn, joinColumnCurrent, Spacing.Page.frameStamp]
  repeat' split
  all_goals first | exact ha.1 | exact hb.1

private def ColumnFlow.footed (openings : Array FrameOpening) (save : ColumnFlow) : Prop :=
  FramesFooted openings save.start ∧ ∀ b ∈ save.completed, FramesFooted openings b

private theorem ColumnFlow.add_frames (save : ColumnFlow) (b : B)
    (openings : Array FrameOpening) (hs : save.footed openings)
    (hb : FramesFooted openings b) : FramesFooted openings (save.add b) := by
  unfold ColumnFlow.add
  split
  · exact hb
  · next previous he =>
    exact joinColumn_frames _ _ _ openings (hs.2 previous he) hb

private def FlowFooted (openings : Array FrameOpening) (st : FlowSt) : Prop :=
  FramesFooted openings st.placed.b ∧ ∀ save ∈ st.columns, save.footed openings

private theorem stepFlow_frames (fs : FontSet) (imgs : Image.Store)
    (st : FlowSt) (op : Op) (openings : Array FrameOpening)
    (h : FlowFooted openings st) (ho : ∀ f ∈ op.frameOpening?, f ∈ openings) :
    FlowFooted openings (stepFlow fs imgs st op) := by
  cases op with
  | colOpen pos =>
    have hp := stepStaged_frames fs imgs st.placed (.colOpen pos) openings h.1 ho
    refine ⟨hp, ?_⟩
    simp only [stepFlow, List.forall_mem_cons]
    exact ⟨⟨hp, by simp⟩, h.2⟩
  | colNext =>
    cases hc : st.columns with
    | nil =>
      simp only [stepFlow, hc, FlowFooted]
      exact ⟨stepStaged_frames fs imgs st.placed .colNext openings h.1 ho, by simp⟩
    | cons save rest =>
      have hs := h.2 save (hc ▸ List.mem_cons_self)
      have hr : ∀ s ∈ rest, s.footed openings := fun s hm =>
        h.2 s (hc ▸ List.mem_cons_of_mem _ hm)
      simp only [stepFlow, hc]
      split
      · exact ⟨stepStaged_frames fs imgs st.placed .colNext openings h.1 ho,
          by simpa only [hc] using h.2⟩
      · refine ⟨hs.1.step (frameStep_restartColumn ..), ?_⟩
        simp only [List.forall_mem_cons, ColumnFlow.footed, Option.mem_some]
        exact ⟨⟨hs.1, fun _ he =>
          he ▸ save.add_frames st.placed.b openings hs h.1⟩, hr⟩
  | colClose =>
    cases hc : st.columns with
    | nil =>
      simp only [stepFlow, hc, FlowFooted]
      exact ⟨stepStaged_frames fs imgs st.placed .colClose openings h.1 ho, by simp⟩
    | cons save rest =>
      have hs := h.2 save (hc ▸ List.mem_cons_self)
      have hb : FramesFooted openings (columnEnd save st.placed).b :=
        save.add_frames st.placed.b openings hs h.1
      simp only [stepFlow, hc, FlowFooted]
      refine ⟨stepStaged_frames fs imgs (columnEnd save st.placed) .colClose openings hb ho, ?_⟩
      exact fun s hm => h.2 s (hc ▸ List.mem_cons_of_mem _ hm)
  | _ => exact ⟨stepStaged_frames fs imgs st.placed _ openings h.1 ho, h.2⟩

private theorem placeFlowFrom_frames (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : FlowSt) (si : Nat) (openings : Array FrameOpening)
    (ho : ∀ op ∈ staged, ∀ f ∈ op.frameOpening?, f ∈ openings)
    (hs : FlowFooted openings st) :
    FlowFooted openings (placeFlowFrom fs imgs staged st si) := by
  rw [placeFlowFrom]
  split
  · rename_i hi
    have hj : si + 1 ≤ matchingClose staged (si + 1) 1 :=
      matchingClose_ge staged (si + 1) 1
    split
    · have hgroup : ∀ op ∈ staged.extract (si + 1) (matchingClose staged (si + 1) 1),
          ∀ f ∈ op.frameOpening?, f ∈ openings := by
        intro op hop
        obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.mp hop
        exact ho _ (Array.getElem_mem (by omega))
      exact placeFlowFrom_frames _ _ _ _ _ openings ho
        ⟨runFloat_frames fs imgs st.placed _ openings hs.1 hgroup, hs.2⟩
    · apply placeFlowFrom_frames _ _ _ _ _ openings ho
        (stepFlow_frames fs imgs st _ openings hs ?_)
      rw [keepAt_frameOpening]
      exact ho _ (Array.getElem_mem hi)
  · exact hs
termination_by staged.size - si
decreasing_by all_goals omega

private theorem placeFrom_frames (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : StepSt) (si : Nat) (openings : Array FrameOpening)
    (ho : ∀ op ∈ staged, ∀ f ∈ op.frameOpening?, f ∈ openings)
    (hs : FramesFooted openings st.b) :
    FramesFooted openings (placeFrom fs imgs staged st si).b :=
  (placeFlowFrom_frames fs imgs staged { placed := st } si openings ho
    ⟨hs, by simp⟩).1


private def ReflowStep (a b : B) : Prop :=
  b.paragraphBreaks = a.paragraphBreaks ∧ ∀ d ∈ a.diags, d ∈ b.diags

private theorem ReflowStep.refl (b : B) : ReflowStep b b :=
  ⟨rfl, fun _ h => h⟩

private theorem ReflowStep.of_eq {a b : B}
    (hp : b.paragraphBreaks = a.paragraphBreaks) (hd : b.diags = a.diags) :
    ReflowStep a b :=
  ⟨hp, fun _ h => hd ▸ h⟩

private theorem ReflowStep.trans {a b c : B}
    (hab : ReflowStep a b) (hbc : ReflowStep b c) : ReflowStep a c :=
  ⟨hbc.1.trans hab.1, fun d hd => hbc.2 d (hab.2 d hd)⟩

private theorem ReflowStep.keepInk {a b : B} (h : ReflowStep a b) (d : Sp) :
    ReflowStep a (b.keepInk d) :=
  h.trans (ReflowStep.of_eq rfl rfl)

private theorem ReflowStep.displayState {a b : B} (h : ReflowStep a b)
    (tex : Bool) (e : Option Sp) : ReflowStep a (b.displayState tex e) :=
  h.trans (ReflowStep.of_eq rfl rfl)

private def Spacing.Page.ReflowsNamed (b : B) : Prop :=
  Layout.ReflowsNamed b.paragraphBreaks b.diags

private theorem Spacing.Page.ReflowsNamed.step {a b : B} (ha : a.ReflowsNamed)
    (h : ReflowStep a b) : b.ReflowsNamed := by
  intro p hp k hk
  rw [h.1] at hp
  obtain ⟨d, hd, hc, hs⟩ := ha p hp k hk
  exact ⟨d, h.2 d hd, hc, hs⟩

@[simp] private theorem attachNotes_paragraphBreaks (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).paragraphBreaks = b.paragraphBreaks := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction
      (motive := fun _ (acc : B) => acc.paragraphBreaks = b.paragraphBreaks)
      rfl (fun _ _ h => h)

@[simp] private theorem attachNotes_diags (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).diags = b.diags := by
  unfold Spacing.Page.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.diags = b.diags)
      rfl (fun _ _ h => h)

private theorem reflowStep_attachNotes (b : B) (ns : Array NoteBlock) :
    ReflowStep b (b.attachNotes ns) :=
  ReflowStep.of_eq (attachNotes_paragraphBreaks ..) (attachNotes_diags ..)

private theorem reflowStep_finishPage (b : B) (owed : Sp) (flush : Bool) :
    ReflowStep b (b.finishPage owed flush) := by
  refine ⟨rfl, ?_⟩
  intro d hd
  simp only [Spacing.Page.finishPage]
  split
  · exact Array.mem_push.mpr (Or.inl hd)
  · exact hd

@[simp] private theorem reopenChrome_paragraphBreaks (b : B) :
    b.reopenChrome.paragraphBreaks = b.paragraphBreaks := by
  unfold Spacing.Page.reopenChrome
  split <;> rfl

@[simp] private theorem reopenChrome_diags (b : B) :
    b.reopenChrome.diags = b.diags := by
  unfold Spacing.Page.reopenChrome
  split <;> rfl

private theorem reflowStep_warnSpill (b : B) (over : Sp) :
    ReflowStep b (b.warnSpill over) := by
  unfold Spacing.Page.warnSpill
  repeat' split
  all_goals first
    | exact ⟨rfl, fun _ h => Array.mem_push.mpr (Or.inl h)⟩
    | exact ⟨rfl, fun _ h => h⟩
    | exact ReflowStep.refl b

private theorem reflowStep_spillPage (b : B) (over : Sp) :
    ReflowStep b (b.spillPage over) :=
  (reflowStep_finishPage b 0 b.flushes).trans
    ((ReflowStep.of_eq (reopenChrome_paragraphBreaks ..) (reopenChrome_diags ..)).trans
      ((reflowStep_warnSpill ..).trans (ReflowStep.of_eq rfl rfl)))

@[simp] private theorem pushSibling_paragraphBreaks (b : B) (l : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp) (fils : Option Nat) :
    (b.pushSibling l fills inks shrink fils).paragraphBreaks = b.paragraphBreaks := by
  cases l <;> simp only [Spacing.Page.pushSibling] <;> split <;> rfl

@[simp] private theorem pushSibling_diags (b : B) (l : Option LineOut)
    (fills : Array Fill) (inks : Array InkOut) (shrink : Option Sp) (fils : Option Nat) :
    (b.pushSibling l fills inks shrink fils).diags = b.diags := by
  cases l <;> simp only [Spacing.Page.pushSibling] <;> split <;> rfl

@[simp] private theorem pushLabels_paragraphBreaks (b : B) (ls : Array LineOut)
    (shrink : Sp) (fils : Nat) :
    (b.pushLabels ls shrink fils).paragraphBreaks = b.paragraphBreaks := by
  unfold Spacing.Page.pushLabels
  exact Array.foldl_induction
    (motive := fun _ (acc : B) => acc.paragraphBreaks = b.paragraphBreaks)
    rfl (fun _ _ h => by rw [pushSibling_paragraphBreaks]; exact h)

@[simp] private theorem pushLabels_diags (b : B) (ls : Array LineOut)
    (shrink : Sp) (fils : Nat) :
    (b.pushLabels ls shrink fils).diags = b.diags := by
  unfold Spacing.Page.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.diags = b.diags)
    rfl (fun _ _ h => by rw [pushSibling_diags]; exact h)

private theorem reflowStep_commit (b : B) (l : LineOut) (depth below : Sp)
    (ruleLine consume : Bool) (overflow : Sp) :
    ReflowStep b (b.commit l depth below ruleLine consume overflow) :=
  ReflowStep.of_eq rfl rfl

private theorem reflowStep_warnNoteOverrun (b : B) (y depth : Sp) :
    ReflowStep b (b.warnNoteOverrun y depth) := by
  simp only [Spacing.Page.warnNoteOverrun]
  split
  · exact ⟨rfl, fun _ h => Array.mem_push.mpr (Or.inl h)⟩
  · exact ReflowStep.refl b

private theorem reflowStep_noteOverrun (b : B) (o : Sp) : ReflowStep b (b.noteOverrun o) :=
  ReflowStep.of_eq (by simp) (by simp)

private theorem reflowStep_fitWith (b : B) (place : B → Sp → Bool → Sp → B)
    (settle : B → Sp → Sp → B) (firstY stepY retryY : B → Sp) (inkBelow bottom : Sp)
    (holdsBlank : Bool) (hp : ∀ b y c o, ReflowStep b (place b y c o))
    (hs : ∀ b y d, ReflowStep b (settle b y d)) :
    ReflowStep b (b.fitWith place settle firstY stepY retryY inkBelow bottom holdsBlank) := by
  simp only [Spacing.Page.fitWith]
  split
  · exact (hp ..).trans (hs ..)
  · split
    · exact hp ..
    · split
      · exact (hp ..).trans (reflowStep_noteOverrun ..)
      · refine ReflowStep.trans ?_ (reflowStep_noteOverrun ..)
        split <;> exact (reflowStep_spillPage b _).trans ((hp ..).trans (hs ..))

private theorem reflowStep_fitCommit (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) :
    ReflowStep b (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns) :=
  reflowStep_fitWith b _ _ firstY stepY retryY inkBelow bottom true
    (fun _ _ _ _ => (reflowStep_commit ..).trans (reflowStep_attachNotes ..))
    fun _ _ _ => reflowStep_warnNoteOverrun ..

private theorem reflowStep_placeAnchor (fs : FontSet) (b : B) (h : AnchorRule) (shift : Sp)
    (paints : Bool) : ReflowStep b (b.placeAnchor fs h shift paints) := by
  simp only [Spacing.Page.placeAnchor]
  split
  · apply ReflowStep.keepInk
    exact reflowStep_fitCommit ..
  · exact ReflowStep.of_eq rfl rfl

private theorem reflowStep_placeLine (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (firstBaseline : Option Sp) (dj : Option DisplayJob) (op : Bool)
    (anchors : Array String) (paintPadding : Option Sp) (step : Option Sp) (rs : Option (Sp × Sp)) (strut : Option Sp) :
    ReflowStep b
      (b.placeLine fs x size segs w hang ex ns c lf firstBaseline dj op anchors paintPadding
        step rs strut) := by
  simp only [Spacing.Page.placeLine]
  apply ReflowStep.displayState
  apply ReflowStep.keepInk
  exact reflowStep_fitCommit ..

private theorem reflowStep_warnOverfull (b : B) (source : Option Span) :
    ReflowStep b (b.warnOverfull source) :=
  ⟨rfl, fun _ h => Array.mem_push.mpr (Or.inl h)⟩

private theorem reflowStep_openDisplayAt (b : B) (j : ParaJob) (first : Bool)
    (x : Sp) (segs : Array Seg) :
    ReflowStep b (b.openDisplayAt j first x segs) := by
  unfold Spacing.Page.openDisplayAt
  split <;> exact ReflowStep.of_eq rfl rfl

private theorem reflowStep_placeParaTrailer (fs : FontSet) (j : ParaJob) (k : Nat)
    (segs : Array Seg) (b : B) : ReflowStep b (placeParaTrailer fs j k segs b) := by
  unfold placeParaTrailer reachDepth
  repeat' split
  all_goals exact ReflowStep.of_eq rfl rfl

private theorem reflowStep_withPendingSource (b : B) (source : Option Span) :
    ReflowStep b (b.withPendingSource source) := ReflowStep.of_eq rfl rfl

private theorem reflowStep_placeParaLine (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) :
    ReflowStep st.1 (placeParaLine fs j st brk).1 := by
  simp only [placeParaLine]
  refine ReflowStep.trans (ReflowStep.trans (ReflowStep.trans (ReflowStep.trans ?_
    (reflowStep_openDisplayAt ..)) (reflowStep_withPendingSource ..))
    (reflowStep_placeLine ..)) (reflowStep_placeParaTrailer ..)
  split
  · exact reflowStep_warnOverfull ..
  · exact ReflowStep.refl _

private theorem reflowStep_paraLines (fs : FontSet) (j : ParaJob)
    (breaks : Array Nat) (st : B × Nat × Bool) :
    ReflowStep st.1 (breaks.foldl (placeParaLine fs j) st).1 :=
  Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) => ReflowStep st.1 acc.1)
    (ReflowStep.refl _) (fun _ _ h => h.trans (reflowStep_placeParaLine ..))

private theorem placePara_breaks_exact (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) :
    (placePara fs b j breaks).paragraphBreaks =
      b.paragraphBreaks.push (paragraphRecord b j breaks) :=
  (reflowStep_paraLines ..).1

private theorem reflowStep_warnReflow (b : B) (q : ParagraphBreaks) (split : Bool) :
    ReflowStep b (b.warnReflow q split) := by
  unfold Spacing.Page.warnReflow
  split
  · exact ⟨rfl, fun _ h => Array.mem_push.mpr (Or.inl h)⟩
  · exact ReflowStep.refl b

private theorem warnReflow_diag (b : B) (q : ParagraphBreaks) :
    ∃ d ∈ (b.warnReflow q true).diags, d.code = "W0386" ∧ d.subject = some q.subject := by
  unfold Spacing.Page.warnReflow
  exact ⟨_, Array.mem_push_self, rfl, rfl⟩

private theorem placePara_reflows (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) (hb : b.ReflowsNamed) :
    (placePara fs b j breaks).ReflowsNamed := by
  let p := paragraphRecord b j breaks
  let start := ({ b with diags := b.diags ++ j.diags }).warnReflow p (!p.reflows.isEmpty)
  have appended : ReflowStep b { b with diags := b.diags ++ j.diags } :=
    ⟨rfl, fun _ h => Array.mem_append.mpr (Or.inl h)⟩
  have old : start.ReflowsNamed :=
    hb.step (appended.trans (reflowStep_warnReflow ..))
  have startBreaks : start.paragraphBreaks = b.paragraphBreaks :=
    (reflowStep_warnReflow ..).1
  have named : ({ start with paragraphBreaks := b.paragraphBreaks.push p } : B).ReflowsNamed := by
    intro q hq k hk
    rcases Array.mem_push.mp hq with hq | rfl
    · exact old q (startBreaks.symm ▸ hq) k hk
    · have hm : k ∈ p.reflows := (ParagraphBreaks.reflows_mem p k).mpr hk
      have he : (!p.reflows.isEmpty) = true := by
        rw [Bool.not_eq_true', Array.isEmpty_eq_false_iff_exists_mem]
        exact ⟨k, hm⟩
      change ∃ d ∈ (({ b with diags := b.diags ++ j.diags }).warnReflow p
          (!p.reflows.isEmpty)).diags,
          d.code = "W0386" ∧ d.subject = some p.subject
      rw [he]
      exact warnReflow_diag { b with diags := b.diags ++ j.diags } p
  exact named.step (reflowStep_paraLines fs (placedJob fs b j breaks) breaks (_, 0, true))

private theorem reflowStep_placePicture (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (origin : Nat) :
    ReflowStep b (placePicture fs imgs b x pic leaf origin) := by
  simp only [placePicture]
  exact reflowStep_fitWith b _ _ _ _ _ _ _ _
    (fun _ _ _ _ => ⟨by simp, fun _ hd => by simpa using Array.mem_append_left _ hd⟩)
    fun _ _ _ => ReflowStep.refl _

private theorem reflowStep_keepHeading (b : B) (j : ParaJob) (n : Nat) :
    ReflowStep b (b.keepHeading j n) := by
  unfold Spacing.Page.keepHeading
  split
  · exact reflowStep_spillPage b 0
  · exact ReflowStep.refl b

private theorem reflowStep_placeSlot (fs : FontSet) (b : B) (save : ColSave × Nat × Nat × Nat)
    (spec : SlotSpec) : ReflowStep b (b.placeSlot fs save spec) := by
  obtain ⟨col, l0, f0, k0⟩ := save
  simp only [Spacing.Page.placeSlot]
  split <;> exact ReflowStep.of_eq rfl rfl

private theorem reflowStep_alignRow (b : B) (save : ColSave) :
    ReflowStep b (b.alignRow save) := by
  refine ReflowStep.of_eq ?_ ?_ <;> simp [Spacing.Page.alignRow]

private theorem stepStaged_reflows (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (op : Op) (hb : st.b.ReflowsNamed) :
    (stepStaged fs imgs st op).b.ReflowsNamed := by
  cases op
  case regionClose =>
    rw [stepStaged_regionClose_b]
    exact hb.step (ReflowStep.of_eq (closeRegion_shipped_id fs st.b).2.2.2.2.2.1
      (closeRegion_shipped_id fs st.b).2.2.2.2.2.2)
  case boxAnchor h shift paints =>
    rw [stepStaged_boxAnchor_b]
    exact hb.step (reflowStep_placeAnchor ..)
  case hrule color th =>
    rw [stepStaged_hrule_b]
    exact hb.step (reflowStep_placeLine ..)
  case tableRule th x w segs =>
    rw [stepStaged_tableRule_b]
    exact hb.step (reflowStep_fitCommit ..)
  case para j task =>
    rw [stepStaged_para_b]
    exact placePara_reflows _ _ _ _ (hb.step (reflowStep_keepHeading ..))
  case picture x pic leaf origin =>
    rw [stepStaged_picture_b]
    exact hb.step (reflowStep_placePicture ..)
  all_goals simp only [stepStaged, Id.run, Id, pure, Spacing.Page.openBody] <;> repeat' split
  all_goals first
    | (refine hb.step (ReflowStep.of_eq ?_ ?_) <;> simp
       done)
    | exact hb.step (reflowStep_placeSlot ..)
    | exact hb.step ((ReflowStep.of_eq rfl rfl).trans (reflowStep_alignRow ..))
    | (refine hb.step ((reflowStep_finishPage _ st.b.closingOwed false).trans
        (ReflowStep.of_eq ?_ ?_)) <;> simp
       done)

private theorem foldSteps_reflows (fs : FontSet) (imgs : Image.Store)
    (group : Array Op) (st : StepSt) (hb : st.b.ReflowsNamed) :
    (group.foldl (stepStaged fs imgs) st).b.ReflowsNamed :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => acc.b.ReflowsNamed)
    hb (fun _ _ h => stepStaged_reflows _ _ _ _ h)

private theorem runFloat_reflows (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (group : Array Op) (hb : st.b.ReflowsNamed) :
    (runFloat fs imgs st group).b.ReflowsNamed := by
  have finish : ∀ (b : B) (c : Prop) [Decidable c] (d : Diag), b.ReflowsNamed →
      ({ (if c then { b with diags := b.diags.push d } else b) with
          noBreak := false } : B).ReflowsNamed := by
    intro b c inst d h
    split
    · exact h.step ⟨rfl, fun _ hm => Array.mem_push.mpr (Or.inl hm)⟩
    · exact h.step (ReflowStep.of_eq rfl rfl)
  simp only [LeanTex.Core.Layout.runFloat]
  split
  · exact foldSteps_reflows fs imgs group st hb
  · have hc : (if st.b.cur.blank
        then st.b else st.b.finishPage).ReflowsNamed := by
      split
      · exact hb
      · exact hb.step (reflowStep_finishPage ..)
    have hr := foldSteps_reflows fs imgs group
      { st with b :=
        { (if st.b.cur.blank then st.b
           else st.b.finishPage) with noBreak := true } }
      (hc.step (ReflowStep.of_eq rfl rfl))
    exact finish _ _ _ hr

private theorem reflowStep_restartColumn (start latest : B) :
    ReflowStep latest (restartColumn start latest) :=
  ReflowStep.of_eq rfl rfl

private theorem reflowStep_joinColumn (first : Nat) (a b : B) :
    ReflowStep b (joinColumn first a b) :=
  ⟨rfl, fun _ h => Array.mem_append.mpr (Or.inl (Array.mem_append.mpr (Or.inl h)))⟩

private theorem reflowStep_columnAdd (save : ColumnFlow) (b : B) :
    ReflowStep b (save.add b) := by
  unfold ColumnFlow.add
  split
  · exact ReflowStep.refl b
  · exact reflowStep_joinColumn ..

private theorem stepFlow_reflows (fs : FontSet) (imgs : Image.Store)
    (st : FlowSt) (op : Op) (hb : st.placed.b.ReflowsNamed) :
    (stepFlow fs imgs st op).placed.b.ReflowsNamed := by
  unfold stepFlow
  split
  · exact stepStaged_reflows _ _ _ _ hb
  · split
    · exact stepStaged_reflows _ _ _ _ hb
    · exact hb.step (reflowStep_restartColumn ..)
  · exact stepStaged_reflows _ _ _ _ (hb.step (reflowStep_columnAdd ..))
  · exact stepStaged_reflows _ _ _ _ hb

private theorem placeFlowFrom_reflows (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : FlowSt) (si : Nat)
    (hb : st.placed.b.ReflowsNamed) :
    (placeFlowFrom fs imgs staged st si).placed.b.ReflowsNamed := by
  rw [placeFlowFrom]
  split
  · have hj : si + 1 ≤ matchingClose staged (si + 1) 1 :=
      matchingClose_ge staged (si + 1) 1
    split
    · exact placeFlowFrom_reflows _ _ _ _ _ (runFloat_reflows _ _ _ _ hb)
    · exact placeFlowFrom_reflows _ _ _ _ _ (stepFlow_reflows _ _ _ _ hb)
  · exact hb
termination_by staged.size - si
decreasing_by all_goals omega

private theorem placeFrom_reflows (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : StepSt) (si : Nat) (hb : st.b.ReflowsNamed) :
    (placeFrom fs imgs staged st si).b.ReflowsNamed :=
  placeFlowFrom_reflows fs imgs staged { placed := st } si hb

private theorem placeFlowFrom_ground (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : FlowSt) (si : Nat) {g : Geom} {d : Bool}
    (hg : ∀ op ∈ staged, op.preservesGround = true) (hs : FlowGround g d st) :
    FlowGround g d (placeFlowFrom fs imgs staged st si) := by
  rw [placeFlowFrom]
  split
  · rename_i h
    have hj : si + 1 ≤ matchingClose staged (si + 1) 1 :=
      matchingClose_ge staged (si + 1) 1
    split
    · have hgroup : ∀ op ∈ staged.extract (si + 1) (matchingClose staged (si + 1) 1),
          op.preservesGround = true := by
        intro op hop
        obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.mp hop
        exact hg _ (Array.getElem_mem (by omega))
      exact placeFlowFrom_ground _ _ _ _ _ hg
        ⟨hs.1.step (bgStep_runFloat fs imgs st.placed _ hgroup), hs.2⟩
    · apply placeFlowFrom_ground _ _ _ _ _ hg (stepFlow_ground fs imgs st _ hs ?_)
      rw [keepAt_preservesGround]
      exact hg _ (Array.getElem_mem h)
  · exact hs
termination_by staged.size - si
decreasing_by all_goals omega

private theorem bgStep_placeFrom (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (st : StepSt) (si : Nat)
    (hg : ∀ op ∈ staged, op.preservesGround = true)
    (hp : st.b.docBg.isSome = true → ∀ p ∈ st.b.pages, bgFilled st.b.geom p) :
    BgStep st.b (placeFrom fs imgs staged st si).b := by
  have h := (placeFlowFrom_ground fs imgs staged { placed := st } si hg
    ⟨⟨rfl, fun hd => ⟨hd, hp hd⟩⟩, by simp⟩).1
  exact ⟨h.1, fun hd => (h.2 hd).1,
    fun hd p hm => Or.inr ((h.2 hd).2 p hm)⟩

private theorem runFloat_whole (fs : FontSet) (imgs : Image.Store) (st : StepSt)
    (group : Array Op) (hg : ∀ s ∈ group, s ≠ Op.brk) :
    (runFloat fs imgs st group).b.pages = st.b.pages ∨
    (runFloat fs imgs st group).b.pages = st.b.finishPage.pages := by
  simp only [runFloat]
  split
  ·
    next hsize =>
    left
    obtain ⟨s, hs⟩ := foldSteps_extends fs imgs group st
    have hlen : (group.foldl (stepStaged fs imgs) st).b.pages.size
        = st.b.pages.size := by simpa using hsize
    rw [hs] at hlen ⊢
    simp only [Array.size_append] at hlen
    have hz : s = #[] := by
      rw [← Array.size_eq_zero_iff]; omega
    simp [hz]
  ·
    have hfold := foldSteps_noBreak fs imgs group
      { st with b :=
        { (if st.b.cur.blank then st.b
           else st.b.finishPage) with noBreak := true } } rfl hg
    split at hfold
    · left
      repeat' split
      all_goals simp_all
    · right
      repeat' split
      all_goals simp_all

/-- The placement result before the furniture pass, with the context that pass reads. -/
public structure Shipped where
  pages : Array PageOut
  footGap : Sp
  /-- The overflow ladder's records (`Out.overruns`, `Out.needs`,
  `Out.spilled`). -/
  overruns : Array (FrameOrigin × Sp × Sp) := #[]
  needs : Array (FrameOrigin × Sp) := #[]
  spilled : Array FrameOrigin := #[]
  /-- The diagnostics as of shipping, the builder's own and the measure band's. -/
  diags : Array Diag
  paragraphBreaks : Array ParagraphBreaks := #[]
  labelRequests : Array LabelAudit.Request := #[]
  doc : Doc
  geom : Geom
  xHeight : Sp
  pats : Option Hyphen.Patterns
  fs : FontSet
  imgs : Image.Store
  hyphCache : Std.HashMap String (Array Nat)
  navEntries : Array (String × String)
  logoSpans : Array (Nat × Array Ir.Inline)
  plainFoot : Bool
  footSize : Sp
  headY : Sp
  footY : Sp
  muted : Ir.Color

/-- The furniture pass's spine: page `i` gains the
running lines its step computes, and only lines. -/
private def furnishFrom {σ : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (pages : Array PageOut) (s : σ) (i : Nat) : Array PageOut × σ :=
  if h : i < pages.size then
    let (ls, s') := f i pages[i] s
    furnishFrom f (pages.set i { pages[i] with lines := ls }) s' (i + 1)
  else (pages, s)
termination_by pages.size - i
decreasing_by simp only [Array.size_set]; omega

private theorem furnishFrom_preserves {σ α : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (read : PageOut → α)
    (hread : ∀ i p s, read { p with lines := (f i p s).1 } = read p)
    (pages : Array PageOut) (s : σ) (i : Nat) :
    (furnishFrom f pages s i).1.map read = pages.map read := by
  induction pages, s, i using furnishFrom.induct f with
  | case1 pages s i h ls s' heq ih =>
    have hr := hread i pages[i] s
    rw [heq] at hr
    rw [furnishFrom]
    simp only [h, reduceDIte, heq]
    rw [ih]
    apply Array.ext
    · simp
    · intro j hj hj'
      simp only [Array.getElem_map, Array.getElem_set]
      split <;> simp_all
  | case2 pages s i h =>
    rw [furnishFrom]
    simp only [h, reduceDIte]

private theorem furnishFrom_projects {σ α : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (read : PageOut → α)
    (hread : ∀ p ls, read { p with lines := ls } = read p)
    (pages : Array PageOut) (s : σ) (i : Nat) :
    (furnishFrom f pages s i).1.map read = pages.map read :=
  furnishFrom_preserves f read (fun _ p _ => hread p _) pages s i

private theorem furnishFrom_inv {σ : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (P : σ → Prop) (hstep : ∀ i p s, P s → P (f i p s).2)
    (pages : Array PageOut) (s : σ) (i : Nat) (hs : P s) :
    P (furnishFrom f pages s i).2 := by
  induction pages, s, i using furnishFrom.induct f with
  | case1 pages s i h ls s' heq ih =>
    rw [furnishFrom]
    simp only [h, reduceDIte, heq]
    apply ih
    simpa only [heq] using hstep i pages[i] s hs
  | case2 pages s i h =>
    rw [furnishFrom]
    simpa only [h, reduceDIte] using hs

private theorem furnishFrom_keeps {σ : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (pages : Array PageOut) (s : σ) (i : Nat) :
    ∀ p ∈ (furnishFrom f pages s i).1, ∃ q ∈ pages,
      p.fills = q.fills ∧ p.links = q.links ∧ p.inks = q.inks ∧ p.foot = q.foot ∧
        p.frame = q.frame := by
  intro p hp
  let read := fun p : PageOut => (p.fills, p.links, p.inks, p.foot, p.frame)
  have h := furnishFrom_projects f read (fun _ _ => rfl) pages s i
  have hm : read p ∈ pages.map read := h ▸ Array.mem_map_of_mem hp
  obtain ⟨q, hq, heq⟩ := Array.mem_map.mp hm
  exact ⟨q, hq, by simpa only [read, Prod.mk.injEq] using heq.symm⟩

/-- A generated furniture line, with no body leaf or counted-line identity. -/
private def furnitureLine (l : LineOut) : LineOut :=
  { l with furniture := true, leaf := none, counted := false }

/-- A page's lines: the running head, the body in order, then numbers, footers and logos. -/
private def furnishLines (fs : FontSet) (before body after : Array LineOut) : Array LineOut :=
  paintLines fs (before.map furnitureLine ++ body ++ after.map furnitureLine)

private theorem furnishLines_attributed_projects (fs : FontSet)
    (before body after : Array LineOut) :
    (furnishLines fs before body after).filter (fun l => l.leaf.isSome) =
      body.filter (fun l => l.leaf.isSome) := by
  unfold furnishLines
  rw [paintLines_attributed_projects]
  apply Array.toList_inj.mp
  have hempty (ls : List LineOut) : ls.filter (fun _ => false) = [] := by simp
  simp [List.filter_map, Function.comp_def, furnitureLine, hempty]

private theorem furnishLines_counted_projects (fs : FontSet)
    (before body after : Array LineOut) :
    (furnishLines fs before body after).filter (·.counted) = body.filter (·.counted) := by
  unfold furnishLines
  rw [paintLines_counted_projects]
  apply Array.toList_inj.mp
  have hempty (ls : List LineOut) : ls.filter (fun _ => false) = [] := by simp
  simp [List.filter_map, Function.comp_def, furnitureLine, hempty]

/-- One furniture step, joining the setter's lines and diagnostics to the page's. -/
private def furnishStep {σ : Type} (fs : FontSet)
    (f : Nat → PageOut → σ → (Array LineOut × Array LineOut) × Array Diag × σ)
    (i : Nat) (page : PageOut) (s : Array Diag × σ) : Array LineOut × Array Diag × σ :=
  let out := f i page s.2
  (furnishLines fs out.1.1 page.lines out.1.2, s.1 ++ out.2.1, out.2.2)

private theorem sourceBound_furnishLines {n : Nat} (fs : FontSet)
    (before body after : Array LineOut)
    (h : ∀ l ∈ body, l.furniture = false → l.SourceBound n) :
    ∀ l ∈ furnishLines fs before body after,
      l.furniture = false → l.SourceBound n := by
  apply sourceBound_paintLines
  intro l hl hf
  rcases Array.mem_append.mp hl with hl | hl
  · rcases Array.mem_append.mp hl with hl | hl
    · obtain ⟨r, hr, rfl⟩ := Array.mem_map.mp hl
      simp [furnitureLine] at hf
    · exact h l hl hf
  · obtain ⟨r, hr, rfl⟩ := Array.mem_map.mp hl
    simp [furnitureLine] at hf

private theorem furnishFrom_pagesInv {σ : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (P : PageOut → Prop)
    (hstep : ∀ i p s, P p → P { p with lines := (f i p s).1 })
    (pages : Array PageOut) (s : σ) (i : Nat)
    (hs : ∀ p ∈ pages, P p) :
    ∀ p ∈ (furnishFrom f pages s i).1, P p := by
  induction pages, s, i using furnishFrom.induct f with
  | case1 pages s i h ls s' heq ih =>
    rw [furnishFrom]
    simp only [h, reduceDIte, heq]
    apply ih
    intro p hp
    rcases Array.mem_or_eq_of_mem_set hp with hp | rfl
    · exact hs p hp
    · have hh := hstep i pages[i] s (hs _ (Array.getElem_mem h))
      simpa only [heq] using hh
  | case2 pages s i h =>
    rw [furnishFrom]
    simpa only [h, reduceDIte] using hs


private abbrev DiagKey :=
  String × String × Option String × Option (String × Nat × Nat ×
    List (Nat × String) × Option String) × Option String

private def diagKey (d : Diag) : DiagKey :=
  (d.code, d.message, d.subject, d.span.map (fun s =>
    (s.file, s.pos.line, s.pos.col, s.pos.origins.map (fun o => (o.id, o.name)), s.pos.command)),
    d.detail)

/-- The one record the unlocated overfull lines collapse into,
worded as their summary with the count in its detail. -/
private def summarizeOverfull (overfull : Nat) (d : Diag) : Diag :=
  if d.code == "W0005" && d.span.isNone && overfull > 1 then
    { d with message := "overfull lines that no source site names; no feasible break"
             detail := some s!"{overfull} overfull lines" }
  else d

/-- Drop repeated reports of one source site, keeping
distinct declarations with their provenance. -/
private def uniqueDiags (diags : Array Diag) : Array Diag := Id.run do
  let overfull := diags.foldl (fun n d =>
    if d.code == "W0005" && d.span.isNone then n + 1 else n) 0
  let mut st : Std.HashSet DiagKey × Array Diag := ({}, #[])
  for d in diags do
    st := if st.1.contains (diagKey d) then st
      else (st.1.insert (diagKey d), st.2.push (summarizeOverfull overfull d))
  return st.2

private def diagReported (diags : Array Diag) (code : String) (subject : Option String) : Prop :=
  ∃ d ∈ diags, d.code = code ∧ d.subject = subject

private theorem push_reported {diags : Array Diag} {code : String} {subject : Option String}
    (d : Diag) (h : diagReported diags code subject) :
    diagReported (diags.push d) code subject := by
  obtain ⟨e, he, hc, hs⟩ := h
  exact ⟨e, Array.mem_push.mpr (Or.inl he), hc, hs⟩

private theorem summarizeOverfull_names (overfull : Nat) (d : Diag) :
    (summarizeOverfull overfull d).code = d.code ∧
    (summarizeOverfull overfull d).subject = d.subject := by
  unfold summarizeOverfull
  split <;> exact ⟨rfl, rfl⟩

private theorem uniqueDiags_covers (diags : Array Diag) :
    ∀ d ∈ diags, diagReported (uniqueDiags diags) d.code d.subject := by
  unfold uniqueDiags
  simp only [Array.forIn_pure_yield_eq_foldl]
  let overfull := diags.foldl (fun n d =>
    if d.code == "W0005" && d.span.isNone then n + 1 else n) 0
  have h := Array.foldl_induction (as := diags)
    (motive := fun i (st : Std.HashSet DiagKey × Array Diag) =>
      (∀ key ∈ st.1, diagReported st.2 key.1 key.2.2.1) ∧
      (∀ d ∈ diags.toList.take i, diagReported st.2 d.code d.subject))
    (init := ({}, #[]))
    (f := fun st d => if st.1.contains (diagKey d) then st
      else (st.1.insert (diagKey d), st.2.push (summarizeOverfull overfull d)))
    (by simp)
    (by
      intro i st hst
      have htake : diags.toList.take (i.val + 1) =
          diags.toList.take i.val ++ [diags[i]] := by
        exact List.take_succ_eq_append_getElem (by simp)
      split
      · rename_i hc
        refine ⟨hst.1, ?_⟩
        intro d hd
        rw [htake] at hd
        rcases List.mem_append.mp hd with hp | hp
        · exact hst.2 d hp
        · have he : d = diags[i] := by simpa using hp
          subst d
          exact hst.1 _ (Std.HashSet.contains_iff_mem.mp hc)
      · refine ⟨?_, ?_⟩
        · intro key hk
          rcases Std.HashSet.mem_insert.mp hk with heq | hold
          · have heq' : diagKey diags[i] = key := eq_of_beq heq
            subst key
            exact ⟨summarizeOverfull overfull diags[i],
              Array.mem_push.mpr (Or.inr rfl), summarizeOverfull_names _ _⟩
          · exact push_reported _ (hst.1 key hold)
        · intro d hd
          rw [htake] at hd
          rcases List.mem_append.mp hd with hp | hp
          · exact push_reported _ (hst.2 d hp)
          · have he : d = diags[i] := by simpa using hp
            subst d
            exact ⟨summarizeOverfull overfull diags[i],
              Array.mem_push.mpr (Or.inr rfl), summarizeOverfull_names _ _⟩)
  have ht : diags.toList.take diags.size = diags.toList := by
    simpa only [Array.length_toList] using (List.take_length (l := diags.toList))
  simpa only [ht, Array.mem_toList_iff, overfull, Id.run, bind, pure, Id] using h.2

/-- Two settings' overruns of one declared line, merged
by rank: the furthest each runs past the measure. -/
private def mergeOverruns (a b : Array Overrun) : Array Overrun := Id.run do
  let mut out : Array Overrun := #[]
  let mut i := 0
  let mut k := 0
  for _ in [0:a.size + b.size] do
    match a[i]?, b[k]? with
    | some x, some y =>
      if x.rank < y.rank then
        out := out.push x
        i := i + 1
      else if y.rank < x.rank then
        out := out.push y
        k := k + 1
      else
        out := out.push (if x.excess < y.excess then
            { y with site := y.site.orElse fun _ => x.site }
          else { x with site := x.site.orElse fun _ => y.site })
        i := i + 1
        k := k + 1
    | some x, none =>
      out := out.push x
      i := i + 1
    | none, some y =>
      out := out.push y
      k := k + 1
    | none, none => break
  return out

/-- One declared line's account across its paragraph's
settings: the most lines any ships, its overruns merged. -/
private def ReflowedLine.mergeWith (a b : ReflowedLine) : ReflowedLine :=
  { a with site := a.site.orElse fun _ => b.site, ships := max a.ships b.ships,
           over := mergeOverruns a.over b.over }

/-- A paragraph's re-flowed declared lines across its settings, merged by rank. -/
private def mergeReflowLines (a b : Array ReflowedLine) : Array ReflowedLine := Id.run do
  let mut out := a
  let mut rank : Std.HashMap Nat Nat := {}
  let mut i := 0
  for l in a do
    rank := rank.insert l.ordinal i
    i := i + 1
  for l in b do
    match rank.get? l.ordinal with
    | some k => out := out.modify k (·.mergeWith l)
    | none =>
      rank := rank.insert l.ordinal out.size
      out := out.push l
  return out.qsort (·.ordinal < ·.ordinal)

/-- The re-flow records the postlude remakes, one per
census key overlay steps of one frame each named. -/
private def reflowsMerged (ps : Array ParagraphBreaks) : Std.HashMap String Diag := Id.run do
  let mut groups : Std.HashMap String
      (Option Nat × Array ReflowedLine × Array (Option FrameOrigin) × Bool) := {}
  for p in ps do
    unless p.lines.isEmpty do
      let s := p.subject
      groups := groups.insert s <| match groups.get? s with
        | some (f, ls, steps, apart) =>
          (f, mergeReflowLines ls p.lines, steps.push p.frame, apart && !steps.contains p.frame)
        | none => (p.frameNumber, p.lines, #[p.frame], p.frame.isSome)
  let mut out : Std.HashMap String Diag := {}
  for (s, f, ls, steps, apart) in groups do
    if apart && steps.size > 1 then out := out.insert s (reflowRecord s f ls)
  return out

/-- A W0386 record as its census key's merged record says it. -/
private def mergeReflow (merged : Std.HashMap String Diag) (d : Diag) : Diag :=
  if d.kind == .W0386 then
    match d.subject.bind merged.get? with
    | some m => { d with message := m.message, span := m.span, detail := m.detail,
                         carries := m.carries }
    | none => d
  else d

private theorem mergeReflow_names (merged : Std.HashMap String Diag) (d : Diag) :
    (mergeReflow merged d).code = d.code ∧ (mergeReflow merged d).subject = d.subject := by
  unfold mergeReflow
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- One report per problem: re-flows merged
(`mergeReflow`), then repeats dropped (`uniqueDiags`). -/
private def reportOnce (ps : Array ParagraphBreaks) (diags : Array Diag) : Array Diag :=
  uniqueDiags (diags.map (mergeReflow (reflowsMerged ps)))

private theorem reportOnce_covers (ps : Array ParagraphBreaks) (diags : Array Diag) :
    ∀ d ∈ diags, diagReported (reportOnce ps diags) d.code d.subject := by
  intro d hd
  obtain ⟨e, he, hc, hs⟩ :=
    uniqueDiags_covers _ _ (Array.mem_map_of_mem (f := mergeReflow (reflowsMerged ps)) hd)
  exact ⟨e, he, hc.trans (mergeReflow_names _ d).1, hs.trans (mergeReflow_names _ d).2⟩

/-- The postlude: running furniture per page (`furnishFrom`),
one report per problem, and the resolved outline. -/
public def runPost (sh : Shipped) : Out := Id.run do
  let doc := sh.doc
  let geom := sh.geom
  let xHeight := sh.xHeight
  let pats := sh.pats
  let fs := sh.fs
  let imgs := sh.imgs
  let footSize := sh.footSize
  let plainFoot := sh.plainFoot
  let logoSpans := sh.logoSpans
  let headY := sh.headY
  let footY := sh.footY
  let mutedC := sh.muted
  let pages := sh.pages
  -- Running content is laid out per page once the count is known, into the margin.
  let total := pages.size
  let furnGround := Ir.Design.declared? doc.palette .page
  -- Margin line numbers: muted furniture at the footnotesize step, left of the measure.
  let lineNumbersOn := doc.lineNumbersOn
  let lineModulo := doc.lineModulo
  let numSize := Ir.scaleStep geom.fontSize "footnotesize"
  let numRight := match doc.page.furnitureGap with
    | some g => geom.hmargin - g
    | none => geom.hmargin / 2
  let runLine (content : Array Inline) (n : Nat) (y size : Sp) (baseStyle : TextStyle)
      (cache : _) :
      Option LineOut × Array Diag × _ :=
    let sub := substPage n total content
    let (items, ds, cache, _) :=
      itemsOfInlines pats size xHeight fs { baseStyle with ground := furnGround } sub cache
        (.fixed .unattributed) imgs geom.textWidth geom.textHeight (ladder := geom.scale)
    let target := geom.textWidth
    let breaks := kp items target
    -- A running line is one line by construction; content that wraps is named (W0328).
    let ds := if breaks.size > 1 then ds.push (Diag.of .W0328
        "running content wraps at the text width; only its first line is kept"
        (help := "the head, foot, and chrome bands hold one line each: shorten the content"))
      else ds
    match breaks[0]? with
    | none => (none, ds, cache)
    | some brk =>
      -- A running line's leading fill is content, so only leading interword space is skipped.
      let start := Id.run do
        let mut k := 0
        for _ in [0:items.size] do
          match items[k]? with
          | some (Item.glue g) => if g.fil then break else k := k + 1
          | _ => break
        return k
      let (segs, w, _) := setLine items start brk target true
      (some { x := geom.hmargin, y := y, size := size, segs := segs,
              setWidth := w }, ds, cache)
  -- A band slot is its own line, placed by its side and the paper's edge alone (`bandSlotX`).
  let slotLine (side : Ir.BandSide) (content : Array Inline) (n : Nat)
      (y : Sp) (baseStyle : TextStyle) (cache : _) :
      Option LineOut × Array Diag × _ :=
    let (set?, wraps, ds, cache) := setBandSlot pats fs imgs geom xHeight
      { baseStyle with ground := baseStyle.ground.or furnGround } (substPage n total content) cache
    let ds := if wraps then ds.push (Diag.of .W0328
        "running content wraps at the text width; only its first line is kept"
        (help := "the head, foot, and chrome bands hold one line each: shorten the content"))
      else ds
    match set? with
    | none => (none, ds, cache)
    | some (segs, w) =>
      (some { x := bandSlotX geom side w, y := y, size := footSize, segs := segs,
              setWidth := w }, ds, cache)
  -- The logo: the preamble `\logo` is the initial state; a body `\logo` changes it onward.
  let mkLogoLine (content : Array Inline) (textH : Sp) (cache0 : Std.HashMap String (Array Nat)) :
      Option LineOut × Array Diag × Std.HashMap String (Array Nat) :=
    let (items, ds, c, _) :=
      itemsOfInlines pats geom.fontSize xHeight fs { ground := furnGround } content cache0
        (.fixed .unattributed) imgs geom.textWidth textH (ladder := geom.scale)
    let breaks := kp items geom.textWidth
    match breaks[0]? with
    | none => (none, ds, c)
    | some brk =>
      let (segs, w, _) := setLine items (lineStart items 0) brk geom.textWidth false
      let x := match Ir.logoAlign doc.styles with
        | .left => geom.hmargin
        | .center => (geom.pageW - w) / 2
        | .right => geom.pageW - geom.hmargin - w
      (some { x := x
              y := geom.pageH - geom.vmargin
              size := geom.fontSize, segs := segs, setWidth := w }, ds, c)
  let furnishPage (i : Nat) (page : PageOut)
      (st0 : Std.HashMap String (Array Nat) × Nat) :
      (Array LineOut × Array LineOut) × Array Diag × Std.HashMap String (Array Nat) × Nat :=
      Id.run do
    let mut diags : Array Diag := #[]
    let mut cache := st0.1
    let mut count := st0.2
    let mut head : Array LineOut := #[]
    let mut lines : Array LineOut := #[]
    -- Margin numbers count counted lines across pages; the modulus filters what prints.
    if lineNumbersOn then
      for l in page.lines do
        if l.counted then
          count := count + 1
          if count % lineModulo == 0 then
            let (items, ds, c, _) :=
              itemsOfInlines pats numSize xHeight fs
                { color := mutedC, ground := furnGround }
                #[.text (toString count)] cache (.fixed .unattributed) imgs geom.textWidth
                geom.textHeight (ladder := geom.scale)
            diags := diags ++ ds
            cache := c
            let breaks := kp items geom.textWidth
            if let some brk := breaks[0]? then
              let (segs, w, _) := setLine items (lineStart items 0) brk
                geom.textWidth false
              lines := lines.push { x := numRight - w, y := l.y, size := numSize
                                    segs := segs, setWidth := w, furniture := true }
    -- Pages before a declaration's `from` carry none of it; the chrome footer follows its frame.
    let headOn := page.pageState.furniture && doc.headFrom ≤ i + 1
    let footOn := page.pageState.furniture && doc.footFrom ≤ i + 1
    if headOn then
      if let some content := doc.head then
        let (l?, ds, c) := runLine content page.pageState.folio headY geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then head := #[l]
    if footOn then
      if let some content := doc.foot then
        let (l?, ds, c) := runLine content page.pageState.folio footY geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then lines := lines.push { l with furniture := true }
      else if plainFoot then
        -- plain's foot: the page number between two fills, as `\ps@plain` sets it.
        let (l?, ds, c) := runLine #[.fill, .pageNumber, .fill] page.pageState.folio footY
          geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then lines := lines.push { l with furniture := true }
    -- The headline band's corner logos, once per page carrying a page-top bar.
    if let some bandB := page.band then
      for (content?, left) in [(doc.logoLeft, true), (doc.logoRight, false)] do
        if let some content := content? then
          let (items, lds, c, _) :=
            itemsOfInlines pats geom.fontSize xHeight fs { ground := furnGround }
              content cache (.fixed .unattributed) imgs geom.textWidth geom.textHeight
          diags := diags ++ lds
          cache := c
          let breaks := kp items geom.textWidth
          if let some brk := breaks[0]? then
            let (segs, w, _) := setLine items (lineStart items 0) brk geom.textWidth false
            -- A glyph run's size stands in for its ascent, the band centring's only estimate.
            let inkH := segs.foldl (init := (0 : Sp)) fun m sg => match sg with
              | .image _ _ h _ => max m h
              | .run _ _ _ _ _ size _ _ raise _ _ => max m (size + raise)
              | _ => m
            let x := if left then geom.hmargin else geom.pageW - geom.hmargin - w
            lines := lines.push { x := x, y := (bandB + inkH) / 2,
                                  size := geom.fontSize, segs := segs,
                                  setWidth := w, furniture := true }
    -- Colliding slots yield by ink, never position (W0333); ink off the medium is named (W0388).
    if let some band := page.foot then
      -- One baseline for the band, from the box the page's floor was set against (`footBaseline`).
      let footY := footBaseline geom.pageH ((page.footBox.map (·.2)).getD 0)
      let mut placed : Array (Ir.BandSlot × LineOut) := #[]
      for slot in band do
        let (l?, ds, c) := slotLine slot.side slot.content (i + 1) footY
          { color := (page.footLook.map (·.fg)).getD mutedC,
            ground := page.footLook.bind (·.bar) } cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then
          unless geom.onMedium l.x l.setWidth do
            diags := diags.push (Diag.of .W0388
              s!"{slot.label} reaches off the page: what stands past its edge cannot be \
shown, whatever reads the file"
              (help := "a band holds one line at a fixed position: shorten \
the content, or widen the page (\\page{ width = ... })")
              (detail := some s!"on page {i + 1}, \
{(geom.offMedium l.x l.setWidth).toPtString}pt past its edge"))
          placed := placed.push (slot, { l with furniture := true })
      let slots := placed
      for hj : j in [0:slots.size] do
        for hk : k in [j+1:slots.size] do
          let (a, la) := slots[j]
          let (bs, lb) := slots[k]
          if la.x < lb.x + lb.setWidth && lb.x < la.x + la.setWidth then
            let (lo, hi) := if a.rank < bs.rank then (a, bs) else (bs, a)
            diags := diags.push (Diag.of .W0333
              s!"the footer's slots collide: {lo.label} yields, painted over by {hi.label}"
              (help := "slot positions are fixed and the lower-priority \
slot yields in place: shorten the content or drop a slot")
              (detail := some s!"on page {i + 1}"))
      for p in slots.qsort (fun a b => a.1.rank < b.1.rank) do
        lines := lines.push p.2
    let logoContent := Ir.logoInForce doc.logo logoSpans i
    if headOn && footOn then
      if let some content := logoContent then
        unless content.isEmpty do
          -- Sized by the page's `\textheight`, beamer's in its text area (`frameFloor`).
          let textH := match page.frameArea with
            | .margins => page.footBox.elim geom.textHeight fun (h, d) =>
                footFloor geom.pageH sh.footGap h d
            | .text | .paper => frameFloor geom.pageH sh.footGap page.footBox
          let (l?, ds, c) := mkLogoLine content textH cache
          diags := diags ++ ds
          cache := c
          if let some l := l? then lines := lines.push { l with furniture := true }
    return ((head, lines), diags, cache, count)
  let fout := furnishFrom (furnishStep fs furnishPage) pages (sh.diags, sh.hyphCache, 0) 0
  let out := fout.1
  let diags := fout.2.1
  let unique := reportOnce sh.paragraphBreaks diags
  -- An in-document outline target resolves against finalized lines, as a PDF link annotation does.
  let outline := sh.navEntries.map fun (title, target) =>
    if target.startsWith "#" then
      { title := title
        page := (destination? out (target.drop 1).toString).map (·.1) }
    else ({ title := title, url := some target } : OutlineEntry)
  return { pages := out, diags := unique, outline := outline
           paragraphBreaks := sh.paragraphBreaks, overruns := sh.overruns, needs := sh.needs
           spilled := sh.spilled }

public theorem runPost_diags_covers (sh : Shipped) :
    ∀ d ∈ sh.diags, ∃ e ∈ (runPost sh).diags,
      e.code = d.code ∧ e.subject = d.subject := by
  intro d hd
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  apply reportOnce_covers
  apply furnishFrom_inv _
    (fun s : Array Diag × Std.HashMap String (Array Nat) × Nat => d ∈ s.1)
  · intro i page s hs
    exact Array.mem_append.mpr (Or.inl hs)
  · exact hd

public theorem runPost_pages (sh : Shipped) :
    ∀ p ∈ (runPost sh).pages, ∃ q ∈ sh.pages,
      p.fills = q.fills ∧ p.links = q.links ∧ p.inks = q.inks ∧ p.foot = q.foot ∧
        p.frame = q.frame := by
  intro p hp
  unfold runPost at hp
  dsimp only [Id.run, bind, pure, Id] at hp
  exact furnishFrom_keeps _ _ _ _ p hp

public theorem runPost_lifecycle_projects (sh : Shipped) :
    (runPost sh).pages.map (·.pageState) = sh.pages.map (·.pageState) := by
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  exact furnishFrom_projects _ _ (fun _ _ => rfl) _ _ _

public theorem runPost_frames_projects (sh : Shipped) :
    (runPost sh).pages.map (fun p => (p.frame, p.foot)) =
      sh.pages.map (fun p => (p.frame, p.foot)) := by
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  exact furnishFrom_projects _ _ (fun _ _ => rfl) _ _ _

public theorem runPost_frameOrigins_projects (sh : Shipped) :
    (runPost sh).pages.map (fun p => (p.frameOrigin, p.frame, p.foot)) =
      sh.pages.map (fun p => (p.frameOrigin, p.frame, p.foot)) := by
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  exact furnishFrom_projects _ _ (fun _ _ => rfl) _ _ _

public theorem runPost_attributed_projects (sh : Shipped) :
    (runPost sh).pages.map (fun p => p.lines.filter (fun l => l.leaf.isSome)) =
      sh.pages.map (fun p => p.lines.filter (fun l => l.leaf.isSome)) := by
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  apply furnishFrom_preserves
  intro i p s
  exact furnishLines_attributed_projects _ _ _ _

public theorem runPost_counted_projects (sh : Shipped) :
    (runPost sh).pages.map (fun p => p.lines.filter (·.counted)) =
      sh.pages.map (fun p => p.lines.filter (·.counted)) := by
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  apply furnishFrom_preserves
  intro i p s
  exact furnishLines_counted_projects _ _ _ _

private theorem sourceBound_runPost {n : Nat} (sh : Shipped)
    (h : ∀ p ∈ sh.pages, ∀ l ∈ p.lines, l.SourceBound n) :
    ∀ p ∈ (runPost sh).pages, ∀ l ∈ p.lines,
      l.furniture = false → l.SourceBound n := by
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  apply furnishFrom_pagesInv _
    (fun p => ∀ l ∈ p.lines, l.furniture = false → l.SourceBound n)
  · intro i p s hp
    exact sourceBound_furnishLines _ _ _ _ hp
  · intro p hp l hl _
    exact h p hp l hl

/-- Append the derived cut-mark fills after every shipped
page's own fills, so the marks paint over any background. -/
public def addMarks (out : Out) (m : Array Fill) : Out :=
  { out with pages := out.pages.map fun p => { p with fills := p.fills ++ m } }

public theorem addMarks_mem (out : Out) (m : Array Fill) (p : PageOut)
    (hp : p ∈ (addMarks out m).pages) :
    ∃ q ∈ out.pages, p.fills = q.fills ++ m := by
  obtain ⟨q, hq, rfl⟩ := Array.mem_map.mp hp
  exact ⟨q, hq, rfl⟩

/-- The mark fills a document's pages take: the derived eight when marks are declared
and fit the bleed, in the registration colour, then the rules the document drew. -/
private def markFillsOf (geom : Geom) (doc : Doc) : Array Fill :=
  let marks := if geom.marks && geom.markGap < geom.bleed && 0 < geom.markThick then
      cutMarks geom.pageW geom.pageH geom.bleed geom.markGap geom.markThick
        (Ir.Color.registration (doc.palette.entries.any (·.2.cmyk.isSome)))
    else #[]
  marks ++ doc.page.drawn.map fun r =>
    ({ x := r.x - geom.bleed, y := r.y - geom.bleed, w := r.w, h := r.h,
       color := (doc.palette.resolve r.color).getD Ir.Color.black }
      : Fill)

/-- W0304 for each colour a drawn rule names that resolves to nothing, once per name. -/
public def drawnInkDiags (doc : Doc) : Array Diag :=
  (doc.page.drawn.map (·.color)).foldl (fun (acc : Array String) c =>
      if (doc.palette.resolve c).isNone && !acc.contains c then acc.push c else acc) #[]
    |>.map fun c => Diag.of .W0304
      s!"'{c}' is not a colour here; the rules the page draws in it paint black"
      (help := "declare colours with \\palette{ name = #RRGGBB }")
      (subject := some ("palette:" ++ c))

/-- The document as the paged backend reads it, backend
conditionals resolved (`Ir.keepFor_covers`). -/
public def pdfView (doc : Doc) : Doc := { doc with body := Ir.keepFor "pdf" doc.body }

/-- Picture ordinals in the elaborator's document order; hidden
backend branches consume an ordinal but supply no PDF slot. -/
private def pdfPictureOrdinals (doc : Doc) : Array Nat :=
  let walk : Ir.CtxFold Bool (Nat × Array Nat) := {
    openBlock := fun kept (n, out) b =>
      let kept := kept && Ir.keptBy "pdf" b
      match b with
      | .picture _ => ((n + 1, if kept then out.push n else out), kept)
      | _ => ((n, out), kept)
    closeBlock := fun _ acc _ => acc
    openInline := fun kept acc _ => (acc, kept)
    closeInline := fun _ acc _ => acc }
  (Ir.foldCtxBlocks walk true (0, #[]) doc.body).2

/-- Translate native-picture request keys into the PDF structure leaves
placement reads, pairing every picture before looking up its source. -/
-- conserves: none — collects source evidence, not document content.
public def pictureSpansForPdf (doc : Doc) (spans : Array (String × Span)) :
    Array (Nat × Span) :=
  let leaves := (Struct.ofDoc (pdfView doc)).leaves.filterMap fun (id, leaf) =>
    match leaf with
    | .picture _ => some id
    | _ => none
  (leaves.zip (pdfPictureOrdinals doc)).filterMap fun (id, ordinal) =>
    (spans.find? (·.1 == Ir.picKeyPrefix ++ toString ordinal)).map fun (_, source) =>
      (id, source)

/-- Translate opening-frame source sites from the elaborated document's
body indices to the indices `run` reads after backend filtering. -/
public def frameSpansForPdf (doc : Doc) (spans : Array (Nat × Span)) : Array (Nat × Span) :=
  spans.filterMap fun (i, source) =>
    match doc.body[i]? with
    | some (.frame _ _ _ _ _) =>
      some (((doc.body.toList.take i).filter (keptBy "pdf")).length, source)
    | _ => none

private theorem keepForList_frame (bs : List Block) (i : Nat)
    (title : Array Inline) (standout : Bool) (valign : VAlign) (breakable : Bool)
    (body : Array Block)
    (h : bs[i]? = some (.frame title standout valign breakable body)) :
    (keepForList "pdf" bs)[((bs.take i).filter (keptBy "pdf")).length]? =
      some (keepForOne "pdf" (.frame title standout valign breakable body)) := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst b
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hr := ih i h
      cases hk : keptBy "pdf" b <;>
        simpa [keepForList, hk, List.filter_cons] using hr

public theorem frameSpansForPdf_covers (doc : Doc) (spans : Array (Nat × Span))
    (i : Nat) (source : Span)
    (title : Array Inline) (standout : Bool) (valign : VAlign) (breakable : Bool)
    (body : Array Block)
    (hs : (i, source) ∈ spans)
    (hb : doc.body[i]? = some (.frame title standout valign breakable body)) :
    let j := ((doc.body.toList.take i).filter (keptBy "pdf")).length
    (j, source) ∈ frameSpansForPdf doc spans ∧
      (pdfView doc).body[j]? =
        some (keepForOne "pdf" (.frame title standout valign breakable body)) := by
  constructor
  · exact Array.mem_filterMap.mpr ⟨(i, source), hs, by simp [hb]⟩
  · simpa [pdfView, keepFor] using
      keepForList_frame doc.body.toList i title standout valign breakable body
        (by simpa using hb)

/-- One top-level source block, overlay rewind included; the index is the source identity. -/
private def collectDocBlock (rd : Rd) (doc : Doc) (cover : Ir.Cover)
    (frameSpans : Array (Nat × Span)) (nums : Array (Option Nat))
    (i : Nat) (hi : i < doc.body.size)
    (st : Acc × Bool) : Acc × Bool := Id.run do
  let blk := doc.body[i]
  let mut acc := if st.2 || statefulBlock blk then st.1 else st.1.wantGap
  let firstBlk := st.2 && statefulBlock blk
  acc := { acc with frameCount := doc.frameCountAt i
                    framesDone := if doc.frameRestart == some i then 0 else acc.framesDone }
  match blk with
  | .frame title standout valign breakable body =>
    let num := nums[i]?.getD none
    acc := { acc with frameNum := num, frameLabel := rd.frameLabels[i]?.getD none,
                      frameOrigin := some ⟨i, 1⟩,
                      framesDone := num.getD acc.framesDone
                      frameSource := (frameSpans.find? (·.1 == i)).map (·.2) }
    let steps := Ir.frameSteps blk
    if steps ≤ 1 then
      acc := collectBlock { rd with steps := steps } acc
        (.frame title standout valign breakable
          (Ir.unwrapItemSteps (Ir.dimBlocks cover 1 body))) 0
    else
      let leafStart := acc.leafNext
      for k in [1:steps + 1] do
        acc := collectBlock { rd with step := k, steps := steps }
          { acc with leafNext := leafStart, frameOrigin := some ⟨i, k⟩ }
          (.frame title standout valign breakable
            (Ir.unwrapItemSteps (Ir.dimBlocks cover k body))) 0
  | other => acc := collectBlock rd acc (Ir.unwrapItemStep other) 0
  return (acc, firstBlk)

/-- The source loop, its state recording whether a real block has appeared. -/
private def collectDocBody (rd : Rd) (doc : Doc) (cover : Ir.Cover)
    (frameSpans : Array (Nat × Span)) (acc0 : Acc) : Acc := Id.run do
  let nums := doc.frameNumbers
  let mut st := (acc0, true)
  for h : i in [0:doc.body.size] do
    st := collectDocBlock rd doc cover frameSpans nums i h.upper st
  return st.1

private theorem Spacing.Paragraph.SourceBound.mono {n m : Nat} {j : ParaJob}
    (h : j.SourceBound n) (hn : n ≤ m) : j.SourceBound m := by
  refine ⟨?_, h.notes, h.marker, h.rule⟩
  rcases h.source with ⟨k, hk, hb⟩ | hg
  · exact Or.inl ⟨k, hk, Nat.lt_of_lt_of_le hb hn⟩
  · exact Or.inr hg

private theorem Op.SourceBound.mono {n m : Nat} {op : Op}
    (h : op.SourceBound n) (hn : n ≤ m) : op.SourceBound m := by
  cases op <;> simp only [Op.SourceBound] at h ⊢
  all_goals first | exact h.mono hn | exact h

private def Spacing.Pending.SourceBound (n : Nat) (a : Acc) : Prop :=
  ∀ op ∈ a.ops, op.SourceBound n

private theorem Spacing.Pending.SourceBound.mono {n m : Nat} {a : Acc}
    (h : a.SourceBound n) (hn : n ≤ m) : a.SourceBound m :=
  fun op ho => (h op ho).mono hn

private theorem sourceBound_owedOp (a : Acc) (g : Glue) (n : Nat) :
    (a.owedOp g).SourceBound n := by
  cases h : a.dispAlt <;> simp [Spacing.Pending.owedOp, h, Op.SourceBound]

private theorem sourceBound_flushAnchored {n : Nat} (a : Acc) (r : Rd)
    (k : Nat) (h : a.SourceBound n) : (a.flushAnchored r k).SourceBound n := by
  intro op ho
  simp only [Spacing.Pending.flushAnchored, Array.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · exact h op ho
  · split at ho <;> simp_all [Op.SourceBound]
  · simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> trivial

private theorem sourceBound_flushGap {n : Nat} (a : Acc) (r : Rd)
    (h : a.SourceBound n) : (a.flushGap r).SourceBound n := by
  cases hk : a.anchorAt with
  | some k =>
    simpa only [Spacing.Pending.SourceBound, Spacing.Pending.flushGap, hk] using
      sourceBound_flushAnchored a r k h
  | none =>
    simp only [Spacing.Pending.SourceBound, Spacing.Pending.flushGap, hk]
    repeat' split
    all_goals
      intro op ho
      first
      | exact h op ho
      | simp only [Array.mem_push] at ho
        rcases ho with ho | rfl
        · first
          | exact h op ho
          | rcases ho with ho | rfl
            · exact h op ho
            · trivial
        · first | exact sourceBound_owedOp a _ n | trivial

private theorem flushGap_leafNext (a : Acc) (r : Rd) :
    (a.flushGap r).leafNext = a.leafNext := by
  unfold Spacing.Pending.flushGap
  repeat' split
  all_goals rfl

private theorem itemsOfInlines_empty (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (cache : Std.HashMap String (Array Nat))
    (ctr : LeafCtr) (imgs : Image.Store) (textW textH : Sp) (noteOk : Bool)
    (ladder : List (String × Nat)) (step : Nat)
    (roleMetrics : List (String × (Sp × Option Sp))) (steps : Nat) :
    (itemsOfInlines pats size xHeight fs baseStyle #[] cache ctr imgs textW textH
      noteOk ladder step roleMetrics steps).1 =
      #[.glue { fil := true, parfill := true },
        .pen 0 forcedCost false 0 Ir.Color.black #[]] := by
  rfl

private theorem raggedItems_noGlyph (items : Array Item)
    (h : ∀ it ∈ items, it.NoGlyph) : ∀ it ∈ raggedItems items, it.NoGlyph := by
  intro it hi
  obtain ⟨x, hx, rfl⟩ := Array.mem_map.mp hi
  have hg := h x hx
  cases x <;> dsimp only at hg ⊢
  all_goals first | exact hg | split <;> trivial

private theorem collectPara_leafNext (r : Rd) (a : Acc)
    (xs : Array Inline) (indent : Sp) (leaf : Option Nat) (span : Nat) :
    (collectPara r a xs indent false r.geom.fontSize
      (leaf := leaf) (span := span)).leafNext = a.leafNext := by
  simp only [collectPara]
  exact flushGap_leafNext a r

private theorem sourceBound_collectPara {n : Nat} (r : Rd) (a : Acc)
    (xs : Array Inline) (indent : Sp) (leaf : Option Nat) (span : Nat)
    (ha : a.SourceBound n) (hp : PlainInlines xs)
    (hs : (∃ k, leaf = some k ∧ k < n) ∨ xs = #[]) :
    (collectPara r a xs indent false r.geom.fontSize
      (leaf := leaf) (span := span)).SourceBound n := by
  have hn := itemsOfInlines_plainNotes r.pats r.geom.fontSize r.xHeight r.fs
    ({ color := (a.flushGap r).fg, ground := (a.flushGap r).ground
       urlBreaks := r.surface == .markdown } : TextStyle)
    xs (a.flushGap r).hyphCache (LeafCtr.of leaf span xs) r.imgs
    ((a.flushGap r).measure.getD r.geom.textWidth - (indent + 0))
    r.geom.textHeight true r.geom.scale r.step r.roleMetrics r.steps hp
  simp only [collectPara, show (Color.black == Color.black) = true from rfl,
    BEq.rfl, Bool.false_eq_true, ↓reduceIte]
  rw [hn]
  simp only [Array.isEmpty_empty, ↓reduceIte]
  intro op ho
  simp only [Array.mem_push] at ho
  rcases ho with ho | rfl
  · exact sourceBound_flushGap a r ha _ ho
  · refine ⟨?_, rfl, rfl, rfl⟩
    rcases hs with hs | rfl
    · exact Or.inl hs
    · apply Or.inr
      have hi : ∀ it ∈ (itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs
          ({ color := (a.flushGap r).fg, ground := (a.flushGap r).ground } : TextStyle)
          #[] (a.flushGap r).hyphCache (LeafCtr.of leaf span #[]) r.imgs
          ((a.flushGap r).measure.getD r.geom.textWidth - (indent + 0))
          r.geom.textHeight true r.geom.scale r.step r.roleMetrics r.steps).1, it.NoGlyph := by
        rw [itemsOfInlines_empty]
        intro it hi
        simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> first | rfl | trivial
      split
      · exact hi
      · exact raggedItems_noGlyph _ hi

private theorem plainInlines_rawCount (xs : List Inline) (out : Array Struct.Node)
    (hp : ∀ x ∈ xs, ∃ s, x = .text s) :
    (Struct.leaves (Struct.inlinesRaw out xs)).size =
      (Struct.leaves out).size + xs.length := by
  induction xs generalizing out with
  | nil => simp [Struct.inlinesRaw]
  | cons x xs ih =>
    obtain ⟨s, rfl⟩ := hp x (by simp)
    rw [Struct.inlinesRaw, ih _ (fun y hy => hp y (by simp [hy]))]
    simp only [Struct.inlineRaw, Struct.leaves, Array.toList_push,
      Struct.leavesList_snoc, Struct.leavesOne_leaf_exact, Array.size_push,
      List.length_cons]
    omega

private theorem plainInlines_leafCount (xs : Array Inline)
    (hp : ∀ x ∈ xs, ∃ s, x = .text s) :
    Struct.leafCountInlines xs = xs.size := by
  simpa [Struct.leafCountInlines, Struct.leaves, Struct.leavesList_nil_exact] using
    plainInlines_rawCount xs.toList #[] (by simpa using hp)

private def sourceLeafSum (bs : List Block) : Nat :=
  (bs.map fun b => Struct.leafCountBlocks #[b]).sum

private theorem blocksRaw_leafCount (bs : List Block) (out : Array Struct.Node) :
    (Struct.leaves (Struct.blocksRaw out bs)).size =
      (Struct.leaves out).size + sourceLeafSum bs := by
  induction bs generalizing out with
  | nil => simp [Struct.blocksRaw, sourceLeafSum]
  | cons b bs ih =>
    rw [Struct.blocksRaw, ih]
    rw [Struct.blockRaw_acc]
    simp only [Struct.leaves, Array.toList_append, Struct.leavesList_append]
    rw [Struct.leavesList_acc]
    simp only [Array.size_append]
    simp only [sourceLeafSum, List.map_cons, List.sum_cons, Struct.leafCountBlocks,
      Struct.blocksRaw, Struct.leaves]
    omega

private theorem sourceLeafSum_append (as bs : List Block) :
    sourceLeafSum (as ++ bs) = sourceLeafSum as + sourceLeafSum bs := by
  simp [sourceLeafSum]

private theorem sourceLeafSum_take_le (bs : List Block) (i : Nat) :
    sourceLeafSum (bs.take i) ≤ sourceLeafSum bs := by
  have h := sourceLeafSum_append (bs.take i) (bs.drop i)
  rw [List.take_append_drop] at h
  omega

private theorem sourceLeafSum_para (xs : Array Inline) :
    Struct.leafCountBlocks #[.para xs] = Struct.leafCountInlines xs := by
  simp [Struct.leafCountBlocks, Struct.blocksRaw, Struct.blockRaw, Struct.leaves,
    Struct.leavesList_cons_exact, Struct.leavesOne_node_exact,
    Struct.leavesList_nil_exact, Struct.leafCountInlines]

private theorem sourceLeafSum_ofDoc (doc : Doc) :
    (Struct.ofDoc doc).leaves.size = sourceLeafSum doc.body.toList := by
  simp only [Struct.ofDoc, Struct.ofBlocks, Struct.Tree.leaves, Struct.leaves,
    Struct.number, Struct.numberList_leafCount]
  simpa [Struct.leaves, Struct.leavesList_nil_exact] using
    blocksRaw_leafCount doc.body.toList #[]

private theorem collectParaBlock_plain (r : Rd) (a : Acc) (xs : Array Inline)
    (indent : Sp) (hp : PlainInlines xs) :
    collectParaBlock r a xs indent =
      collectPara r (a.leafRange (Struct.leafCountInlines xs)).1 xs indent false r.geom.fontSize
        (leaf := (a.leafRange (Struct.leafCountInlines xs)).2) (span := Struct.leafCountInlines xs) := by
  unfold collectParaBlock
  split
  · rename_i h
    have hall := (Bool.and_eq_true_iff.mp h).2
    by_cases he : xs = #[]
    · simp [he] at h
    · obtain ⟨x, hx⟩ := Array.exists_mem_of_ne_empty xs he
      obtain ⟨s, rfl⟩ := hp x hx
      have hh := (Array.all_eq_true_iff_forall_mem.mp hall) (.text s) hx
      contradiction
  · rfl

private theorem collectParaBlock_leafNext (r : Rd) (a : Acc) (xs : Array Inline)
    (indent : Sp) (hp : PlainInlines xs) :
    (collectParaBlock r a xs indent).leafNext = a.leafNext + xs.size := by
  rw [collectParaBlock_plain r a xs indent hp]
  simp only [Spacing.Pending.leafRange]
  rw [collectPara_leafNext]
  rw [plainInlines_leafCount xs hp]

private theorem sourceBound_collectParaBlock {n : Nat} (r : Rd) (a : Acc)
    (xs : Array Inline) (indent : Sp) (ha : a.SourceBound n) (hp : PlainInlines xs)
    (hn : a.leafNext + xs.size ≤ n) :
    (collectParaBlock r a xs indent).SourceBound n := by
  rw [collectParaBlock_plain r a xs indent hp]
  simp only [Spacing.Pending.leafRange]
  apply sourceBound_collectPara
  · exact ha
  · exact hp
  · by_cases he : xs = #[]
    · exact Or.inr he
    · apply Or.inl
      have hs : 0 < xs.size := Array.size_pos_iff.mpr he
      refine ⟨a.leafNext, ?_, by omega⟩
      simp [plainInlines_leafCount xs hp, Nat.ne_of_gt hs]

private theorem collectDocBlock_leafNext (rd : Rd) (doc : Doc) (cover : Ir.Cover)
    (frameSpans : Array (Nat × Span)) (nums : Array (Option Nat))
    (i : Nat) (hi : i < doc.body.size) (st : Acc × Bool) (xs : Array Inline)
    (hb : doc.body[i] = .para xs) (hp : PlainInlines xs) :
    (collectDocBlock rd doc cover frameSpans nums i hi st).1.leafNext =
      st.1.leafNext + Struct.leafCountBlocks #[doc.body[i]] := by
  simp only [collectDocBlock, hb, statefulBlock, Ir.pageMarkerBlock,
    Bool.or_false, Bool.and_false, Id.run, Ir.unwrapItemStep_para_exact]
  dsimp only [pure, Id]
  rw [collectBlock, collectParaBlock_leafNext _ _ _ _ hp]
  simp only [sourceLeafSum_para, plainInlines_leafCount xs hp]
  split <;> rfl

private theorem sourceBound_collectDocBlock {n : Nat} (rd : Rd) (doc : Doc)
    (cover : Ir.Cover) (frameSpans : Array (Nat × Span)) (nums : Array (Option Nat))
    (i : Nat) (hi : i < doc.body.size) (st : Acc × Bool) (xs : Array Inline)
    (hb : doc.body[i] = .para xs) (hp : PlainInlines xs)
    (ha : st.1.SourceBound n)
    (hn : st.1.leafNext + Struct.leafCountBlocks #[doc.body[i]] ≤ n) :
    (collectDocBlock rd doc cover frameSpans nums i hi st).1.SourceBound n := by
  simp only [collectDocBlock, hb, statefulBlock, Ir.pageMarkerBlock,
    Bool.or_false, Bool.and_false, Id.run, Ir.unwrapItemStep_para_exact]
  dsimp only [pure, Id]
  rw [collectBlock]
  apply sourceBound_collectParaBlock
  · split <;> exact ha
  · exact hp
  · split <;> simpa only [hb, sourceLeafSum_para, plainInlines_leafCount xs hp, Spacing.Pending.wantGap] using hn

private theorem sourceRange_progress {β : Type}
    (P : Nat → β → Prop) (lo len : Nat)
    (f : (i : Nat) → i ∈ List.range' lo len → β → Id (ForInStep β))
    (init : β) (h0 : P lo init)
    (step : ∀ i hi b, P i b →
      ∃ next, f i hi b = .yield next ∧ P (i + 1) next) :
    P (lo + len) (forIn' (List.range' lo len) init f : Id β).run := by
  induction len generalizing lo init with
  | zero => simpa using h0
  | succ len ih =>
    simp only [List.range'_succ] at f step ⊢
    rw [List.forIn'_cons]
    obtain ⟨next, hf, hp⟩ := step lo (by simp) init h0
    simp only [hf, bind, Id.run]
    have hr := ih (lo + 1) _ next hp (fun i hi b hb =>
      step i (List.mem_cons_of_mem lo hi) b hb)
    simpa only [Nat.add_assoc, Nat.add_comm 1 len, Id.run] using hr


private theorem collectDocBody_source {n : Nat} (rd : Rd) (doc : Doc) (cover : Ir.Cover)
    (frameSpans : Array (Nat × Span)) (acc0 : Acc)
    (hp : ∀ b ∈ doc.body, ∃ xs, b = .para xs ∧ PlainInlines xs)
    (ha : acc0.SourceBound n)
    (hn : acc0.leafNext + sourceLeafSum doc.body.toList ≤ n) :
    (collectDocBody rd doc cover frameSpans acc0).SourceBound n ∧
      (collectDocBody rd doc cover frameSpans acc0).leafNext =
        acc0.leafNext + sourceLeafSum doc.body.toList := by
  let P := fun i (st : Acc × Bool) => st.1.SourceBound n ∧
    st.1.leafNext = acc0.leafNext + sourceLeafSum (doc.body.toList.take i)
  have h0 : P 0 (acc0, true) := by simp [P, sourceLeafSum, ha]
  have step (i : Nat) (hi : i < doc.body.size) (st : Acc × Bool) (hs : P i st) :
      P (i + 1) (collectDocBlock rd doc cover frameSpans doc.frameNumbers i hi st) := by
    obtain ⟨xs, hb, hx⟩ := hp doc.body[i] (Array.getElem_mem hi)
    have hprefix : sourceLeafSum (doc.body.toList.take (i + 1)) =
        sourceLeafSum (doc.body.toList.take i) + Struct.leafCountBlocks #[doc.body[i]] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hi), sourceLeafSum_append]
      simp only [sourceLeafSum, List.map_singleton, List.sum_cons, List.sum_nil, Nat.add_zero,
        Array.getElem_toList]
    have hbnd : st.1.leafNext + Struct.leafCountBlocks #[doc.body[i]] ≤ n := by
      have hle := sourceLeafSum_take_le doc.body.toList (i + 1)
      rw [hprefix] at hle
      dsimp only [P] at hs
      omega
    constructor
    · exact sourceBound_collectDocBlock rd doc cover frameSpans doc.frameNumbers i hi st
        xs hb hx hs.1 hbnd
    · rw [collectDocBlock_leafNext _ _ _ _ _ _ _ _ _ hb hx, hs.2, hprefix]
      omega
  unfold collectDocBody
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  dsimp only [Id.run, bind, pure, Id]
  have hr := sourceRange_progress P 0 doc.body.size
    (fun i hi st => .yield (collectDocBlock rd doc cover frameSpans doc.frameNumbers
      i (by simpa using (List.mem_range'_1.mp hi).2) st)) (acc0, true) h0 ?_
  · have ht : doc.body.toList.take doc.body.size = doc.body.toList := by
      simpa only [Array.length_toList] using (List.take_length (l := doc.body.toList))
    simpa only [P, Nat.zero_add, ht, Id.run, bind, pure, Id] using hr
  · intro i hi st hs
    have hib : i < doc.body.size := (by simpa using (List.mem_range'_1.mp hi).2)
    exact ⟨collectDocBlock rd doc cover frameSpans doc.frameNumbers i hib st, rfl,
      step i hib st hs⟩

private def GlyphClean (ds : Array Diag) : Prop :=
  ∀ d ∈ ds, d.code ≠ "E0405" ∧ d.code ≠ "W0009"

private def Spacing.Paragraph.Prose (j : ParaJob) : Prop :=
  (Spacing.Paragraph.hangIndent j) = 0 ∧ ∃ items, ItemsProse items ∧ (Spacing.Paragraph.items j) = paraItems items

private def Op.Prose : Op → Prop
  | Op.para j t => j.Prose ∧ t.get = Spacing.Paragraph.breaks j
  | Op.skip _ | Op.skipAlt .. | Op.anchorRule _ | Op.anchor _ => True
  | _ => False

private def Op.census (pick : Option Nat → Bool → Bool) : Op → List Char
  | Op.para j _ =>
    if pick (Spacing.Paragraph.leaf j) (!(Spacing.Paragraph.inFloat j)) then (Spacing.Paragraph.items j).toList.flatMap Item.boxChars else []
  | _ => []

private def Op.Clean : Op → Prop
  | Op.para j _ => GlyphClean (Spacing.Paragraph.diags j)
  | _ => True

private theorem raggedItems_chars (items : Array Item) :
    (raggedItems items).toList.flatMap Item.boxChars = items.toList.flatMap Item.boxChars := by
  simp only [raggedItems, Array.toList_map, List.flatMap_map]
  congr 1
  funext it
  cases it <;> dsimp only [Function.comp_def]
  all_goals first | rfl | (split <;> rfl)

private theorem collectPara_prose (r : Rd) (a : Acc)
    (xs : Array Inline) (indent : Sp) (leaf : Option Nat) (span : Nat)
    (hp : PlainInlines xs) (hr : (Spacing.Context.pats r) = none) :
    ∃ j : ParaJob, Spacing.Pending.ops (collectPara r a xs indent false (Spacing.Context.geom r).fontSize
        (leaf := leaf) (span := span)) = (Spacing.Pending.ops (a.flushGap r)).push (Op.ofPara j) ∧
      j.Prose ∧ (Spacing.Paragraph.leaf j) = leaf ∧ (Spacing.Paragraph.inFloat j) = (Spacing.Context.inFloat r) ∧
      (GlyphClean (Spacing.Paragraph.diags j) →
        inkCensus ((Spacing.Paragraph.items j).toList.flatMap Item.boxChars) =
          inkCensus (Ir.plainText xs).toList) := by
  let style : TextStyle := { color := (Spacing.Pending.fg (a.flushGap r)), ground := (Spacing.Pending.ground (a.flushGap r))
                             urlBreaks := Spacing.Context.surface r == .markdown }
  have hn := itemsOfInlines_plainNotes (Spacing.Context.pats r) (Spacing.Context.geom r).fontSize (Spacing.Context.xHeight r) (Spacing.Context.fs r)
    style xs (Spacing.Pending.hyphCache (a.flushGap r)) (LeafCtr.of leaf span xs) (Spacing.Context.imgs r)
    ((Spacing.Pending.measure (a.flushGap r)).getD (Spacing.Context.geom r).textWidth - (indent + 0))
    (Spacing.Context.geom r).textHeight true (Spacing.Context.geom r).scale (Spacing.Context.step r) (Spacing.Context.roleMetrics r) (Spacing.Context.steps r) hp
  have hi := itemsOfInlines_none_prose (Spacing.Context.geom r).fontSize (Spacing.Context.xHeight r) (Spacing.Context.fs r)
    style xs (Spacing.Pending.hyphCache (a.flushGap r)) (LeafCtr.of leaf span xs) (Spacing.Context.imgs r)
    ((Spacing.Pending.measure (a.flushGap r)).getD (Spacing.Context.geom r).textWidth - (indent + 0))
    (Spacing.Context.geom r).textHeight true (Spacing.Context.geom r).scale (Spacing.Context.step r) (Spacing.Context.roleMetrics r) (Spacing.Context.steps r) hp rfl
  have hc := itemsOfInlines_none_chars (Spacing.Context.geom r).fontSize (Spacing.Context.xHeight r) (Spacing.Context.fs r) (Spacing.Context.imgs r)
    ((Spacing.Pending.measure (a.flushGap r)).getD (Spacing.Context.geom r).textWidth - (indent + 0))
    (Spacing.Context.geom r).textHeight (Spacing.Pending.hyphCache (a.flushGap r)) (LeafCtr.of leaf span xs)
    style xs true (Spacing.Context.geom r).scale (Spacing.Context.step r) (Spacing.Context.roleMetrics r) (Spacing.Context.steps r) hp rfl
  simp only [collectPara, show (Color.black == Color.black) = true from rfl,
    BEq.rfl, Bool.false_eq_true, ↓reduceIte]
  rw [hn]
  simp only [Array.isEmpty_empty, ↓reduceIte]
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · refine ⟨rfl, ?_⟩
    rcases hi with ⟨items, hi, he⟩
    split
    · exact ⟨items, hi, by simpa only [hr] using he⟩
    · exact ⟨raggedItems items, raggedItems_prose items hi, by
        simpa only [hr] using
          (congrArg raggedItems he).trans (raggedItems_paraItems items)⟩
  · intro hd
    change inkCensus ((if _ then _ else raggedItems _).toList.flatMap _) = _
    split
    · simpa only [hr] using hc (by simpa only [hr, GlyphClean, Id.run, pure, Id] using hd)
    · rw [raggedItems_chars]
      simpa only [hr] using hc (by simpa only [hr, GlyphClean, Id.run, pure, Id] using hd)

private def Op.Gap : Op → Prop
  | Op.skip _ | Op.skipAlt .. | Op.anchorRule _ | Op.anchor _ => True
  | _ => False

private def Spacing.Pending.GapAppend (a b : Acc) : Prop :=
  ∃ tail : Array Op, Spacing.Pending.ops b = Spacing.Pending.ops a ++ tail ∧ ∀ op ∈ tail, op.Gap

private theorem gap_owedOp (a : Acc) (g : Glue) : (a.owedOp g).Gap := by
  cases h : Spacing.Pending.dispAlt a <;> simp [Spacing.Pending.owedOp, h, Op.Gap]

private theorem flushAnchored_gapAppend (a : Acc) (r : Rd) (k : Nat) :
    a.GapAppend (a.flushAnchored r k) := by
  let par := if Spacing.Pending.trivOwed a then r.resolve (Spacing.Context.geom r).texParskip else r.parskip
  let lead := if Spacing.Pending.wantDefault a && Spacing.Pending.declaredSkip a then #[Op.skip par] else #[]
  refine ⟨lead ++ #[Op.skip ((Spacing.Pending.owed a).extract 0 k |>.foldl Glue.add {}),
    Op.anchorRule (r.resolve (Spacing.Context.geom r).texParskip),
    Op.skip ((Spacing.Pending.owed a).extract k (Spacing.Pending.owed a).size |>.foldl Glue.add {})], ?_, ?_⟩
  · simp only [Spacing.Pending.flushAnchored, par, lead, Array.append_assoc]
  · intro op ho
    simp only [Array.mem_append] at ho
    rcases ho with ho | ho
    · dsimp only [lead] at ho
      split at ho <;> simp_all [Op.Gap]
    · simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> trivial

private theorem flushGap_gapAppend (a : Acc) (r : Rd) :
    a.GapAppend (a.flushGap r) := by
  cases hk : Spacing.Pending.anchorAt a with
  | some k =>
    simpa only [Spacing.Pending.GapAppend, Spacing.Pending.flushGap, hk] using flushAnchored_gapAppend a r k
  | none =>
    simp only [Spacing.Pending.GapAppend, Spacing.Pending.flushGap, hk]
    split
    · split
      · exact ⟨#[Op.skip (r.parskip)], by simp, by simp [Op.Gap]⟩
      · exact ⟨#[], by simp, by simp⟩
    · split
      · refine ⟨#[Op.skip (if Spacing.Pending.trivOwed a then r.resolve (Spacing.Context.geom r).texParskip
          else r.parskip), a.owedOp ((Spacing.Pending.owed a).foldl Glue.add {})],
          by apply Array.toList_inj.mp; simp [List.append_assoc], ?_⟩
        intro op ho
        simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · trivial
        · exact gap_owedOp a _
      · refine ⟨#[a.owedOp (a.gapGlue r)], by apply Array.toList_inj.mp; simp, ?_⟩
        intro op ho
        simp only [Array.mem_singleton] at ho
        subst op
        exact gap_owedOp a _

private def Spacing.Pending.Prose (a : Acc) : Prop := ∀ op ∈ Spacing.Pending.ops a, op.Prose
private def Spacing.Pending.Clean (a : Acc) : Prop := ∀ op ∈ Spacing.Pending.ops a, op.Clean
private def Spacing.Pending.census (pick : Option Nat → Bool → Bool) (a : Acc) : List Char :=
  (Spacing.Pending.ops a).toList.flatMap (Op.census pick)

private theorem Op.Gap.prose {op : Op} (h : op.Gap) : op.Prose := by
  cases op <;> simp only [Op.Gap, Op.Prose] at h ⊢ <;> trivial

private theorem Op.Gap.clean {op : Op} (h : op.Gap) : op.Clean := by
  cases op <;> simp only [Op.Gap, Op.Clean] at h ⊢ <;> trivial

private theorem Op.Gap.census {op : Op} (h : op.Gap) (pick : Option Nat → Bool → Bool) :
    op.census pick = [] := by
  cases op <;> simp only [Op.Gap, Op.census] at h ⊢ <;> trivial

private theorem Spacing.Pending.GapAppend.prose {a b : Acc} (h : a.GapAppend b)
    (ha : a.Prose) : b.Prose := by
  obtain ⟨tail, he, ht⟩ := h
  intro op ho
  rw [he] at ho
  rcases Array.mem_append.mp ho with ho | ho
  · exact ha op ho
  · exact (ht op ho).prose

private theorem Spacing.Pending.GapAppend.clean {a b : Acc} (h : a.GapAppend b)
    (hb : b.Clean) : a.Clean := by
  obtain ⟨tail, he, _⟩ := h
  exact fun op ho => hb op (he ▸ Array.mem_append_left tail ho)

private theorem Spacing.Pending.GapAppend.census {a b : Acc} (h : a.GapAppend b)
    (pick : Option Nat → Bool → Bool) : b.census pick = a.census pick := by
  obtain ⟨tail, he, ht⟩ := h
  simp only [Spacing.Pending.census, he, Array.toList_append, List.flatMap_append]
  have hn : tail.toList.flatMap (Op.census pick) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro op ho
    exact (ht op (by simpa using ho)).census pick
  rw [hn, List.append_nil]


private theorem collectPara_census (r : Rd) (a : Acc)
    (xs : Array Inline) (indent : Sp) (leaf : Option Nat) (span : Nat)
    (hp : PlainInlines xs) (hr : (Spacing.Context.pats r) = none) (ha : a.Prose)
    (pick : Option Nat → Bool → Bool) :
    let out := collectPara r a xs indent false (Spacing.Context.geom r).fontSize
      (leaf := leaf) (span := span)
    out.Prose ∧ (out.Clean → a.Clean ∧
      inkCensus (out.census pick) = inkCensus (a.census pick) ++
        if pick leaf (!(Spacing.Context.inFloat r)) then inkCensus (Ir.plainText xs).toList else []) := by
  dsimp only
  obtain ⟨j, he, hj, hl, hf, hc⟩ := collectPara_prose r a xs indent leaf span hp hr
  have hg := flushGap_gapAppend a r
  constructor
  · intro op ho
    rw [he] at ho
    rcases Array.mem_push.mp ho with ho | rfl
    · exact hg.prose ha op ho
    · exact ⟨hj, rfl⟩
  · intro hd
    have hbefore : (a.flushGap r).Clean := fun op ho => hd op (he ▸ Array.mem_push.mpr (Or.inl ho))
    have hjob : GlyphClean (Spacing.Paragraph.diags j) := hd (Op.ofPara j) (he ▸ Array.mem_push_self)
    refine ⟨hg.clean hbefore, ?_⟩
    change inkCensus ((Spacing.Pending.ops _).toList.flatMap (Op.census pick)) = _
    rw [he]
    simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    change inkCensus ((a.flushGap r).census pick ++ (Op.ofPara j).census pick) = _
    rw [hg.census pick]
    simp only [inkCensus, List.filter_append, Op.ofPara, Op.census, hl, hf]
    split
    · exact congrArg (inkCensus (a.census pick) ++ ·) (hc hjob)
    · rfl

private theorem collectParaBlock_census (r : Rd) (a : Acc) (xs : Array Inline)
    (indent : Sp) (hp : PlainInlines xs) (hr : (Spacing.Context.pats r) = none) (ha : a.Prose)
    (pick : Option Nat → Bool → Bool) :
    let out := collectParaBlock r a xs indent
    out.Prose ∧ (out.Clean → a.Clean ∧
      inkCensus (out.census pick) = inkCensus (a.census pick) ++
        if pick (if xs.size == 0 then none else some (Spacing.Pending.leafNext a)) (!(Spacing.Context.inFloat r))
        then inkCensus (Ir.plainText xs).toList else []) := by
  dsimp only
  rw [collectParaBlock_plain r a xs indent hp]
  simpa only [Spacing.Pending.leafRange, plainInlines_leafCount xs hp,
    Spacing.Pending.Prose, Spacing.Pending.Clean, Spacing.Pending.census] using
    collectPara_census r (a.leafRange (Struct.leafCountInlines xs)).1 xs indent
      (a.leafRange (Struct.leafCountInlines xs)).2 (Struct.leafCountInlines xs) hp hr ha pick

private theorem collectDocBlock_census (rd : Rd) (doc : Doc) (cover : Ir.Cover)
    (frameSpans : Array (Nat × Span)) (nums : Array (Option Nat))
    (i : Nat) (hi : i < doc.body.size) (st : Acc × Bool) (xs : Array Inline)
    (hb : doc.body[i] = .para xs) (hp : PlainInlines xs)
    (hr : (Spacing.Context.pats rd) = none) (ha : st.1.Prose) (pick : Option Nat → Bool → Bool) :
    let out := (collectDocBlock rd doc cover frameSpans nums i hi st).1
    out.Prose ∧ (out.Clean → st.1.Clean ∧
      inkCensus (out.census pick) = inkCensus (st.1.census pick) ++
        if pick (if xs.size == 0 then none else some (Spacing.Pending.leafNext st.1)) (!(Spacing.Context.inFloat rd))
        then inkCensus (Ir.plainText xs).toList else []) := by
  simp only [collectDocBlock, hb, statefulBlock, Ir.pageMarkerBlock,
    Bool.or_false, Bool.and_false, Id.run, Ir.unwrapItemStep_para_exact]
  dsimp only [pure, Id]
  rw [collectBlock]
  split <;> refine collectParaBlock_census rd _ xs 0 hp hr ?_ pick <;> exact ha

private def sourceInkAt (pick : Option Nat → Bool → Bool) (body : Array Block)
    (start : Nat) (counted : Bool) (i : Nat) : List Char :=
  match body[i]? with
  | none => []
  | some b =>
    if pick (if Struct.leafCountBlocks #[b] == 0 then none
        else some (start + sourceLeafSum (body.toList.take i))) counted
    then inkCensus (Ir.blocksText #[b]).toList else []

private def sourceInkPrefix (pick : Option Nat → Bool → Bool) (body : Array Block)
    (start : Nat) (counted : Bool) (n : Nat) : List Char :=
  (List.range n).flatMap (sourceInkAt pick body start counted)

private theorem sourceInkPrefix_succ (pick : Option Nat → Bool → Bool)
    (body : Array Block) (start : Nat) (counted : Bool) (n : Nat) :
    sourceInkPrefix pick body start counted (n + 1) =
      sourceInkPrefix pick body start counted n ++ sourceInkAt pick body start counted n := by
  simp [sourceInkPrefix, List.range_succ]

private theorem sourceInkAt_para (pick : Option Nat → Bool → Bool)
    (body : Array Block) (start : Nat) (counted : Bool)
    (i : Nat) (hi : i < body.size) (xs : Array Inline)
    (hb : body[i] = .para xs) (hp : PlainInlines xs) :
    sourceInkAt pick body start counted i =
      if pick (if xs.size == 0 then none
        else some (start + sourceLeafSum (body.toList.take i))) counted
      then inkCensus (Ir.plainText xs).toList else [] := by
  simp only [sourceInkAt, Array.getElem?_eq_getElem hi, hb,
    sourceLeafSum_para, plainInlines_leafCount xs hp]
  simp only [Ir.blocksText, Ir.blockTextList,
    Ir.blockTextOne, String.empty_append]

private theorem collectDocBody_census (rd : Rd) (doc : Doc) (cover : Ir.Cover)
    (frameSpans : Array (Nat × Span)) (acc0 : Acc)
    (hp : ∀ b ∈ doc.body, ∃ xs, b = .para xs ∧ PlainInlines xs)
    (hr : (Spacing.Context.pats rd) = none) (ha : acc0.Prose)
    (pick : Option Nat → Bool → Bool) :
    let out := collectDocBody rd doc cover frameSpans acc0
    out.Prose ∧ (out.Clean → acc0.Clean ∧
      inkCensus (out.census pick) = inkCensus (acc0.census pick) ++
        sourceInkPrefix pick doc.body (Spacing.Pending.leafNext acc0) (!(Spacing.Context.inFloat rd)) doc.body.size) := by
  let P := fun i (st : Acc × Bool) => st.1.Prose ∧
    Spacing.Pending.leafNext st.1 = Spacing.Pending.leafNext acc0 + sourceLeafSum (doc.body.toList.take i) ∧
    (st.1.Clean → acc0.Clean ∧
      inkCensus (st.1.census pick) = inkCensus (acc0.census pick) ++
        sourceInkPrefix pick doc.body (Spacing.Pending.leafNext acc0) (!(Spacing.Context.inFloat rd)) i)
  have h0 : P 0 (acc0, true) := by
    simp [P, sourceLeafSum, sourceInkPrefix, ha]
  have step (i : Nat) (hi : i < doc.body.size) (st : Acc × Bool) (hs : P i st) :
      P (i + 1) (collectDocBlock rd doc cover frameSpans doc.frameNumbers i hi st) := by
    obtain ⟨xs, hb, hx⟩ := hp doc.body[i] (Array.getElem_mem hi)
    have hprefix : sourceLeafSum (doc.body.toList.take (i + 1)) =
        sourceLeafSum (doc.body.toList.take i) + Struct.leafCountBlocks #[doc.body[i]] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hi), sourceLeafSum_append]
      simp only [sourceLeafSum, List.map_singleton, List.sum_cons, List.sum_nil, Nat.add_zero,
        Array.getElem_toList]
    have hc := collectDocBlock_census rd doc cover frameSpans doc.frameNumbers i hi st
      xs hb hx hr hs.1 pick
    refine ⟨hc.1, ?_, ?_⟩
    · rw [collectDocBlock_leafNext _ _ _ _ _ _ _ _ _ hb hx, hs.2.1, hprefix]
      omega
    · intro hd
      obtain ⟨hprev, hstep⟩ := hc.2 hd
      obtain ⟨hinit, he⟩ := hs.2.2 hprev
      refine ⟨hinit, ?_⟩
      rw [hstep, he, sourceInkPrefix_succ, sourceInkAt_para _ _ _ _ _ hi xs hb hx,
        hs.2.1, List.append_assoc]
  unfold collectDocBody
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  dsimp only [Id.run, bind, pure, Id]
  have hresult := sourceRange_progress P 0 doc.body.size
    (fun i hi st => .yield (collectDocBlock rd doc cover frameSpans doc.frameNumbers
      i (by simpa using (List.mem_range'_1.mp hi).2) st)) (acc0, true) h0 ?_
  · simpa only [Nat.zero_add, Id.run] using And.intro hresult.1 hresult.2.2
  · intro i hi st hs
    have hib : i < doc.body.size := (by simpa using (List.mem_range'_1.mp hi).2)
    exact ⟨collectDocBlock rd doc cover frameSpans doc.frameNumbers i hib st, rfl,
      step i hib st hs⟩

/-- The collected ops, the initial page state and the postlude, the
continuation reading the exact ops placement consumes. -/
private def withLayoutOps {α : Type} (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (k : Array Op → B → (StepSt → Shipped) → α)
    (frameSpans : Array (Nat × Span) := #[])
    (pictureSpans : Array (Nat × Span) := #[]) : α := Id.run do
  -- Backend conditionals resolve here, at the backend's entry.
  let doc := pdfView doc
  -- The geometry decides whether patterns apply: a card never hyphenates.
  let pats := if geom.hyphenate then pats else none
  let font := fs.body
  let scale (u : Int) : Sp := u * geom.fontSize / font.unitsPerEm
  -- The chrome footer draws only on slides that declare it and no `\runningfoot` overrides.
  let footAllowed := doc.chromeAllowed
  let plainFoot := doc.foot.isNone && doc.pageNumbersOn
  -- The chrome footer's size is the footline's step (`Ir.footline`) and its colour a palette key.
  let footSize := Ir.scaleStep geom.fontSize Ir.footline.step
  -- One `furnitureBand` per side from one ink and gap (`furniture_symmetric`).
  let runInk := scale font.ascent + scale (-font.descent)
  let corr := scale (-font.descent)
  let xHeight := scale font.xHeight
  let tokenLen (n : String) : Option Sp :=
    (doc.tokens.find? n).map fun g => (g.resolve geom.fontSize xHeight).width
  let headsep := doc.page.headsep <|> tokenLen "headsep"
  let footskip := doc.page.footskip <|> tokenLen "footskip"
  let gapTop := doc.page.furnitureGap <|> headsep.map (furnGapOfSep · corr)
  let gapBot := doc.page.furnitureGap <|> footskip.map (furnGapOfSep · corr)
  let latexFoot := if doc.page.furnitureGap.isSome then none else footskip
  let headFurn := furnitureBand geom.vmargin runInk gapTop
  let footFurn := furnitureBand geom.vmargin runInk gapBot
  -- A footer reserves its band before anything is placed (`bodyBottom_clears_footer`).
  let geom := if doc.foot.isSome || plainFoot then
      { geom with footBand := if latexFoot.isSome then 0 else footFurn.band }
    else geom
  -- The running head reserves its band the same way (`bodyTop_clears_head`).
  let geom := if doc.head.isSome then
      { geom with headBand := headFurn.band }
    else geom
  -- TeX's `\topskip` on a TeX page: the document's own, else the class's body size (size10.clo).
  let geom := if doc.docClass.record.model == .frame then geom
    else { geom with topskip := some ((tokenLen "topskip").getD geom.fontSize) }
  -- `Design.ofDoc` resolves the document colours, the ink `Contrast.docDiags` judges.
  let design := Ir.Design.ofDoc doc
  let cover := design.cover
  let footGap := doc.page.furnitureGap.getD Ir.footline.sep
  let rd : Rd := { geom := geom, xHeight := xHeight, pats := pats, fs := fs
                   preamble := doc.preambleFace
                   styles := doc.styles
                   captionPos := doc.captionPos
                   locale := doc.info.locale
                   slides := doc.docClass.record.model == .frame
                   lists := doc.docClass.record.lists
                   frameKeys := doc.frameKeys
                   frameLabels := doc.frameLabels
                   imgs := imgs
                   pictureSpans := pictureSpans
                   headline := doc.headline
                   footGap := footGap
                   cover := some cover
                   surface := doc.surface }
  let acc0 : Acc := { pal := doc.palette
                      tokens := doc.tokens
                      frameCount := doc.frameCount
                      chromeL := if footAllowed then doc.chrome.footerLeft else none
                      chromeR := if footAllowed then doc.chrome.footerRight else none
                      standoutNote := doc.chrome.standoutNote
                      footAllowed := footAllowed
                      fg := design.fg
                      ground := Ir.Design.declared? doc.palette .page }
  -- One handout page per overlay step, collected under one frame number read off `Ir.frameNumbers`.
  let acc := collectDocBody rd doc cover frameSpans acc0
  -- Trailing fil glue stretches on the page it ends, so it reaches placement; finite glue drops.
  let accF := if acc.owed.any (·.fil) then
      { acc with ops := acc.ops.push (.skip (acc.owed.foldl Glue.add {})) }
    else acc
  -- A declared furniture-gap asymmetry that survives the reading is named.
  let preDiags := if let (some gt, some gb) := (gapTop, gapBot) then
      if gt != gb then
        acc.diags.push (Diag.of .N0021
          (s!"header and footer gaps differ by " ++
            s!"{(if gt > gb then gt - gb else gb - gt).toPtString}pt as declared; " ++
            "equal gaps are the default"))
      else acc.diags
    else acc.diags
  -- A heading's declared space above must not be the smaller (Butterick); defaults satisfy it.
  let preDiags := ["section", "subsection", "subsubsection"].foldl (fun ds element =>
    match doc.styles.find? element with
    | some st =>
      match st.before, st.after with
      | some before, some after =>
        let up := (before.resolve geom.fontSize xHeight).width
        let down := (after.resolve geom.fontSize xHeight).width
        if down > up then
          ds.push (Diag.of .W0202
            s!"'{element}' sets more space below the heading than above it"
            (help := s!"a heading binds to the text it introduces: in " ++
              s!"\\style\{{element}}\{...} keep 'after' at most 'before'")
            (detail := some s!"{down.toPtString}pt below, {up.toPtString}pt above"))
        else ds
      | _, _ => ds
    | none => ds) preDiags
  let preDiags := preDiags ++ drawnInkDiags doc
  let b0 : B := {
    geom := geom
    ascent := scale font.ascent
    descent := scale (-font.descent)
    capHeight := scale font.capHeight
    xHeight := xHeight
    pictureSpans := pictureSpans
    docBg := if design.bgDeclared then some design.bg else none
    footins := ((doc.tokens.find? "footins").getD
      (Ir.footinsDefault geom.fontSize)).resolve geom.fontSize xHeight |>.width
    noteInk := design.fg
    footGap := footGap
    diags := preDiags
  }
  let post := fun (st : StepSt) => Id.run do
    let logoSpans := st.logoSpans
    let prose := st.prose
    -- A final frame's trailing boundary has already closed its page; no empty page is added.
    let b := if !st.b.cur.blank || st.b.pages.isEmpty then
        st.b.finishPage st.b.closingOwed
      else st.b
    -- The measure against the readable band (Bringhurst §2.1.2), via memoir's copy-fitting lines.
    let shipDiags :=
      if doc.docClass.record.measureBand && doc.page.measureChecked
          && prose ≥ 4 then
        let alphabet := (List.range 26).foldl (fun acc k =>
          acc + scaledAt geom.fontSize font (font.advance (Char.ofNat ('a'.toNat + k)))) 0
        if alphabet > 0 then
          let l45 := 1415 * alphabet / 1000 + 2303 * spPerPt / 100
          let l65 := 2042 * alphabet / 1000 + 3341 * spPerPt / 100
          let cpl10 := 450 + 200 * (geom.textWidth - l45) / (l65 - l45)
          if cpl10 < 450 || cpl10 > 900 then
            let dir := if cpl10 > 900 then "narrow" else "widen"
            b.diags.push (Diag.of .W0201
              (s!"the measure holds {if cpl10 > 900 then "more" else "fewer"} characters " ++
                "per line than the readable band")
              (help := s!"{dir} the text block (\\page\{ hmargin = ... }; 66 characters " ++
                "is the ideal) or declare \\page{ measure = free }")
              (detail := some s!"about {(cpl10 + 5) / 10} characters per line, outside 45\u201390"))
          else b.diags
        else b.diags
      else b.diags
    return {
      pages := b.pages
      footGap := b.footGap
      overruns := b.overruns
      needs := b.needs
      spilled := b.spilled
      diags := shipDiags
      paragraphBreaks := b.paragraphBreaks
      labelRequests := stagedLabelRequests accF.ops
      doc := doc
      geom := geom
      xHeight := xHeight
      pats := pats
      fs := fs
      imgs := imgs
      hyphCache := acc.hyphCache
      navEntries := acc.navEntries
      logoSpans := logoSpans
      plainFoot := plainFoot
      footSize := footSize
      headY := furnHeadY headFurn (scale font.ascent)
      footY := match latexFoot with
        | some fs => latexFootY geom fs
        | none => furnFootY footFurn geom.pageH (scale (-font.descent))
      muted := design.muted }
  return k accF.ops b0 post

/-- The one shipment producer: collection, placement, and final close. -/
private def shipCore (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) (frameSpans : Array (Nat × Span) := #[])
    (pictureSpans : Array (Nat × Span) := #[]) : Shipped :=
  withLayoutOps geom fs pats doc imgs (fun staged b0 post =>
    post (placeFrom fs imgs staged { b := b0 } 0)) frameSpans pictureSpans

private theorem sourceBound_collected {n : Nat} (rd : Rd) (doc : Doc) (cover : Ir.Cover)
    (frameSpans : Array (Nat × Span)) (acc0 : Acc)
    (hp : ∀ b ∈ doc.body, ∃ xs, b = .para xs ∧ PlainInlines xs)
    (ha : acc0.ops = #[]) (hk : acc0.leafNext = 0)
    (hn : (Struct.ofDoc doc).leaves.size ≤ n) :
    (collectDocBody rd doc cover frameSpans acc0).SourceBound n := by
  apply (collectDocBody_source rd doc cover frameSpans acc0 hp ?_ ?_).1
  · simp [Spacing.Pending.SourceBound, ha]
  · simpa [hk, sourceLeafSum_ofDoc] using hn

private theorem sourceBound_trailing {n : Nat} (acc : Acc) (h : acc.SourceBound n) :
    (if acc.owed.any (·.fil) then
      { acc with ops := acc.ops.push (.skip (acc.owed.foldl Glue.add {})) }
    else acc).SourceBound n := by
  split
  · intro op ho
    rcases Array.mem_push.mp ho with ho | rfl
    · exact h op ho
    · trivial
  · exact h

private theorem shipCore_source (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span))
    (hp : ∀ b ∈ (pdfView doc).body, ∃ xs, b = .para xs ∧ PlainInlines xs) :
    ∀ p ∈ (shipCore geom fs pats doc imgs frameSpans).pages, ∀ l ∈ p.lines,
      l.SourceBound (Struct.ofDoc (pdfView doc)).leaves.size := by
  have close : ∀ (c : Prop) [Decidable c] (b : B) (n : Nat), b.SourceBound n →
      (if c then b.finishPage b.closingOwed else b).SourceBound n := by
    intro c inst b n hb
    split
    · exact sourceBound_finishPage _ _ _ hb
    · exact hb
  unfold shipCore withLayoutOps
  dsimp only [Id.run, bind, pure, Id]
  apply (close _ _ _ ?_).pages
  apply sourceBound_placeFrom
  · exact sourceBound_trailing (n := (Struct.ofDoc (pdfView doc)).leaves.size)
      _ (sourceBound_collected _ _ _ _ _ hp rfl rfl (Nat.le_refl _))
  · exact ⟨by simp, by simp, rfl, rfl, rfl⟩

private theorem census_keepHeading {n : Nat} (pick : Option Nat → Bool → Bool)
    (b : B) (j : ParaJob) (lines : Nat) (hb : b.SourceBound n) :
    Spacing.Page.census pick (b.keepHeading j lines) = Spacing.Page.census pick b := by
  unfold Spacing.Page.keepHeading
  split
  · exact census_spillPage pick b 0 hb
  · rfl

private theorem placePara_diags (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) :
    ∀ d ∈ Spacing.Page.diags b ++ Spacing.Paragraph.diags j, d ∈ Spacing.Page.diags (placePara fs b j breaks) := by
  intro d hd
  unfold placePara
  exact (reflowStep_paraLines fs (placedJob fs b j breaks) breaks _).2 d
    ((reflowStep_warnReflow { b with diags := b.diags ++ j.diags } (paragraphRecord b j breaks)
      (!(paragraphRecord b j breaks).reflows.isEmpty)).2 d hd)

private theorem clean_placePara (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) (hd : GlyphClean (Spacing.Page.diags (placePara fs b j breaks))) :
    GlyphClean (Spacing.Page.diags b) ∧ GlyphClean (Spacing.Paragraph.diags j) := by
  constructor
  · intro d hm
    exact hd d (placePara_diags fs b j breaks d (Array.mem_append.mpr (Or.inl hm)))
  · intro d hm
    exact hd d (placePara_diags fs b j breaks d (Array.mem_append.mpr (Or.inr hm)))

private theorem census_stepStaged {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (imgs : Image.Store) (st : StepSt) (op : Op)
    (hb : (StepSt.b st).SourceBound n) (ho : op.SourceBound n) (hp : op.Prose) :
    Spacing.Page.census pick (StepSt.b (stepStaged fs imgs st op)) =
      Spacing.Page.census pick (StepSt.b st) ++ op.census pick := by
  cases op <;> simp only [Op.SourceBound] at ho
  all_goals try contradiction
  case para j t =>
    obtain ⟨hj, ht⟩ := hp
    obtain ⟨hh, items, hi, he⟩ := hj
    simp only [stepStaged, Id.run, Id, pure]
    split
    all_goals
      rw [ht, Spacing.Paragraph.breaks, census_placePara_prose pick fs _ j items _ _ _ ho
        (sourceBound_keepHeading (StepSt.b st) j _ hb) hh hi he,
        census_keepHeading pick _ j _ hb]
      rfl
  all_goals
    simp only [stepStaged, Id.run, Id, pure, Op.census, List.append_nil]
    repeat' split
    all_goals exact census_of_eq pick _ _ rfl rfl

private theorem clean_stepStaged (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (op : Op) (hp : op.Prose)
    (hd : GlyphClean (Spacing.Page.diags (StepSt.b (stepStaged fs imgs st op)))) :
    GlyphClean (Spacing.Page.diags (StepSt.b st)) ∧ op.Clean := by
  cases op <;> simp only [Op.Prose] at hp
  all_goals try contradiction
  case para j t =>
    simp only [stepStaged, Id.run, Id, pure] at hd
    split at hd
    all_goals
      obtain ⟨hbefore, hj⟩ := clean_placePara fs _ j t.get hd
      exact ⟨fun d hm => hbefore d ((reflowStep_keepHeading (StepSt.b st) j _).2 d hm), hj⟩
  all_goals
    simp only [stepStaged, Id.run, Id, pure] at hd
    repeat' split at hd
    all_goals exact ⟨hd, trivial⟩

private theorem prose_keepAt (b : B) (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (si : Nat) (op : Op) (hp : op.Prose) :
    (keepAt b fs imgs staged si op).Prose := by
  cases op with
  | para j t =>
    simp only [keepAt]
    split <;> exact hp
  | _ => exact hp

private theorem census_keepAt (pick : Option Nat → Bool → Bool) (b : B)
    (fs : FontSet) (imgs : Image.Store) (staged : Array Op)
    (si : Nat) (op : Op) :
    (keepAt b fs imgs staged si op).census pick = op.census pick := by
  cases op <;> simp only [keepAt]
  all_goals first | rfl | (split <;> rfl)

private theorem clean_keepAt (b : B) (fs : FontSet) (imgs : Image.Store)
    (staged : Array Op) (si : Nat) (op : Op) :
    (keepAt b fs imgs staged si op).Clean = op.Clean := by
  cases op <;> simp only [keepAt]
  all_goals first | rfl | (split <;> rfl)

private theorem census_stepFlow {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (imgs : Image.Store) (st : FlowSt) (op : Op)
    (hb : (StepSt.b (FlowSt.placed st)).SourceBound n)
    (ho : op.SourceBound n) (hp : op.Prose) :
    Spacing.Page.census pick (StepSt.b (FlowSt.placed (stepFlow fs imgs st op))) =
      Spacing.Page.census pick (StepSt.b (FlowSt.placed st)) ++ op.census pick := by
  cases op <;> simp only [Op.Prose] at hp
  all_goals try contradiction
  all_goals exact census_stepStaged pick fs imgs (FlowSt.placed st) _ hb ho hp

private theorem clean_stepFlow (fs : FontSet) (imgs : Image.Store)
    (st : FlowSt) (op : Op) (hp : op.Prose)
    (hd : GlyphClean (Spacing.Page.diags (StepSt.b (FlowSt.placed (stepFlow fs imgs st op))))) :
    GlyphClean (Spacing.Page.diags (StepSt.b (FlowSt.placed st))) ∧ op.Clean := by
  cases op <;> simp only [Op.Prose] at hp
  all_goals try contradiction
  all_goals exact clean_stepStaged fs imgs (FlowSt.placed st) _ hp hd

private theorem census_placeFlowFrom {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (imgs : Image.Store) (staged : Array Op)
    (st : FlowSt) (si : Nat)
    (ho : ∀ op ∈ staged, op.SourceBound n)
    (hp : ∀ op ∈ staged, op.Prose)
    (hb : (StepSt.b (FlowSt.placed st)).SourceBound n) :
    let out := placeFlowFrom fs imgs staged st si
    Spacing.Page.census pick (StepSt.b (FlowSt.placed out)) =
        Spacing.Page.census pick (StepSt.b (FlowSt.placed st)) ++
          (staged.toList.drop si).flatMap (Op.census pick) ∧
      (GlyphClean (Spacing.Page.diags (StepSt.b (FlowSt.placed out))) →
        GlyphClean (Spacing.Page.diags (StepSt.b (FlowSt.placed st))) ∧
          ∀ op ∈ staged.toList.drop si, op.Clean) := by
  rw [placeFlowFrom]
  split
  · rename_i hi
    have hso := ho _ (Array.getElem_mem hi)
    have hsp := hp _ (Array.getElem_mem hi)
    have hd : staged.toList.drop si = staged[si] :: staged.toList.drop (si + 1) := by
      simpa only [← Array.getElem_toList] using
        List.drop_eq_getElem_cons (l := staged.toList) (i := si) (by simpa)
    split
    · rename_i he
      simp only [he, Op.SourceBound] at hso
    · have hk := sourceBound_keepAt (StepSt.b (FlowSt.placed st)) fs imgs staged si _ hso
      have hkp := prose_keepAt (StepSt.b (FlowSt.placed st)) fs imgs staged si _ hsp
      have hnext := sourceBound_stepFlow fs imgs st _ hb hk
      obtain ⟨hc, hclean⟩ := census_placeFlowFrom pick fs imgs staged _ (si + 1) ho hp hnext
      constructor
      · rw [hc, census_stepFlow pick fs imgs st _ hb hk hkp,
          census_keepAt, hd, List.flatMap_cons, List.append_assoc]
      · intro hgood
        obtain ⟨hn, ht⟩ := hclean hgood
        obtain ⟨hs, hj⟩ := clean_stepFlow fs imgs st _ hkp hn
        rw [clean_keepAt] at hj
        refine ⟨hs, ?_⟩
        rw [hd]
        intro op hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hj
        · exact ht op hm
  · rename_i hi
    have hd : staged.toList.drop si = [] := List.drop_eq_nil_iff.mpr (by simpa using Nat.le_of_not_lt hi)
    simp only [hd, List.flatMap_nil, List.append_nil, List.not_mem_nil, false_implies,
      implies_true, and_true, true_and]
    exact fun h => h
termination_by staged.size - si
decreasing_by omega

private theorem census_placeFrom {n : Nat} (pick : Option Nat → Bool → Bool)
    (fs : FontSet) (imgs : Image.Store) (staged : Array Op) (st : StepSt)
    (ho : ∀ op ∈ staged, op.SourceBound n)
    (hp : ∀ op ∈ staged, op.Prose) (hb : (StepSt.b st).SourceBound n) :
    Spacing.Page.census pick (StepSt.b (placeFrom fs imgs staged st 0)) =
        Spacing.Page.census pick (StepSt.b st) ++ staged.toList.flatMap (Op.census pick) ∧
      (GlyphClean (Spacing.Page.diags (StepSt.b (placeFrom fs imgs staged st 0))) →
        GlyphClean (Spacing.Page.diags (StepSt.b st)) ∧ ∀ op ∈ staged, op.Clean) := by
  simpa only [placeFrom, List.drop_zero, Array.mem_toList_iff] using
    census_placeFlowFrom pick fs imgs staged (FlowSt.mk st []) 0 ho hp hb

private theorem census_close {n : Nat} (pick : Option Nat → Bool → Bool)
    (b : B) (hb : b.SourceBound n) :
    let out := if !(Spacing.Page.cur b).blank || (Spacing.Page.pages b).isEmpty
      then b.finishPage b.closingOwed else b
    (Spacing.Page.pages out).toList.flatMap (pageCensus pick) = Spacing.Page.census pick b := by
  dsimp only
  split
  · have hc := census_finishPage pick b b.closingOwed false hb
    change _ ++ [] = _ at hc
    simpa only [List.append_nil] using hc
  · rename_i hn
    have he : (Spacing.Page.cur b).lines = #[] := by
      have hb := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hn)).1
      simp only [PageOut.blank, Bool.not_eq_false', Bool.and_eq_true, Array.isEmpty_iff] at hb
      exact hb.1.1
    simp only [Spacing.Page.census, pageCensus, he, Array.toList_empty, List.flatMap_nil, List.append_nil]

private theorem clean_close (b : B) :
    let out := if !(Spacing.Page.cur b).blank || (Spacing.Page.pages b).isEmpty
      then b.finishPage b.closingOwed else b
    GlyphClean (Spacing.Page.diags out) → GlyphClean (Spacing.Page.diags b) := by
  dsimp only
  split
  · intro hd d hm
    exact hd d ((reflowStep_finishPage b b.closingOwed false).2 d hm)
  · exact fun h => h

private theorem clean_measured (a b c : Prop) [Decidable a] [Decidable b] [Decidable c]
    (ds : Array Diag) (d : Diag)
    (h : GlyphClean (if a then if b then if c then ds.push d else ds else ds else ds)) :
    GlyphClean ds := by
  repeat' split at h
  all_goals first | exact h | exact fun e he => h e (Array.mem_push.mpr (Or.inl he))

private theorem shipCore_census (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (pick : Option Nat → Bool → Bool)
    (hp : ∀ b ∈ (pdfView doc).body, ∃ xs, b = .para xs ∧ PlainInlines xs)
    (hh : geom.hyphenate = false ∨ pats = none) :
    GlyphClean (shipCore geom fs pats doc imgs frameSpans).diags →
      inkCensus ((shipCore geom fs pats doc imgs frameSpans).pages.toList.flatMap
        (pageCensus pick)) =
      sourceInkPrefix pick (pdfView doc).body 0 true (pdfView doc).body.size := by
  unfold shipCore withLayoutOps
  dsimp (config := { zeta := false }) only [Id.run, bind, pure, Id]
  extract_lets d ps font scale footAllowed plainFoot footSize runInk corr xHeight
    tokenLen headsep footskip gapTop gapBot latexFoot headFurn footFurn g1 g2 g
    design cover footGap rd acc0 acc accF preDiags1 preDiags2 preDiags b0
    alphabet l45 l65 cpl10 dir post
  have hacc := collectDocBody_census rd d cover frameSpans acc0 hp
    (by rcases hh with hh | hh <;>
      simp only [rd, ps, hh, Bool.false_eq_true, ↓reduceIte, ite_self])
    (by intro op ho; simp [acc0] at ho) pick
  have htrail : acc.GapAppend accF := by
    dsimp only [accF]
    split
    · exact ⟨#[Op.skip ((Spacing.Pending.owed acc).foldl Glue.add {})], by simp, by simp [Op.Gap]⟩
    · exact ⟨#[], by simp, by simp⟩
  have hprose : ∀ op ∈ accF.ops, op.Prose := htrail.prose hacc.1
  have hbound : ∀ op ∈ accF.ops, op.SourceBound (Struct.ofDoc d).leaves.size :=
    sourceBound_trailing acc
      (sourceBound_collected rd d cover frameSpans acc0 hp rfl rfl (Nat.le_refl _))
  have hb0 : b0.SourceBound (Struct.ofDoc d).leaves.size :=
    Spacing.Page.SourceBound.mk (by simp [b0]) (by simp [b0]) rfl rfl rfl
  have hplaced := census_placeFrom pick fs imgs accF.ops { b := b0 } hbound hprose hb0
  have hbp := sourceBound_placeFrom fs imgs accF.ops { b := b0 } 0 hbound hb0
  have hstage : accF.ops.toList.flatMap (Op.census pick) = accF.census pick := rfl
  intro hd
  have hc : GlyphClean (Spacing.Page.diags (StepSt.b (placeFrom fs imgs accF.ops { b := b0 } 0))) := by
    apply clean_close
    exact clean_measured _ _ _ _ _ hd
  have hac : acc.Clean := htrail.clean (hplaced.2 hc).2
  have he := (hacc.2 hac).2
  change inkCensus (acc.census pick) = [] ++
    sourceInkPrefix pick d.body 0 true d.body.size at he
  change inkCensus ((Spacing.Page.pages (if _ then _ else _)).toList.flatMap _) = _
  rw [census_close pick _ hbp, hplaced.1, hstage, htrail.census]
  simpa only [Spacing.Page.census, pageCensus, b0, acc0, Spacing.Pending.census, Array.toList_empty,
    List.flatMap_nil, List.append_nil, List.nil_append, inkCensus, List.filter_nil] using he

private theorem sourceInkPrefix_body (body : Array Block)
    (hp : ∀ b ∈ body, ∃ xs, b = .para xs ∧ PlainInlines xs)
    (n : Nat) (hn : n ≤ body.size) :
    sourceInkPrefix (fun _ counted => counted) body 0 true n =
      inkCensus (Ir.blockTextList "" (body.toList.take n)).toList := by
  induction n with
  | zero => simp [sourceInkPrefix, Ir.blockTextList, inkCensus]
  | succ n ih =>
    have hi : n < body.size := by omega
    obtain ⟨xs, hx, hp⟩ := hp body[n] (Array.getElem_mem hi)
    rw [sourceInkPrefix_succ, ih (by omega),
      sourceInkAt_para _ _ _ _ _ hi xs hx hp,
      List.take_succ_eq_append_getElem (by simpa using hi),
      Ir.blockTextList_append]
    simp only [↓reduceIte, Array.getElem_toList, hx,
      Ir.blockTextList, Ir.blockTextOne, String.toList_append,
      inkCensus, List.filter_append]

private def frameOpeningsCore (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span)) : Array FrameOpening :=
  withLayoutOps geom fs pats doc imgs (fun staged _ _ =>
    staged.filterMap Op.frameOpening?) frameSpans

private def labelRequestsCore (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span)) :
    Array LabelAudit.Request :=
  withLayoutOps geom fs pats doc imgs (fun staged _ _ => stagedLabelRequests staged) frameSpans

/-- The pre-marks pipeline over the shipment. -/
private def runCore (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) (frameSpans : Array (Nat × Span) := #[])
    (pictureSpans : Array (Nat × Span) := #[]) : Out :=
  let sh := shipCore geom fs pats doc imgs frameSpans pictureSpans
  auditLabelInk fs sh.labelRequests (runPost sh)

/-- Whether no collected palette epoch removes `bg`,
the precondition of the all-pages background claim. -/
private def pageGroundsDeclaredCore (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) : Bool :=
  withLayoutOps geom fs pats doc imgs fun staged _ _ =>
    staged.all Op.preservesGround

private def resolveDocMath (fs : FontSet) (doc : Doc) : Doc × Array Diag :=
  let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
  Ir.resolveMathAlphas fs.mathAlphabets family doc

/-- The pages placement ships, before the running furniture and print marks `run` adds. -/
public def ship (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) (frameSpans : Array (Nat × Span) := #[])
    (pictureSpans : Array (Nat × Span) := #[]) : Shipped :=
  shipCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans pictureSpans

/-- The frame decisions the collector emits, before placement. -/
public def frameOpenings (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) (frameSpans : Array (Nat × Span) := #[]) :
    Array FrameOpening :=
  frameOpeningsCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans

/-- Label occurrences the collector selects, before pagination. -/
public def labelRequests (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) (frameSpans : Array (Nat × Span) := #[]) :
    Array LabelAudit.Request :=
  labelRequestsCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans

/-- Whether no palette epoch of the document `run` sets removes `bg`. -/
public def pageGroundsDeclared (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) : Bool :=
  pageGroundsDeclaredCore geom fs pats (resolveDocMath fs doc).1 imgs

/-- Typeset a document body into positioned pages: placement, the furniture pass, then printer's
cut marks (`addMarks`); `frameSpans` and `pictureSpans` carry source provenance only. -/
public def run (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns) (doc : Doc)
    (imgs : Image.Store := {}) (frameSpans : Array (Nat × Span) := #[])
    (pictureSpans : Array (Nat × Span) := #[]) : Out :=
  let (doc, diags) := resolveDocMath fs doc
  let out := addMarks (runCore geom fs pats doc imgs frameSpans pictureSpans) (markFillsOf geom doc)
  { out with diags := diags ++ out.diags }

/-- The body index of the `k`-th block `pdfView` keeps, inverting `frameSpansForPdf`. -/
public def pdfSourceIndex (doc : Doc) (k : Nat) : Option Nat :=
  ((List.range doc.body.size).filter fun i =>
    (doc.body[i]?.map (keptBy "pdf")).getD false)[k]?

/-- The frames the overflow ladder decides: top-level
frames not declared breakable, by body index. -/
public def ladderFrames (doc : Doc) : Array Nat :=
  (List.range doc.body.size).toArray.filter fun i =>
    match doc.body[i]? with
    | some (.frame _ _ _ breakable _) => !breakable
    | some _ | none => false

/-- The overflow ladder's decision for each frame
step its first setting measured (`Ir.frameFit`). -/
public def stepDecisions (first : Out) : Array (FrameOrigin × Ir.FrameFit) :=
  let keys := ((first.needs.map (·.1) ++ first.overruns.map (·.1)).toList.eraseDups.toArray.qsort
    fun a b => a.source < b.source || (a.source == b.source && a.step < b.step))
  keys.map fun o =>
    let needed := ((first.needs.find? (·.1 == o)).map (·.2)).getD 0
    match first.overruns.find? (·.1 == o) with
    | some (_, beyond, clearance) => (o, Ir.frameFit needed beyond clearance)
    | none => (o, Ir.frameFit needed 0 0)

/-- The document as the ladder sets it, each decided frame step marked by its decision. -/
public def fittedDoc (doc : Doc) (decisions : Array (FrameOrigin × Ir.FrameFit)) : Doc :=
  let marks := decisions.filterMap fun (o, fit) =>
    match fit with
    | .overfull _ => (pdfSourceIndex doc o.source).map (·, Ir.fitOverhangRole o.step)
    | .continued _ => (pdfSourceIndex doc o.source).map (·, Ir.fitContinuesRole o.step)
    | .natural | .shrunk => none
  { doc with body := Ir.markFramesAt doc.body marks }

/-- What the ladder names of the setting `final`: each marked
step that reached past its text area, continued or overfull. -/
public def fitAccount (first final : Out) : Array (FrameOrigin × Ir.FrameFit) :=
  let measured (o : FrameOrigin) (x : Sp) : Sp :=
    ((first.overruns.find? (·.1 == o)).map (·.2.1)).getD x
  let steps := final.overruns.map fun (o, x, _) =>
    if final.spilled.contains o then (o, Ir.FrameFit.continued (measured o x))
    else (o, .overfull x)
  steps ++ (final.spilled.filter fun o => !final.overruns.any (·.1 == o)).map fun o =>
    (o, Ir.FrameFit.continued (measured o 0))

/-- The overruns the continuing steps of frame `k` measured. -/
private def continuedBy (steps : List (FrameOrigin × Ir.FrameFit)) (k : Nat) : List Sp :=
  steps.filterMap fun p => match p.2 with
    | .continued c => if p.1.source == k then some c else none
    | .natural | .shrunk | .overfull _ => none

/-- The overhangs the overfull steps of frame `k` stood. -/
private def overfullBy (steps : List (FrameOrigin × Ir.FrameFit)) (k : Nat) : List Sp :=
  steps.filterMap fun p => match p.2 with
    | .overfull v => if p.1.source == k then some v else none
    | .natural | .shrunk | .continued _ => none

/-- Frame `k`'s one account from its steps: continued with
the largest overrun where any continued, else overfull. -/
private def frameEntry (steps : List (FrameOrigin × Ir.FrameFit)) (k : Nat) :
    Option (Nat × Ir.FrameFit × Option Sp) :=
  match (continuedBy steps k).max?, (overfullBy steps k).max? with
  | some c, v => some (k, .continued c, v)
  | none, some v => some (k, .overfull v, none)
  | none, none => none

/-- One account per frame each step of `steps` moved, by its index in the PDF's view. -/
public def frameAccount (steps : List (FrameOrigin × Ir.FrameFit)) :
    List (Nat × Ir.FrameFit × Option Sp) :=
  (steps.map (·.1.source)).eraseDups.filterMap (frameEntry steps)

private theorem frameEntry_moved (steps : List (FrameOrigin × Ir.FrameFit)) (k : Nat)
    (e : Nat × Ir.FrameFit × Option Sp) (h : frameEntry steps k = some e) :
    e.1 = k ∧ e.2.1.moved := by
  unfold frameEntry at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact ⟨rfl, rfl⟩

public theorem frameAccount_moved (steps : List (FrameOrigin × Ir.FrameFit))
    (e : Nat × Ir.FrameFit × Option Sp) (he : e ∈ frameAccount steps) : e.2.1.moved := by
  obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp he
  exact (frameEntry_moved steps k e hk).2

public theorem frameAccount_covers (steps : List (FrameOrigin × Ir.FrameFit))
    (o : FrameOrigin) (fit : Ir.FrameFit) (hs : (o, fit) ∈ steps) (hm : fit.moved) :
    ∃ e ∈ frameAccount steps, e.1 = o.source ∧ (fit.continues → e.2.1.continues) := by
  have hk : o.source ∈ (steps.map (·.1.source)).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_map.mpr ⟨(o, fit), hs, rfl⟩)
  have entry : ∀ e, frameEntry steps o.source = some e → e ∈ frameAccount steps :=
    fun e h => List.mem_filterMap.mpr ⟨o.source, hk, h⟩
  cases fit with
  | natural => exact absurd hm (by simp [Ir.FrameFit.moved])
  | shrunk => exact absurd hm (by simp [Ir.FrameFit.moved])
  | continued c =>
    have hc : c ∈ continuedBy steps o.source :=
      List.mem_filterMap.mpr ⟨(o, .continued c), hs, by simp⟩
    cases hmax : (continuedBy steps o.source).max? with
    | none => exact absurd (List.max?_eq_none_iff.mp hmax ▸ hc) (by simp)
    | some m =>
      have he : frameEntry steps o.source =
          some (o.source, .continued m, (overfullBy steps o.source).max?) := by
        simp only [frameEntry, hmax]
      exact ⟨_, entry _ he, rfl, fun _ => rfl⟩
  | overfull v =>
    have hv : v ∈ overfullBy steps o.source :=
      List.mem_filterMap.mpr ⟨(o, .overfull v), hs, by simp⟩
    cases hover : (overfullBy steps o.source).max? with
    | none => exact absurd (List.max?_eq_none_iff.mp hover ▸ hv) (by simp)
    | some w =>
      cases hcont : (continuedBy steps o.source).max? with
      | none =>
        have he : frameEntry steps o.source = some (o.source, .overfull w, none) := by
          simp only [frameEntry, hcont, hover]
        exact ⟨_, entry _ he, rfl, fun h => absurd h (by simp [Ir.FrameFit.continues])⟩
      | some c =>
        have he : frameEntry steps o.source = some (o.source, .continued c, some w) := by
          simp only [frameEntry, hcont, hover]
        exact ⟨_, entry _ he, rfl, fun h => absurd h (by simp [Ir.FrameFit.continues])⟩

/-- The overflow ladder's result: the pages, the IR document they set,
each frame step's decision, and the frames the web deck squeezes. -/
public structure Fitted where
  out : Out
  setting : Doc
  decisions : Array (FrameOrigin × Ir.FrameFit) := #[]
  webSqueeze : Array Nat := #[]

/-- The overflow ladder (`Ir.frameFit`): set every unbreakable frame to measure, decide each
step as beamer sets it, set the document again where needed, name every frame moved once, and
ship the pages (`PageOut.shipped`). -/
public def runFitted (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns) (doc : Doc)
    (imgs : Image.Store := {}) (frameSpans : Array (Nat × Span) := #[])
    (pictureSpans : Array (Nat × Span) := #[]) : Fitted :=
  let measured := { doc with body := Ir.markFrames doc.body (ladderFrames doc) Ir.fitMeasureRole }
  let first := run geom fs pats measured imgs frameSpans pictureSpans
  let decisions := stepDecisions first
  let setting := if first.overruns.isEmpty then measured else fittedDoc doc decisions
  let final := if first.overruns.isEmpty then first
    else run geom fs pats setting imgs frameSpans pictureSpans
  let labels := (pdfView doc).frameLabels
  let account := (frameAccount (fitAccount first final).toList).toArray.filterMap
    fun (k, fit, also) =>
      fitDiag fit (labels[k]?.getD none) ((frameSpans.find? (·.1 == k)).map (·.2)) also
  let webSqueeze := ((decisions.filterMap fun (o, fit) =>
    match fit with
    | .natural => none
    | .shrunk | .overfull _ | .continued _ =>
      (pdfSourceIndex doc o.source).bind fun i => match doc.body[i]? with
        | some (.frame _ _ _ _ fbody) =>
          if Ir.frameSqueeze fbody == .none && Ir.holdsList fbody then some i else none
        | some _ | none => none).toList.eraseDups).toArray
  { out := { final with pages := final.pages.map PageOut.shipped, diags := final.diags ++ account },
    setting, decisions, webSqueeze }

public theorem runFitted_projects (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans pictureSpans : Array (Nat × Span)) :
    let f := runFitted geom fs pats doc imgs frameSpans pictureSpans
    f.out.pages = (run geom fs pats f.setting imgs frameSpans pictureSpans).pages.map
        PageOut.shipped ∧
      ∃ account, f.out.diags = (run geom fs pats f.setting imgs frameSpans pictureSpans).diags ++
        account := by
  simp only [runFitted]
  split
  · exact ⟨rfl, _, rfl⟩
  · exact ⟨rfl, _, rfl⟩

public theorem runFitted_accounts (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans pictureSpans : Array (Nat × Span))
    (o : FrameOrigin) (fit : Ir.FrameFit)
    (hs : (o, fit) ∈ fitAccount
      (run geom fs pats
        { doc with body := Ir.markFrames doc.body (ladderFrames doc) Ir.fitMeasureRole }
        imgs frameSpans pictureSpans)
      (run geom fs pats (runFitted geom fs pats doc imgs frameSpans pictureSpans).setting
        imgs frameSpans pictureSpans))
    (hm : fit.moved) :
    ∃ d ∈ (runFitted geom fs pats doc imgs frameSpans pictureSpans).out.diags,
      d.subject = (pdfView doc).frameLabels[o.source]?.getD none ∧
        (fit.continues → d.kind = .W0384) := by
  have named : ∀ first final : Out, (o, fit) ∈ fitAccount first final →
      ∃ d ∈ (frameAccount (fitAccount first final).toList).toArray.filterMap
          (fun (e : Nat × Ir.FrameFit × Option Sp) =>
            fitDiag e.2.1 ((pdfView doc).frameLabels[e.1]?.getD none)
              ((frameSpans.find? (·.1 == e.1)).map (·.2)) e.2.2),
        d.subject = (pdfView doc).frameLabels[o.source]?.getD none ∧
          (fit.continues → d.kind = .W0384) := by
    intro first final h
    obtain ⟨e, he, hk, hc⟩ := frameAccount_covers _ o fit (Array.mem_toList_iff.mpr h) hm
    have hmv := frameAccount_moved _ e he
    obtain ⟨k, f, also⟩ := e
    simp only at hk hc hmv
    subst hk
    cases f with
    | natural => simp [Ir.FrameFit.moved] at hmv
    | shrunk => simp [Ir.FrameFit.moved] at hmv
    | overfull v =>
      refine ⟨_, Array.mem_filterMap.mpr ⟨_, List.mem_toArray.mpr he, rfl⟩, rfl, fun h => ?_⟩
      exact absurd (hc h) (by simp [Ir.FrameFit.continues])
    | continued c =>
      exact ⟨_, Array.mem_filterMap.mpr ⟨_, List.mem_toArray.mpr he, rfl⟩, rfl, fun _ => rfl⟩
  simp only [runFitted] at hs ⊢
  split at hs <;> simp only [*, ite_true, ite_false, Bool.false_eq_true] <;>
    · obtain ⟨d, hd, hsub, hk⟩ := named _ _ hs
      exact ⟨d, Array.mem_append.mpr (Or.inr hd), hsub, hk⟩

private theorem keepFor_plain_body (backend : String) (body : Array Block)
    (h : ∀ b ∈ body, ∃ xs, b = .para xs ∧ PlainInlines xs) :
    Ir.keepFor backend body = body := by
  apply Ir.keepFor_id
  change Ir.onlyFreeList body.toList = true
  have each : ∀ b ∈ body.toList, Ir.onlyFreeOne b = true := by
    intro b hb
    obtain ⟨xs, rfl, _⟩ := h b (by simpa using hb)
    rfl
  generalize body.toList = bs at *
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [Ir.onlyFreeList, each b (by simp), Bool.true_and]
    exact ih (fun b hb => each b (by simp [hb]))

private theorem resolveAlpha_plain_inlines (coverage : Math.MathAlphabetCoverage)
    (xs : Array Inline) (h : PlainInlines xs) :
    Ir.mapInlines (Ir.resolveMathAlphaInline coverage) xs = xs := by
  have aux : ∀ (ys : List Inline) (acc : Array Inline),
      (∀ y ∈ ys, ∃ s, y = .text s) →
      Ir.mapInlineList (Ir.resolveMathAlphaInline coverage) acc ys = acc ++ ys.toArray := by
    intro ys
    induction ys with
    | nil => intro acc _; simp [Ir.mapInlineList]
    | cons y ys ih =>
      intro acc hp
      obtain ⟨s, rfl⟩ := hp y (by simp)
      rw [Ir.mapInlineList, ih _ (fun y hy => hp y (by simp [hy]))]
      apply Array.toList_inj.mp
      simp [Ir.mapInline, Ir.resolveMathAlphaInline]
  simpa [Ir.mapInlines] using aux xs.toList #[] (by simpa [PlainInlines] using h)

private theorem resolveMathAlphas_plain_body (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc)
    (h : ∀ b ∈ doc.body, ∃ xs, b = .para xs ∧ PlainInlines xs) :
    (Ir.resolveMathAlphas coverage family doc).1.body = doc.body := by
  have aux : ∀ (bs : List Block) (acc : Array Block),
      (∀ b ∈ bs, ∃ xs, b = .para xs ∧ PlainInlines xs) →
      Ir.mapBlockList (Ir.resolveMathAlphaPicture coverage) (Ir.resolveMathAlphaInline coverage)
        acc bs = acc ++ bs.toArray := by
    intro bs
    induction bs with
    | nil => intro acc _; simp [Ir.mapBlockList]
    | cons b bs ih =>
      intro acc hp
      obtain ⟨xs, rfl, hx⟩ := hp b (by simp)
      rw [Ir.mapBlockList, ih _ (fun b hb => hp b (by simp [hb]))]
      apply Array.toList_inj.mp
      simp [Ir.mapBlock, resolveAlpha_plain_inlines coverage xs hx]
  simpa [Ir.resolveMathAlphas, Ir.mapDoc, Ir.mapBlocksPic] using
    aux doc.body.toList #[] (by simpa using h)

public def LineOut.glyphChars (line : LineOut) : List Char :=
  line.segs.toList.flatMap Seg.glyphChars

/-- Every body block is a paragraph of literal text. -/
@[expose] public def PlainParagraphs (body : Array Block) : Prop :=
  ∀ b ∈ body, ∃ xs, b = .para xs ∧ (∀ x ∈ xs, ∃ s, x = .text s)

private theorem pageCensus_filter (pick : Option Nat → Bool → Bool) (p : PageOut) :
    pageCensus pick p =
      (p.lines.filter fun l => pick l.leaf l.counted).toList.flatMap LineOut.glyphChars := by
  simp only [pageCensus, Array.toList_filter]
  generalize p.lines.toList = ls
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases h : pick l.leaf l.counted <;>
      simp [List.flatMap_cons, lineCensus, LineOut.glyphChars, h, ih]

private theorem pageCensus_filter_fun (pick : Option Nat → Bool → Bool) :
    pageCensus pick = fun p =>
      (p.lines.filter fun l => pick l.leaf l.counted).toList.flatMap LineOut.glyphChars :=
  funext (pageCensus_filter pick)

private theorem ship_census (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (pick : Option Nat → Bool → Bool)
    (hplain : PlainParagraphs doc.body) (hh : geom.hyphenate = false ∨ pats = none)
    (hd : GlyphClean (ship geom fs pats doc imgs frameSpans).diags) :
    inkCensus ((ship geom fs pats doc imgs frameSpans).pages.toList.flatMap
      (pageCensus pick)) = sourceInkPrefix pick doc.body 0 true doc.body.size := by
  have hm : (resolveDocMath fs doc).1.body = doc.body :=
    resolveMathAlphas_plain_body _ _ doc hplain
  have hb : (pdfView (resolveDocMath fs doc).1).body = doc.body := by
    change Ir.keepFor "pdf" (resolveDocMath fs doc).1.body = doc.body
    rw [hm, keepFor_plain_body _ _ hplain]
  have h := shipCore_census geom fs pats (resolveDocMath fs doc).1 imgs frameSpans pick
    (by rw [hb]; exact hplain) hh hd
  simpa only [ship, hb] using h

/-- The literal glyph text a source paragraph owns, at its opening structural leaf. -/
public def paragraphSourceInk (body : Array Block) (k : Nat) : List Char :=
  sourceInkPrefix (fun leaf _ => leaf == some k) body 0 true body.size

public theorem ship_paras_body_exact (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (hplain : PlainParagraphs doc.body)
    (hh : geom.hyphenate = false ∨ pats = none)
    (hd : ∀ d ∈ (ship geom fs pats doc imgs frameSpans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") :
    inkCensus ((ship geom fs pats doc imgs frameSpans).pages.toList.flatMap fun p =>
      (p.lines.filter (·.counted)).toList.flatMap LineOut.glyphChars) =
      inkCensus (Ir.blocksText doc.body).toList := by
  have h := ship_census geom fs pats doc imgs frameSpans
    (fun _ counted => counted) hplain hh hd
  have hs := sourceInkPrefix_body doc.body hplain doc.body.size (Nat.le_refl _)
  rw [← Array.length_toList, List.take_length] at hs
  simpa only [pageCensus_filter_fun, Ir.blocksText] using h.trans hs

public theorem ship_paras_leaf_exact (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (hplain : PlainParagraphs doc.body)
    (hh : geom.hyphenate = false ∨ pats = none)
    (hd : ∀ d ∈ (ship geom fs pats doc imgs frameSpans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") (k : Nat) :
    inkCensus ((ship geom fs pats doc imgs frameSpans).pages.toList.flatMap fun p =>
      (p.lines.filter fun l => l.leaf == some k).toList.flatMap LineOut.glyphChars) =
      paragraphSourceInk doc.body k := by
  simpa only [pageCensus_filter_fun, paragraphSourceInk] using
    ship_census geom fs pats doc imgs frameSpans
      (fun leaf _ => leaf == some k) hplain hh hd


private theorem noGlyph_glyphChars (line : LineOut)
    (h : ∀ s ∈ line.segs, s.NoGlyph) : line.glyphChars = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro s hs
  have hh := h s (by simpa using hs)
  cases s <;> simp only [Seg.NoGlyph, Seg.glyphChars] at hh ⊢
  all_goals first | rfl | simp [hh]

private theorem sourceBound_run (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (hplain : PlainParagraphs doc.body) :
    ∀ p ∈ (run geom fs pats doc imgs frameSpans).pages, ∀ l ∈ p.lines,
      l.furniture = false → l.SourceBound (Struct.ofDoc (pdfView doc)).leaves.size := by
  have hm : (resolveDocMath fs doc).1.body = doc.body :=
    resolveMathAlphas_plain_body _ _ doc hplain
  have he : (pdfView (resolveDocMath fs doc).1).body = (pdfView doc).body := by
    simp only [pdfView, hm]
  have hp : ∀ b ∈ (pdfView (resolveDocMath fs doc).1).body,
      ∃ xs, b = .para xs ∧ PlainInlines xs := by
    change ∀ b ∈ Ir.keepFor "pdf" (resolveDocMath fs doc).1.body, _
    rw [hm, keepFor_plain_body _ _ hplain]
    exact hplain
  have ht : Struct.ofDoc (pdfView (resolveDocMath fs doc).1) =
      Struct.ofDoc (pdfView doc) := by
    simp only [Struct.ofDoc, he]
  intro p hpage l hline hf
  simp only [run, runCore, addMarks, auditLabelInk] at hpage
  obtain ⟨q, hq, rfl⟩ := Array.mem_map.mp hpage
  have hs := sourceBound_runPost _
    (shipCore_source geom fs pats (resolveDocMath fs doc).1 imgs frameSpans hp)
    q hq l hline hf
  simpa only [ht] using hs

public theorem lines_attributed_covers (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (hplain : PlainParagraphs doc.body) :
    ∀ p ∈ (run geom fs pats doc imgs frameSpans).pages, ∀ l ∈ p.lines,
      l.furniture = false → l.glyphChars ≠ [] →
      ∃ k, l.leaf = some k ∧ k < (Struct.ofDoc (pdfView doc)).leaves.size := by
  intro p hp l hl hf hi
  rcases sourceBound_run geom fs pats doc imgs frameSpans hplain p hp l hl hf with h | h
  · exact h
  · exact False.elim (hi (noGlyph_glyphChars l h))

public theorem ship_labelRequests_projects (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    (ship geom fs pats doc imgs frameSpans).labelRequests =
      labelRequests geom fs pats doc imgs frameSpans := by
  rfl

public theorem run_labelObservations_projects (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    labelObservations fs (run geom fs pats doc imgs frameSpans).pages =
      labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages := by
  simp only [run, runCore, ship, addMarks, auditLabelInk, labelObservations,
    Array.flatMap_map]

public theorem run_label_accounts (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (r : LabelAudit.Request)
    (hr : r ∈ labelRequests geom fs pats doc imgs frameSpans) :
    LabelAudit.accounted r (labelObservations fs (run geom fs pats doc imgs frameSpans).pages)
      (run geom fs pats doc imgs frameSpans).diags := by
  rw [run_labelObservations_projects]
  have hr' : r ∈ (ship geom fs pats doc imgs frameSpans).labelRequests := by
    rw [ship_labelRequests_projects]
    exact hr
  have h := LabelAudit.finish_accounts
    (ship geom fs pats doc imgs frameSpans).labelRequests
    (labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages)
    (runPost (ship geom fs pats doc imgs frameSpans)).diags r hr'
  apply LabelAudit.accounted_mono _ _ _ _ h
  intro d hd
  simpa only [run, runCore, ship, addMarks, auditLabelInk] using
    (Array.mem_append.mpr (Or.inr hd) :
      d ∈ (resolveDocMath fs doc).2 ++
        LabelAudit.finish (ship geom fs pats doc imgs frameSpans).labelRequests
          (labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages)
          (runPost (ship geom fs pats doc imgs frameSpans)).diags)

public theorem run_label_observed_accounts (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (o : LabelAudit.Observation)
    (ho : o ∈ labelObservations fs (run geom fs pats doc imgs frameSpans).pages) :
    LabelAudit.Observed o (run geom fs pats doc imgs frameSpans).diags := by
  rw [run_labelObservations_projects] at ho
  have h := LabelAudit.finish_observed_accounts
    (ship geom fs pats doc imgs frameSpans).labelRequests
    (labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages)
    (runPost (ship geom fs pats doc imgs frameSpans)).diags o ho
  apply LabelAudit.Observed.mono _ _ _ h
  intro d hd
  simpa only [run, runCore, ship, addMarks, auditLabelInk] using
    (Array.mem_append.mpr (Or.inr hd) :
      d ∈ (resolveDocMath fs doc).2 ++
        LabelAudit.finish (ship geom fs pats doc imgs frameSpans).labelRequests
          (labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages)
          (runPost (ship geom fs pats doc imgs frameSpans)).diags)

public theorem run_label_unknown_named (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (o : LabelAudit.Observation)
    (ho : o ∈ labelObservations fs (run geom fs pats doc imgs frameSpans).pages)
    (hu : o.known = false) :
    LabelAudit.named o.stamp.key o.stamp.source .W0394
      (run geom fs pats doc imgs frameSpans).diags := by
  rw [run_labelObservations_projects] at ho
  have h := LabelAudit.finish_unknown_named
    (ship geom fs pats doc imgs frameSpans).labelRequests
    (labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages)
    (runPost (ship geom fs pats doc imgs frameSpans)).diags o ho hu
  apply LabelAudit.named_mono _ _ _ _ _ h
  intro d hd
  simpa only [run, runCore, ship, addMarks, auditLabelInk] using
    (Array.mem_append.mpr (Or.inr hd) :
      d ∈ (resolveDocMath fs doc).2 ++
        LabelAudit.finish (ship geom fs pats doc imgs frameSpans).labelRequests
          (labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages)
          (runPost (ship geom fs pats doc imgs frameSpans)).diags)

public theorem shipment_diags_covers (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span)) :
    ∀ d ∈ (ship geom fs pats doc imgs frameSpans).diags,
      ∃ e ∈ (run geom fs pats doc imgs frameSpans).diags,
        e.code = d.code ∧ e.subject = d.subject := by
  intro d hd
  obtain ⟨e, he, hc, hs⟩ := runPost_diags_covers
    (ship geom fs pats doc imgs frameSpans) d hd
  have kept := LabelAudit.finish_keeps
    (ship geom fs pats doc imgs frameSpans).labelRequests
    (labelObservations fs (runPost (ship geom fs pats doc imgs frameSpans)).pages)
    _ e he
  refine ⟨e, ?_, hc, hs⟩
  simpa only [run, runCore, ship, addMarks, auditLabelInk] using
    (Array.mem_append.mpr (Or.inr kept) :
      e ∈ (resolveDocMath fs doc).2 ++
        (auditLabelInk fs (ship geom fs pats doc imgs frameSpans).labelRequests
          (runPost (ship geom fs pats doc imgs frameSpans))).diags)

private theorem shipCore_frames (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    ∀ p ∈ (shipCore geom fs pats doc imgs frameSpans).pages,
      SelectedFrame (frameOpeningsCore geom fs pats doc imgs frameSpans) p.frameStamp := by
  have close : ∀ (c : Prop) [Decidable c] (b : B) (openings : Array FrameOpening),
      FramesFooted openings b →
      FramesFooted openings (if c then b.finishPage b.closingOwed else b) := by
    intro c inst b openings hb
    split
    · exact hb.step (frameStep_finishPage ..)
    · exact hb
  unfold shipCore frameOpeningsCore withLayoutOps
  dsimp only [Id.run, bind, pure, Id]
  apply (close _ _ _ ?_).2
  apply placeFrom_frames
  · intro op hop opening hf
    exact Array.mem_filterMap.mpr ⟨op, hop, hf⟩
  · exact ⟨Or.inl rfl, by simp⟩

public theorem ship_frames_footed (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    ∀ p ∈ (ship geom fs pats doc imgs frameSpans).pages,
      SelectedFrame (frameOpenings geom fs pats doc imgs frameSpans) p.frameStamp :=
  shipCore_frames geom fs pats (resolveDocMath fs doc).1 imgs frameSpans

private theorem shipCore_reflows (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    ReflowsNamed (shipCore geom fs pats doc imgs frameSpans).paragraphBreaks
      (shipCore geom fs pats doc imgs frameSpans).diags := by
  have close : ∀ (c : Prop) [Decidable c] (b : B), b.ReflowsNamed →
      (if c then b.finishPage b.closingOwed else b).ReflowsNamed := by
    intro c inst b hb
    split
    · exact hb.step (reflowStep_finishPage ..)
    · exact hb
  have measured : ∀ (a b c : Prop) [Decidable a] [Decidable b] [Decidable c]
      (ps : Array ParagraphBreaks) (ds : Array Diag) (d : Diag),
      ReflowsNamed ps ds →
        ReflowsNamed ps
          (if a then if b then if c then ds.push d else ds else ds else ds) := by
    intro a b c ia ib ic ps ds d h
    repeat' split
    all_goals first
      | exact h
      | exact fun p hp k hk => by
          obtain ⟨e, he, hc, hs⟩ := h p hp k hk
          exact ⟨e, Array.mem_push.mpr (Or.inl he), hc, hs⟩
  unfold shipCore withLayoutOps
  dsimp only [Id.run, bind, pure, Id]
  apply measured
  apply close
  apply placeFrom_reflows
  intro p hp
  simp at hp

public theorem ship_reflows_named (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    ReflowsNamed (ship geom fs pats doc imgs frameSpans).paragraphBreaks
      (ship geom fs pats doc imgs frameSpans).diags :=
  shipCore_reflows geom fs pats (resolveDocMath fs doc).1 imgs frameSpans

public theorem paragraph_breaks_projects (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    (run geom fs pats doc imgs frameSpans).paragraphBreaks =
      (ship geom fs pats doc imgs frameSpans).paragraphBreaks := by rfl

public theorem reflow_named (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    ReflowsNamed (run geom fs pats doc imgs frameSpans).paragraphBreaks
      (run geom fs pats doc imgs frameSpans).diags := by
  intro p hp k hk
  rw [paragraph_breaks_projects] at hp
  obtain ⟨d, hd, hc, hs⟩ :=
    ship_reflows_named geom fs pats doc imgs frameSpans p hp k hk
  obtain ⟨e, he, ec, es⟩ :=
    shipment_diags_covers geom fs pats doc imgs frameSpans d hd
  exact ⟨e, he, ec.trans hc, es.trans hs⟩

public theorem frame_pages_projects (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span)) :
    (run geom fs pats doc imgs frameSpans).pages.map (fun p => (p.frame, p.foot)) =
      (ship geom fs pats doc imgs frameSpans).pages.map (fun p => (p.frame, p.foot)) := by
  simpa only [run, runCore, ship, addMarks, auditLabelInk, Array.map_map, Function.comp_def] using
    runPost_frames_projects (shipCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans)

public theorem frame_origins_projects (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span)) :
    (run geom fs pats doc imgs frameSpans).pages.map
        (fun p => (p.frameOrigin, p.frame, p.foot)) =
      (ship geom fs pats doc imgs frameSpans).pages.map
        (fun p => (p.frameOrigin, p.frame, p.foot)) := by
  simpa only [run, runCore, ship, addMarks, auditLabelInk, Array.map_map, Function.comp_def] using
    runPost_frameOrigins_projects
      (shipCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans)

public theorem run_frames_footed (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    ∀ p ∈ (run geom fs pats doc imgs frameSpans).pages,
      SelectedFrame (frameOpenings geom fs pats doc imgs frameSpans) p.frameStamp := by
  intro p hp
  have hm : p.frameStamp ∈
      (run geom fs pats doc imgs frameSpans).pages.map
        (fun q => (q.frameOrigin, q.frame, q.foot)) :=
    Array.mem_map.mpr ⟨p, hp, rfl⟩
  rw [frame_origins_projects] at hm
  obtain ⟨q, hq, he⟩ := Array.mem_map.mp hm
  exact he ▸ ship_frames_footed geom fs pats doc imgs frameSpans q hq

public theorem frame_pages_footed (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (p : PageOut)
    (hp : p ∈ (run geom fs pats doc imgs frameSpans).pages)
    (origin : FrameOrigin) (ho : p.frameOrigin = some origin) :
    ∃ f ∈ frameOpenings geom fs pats doc imgs frameSpans,
      f.origin = some origin ∧ p.frame = f.number ∧ p.foot = f.footer := by
  rcases run_frames_footed geom fs pats doc imgs frameSpans p hp with empty | selected
  · have he := congrArg Prod.fst empty
    simp only [PageOut.frameStamp, ho] at he
    contradiction
  · obtain ⟨f, hf, he⟩ := selected
    simp only [PageOut.frameStamp, FrameOpening.stamp, Prod.mk.injEq] at he
    exact ⟨f, hf, he.1.symm.trans ho, he.2.1, he.2.2⟩

public theorem page_lifecycle_projects (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span)) :
    (run geom fs pats doc imgs frameSpans).pages.map (·.pageState) =
      (ship geom fs pats doc imgs frameSpans).pages.map (·.pageState) := by
  simpa only [run, runCore, ship, addMarks, auditLabelInk, Array.map_map, Function.comp_def] using
    runPost_lifecycle_projects (shipCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans)

public theorem lines_attributed_projects (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    (run geom fs pats doc imgs frameSpans).pages.map
        (fun p => p.lines.filter (fun l => l.leaf.isSome)) =
      (ship geom fs pats doc imgs frameSpans).pages.map
        (fun p => p.lines.filter (fun l => l.leaf.isSome)) := by
  simpa only [run, runCore, ship, addMarks, auditLabelInk, Array.map_map, Function.comp_def] using
    runPost_attributed_projects (shipCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans)

public theorem lines_counted_projects (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    (run geom fs pats doc imgs frameSpans).pages.map (fun p => p.lines.filter (·.counted)) =
      (ship geom fs pats doc imgs frameSpans).pages.map (fun p => p.lines.filter (·.counted)) := by
  simpa only [run, runCore, ship, addMarks, auditLabelInk, Array.map_map, Function.comp_def] using
    runPost_counted_projects (shipCore geom fs pats (resolveDocMath fs doc).1 imgs frameSpans)

public theorem run_resolve_pages_agree (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store) :
    (run geom fs pats
      (Ir.resolveMathAlphas fs.mathAlphabets
        (fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face") doc).1 imgs).pages =
      (run geom fs pats doc imgs).pages := by
  simp only [run, resolveDocMath]
  rw [Ir.resolveMathAlphas_fixed_point]

private theorem runCore_bg
    (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store)
    (hbg : (Ir.Design.declared? doc.palette .page).isSome = true)
    (hepoch : pageGroundsDeclaredCore geom fs pats doc imgs = true) :
    ∀ p ∈ (runCore geom fs pats doc imgs).pages,
      ∃ f ∈ p.fills.toList,
        f.x = -geom.bleed ∧ f.y = -geom.bleed ∧ f.w = geom.pageW + 2 * geom.bleed ∧
          f.h = geom.pageH + 2 * geom.bleed := by
  have key : ∀ (b0 c : B), BgStep b0 c →
      b0.docBg.isSome = true → b0.pages = #[] →
      ∀ x ∈ c.pages, bgFilled b0.geom x := by
    intro b0 c hc hd hemp x hx
    rcases hc.2.2 hd x hx with h | h
    · rw [hemp] at h
      simp at h
    · exact h
  intro p hp
  change p ∈ (runPost (shipCore geom fs pats doc imgs)).pages at hp
  unfold shipCore withLayoutOps at hp
  unfold pageGroundsDeclaredCore withLayoutOps at hepoch
  dsimp only [Id.run, bind, pure, Id] at hp hepoch
  obtain ⟨q, hq, hfills, -, -, -, -⟩ := runPost_pages _ p hp
  have fin : ∀ (b0 : B), bgFilled b0.geom q →
      b0.geom.pageW = geom.pageW → b0.geom.pageH = geom.pageH →
      b0.geom.bleed = geom.bleed →
      ∃ f ∈ p.fills.toList,
        f.x = -geom.bleed ∧ f.y = -geom.bleed ∧ f.w = geom.pageW + 2 * geom.bleed ∧
          f.h = geom.pageH + 2 * geom.bleed := by
    intro b0 h hW hH hB
    obtain ⟨f, hf, hx, hy, hw, hh⟩ := h
    refine ⟨f, hfills ▸ hf, ?_, ?_, ?_, ?_⟩
    · rw [← hB]; exact hx
    · rw [← hB]; exact hy
    · rw [← hW, ← hB]; exact hw
    · rw [← hH, ← hB]; exact hh
  have bgStep_close : ∀ (c : Prop) [inst : Decidable c] (b0 X : B),
      BgStep b0 X → BgStep b0 (if c then X.finishPage X.closingOwed else X) := by
    intro c inst b0 X h
    split
    · exact h.trans (bgStep_finishPage _)
    · exact h
  refine fin _ (key _ _ (bgStep_close _ _ _
    (bgStep_placeFrom _ _ _ _ _ (Array.all_eq_true'.mp hepoch) (by simp))) ?_ rfl q hq)
    ?_ ?_ ?_
  all_goals first
    | (simp [Ir.Design.ofDoc, Ir.Design.ofPalette, Ir.Design.resolve, pdfView, hbg]
       done)
    | (try dsimp only
       repeat' split
       all_goals rfl)

public theorem page_background_survives
    (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store)
    (hbg : (Ir.Design.declared? doc.palette .page).isSome = true)
    (hepoch : pageGroundsDeclared geom fs pats doc imgs = true) :
    ∀ p ∈ (run geom fs pats doc imgs).pages,
      ∃ f ∈ p.fills.toList,
        f.x = -geom.bleed ∧ f.y = -geom.bleed ∧ f.w = geom.pageW + 2 * geom.bleed ∧
          f.h = geom.pageH + 2 * geom.bleed := by
  intro p hp
  change p ∈ (addMarks (runCore geom fs pats (resolveDocMath fs doc).1 imgs)
    (markFillsOf geom (resolveDocMath fs doc).1)).pages at hp
  obtain ⟨p0, hp0, hpf⟩ := addMarks_mem
    (runCore geom fs pats (resolveDocMath fs doc).1 imgs)
    (markFillsOf geom (resolveDocMath fs doc).1) p hp
  obtain ⟨f, hf, hx, hy, hw, hh⟩ := runCore_bg geom fs pats (resolveDocMath fs doc).1 imgs hbg hepoch p0 hp0
  have hf0 : f ∈ p0.fills := Array.mem_toList_iff.mp hf
  have hfp : f ∈ p.fills.toList := by
    rw [hpf, Array.mem_toList_iff]
    exact Array.mem_append.mpr (Or.inl hf0)
  exact ⟨f, hfp, hx, hy, hw, hh⟩

end LeanTex.Core.Layout


namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font


/-- The inputs that decide ordinary element glue, widths in scaled points. -/
public structure PendingView where
  owed : Array Glue
  wantDefault : Bool
  declaredSkip : Bool
  trivOwed : Bool

public def pending (a : Pending) : PendingView :=
  ⟨a.owed, a.wantDefault, a.declaredSkip, a.trivOwed⟩

/-- An ordinary boundary: no starred anchor and no short-display alternative. -/
public def Ordinary (a : Pending) : Prop := a.anchorAt = none ∧ a.dispAlt = none

public def peerGap (r : Context) : Glue := Spacing.Context.parskip r
public def texGap (r : Context) : Glue := Spacing.Context.resolve r r.geom.texParskip
public def merge (gs : Array Glue) (g : Glue) : Array Glue := addvOwed gs g
public def add (a : Pending) (g : Glue) : Pending := Spacing.Pending.addvspace a g

public theorem merge_exact (gs : Array Glue) (g : Glue) :
    merge gs g = match gs.back? with
      | none => #[g]
      | some last =>
        if last.width == 0 then gs.push g
        else if last.width < g.width then gs.pop.push g else gs := by
  unfold merge addvOwed
  cases gs.back? <;> rfl

public theorem add_pending_exact (a : Pending) (g : Glue) :
    pending (add a g) =
      { pending a with
        owed := merge (pending a).owed g
        declaredSkip := if (pending a).owed.back?.any (fun last => last.width == 0)
          then false else (pending a).declaredSkip } := by
  unfold add pending Spacing.Pending.addvspace merge addvOwed
  cases h : a.owed.back? with
  | none => simp [h]
  | some last =>
    by_cases h0 : last.width == 0
    · simp [h, h0]
    · by_cases hlt : last.width < g.width <;> simp [h, h0, hlt]

public theorem add_ordinary (a : Pending) (g : Glue) (h : Ordinary a) :
    Ordinary (add a g) := by
  unfold Ordinary add Spacing.Pending.addvspace
  rcases h with ⟨ha, hd⟩
  cases hl : a.owed.back? with
  | none => simp [hl, ha, hd]
  | some last =>
    by_cases h0 : last.width == 0
    · simp [hl, h0, ha, hd]
    · by_cases hlt : last.width < g.width <;> simp [hl, h0, hlt, ha, hd]

/-- The skip operations a flush newly emits, read back. -/
public def flushed (a : Pending) (r : Context) : Array Glue :=
  (((Spacing.Pending.flushGap a r).ops.toList.drop a.ops.size).filterMap fun op =>
    match op with
    | .skip g => some g
    | _ => none).toArray

/-- The collector emitted precisely these skips after its existing prefix. -/
public def Emits (a : Pending) (r : Context) (gs : Array Glue) : Prop :=
  (Spacing.Pending.flushGap a r).ops = a.ops ++ gs.map Op.skip

public theorem flush_emits_exact (a : Pending) (r : Context) (h : Ordinary a) :
    Emits a r (flushed a r) ∧
      flushed a r =
        if (pending a).owed.isEmpty then
          if (pending a).wantDefault then #[peerGap r] else #[]
        else if (pending a).wantDefault && (pending a).declaredSkip then
          #[if (pending a).trivOwed then texGap r else peerGap r,
            (pending a).owed.foldl Glue.add {}]
        else #[(pending a).owed.foldl Glue.add {}] := by
  rcases h with ⟨ha, hd⟩
  unfold Emits flushed pending peerGap texGap
  simp only [Spacing.Pending.flushGap, ha, Spacing.Pending.owedOp, hd, Spacing.Pending.gapGlue]
  split
  · split <;>
      simp [← Array.length_toList]
  · split <;>
      simp_all [← Array.length_toList, List.append_assoc]
    all_goals simp [Array.push_eq_append, -Array.append_singleton, Array.append_assoc]

/-- The measurements `placeLine` reads for one ordinary text line. -/
public structure LineInput where
  origin : Sp
  inkBelow : Sp
  floor : Sp
  skip : Glue
  shrink : Sp

public def input (r : Context) (b : Page) (size : Sp) (segs : Array Seg) : LineInput :=
  let box := lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs
  ⟨b.y + b.textGap box (segs.any Seg.isMath) (segsInk r.fs segs).1 + b.surfaceTop, box.inkBelow,
    Spacing.Page.bottom b - b.surfaceBottom, b.skip, b.pageShrink⟩

/-- Fixed prior layout: an existing non-rule line on the page,
with nothing pending that changes the next text line's spacing. -/
public def Ready (b : Page) (segs : Array Seg) : Prop :=
  b.cur.lines.isEmpty = false ∧ b.freshStart = false ∧
  b.prevBand = .text ∧ ruleOnly segs = false ∧ b.notesH = 0 ∧
  b.ignoreDepth = false ∧ b.texAfter = false ∧ b.opening = false

public def baselines (b : Page) : Array Sp := b.cur.lines.map (·.y)
public def shipped (b : Page) : Array PageOut := b.pages
public def queuedGlue (b : Page) : Glue := b.skip

/-- The placement steps for the skips `flushGap` emitted, then `placeLine`. -/
public def place (a : Pending) (r : Context) (b : Page) (x size : Sp)
    (segs : Array Seg) (width : Sp) : Page :=
  let st : StepSt := { b }
  let st := (flushed a r).foldl (fun st g => stepStaged r.fs r.imgs st (.skip g)) st
  st.b.placeLine r.fs x size segs width

private theorem skip_step (r : Context) (st : StepSt) (g : Glue)
    (h : st.b.fresh = false) :
    stepStaged r.fs r.imgs st (.skip g) =
      { st with b := { st.b with skip := st.b.skip.add g } } := by
  simp [stepStaged, h]

private theorem skip_steps (r : Context) (b : B) (gs : Array Glue)
    (h : b.fresh = false) :
    gs.foldl (fun st g => stepStaged r.fs r.imgs st (.skip g)) { b } =
      { b := { b with skip := gs.foldl Glue.add b.skip } : StepSt } := by
  have hh := Array.foldl_hom (fun glue => ({ b := { b with skip := glue } } : StepSt))
    (g₁ := Glue.add)
    (g₂ := fun st g => stepStaged r.fs r.imgs st (.skip g))
    (xs := gs) (init := b.skip) (by
      intro glue g
      rw [skip_step]
      simpa [Spacing.Page.fresh] using h)
  simpa using hh

private theorem line_placement (r : Context) (b : Page) (x size : Sp)
    (segs : Array Seg) (width : Sp) (h : Ready b segs)
    (hfit : b.y + b.skip.width +
      (b.textGap (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
        b.geom.leading size segs) (segs.any Seg.isMath) (segsInk r.fs segs).1) + b.surfaceTop +
      (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
        b.geom.leading size segs).inkBelow + b.surfaceBottom -
      Spacing.Page.bottom b ≤ b.pageShrink + b.skip.shrink) :
    shipped (Spacing.Page.placeLine r.fs b x size segs width) = shipped b ∧
    baselines (Spacing.Page.placeLine r.fs b x size segs width) =
      (baselines b).push (b.y + b.skip.width +
        (b.textGap (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
          b.geom.leading size segs) (segs.any Seg.isMath) (segsInk r.fs segs).1) + b.surfaceTop) := by
  rcases h with ⟨hcur, hfresh, hpr, hrl, hnn, hid, htx, hop⟩
  rcases hle : lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs with ⟨ht, bl, ia, dp⟩
  rw [hle] at hfit
  dsimp only at hfit ⊢
  unfold shipped baselines Spacing.Page.placeLine Spacing.Page.fitCommit Spacing.Page.fitWith
  rw [hle]
  dsimp only
  simp only [displayState_cur, keepInk_cur, displayState_pages, keepInk_pages]
  simp only [Spacing.Page.fresh, PageOut.blank, hcur, hfresh, Bool.false_and, hpr, hrl, hid, Spacing.Page.peerGap, hnn,
    noteFloor, htx, hop, Option.isSome_none, Array.isEmpty_empty, Bool.or_self,
    Bool.false_eq_true, ite_false, ite_true, Int.add_zero, beq_self_eq_true,
    Option.getD_none]
  simp only [hfit, true_or, ite_true, Spacing.Page.commit, Spacing.Page.attachNotes,
    Array.isEmpty_empty, ite_true]
  simp

public theorem place_exact (a : Pending) (r : Context) (b : Page) (x size : Sp)
    (segs : Array Seg) (width : Sp) (h : Ready b segs)
    (hfit : let i := input r b size segs
      let g := (flushed a r).foldl Glue.add i.skip
      i.origin + g.width + i.inkBelow - i.floor ≤ i.shrink + g.shrink) :
    let i := input r b size segs
    let g := (flushed a r).foldl Glue.add i.skip
    shipped (place a r b x size segs width) = shipped b ∧
      baselines (place a r b x size segs width) =
        (baselines b).push (i.origin + g.width) := by
  have hf : Spacing.Page.fresh b = false := by simp [Spacing.Page.fresh, PageOut.blank, h.1, h.2.1]
  let g := (flushed a r).foldl Glue.add b.skip
  have hr : Ready { b with skip := g } segs := h
  have hp := line_placement r { b with skip := g } x size segs width hr (by
    change b.y + g.width +
      (b.textGap (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
        b.geom.leading size segs) (segs.any Seg.isMath) (segsInk r.fs segs).1) + b.surfaceTop +
      (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
        b.geom.leading size segs).inkBelow + b.surfaceBottom -
      Spacing.Page.bottom b ≤ b.pageShrink + g.shrink
    unfold input at hfit
    dsimp only at hfit
    simpa only [g, Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg,
      Int.add_assoc, Int.add_comm, Int.add_left_comm] using hfit)
  dsimp only [place]
  rw [skip_steps r b _ hf]
  constructor
  · exact hp.1
  · rw [hp.2]
    simp only [baselines, input, g, Spacing.Page.surfaceTop,
      Spacing.Page.textGap, Spacing.Page.previousMath, Spacing.Page.boxDepth,
      Int.add_assoc, Int.add_comm, Int.add_left_comm]

end LeanTex.Core.Layout.Spacing

namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font

/-- The production placement input after backend projection,
math resolution, collection and paragraph breaking. -/
public structure Program where
  private mk ::
  private ops : Array Op
  private initial : B

/-- The preparation continuation's program for a document. -/
public def program (geom : Geom) (fs : FontSet) (doc : Ir.Doc) : Program :=
  withLayoutOps geom fs none (resolveDocMath fs doc).1 {}
    (fun ops initial _ => ⟨ops, initial⟩)

private def closeLast (b : B) : B :=
  if !b.cur.blank || b.pages.isEmpty then
    b.finishPage b.closingOwed
  else b

private theorem program_ship (geom : Geom) (fs : FontSet) (doc : Ir.Doc) :
    (ship geom fs none doc).pages =
      (closeLast (placeFrom fs {} (program geom fs doc).ops
        { b := (program geom fs doc).initial } 0).b).pages := by
  rfl

private theorem close_natural (b : B)
    (hcur : b.cur.lines.isEmpty = false)
    (hn : b.needed ≤ 0) (hv : b.vdist = .top)
    (hf : b.pageFils = 0) (hs : b.skip.fil = false)
    (hp : b.pendingNotes.isEmpty = true) :
    (closeLast b).pages.map (fun p => p.lines) =
      (b.pages.map (fun p => p.lines)).push b.cur.lines := by
  simp [closeLast, PageOut.blank, hcur, Spacing.Page.finishPage, Int.not_lt.mpr hn, hf, hs,
    hv, VDist.aboveShare, VDist.top, filShare, Spacing.Page.noteLines, hp]

private theorem closeLast_ships_exact (b : B) (hb : b.cur.blank = false) :
    (closeLast b).pages.size = b.pages.size + 1 ∧
      ((closeLast b).pages.back?.map (·.inks.size)) = some b.cur.inks.size := by
  constructor
  · simp [closeLast, hb, Spacing.Page.finishPage]
  · simp [closeLast, hb, Spacing.Page.finishPage]
    split <;> simp

end LeanTex.Core.Layout.Spacing

namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font

private structure LineRise (a b : LineOut) : Prop where
  segs : a.segs = b.segs
  size : a.size = b.size
  note : a.note = b.note
  furniture : a.furniture = b.furniture
  pictureLabel : a.pictureLabel = b.pictureLabel
  baseline : a.y ≤ b.y

private inductive LinesRise : List LineOut → List LineOut → Prop
  | nil : LinesRise [] []
  | cons {a b as bs} : LineRise a b → LinesRise as bs → LinesRise (a :: as) (b :: bs)

private theorem LinesRise.refl (ls : List LineOut) : LinesRise ls ls := by
  induction ls with
  | nil => exact .nil
  | cons l ls ih => exact .cons ⟨rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩ ih

private theorem LinesRise.append {as bs cs ds : List LineOut}
    (h : LinesRise as bs) (h' : LinesRise cs ds) :
    LinesRise (as ++ cs) (bs ++ ds) := by
  induction h with
  | nil => exact h'
  | cons hl _ ih => exact .cons hl ih

/-- The fields that determine ordinary paragraph geometry and its cursor. -/
private structure PageRise (a b : B) : Prop where
  geom : a.geom = b.geom
  ascent : a.ascent = b.ascent
  capHeight : a.capHeight = b.capHeight
  descent : a.descent = b.descent
  xHeight : a.xHeight = b.xHeight
  below : a.prevBelow = b.prevBelow
  depth : a.boxDepth = b.boxDepth
  math : a.previousMath = b.previousMath
  cursor : a.y + a.skip.width ≤ b.y + b.skip.width
  lines : LinesRise a.cur.lines.toList b.cur.lines.toList
  pages : a.pages = b.pages
  regions : a.openRegions = b.openRegions

private def nextBaseline (fs : FontSet) (b : B) (size : Sp)
    (segs : Array Seg) (first : Option Sp) (step : Option Sp := none) : Sp :=
  b.y + b.skip.width + first.getD
    (b.textGap (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
      b.geom.leading size segs step) (segs.any Seg.isMath) (segsInk fs segs).1) + b.surfaceTop

/-- Numeric fit at the next call to the placer. -/
private def LineFits (fs : FontSet) (b : B) (size : Sp)
    (segs : Array Seg) (first : Option Sp) (step : Option Sp := none) : Prop :=
  nextBaseline fs b size segs first step +
    (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
      b.geom.leading size segs step).inkBelow + b.surfaceBottom -
    b.bottom ≤ b.pageShrink + b.skip.shrink

private theorem ordinary_line (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (expand : Int) (counted : Bool)
    (leaf : Option Nat) (first : Option Sp) (opens : Bool) (anchors : Array String)
    (step : Option Sp) (strut : Option Sp)
    (h : Ready b segs) (hf : LineFits fs b size segs first step) :
    b.placeLine fs x size segs w hang expand #[] counted leaf first none opens anchors none
        step none strut =
      ((b.commit
        { x, y := nextBaseline fs b size segs first step, size
          segs := segs.filter fun s => match s with
            | .rule width _ _ _ => width != 0
            | _ => true
          setWidth := w, hang, expand, counted, leaf, anchors
          regionExtent := some (lineStrutInk strut (segsInk fs segs)) }
        (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
          b.geom.leading size segs step).inkBelow
        (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
          b.geom.leading size segs step).below
        false true
        (min (nextBaseline fs b size segs first step +
          (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
            b.geom.leading size segs step).inkBelow + b.surfaceBottom - b.bottom)
          (b.pageShrink + b.skip.shrink))).keepInk (lineStrutInk strut (segsInk fs segs)).2).displayState
        false (some (x + w - b.geom.hmargin)) := by
  rcases h with ⟨hc, hs, hp, hr, hn, hi, ht⟩
  unfold Spacing.Page.placeLine Spacing.Page.fitCommit Spacing.Page.fitWith
  dsimp only
  simp only [Spacing.Page.fresh, PageOut.blank, hc, hs, Bool.false_and, hp, hr, hi, Spacing.Page.peerGap, hn,
    noteFloor, ht, Option.isSome_none, Array.isEmpty_empty, Bool.or_self,
    Bool.false_eq_true, ite_false, ite_true, Int.add_zero, beq_self_eq_true]
  simp only [LineFits, nextBaseline] at hf
  simp only [hf, true_or, ite_true, Spacing.Page.attachNotes, Array.isEmpty_empty]
  rfl

private theorem line_rise (fs : FontSet) (a b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (expand : Int) (counted : Bool)
    (leaf : Option Nat) (first : Option Sp) (opens : Bool)
    (aa ab : Array String) (step : Option Sp) (strut : Option Sp) (h : PageRise a b)
    (ha : Ready a segs) (hb : Ready b segs)
    (hfa : LineFits fs a size segs first step) (hfb : LineFits fs b size segs first step) :
    PageRise (a.placeLine fs x size segs w hang expand #[] counted leaf first none opens aa none
        step none strut)
      (b.placeLine fs x size segs w hang expand #[] counted leaf first none opens ab none
        step none strut) := by
  have hy : nextBaseline fs a size segs first step ≤ nextBaseline fs b size segs first step := by
    simp only [nextBaseline, Spacing.Page.surfaceTop, h.regions, h.geom, h.ascent,
      h.capHeight, h.descent, Spacing.Page.textGap, h.below, h.depth, h.math]
    exact Int.add_le_add_right (Int.add_le_add_right h.cursor _) _
  rw [ordinary_line fs a x size segs w hang expand counted leaf first opens aa step strut ha hfa,
      ordinary_line fs b x size segs w hang expand counted leaf first opens ab step strut hb hfb]
  constructor
  · exact h.geom
  · exact h.ascent
  · exact h.capHeight
  · exact h.descent
  · exact h.xHeight
  · simp only [Spacing.Page.displayState, Spacing.Page.keepInk, Spacing.Page.commit, h.geom, h.ascent, h.capHeight, h.descent]
  · simp only [displayState_boxDepth, keepInk_boxDepth_exact]
  · simp only [Spacing.Page.previousMath, displayState_cur, keepInk_cur,
      Spacing.Page.commit, Array.back?_push, Option.any_some]
  · simpa only [Spacing.Page.displayState, Spacing.Page.keepInk, Spacing.Page.commit, Int.add_zero] using hy
  · simp only [Spacing.Page.displayState, Spacing.Page.keepInk, Spacing.Page.commit, Array.toList_push]
    exact h.lines.append (.cons ⟨rfl, rfl, rfl, rfl, rfl, hy⟩ .nil)
  · exact h.pages
  · simp only [Spacing.Page.displayState, Spacing.Page.keepInk, Spacing.Page.commit,
      h.regions]

/-- A line the rise certificate covers: an ordinary line spaced by the metric rule. -/
private def ParaFits (fs : FontSet) (j : ParaJob) (s : B × Nat × Bool) (brk : Nat) : Prop :=
  let g := paraLineGeom fs j s.1 s.2.2 s.2.1 brk
  (j.paintPadding = none ∧ j.texBox = none) ∧ j.rowStrut = none ∧
    Ready s.1 g.1 ∧ LineFits fs s.1 j.size g.1 (if s.2.2 then j.firstBaseline else none) j.lead

private theorem reachDepth_rise (j : ParaJob) (brk : Nat) (a b : B) (h : PageRise a b) :
    PageRise (reachDepth j brk a) (reachDepth j brk b) := by
  unfold reachDepth
  split
  · split
    · exact { h with depth := by rw [keepInk_boxDepth_exact, keepInk_boxDepth_exact, h.depth] }
    · exact h
  · exact h

private theorem trailer_rise (fs : FontSet) (j : ParaJob) (brk : Nat)
    (segs : Array Seg) (a b : B) (h : PageRise a b) :
    PageRise (placeParaTrailer fs j brk segs a) (placeParaTrailer fs j brk segs b) := by
  have h' := reachDepth_rise j brk a b h
  unfold placeParaTrailer
  dsimp only
  split
  · refine { h' with cursor := ?_ }
    dsimp only
    simpa only [Int.add_assoc] using Int.add_le_add_right h'.cursor _
  · exact { h' with }

private theorem paragraph_step (fs : FontSet) (j : ParaJob)
    (a b : B) (prev brk : Nat) (first : Bool)
    (hj : j.display = none) (hn : j.notes.isEmpty = true)
    (h : PageRise a b)
    (ha : ParaFits fs j (a, prev, first) brk)
    (hb : ParaFits fs j (b, prev, first) brk) :
    PageRise (placeParaLine fs j (a, prev, first) brk).1
      (placeParaLine fs j (b, prev, first) brk).1 := by
  have hg : paraLineGeom fs j a first prev brk = paraLineGeom fs j b first prev brk := by
    simp only [paraLineGeom, h.geom, h.xHeight]
  unfold ParaFits at ha hb
  simp only [hg] at ha
  have hp := ha.1
  have hr := ha.2.1
  have ha := ha.2.2
  have hb := hb.2.2
  unfold placeParaLine
  dsimp only
  simp only [hg, hn, ite_true, Spacing.Page.openDisplayAt, hj, hp.1, hp.2, hr, ite_self]
  apply trailer_rise
  split
  · exact line_rise fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      { h with } ha.1 hb.1 ha.2 hb.2
  · exact line_rise fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      { h with } ha.1 hb.1 ha.2 hb.2

/-- A trace of the numeric input conditions at every iteration of the paragraph fold. -/
private inductive ParagraphInputs (fs : FontSet) (j : ParaJob) :
    List Nat → (B × Nat × Bool) → Prop
  | nil (s) : ParagraphInputs fs j [] s
  | cons {brk rest s} : ParaFits fs j s brk →
      ParagraphInputs fs j rest (placeParaLine fs j s brk) →
      ParagraphInputs fs j (brk :: rest) s

private theorem paragraph_fold (fs : FontSet) (j : ParaJob)
    (hj : j.display = none) (hn : j.notes.isEmpty = true)
    (breaks : List Nat) (a b : B × Nat × Bool)
    (h : PageRise a.1 b.1) (hm : a.2 = b.2)
    (ha : ParagraphInputs fs j breaks a) (hb : ParagraphInputs fs j breaks b) :
    PageRise (breaks.foldl (placeParaLine fs j) a).1
      (breaks.foldl (placeParaLine fs j) b).1 := by
  induction ha generalizing b with
  | nil => exact h
  | @cons brk rest a ha hrest ih =>
    cases hb with
    | cons hb hrest' =>
      rcases a with ⟨a, prev, first⟩
      rcases b with ⟨b, prev', first'⟩
      cases hm
      exact ih _ (paragraph_step fs j a b prev brk first hj hn h ha hb) rfl hrest'

private def paragraphStart (b : B) (j : ParaJob) (breaks : Array Nat) : B × Nat × Bool :=
  let p := paragraphRecord b j breaks
  let start := ({ b with diags := b.diags ++ j.diags }).warnReflow p (!p.reflows.isEmpty)
  ({ start with paragraphBreaks := b.paragraphBreaks.push p }, 0, true)

private theorem paragraph_rise (fs : FontSet) (j : ParaJob) (breaks : Array Nat)
    (a b : B) (hj : j.display = none) (hn : j.notes.isEmpty = true) (h : PageRise a b)
    (ha : ParagraphInputs fs (placedJob fs a j breaks) breaks.toList (paragraphStart a j breaks))
    (hb : ParagraphInputs fs (placedJob fs b j breaks) breaks.toList (paragraphStart b j breaks)) :
    PageRise (placePara fs a j breaks) (placePara fs b j breaks) := by
  have hs : PageRise (paragraphStart a j breaks).1 (paragraphStart b j breaks).1 := by
    dsimp only [paragraphStart]
    unfold Spacing.Page.warnReflow
    repeat' split
    all_goals exact { h with }
  have hw : placedJob fs a j breaks = placedJob fs b j breaks := by
    simp only [placedJob, paraLineGeom, h.geom, h.xHeight]
  rw [hw] at ha
  have hp := paragraph_fold fs (placedJob fs b j breaks) hj hn breaks.toList _ _ hs rfl ha hb
  simpa only [placePara, paragraphStart, Array.foldl_toList, hw] using hp

end LeanTex.Core.Layout.Spacing

namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font

private theorem appendRiders_toList (fs : FontSet) (l : LineOut)
    (lines : Array LineOut) :
    (appendRiders fs l lines).toList =
      lines.toList ++ (decorationRiders fs l).toList := by
  unfold appendRiders
  simp only [Array.forIn_pure_yield_eq_foldl]
  simp [← Array.foldl_toList]

private theorem appendMarks_toList (l : LineOut) (lines : Array LineOut) :
    (appendMarks l lines).toList = lines.toList ++ (markRiders l).toList := by
  unfold appendMarks
  simp only [Array.forIn_pure_yield_eq_foldl]
  simp [← Array.foldl_toList]

private theorem paintLines_toList (fs : FontSet) (lines : Array LineOut) :
    (paintLines fs lines).toList =
      lines.toList.flatMap
        (fun l => (markRiders l).toList ++ l :: (decorationRiders fs l).toList) := by
  unfold paintLines
  simp only [Array.forIn_pure_yield_eq_foldl]
  have h := Array.foldl_induction
    (as := lines)
    (motive := fun i (out : Array LineOut) =>
      out.toList = (lines.toList.take i).flatMap
        (fun l => (markRiders l).toList ++ l :: (decorationRiders fs l).toList))
    (init := Array.mkEmpty lines.size)
    (f := fun out l => appendRiders fs l ((appendMarks l out).push l))
    (by simp)
    (by
      intro i out hout
      rw [appendRiders_toList, Array.toList_push, appendMarks_toList, hout]
      rw [List.take_succ_eq_append_getElem (by simp)]
      simp [List.flatMap_append, List.append_assoc])
  simpa [← Array.length_toList] using h

private theorem marks_rise {a b : LineOut} (h : LineRise a b) :
    LinesRise (markRiders a).toList (markRiders b).toList := by
  simp only [markRiders, Array.toList_filterMap,
    List.filterMap_cons, List.filterMap_nil, h.segs, h.size, h.pictureLabel]
  by_cases hp : b.pictureLabel.isSome = true
  · simp only [hp, ite_true, Array.isEmpty_empty]
    exact .nil
  · by_cases hm : (markSegs b.segs).isEmpty = true
    all_goals simp only [hp, hm, ite_true, Bool.false_eq_true, ite_false]
    · exact .nil
    · exact .cons ⟨rfl, rfl, h.note, h.furniture, rfl, h.baseline⟩ .nil

private theorem riders_rise (fs : FontSet) {a b : LineOut} (h : LineRise a b) :
    LinesRise (decorationRiders fs a).toList (decorationRiders fs b).toList := by
  simp only [decorationRiders, Array.toList_filterMap,
    List.filterMap_cons, List.filterMap_nil, h.segs, h.size]
  by_cases hu : (underlineSegs fs b.size b.segs).isEmpty = true <;>
    by_cases ht : (lineThroughSegs b.segs).isEmpty = true
  all_goals simp only [hu, ht, ite_true]
  · exact .nil
  · exact .cons ⟨rfl, rfl, h.note, h.furniture, rfl, h.baseline⟩ .nil
  · exact .cons ⟨rfl, rfl, h.note, h.furniture, rfl, h.baseline⟩ .nil
  · exact .cons ⟨rfl, rfl, h.note, h.furniture, rfl, h.baseline⟩
      (.cons ⟨rfl, rfl, h.note, h.furniture, rfl, h.baseline⟩ .nil)

private theorem paint_rise (fs : FontSet) {as bs : List LineOut}
    (h : LinesRise as bs) :
    LinesRise (as.flatMap fun l => (markRiders l).toList ++ l :: (decorationRiders fs l).toList)
      (bs.flatMap fun l => (markRiders l).toList ++ l :: (decorationRiders fs l).toList) := by
  induction h with
  | nil => exact .nil
  | cons hl _ ih =>
    exact ((marks_rise hl).append (LinesRise.cons hl (riders_rise fs hl))).append ih

/-- A segment's text glyphs, white space, NBSP and soft hyphens excluded. -/
public def textInk : Seg → List Char
  | .run _ _ _ _ glyphs _ _ _ _ _ _ =>
    (String.ofList (glyphs.toList.map (·.2.1))).toList.filter fun c =>
      !(c.isWhitespace || c == ' ' || c == '\u00a0' || c == '\u00ad')
  | .gap _ _ | .decoratedGap _ _ _ | .rule _ _ _ _ | .decoration _ _ _ _ _
    | .image _ _ _ _ | .poly _ _ => []

public def inkLine (l : LineOut) : Bool :=
  !l.furniture && !l.note && l.segs.toList.flatMap textInk != []

public def inkBaselines (o : Out) : List Sp :=
  (o.pages.toList.flatMap fun p => p.lines.toList.filter inkLine).map (·.y)

private theorem inkLine_rise {a b : LineOut} (h : LineRise a b) :
    inkLine a = inkLine b := by
  simp only [inkLine, h.segs, h.note, h.furniture]

private theorem LinesRise.filter {as bs : List LineOut} (h : LinesRise as bs) :
    LinesRise (as.filter inkLine) (bs.filter inkLine) := by
  induction h with
  | nil => exact .nil
  | cons hl _ ih =>
    simp only [List.filter_cons, inkLine_rise hl]
    split
    · exact .cons hl ih
    · exact ih

private theorem LinesRise.last {as bs : List LineOut} (h : LinesRise as bs) :
    ((as.map (·.y)).getLast?.getD 0 : Int) ≤ (bs.map (·.y)).getLast?.getD 0 := by
  induction h with
  | nil => exact Int.le_refl _
  | @cons a b as bs hl ht ih =>
    cases ht with
    | nil => simpa using hl.baseline
    | cons _ _ => simpa using ih

private theorem furniture_ink_empty (fs : FontSet) (lines : Array LineOut) :
    (paintLines fs (lines.map furnitureLine)).toList.filter inkLine = [] := by
  rw [paintLines_toList]
  simp only [Array.toList_map, List.flatMap_map,
    List.filter_flatMap]
  apply List.flatMap_eq_nil_iff.mpr
  intro l hl
  simp only [List.filter_append, List.filter_cons, inkLine, furnitureLine, Bool.not_true,
    Bool.false_and, Bool.false_eq_true, reduceIte, List.append_eq_nil_iff]
  constructor
  · apply List.filter_eq_nil_iff.mpr
    intro r hr
    have hb := markRiders_band (furnitureLine l) r
      (by simpa only [furnitureLine, Array.mem_toList_iff] using hr)
    simp [inkLine, hb.1, furnitureLine]
  · apply List.filter_eq_nil_iff.mpr
    intro r hr
    have hb := decorationRiders_band fs (furnitureLine l) r
      (by simpa only [furnitureLine, Array.mem_toList_iff] using hr)
    simp [inkLine, hb.1, furnitureLine]

private theorem furnishLines_ink_projects (fs : FontSet)
    (before body after : Array LineOut) :
    (furnishLines fs before body after).toList.filter inkLine =
      (paintLines fs body).toList.filter inkLine := by
  unfold furnishLines
  simp only [paintLines_toList, Array.toList_append, List.flatMap_append,
    List.filter_append]
  have hb := furniture_ink_empty fs before
  have ha := furniture_ink_empty fs after
  rw [paintLines_toList] at hb ha
  rw [hb, ha]
  simp

private theorem furnishFrom_transforms {σ α : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (read transform : PageOut → α)
    (hread : ∀ i p s, read { p with lines := (f i p s).1 } = transform p)
    (pages : Array PageOut) (s : σ) (i : Nat) :
    (furnishFrom f pages s i).1.map read =
      pages.mapIdx (fun j p => if j < i then read p else transform p) := by
  induction pages, s, i using furnishFrom.induct f with
  | case1 pages s i h ls s' heq ih =>
    have hr := hread i pages[i] s
    rw [heq] at hr
    rw [furnishFrom]
    simp only [h, reduceDIte, heq]
    rw [ih]
    apply Array.ext
    · simp
    · intro j hj hj'
      simp only [Array.getElem_mapIdx, Array.getElem_set]
      by_cases hji : j = i
      · subst j
        simpa using hr
      · have hn : (j < i + 1) = (j < i) := propext (by omega)
        simp [Ne.symm hji, hn]
  | case2 pages s i h =>
    rw [furnishFrom]
    simp only [h, reduceDIte]
    apply Array.ext
    · simp
    · intro j hj hj'
      have hi : j < i := by simp only [Array.size_map] at hj; omega
      simp [hi]

private theorem furnishFrom_transforms_zero {σ α : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (read transform : PageOut → α)
    (hread : ∀ i p s, read { p with lines := (f i p s).1 } = transform p)
    (pages : Array PageOut) (s : σ) :
    (furnishFrom f pages s 0).1.map read = pages.map transform := by
  rw [furnishFrom_transforms f read transform hread]
  apply Array.ext
  · simp
  · intro j hj hj'
    simp

private theorem runPost_ink_projects (sh : Shipped) :
    (runPost sh).pages.map (fun p => p.lines.toList.filter inkLine) =
      sh.pages.map (fun p => (paintLines sh.fs p.lines).toList.filter inkLine) := by
  unfold runPost
  dsimp only [Id.run, bind, pure, Id]
  apply furnishFrom_transforms_zero
  intro i p s
  exact furnishLines_ink_projects _ _ _ _

end LeanTex.Core.Layout.Spacing

namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font


/-- A trace of the driver's prefix, one constructor per production call. -/
private inductive Prefix (fs : FontSet) (p : Program) : FlowSt → Nat → Prop
  | start : Prefix fs p { placed := { b := p.initial } } 0
  | step {st i} (prior : Prefix fs p st i) (hi : i < p.ops.size)
      (ordinary : p.ops[i] ≠ .floatOpen) :
      Prefix fs p
        (stepFlow fs {} st (keepAt st.placed.b fs {} p.ops i p.ops[i])) (i + 1)

private theorem prefix_continue (fs : FontSet) (p : Program)
    {st : FlowSt} {i : Nat} (h : Prefix fs p st i) :
    placeFlowFrom fs {} p.ops { placed := { b := p.initial } } 0 =
      placeFlowFrom fs {} p.ops st i := by
  induction h with
  | start => rfl
  | @step st i _ hi hn ih =>
    rw [ih, placeFlowFrom]
    simp only [hi, reduceDIte]

/-- The unconsumed input: exactly the emitted ordinary skips and one prepared paragraph. -/
private inductive ParagraphTail (ops : Array Op) (j : ParaJob)
    (t : Task (Array Nat)) : Nat → List Glue → Prop
  | last {i} (hi : i < ops.size) (hop : ops[i] = .para j t)
      (done : ops.size = i + 1) : ParagraphTail ops j t i []
  | skip {i g gs} (hi : i < ops.size) (hop : ops[i] = .skip g)
      (rest : ParagraphTail ops j t (i + 1) gs) :
      ParagraphTail ops j t i (g :: gs)

private theorem skip_step_fs (fs : FontSet) (st : StepSt) (g : Glue)
    (h : st.b.fresh = false) :
    stepStaged fs {} st (.skip g) =
      { st with b := { st.b with skip := st.b.skip.add g } } := by
  simp [stepStaged, h]

private theorem para_step_b (fs : FontSet) (st : FlowSt) (j : ParaJob)
    (t : Task (Array Nat)) (hk : j.keepNext ≤ 0) :
    (stepFlow fs {} st (.para j t)).placed.b = placePara fs st.placed.b j t.get := by
  simp only [stepFlow, stepStaged]
  have hn : ¬ (0 : Int) < j.keepNext := Int.not_lt.mpr hk
  simp only [Spacing.Page.keepHeading, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
  split <;> rfl

private theorem paragraph_tail_place (fs : FontSet) (ops : Array Op)
    (j : ParaJob) (t : Task (Array Nat)) {i : Nat} {gs : List Glue}
    (h : ParagraphTail ops j t i gs) (hk : j.keepNext ≤ 0)
    (st : FlowSt) (hf : st.placed.b.fresh = false) :
    (placeFlowFrom fs {} ops st i).placed.b =
      placePara fs { st.placed.b with skip := gs.foldl Glue.add st.placed.b.skip } j t.get := by
  induction h generalizing st with
  | @last i hi hop hend =>
    rw [placeFlowFrom]
    simp only [hi, reduceDIte, hop, keepAt, Int.not_lt.mpr hk, ite_false]
    rw [placeFlowFrom]
    simp only [hend, Nat.lt_irrefl, reduceDIte]
    simpa using para_step_b fs st j t hk
  | @skip i g gs hi hop _ ih =>
    rw [placeFlowFrom]
    simp only [hi, reduceDIte, hop, keepAt]
    rw [ih]
    · simp only [stepFlow, skip_step_fs fs st.placed g hf, List.foldl_cons]
    · simp only [stepFlow, skip_step_fs fs st.placed g hf]
      simpa only [Spacing.Page.fresh] using hf

/-- A document's prepared input reaches a fixed prior
layout, then holds the named skips and paragraph. -/
public def AtTail (geom : Geom) (fs : FontSet) (doc : Ir.Doc)
    (b : Page) (j : Paragraph) (breaks : Array Nat) (gs : Array Glue) : Prop :=
  let p := program geom fs doc
  ∃ (st : FlowSt) (i : Nat) (t : Task (Array Nat)),
    Prefix fs p st i ∧ st.placed.b = b ∧ t.get = breaks ∧
      ParagraphTail p.ops j t i gs.toList

private theorem tail_ship (geom : Geom) (fs : FontSet) (doc : Ir.Doc)
    (b : Page) (j : Paragraph) (breaks : Array Nat) (gs : Array Glue)
    (h : AtTail geom fs doc b j breaks gs) (hk : j.keepNext ≤ 0)
    (hf : Spacing.Page.fresh b = false) :
    (ship geom fs none doc).pages =
      (closeLast (placePara fs { b with skip := gs.foldl Glue.add b.skip } j breaks)).pages := by
  obtain ⟨st, i, t, hp, hs, ht, htail⟩ := h
  rw [program_ship]
  unfold placeFrom
  rw [prefix_continue fs (program geom fs doc) hp]
  rw [paragraph_tail_place fs _ j t htail hk st (hs.symm ▸ hf), hs, ht]
  simp only [Array.foldl_toList]

end LeanTex.Core.Layout.Spacing

namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font

/-- Inputs to the page-closing door that keep every
baseline: natural fit, top distribution and no fil. -/
private def NaturalClose (b : B) : Prop :=
  b.cur.lines.isEmpty = false ∧ b.needed ≤ 0 ∧ b.vdist = .top ∧
    b.pageFils = 0 ∧ b.skip.fil = false ∧ b.pendingNotes.isEmpty = true

private def boundaryStart (b : B) (gs : Array Glue) : B :=
  { b with skip := gs.foldl Glue.add b.skip }

private def boundaryEnd (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) (gs : Array Glue) : B :=
  placePara fs (boundaryStart b gs) j breaks

/-- Checkable inputs to the production calls after the fixed prefix:
ordinary modes, numeric fit at every commit, natural close. -/
public def ParagraphSafe (fs : FontSet) (b : Page) (j : Paragraph)
    (breaks : Array Nat) (gs : Array Glue) : Prop :=
  Spacing.Page.fresh b = false ∧ j.keepNext ≤ 0 ∧ j.display = none ∧ j.notes.isEmpty = true ∧
    ParagraphInputs fs (placedJob fs (boundaryStart b gs) j breaks) breaks.toList
      (paragraphStart (boundaryStart b gs) j breaks) ∧
    NaturalClose (boundaryEnd fs b j breaks gs)

private def paintedInk (fs : FontSet) (ls : Array LineOut) : List LineOut :=
  (paintLines fs ls).toList.filter inkLine

private theorem run_ink_projects (geom : Geom) (fs : FontSet) (doc : Ir.Doc) :
    (run geom fs none doc).pages.map (fun p => p.lines.toList.filter inkLine) =
      (ship geom fs none doc).pages.map (fun p => paintedInk fs p.lines) := by
  have hf : (shipCore geom fs none (resolveDocMath fs doc).1 {}).fs = fs := by rfl
  simpa only [run, runCore, ship, addMarks, auditLabelInk, Array.map_map, Function.comp_def,
    paintedInk, hf] using
    runPost_ink_projects (shipCore geom fs none (resolveDocMath fs doc).1 {})

private theorem tail_baselines (geom : Geom) (fs : FontSet) (doc : Ir.Doc)
    (b : Page) (j : Paragraph) (breaks : Array Nat) (gs : Array Glue)
    (ha : AtTail geom fs doc b j breaks gs)
    (hs : ParagraphSafe fs b j breaks gs) :
    inkBaselines (run geom fs none doc) =
      ((boundaryEnd fs b j breaks gs).pages.toList.flatMap
        (fun p => paintedInk fs p.lines) ++
          paintedInk fs (boundaryEnd fs b j breaks gs).cur.lines).map (·.y) := by
  have hr := run_ink_projects geom fs doc
  rw [tail_ship geom fs doc b j breaks gs ha hs.2.1 hs.1] at hr
  rcases hs.2.2.2.2.2 with ⟨hc, hn, hv, hf, hg, hp⟩
  have hclose := close_natural (boundaryEnd fs b j breaks gs) hc hn hv hf hg hp
  have hm := congrArg (fun xs : Array (Array LineOut) =>
    (xs.toList.flatMap (paintedInk fs)).map (·.y)) hclose
  have ho := congrArg (fun xs : Array (List LineOut) =>
    xs.toList.flatten.map (·.y)) hr
  simp only [Array.toList_map, ← List.flatMap_def] at ho
  simp only [Array.toList_map, List.flatMap_map, Array.toList_push,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hm
  exact ho.trans hm

public theorem run_tail_monotone (geom : Geom) (fs : FontSet) (before after : Ir.Doc)
    (b : Page) (j : Paragraph) (breaks : Array Nat) (gs gs' : Array Glue)
    (ha : AtTail geom fs before b j breaks gs)
    (ha' : AtTail geom fs after b j breaks gs')
    (hs : ParagraphSafe fs b j breaks gs)
    (hs' : ParagraphSafe fs b j breaks gs')
    (hw : (gs.foldl Glue.add (queuedGlue b)).width ≤
      (gs'.foldl Glue.add (queuedGlue b)).width) :
    ((inkBaselines (run geom fs none before)).getLast?.getD 0 : Int) ≤
      (inkBaselines (run geom fs none after)).getLast?.getD 0 := by
  have hb : PageRise (boundaryStart b gs) (boundaryStart b gs') :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.add_le_add_left hw _,
      LinesRise.refl _, rfl, rfl⟩
  have hp := paragraph_rise fs j breaks _ _ hs.2.2.1 hs.2.2.2.1 hb
    hs.2.2.2.2.1 hs'.2.2.2.2.1
  change PageRise (boundaryEnd fs b j breaks gs) (boundaryEnd fs b j breaks gs') at hp
  rw [tail_baselines geom fs before b j breaks gs ha hs,
    tail_baselines geom fs after b j breaks gs' ha' hs']
  apply LinesRise.last
  rw [hp.pages]
  apply (LinesRise.refl _).append
  have hl := (paint_rise fs hp.lines).filter
  simpa only [paintedInk, paintLines_toList] using hl

end LeanTex.Core.Layout.Spacing

namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font

-- Exact equality keeps colour spellings and provenance, which the BEq instances omit.
deriving instance DecidableEq for Ir.PdfColor, Ir.Color
deriving instance DecidableEq for Diag
deriving instance DecidableEq for Geom, Attribution, DecorationRule, Decorations,
  MathLineMetrics, RunMetrics
deriving instance DecidableEq for Item, Seg, LineOut, HeadingRule
deriving instance DecidableEq for NoteBlock, DisplayJob

private def bucketEq :
    DecidableEq (Std.DHashMap.Internal.AssocList Nat (fun _ => Sp))
  | .nil, .nil => isTrue rfl
  | .nil, .cons _ _ _ => isFalse (by intro h; cases h)
  | .cons _ _ _, .nil => isFalse (by intro h; cases h)
  | .cons a b t, .cons a' b' t' =>
    letI := bucketEq t t'
    decidable_of_iff (a = a' ∧ b = b' ∧ t = t') (by simp)

-- Representation equality, stronger than map equivalence, so certificates substitute exactly.
private instance : DecidableEq (Std.HashMap Nat Sp) := fun a b =>
  letI := bucketEq
  decidable_of_iff
    (a.inner.inner.size = b.inner.inner.size ∧
      a.inner.inner.buckets = b.inner.inner.buckets) (by
    cases a with | mk a =>
      cases b with | mk b =>
        cases a with | mk a aw =>
          cases b with | mk b bw =>
            cases a
            cases b
            simp)

deriving instance DecidableEq for Paragraph

/-- Inputs to the initial page builder; every other field
starts at its default (`program_initial_exact`). -/
private structure InitialInput where
  geom : Geom
  ascent : Sp
  descent : Sp
  capHeight : Sp
  xHeight : Sp
  docBg : Option Ir.Color
  footins : Sp
  noteInk : Ir.Color
  footGap : Sp
  diags : Array Diag
  deriving DecidableEq

private def initialInput (b : B) : InitialInput :=
  ⟨b.geom, b.ascent, b.descent, b.capHeight, b.xHeight,
    b.docBg, b.footins, b.noteInk, b.footGap, b.diags⟩

private def InitialInput.page (a : InitialInput) : B := {
  geom := a.geom, ascent := a.ascent, descent := a.descent
  capHeight := a.capHeight, xHeight := a.xHeight, docBg := a.docBg
  footins := a.footins, noteInk := a.noteInk, footGap := a.footGap, diags := a.diags }

private theorem program_initial_exact (geom : Geom) (fs : FontSet) (doc : Ir.Doc) :
    (initialInput (program geom fs doc).initial).page =
      (program geom fs doc).initial := by
  rfl

/-- Shared inputs read before paragraph placement, whose equality yields equal prefix pages. -/
private structure TailInput where
  initial : InitialInput
  first : ParaJob
  firstBreaks : Array Nat
  last : ParaJob
  lastBreaks : Array Nat
  deriving DecidableEq

private def TailInput.page (a : TailInput) (fs : FontSet) : B :=
  placePara fs a.initial.page a.first a.firstBreaks

private structure PreparedTail (geom : Geom) (fs : FontSet) (doc : Ir.Doc) where
  input : TailInput
  skips : Array Glue
  reaches : AtTail geom fs doc (input.page fs) input.last input.lastBreaks skips

private def preparedTail? (geom : Geom) (fs : FontSet) (doc : Ir.Doc) :
    Option (PreparedTail geom fs doc) := by
  let p := program geom fs doc
  match hops : p.ops.toList with
  | [.para first firstTask, .skip g, .para last lastTask] =>
    if hk : first.keepNext ≤ 0 then
      have heq : p.ops = #[.para first firstTask, .skip g, .para last lastTask] :=
        Array.toList_inj.mp hops
      have hi : 0 < p.ops.size := by simp [heq]
      have hn : p.ops[0] ≠ .floatOpen := by simp [heq]
      have hkeep : keepAt p.initial fs {} p.ops 0 p.ops[0] =
          .para first firstTask := by
        simp [heq, keepAt, Int.not_lt.mpr hk]
      let st := stepFlow fs {} { placed := { b := p.initial } }
        (keepAt p.initial fs {} p.ops 0 p.ops[0])
      let input : TailInput :=
        ⟨initialInput p.initial, first, firstTask.get, last, lastTask.get⟩
      refine some ⟨input, #[g], ?_⟩
      change ∃ (s : FlowSt) (i : Nat) (t : Task (Array Nat)),
        Prefix fs p s i ∧ s.placed.b = input.page fs ∧ t.get = lastTask.get ∧
          ParagraphTail p.ops last t i [g]
      refine ⟨st, 1, lastTask, Prefix.step Prefix.start hi hn, ?_, rfl, ?_⟩
      · dsimp only [st]
        rw [hkeep, para_step_b fs _ first firstTask hk]
        exact congrArg (fun b => placePara fs b first firstTask.get)
          (program_initial_exact geom fs doc).symm
      · exact ParagraphTail.skip (by simp [heq]) (by simp [heq])
          (ParagraphTail.last (by simp [heq]) (by simp [heq]) (by simp [heq]))
    else exact none
  | _ => exact none

private def paragraphInputsDecidable (fs : FontSet) (j : ParaJob) :
    (breaks : List Nat) → (s : B × Nat × Bool) →
      Decidable (ParagraphInputs fs j breaks s)
  | [], s => isTrue (.nil s)
  | brk :: rest, s =>
    let fits : Decidable (ParaFits fs j s brk) := by
      unfold ParaFits Ready LineFits
      infer_instance
    match fits with
    | isFalse hn => isFalse fun h => by cases h with | cons hf _ => exact hn hf
    | isTrue hf =>
      match paragraphInputsDecidable fs j rest (placeParaLine fs j s brk) with
      | isTrue hr => isTrue (.cons hf hr)
      | isFalse hn => isFalse fun h => by cases h with | cons _ hr => exact hn hr

/-- Decide `ParagraphSafe` with the real paragraph step at each break. -/
public def paragraphSafeDecision (fs : FontSet) (b : Page) (j : Paragraph)
    (breaks : Array Nat) (gs : Array Glue) :
    Decidable (ParagraphSafe fs b j breaks gs) := by
  letI : Decidable (j.display = none) :=
    match j.display with
    | none => isTrue rfl
    | some _ => isFalse fun h => by contradiction
  letI := paragraphInputsDecidable fs (placedJob fs (boundaryStart b gs) j breaks)
    breaks.toList (paragraphStart (boundaryStart b gs) j breaks)
  let last := boundaryEnd fs b j breaks gs
  letI : Decidable (last.vdist = .top) :=
    decidable_of_iff (last.vdist.above = 0 ∧ last.vdist.below = 1000 ∧
        last.vdist.joins = false) (by
      rcases last.vdist with ⟨above, below, joins⟩
      simp [VDist.top])
  change Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ NaturalClose last)
  unfold NaturalClose
  infer_instance

/-- Delegates to `paragraphSafeDecision`, keeping the representations private. -/
public instance paragraphSafeDecidable (fs : FontSet) (b : Page) (j : Paragraph)
    (breaks : Array Nat) (gs : Array Glue) :
    Decidable (ParagraphSafe fs b j breaks gs) :=
  paragraphSafeDecision fs b j breaks gs

/-- A certificate for the common prefix and safe final paragraph of two documents. -/
public structure TailPair (geom : Geom) (fs : FontSet) (before after : Ir.Doc) where
  page : Page
  paragraph : Paragraph
  breaks : Array Nat
  beforeSkips : Array Glue
  afterSkips : Array Glue
  before_reaches : AtTail geom fs before page paragraph breaks beforeSkips
  after_reaches : AtTail geom fs after page paragraph breaks afterSkips
  before_safe : ParagraphSafe fs page paragraph breaks beforeSkips
  after_safe : ParagraphSafe fs page paragraph breaks afterSkips

/-- Certify two documents whose prepared input is two paragraphs with one
skip between; `none` where they differ otherwise or a fit bound fails. -/
public def twoParagraphPair? (geom : Geom) (fs : FontSet) (before after : Ir.Doc) :
    Option (TailPair geom fs before after) := do
  let a ← preparedTail? geom fs before
  let b ← preparedTail? geom fs after
  if h : a.input = b.input then
    if ha : ParagraphSafe fs (a.input.page fs) a.input.last a.input.lastBreaks a.skips then
      if hb : ParagraphSafe fs (a.input.page fs) a.input.last a.input.lastBreaks b.skips then
        some ⟨a.input.page fs, a.input.last, a.input.lastBreaks, a.skips, b.skips,
          a.reaches, h ▸ b.reaches, ha, hb⟩
      else none
    else none
  else none

end LeanTex.Core.Layout.Spacing
