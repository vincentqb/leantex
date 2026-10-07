module

public import LeanTex.Core.Layout.SpacingContract
import all LeanTex.Core.Layout
import all LeanTex.Core.Layout.SpacingContract

namespace LeanTex.Core.Layout

open Dim

/-- The collision arm reserves the measured neighbouring intervals. This
is a coordinate statement; outline decoding and page redistribution are
separate boundaries. -/
public theorem inlineMathGap_covers (normal depth height : Sp) :
    depth + height ≤ inlineMathGap true normal depth height :=
  Int.le_max_right ..

/-- Whenever the input intervals already clear, math retains exactly the
font-relative baseline gap, for arbitrary sizes and measured extents. -/
public theorem inlineMathGap_fixed_point (math : Bool) (normal depth height : Sp)
    (hclear : depth + height ≤ normal) :
    inlineMathGap math normal depth height = normal := by
  cases math <;> simp only [inlineMathGap, Bool.false_eq_true,
    ite_false, ite_true, Int.max_eq_left hclear]

/-- A formula fits the existing line's font-relative envelope when both
its ambient text strut and its raised construction bounds fit. These are
input measurements, not an assumption about the resulting placement.
Outline containment depends on the font decoder; this contract does not
turn a font's fallback metrics into a proof about paint. -/
public def InlineMathFits (box : LineBox) (m : MathLineMetrics)
    (leading : Option Sp) (factor : Nat) (raise : Sp) : Prop :=
  let strut := leadedBox m.ascent m.descent
    (leading.getD (Ir.leadingFor m.size factor))
  strut.1 ≤ box.above ∧ strut.2 ≤ box.below ∧
    max 0 (m.top + raise) ≤ box.above ∧
    max 0 (-m.bottom - raise) ≤ box.below

private theorem merge_absorbed (acc : Option LineBox) (box : LineBox)
    (ha : box.above ≤ (acc.getD ⟨0, 0, 0, 0⟩).above)
    (hb : box.below ≤ (acc.getD ⟨0, 0, 0, 0⟩).below)
    (hna : 0 ≤ box.above) (hnb : 0 ≤ box.below) :
    ((mergeLineBox acc box).getD ⟨0, 0, 0, 0⟩).above =
        (acc.getD ⟨0, 0, 0, 0⟩).above ∧
      ((mergeLineBox acc box).getD ⟨0, 0, 0, 0⟩).below =
        (acc.getD ⟨0, 0, 0, 0⟩).below := by
  cases acc with
  | none => exact ⟨Int.le_antisymm ha hna, Int.le_antisymm hb hnb⟩
  | some a => exact ⟨Int.max_eq_left ha, Int.max_eq_left hb⟩

/-- Appending any inline math run whose measured bounds fit leaves both
interline terms unchanged. The line already contains text, and an explicit
leading on the new run must already be in force on that line. No glyph,
font index, size, raise, or leading is fixed to a sample value. -/
public theorem inlineMath_extent_fixed_point
    (fs : Font.FontSet) (fontSize bodyAscent bodyCap bodyDescent : Sp)
    (factor : Nat) (size : Sp) (segs : Array Seg)
    (idx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (m : MathLineMetrics)
    (leading : Option Sp) (decorations : Decorations) (raise : Sp)
    (ground : Option Ir.Color) (attr : Attribution)
    (htext : segs.any Seg.isRun = true)
    (hleading : leading.isSome = true →
      segs.any Seg.hasLeading = true)
    (hfit : InlineMathFits
      (lineExtent fs fontSize bodyAscent bodyCap bodyDescent factor size segs)
      m leading factor raise) :
    let extra := Seg.run idx color link width glyphs sz
      {leading, math := some m} decorations raise ground attr
    let before := lineExtent fs fontSize bodyAscent bodyCap bodyDescent factor size segs
    let after := lineExtent fs fontSize bodyAscent bodyCap bodyDescent factor size
      (segs.push extra)
    after.above = before.above ∧ after.below = before.below := by
  let extra := Seg.run idx color link width glyphs sz
    {leading, math := some m} decorations raise ground attr
  have hl : (segs.push extra).any Seg.hasLeading =
    segs.any Seg.hasLeading := by
    simp only [Array.any_push, extra, Seg.hasLeading]
    cases h : leading.isSome with
    | false => exact Bool.or_false _
    | true => simpa only [Bool.or_true] using (hleading h).symm
  have ht : (segs.push extra).any Seg.isRun = true := by
    simp [extra, Seg.isRun]
  dsimp only
  change
    (lineExtent fs fontSize bodyAscent bodyCap bodyDescent factor size
      (segs.push extra)).above = _ ∧
    (lineExtent fs fontSize bodyAscent bodyCap bodyDescent factor size
      (segs.push extra)).below = _
  unfold InlineMathFits at hfit
  unfold lineExtent at hfit ⊢
  dsimp only at hfit ⊢
  rw [hl, ht]
  simp only [htext, Bool.or_true, ite_true, Array.foldl_push, extra,
    lineBoxStep] at hfit ⊢
  rcases hfit with ⟨ha, hb, htop, hbottom⟩
  apply merge_absorbed
  · exact Int.max_le.mpr ⟨ha, htop⟩
  · exact Int.max_le.mpr ⟨hb, hbottom⟩
  · exact Int.le_trans (Int.le_max_left ..) (Int.le_max_right ..)
  · exact Int.le_trans (Int.le_max_left ..) (Int.le_max_right ..)

namespace Spacing

/-- The formula's input envelope at a production placement boundary.
Reading the page and context here keeps their private representation out
of the placement theorem's interface. -/
public def InlineMathFitsAt (r : Context) (b : Page) (size : Sp)
    (segs : Array Seg) (m : MathLineMetrics) (leading : Option Sp)
    (raise : Sp) : Prop :=
  InlineMathFits
    (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
      b.geom.leading size segs) m leading b.geom.leading raise

/-- The two adjacent measured ink intervals fit the font-relative gap.
Unlike the font envelope, this premise sees the preceding line's actual
descender and the new line's actual raised outlines. -/
public def InlineMathClearAt (r : Context) (b : Page) (size : Sp)
    (segs : Array Seg) : Prop :=
  b.boxDepth + (segsInk r.fs segs).1 ≤ b.prevBelow +
    (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
      b.geom.leading size segs).above

private theorem input_origin (r : Context) (b : Page) (size : Sp)
    (segs : Array Seg) (h : InlineMathClearAt r b size segs) :
    (input r b size segs).origin = b.y + (b.prevBelow +
      (lineExtent r.fs b.geom.fontSize b.ascent b.capHeight b.descent
        b.geom.leading size segs).above) + b.surfaceTop := by
  simp only [input, Page.textGap, inlineMathGap_fixed_point _ _ _ _ h]

/-- A bounded inline formula preserves the baseline appended by the actual
production placer, and both placements preserve the shipped prefix.
The premises are input geometry: an ordinary text boundary, a common
font-relative envelope, and both page-fit inequalities. The claim is
before page-close stretch/shrink distribution and does not cover a page
break or claim that arbitrary font metadata bounds visible ink. -/
public theorem inlineMath_placement_fixed_point
    (a : Pending) (r : Context) (b : Page) (x size : Sp) (segs : Array Seg)
    (width : Sp) (idx : Nat) (color : Ir.Color) (link : Option String)
    (runWidth : Sp) (glyphs : Array (Nat × Char × Sp)) (sz : Sp)
    (m : MathLineMetrics) (leading : Option Sp) (decorations : Decorations)
    (raise : Sp) (ground : Option Ir.Color) (attr : Attribution)
    (htext : segs.any Seg.isRun = true)
    (hleading : leading.isSome = true →
      segs.any Seg.hasLeading = true)
    (henvelope : InlineMathFitsAt r b size segs m leading raise)
    (hclear : InlineMathClearAt r b size segs)
    (hclear' : InlineMathClearAt r b size (segs.push (.run idx color link runWidth glyphs sz
      {leading, math := some m} decorations raise ground attr)))
    (hready : Ready b segs) (hfit : Fits a r b size segs)
    (hready' : Ready b (segs.push (.run idx color link runWidth glyphs sz
      {leading, math := some m} decorations raise ground attr)))
    (hfit' : Fits a r b size (segs.push (.run idx color link runWidth glyphs sz
      {leading, math := some m} decorations raise ground attr))) :
    let extra := Seg.run idx color link runWidth glyphs sz
      {leading, math := some m} decorations raise ground attr
    shipped (place a r b x size segs width) = shipped b ∧
    shipped (place a r b x size (segs.push extra) (width + runWidth)) = shipped b ∧
    baselines (place a r b x size (segs.push extra) (width + runWidth)) =
      baselines (place a r b x size segs width) := by
  have hg := inlineMath_extent_fixed_point r.fs b.geom.fontSize b.ascent
    b.capHeight b.descent b.geom.leading size segs idx color link runWidth
    glyphs sz m leading decorations raise ground attr htext hleading henvelope
  have hp := place_exact a r b x size segs width hready hfit
  have hp' := place_exact a r b x size _ (width + runWidth) hready' hfit'
  refine ⟨hp.1, hp'.1, ?_⟩
  rw [hp.2, hp'.2]
  rw [input_origin _ _ _ _ hclear, input_origin _ _ _ _ hclear', hg.1]
  rfl

end Spacing
end LeanTex.Core.Layout
