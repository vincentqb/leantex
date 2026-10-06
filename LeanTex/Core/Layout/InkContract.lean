import LeanTex.Core.Layout
import LeanTex.Core.Layout.GlyphBounds

namespace LeanTex.Core.Layout

open Dim Font

/-- Pairing an extent with its outline status preserves the actual
producer's placement arithmetic, including the nominal fallback. This
equation does not turn that fallback into containment evidence. -/
theorem glyphBounds_agree (font : Font) (size raise : Sp) (gid : Nat) :
    (GlyphBounds.glyph font size raise gid).extent = glyphVExtent font size raise gid := by
  unfold GlyphBounds.glyph glyphVExtent
  cases font.yExtent gid <;> rfl

/-- A known outline in a line returned by the real label producer is
contained vertically after the real label placement. The metric belongs
to those produced segments; the formula reads the painted run's own face,
size and raise. Missing outlines are deliberately outside this conditional
geometry lemma and require a diagnostic from the producer. -/
theorem labelLine_outline_covers (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (segs : Array Seg) (size : Sp)
    (ink : Ir.Pic.LabelInk)
    (h : labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink))
    (idx : Nat) (runColor : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : Option Sp)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution)
    (hrun : Seg.run idx runColor link width glyphs sz leading decorations raise ground attr ∈ segs)
    (g : Nat × Char × Sp) (hg : g ∈ glyphs) (lo hi : Int)
    (houtline : (fs.get idx).yExtent g.1 = some (lo, hi))
    (place : Ir.Pic.Place) (x y : Sp) (align : Ir.Pic.LabelAlign) :
    let runSize := if sz == 0 then size else sz
    let top := hi * runSize / ((fs.get idx).unitsPerEm : Int) + raise
    let below := (-lo) * runSize / ((fs.get idx).unitsPerEm : Int) - raise
    let line := labelLine place x y align ink segs size leaf
    let box := Ir.Pic.labelGlyphBox x y align ink
    (place.toPage box.2).2 ≤ line.y - top ∧
      line.y + below ≤ (place.toPage box.1).2 := by
  have covered := labelLine_covers fs imgs geom xHeight leaf content color scale
    segs size ink h idx runColor link width glyphs sz leading decorations raise ground
    attr hrun g hg place x y align
  simpa only [glyphVExtent, houtline] using covered

end LeanTex.Core.Layout
