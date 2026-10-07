module

public import LeanTex.Core.Layout
import all LeanTex.Core.Layout
public import LeanTex.Core.Layout.GlyphBounds

namespace LeanTex.Core.Layout

open Dim Font

/-- Pairing an extent with its outline status preserves the actual
producer's placement arithmetic, including the nominal fallback. This
equation does not turn that fallback into containment evidence. -/
public theorem glyphBounds_agree (font : Font) (size raise : Sp) (gid : Nat) :
    (GlyphBounds.glyph font size raise gid).extent = glyphVExtent font size raise gid := by
  unfold GlyphBounds.glyph glyphVExtent
  cases font.yExtent gid <;> rfl

/-- A known outline in a line returned by the real label producer is
contained vertically after the real label placement. The metric belongs
to those produced segments; the formula reads the painted run's own face,
size and raise. Missing outlines are deliberately outside this conditional
geometry lemma and require a diagnostic from the producer. -/
public theorem labelLine_outline_covers (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (segs : Array Seg) (size : Sp)
    (ink : Ir.Pic.LabelInk)
    (h : labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink))
    (idx : Nat) (runColor : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : RunMetrics)
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

/-- The missing-evidence check sees every glyph of every actual run. A
larger known outline in another run cannot hide an unresolved glyph. -/
public theorem labelGlyphUnknown_missing (fs : FontSet) (size : Sp) (segs : Array Seg)
    (idx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution)
    (hrun : Seg.run idx color link width glyphs sz leading decorations raise ground attr ∈ segs)
    (g : Nat × Char × Sp) (hg : g ∈ glyphs)
    (hmissing : (fs.get idx).yExtent g.1 = none) :
    labelGlyphUnknown fs size segs = true := by
  apply Array.any_eq_true'.mpr
  refine ⟨_, hrun, ?_⟩
  apply Array.any_eq_true'.mpr
  exact ⟨g, hg, (GlyphBounds.glyph_unresolved_exact _ _ _ _).mpr hmissing⟩

/-- Passing the producer's check supplies real outline evidence for each
painted glyph. This is derived from the check, never assumed of the font. -/
public theorem labelGlyphUnknown_complete (fs : FontSet) (size : Sp) (segs : Array Seg)
    (h : labelGlyphUnknown fs size segs = false)
    (idx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution)
    (hrun : Seg.run idx color link width glyphs sz leading decorations raise ground attr ∈ segs)
    (g : Nat × Char × Sp) (hg : g ∈ glyphs) :
    ∃ lo hi, (fs.get idx).yExtent g.1 = some (lo, hi) := by
  cases he : (fs.get idx).yExtent g.1 with
  | none =>
    have hm := labelGlyphUnknown_missing fs size segs idx color link width glyphs sz
      leading decorations raise ground attr hrun g hg he
    simp [h] at hm
  | some p => exact ⟨p.1, p.2, rfl⟩

/-- Vertical outline containment over the runs a line actually paints.
Each glyph is read in its own face, size and raise. Non-glyph segments do
not assert a font-outline fact. -/
public def LineOut.OutlinesIn (line : LineOut) (fs : FontSet) (top bottom : Sp) : Prop :=
  ∀ (idx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution),
    Seg.run idx color link width glyphs sz leading decorations raise ground attr ∈ line.segs →
    ∀ g ∈ glyphs, ∃ lo hi,
      (fs.get idx).yExtent g.1 = some (lo, hi) ∧
      let runSize := if sz == 0 then line.size else sz
      let above := hi * runSize / ((fs.get idx).unitsPerEm : Int) + raise
      let below := (-lo) * runSize / ((fs.get idx).unitsPerEm : Int) - raise
      top ≤ line.y - above ∧ line.y + below ≤ bottom

/-- Containment survives enlarging the reserved interval. -/
public theorem LineOut.OutlinesIn.mono (line : LineOut) (fs : FontSet)
    (top bottom top' bottom' : Sp) (h : line.OutlinesIn fs top bottom)
    (htop : top' ≤ top) (hbottom : bottom ≤ bottom') :
    line.OutlinesIn fs top' bottom' := by
  intro idx color link width glyphs sz leading decorations raise ground attr hrun g hg
  obtain ⟨lo, hi, he, ha, hb⟩ :=
    h idx color link width glyphs sz leading decorations raise ground attr hrun g hg
  exact ⟨lo, hi, he, Int.le_trans htop ha, Int.le_trans hb hbottom⟩

/-- With complete outline evidence, the actual placed producer result
satisfies containment for every run, including mixed faces and raises. -/
public theorem labelLine_outlines_covers (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (segs : Array Seg) (size : Sp)
    (ink : Ir.Pic.LabelInk)
    (h : labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink))
    (hk : labelGlyphUnknown fs size segs = false)
    (place : Ir.Pic.Place) (x y : Sp) (align : Ir.Pic.LabelAlign) :
    let box := Ir.Pic.labelGlyphBox x y align ink
    (labelLine place x y align ink segs size leaf).OutlinesIn fs
      (place.toPage box.2).2 (place.toPage box.1).2 := by
  dsimp only
  intro idx runColor link width glyphs sz leading decorations raise ground attr hrun g hg
  obtain ⟨lo, hi, he⟩ := labelGlyphUnknown_complete fs size segs hk idx runColor link
    width glyphs sz leading decorations raise ground attr hrun g hg
  refine ⟨lo, hi, he, ?_⟩
  exact labelLine_outline_covers fs imgs geom xHeight leaf content color scale segs size
    ink h idx runColor link width glyphs sz leading decorations raise ground attr hrun
    g hg lo hi he place x y align

/-- Losses introduced by the picture-label boundary carry the source
label's structured key. Existing producer diagnostics retain their own
subjects and are accounted separately. -/
public def LabelLossNamed (content : Array Ir.Inline) (diags : Array Diag) : Prop :=
  ∃ d ∈ diags, d.subject = some (Ir.plainText content) ∧
    (d.kind ∈ ([.W0328, .W0394, .E0395, .W0396] : List DiagCode) ∨
      (d.kind.loss == .dropped || d.kind.loss == .pending) = true)

public theorem labelFailureNamed_accounts (content : Array Ir.Inline) (diags : Array Diag)
    (h : labelFailureNamed content diags = true) : LabelLossNamed content diags := by
  obtain ⟨d, hd, hs⟩ := Array.any_eq_true'.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨d, hd, hs.1, Or.inr hs.2⟩

public theorem LabelLossNamed.mono (content : Array Ir.Inline) (before after : Array Diag)
    (h : LabelLossNamed content before)
    (keep : ∀ d ∈ before, d ∈ after) : LabelLossNamed content after := by
  obtain ⟨d, hd, hs, hk⟩ := h
  exact ⟨d, keep d hd, hs, hk⟩

/-- The complete producer line, with real outline evidence, fits the box
that picture layout actually reserves. The premise is the decidable
comparison that `emitLabel` executes on the two actual measurements. -/
public theorem labelLine_reserved_covers (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (segs : Array Seg) (size : Sp)
    (ink : Ir.Pic.LabelInk)
    (h : labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink))
    (hk : labelGlyphUnknown fs size segs = false)
    (place : Ir.Pic.Place) (x y : Sp) (align : Ir.Pic.LabelAlign)
    (hr : labelReserveCovers (Ir.Pic.labelGlyphBox x y align ink)
      (pictureLabelBox fs imgs geom xHeight x y content scale align)) :
    let box := pictureLabelBox fs imgs geom xHeight x y content scale align
    (labelLine place x y align ink segs size leaf).OutlinesIn fs
      (place.toPage box.2).2 (place.toPage box.1).2 := by
  dsimp only
  apply LineOut.OutlinesIn.mono _ _ _ _
    _ _ (labelLine_outlines_covers fs imgs geom xHeight leaf content color scale
      segs size ink h hk place x y align)
  · simp only [Ir.Pic.Place.toPage]
    exact Int.add_le_add_left (Int.sub_le_sub_left hr.2 _) _
  · simp only [Ir.Pic.Place.toPage]
    exact Int.add_le_add_left (Int.sub_le_sub_left hr.1 _) _

/-- A source label contributes the exact line selected by its
producer, contains every chosen line, and bounds every painted glyph
inside its canonical reserve. Textually blank content may produce no line. -/
public def LabelCovered (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) (lines : Array LineOut) : Prop :=
  (labelTextBlank content = true ∧
    labelInk fs imgs geom xHeight leaf content color scale = none) ∨
    ∃ segs size ink,
      labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink) ∧
      (labelResult fs imgs geom xHeight leaf content color scale).lineCount ≤ 1 ∧
      labelLine place x y align ink segs size leaf ∈ lines ∧
      let box := pictureLabelBox fs imgs geom xHeight x y content scale align
      (labelLine place x y align ink segs size leaf).OutlinesIn fs
        (place.toPage box.2).2 (place.toPage box.1).2

public theorem LabelCovered.mono (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) (before after : Array LineOut)
    (h : LabelCovered fs imgs geom xHeight leaf place x y content color scale align before)
    (keep : ∀ line ∈ before, line ∈ after) :
    LabelCovered fs imgs geom xHeight leaf place x y content color scale align after := by
  rcases h with he | ⟨segs, size, ink, hp, hn, hl, hb⟩
  · exact Or.inl he
  · exact Or.inr ⟨segs, size, ink, hp, hn, keep _ hl, hb⟩

/-- Every source label passed to the actual emitter either contributes its
complete, measured line within the canonical reserve, or names the precise
loss in a diagnostic keyed by the label. No premise asserts correctness of
shaping, font outlines, or the metric consumer. -/
public theorem emitLabel_ink_covered_or_named (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) :
    let emitted := emitLabel fs imgs geom xHeight leaf place x y content color scale align
    LabelCovered fs imgs geom xHeight leaf place x y content color scale align
      emitted.line?.toArray ∨ LabelLossNamed content emitted.diags := by
  dsimp only
  cases hl : (labelResult fs imgs geom xHeight leaf content color scale).line? with
  | none =>
    by_cases he : labelTextBlank content = true
    · exact Or.inl (Or.inl ⟨he, hl⟩)
    by_cases hd : labelFailureNamed content
        (if 1 < (labelResult fs imgs geom xHeight leaf content color scale).lineCount then
          ((labelResult fs imgs geom xHeight leaf content color scale).diags.map
            (nameLabelDiag (Ir.plainText content))).push {
              kind := .W0328,
              message := "picture label spans multiple lines; only its first line is kept",
              span := (labelResult fs imgs geom xHeight leaf content color scale).source,
              subject := some (Ir.plainText content) }
        else (labelResult fs imgs geom xHeight leaf content color scale).diags.map
          (nameLabelDiag (Ir.plainText content))) = true
    · right
      simpa [emitLabel, finishLabel, hl, he, hd] using labelFailureNamed_accounts content _ hd
    right
    refine ⟨{
      kind := .E0395, message := "picture label produced no line",
      span := (labelResult fs imgs geom xHeight leaf content color scale).source,
      subject := some (Ir.plainText content) }, ?_, rfl, by simp⟩
    simp [emitLabel, finishLabel, hl, he, hd]
  | some p =>
    rcases p with ⟨segs, size, ink⟩
    have hp : labelInk fs imgs geom xHeight leaf content color scale =
        some (segs, size, ink) := hl
    by_cases hn : 1 < (labelResult fs imgs geom xHeight leaf content color scale).lineCount
    · right
      refine ⟨{
        kind := .W0328,
        message := "picture label spans multiple lines; only its first line is kept",
        span := (labelResult fs imgs geom xHeight leaf content color scale).source,
        subject := some (Ir.plainText content) }, ?_, rfl, by simp⟩
      simp only [emitLabel, finishLabel, hl, hn, ↓reduceIte]
      repeat' split
      all_goals simp
    by_cases hk : labelGlyphUnknown fs size segs = true
    · right
      refine ⟨{
        kind := .W0394,
        message := "picture label has glyphs without measured outline bounds",
        span := (labelResult fs imgs geom xHeight leaf content color scale).source,
        subject := some (Ir.plainText content) }, ?_, rfl, by simp⟩
      simp only [emitLabel, finishLabel, hl, hn, hk, ↓reduceIte]
      split <;> simp
    have hknown : labelGlyphUnknown fs size segs = false := Bool.eq_false_iff.mpr hk
    by_cases hr : labelReserveCovers (Ir.Pic.labelGlyphBox x y align ink)
        (pictureLabelBox fs imgs geom xHeight x y content scale align)
    · left
      right
      refine ⟨segs, size, ink, hp, Nat.le_of_not_gt hn, ?_, ?_⟩
      · simp [emitLabel, finishLabel, hl, hn, hk, hr]
      · exact labelLine_reserved_covers fs imgs geom xHeight leaf content color scale
          segs size ink hp hknown place x y align hr
    · right
      refine ⟨{
        kind := .W0396,
        message := "picture label extends beyond its reserved glyph box",
        span := (labelResult fs imgs geom xHeight leaf content color scale).source,
        subject := some (Ir.plainText content) }, ?_, rfl, by simp⟩
      simp [emitLabel, finishLabel, hl, hn, hk, hr]

/-- The label boundary preserves every producer diagnostic, supplying the
label key only when the producer supplied none. -/
public theorem emitLabel_producer_diags_accounts (fs : FontSet) (imgs : Image.Store)
    (geom : Geom) (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) (d : Diag)
    (hd : d ∈ (labelResult fs imgs geom xHeight leaf content color scale).diags) :
    nameLabelDiag (Ir.plainText content) d ∈
      (emitLabel fs imgs geom xHeight leaf place x y content color scale align).diags := by
  have hm : nameLabelDiag (Ir.plainText content) d ∈
      (labelResult fs imgs geom xHeight leaf content color scale).diags.map
        (nameLabelDiag (Ir.plainText content)) := Array.mem_map_of_mem hd
  simp only [emitLabel, finishLabel]
  repeat' split
  all_goals simp [hm]

/-- Adding a label subject does not replace a producer's source location. -/
public theorem nameLabelDiag_source_exact (key : String) (d : Diag) :
    (nameLabelDiag key d).span = d.span := by rfl

/-- Missing outline evidence always emits its own keyed diagnostic, even
when the same label also wraps or exceeds its reserve. The nominal extent
used for placement is never substituted for this evidence. -/
public theorem emitLabel_unresolved_named (fs : FontSet) (imgs : Image.Store)
    (geom : Geom) (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) (segs : Array Seg) (size : Sp) (ink : Ir.Pic.LabelInk)
    (hl : labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink))
    (hu : labelGlyphUnknown fs size segs = true) :
    ∃ d ∈ (emitLabel fs imgs geom xHeight leaf place x y content color scale align).diags,
      d.kind = .W0394 ∧ d.subject = some (Ir.plainText content) := by
  refine ⟨{
    kind := .W0394,
    message := "picture label has glyphs without measured outline bounds",
    span := (labelResult fs imgs geom xHeight leaf content color scale).source,
    subject := some (Ir.plainText content) }, ?_, rfl, rfl⟩
  change (labelResult fs imgs geom xHeight leaf content color scale).line? =
    some (segs, size, ink) at hl
  simp only [emitLabel, finishLabel, hl, hu, ↓reduceIte]
  repeat' split
  all_goals simp

/-- The missing-outline account uses the source of the line actually
selected by the producer, including after a later line is truncated. -/
public theorem emitLabel_unresolved_source_named (fs : FontSet) (imgs : Image.Store)
    (geom : Geom) (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) (segs : Array Seg) (size : Sp) (ink : Ir.Pic.LabelInk)
    (hl : labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink))
    (hu : labelGlyphUnknown fs size segs = true) :
    ∃ d ∈ (emitLabel fs imgs geom xHeight leaf place x y content color scale align).diags,
      d.kind = .W0394 ∧ d.subject = some (Ir.plainText content) ∧
        d.span = (labelResult fs imgs geom xHeight leaf content color scale).source := by
  refine ⟨{
    kind := .W0394,
    message := "picture label has glyphs without measured outline bounds",
    span := (labelResult fs imgs geom xHeight leaf content color scale).source,
    subject := some (Ir.plainText content) }, ?_, rfl, rfl, rfl⟩
  change (labelResult fs imgs geom xHeight leaf content color scale).line? =
    some (segs, size, ink) at hl
  simp only [emitLabel, finishLabel, hl, hu, ↓reduceIte]
  repeat' split
  all_goals simp

/-- A shape step preserves every line emitted by an earlier shape. -/
public theorem emitPictureShape_lines (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (out : PictureEmission) (shape : Ir.Pic.Shape) (line : LineOut)
    (h : line ∈ out.lines) :
    line ∈ (emitPictureShape fs imgs geom xHeight leaf place out shape).lines := by
  cases shape <;> simp only [emitPictureShape, Id.run, pure]
  all_goals first
    | exact h
    | (split <;> simp [h])

/-- A shape step preserves every diagnostic emitted by an earlier shape. -/
public theorem emitPictureShape_diags (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (out : PictureEmission) (shape : Ir.Pic.Shape) (d : Diag)
    (h : d ∈ out.diags) :
    d ∈ (emitPictureShape fs imgs geom xHeight leaf place out shape).diags := by
  cases shape <;> simp only [emitPictureShape, Id.run, pure]
  all_goals first
    | exact h
    | exact Array.mem_append_left _ h

/-- The actual shape emitter appends the selected line; a label cannot be
certified by a line present only in an unused producer result. -/
public theorem emitPictureShape_label_lines (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place) (out : PictureEmission)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) (line : LineOut)
    (h : line ∈
      (emitLabel fs imgs geom xHeight leaf place x y content color scale align).line?.toArray) :
    line ∈ (emitPictureShape fs imgs geom xHeight leaf place out
      (.label x y content color scale align)).lines := by
  simp only [emitPictureShape, Id.run, pure]
  cases he : (emitLabel fs imgs geom xHeight leaf place x y content color scale align).line?
  · simp [he] at h
  · simp [he] at h
    simp [h]

/-- The actual shape emitter appends the label's entire diagnostic account. -/
public theorem emitPictureShape_label_diags (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place) (out : PictureEmission)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign) (d : Diag)
    (h : d ∈ (emitLabel fs imgs geom xHeight leaf place x y content color scale align).diags) :
    d ∈ (emitPictureShape fs imgs geom xHeight leaf place out
      (.label x y content color scale align)).diags := by
  exact Array.mem_append_right _ h

/-- Each label step of the real shape emitter either appends a complete
covered line or a keyed loss. This includes failed production, unknown
outlines, extra chosen lines, and differences from the reserved metric. -/
public theorem emitPictureShape_label_ink_covered_or_named (fs : FontSet) (imgs : Image.Store)
    (geom : Geom) (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (out : PictureEmission) (x y : Sp) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (align : Ir.Pic.LabelAlign) :
    let emitted := emitPictureShape fs imgs geom xHeight leaf place out
      (.label x y content color scale align)
    LabelCovered fs imgs geom xHeight leaf place x y content color scale align
      emitted.lines ∨ LabelLossNamed content emitted.diags := by
  rcases emitLabel_ink_covered_or_named fs imgs geom xHeight leaf place
      x y content color scale align with hc | hn
  · exact Or.inl (LabelCovered.mono fs imgs geom xHeight leaf place
      x y content color scale align _ _ hc
      (emitPictureShape_label_lines fs imgs geom xHeight leaf place out
        x y content color scale align))
  · exact Or.inr (LabelLossNamed.mono content _ _ hn
      (emitPictureShape_label_diags fs imgs geom xHeight leaf place out
        x y content color scale align))

/-- Every source label in the actual picture shape fold is covered or
named. The induction tracks how many source shapes have been consumed,
so neither an unvisited label nor a detached measurement can satisfy it.

This replaces a claim about plain text in the body face and the cap-height
alignment band with actual shaped runs and their reserved glyph box. It is
the producer contract consumed by picture placement, not a claim that an
author's explicit bounding box encloses all of a picture's ink. -/
public theorem ink_covered_or_named (fs : FontSet) (imgs : Image.Store) (geom : Geom)
    (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place) (pic : Ir.Pic.Picture)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ pic.shapes) :
    let emitted := emitPicture fs imgs geom xHeight leaf place pic
    LabelCovered fs imgs geom xHeight leaf place x y content color scale align
      emitted.lines ∨ LabelLossNamed content emitted.diags := by
  obtain ⟨j, hj, hget⟩ := Array.mem_iff_getElem.mp hs
  have all : j < pic.shapes.size →
      let emitted := emitPicture fs imgs geom xHeight leaf place pic
      LabelCovered fs imgs geom xHeight leaf place x y content color scale align
        emitted.lines ∨ LabelLossNamed content emitted.diags := by
    refine Array.foldl_induction
      (motive := fun n (acc : PictureEmission) => j < n →
        LabelCovered fs imgs geom xHeight leaf place x y content color scale align
          acc.lines ∨ LabelLossNamed content acc.diags) ?_ ?_
    · omega
    · intro i acc ih hnext
      by_cases hprev : j < i.val
      · rcases ih hprev with hc | hn
        · exact Or.inl (LabelCovered.mono fs imgs geom xHeight leaf place
            x y content color scale align _ _ hc
            (emitPictureShape_lines fs imgs geom xHeight leaf place acc pic.shapes[i]))
        · exact Or.inr (LabelLossNamed.mono content _ _ hn
            (emitPictureShape_diags fs imgs geom xHeight leaf place acc pic.shapes[i]))
      · have hij : i.val = j := by omega
        have hshape : pic.shapes[i] = .label x y content color scale align := by
          change pic.shapes[i.val] = _
          simpa only [hij] using hget
        rw [hshape]
        exact emitPictureShape_label_ink_covered_or_named fs imgs geom xHeight leaf place
          acc x y content color scale align
  exact all hj

/-- Every label diagnostic survives the actual picture fold. The index
tracks the source label's visit; later shapes can only append diagnostics. -/
public theorem emitPicture_label_diags_accounts (fs : FontSet) (imgs : Image.Store)
    (geom : Geom) (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (pic : Ir.Pic.Picture) (x y : Sp) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (align : Ir.Pic.LabelAlign)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ pic.shapes)
    (d : Diag)
    (hd : d ∈ (emitLabel fs imgs geom xHeight leaf place x y content color scale align).diags) :
    d ∈ (emitPicture fs imgs geom xHeight leaf place pic).diags := by
  obtain ⟨j, hj, hget⟩ := Array.mem_iff_getElem.mp hs
  have all : j < pic.shapes.size →
      d ∈ (emitPicture fs imgs geom xHeight leaf place pic).diags := by
    refine Array.foldl_induction
      (motive := fun n (acc : PictureEmission) => j < n → d ∈ acc.diags) ?_ ?_
    · omega
    · intro i acc ih hnext
      by_cases hprev : j < i.val
      · exact emitPictureShape_diags fs imgs geom xHeight leaf place acc
          pic.shapes[i] d (ih hprev)
      · have hij : i.val = j := by omega
        have hshape : pic.shapes[i] = .label x y content color scale align := by
          change pic.shapes[i.val] = _
          simpa only [hij] using hget
        rw [hshape]
        exact emitPictureShape_label_diags fs imgs geom xHeight leaf place acc
          x y content color scale align d hd
  exact all hj

/-- Diagnostics from actual inline production reach the picture account,
including failures that prevented a glyph or an entire line from being
produced. Existing subjects are preserved. -/
public theorem emitPicture_producer_diags_accounts (fs : FontSet) (imgs : Image.Store)
    (geom : Geom) (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (pic : Ir.Pic.Picture) (x y : Sp) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (align : Ir.Pic.LabelAlign)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ pic.shapes)
    (d : Diag)
    (hd : d ∈ (labelResult fs imgs geom xHeight leaf content color scale).diags) :
    nameLabelDiag (Ir.plainText content) d ∈
      (emitPicture fs imgs geom xHeight leaf place pic).diags :=
  emitPicture_label_diags_accounts fs imgs geom xHeight leaf place pic x y content
    color scale align hs _ (emitLabel_producer_diags_accounts fs imgs geom xHeight
      leaf place x y content color scale align d hd)

/-- A glyph with missing outline evidence in any actual label run is
named by the picture that emits it. This conclusion holds independently
of line wrapping, the other glyphs' extents, or subsequent shapes. -/
public theorem emitPicture_missing_outline_named (fs : FontSet) (imgs : Image.Store)
    (geom : Geom) (xHeight : Sp) (leaf : Option Nat) (place : Ir.Pic.Place)
    (pic : Ir.Pic.Picture) (x y : Sp) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (align : Ir.Pic.LabelAlign)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ pic.shapes)
    (segs : Array Seg) (size : Sp) (ink : Ir.Pic.LabelInk)
    (hl : labelInk fs imgs geom xHeight leaf content color scale = some (segs, size, ink))
    (idx : Nat) (runColor : Ir.Color) (link : Option String) (width : Sp)
    (glyphs : Array (Nat × Char × Sp)) (sz : Sp) (leading : RunMetrics)
    (decorations : Decorations) (raise : Sp) (ground : Option Ir.Color)
    (attr : Attribution)
    (hrun : Seg.run idx runColor link width glyphs sz leading decorations raise ground attr ∈ segs)
    (g : Nat × Char × Sp) (hg : g ∈ glyphs)
    (hmissing : (fs.get idx).yExtent g.1 = none) :
    ∃ d ∈ (emitPicture fs imgs geom xHeight leaf place pic).diags,
      d.kind = .W0394 ∧ d.subject = some (Ir.plainText content) := by
  obtain ⟨d, hd, hk, hkey⟩ := emitLabel_unresolved_named fs imgs geom xHeight
    leaf place x y content color scale align segs size ink hl
    (labelGlyphUnknown_missing fs size segs idx runColor link width glyphs sz
      leading decorations raise ground attr hrun g hg hmissing)
  exact ⟨d, emitPicture_label_diags_accounts fs imgs geom xHeight leaf place pic
    x y content color scale align hs d hd, hk, hkey⟩

/-- The former alignment-band bound is precisely a cap-height bound,
regardless of alignment or position. Actual outlines above that height
falsify it while remaining inside the separately reserved glyph box. -/
public theorem label_alignment_covers_exact (x y : Sp) (align : Ir.Pic.LabelAlign)
    (ink : Ir.Pic.LabelInk) (reach : Sp) :
    Ir.Pic.labelBaseline y align ink + reach ≤ (Ir.Pic.labelInkBox x y align ink).2.2 ↔
      reach ≤ ink.height := by
  rw [Ir.Pic.labelBaseline_box_exact x y align ink]
  have arith : ∀ top height above : Int, top - height + above ≤ top ↔ above ≤ height := by
    intro top height above
    omega
  exact arith _ _ _

end LeanTex.Core.Layout
