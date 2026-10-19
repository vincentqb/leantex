module

public import LeanTex.Core.Gfx
public import LeanTex.Core.GfxSvg
public import LeanTex.Core.Html
public import LeanTex.Core.Image

/-! A drawn SVG figure as the page's own inline SVG, its text live `<text>` in the document's faces
at the shaped pens. -/

namespace LeanTex.Core.FigureSvg

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx

/-- The custom property a role's text reads its family from. -/
@[expose] public def roleFamily : Nat → String
  | 0 => "var(--font-body)"
  | 1 => "var(--font-sans)"
  | _ => "var(--font-mono)"

/-- A run's own space is y up, as a font's is; SVG text's is y down. -/
@[expose] public def textFlip : Affine := ⟨1, 0, 0, -1, 0, 0⟩

/-- The scalars a shaped run sets, one per glyph, in order. -/
@[expose] public def runText (s : Shaped) : String := String.ofList (s.glyphs.toList.map (·.2.2.1))

/-- Each glyph's pen x, in points: the `x` list that places the glyph of the
same position. -/
@[expose] public def penList (s : Shaped) : String :=
  " ".intercalate (s.glyphs.toList.map (·.2.2.2.toBpString))

/-- The run's font as CSS: its role's family and the resolved face's weight and style. -/
@[expose] public def fontCss (s : Shaped) : String :=
  s!"font-family: {roleFamily s.role}; font-weight: {s.weight}; " ++
    s!"font-style: {if s.italic then "italic" else "normal"}; direction: ltr"

/-- The run's paint: its solid fill, translucent where it is; a run with no solid fill paints nothing. -/
@[expose] public def paintAttrs (s : Shaped) : Array (String × String) :=
  match s.fill with
  | some { paint := .solid c, alpha, .. } =>
    #[("fill", c.css)] ++
      (if alpha = Alpha.opaque then #[] else #[("fill-opacity", GfxSvg.alphaSpell alpha)])
  | _ => #[("fill", "none")]

/-- Whether a run sets a scalar past the Basic Multilingual Plane, which a browser may count twice
in an `x` list. -/
@[expose] public def astral (s : Shaped) : Bool := s.glyphs.any fun g => 0x10000 ≤ g.2.2.1.toNat

/-- A shaped run as live SVG text, each glyph at its pen x; a run with an astral scalar places
each glyph in its own `tspan`. -/
public def textNode (fr : GfxSvg.SFrame) (s : Shaped) : Html.Node :=
  let lang : Array (String × String) := match s.lang with
    | some t => #[("lang", t)]
    | none => #[]
  -- A run that paints nothing sets no words on the page, as on the PDF's.
  if (paintAttrs s).contains ("fill", "none") then Html.elem "g" else
  let xf := GfxSvg.transformAttr (fr.lift (s.xf.compose textFlip))
  let rest : Array (String × String) :=
    #[("y", "0"), ("font-size", s.size.toBpString), ("style", fontCss s), ("xml:space", "preserve")] ++
      paintAttrs s ++ lang
  if astral s then
    Html.elem "text" (s.glyphs.map fun g =>
      Html.elem "tspan" #[Html.text (String.singleton g.2.2.1)] #[("x", g.2.2.2.toBpString)])
      (#[xf] ++ rest)
  else Html.elem "text" #[Html.text (runText s)] (#[xf, ("x", penList s)] ++ rest)

mutual

-- conserves: none — a test: whether any node of a tree sets text.
/-- Whether a node, or any node under it, is engine-set text. -/
public def labelsOne {L : Type} (acc : Bool) : Node L → Bool
  | .label _ => true
  | .group _ _ _ kids => labelsList acc kids.toList
  | .draw _ _ _ | .use _ _ | .stamp _ _ _ _ | .image _ _ | .words _ => acc

public def labelsList {L : Type} (acc : Bool) : List (Node L) → Bool
  | [] => acc
  | n :: rest => labelsList (labelsOne acc n) rest

end

/-- Whether a figure sets any text: in its nodes or a symbol's body. -/
@[expose] public def setsText {L : Type} (fig : Figure L) : Bool :=
  labelsList false fig.nodes.toList || fig.symbols.any (labelsList false ·.toList)

/-- Whether a drawn figure ships inline: still, drawn whole, with no raster, and setting text. -/
@[expose] public def inlines {L : Type} (fig : Figure L) (moving : Bool) : Bool :=
  !moving && fig.losses.isEmpty && fig.rasters.isEmpty && setsText fig

/-- Whether a store entry ships inline: a drawn figure that `inlines`. -/
@[expose] public def inlineable (en : Image.Loaded) : Bool :=
  match en.vector with
  | some v => inlines v en.moving
  | none => false

/-- Where the engine's drawing of an SVG figure ships: the PDF always, the HTML too where it inlines or moves. -/
@[expose] public def drawingShipsIn {L : Type} (fig : Figure L) (moving : Bool) :
    Option Diag.Output :=
  -- premise: svgOutputScopeChecks — an inlined figure's page names its text's notes
  if moving || inlines fig moving then none else some .pdf

/-- The shaped figure an entry's page ships inline, if it ships one. -/
public def inlineFigure? (imgs : Image.Store) (k : Nat) : Option (Figure Shaped) := do
  let en ← imgs.get? k
  if inlineable en then (imgs.shaped[k]?).join else none

/-- A drawn figure as inline SVG: its box as the viewBox in points, under `attrs`, clipping where it clips. -/
public def inlineSvg (fig : Figure Shaped) (attrs : Array (String × String)) : Html.Node :=
  let w := (fig.box.2.1 - fig.box.1.1).toBpString
  let h := (fig.box.2.2 - fig.box.1.2).toBpString
  Html.elem "svg" (GfxSvg.spell 0 (GfxSvg.tree textNode #[] (GfxSvg.documentIso fig.box) fig))
    (#[("viewBox", s!"0 0 {w} {h}")] ++ attrs ++
      #[("overflow", if fig.clipToBox then "hidden" else "visible")])

public theorem inlineSvg_marks_projects (fig : Figure Shaped) :
    GfxSvg.readMarks (GfxSvg.documentIso fig.box) (GfxSvg.tree textNode #[] (GfxSvg.documentIso fig.box) fig) =
      fig.marks :=
  GfxSvg.marks_projects textNode #[] (GfxSvg.documentIso fig.box) fig

end LeanTex.Core.FigureSvg
