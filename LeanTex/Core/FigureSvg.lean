module

public import LeanTex.Core.Gfx
public import LeanTex.Core.GfxSvg
public import LeanTex.Core.Html
public import LeanTex.Core.Image

/-!
# A drawn figure as the page's own SVG, its text live

An imported SVG the engine draws whole, and whose text it shaped in the
document's faces (`Image.Store.shaped`), ships in the HTML as inline SVG:
the figure through the SVG emitter (`GfxSvg.tree`), and each run a
`<text>` in its role's family — the custom property the page's body text
reads (`--font-body`, `--font-sans`, `--font-mono`) — at the resolved
face's own weight and style, every glyph at the pen x the shaping gave. So
the browser sets the scalars the PDF sets, in the face the PDF sets them
in, where the PDF sets them, and the words stay text a reader can select
and a search can find.

Only such a figure: one that moves keeps its authored bytes in an
`<img>`, where its animation runs, and so does one the engine draws with a
loss, one that embeds a raster (an inline `<image>` names a resource the
page would have to carry twice) and one that sets no text, which an `<img>`
already draws exactly (`inlineable`).
-/

namespace LeanTex.Core.FigureSvg

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx

/-- The family a role's text reads: the custom property the page's text in
that role reads too, whatever stylesheet mode declared it. -/
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
  " ".intercalate (s.glyphs.toList.map (·.2.2.2.toPtString))

/-- The run's font as CSS: its role's family, and the resolved face's weight
and style stated outright, so nothing the page inherits selects another
face. -/
@[expose] public def fontCss (s : Shaped) : String :=
  s!"font-family: {roleFamily s.role}; font-weight: {s.weight}; " ++
    s!"font-style: {if s.italic then "italic" else "normal"}; direction: ltr"

/-- The run's paint: its solid fill, translucent where it is. A run with no
solid fill paints nothing, as on the PDF page (`Pdf.shapedOps`). -/
@[expose] public def paintAttrs (s : Shaped) : Array (String × String) :=
  match s.fill with
  | some { paint := .solid c, alpha, .. } =>
    #[("fill", c.css)] ++
      (if alpha = Alpha.opaque then #[] else #[("fill-opacity", GfxSvg.alphaSpell alpha)])
  | _ => #[("fill", "none")]

/-- Whether a run sets a scalar past the Basic Multilingual Plane: one a
browser may count as two characters of an `x` list (a UTF-16 surrogate
pair), where SVG 2 counts it as one. -/
@[expose] public def astral (s : Shaped) : Bool := s.glyphs.any fun g => 0x10000 ≤ g.2.2.1.toNat

/-- **A shaped run as live SVG text**: the run's frame map, placed by the
frame it stands in, carries its baseline origin; each glyph sits at its pen
x on that baseline, every character addressable (`xml:space`), so the `x`
list and the characters pair one to one. A run with a scalar past the Basic
Multilingual Plane places each glyph in a `tspan` of its own instead, one
`x` each, so no count of characters can shift the pens after it. -/
public def textNode (fr : GfxSvg.SFrame) (s : Shaped) : Html.Node :=
  let lang : Array (String × String) := match s.lang with
    | some t => #[("lang", t)]
    | none => #[]
  -- A run that paints nothing sets no words on the page, as on the PDF's.
  if (paintAttrs s).contains ("fill", "none") then Html.elem "g" else
  let xf := GfxSvg.transformAttr (fr.lift (s.xf.compose textFlip))
  let rest : Array (String × String) :=
    #[("y", "0"), ("font-size", s.size.toPtString), ("style", fontCss s), ("xml:space", "preserve")] ++
      paintAttrs s ++ lang
  if astral s then
    Html.elem "text" (s.glyphs.map fun g =>
      Html.elem "tspan" #[Html.text (String.singleton g.2.2.1)] #[("x", g.2.2.2.toPtString)])
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

/-- **Which drawn figures ship inline**, read off the figure and whether it
moves: still, drawn whole, with no raster, and setting text. -/
@[expose] public def inlines {L : Type} (fig : Figure L) (moving : Bool) : Bool :=
  !moving && fig.losses.isEmpty && fig.rasters.isEmpty && setsText fig

/-- **Which store entries ship inline**: a drawn figure that `inlines`. -/
@[expose] public def inlineable (en : Image.Loaded) : Bool :=
  match en.vector with
  | some v => inlines v en.moving
  | none => false

/-- **Where the engine's drawing of an SVG figure ships**: the PDF always,
and the HTML too where the figure ships inline (`inlines`) or moves — its
print and reduced-motion still face is the drawing — while any other still
figure's HTML face is its authored bytes, which the browser draws in its
own faces. What a note says of the text the engine's drawing sets — a
family set in the document's face, a substituted or uncovered glyph — is
the scope of the artifacts it ships in. -/
@[expose] public def drawingShipsIn {L : Type} (fig : Figure L) (moving : Bool) :
    Option Diag.Output :=
  -- premise: svgOutputScopeChecks — the page of an inlined figure carries the engine's
  -- <svg> and names its text's notes; the page of a figure kept as authored bytes names
  -- none of them
  if moving || inlines fig moving then none else some .pdf

/-- The shaped figure an entry's page ships inline, if it ships one. -/
public def inlineFigure? (imgs : Image.Store) (k : Nat) : Option (Figure Shaped) := do
  let en ← imgs.get? k
  if inlineable en then (imgs.shaped[k]?).join else none

/-- **A drawn figure as inline SVG**: the figure's box as the viewBox in
points, under `attrs` (its name and the size the page gives it), clipping
exactly where the figure clips to its box. -/
public def inlineSvg (fig : Figure Shaped) (attrs : Array (String × String)) : Html.Node :=
  let w := (fig.box.2.1 - fig.box.1.1).toPtString
  let h := (fig.box.2.2 - fig.box.1.2).toPtString
  Html.elem "svg" (GfxSvg.spell 0 (GfxSvg.tree textNode #[] (GfxSvg.documentIso fig.box) fig))
    (#[("viewBox", s!"0 0 {w} {h}")] ++ attrs ++
      #[("overflow", if fig.clipToBox then "hidden" else "visible")])

/-- **The inline figure paints the figure's marks** (`_projects`): the typed
tree the page spells, read with SVG's meaning, is the figure's own ink —
the reading `Gfx.backend_marks_agree` holds the PDF's operators to. -/
public theorem inlineSvg_marks_projects (fig : Figure Shaped) :
    GfxSvg.readMarks (GfxSvg.documentIso fig.box) (GfxSvg.tree textNode #[] (GfxSvg.documentIso fig.box) fig) =
      fig.marks :=
  GfxSvg.marks_projects textNode #[] (GfxSvg.documentIso fig.box) fig

end LeanTex.Core.FigureSvg
