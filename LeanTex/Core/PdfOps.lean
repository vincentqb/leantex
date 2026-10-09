module

public import LeanTex.Core.Dim
public import LeanTex.Core.Color
public import LeanTex.Core.Gfx

/-!
# The PDF content operators, as types

The vocabulary of a content stream, alone in a module so both the page
assembly (`PdfContent`) and the figure emitter (`GfxPdf`) build it. An
operator that names a resource also carries what the resource means — a
pattern's gradient, a form's body, an ExtGState's alphas — so a reader of the
typed stream recovers the meaning without the writer's table, while the
spelling reads only the name.
-/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim

/-- Path construction operators, ISO 32000-2 §8.5.2 (Table 58). -/
public inductive PathOp where
  | moveTo (x y : Sp)
  | lineTo (x y : Sp)
  | curveTo (x1 y1 x2 y2 x3 y3 : Sp)
  | close
  | rect (x y w h : Sp)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One element of a `TJ` array (§9.4.3): a glyph string, or a horizontal
adjustment in thousandths of the text space unit. `kerned` is a glyph
string whose glyphs each carry the number set before them — `nums`
beside `gids`, 0 for none — one run's string with its pair kerns, spelled
`<…>n<…>` as lualatex spells it, and one run for the glyph census all the
same. -/
public inductive TextItem where
  | glyphs (gids : Array Nat)
  | kerned (gids : Array Nat) (nums : Array Int)
  | adjust (d : Int)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Artifact types, ISO 32000-2 §14.8.2.2.2 Table 363: `/Pagination` for
running heads, feet and page numbers, `/Layout` for rules, fills and
bars, `/Page` for cut marks and printer's marks. -/
public inductive ArtifactKind where
  | pagination
  | layout
  | page
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The tag a marked-content sequence opens with (§14.6.2). An artifact
carries its type when the emission site knows it; a page fill carries
none, because the layout ships backgrounds, bars and cut marks in one
array and the writer will not guess between `/Layout` and `/Page`. Real
content carries the structure type of the element that lists it, its
marked-content identifier on the page (§14.7.5.1: unique per page), and
the structure leaf it paints — the last is data for the structure walk,
never spelled. -/
public inductive MarkTag where
  | artifact (kind : Option ArtifactKind)
  | content (s : String) (mcid : Nat) (leaf : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Text-object operators (§9.3–9.4): horizontal scale in per-mille,
text matrix, font resource and size, fill colour, and one `TJ` array;
and a marked-content sequence (§14.6: `BDC … EMC` may nest inside
`BT … ET`) — the only spelling of the pair, so an unbalanced one is
unrepresentable. -/
public inductive TextOp where
  | scale (permille : Int)
  | move (x y : Sp)
  | font (res : Nat) (size : Sp)
  | color (c : Ir.Color)
  | show (items : Array TextItem)
  | marked (tag : MarkTag) (body : Array TextOp)
  deriving Repr, BEq, Inhabited

/-- What a path paints with: a device colour, or a shading pattern (§8.7.3)
— its resource and the gradient it shades, whose frame map is the pattern
matrix: pattern space to the default space of the stream that paints
(§8.7.2), the placement composed in. -/
public inductive PdfPaint where
  | solid (c : Ir.Color)
  | pattern (res : Nat) (g : Gfx.Gradient)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A path's fill: its paint, and whether the even–odd rule decides
inside (`f*`, `B*`) rather than the nonzero rule. -/
public structure PaintFill where
  paint : PdfPaint
  evenOdd : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A path's stroke, each field spelled only where it differs from PDF's
initial graphics state (§8.4.1, Table 51: butt caps, miter joins, miter
limit 10, a solid line); the width is always spelled, as every stroked
path this writer ever shipped spelled it. -/
public structure PaintStroke where
  paint : PdfPaint
  width : Sp
  cap : Option Gfx.Cap
  join : Option Gfx.Join
  miter : Option Rat
  dash : Option (Array Sp × Sp)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An ExtGState resource (§8.4.5) and the constant alphas it sets: `ca`
for fills, `CA` for strokes. -/
public structure ExtG where
  res : Nat
  fill : Gfx.Alpha
  stroke : Gfx.Alpha
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What an XObject a figure paints is: a symbol's form, a transparency
group's form (§11.6.6, isolated), an outline stamp's form, or a figure
raster's image. A stamp's form is its outline and a painting operator and
nothing else, so it paints with the state its instance sets before the
`Do` — the fill colour, the stroke's colour and parameters, the alphas
carried here — as a Type 3 `d1` glyph does (§9.6.5): one form per outline
and operator, whatever paints it. -/
public inductive XKind where
  | symbol
  | group
  | stamp (fill : Option PdfPaint) (stroke : Option PaintStroke) (gs : Option ExtG)
  | raster (k : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a figure form is, keyed by content: a symbol's body, a
transparency group's, a stamp's outline with the reach its instances'
strokes extend past it — never the colour an instance paints a stamp with.
The reach is the margin the form's box needs: a form's box clips
(§8.10.1), so a stroked instance needs room for its stroke. -/
public inductive FormKind where
  | symbol
  | group
  | stamp (reach : Sp)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One page-level painting operation, in PDF user space. -/
public inductive ContentOp where
  /-- A filled rectangle: a page fill or a rule. -/
  | fill (color : Ir.Color) (x y w h : Sp)
  /-- A path with its paints, inside its own `q … Q`: the painting operator
  (`B`/`S`/`f`/`n`, starred under even–odd) is decided by which paints are
  present, and `gs` sets the constant alphas. -/
  | paint (fill : Option PaintFill) (stroke : Option PaintStroke) (gs : Option ExtG)
      (segs : Array PathOp)
  /-- The page's one text object, `BT … ET`. -/
  | text (ops : Array TextOp)
  /-- An image XObject mapped onto `w × h` at `(x, y)`. -/
  | image (x y w h : Sp) (res : Nat)
  /-- The outlined box standing where an image that did not load would. -/
  | imageMissing (x y w h : Sp)
  /-- A marked-content sequence around page-level operations. -/
  | marked (tag : MarkTag) (body : Array ContentOp)
  /-- A saved graphics state: `q [cm] [/GS gs] [clip W n]… body Q` — the
  only way this layer writes `q`/`Q` around operators, as `marked` is the
  only way it writes `BDC`/`EMC`. -/
  | group (m : Option Gfx.Affine) (gs : Option ExtG) (clips : Array (Array PathOp × Gfx.Rule))
      (body : Array ContentOp)
  /-- A shading painted over the clip in force (`sh`, §8.7.4.2). -/
  | shade (res : Nat) (g : Gfx.Gradient)
  /-- A path painted with the state in force and none of its own: the
  operator (`f`/`S`/`B`/`n`, starred under even–odd) by which paints it
  names — a stamp form's body. -/
  | outline (fill : Option Gfx.Rule) (stroke : Bool) (segs : Array PathOp)
  /-- An XObject painted under a matrix: `q [cm] [state] /Name Do Q`. The
  body is what the XObject's content means — the writer spells it once as
  the form's stream, a reader reads it here. -/
  | xobject (m : Option Gfx.Affine) (res : Nat) (kind : XKind) (body : Array ContentOp)
  deriving Repr, BEq, Inhabited

end LeanTex.Core.Pdf
