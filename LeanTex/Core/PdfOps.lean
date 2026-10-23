module

public import LeanTex.Core.Dim
public import LeanTex.Core.Color
public import LeanTex.Core.Gfx
import LeanTex.Core.DeriveBEq

/-! The typed operators of a PDF content stream, shared by page assembly and the figure writer. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim

/-- Path construction operators, ISO 32000-2 §8.5.2 (Table 58). -/
public inductive PathOp where
  | moveTo (x y : Length)
  | lineTo (x y : Length)
  | curveTo (x1 y1 x2 y2 x3 y3 : Length)
  | close
  | rect (x y w h : Length)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One element of a `TJ` array (ISO 32000-2 §9.4.3): glyphs, glyphs with their pair kerns,
or an adjustment in thousandths of the text space unit. -/
public inductive TextItem where
  | glyphs (gids : Array Nat)
  | kerned (gids : Array Nat) (nums : Array Int)
  | adjust (d : Int)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Artifact types (ISO 32000-2 §14.8.2.2.2, Table 363). -/
public inductive ArtifactKind where
  | pagination
  | layout
  | page
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The tag a marked-content sequence opens with (§14.6.2): an artifact, content with its
structure type, page-unique MCID and structure leaf, or a span replacing its text. -/
public inductive MarkTag where
  | artifact (kind : Option ArtifactKind)
  | content (s : String) (mcid : Nat) (leaf : Nat)
  /-- A span whose text reads as `actual` in place of its glyphs' (§14.9.4). -/
  | span (actual : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Text-object operators (§9.3–9.4), with marked content nested as a balanced pair. -/
public inductive TextOp where
  | scale (permille : Int)
  | move (x y : Length)
  | font (res : Nat) (size : Length)
  | color (c : Ir.Color)
  | show (items : Array TextItem)
  | marked (tag : MarkTag) (body : Array TextOp)
  deriving Repr, Inhabited

deriving_structural_beq TextOp

/-- A path's paint: a device colour, or a shading pattern (§8.7.3) with its gradient. -/
public inductive PdfPaint where
  | solid (c : Ir.Color)
  | pattern (res : Nat) (g : Gfx.Gradient)
  deriving Repr, BEq, DecidableEq, Inhabited

public structure PaintFill where
  paint : PdfPaint
  evenOdd : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A path's stroke; an absent field keeps PDF's initial graphics state (§8.4.1, Table 51). -/
public structure PaintStroke where
  paint : PdfPaint
  width : Length
  cap : Option Gfx.Cap
  join : Option Gfx.Join
  miter : Option Rat
  dash : Option (Array Length × Length)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An ExtGState resource (§8.4.5) and the constant alphas it sets for fills and strokes. -/
public structure ExtG where
  res : Nat
  fill : Gfx.Alpha
  stroke : Gfx.Alpha
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a figure's XObject is: a symbol form, an isolated transparency group (§11.6.6), a
stamp painted with its instance's state, or a raster image. -/
public inductive XKind where
  | symbol
  | group
  | stamp (fill : Option PdfPaint) (stroke : Option PaintStroke) (gs : Option ExtG)
  | raster (k : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A figure form's content key; a stamp carries the reach its instances' strokes extend past it. -/
public inductive FormKind where
  | symbol
  | group
  | stamp (reach : Length)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One page-level painting operation, in PDF user space. -/
public inductive ContentOp where
  | fill (color : Ir.Color) (x y w h : Length)
  /-- A path with its own paints inside `q … Q`; the paints present decide the painting operator. -/
  | paint (fill : Option PaintFill) (stroke : Option PaintStroke) (gs : Option ExtG)
      (segs : Array PathOp)
  /-- The page's one text object, `BT … ET`. -/
  | text (ops : Array TextOp)
  | image (x y w h : Length) (res : Nat)
  /-- The outlined box drawn in place of an image that did not load. -/
  | imageMissing (x y w h : Length)
  | marked (tag : MarkTag) (body : Array ContentOp)
  /-- A saved graphics state, `q [cm] [/GS gs] [clip W n]… body Q`. -/
  | group (m : Option Gfx.Affine) (gs : Option ExtG) (clips : Array (Array PathOp × Gfx.Rule))
      (body : Array ContentOp)
  /-- A shading painted over the clip in force (`sh`, §8.7.4.2). -/
  | shade (res : Nat) (g : Gfx.Gradient)
  /-- A path painted with the state in force, as a stamp form's body. -/
  | outline (fill : Option Gfx.Rule) (stroke : Bool) (segs : Array PathOp)
  /-- An XObject painted under a matrix, `q [cm] [state] /Name Do Q`, with the content it means. -/
  | xobject (m : Option Gfx.Affine) (res : Nat) (kind : XKind) (body : Array ContentOp)
  deriving Repr, Inhabited

deriving_structural_beq ContentOp

end LeanTex.Core.Pdf
