module

public import LeanTex.Core.Gfx
public import LeanTex.Core.GfxSvg
public import LeanTex.Core.Font
public import LeanTex.Core.Ink
public import LeanTex.Core.Xml
import LeanTex.Core.HtmlResource

/-! A drawn figure's text as its faces' glyph outlines, for a still face that reads no font the page ships. -/

namespace LeanTex.Core.FigureOutline

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx

/-- One font unit in outline space: three points of 65536 sp. -/
@[expose] public def unitsPerFontUnit : Int := 3 * 65536

/-- A glyph's outline commands as closed subpaths in outline space, each quadratic as its cubic. -/
public def subpathsOf (cmds : Array Ink.Cmd) : Array Subpath := Id.run do
  let k := unitsPerFontUnit
  let q : Int := 65536
  let mut out : Array Subpath := #[]
  let mut cur : Option Subpath := none
  let mut px : Int := 0
  let mut py : Int := 0
  for c in cmds do
    match c with
    | .move x y =>
      if let some sp := cur then out := out.push sp
      cur := some { start := (k * x, k * y), segs := #[], closed := true }
      px := x
      py := y
    | .line x y =>
      cur := cur.map fun sp => { sp with segs := sp.segs.push (.line (k * x, k * y)) }
      px := x
      py := y
    | .quad cx cy x y =>
      let seg : Seg := .cubic ((px + 2 * cx) * q, (py + 2 * cy) * q)
        ((x + 2 * cx) * q, (y + 2 * cy) * q) (k * x, k * y)
      cur := cur.map fun sp => { sp with segs := sp.segs.push seg }
      px := x
      py := y
    | .cube ax ay bx bY x y =>
      let seg : Seg := .cubic (k * ax, k * ay) (k * bx, k * bY) (k * x, k * y)
      cur := cur.map fun sp => { sp with segs := sp.segs.push seg }
      px := x
      py := y
  if let some sp := cur then out := out.push sp
  return out

mutual

-- conserves: none — a census of the distinct glyphs a tree's text sets.
/-- Every distinct `(face, glyph)` a node's text sets, onto `acc`, in first
appearance. -/
public def glyphsOne (acc : Array (Nat × Nat)) : Node Shaped → Array (Nat × Nat)
  | .label s => s.glyphs.foldl (fun a (f, g, _, _) => if a.contains (f, g) then a else a.push (f, g)) acc
  | .group _ _ _ kids => glyphsList acc kids.toList
  | .draw _ _ _ | .use _ _ | .stamp _ _ _ _ | .image _ _ | .words _ => acc

public def glyphsList (acc : Array (Nat × Nat)) : List (Node Shaped) → Array (Nat × Nat)
  | [] => acc
  | n :: rest => glyphsList (glyphsOne acc n) rest

end

/-- Every distinct glyph a figure's text sets, nodes then symbols. -/
public def glyphTable (fig : Figure Shaped) : Array (Nat × Nat) :=
  fig.symbols.foldl (fun acc b => glyphsList acc b.toList) (glyphsList #[] fig.nodes.toList)

/-- Each glyph of a run as a stamp of its outline onto `acc`; a glyph without outline, or a run
without fill, paints nothing. -/
public def stampsOf (fs : Font.FontSet) (table : Array (Nat × Nat)) (glyphs : Array (Array Subpath))
    (base : Nat) (acc : Array (Node Empty)) (s : Shaped) : Array (Node Empty) :=
  if s.fill.isNone then acc else
  s.glyphs.foldl (fun acc (face, g, _, x) =>
    match table.idxOf? (face, g) with
    | some i =>
      if (glyphs[i]?.getD #[]).isEmpty then acc else
      let k : Rat := (s.size : Rat) / ((unitsPerFontUnit * ((fs.get face).unitsPerEm : Int) : Int) : Rat)
      acc.push (.stamp (base + i) (s.xf.compose ((Affine.translate x 0).compose (Affine.scale k k)))
        s.fill none)
    | none => acc) acc

mutual

-- conserves: none — a rewriting of text into the outlines it paints.
/-- One node with its text as stamps of its glyphs' outlines. -/
public def outlineOne (fs : Font.FontSet) (table : Array (Nat × Nat)) (glyphs : Array (Array Subpath))
    (base : Nat) (acc : Array (Node Empty)) : Node Shaped → Array (Node Empty)
  | .label s => stampsOf fs table glyphs base acc s
  | .group xf clips alpha kids =>
    acc.push (.group xf clips alpha (outlineList fs table glyphs base #[] kids.toList))
  | .draw g f st => acc.push (.draw g f st)
  | .use k xf => acc.push (.use k xf)
  | .stamp o xf f st => acc.push (.stamp o xf f st)
  | .image k xf => acc.push (.image k xf)
  | .words w => acc.push (.words w)

public def outlineList (fs : Font.FontSet) (table : Array (Nat × Nat)) (glyphs : Array (Array Subpath))
    (base : Nat) (acc : Array (Node Empty)) : List (Node Shaped) → Array (Node Empty)
  | [] => acc
  | n :: rest => outlineList fs table glyphs base (outlineOne fs table glyphs base acc n) rest

end

/-- A glyph's outline, or none where its face's outlines cannot be read. -/
public def glyphOutline (fs : Font.FontSet) (face g : Nat) : Array Subpath :=
  (((fs.get face).inkSrc.get.cmdsAt g).map subpathsOf).getD #[]

/-- A shaped figure with each run stamped glyph by glyph from outlines appended after the figure's own. -/
public def outlined (fs : Font.FontSet) (fig : Figure Shaped) : Figure Empty :=
  let table := glyphTable fig
  let base := fig.outlines.size
  let glyphs := table.map fun (face, g) => glyphOutline fs face g
  { box := fig.box, clipToBox := fig.clipToBox
    nodes := outlineList fs table glyphs base #[] fig.nodes.toList
    outlines := fig.outlines ++ glyphs
    symbols := fig.symbols.map fun b => outlineList fs table glyphs base #[] b.toList
    rasters := fig.rasters, title := fig.title, losses := fig.losses }

/-- A figure's rasters as the data URIs a file of its own embeds. -/
public def rasterRefs {L : Type} (fig : Figure L) : Array GfxSvg.RasterRef :=
  fig.rasters.map fun r =>
    { href := s!"data:image/{if r.jpeg then "jpeg" else "png"};base64,{HtmlResource.base64 r.bytes}"
      smooth := r.smooth }

mutual

-- conserves: none — a change of tree type, element for element.
/-- A spelled SVG tree as XML onto `acc`, every attribute written as one, empty values included. -/
public def xmlOne (acc : Array Xml.Node) : Html.Node → Array Xml.Node
  | .elem tag attrs kids => acc.push (.elem tag attrs (xmlList #[] kids.toList))
  | .text s => acc.push (.text s)
  | .style _ => acc
  | .script _ _ => acc

public def xmlList (acc : Array Xml.Node) : List Html.Node → Array Xml.Node
  | [] => acc
  | n :: rest => xmlList (xmlOne acc n) rest

end

/-- The still face of a drawn figure: a standalone SVG file, its text the faces' outlines, written as XML. -/
public def poster (fs : Font.FontSet) (fig : Figure Shaped) : String :=
  let o := outlined fs fig
  let root := GfxSvg.documentRoot o.box o.clipToBox
    (GfxSvg.spell 0 (GfxSvg.tree (fun _ e => nomatch e) (rasterRefs o) (GfxSvg.documentIso o.box) o))
  let body := (xmlOne #[] root).foldl (fun s n => s ++ (String.fromUTF8? (Xml.render n)).getD "") ""
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ body

end LeanTex.Core.FigureOutline
