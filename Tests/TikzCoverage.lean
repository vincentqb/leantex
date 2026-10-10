module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

namespace Tests.TikzCoverage

/-- A document holding one picture under the declared refusal, so what the
subset draws is what ships. -/
def picDoc (opts body : String) (pre : String := "") : String :=
  "\\documentclass{article}\n\\pictures{ tool = none }\n" ++ pre ++
    "\\palette{ grid = #2A6F4E }\n\\begin{document}\n\\begin{tikzpicture}" ++ opts ++ "\n" ++
    body ++ "\n\\end{tikzpicture}\n\\end{document}"

/-- What a page of pictures shows, read off `Layout.Out`: each line's text
and position, each mark's box, stroke and runs. -/
structure Shown where
  lines : Array (String × Dim.Sp × Dim.Sp)
  boxes : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp)
  strokes : Array (Ir.Color × Dim.Sp)
  runs : Array (Array Nat × Bool)
  deriving BEq, Repr

def shownOf (oneFace : Font.FontSet) (src : String) : Shown :=
  let c := censusOf #[] (layoutOf oneFace (elabStr src).1)
  match c[0]? with
  | some p =>
    { lines := p.lines.map fun l => (l.text, l.x, l.y), boxes := p.pathBoxes
      strokes := p.pathStrokes, runs := p.pathRuns }
  | none => { lines := #[], boxes := #[], strokes := #[], runs := #[] }

/-- Two shown pages agree within the rounding two separately rounded offsets
can differ by: two sp per coordinate. -/
def Shown.close (a b : Shown) : Bool :=
  let near (x y : Dim.Sp) : Bool := decide (x - y ≤ 2 ∧ y - x ≤ 2)
  a.lines.size == b.lines.size && a.boxes.size == b.boxes.size &&
    (a.lines.zip b.lines).all (fun ((s, x, y), (s', x', y')) => s == s' && near x x' && near y y') &&
    (a.boxes.zip b.boxes).all (fun ((x, y, w, h), (x', y', w', h')) =>
      near x x' && near y y' && near w w' && near h h') &&
    a.strokes == b.strokes && a.runs == b.runs

/-- The typed SVG a picture ships: every path's `d`, every text's position. -/
def svgOf (src : String) : Array String × Array (Array (String × String)) :=
  let doc := (elabStr src).1
  let ds := doc.body.foldl (fun acc b => acc ++ attrValuesOf (· == "path") "d" (HtmlDoc.blockNode {} b)) #[]
  let texts := doc.body.foldl (fun acc b =>
    acc ++ (elemNodesOne (· == "text") #[] (HtmlDoc.blockNode {} b)).filterMap fun n =>
      match n with
      | .elem _ attrs _ => some (attrs.filter fun (k, _) => k == "x" || k == "y")
      | _ => none) #[]
  (ds, texts)

/-- The losses the subset named. -/
def lossesOf (src : String) : Array Diag :=
  (elabStr src).2.filter fun d => d.code == "W0334" || d.code == "E0333" || d.code == "W0012"

/-- The colour of the first glyph run on the first line holding `needle`. -/
def runColorOf (oneFace : Font.FontSet) (src : String) (needle : String) : Option Ir.Color :=
  let out := layoutOf oneFace (elabStr src).1
  let line := (out.pages.flatMap (·.lines)).find? fun l => hasStr (lineText l) needle
  line.bind fun l => l.segs.findSome? fun seg => match seg with
    | .run _ color .. => some color
    | _ => none

/-- The geometry a page's picture draws, as the figure states it. -/
def drawsOf (oneFace : Font.FontSet) (src : String) :
    Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke) :=
  (layoutOf oneFace (elabStr src).1).pages.flatMap pageDraws

end Tests.TikzCoverage

open Tests.TikzCoverage in
/-- **A tree is placed as pgf's growth function places it.** The invariant
whose absence sent every `child` to the boundary: TikZ's tree syntax
(manual §21) is a node and its children, each child `level distance` from
its parent's centre along the growth direction and the `n` siblings spread
`sibling distance` apart across it (tikz.code.tex, `\tikz@grow@direction`),
each joined to its parent by an `edge from parent` path. So a tree ships
exactly the page its explicit spelling ships — nodes at the computed
positions, `\draw (parent) -- (child)` for each edge — on `Layout.Out` and
in the typed SVG alike: growth up flips the sibling order, `grow'` turns it
back, a level style sets a level's spread, `missing` keeps its slot, an
`edge from parent[draw=none]` draws no edge, the `edge from parent` style's
tips stand at the parent, and a child's default name is pgf's
`<parent>-<k>`. Invented content; each explicit position is the growth
function's arithmetic and a LuaLaTeX probe of the same tree. -/
def tikzTreeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let dist := "[level distance=10mm, sibling distance=20mm]"
  let cases : Array (String × String × String × String) := #[
    ("two children grow down", dist,
      "\\node (r) {R} child {node (a) {A}} child {node (b) {B}};",
      "\\node (r) {R};\\node (a) at (-1,-1) {A};\\node (b) at (1,-1) {B};\\draw (r) -- (a);\\draw (r) -- (b);"),
    ("growth up turns the siblings' order", dist,
      "\\node (r) {R} [grow=up] child {node (a) {A}} child {node (b) {B}};",
      "\\node (r) {R};\\node (a) at (1,1) {A};\\node (b) at (-1,1) {B};\\draw (r) -- (a);\\draw (r) -- (b);"),
    ("grow' turns it back", dist,
      "\\node (r) {R} [grow'=up] child {node (a) {A}} child {node (b) {B}};",
      "\\node (r) {R};\\node (a) at (-1,1) {A};\\node (b) at (1,1) {B};\\draw (r) -- (a);\\draw (r) -- (b);"),
    ("a grandchild stands under its parent", dist,
      "\\node (r) {R} child {node (a) {A} child {node (c) {C}}};",
      "\\node (r) {R};\\node (a) at (0,-1) {A};\\node (c) at (0,-2) {C};\\draw (r) -- (a);\\draw (a) -- (c);"),
    ("a level style spreads its level, missing keeps a slot, draw=none drops an edge, \
the edge style's tip stands at the parent",
      "[level distance=10mm, level 1/.style={sibling distance=30mm}, edge from parent/.style={draw,latex-}]",
      "\\node (r) {R} child {node (a) {A}} child[missing] child {node (b) {B} edge from parent[draw=none]};",
      "\\node (r) {R};\\node (a) at (-3,-1) {A};\\node (b) at (3,-1) {B};\\draw[latex-] (r) -- (a);"),
    ("a child's default name is its parent's and its place", dist,
      "\\node (r) {R} child {node {A}} child {node {B}};\\draw[->] (r-1) -- (r-2);",
      "\\node (r) {R};\\node (a) at (-1,-1) {A};\\node (b) at (1,-1) {B};\\draw (r) -- (a);\\draw (r) -- (b);\\draw[->] (a) -- (b);"),
    ("a coordinate child ends its edge at its point", dist,
      "\\node (r) {R} child {coordinate (k)} child {node (b) {B}};",
      "\\node (r) {R};\\coordinate (k) at (-1,-1);\\node (b) at (1,-1) {B};\\draw (r) -- (k);\\draw (r) -- (b);")]
  for (name, opts, written, explicit) in cases do
    let w := picDoc opts written
    let e := picDoc opts explicit
    t s!"tree: {name}: no loss is named" (lossesOf w).isEmpty
    t s!"tree: {name}: Layout.Out ships the explicit page"
      (let a := shownOf oneFace w; let b := shownOf oneFace e
       !a.lines.isEmpty && a.close b)
    t s!"tree: {name}: the typed SVG ships the explicit tree" (svgOf w == svgOf e)
  -- A tree construct outside the subset is named, never dropped in silence.
  t "tree: child foreach is named"
    ((lossesOf (picDoc dist "\\node {R} child foreach \\x in {1,2} {node {\\x}};")).any
      fun d => d.code == "W0334" && hasStr d.message "child foreach")

open Tests.TikzCoverage in
/-- **A picture's statements read the colour and the font declared around
them.** The invariant whose absence routed every picture that grouped its
paths under `\textcolor`, `\color` or beamer's `\alert`: pgf's current
colour (`.`) is TeX's colour in force, so a path or a node's text with no
colour of its own sets in it, and a declaration holds to the end of its
group (TeXbook ch. 5); a font or size declaration sets every node after it
the same way. Read off `Layout.Out`: the stroke a path ships and the run a
label sets. Invented content. -/
def tikzScopeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let grid : Ir.Color := { r := 42, g := 111, b := 78 }
  let strokesOf (src : String) := (shownOf oneFace src).strokes.map (·.1)
  let colored := picDoc "" "\\textcolor{grid}{\\draw (0,0) -- (1,0);}\\draw (0,1) -- (1,1);"
  t "colour: a \\textcolor group strokes its paths, and only those"
    ((lossesOf colored).isEmpty && strokesOf colored == #[grid, Ir.Color.black])
  let declared := picDoc "" "{\\color{grid}\\draw (0,0) -- (1,0);}\\draw (0,1) -- (1,1);"
  t "colour: a \\color declaration holds to the end of its group"
    ((lossesOf declared).isEmpty && strokesOf declared == #[grid, Ir.Color.black])
  let explicitColor := picDoc "" "\\draw[grid] (0,0) -- (1,0);\\draw (0,1) -- (1,1);"
  t "colour: the group ships the page its explicit colour ships"
    ((shownOf oneFace colored).close (shownOf oneFace explicitColor))
  let label := picDoc "" "\\textcolor{grid}{\\node at (0,0) {G};}\\node at (1,0) {K};"
  t "colour: a node's text sets in the colour in force"
    (runColorOf oneFace label "G" == some grid && runColorOf oneFace label "K" == some Ir.Color.black)
  -- beamer's \alert over a statement: the slides class's alert colour.
  let deck := "\\documentclass{slides}\n\\theme{moloch}\n\\pictures{ tool = none }\n\\begin{document}\n" ++
    "\\begin{frame}{T}\n\\begin{tikzpicture}\n\\alert{\\draw (0,0) -- (1,0);}\\draw (0,1) -- (1,1);\n" ++
    "\\end{tikzpicture}\n\\end{frame}\n\\end{document}"
  let (deckDoc, deckDs) := elabStr deck
  let alertInk := (deckDoc.palette.find? "alert").getD Ir.Color.black
  t "colour: an \\alert group strokes in the alert colour"
    (!(deckDs.any fun d => d.code == "W0334") && alertInk != Ir.Color.black &&
      ((censusOf #[] (layoutOf oneFace deckDoc)).flatMap (·.pathStrokes)).map (·.1) ==
        #[alertInk, Ir.Color.black])
  -- Size: the picture's font= and a declaration among the statements.
  let sizeOf (src : String) (needle : String) := lineSizeOf (censusOf #[] (layoutOf oneFace (elabStr src).1)) 0 needle
  let picFont := picDoc "[font=\\scriptsize]" "\\node at (0,0) {A};"
  let nodeFont := picDoc "" "\\node[font=\\scriptsize] at (0,0) {A};"
  t "size: the picture's font= sets every node"
    ((sizeOf picFont "A").isSome && sizeOf picFont "A" == sizeOf nodeFont "A")
  let declSize := picDoc "" "{\\small\\node at (0,0) {A};}\\node at (2,0) {B};"
  let nodeSmall := picDoc "" "\\node[font=\\small] at (0,0) {A};\\node at (2,0) {B};"
  t "size: a declaration among the statements sets the nodes after it in its group"
    ((lossesOf declSize).isEmpty && sizeOf declSize "A" == sizeOf nodeSmall "A" &&
      sizeOf declSize "B" == sizeOf nodeSmall "B" && sizeOf declSize "A" != sizeOf declSize "B")

open Tests.TikzCoverage in
/-- **A path's operations draw what TikZ's path grammar says.** The
invariant whose absence routed a picture of dots and a computation graph:
`circle (r)` and `ellipse (a and b)` are closed curves about the current
point (manual §14.6), `\fill` of one is the curve filled and `\filldraw`
both; an arrow specification is two ends, `<-` a tip at the start and `<->`
one at each (§16.2); `draw=none` strokes nothing; a `coordinate` names a
point and reaches no box (§17.2.1); `above` and its siblings are the
opposite anchor standing on the coordinate, a length shifting it (§17.5.2).
Read off `Layout.Out` and the typed SVG; each explicit spelling is TikZ's
own equivalence. Invented content. -/
def tikzPathChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let grid : Ir.Color := { r := 42, g := 111, b := 78 }
  -- Circles and ellipses: the figure's own geometry, filled or stroked.
  let dot := picDoc "" "\\fill (1,1) circle (2pt);"
  t "circle: a filled circle ships one filled ellipse of its radius, no stroke"
    ((lossesOf dot).isEmpty && match (drawsOf oneFace dot).toList with
      | [(.ellipse _ _ rx ry, some fl, none)] =>
        rx == Dim.pt 2 && ry == Dim.pt 2 && fillColor? fl == some Ir.Color.black
      | _ => false)
  let oval := picDoc "" "\\draw (0,0) ellipse (1 and 0.5);"
  t "ellipse: two radii, stroked, unfilled"
    ((lossesOf oval).isEmpty && match (drawsOf oneFace oval).toList with
      | [(.ellipse _ _ rx ry, none, some _)] => rx == Dim.mm 10 && ry == Dim.mm 5
      | _ => false)
  let keyed := picDoc "" "\\draw (0,0) circle [radius=3mm];"
  t "circle: the radius key reads as the radius"
    ((lossesOf keyed).isEmpty && match (drawsOf oneFace keyed).toList with
      | [(.ellipse _ _ rx ry, none, some _)] => rx == Dim.mm 3 && ry == Dim.mm 3
      | _ => false)
  let both := picDoc "" "\\filldraw[fill=grid] (0,0) circle (1);"
  t "filldraw: the fill colour fills and the path's colour strokes"
    ((lossesOf both).isEmpty && match (drawsOf oneFace both).toList with
      | [(.ellipse .., some fl, some st)] =>
        fillColor? fl == some grid && strokeColor? st == some Ir.Color.black
      | _ => false)
  let lengthRadius := picDoc ""
    "\\pgfmathsetlengthmacro{\\p}{1.5pt}\\coordinate (z) at (1,0);\\fill (z) circle (\\p);"
  t "circle: a length macro is the radius, about a named point"
    ((lossesOf lengthRadius).isEmpty && match (drawsOf oneFace lengthRadius).toList with
      | [(.ellipse _ _ rx _, some _, none)] => rx == Dim.pt 3 / 2
      | _ => false)
  t "circle: the typed SVG ships an ellipse element"
    ((elabStr oval).1.body.foldl (fun n b =>
      n + (attrValuesOf (fun tag => tag == "ellipse" || tag == "circle") "cx"
        (HtmlDoc.blockNode {} b)).size) 0 == 1)
  -- Tips at either end.
  let tipsOf (src : String) : Nat := (drawsOf oneFace src).foldl (fun n (g, fl, st) =>
    match g with
    | .path _ => if isTipDraw fl st then n + 1 else n
    | _ => n) 0
  let back := picDoc "" "\\draw[<-] (0,0) -- (2,0);"
  let fore := picDoc "" "\\draw[->] (2,0) -- (0,0);"
  t "tips: a start tip stands where the reversed path's end tip stands"
    ((lossesOf back).isEmpty && tipsOf back == 1 &&
      ((shownOf oneFace back).boxes.qsort (fun a b => a.1 < b.1)) ==
        ((shownOf oneFace fore).boxes.qsort (fun a b => a.1 < b.1)))
  let twin := picDoc "" "\\draw[<->] (0,0) -- (2,0);"
  t "tips: a two-ended specification draws both tips" ((lossesOf twin).isEmpty && tipsOf twin == 2)
  let latexBack := picDoc "" "\\draw[latex-] (0,0) -- (2,0);"
  t "tips: a named start tip draws" ((lossesOf latexBack).isEmpty && tipsOf latexBack == 1)
  -- draw=none.
  let hidden := picDoc "" "\\draw[draw=none] (0,0) -- (1,0);\\node[draw, draw=none] at (0,1) {A};"
  t "draw=none: neither the path nor the node's outline strokes"
    ((lossesOf hidden).isEmpty && (shownOf oneFace hidden).boxes.isEmpty)
  -- Coordinates.
  let viaCoord := picDoc "" "\\coordinate (c) at (1,1);\\draw (0,0) -- (c);"
  let direct := picDoc "" "\\draw (0,0) -- (1,1);"
  t "coordinate: an edge to a coordinate is the edge to its point"
    ((lossesOf viaCoord).isEmpty && (shownOf oneFace viaCoord).close (shownOf oneFace direct))
  let far := picDoc "" "\\coordinate (k) at (5,5);\\draw (0,0) -- (1,1);"
  t "coordinate: a coordinate reaches no box"
    ((shownOf oneFace far).close (shownOf oneFace direct) && svgOf far == svgOf direct)
  -- Placement anchors.
  let above := picDoc "" "\\node[above] at (0,0) {A};\\draw (0,0) -- (1,0);"
  let south := picDoc "" "\\node[anchor=south] at (0,0) {A};\\draw (0,0) -- (1,0);"
  t "anchor: above is the south anchor on the coordinate"
    ((lossesOf above).isEmpty && (shownOf oneFace above).close (shownOf oneFace south))
  let shifted := picDoc "" "\\node[below left=2pt] at (0,0) {A};\\draw (0,0) -- (1,0);"
  let corner := picDoc "" "\\node[anchor=north east] at (-2pt,-2pt) {A};\\draw (0,0) -- (1,0);"
  t "anchor: a length after a corner direction shifts both axes"
    ((lossesOf shifted).isEmpty && (shownOf oneFace shifted).close (shownOf oneFace corner))
