import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A synthetic article holding one picture: `pre` in the preamble, `opts`
the picture's own bracket, `body` its statements. -/
def picDoc (pre opts body : String) : String :=
  "\\documentclass{article}\\pictures{ tool = none }" ++ pre ++ "\\begin{document}\n" ++
  "\\begin{tikzpicture}" ++ opts ++ "\n" ++ body ++ "\n\\end{tikzpicture}\n\\end{document}"

/-- The stroke widths the first page ships, in paint order. -/
def shippedWidths (oneFace : Font.FontSet) (src : String) : Array Dim.Sp :=
  ((layoutOf oneFace (elabStr src).1).pages[0]?.map fun p =>
    p.paths.filterMap fun q => q.stroke.map (·.width)).getD #[]

/-- Does the source name any picture loss? Over the structured diagnostic. -/
def picLoss (src : String) : Bool :=
  (elabStr src).2.any fun d => d.code == "W0334" || d.code == "E0333"

mutual

/-- Every value an emitted element declares for attribute `key`, in tree
order. -/
def attrValuesOne (key : String) (acc : Array String) : Html.Node → Array String
  | .elem _ attrs kids =>
    let acc := match attrs.find? (·.1 == key) with
      | some (_, w) => acc.push w
      | none => acc
    attrValuesList key acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def attrValuesList (key : String) (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => attrValuesList key (attrValuesOne key acc k) rest

end

/-- Every value the HTML of a document's body declares for `key`. -/
def bodyAttrValues (doc : Ir.Doc) (key : String) : Array String :=
  doc.body.foldl (fun acc b => attrValuesOne key acc (HtmlDoc.blockNode {} b)) #[]

/-- **A declared line width is the width pgf strokes.** tikz.code.tex
(lines 1575–1581) defines the seven named widths as `line width=<w>`
styles, so a name and the key it abbreviates stroke one width, at every
level a key is read: a path's bracket, a node's, the picture's, an `every
path` style and a `\tikzset` line — the inner setting winning, as in pgf.
The defect named `semithick` a dropped key and stroked it at 0.4 pt; every
claim here is over the shipped page (`Layout.Out`) or the SVG the same IR
emits. Invented content. -/
def pictureWidthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let named : List (String × Dim.Sp) :=
    [("ultra thin", Dim.pt 1 / 10), ("very thin", Dim.pt 1 / 5), ("thin", Dim.pt 2 / 5),
     ("semithick", Dim.pt 3 / 5), ("thick", Dim.pt 4 / 5), ("very thick", Dim.pt 6 / 5),
     ("ultra thick", Dim.pt 8 / 5)]
  let path (key : String) : String := picDoc "" "" s!"\\draw[{key}] (0,0) -- (2,0);"
  t "every named width strokes pgf's width on a path, and names nothing"
    (named.all fun (k, w) => shippedWidths oneFace (path k) == #[w] && !picLoss (path k))
  let lw := path "line width=2pt"
  t "line width strokes the length it declares"
    (shippedWidths oneFace lw == #[Dim.pt 2] && !picLoss lw)
  let node := picDoc "" "" "\\node[draw, very thick, minimum size=1cm] at (0,0) {N};"
  t "a node's outline strokes its declared width"
    (shippedWidths oneFace node == #[Dim.pt 6 / 5] && !picLoss node)
  let pic := picDoc "" "[semithick]" "\\draw (0,0) -- (2,0);"
  let set := picDoc "\\tikzset{semithick}" "" "\\draw (0,0) -- (2,0);"
  let every := picDoc "" "[every path/.style={semithick}]" "\\draw (0,0) -- (2,0);"
  t "a width the picture, a tikzset line or every path sets reaches the path"
    ([pic, set, every].all fun s => shippedWidths oneFace s == #[Dim.pt 3 / 5] && !picLoss s)
  let inner := picDoc "" "[ultra thick]" "\\draw[thin] (0,0) -- (2,0);"
  let inner2 := picDoc "" "[thin]" "\\draw[ultra thick] (0,0) -- (2,0);"
  t "the path's own width beats the picture's, either way round"
    (shippedWidths oneFace inner == #[Dim.pt 2 / 5] &&
      shippedWidths oneFace inner2 == #[Dim.pt 8 / 5])
  let edge := picDoc "" "" "\\draw (0,0) to[very thin] (2,0);"
  t "an operation's bracket sets its width"
    (shippedWidths oneFace edge == #[Dim.pt 1 / 5] && !picLoss edge)
  let (doc, _) := elabStr (path "semithick")
  t "the SVG strokes the declared width"
    ((bodyAttrValues doc "stroke-width").contains (Dim.pt 3 / 5).toPtString)

/-- **A node's `font=` sets its label in the fonts it names, at the size the
document's own ladder gives each size switch.** TikZ runs the key's value
before the node's text (tikz.code.tex, the `font` option), so a size switch
means what it means in the document's paragraphs — the step a venue's
redefinition read out, where it did — and a series or shape switch is that
face. The defect expanded a redefined `\small` through the picture's macro
table, named the key as dropped and set the label at the body size; a run of
two switches was dropped whole. Asserted over the shipped page and the SVG.
Invented content. -/
def pictureFontChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let venue := "\\makeatletter\\renewcommand{\\small}{\\@setfontsize\\small{8.5}{10}}\\makeatother"
  let doc (pre body : String) : String :=
    picDoc pre "" body |>.replace "\\begin{document}\n"
      "\\begin{document}\n{\\small Smallword}\n\n"
  let sizes (src : String) (words : List String) : List (Option Dim.Sp) :=
    let c := censusOfSrc oneFace src
    words.map (lineSizeOf c 0)
  let node := doc venue "\\node[font=\\small] at (0,0) {Nodeword};"
  t "font=\\small sets a node at the size the document's \\small sets, and names nothing"
    ((match sizes node ["Smallword", "Nodeword"] with
      | [some a, some b] => a == b && a == Dim.pt 17 / 2
      | _ => false) && !picLoss node)
  let run := doc venue "\\node[font=\\bfseries\\small] at (0,0) {Boldword};"
  let (rd, _) := elabStr run
  t "a run of switches sets both: the size on the page, the weight in the SVG"
    ((match sizes run ["Smallword", "Boldword"] with
      | [some a, some b] => a == b
      | _ => false) && (bodyAttrValues rd "font-weight").contains "bolder" && !picLoss run)
  let edge := doc venue "\\draw (0,0) -- node[font=\\small] {Edgeword} (3,0);"
  t "an edge label's font= reads the same ladder"
    ((match sizes edge ["Smallword", "Edgeword"] with
      | [some a, some b] => a == b
      | _ => false) && !picLoss edge)
  let pic := picDoc venue "[font=\\small]" "\\node at (0,0) {Nodeword};"
  t "a picture's font= reaches its nodes"
    ((match sizes pic ["Nodeword"] with
      | [some a] => a == Dim.pt 17 / 2
      | _ => false) && !picLoss pic)
  t "a switch the engine cannot read is still named"
    (picLoss (doc "" "\\node[font=\\undefinedswitch] at (0,0) {Nodeword};") &&
      !picLoss (doc "" "\\node[font=\\itshape] at (0,0) {Nodeword};"))


/-- The deepest reach below the baseline of a word's glyphs, set in `font`
at `size`: the depth of the TeX box the word makes. -/
def wordDepth (font : Font.Font) (size : Dim.Sp) (word : String) : Dim.Sp :=
  word.toList.foldl (fun d c =>
    match (font.gid c).bind font.yExtent with
    | some (lo, _) => max d (-lo * size / (font.unitsPerEm : Int))
    | none => d) 0

/-- The height of an SVG's viewBox in the emitted page, in sp (to the
thousandth of a point the emitter writes). -/
def viewBoxHeight (page : String) : Option Dim.Sp := do
  let rest ← (page.splitOn "viewBox=\"0 0 ")[1]?
  let v ← (rest.splitOn "\"")[0]?
  let h ← (v.splitOn " ")[1]?
  let (m, sc) ← Decl.parseDecimal h
  pure (m * Dim.pt 1 / sc)

/-- **A node's box is its text box plus inner sep, as TikZ's** (pgf's
`\pgfnodeparttextbox`; tikz.code.tex, `\tikz@fig@continue`, where `text
height` and `text depth` set the box's `\ht` and `\dp`). A declared text box
is the node's, exactly: its north and south anchors stand one inner sep
beyond the declared height above the label's baseline and the declared depth
below it. An undeclared one is the glyphs' own, so a picture reserves below
a label with no descender its inner sep and no more — not the face's descent
as well (review F9). The defect named both keys dropped and measured every
border from the face's band. Asserted over the shipped page, and the SVG's
box. Invented content. -/
def pictureTextBoxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let font := oneFace.body
  let near (p q : Int) : Bool := decide (p - q ≤ 3 ∧ q - p ≤ 3)
  let size := (Layout.Geom.ofPage (elabStr (picDoc "" "" "")).1.page).fontSize
  let ex := font.xHeight * size / (font.unitsPerEm : Int)
  let sep := Picture.innerSep size
  -- The label's baseline and the first point of the first two paths, on the
  -- page (y down): the anchors those paths start from.
  let anchors (src : String) : Option (Dim.Sp × Dim.Sp × Dim.Sp) := do
    let (doc, _) := elabMeasured oneFace src
    let page ← (layoutOf oneFace doc).pages[0]?
    let label ← page.lines.find? fun l => hasStr (lineText l) "Label"
    let starts := page.paths.filterMap fun q => match q.path with
      | .segs ss => ss[0]?.map fun s => match s with
        | .line _ y1 _ _ => y1
        | .cubic _ y1 _ _ _ _ _ _ => y1
      | _ => none
    let north ← starts[0]?
    let south ← starts[1]?
    pure (label.y, north, south)
  let declared := picDoc "" ""
    ("\\node[text height=2ex, text depth=0.5ex] (a) at (0,0) {Label};\n" ++
     "\\draw (a.north) -- (0,2);\n\\draw (a.south) -- (0,-2);")
  t "a declared text box puts the node's anchors one inner sep beyond it, and names nothing"
    ((match anchors declared with
      | some (base, north, south) =>
        near (base - north) (2000 * ex / 1000 + sep) && near (south - base) (500 * ex / 1000 + sep)
      | none => false) && !picLoss declared)
  let below (word : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\begin{document}\n" ++
    "\\begin{tikzpicture}\\node at (0,0) {" ++ word ++ "};\\end{tikzpicture}\n\n" ++
    "Below.\n\\end{document}"
  let room (word : String) : Option Dim.Sp := do
    let (doc, _) := elabMeasured oneFace (below word)
    let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
    let a ← lineYOf c 0 word
    let b ← lineYOf c 0 "Below."
    pure (b - a)
  let deeper := wordDepth font size "vowelp" - wordDepth font size "vowel"
  t "the room a picture keeps below a label is the label's own depth, not the face's descent"
    (match room "vowel", room "vowelp" with
     | some a, some b => decide (0 < deeper) && near (b - a) deeper
     | _, _ => false)
  let svgHeight (word : String) : Option Dim.Sp := do
    let (doc, _) := elabMeasured oneFace (below word)
    viewBoxHeight (HtmlDoc.emit
      { labelMetric := Layout.labelMetric (Layout.Geom.ofPage doc.page) oneFace } doc).1
  t "the SVG's box grows by the same depth"
    (match svgHeight "vowel", svgHeight "vowelp" with
     | some a, some b => decide (b - a - deeper ≤ 70 ∧ deeper - (b - a) ≤ 70)
     | _, _ => false)


/-- **A node's `align=` sets its lines as the key says, and `every text node
part` is read** (tikz.code.tex: `align` chooses `left`, `flush left`,
`right`, `flush right`, `center` or `flush center`; `every text node part`
is the style the text part of every node runs). Lines broken with `\\` stand
flush left, flush right or centred within the widest line, and the block
stays where centring put it. The defect named both as dropped keys. Asserted
over the shipped lines. Invented content. -/
def pictureAlignChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let near (p q : Int) : Bool := decide (p - q ≤ 2 ∧ q - p ≤ 2)
  let node (pre opts : String) : String :=
    picDoc pre "" ("\\node" ++ opts ++ " at (0,0) {Longer first line\\\\ short};")
  let lines (src : String) : Option (Layout.LineOut × Layout.LineOut) := do
    let (doc, _) := elabMeasured oneFace src
    let page ← (layoutOf oneFace doc).pages[0]?
    let a ← page.lines.find? fun l => hasStr (lineText l) "Longer"
    let b ← page.lines.find? fun l => hasStr (lineText l) "short"
    pure (a, b)
  let centred := lines (node "" "")
  t "align=left sets the lines flush left, the widest where centring put it"
    ((match lines (node "" "[align=left]"), centred with
      | some (a, b), some (c, _) => near a.x b.x && near a.x c.x
      | _, _ => false) && !picLoss (node "" "[align=left]"))
  t "align=right sets them flush right"
    ((match lines (node "" "[align=right]"), centred with
      | some (a, b), some (c, _) => near (a.x + a.setWidth) (b.x + b.setWidth) && near a.x c.x
      | _, _ => false) && !picLoss (node "" "[align=right]"))
  let part (v : String) : String :=
    node s!"\\tikzset\{every text node part/.style=\{align={v}}}" ""
  t "every text node part reaches every node's text"
    ((match lines (part "flush left") with
      | some (a, b) => near a.x b.x
      | none => false) && !picLoss (part "flush left") && !picLoss (part "center"))
  let edge := picDoc "" "" "\\draw (0,0) -- node[align=left] {Longer first line\\\\ short} (6,0);"
  t "an edge label's lines stand flush as its align= says"
    ((match lines edge with
      | some (a, b) => near a.x b.x
      | none => false) && !picLoss edge)


/-- Consecutive segments meet end to start, and the last ends where the first
began: a closed chain. -/
def closedChain (ss : Array Ir.Pic.PathSeg) : Bool :=
  let ends : Ir.Pic.PathSeg → (Dim.Sp × Dim.Sp) × (Dim.Sp × Dim.Sp)
    | .line x1 y1 x2 y2 => ((x1, y1), (x2, y2))
    | .cubic x1 y1 _ _ _ _ x2 y2 => ((x1, y1), (x2, y2))
  let es := ss.map ends
  !es.isEmpty && (List.range es.size).all fun k =>
    match es[k]?, es[(k + 1) % es.size]? with
    | some a, some b => a.2 == b.1
    | _, _ => false

/-- **A drawn rectangle and a closed path are drawn** (pgf manual §14.4, the
rectangle operation; §14.2, `cycle`, which closes the path back to its
subpath's start). `\draw (a) rectangle (b)` strokes the box its corners span
as one closed outline; `-- cycle` draws the side back to the start, and the
PDF strokes the polygon as one subpath, so no corner is two caps. The defect
refused both: the rectangle named its statement outside the subset and
dropped it, and `cycle` failed as an unreadable endpoint (E0333), so a closed
shape shipped nothing. Asserted over the shipped page, the PDF's path
operators and the SVG. Invented content. -/
def pictureClosedPathChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let pageOf (src : String) : Option Layout.PageOut := (layoutOf oneFace (elabStr src).1).pages[0]?
  let paths (src : String) : Array Layout.PathOut := ((pageOf src).map (·.paths)).getD #[]
  let rect := picDoc "" "" "\\draw[thick] (0,0) rectangle (2,1);"
  t "a drawn rectangle strokes the box its corners span, and names nothing"
    ((match (paths rect).toList with
      | [q] => match q.path, q.stroke with
        | .rect _ _ w h, some st => w == Dim.mm 20 && h == Dim.mm 10 && st.width == Dim.pt 4 / 5
        | _, _ => false
      | _ => false) && !picLoss rect)
  let (rd, _) := elabStr rect
  t "the SVG strokes the rectangle as one closed outline"
    ((bodyAttrValues rd "stroke-width").size == 1 &&
      (rd.body.foldl (fun acc b => acc ++ attrValuesOne "height" #[] (HtmlDoc.blockNode {} b)) #[]).contains
        (Dim.mm 10).toPtString)
  let tri := picDoc "" "" "\\draw (0,0) -- (2,0) -- (1,1) -- cycle;"
  let triSegs : Array Ir.Pic.PathSeg := (paths tri).foldl (fun acc q => match q.path with
    | .segs ss => acc ++ ss
    | _ => acc) #[]
  t "-- cycle closes the path back to its start, and names nothing"
    (closedChain triSegs && !picLoss tri)
  let geom := Layout.Geom.ofPage (elabStr tri).1.page
  let moves := (paths tri).foldl (fun n q =>
    n + ((Pdf.pathSegs geom q.path).filter fun op => op matches .moveTo ..).size) 0
  t "the PDF strokes the closed polygon as one subpath"
    (moves == 1)


/-- **A drawn node with no minimum ships the outline pgf draws: its text box
plus two inner seps** (pgfmoduleshapes.code.tex: the `rectangle` shape's
`\northeast`, the `circle` shape's `\radius`), per axis the declared minimum
where that is larger, and an edge meets that outline. The defect shipped the
text bare and named the outline as outside the subset. Asserted over the
shipped paths' extents and boxes, against the same text with no inner sep, so
the claim is about the rule and not about one face's metrics. Invented
content. -/
def pictureOutlineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let paths (src : String) : Array (Dim.Sp × Dim.Sp) × Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
    let (doc, _) := elabMeasured oneFace src
    let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
    ((c[0]?.map (·.pathSpans)).getD #[], (c[0]?.map (·.pathBoxes)).getD #[])
  let node (opts : String) : String := picDoc "" "" s!"\\node[draw{opts}] at (0,0) \{Pad};"
  let bare := (paths (node ", inner sep=0pt")).1[0]?
  let padded := (paths (node ", inner sep=6pt")).1[0]?
  t "a drawn node's outline is its text plus an inner sep on every side"
    (match bare, padded with
     | some (w0, h0), some (w6, h6) =>
       decide (0 < w0 ∧ 0 < h0) && w6 - w0 == 2 * Dim.pt 6 && h6 - h0 == 2 * Dim.pt 6
     | _, _ => false)
  t "the drawn outline names nothing" (!picLoss (node "") && !picLoss (node ", inner sep=6pt"))
  -- One declared minimum governs its own axis; the text governs the other.
  let wide := (paths (node ", inner sep=0pt, minimum width=40mm")).1[0]?
  let tall := (paths (node ", inner sep=0pt, minimum height=20mm")).1[0]?
  let near (p q : Int) : Bool := decide (p - q ≤ 1 ∧ q - p ≤ 1)
  t "a declared minimum governs its axis and the text the other"
    (match bare, wide, tall with
     | some (w0, h0), some (ww, wh), some (tw, th) =>
       near ww (Dim.mm 40) && wh == h0 && tw == w0 && near th (Dim.mm 20)
     | _, _, _ => false)
  -- pgf's circle: the text box's half-diagonal, one inner sep out each way.
  let circ := (paths (picDoc "" "" "\\node[circle, draw, inner sep=0pt] at (0,0) {Pad};")).1[0]?
  t "a drawn circle's radius reaches the text box's corners"
    (match bare, circ with
     | some (w0, h0), some (d, _) =>
       let r := d / 2
       decide (r * r ≤ (w0 / 2) * (w0 / 2) + (h0 / 2) * (h0 / 2) + 2 * r + 2 ∧
         (w0 / 2) * (w0 / 2) + (h0 / 2) * (h0 / 2) ≤ (r + 1) * (r + 1) + 2 * r + 2)
     | _, _ => false)
  -- An edge between two drawn nodes starts and ends on their outlines.
  let (_, boxes) := paths (picDoc "" ""
    ("\\node[draw] (a) at (0,0) {Aa};\\node[draw] (b) at (3,0) {Bb};\n" ++
     "\\draw (a) -- (b);"))
  t "an edge meets the outlines it joins"
    (match boxes[0]?, boxes[1]?, boxes[2]? with
     | some (ax, _, aw, _), some (bx, _, _, _), some (ex, _, ew, _) =>
       decide (ex - (ax + aw) ≤ 2 ∧ (ax + aw) - ex ≤ 2 ∧
         (ex + ew) - bx ≤ 2 ∧ bx - (ex + ew) ≤ 2)
     | _, _, _ => false)
