module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- An article holding one picture: `pre` in the preamble, `opts` its bracket, `body` its
statements. -/
def picDoc (pre opts body : String) : String :=
  "\\documentclass{article}\\pictures{ tool = none }" ++ pre ++ "\\begin{document}\n" ++
  "\\begin{tikzpicture}" ++ opts ++ "\n" ++ body ++ "\n\\end{tikzpicture}\n\\end{document}"

/-- The stroke widths the first page ships, in paint order. -/
def shippedWidths (oneFace : Font.FontSet) (src : String) : Array Dim.Sp :=
  ((layoutOf oneFace (elabStr src).1).pages[0]?.map fun p =>
    (pageDraws p).filterMap fun (_, _, st) => st.map (·.width)).getD #[]

/-- Does the source name any picture loss? -/
def picLoss (src : String) : Bool :=
  (elabStr src).2.any fun d => d.code == "W0334" || d.code == "E0333"

/-- Every value a document's body HTML declares for `key`. -/
def bodyAttrValues (doc : Ir.Doc) (key : String) : Array String :=
  doc.body.foldl (fun acc b => acc ++ attrValuesOf (fun _ => true) key (HtmlDoc.blockNode {} b)) #[]

/-- A declared line width is the width pgf strokes, at every level a picture reads a key. -/
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
  t "a width the picture or every path sets reaches the path"
    ([pic, every].all fun s => shippedWidths oneFace s == #[Dim.pt 3 / 5] && !picLoss s)
  -- `\pgfpicture` resets the width to 0.4 pt, so a `\tikzset` outside every picture sets none.
  t "a tikzset line outside every picture sets no width: the picture starts at 0.4 pt"
    (shippedWidths oneFace set == #[Ir.Pic.thinWidth] && !picLoss set)
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

/-- A node's `font=` sets its label in the fonts it names, at the size the document's own ladder
gives each switch. -/
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
  t "font=\\small sets a node at the document's \\small size, naming nothing"
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


/-- The depth of the TeX box a word set in `font` at `size` makes. -/
def wordDepth (font : Font.Font) (size : Dim.Sp) (word : String) : Dim.Sp :=
  word.toList.foldl (fun d c =>
    match (font.gid c).bind font.yExtent with
    | some (lo, _) => max d (-lo * size / (font.unitsPerEm : Int))
    | none => d) 0

/-- The height of the TeX box a word set in `font` at `size` makes. -/
def wordHeight (font : Font.Font) (size : Dim.Sp) (word : String) : Dim.Sp :=
  word.toList.foldl (fun d c =>
    match (font.gid c).bind font.yExtent with
    | some (_, hi) => max d (hi * size / (font.unitsPerEm : Int))
    | none => d) 0

/-- The height of an SVG's viewBox in the emitted page, in sp. -/
def viewBoxHeight (page : String) : Option Dim.Sp := do
  let rest ← (page.splitOn "viewBox=\"0 0 ")[1]?
  let v ← (rest.splitOn "\"")[0]?
  let h ← (v.splitOn " ")[1]?
  let (m, sc) ← Decl.parseDecimal h
  pure (m * Dim.pt 1 / sc)

/-- A node's box is its text box plus inner sep, as TikZ's: a declared text box exactly, an
undeclared one the glyphs' own. -/
def pictureTextBoxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let font := oneFace.body
  let near (p q : Int) : Bool := decide (p - q ≤ 3 ∧ q - p ≤ 3)
  let size := (Layout.Geom.ofPage (elabStr (picDoc "" "" "")).1.page).fontSize
  let ex := font.xHeight * size / (font.unitsPerEm : Int)
  let sep := Picture.innerSep size
  let anchors (src : String) : Option (Dim.Sp × Dim.Sp × Dim.Sp) := do
    let (doc, _) := elabMeasured oneFace src
    let page ← (layoutOf oneFace doc).pages[0]?
    let label ← page.lines.find? fun l => hasStr (lineText l) "Label"
    let starts := (pageDraws page).filterMap fun (g, _, st) => match g, st with
      | .path subs, some _ => subs[0]?.map (·.start.2)
      | _, _ => none
    let north ← starts[0]?
    let south ← starts[1]?
    pure (label.y, north, south)
  let declared := picDoc "" ""
    ("\\node[text height=2ex, text depth=0.5ex] (a) at (0,0) {Label};\n" ++
     "\\draw (a.north) -- (0,2);\n\\draw (a.south) -- (0,-2);")
  t "a declared text box sets the anchors one inner sep out, naming nothing"
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
  t "a picture keeps the label's own depth below it, not the face's descent"
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


/-- A node's `align=` sets its lines as the key says, and `every text node part` is read. -/
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


/-- Consecutive segments meet end to start and the last ends where the first began. -/
def closedChain (ss : Array Ir.Pic.PathSeg) : Bool :=
  let ends : Ir.Pic.PathSeg → (Dim.Sp × Dim.Sp) × (Dim.Sp × Dim.Sp)
    | .line x1 y1 x2 y2 => ((x1, y1), (x2, y2))
    | .cubic x1 y1 _ _ _ _ x2 y2 => ((x1, y1), (x2, y2))
  let es := ss.map ends
  !es.isEmpty && (List.range es.size).all fun k =>
    match es[k]?, es[(k + 1) % es.size]? with
    | some a, some b => a.2 == b.1
    | _, _ => false

/-- A drawn rectangle and a closed path are drawn, each as one closed subpath. -/
def pictureClosedPathChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let pageOf (src : String) : Option Layout.PageOut := (layoutOf oneFace (elabStr src).1).pages[0]?
  let draws (src : String) := ((pageOf src).map pageDraws).getD #[]
  let rect := picDoc "" "" "\\draw[thick] (0,0) rectangle (2,1);"
  t "a drawn rectangle strokes the box its corners span, and names nothing"
    ((match (draws rect).toList with
      | [(.rect _ _ w h, _, some st)] => w == Dim.mm 20 && h == Dim.mm 10 && st.width == Dim.pt 4 / 5
      | _ => false) && !picLoss rect)
  let (rd, _) := elabStr rect
  t "the SVG strokes the rectangle as one closed outline"
    ((bodyAttrValues rd "stroke-width").size == 1 &&
      (rd.body.foldl (fun acc b => acc ++ attrValuesOf (fun _ => true) "height" (HtmlDoc.blockNode {} b)) #[]).contains
        (Dim.mm 10).toPtString)
  let tri := picDoc "" "" "\\draw (0,0) -- (2,0) -- (1,1) -- cycle;"
  let triSegs : Array Ir.Pic.PathSeg := ((pageOf tri).map edgeSegs).getD #[]
  t "-- cycle closes the path back to its start, and names nothing"
    (closedChain triSegs && !picLoss tri)
  let geom := Layout.Geom.ofPage (elabStr tri).1.page
  let moves := ((pageOf tri).map fun p => p.inks.foldl (fun n k =>
    n + ((Pdf.inkPaint geom Pdf.figureNames (fun _ => none) k).foldl (fun n op => match op with
      | .paint _ (some _) _ segs => n + (segs.filter fun op => op matches .moveTo ..).size
      | _ => n) 0)) 0).getD 0
  t "the PDF strokes the closed polygon as one subpath"
    (moves == 1)


/-- A drawn node with no minimum ships pgf's outline, its text box plus two inner seps, and an edge
meets it. -/
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
  -- An edge between two drawn nodes starts and ends one outer sep (half the line width) past their outlines.
  let (_, boxes) := paths (picDoc "" ""
    ("\\node[draw] (a) at (0,0) {Aa};\\node[draw] (b) at (3,0) {Bb};\n" ++
     "\\draw (a) -- (b);"))
  let o := Ir.Pic.thinWidth / 2
  t "an edge meets the outlines it joins"
    (match boxes[0]?, boxes[1]?, boxes[2]? with
     | some (ax, _, aw, _), some (bx, _, _, _), some (ex, _, ew, _) =>
       decide (ex - (ax + aw + o) ≤ 2 ∧ (ax + aw + o) - ex ≤ 2 ∧
         (ex + ew) - (bx - o) ≤ 2 ∧ (bx - o) - (ex + ew) ≤ 2)
     | _, _, _ => false)


/-- A drawn node stands its outline on the node's position, and its text inside it. -/
def pictureNodeCentreChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let near (p q : Int) : Bool := decide (p - q ≤ 2 ∧ q - p ≤ 2)
  let pageOf (body : String) : Option Layout.PageOut :=
    (layoutOf oneFace (elabMeasured oneFace (picDoc "" "" body)).1).pages[0]?
  let frames (p : Layout.PageOut) : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
    (pageDraws p).filterMap fun (g, _, _) => match g with
      | .rect x y w h => some (x, y, w, h)
      | _ => none
  let mid (b : Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) : Dim.Sp := b.2.1 + b.2.2.2 / 2
  let level (bs : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp)) : Bool :=
    match bs[0]? with
    | some b0 => bs.size ≥ 2 && bs.all fun b => near (mid b) (mid b0)
    | none => false
  let pair := pageOf ("\\node[draw] (a) at (0,0) {A};\\node[draw] (b) at (3,0) {g};\n" ++
    "\\draw (a) -- (b);")
  t "drawn nodes at one height share a centre line, whatever their letters"
    ((pair.map fun p => level (frames p)).getD false)
  t "the edge between them is level"
    ((pair.map fun p => (pageDraws p).any fun (g, _, st) => match g, st with
      | .path subs, some _ =>
        let ss := subpathSegs subs
        !ss.isEmpty && ss.all fun s => match s with
          | .line _ y1 _ y2 => y1 == y2
          | .cubic .. => false
      | _, _ => false).getD false)
  let chain := pageOf ("\\node[draw] (c) at (0,0) {A};\\node[draw, right=of c] (d) {g};\n" ++
    "\\node[draw, right=of d] (e) {A};")
  t "a right=of chain of drawn nodes keeps one centre line"
    ((chain.map fun p => (frames p).size == 3 && level (frames p)).getD false)
  let size := (Layout.Geom.ofPage (elabStr (picDoc "" "" "")).1.page).fontSize
  let sep := Picture.innerSep size
  let font := oneFace.body
  let holds (p : Layout.PageOut) (k : Nat) (word : String) : Bool :=
    match p.lines.find? (fun l => lineText l == word), (frames p)[k]? with
    | some l, some (_, y, _, h) =>
      near (l.y - wordHeight font size word - y) sep &&
        near (y + h - (l.y + wordDepth font size word)) sep
    | _, _ => false
  t "each drawn outline holds its letters one inner sep in, above and below"
    ((pair.map fun p => holds p 0 "A" && holds p 1 "g").getD false &&
      decide (0 < wordDepth font size "g"))


/-- A drawn node's anchors stand half a line width beyond its border (pgf's `outer sep`). -/
def pictureOuterSepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let near (p q : Int) : Bool := decide (p - q ≤ 2 ∧ q - p ≤ 2)
  let pageOf (body : String) : Option Layout.PageOut :=
    (layoutOf oneFace (elabMeasured oneFace (picDoc "" "" body)).1).pages[0]?
  let frames (p : Layout.PageOut) : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
    (pageDraws p).filterMap fun (g, _, _) => match g with
      | .rect x y w h => some (x, y, w, h)
      | _ => none
  let edgeXs (p : Layout.PageOut) : Option (Dim.Sp × Dim.Sp) :=
    (pageDraws p).findSome? fun (g, _, st) => match g, st with
      | .path subs, some _ =>
        let ss := subpathSegs subs
        match ss[0]?, ss[ss.size - 1]? with
        | some (Ir.Pic.PathSeg.line x1 _ _ _), some (Ir.Pic.PathSeg.line _ _ x2 _) =>
          some (min x1 x2, max x1 x2)
        | _, _ => none
      | _, _ => none
  let gaps (opts : String) : Option (Dim.Sp × Dim.Sp) := do
    let p ← pageOf ("\\node[draw" ++ opts ++ "] (a) at (0,0) {A};\\node[draw" ++ opts ++
      "] (b) at (3,0) {B};\n\\draw (a) -- (b);")
    let (ax, _, aw, _) ← (frames p)[0]?
    let (bx, _, _, _) ← (frames p)[1]?
    let (x1, x2) ← edgeXs p
    pure (x1 - (ax + aw), bx - x2)
  let half := Ir.Pic.thinWidth / 2
  t "an edge between drawn nodes stops half a line width outside each"
    (match gaps "" with
     | some (g1, g2) => near g1 half && near g2 half
     | none => false)
  t "a node's outer sep is half its own line width"
    (match gaps ", very thick" with
     | some (g1, g2) => near g1 (Dim.pt 3 / 5) && near g2 (Dim.pt 3 / 5)
     | none => false)
  t "outer sep=0pt puts the anchors on the outline, and names nothing"
    ((match gaps ", outer sep=0pt" with
      | some (g1, g2) => near g1 0 && near g2 0
      | none => false) && !picLoss (picDoc "" "" "\\node[draw, outer sep=0pt] at (0,0) {A};"))
  let below := pageOf "\\node[draw] (c) at (0,0) {A};\\node[draw, below=of c] (f) {x};"
  t "below=of parts two outlines by the node distance plus two outer seps"
    (match below.map frames with
     | some fs => match fs[0]?, fs[1]? with
       | some (_, cy, _, ch), some (_, fy, _, _) => near (fy - (cy + ch)) (Dim.mm 10 + 2 * half)
       | _, _ => false
     | none => false)


/-- An attempt that never finished is no answer: it is neither remembered nor withdrawn, and stands
as W0382 with the placeholder. -/
def boundaryUnfinishedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let id := Ir.picHash "\\draw[rounded corners] (0,0) rectangle (1,1);"
  let src := Ir.picSrcPrefix ++ id
  let run (o : PicCache.Outcome) : Boundary.Withdrawal :=
    Boundary.withdraw #[id] ((Boundary.undrawnOf "lualatex" o none src).toArray.map (src, ·))
  let stands (w : Boundary.Withdrawal) : Bool :=
    w.ids.isEmpty && w.said.isEmpty && w.standing.size == 1 &&
      w.standing.all fun (s, d) => s == src && d.code == "W0382" && d.subject == some src
  let endings : List (String × PicCache.Ran × PicCache.Log) :=
    [("exits 3 and leaves no log", .exited 3, .absent),
     ("overruns its budget", .overran 120, .says "! Emergency stop."),
     ("never starts", .unstarted "no such file", .absent)]
  for (what, ran, log) in endings do
    t s!"a tool that {what} withdraws nothing: the picture's W0382 stands"
      (stands (run (PicCache.outcome ran false log)))
  let answered := run (PicCache.outcome (.exited 1) false (.says "! Package pgf Error: invented."))
  t "the tool's own refusal withdraws a picture the subset draws in part"
    (answered.ids == #[id] && answered.standing.isEmpty &&
      answered.said == #[(id, some "! Package pgf Error: invented.")])
  let cold := DriverDiag.boundaryToolUnavailable "lualatex"
  t "no tool at all withdraws it too"
    ((Boundary.withdraw #[id] #[(src, .answered cold none)]).ids == #[id])


/-- The HTML face shows a drawing wherever the engine has one, the subset's where no converter
ran. -/
def pictureHtmlFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := dvDoc "" ("\\begin{tikzpicture}\\draw (0,0) parabola (3,1);\n" ++
    "\\node at (1.5,0.5) {Mark};\\end{tikzpicture}")
  let (toks, lds) := Lex.lex "t" src
  let (raws, pds) := Parse.parse "t" toks
  let p := Elab.prepare "t" raws
  let (routed, _, rs) := Elab.runPrepared "t" p (lds ++ pds)
  let img := ((Ir.imageRefs routed).find? (·.startsWith Ir.picSrcPrefix)).getD ""
  let elems (d : Ir.Doc) : Array (String × Array (String × String)) :=
    d.body.foldl (fun acc b =>
      elemAttrsOne (fun tag => tag == "img" || tag == "svg") acc (HtmlDoc.blockNode {} b)) #[]
  let keyImages (d : Ir.Doc) : Nat :=
    ((elems d).filter fun (tag, attrs) =>
      tag == "img" && attrs.any fun (k, v) => k == "src" && v.startsWith Ir.picSrcPrefix).size
  let drawings (d : Ir.Doc) : Nat := ((elems d).filter (·.1 == "svg")).size
  t "a partly drawn routed picture is a fallback, its HTML the request's image"
    (!rs.fallbacks.isEmpty && keyImages routed == 1 && drawings routed == 0)
  let ids := Boundary.htmlWithdraw rs.fallbacks #[img]
  t "an unconverted routed picture is withdrawn from the HTML face"
    (ids == rs.fallbacks)
  t "one whose SVG converted is not"
    (Boundary.htmlWithdraw rs.fallbacks #[]).isEmpty
  let (face, _, _) := Elab.runPrepared "t" p (lds ++ pds) (fun _ _ => {}) ids
  t "the HTML face then shows the subset's drawing, and no request key"
    (keyImages face == 0 && drawings face == 1)


/-- A picture inside a line of text stands in that line, or is named. -/
def pictureInlineLineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let mark := "\\tikz\\fill (0,0) rectangle (0.15,0.15);"
  let firstPass (src : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
    let (toks, lds) := Lex.lex "t" src
    let (raws, pds) := Parse.parse "t" toks
    Elab.runRawsSpanned "t" raws (lds ++ pds)
  let cell := dvDoc "" ("\\begin{tabular}{ll} Alpha & " ++ mark ++ " \\\\ Beta & words \\end{tabular}")
  let group := dvDoc "" ("\\textbf{Gamma " ++ mark ++ " delta.}")
  let cellImages (d : Ir.Doc) : Array String := d.body.foldl (fun acc b => match b with
    | .table _ _ _ rows _ _ => rows.foldl (fun acc r => r.foldl (fun acc c => c.foldl
        (fun acc i => match i with
          | .image s _ _ => if s.startsWith Ir.picSrcPrefix then acc.push s else acc
          | _ => acc) acc) acc) acc
    | _ => acc) #[]
  let noW0307 (ds : Array Diag) : Bool := ds.all (·.code != "W0307")
  let (cd, cds, _) := firstPass cell
  t "a picture in a table cell ships the boundary image there, no W0307"
    ((cellImages cd).size == 1 && (Ir.pictureRefs cd).size == 1 && noW0307 cds)
  let (gd, gds, _) := firstPass group
  let gc := censusOf (coveredColorsOf gd) (layoutOf oneFace gd)
  t "a picture in a group's text stands in its line, no W0307"
    ((Ir.pictureRefs gd).size == 1 && noW0307 gds &&
      gc.any fun p => p.lines.any fun l => hasStr l.text "Gamma" && hasStr l.text "delta")
  let named (ds : Array Diag) : Bool :=
    ds.any fun d => d.code == "W0334" &&
      (d.subject.map (·.startsWith "picture:inline:")).getD false
  let closed := cell.replace "\\begin{document}" "\\pictures{ tool = none }\\begin{document}"
  let (xd, xds) := elabStr closed
  t "with the boundary closed, a picture in a cell is named and not drawn"
    (named xds && noW0307 xds && (Ir.pictureRefs xd).isEmpty && (cellImages xd).size == 0)
  let (wd, wds) := elabStr cell
  t "a request in a cell is never withdrawn on its own: its image keeps the place"
    ((firstPass cell).2.2.fallbacks.isEmpty && (cellImages wd).size == 1 && !named wds &&
      noW0307 wds)
  let twin := (cd.pictureSrcs[0]?.map (·.1)).getD ""
  let (toks, lds) := Lex.lex "t" cell
  let (raws, pds) := Parse.parse "t" toks
  let (twd, tds, _) := Elab.runPrepared "t" (Elab.prepare "t" raws) (lds ++ pds) (fun _ _ => {})
    #[twin]
  t "a withdrawn picture in a cell is named, undrawn, under the driver's key"
    (!twin.isEmpty && named tds && noW0307 tds && (cellImages twd).size == 0 &&
      tds.any fun d => d.code == "W0334" && Boundary.inlineOf twin d)
  let cmd := dvDoc "\\newcommand{\\dotmark}{\\tikz\\fill (0,0) rectangle (0.15,0.15);}\n"
    "Gamma \\dotmark{} delta."
  t "a command whose body is a picture names the sentence it breaks"
    ((elabStr cmd).2.any fun d => d.code == "W0334" && d.subject == some "picture:inline")
