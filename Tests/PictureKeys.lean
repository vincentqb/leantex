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
