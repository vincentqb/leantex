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

/-- Every `stroke-width` an emitted element declares, in tree order. -/
def strokeWidthsOne (acc : Array String) : Html.Node → Array String
  | .elem _ attrs kids =>
    let acc := match attrs.find? (·.1 == "stroke-width") with
      | some (_, w) => acc.push w
      | none => acc
    strokeWidthsList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def strokeWidthsList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => strokeWidthsList (strokeWidthsOne acc k) rest

end

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
    ((doc.body.foldl (fun acc b => strokeWidthsOne acc (HtmlDoc.blockNode {} b)) #[]).contains
      (Dim.pt 3 / 5).toPtString)
