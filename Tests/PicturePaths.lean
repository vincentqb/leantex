import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

mutual

/-- Every `d` of an emitted `<path>`: the SVG half of what a picture's edges
draw, read off the typed tree. -/
def pathDsOne (acc : Array String) : Html.Node → Array String
  | .elem tag attrs kids =>
    let acc := if tag == "path" then
      match attrs.find? (·.1 == "d") with
      | some (_, d) => acc.push d
      | none => acc
      else acc
    pathDsList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def pathDsList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => pathDsList (pathDsOne acc k) rest

end

/-- **A bent edge is drawn bent** (pgf's To-Path library: `bend left=α` is
`out=α, in=180−α, relative`, tikzlibrarytopaths.code.tex). Asserted over the
shipped page's paths (`Layout.Out`, y down) and the SVG the same IR emits,
through elaboration and layout. The defect drew every bend as its chord, so
two one-way relations between a pair of nodes collapsed onto one overdrawn
segment; each claim below fails on that behaviour. Invented labels. -/
def pictureBendChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (body : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\begin{document}\n" ++
    "\\begin{tikzpicture}\n" ++
    "\\node[draw, minimum width=2cm, minimum height=1cm] (a) at (0,0) {A};\n" ++
    "\\node[draw, minimum width=2cm, minimum height=1cm] (b) at (6,0) {B};\n" ++
    body ++ "\n\\end{tikzpicture}\n\\end{document}"
  let edges (body : String) : Array Ir.Pic.PathSeg :=
    ((layoutOf oneFace (elabStr (src body)).1).pages[0]?.map fun p =>
      p.paths.foldl (fun acc q => match q.path with
        | .segs ss => acc ++ ss
        | _ => acc) #[]).getD #[]
  let cubics (body : String) : Array (Int × Int × Int × Int × Int × Int × Int × Int) :=
    (edges body).filterMap fun s => match s with
      | .cubic x1 y1 c1x c1y c2x c2y x2 y2 => some (x1, y1, c1x, c1y, c2x, c2y, x2, y2)
      | .line .. => none
  let near (p q : Int) : Bool := decide (p - q ≤ 2 ∧ q - p ≤ 2)
  let left := cubics "\\draw (a) to[bend left=40] (b);"
  t "a bent edge ships one cubic and no chord"
    (left.size == 1 && (edges "\\draw (a) to[bend left=40] (b);").size == 1)
  -- On the page, y grows downward: travelling east, the left side is up.
  t "bend left and its reverse bulge to opposite sides"
    (match (cubics "\\draw (a) to[bend left=40] (b);\n\\draw (b) to[bend left=40] (a);").toList with
     | [(_, y1, _, c1y, _, c2y, _, _), (_, z1, _, d1y, _, d2y, _, _)] =>
       decide (c1y < y1 ∧ c2y < y1 ∧ d1y > z1 ∧ d2y > z1)
     | _ => false)
  -- Offsets only: the two pictures' boxes differ, so their ink stands at
  -- different heights on the page.
  t "bend right is bend left mirrored in the chord"
    (match left.toList, (cubics "\\draw (a) to[bend right=40] (b);").toList with
     | [(x1, y1, c1x, c1y, c2x, c2y, x2, y2)], [(u1, v1, d1x, d1y, d2x, d2y, u2, v2)] =>
       near (c1x - x1) (d1x - u1) && near (c2x - x2) (d2x - u2) && near (x2 - x1) (u2 - u1) &&
         near (y1 - c1y) (d1y - v1) && near (y2 - c2y) (d2y - v2) && near (y2 - y1) (v2 - v1)
     | _, _ => false)
  let dflt := cubics "\\draw (a) to[bend left] (b);"
  t "a bend without a value reads the library's thirty degrees"
    (dflt.size == 1 && dflt == cubics "\\draw (a) to[bend left=30] (b);")
  t "a statement's To-Path keys reach its to"
    (dflt.size == 1 && cubics "\\draw[bend left=30] (a) to (b);" == dflt)
  -- `looseness` scales both control distances (line 64).
  t "looseness scales the control distance"
    (match dflt.toList, (cubics "\\draw (a) to[bend left=30, looseness=2] (b);").toList with
     | [(x1, y1, c1x, c1y, _, _, x2, y2)], [(u1, v1, d1x, d1y, _, _, u2, v2)] =>
       x2 - x1 == u2 - u1 && y2 - y1 == v2 - v1 &&
         near (d1x - u1) (2 * (c1x - x1)) && near (d1y - v1) (2 * (c1y - y1))
     | _, _ => false)
  -- A curve one tangent switched on keeps the library's other
  -- (`\def\tikz@to@in{135}`): it was drawn as a chord and named a loss.
  let one := "\\draw (0,0) to[out=90] (4,0);"
  t "a to with one tangent keeps the library's other, and names nothing"
    ((cubics one).size == 1 && cubics one == cubics "\\draw (0,0) to[out=90, in=135] (4,0);" &&
      !((elabStr (src one)).2.any (·.code == "W0334")))
  t "no bend key is named as a loss"
    (!((elabStr (src "\\draw (a) to[bend left=40] (b);\n\\path (b) edge[bend right] (a);")).2.any
      (·.code == "W0334")))
  -- The SVG draws the same cubic: a `C` command in the edge's path.
  let (doc, _) := elabStr (src "\\draw (a) to[bend left=40] (b);")
  t "the SVG draws the bent edge as a cubic"
    ((doc.body.foldl (fun acc b => pathDsOne acc (HtmlDoc.blockNode {} b)) #[]).any
      fun d => hasStr d "C")


/-- **A picture inside a paragraph is named where it stands.** LaTeX sets a
`tikzpicture` as a box of its line; the engine sets it as a block, so a
paragraph with text beside a picture breaks at it. The defect was silent:
the page lost the sentence's continuity and no diagnostic said so. The
divergence is a keyed `W0334` (`picture:inline`), asserted over the
structured diagnostic, and the blocks the page ships are the ones it names.
A picture standing alone, one under a declaration, and one beside a box on
its own line (a row) name nothing. Invented content. -/
def pictureInlineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let mark := "\\begin{tikzpicture}\\fill (0,0) rectangle (0.3,0.3);\\end{tikzpicture}"
  let doc (body : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\begin{document}\n" ++ body ++
      "\n\\end{document}"
  let named (body : String) : Bool :=
    (elabStr (doc body)).2.any fun d => d.code == "W0334" && d.subject == some "picture:inline"
  let mid := "Some running words " ++ mark ++ " and more running words."
  t "a picture inside a paragraph names its block placement"
    (named mid && named ("Words before it " ++ mark) && named (mark ++ " words after it."))
  -- What the name says is what the page ships: the paragraph's text stands
  -- on either side of the picture's fill, as two lines.
  let c := censusOfSrc oneFace (doc mid)
  t "the named placement is what ships: text above the picture, text below it"
    (match lineYOf c 0 "Some running words", lineYOf c 0 "and more running words",
        (c[0]?.bind (·.fillRects[0]?)) with
     | some a, some b, some (_, fy, _, fh) => decide (a < fy ∧ fy + fh < b)
     | _, _, _ => false)
  t "a picture alone, or under a declaration, names nothing"
    (!named mark && !named ("\\centering\n" ++ mark) && !named ("\\vspace{1em}\n" ++ mark) &&
      !named ("Before.\n\n" ++ mark ++ "\n\nAfter."))
  t "a box and a picture on their own line are a row, not a sentence"
    (!named ("\\parbox[t]{3cm}{Lab}\n" ++ mark))
