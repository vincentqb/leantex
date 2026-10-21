module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.FlowClass

/-- An invented flow document: a heading, prose, a theorem and proof, a display and a list. -/
private def sample (body : String) (preamble : String := "") : String :=
  "\\documentclass{ltflow}\n" ++ preamble ++ "\\begin{document}\n\\section{Kilo heading}\n" ++
    body ++ "\n\\end{document}\n"

private def gridBody : String :=
  "Grid alpha opens the section with prose long enough to wrap across two or three lines of " ++
  "the measure, so that the interline rule sets each of them.\n\n" ++
  "\\begin{theorem}Grid bravo states a claim.\\end{theorem}\n" ++
  "\\begin{proof}Grid charlie proves it.\\end{proof}\n" ++
  "Grid delta leads into a display:\n\\begin{equation}\\sum_{i=1}^{n} i = \\frac{n(n+1)}{2}\\end{equation}\n" ++
  "Grid echo follows the display on the line after it.\n" ++
  "\\subsection{Lima list}\n\\begin{itemize}\\item Grid foxtrot.\\item Grid golf.\\end{itemize}\n" ++
  "Grid hotel closes the page."

/-- The page a flow class document sets: its measure settled against the face, then laid out. -/
private def outOf (fonts : Font.FontSet) (src : String) : Ir.Doc × Layout.Out :=
  let doc := (elabStr src).1
  (doc, layoutOf fonts doc)

/-- Whether a baseline stands on the grid, within a hundredth of a point. -/
private def onGrid (origin lead y : Dim.Length) : Bool :=
  Layout.gridOffset origin lead y == 0

/-- The leantex flow class (`tex/ltflow.cls`): its record, its type scale, its text block from a
measure in characters, its leading grid and its keeps. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (sample "Kilo words.")
  t "flow class: \\documentclass{ltflow} is the flow class's article preset"
    (doc.docClass == .flow .article)
  let warned := (ds.filter fun d => d.severity == .warning || d.severity == .error).map (·.code)
  t s!"flow class: the class loads with nothing warned ({warned})" warned.isEmpty
  t "flow class: its ladder is LaTeX's 1.2 step, \\small half a step below the body"
    (doc.page.sizes == some (Ir.gridLadder 1200) &&
      (Ir.gridLadder 1200).lookup "small" == some 913 &&
      (Ir.gridLadder 1200).lookup "Huge" == some 2488)
  let body := (doc.page.skipScale.lookup "normalsize").getD 0
  t "flow class: every size's line is a whole number of body leadings"
    (0 < body && doc.page.skipScale.all fun (_, row) => row % body == 0)
  -- The text block: the copy-fitting width of 66 characters to the nearest pica, whole leadings.
  let (settled, out) := outOf fonts (sample gridBody)
  let page := settled.page
  let lead := page.bodySkip.getD (Ir.leadingFor page.fontSize)
  let width := page.width - 2 * page.hmargin
  let height := page.height - page.vmargin - page.bottomMargin
  t s!"flow class: the measure is 66 characters of Latin Modern, to a pica ({width.toPtString})"
    (width == Ir.measureWidth page.fontSize 66 &&
      (width / Dim.pt 12) * Dim.pt 12 == width)
  t s!"flow class: the text block is a whole number of leadings ({height.toPtString})"
    (0 < height && (height / lead) * lead == height)
  t "flow class: the text block stands a third of the free height from the top"
    (let d := 2 * page.vmargin - page.bottomMargin; let tol := Dim.pt 1 / (100 : Int); -tol ≤ d && d ≤ tol)
  -- Every text line of the flow stands on the grid of the body leading from the first baseline.
  let origin := page.vmargin + lead
  let lines := (out.pages.flatMap (·.lines)).filter fun l => hasStr (lineText l) "Grid "
  let off := lines.filter fun l => !onGrid origin lead l.y
  t s!"flow class: every text line stands on the leading grid \
({off.toList.map fun l => (lineText l, (l.y - origin).toPtString)})"
    (8 ≤ lines.size && off.isEmpty)
  let (_, freeOut) := outOf fonts (sample gridBody "\\page{ grid = off }\n")
  let freeLines := (freeOut.pages.flatMap (·.lines)).filter fun l => hasStr (lineText l) "Grid "
  t "flow class: off the grid, the line after the display stands off it"
    (freeLines.any fun l => hasStr (lineText l) "Grid echo" && !onGrid origin lead l.y)
  -- Keeps: a two-line paragraph never splits, and no page ends on a heading.
  let paras := (List.range 40).map fun i =>
    s!"Para{i}start opens a paragraph written to fill exactly two lines of the measure with " ++
      s!"plain words, ending Para{i}end."
  let keepSrc := "\\documentclass{ltflow}\n\\begin{document}\n" ++
    "\n\n".intercalate (paras.zipIdx.map fun (p, i) =>
      if i % 7 == 3 then s!"\\section\{Heading {i}}\n" ++ p else p) ++ "\n\\end{document}\n"
  let (_, keepOut) := outOf fonts keepSrc
  let pageTexts := keepOut.pages.map fun p => p.lines.map lineText
  let split := (List.range 40).filter fun i =>
    pageTexts.any fun ts => (ts.any (hasStr · s!"Para{i}start")) != (ts.any (hasStr · s!"Para{i}end."))
  t s!"flow class: no paragraph leaves a widow or a club ({split})"
    (1 < keepOut.pages.size && split.isEmpty)
  let freeKeep := keepSrc.replace "\\begin{document}"
    "\\page{ clubpenalty = 100, widowpenalty = 100 }\n\\begin{document}"
  let (_, freeKeepOut) := outOf fonts freeKeep
  let freeTexts := freeKeepOut.pages.map fun p => p.lines.map lineText
  t "flow class: at LaTeX's own penalties some two-line paragraph splits, so the check can fail"
    ((List.range 40).any fun i =>
      freeTexts.any fun ts => (ts.any (hasStr · s!"Para{i}start")) != (ts.any (hasStr · s!"Para{i}end.")))
  let headingLast := keepOut.pages.filter fun p =>
    (p.lines.filter fun l => hasStr (lineText l) "Para" || hasStr (lineText l) "Heading").back?.map
      (fun l => hasStr (lineText l) "Heading") == some true
  t "flow class: no page ends on a heading" headingLast.isEmpty
  let (_, deckDs) := elabStr ("\\documentclass{beamer}\n\\page{ measure = 60 }\n" ++
    "\\begin{document}\n\\begin{frame}x\\end{frame}\n\\end{document}\n")
  t "flow class: a measure in characters on a deck is named, its page kept"
    (deckDs.any fun d => d.code == "W0104" && hasStr d.message "measure = 60")
  let (bottomDoc, _) := outOf fonts (sample "Kilo." "\\page{ bmargin = 2in }\n")
  t "flow class: a declared bottom margin stands"
    (bottomDoc.page.bottomMargin == Dim.inch 2)
  t "flow class: tex/ltdefaults.tex is generated from the records it mirrors"
    ((← IO.FS.readFile "tex/ltdefaults.tex") == Ir.ltDefaultsTex)

/-- `tex/ltdefaults.tex` written from `Ir.ltDefaultsTex` under `--update`. -/
def update : IO Unit := do
  IO.FS.writeFile "tex/ltdefaults.tex" Ir.ltDefaultsTex
  IO.println "updated tex/ltdefaults.tex"

end Tests.FlowClass
