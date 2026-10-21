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

/-- A line's first glyph's x: its start past the glyphless runs and gaps before it. -/
private def firstInk (l : Layout.LineOut) : Dim.Length := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ => if glyphs.isEmpty then x := x + w else return x
    | .gap w _ => x := x + w
    | _ => return x
  return x

/-- Paragraphs after each kind of block, each named by its first word. -/
private def indentBody : String :=
  "Alpha opens the body.\n\nBravo follows a paragraph.\n\\section{Kilo heading}\n" ++
  "Charlie follows a heading.\n\n\\noindent Delta follows noindent.\n" ++
  "\\begin{itemize}\\item An item.\\end{itemize}\nEcho goes on past a list.\n" ++
  "\\begin{itemize}\\item An item.\\end{itemize}\n\nFoxtrot follows a blank line.\n" ++
  "\\begin{quote}A quote.\\end{quote}\nGolf goes on past a quote.\n" ++
  "\\begin{theorem}A claim.\\end{theorem}\nHotel follows a theorem.\n" ++
  "\\begin{proof}A proof.\\end{proof}\nIndia follows a proof.\n\n\\medskip\n" ++
  "\\noindent Juliet follows a skip.\n\n\\paragraph{Kilo head} Kilo runs in.\n\n" ++
  "Lima holds {\\noindent a group} and goes on.\n\n\\begin{theorem}\\noindent Mike claims.\\end{theorem}"

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
  -- Presets and the class words that alias them.
  let presetOf (src : String) : Ir.DocClass := (elabStr src).1.docClass
  let doc0 (cls : String) : String := s!"\\documentclass{cls}\n\\begin\{document}\nx\n\\end\{document}\n"
  t "flow class: preset=cv and the cv, resume and webpage words name their presets"
    (presetOf (doc0 "[preset=cv]{ltflow}") == .flow .cv && presetOf (doc0 "{cv}") == .flow .cv &&
      presetOf (doc0 "{resume}") == .flow .resume && presetOf (doc0 "{webpage}") == .flow .cvweb &&
      presetOf (doc0 "[preset=cookbook]{ltflow}") == .flow .cookbook)
  let (_, badDs) := elabStr (doc0 "[preset=nope]{ltflow}")
  t "flow class: an unknown preset is named and the article stands"
    (presetOf (doc0 "[preset=nope]{ltflow}") == .flow .article &&
      badDs.any fun d => d.code == "W0104" && hasStr d.message "preset=nope")
  t "flow class: the resume keeps the old class's one-page, in-area and legibility contracts"
    ((Ir.DocClass.flow .resume).record.pagesBound == some (.lit .eq 1) &&
      (Ir.DocClass.flow .resume).record.inkInArea.isSome &&
      (Ir.DocClass.flow .resume).record.xHeightFloor.isSome)
  let (webDoc, _) := elabStr (doc0 "{webpage}")
  t "flow class: the web CV keeps the old class's build intent and twin"
    (webDoc.output.formats.contains "html" && webDoc.output.formats.contains "md" &&
      webDoc.output.md == some "llms.txt")
  let (cvDoc, _) := elabStr ("\\documentclass[preset=cv]{ltflow}\n\\begin{document}\n" ++
    "\\section{Work}\n\\entry{2020}{Keeper}{Kept an orchard.}\n\\end{document}\n")
  let numbered := cvDoc.body.any fun b => match b with
    | .section _ _ (some _) _ => true
    | _ => false
  t "flow class: a CV's headings stand unnumbered" (!numbered)
  t "flow class: tex/ltdefaults.tex is generated from the records it mirrors"
    ((← IO.FS.readFile "tex/ltdefaults.tex") == Ir.ltDefaultsTex)
  t "flow class: tex/ltflowsource.tex is generated from the source leantex splices"
    ((← IO.FS.readFile "tex/ltflowsource.tex") == Ir.ltFlowSourceTex)

/-- The flow class's first-line indents (`Ir.indentParagraphs`), against lualatex's. -/
def firstIndentChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  -- lualatex, `{ltflow}`: size11.clo's 17pt, none past a heading, `\noindent` or `\@endpe`.
  let indentsOf (src : String) : Dim.Length × List (String × Dim.Length) :=
    let (d, out) := outOf fonts src
    let lines := out.pages.flatMap (·.lines)
    (Ir.sizeFileParindent d.page.fontSize,
      ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf", "Hotel", "India", "Juliet",
        "Kilo", "Lima"].filterMap
        fun w => (lines.find? fun l => (lineText l).trimAscii.toString.startsWith w).map fun l =>
          (w, firstInk l - d.page.hmargin))
  let near (a b : Dim.Length) : Bool := (a - b).abs ≤ Dim.pt 1
  let (w, got) := indentsOf ("\\documentclass{ltflow}\n\\begin{document}\n" ++ indentBody ++
    "\n\\end{document}\n")
  t s!"flow class: a paragraph opens on the size file's indent but past a heading, \\noindent or \\@endpe ({got.map fun (word, x) => (word, x.toPtString)})"
    (w == Dim.pt 17 && got.length == 12 && got.all fun (word, x) =>
      near x (if ["Alpha", "Bravo", "Foxtrot", "Hotel", "India", "Lima"].contains word then w else 0))
  let (_, flush) := indentsOf ("\\documentclass{ltflow}\n\\setlength{\\parindent}{0pt}\n" ++
    "\\begin{document}\n" ++ indentBody ++ "\n\\end{document}\n")
  t "flow class: a declared zero \\parindent sets every paragraph flush"
    (flush.length == 12 && flush.all fun (_, x) => near x 0)
  let (d, out) := outOf fonts ("\\documentclass{ltflow}\n\\begin{document}\n" ++ indentBody ++
    "\n\\end{document}\n")
  let lines := (out.pages.flatMap (·.lines)).map lineText
  t "flow class: a \\noindent TeX ignores neither warns nor breaks its line"
    (lines.any (fun l => hasStr l "Theorem" && hasStr l "Mike") &&
      lines.any (fun l => hasStr l "a group" && hasStr l "Lima") &&
      !(elabStr ("\\documentclass{ltflow}\n\\begin{document}\n" ++ indentBody ++
        "\n\\end{document}\n")).2.any (·.code == "W0301") && 0 < d.body.size)
  let (_, wide) := indentsOf ("\\documentclass{ltflow}\n\\setlength{\\parindent}{2em}\n" ++
    "\\begin{document}\n" ++ indentBody ++ "\n\\end{document}\n")
  t "flow class: the preamble's \\parindent replaces the size file's"
    (wide.any fun (word, x) => word == "Bravo" && near x (d.page.fontSize * 2))
  let (_, bodyDs) := elabStr ("\\documentclass{ltflow}\n\\begin{document}\n" ++
    "\\setlength{\\parindent}{0pt}\nAlpha.\n\\end{document}\n")
  t "flow class: a body \\parindent is named, the preamble's indent standing"
    (bodyDs.any fun d => hasStr d.message "parindent")
  let html := (HtmlDoc.emit {} (elabStr ("\\documentclass{ltflow}\n\\begin{document}\n" ++ indentBody ++
    "\n\\end{document}\n")).1).1
  t "flow class: the web page opens the same paragraphs on the indent"
    (hasStr html "</span>Bravo follows" && hasStr html "</span>India follows" &&
      !hasStr html "</span>Charlie follows" && !hasStr html "</span>Echo goes")
  let (_, article) := indentsOf ("\\documentclass{article}\n\\usepackage{amsthm}\n" ++
    "\\newtheorem{theorem}{Theorem}\n\\begin{document}\n" ++ indentBody ++ "\n\\end{document}\n")
  t "flow class: the article class's paragraphs stay flush, the indent the flow class's own"
    (article.length == 12 && article.all fun (_, x) => near x 0)

/-- `tex/ltdefaults.tex` written from `Ir.ltDefaultsTex` under `--update`. -/
def update : IO Unit := do
  IO.FS.writeFile "tex/ltdefaults.tex" Ir.ltDefaultsTex
  IO.FS.writeFile "tex/ltflowsource.tex" Ir.ltFlowSourceTex
  IO.println "updated tex/ltdefaults.tex and tex/ltflowsource.tex"

end Tests.FlowClass
