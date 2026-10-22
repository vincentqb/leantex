module

public import Tests.Support
public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FrameClass

/-- An invented talk: a title page, a titled frame of prose, a list, a display and a block, and a
frame with no title. -/
private def talk (preamble : String := "") (cls : String := "{ltframe}") : String :=
  "\\documentclass" ++ cls ++ "\n" ++ preamble ++
  "\\title{Invented Lattices}\n\\author{Pat Placeholder}\n\\date{20 October 2026}\n" ++
  "\\begin{document}\n\\begin{frame}\n\\titlepage\n\\end{frame}\n" ++
  "\\begin{frame}{Kilo heading}\nAlpha opens the frame with prose long enough to wrap across " ++
  "two lines of the stage measure.\n\\begin{itemize}\n\\item Bravo, the first item.\n" ++
  "\\item Charlie, the second.\n\\end{itemize}\nDelta leads into a display:\n" ++
  "\\[ a \\wedge (b \\vee c) \\ge (a \\wedge b) \\vee (a \\wedge c). \\]\n" ++
  "Echo follows the display.\n\\begin{block}{Foxtrot}\nGolf sits in a block.\n\\end{block}\n" ++
  "Hotel follows the block.\n\\end{frame}\n" ++
  "\\begin{frame}\nIndia opens a frame with no title.\n\\end{frame}\n\\end{document}\n"

/-- The first line on page `i` whose text starts with `w`, its baseline from the page's top. -/
private def lineY (out : Layout.Out) (i : Nat) (w : String) : Option Dim.Length :=
  (out.pages[i]?.bind fun p => p.lines.find? fun l =>
    (lineText l).trimAscii.toString.startsWith w).map (·.y)

/-- The leantex frame class (`tex/ltframe.cls`): its record, its stage and margins, and every line
of a frame on the stage's grid of sixteen lines, as lualatex sets the class. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (talk)
  t "frame class: \\documentclass{ltframe} is the frame class's talk preset"
    (doc.docClass == .frame .talk)
  let warned := (ds.filter fun d => d.severity == .warning || d.severity == .error).map (·.code)
  t s!"frame class: the class loads with nothing warned ({warned})" warned.isEmpty
  let page := doc.page
  let lead := page.height / (Ir.frameGridLines : Int)
  t "frame class: beamer's 16:9 stage, its body a leading over the scale's step, on the grid"
    (page.width == Dim.mm 160 && page.height == Dim.mm 90 &&
      page.fontSize == lead * (10 : Int) / (12 : Int) && page.grid == some true)
  t "frame class: two lines in from either side, half a line from the top"
    (page.hmargin == 2 * lead && page.vmargin == lead / (2 : Int))
  let out := layoutOf fonts doc
  let near (a b : Dim.Length) : Bool := (a - b).abs ≤ Dim.pt 1 / (100 : Int)
  let lineAt (k : Int) : Dim.Length := lead * k - lead / (2 : Int)
  let onGrid (y : Dim.Length) : Bool := Layout.gridOffset (lead / (2 : Int)) lead y == 0
  t "frame class: the title page's title stands on its seventh line, author and date below a gap"
    ((lineY out 0 "Invented").any (near · (lineAt 7)) && (lineY out 0 "Pat").any (near · (lineAt 9)) &&
      (lineY out 0 "20").any (near · (lineAt 10)))
  t "frame class: a frame's title stands on its second line, its body from the third"
    ((lineY out 1 "Kilo").any (near · (lineAt 2)) && (lineY out 1 "Alpha").any (near · (lineAt 3)))
  t "frame class: a frame with no title keeps the band, its body from the third line"
    ((lineY out 2 "India").any (near · (lineAt 3)))
  let lines := (out.pages[1]?.map (·.lines)).getD #[]
  let off := lines.filter fun l => !onGrid l.y && !hasStr (lineText l) "≥"
  t s!"frame class: every line but the display's stands on the grid \
({off.toList.map fun l => (lineText l, l.y.toPtString)})"
    (6 ≤ lines.size && off.isEmpty)
  -- lualatex: half a leading above and below the display, a blank line around the block.
  let gap (a b : String) : Option Dim.Length := do
    let ya ← lineY out 1 a
    let yb ← lineY out 1 b
    pure (yb - ya)
  t "frame class: the line after a display stands three leadings below the line before it"
    ((gap "Delta" "Echo").any (near · (3 * lead)))
  t "frame class: a block's bold title stands a blank line below the text, its body on the next"
    ((gap "Echo" "Foxtrot").any (near · (2 * lead)) && (gap "Foxtrot" "Golf").any (near · lead) &&
      (gap "Golf" "Hotel").any (near · (2 * lead)))
  -- The footline: the frame number at the right margin, half a leading above the paper's edge.
  let geom := Layout.Geom.ofPage page
  match readArtifact (driverPdf fonts geom doc out) with
  | .error e => t s!"frame class: the talk reads back: {e}" false
  | .ok pages =>
    let num := (pages[1]?.map (·.runs)).getD #[] |>.find? (·.text.trimAscii.toString == "2")
    t "frame class: the footline's frame number stands half a leading above the edge, at the margin"
      (num.any fun r => near r.y (lead / (2 : Int)) && near (r.x + r.w) (page.width - 2 * lead))
  let (four, _) := elabStr (talk (cls := "[aspect=43]{ltframe}"))
  t "frame class: aspect=43 sets beamer's 4:3 stage, its leading a sixteenth of it"
    (four.page.width == Dim.mm 128 && four.page.height == Dim.mm 96 &&
      four.page.hmargin == 2 * (Dim.mm 96 / (16 : Int)))
  let (sized, _) := elabStr (talk "\\setbeamersize{text margin left=1cm, text margin right=1cm}\n")
  t "frame class: equal beamer text margins are the page's side margins"
    (sized.page.hmargin == Dim.mm 10)
  let (lop, lopDs) := elabStr (talk "\\setbeamersize{text margin left=1cm, text margin right=2cm}\n")
  t "frame class: unequal text margins are named, the class's margins standing"
    (lop.page.hmargin == 2 * lead && lopDs.any fun d => hasStr d.message "text margin left")
  let (deck, _) := elabStr (talk (cls := "{beamer}"))
  t "frame class: beamer itself keeps its 4:3 stage, its margins and no grid"
    (deck.page.height == Dim.mm 96 && deck.page.hmargin == Ir.slidesHMargin && deck.page.grid.isNone)
  t "frame class: tex/ltframesource.tex is generated from the source leantex splices"
    ((← IO.FS.readFile "tex/ltframesource.tex") == Ir.ltFrameSourceTex)

/-- `tex/ltframesource.tex` written from `Ir.ltFrameSourceTex` under `--update`. -/
def update : IO Unit := do
  IO.FS.writeFile "tex/ltframesource.tex" Ir.ltFrameSourceTex
  IO.println "updated tex/ltframesource.tex"

end Tests.FrameClass
