module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.PageTurns

/-- An article whose page holds a rule of `high` points above a paragraph of nine lines or so,
`stretch` points of stretchable space between two rules above it, after the preamble `pre`. -/
private def turned (pre : String) (stretch high : Nat) (head : Bool := false) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n\\noindent\\rule{1pt}{100pt}\\par\n" ++
    s!"\\vspace\{0pt plus {stretch}pt}\n\\noindent\\rule\{1pt}\{{high}pt}\\par\n" ++
    (if head then "\\section{Lima}\n" else "") ++
    String.join (List.replicate 60 "Kilo ") ++ "Kilo.\n\nMike words.\n\\end{document}\n"

/-- An article whose page holds `n` one-line paragraphs, a rule of `high` points and a paragraph of
nine lines or so after `between`. -/
private def prose (n high : Nat) (between : String := "") : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++
    String.join ((List.range n).map fun i => s!"Zulu {i}.\n\n") ++
    s!"\\noindent\\rule\{1pt}\{{high}pt}\\par\n" ++ between ++
    String.join (List.replicate 60 "Kilo ") ++ "Kilo.\n\nMike words.\n\\end{document}\n"

/-- How many of the paragraph's lines each page holds. -/
private def split (fonts : Font.FontSet) (src : String) : List Nat :=
  ((fittedOf fonts (elabStr src).1).out.pages.map fun p =>
    (p.lines.filter fun l => ((lineText l).splitOn "Kilo").length > 1).size).toList

/-- The page splits a paragraph takes as the space above it grows, two points at a time. -/
private def splits (fonts : Font.FontSet) (pre : String) (stretch : Nat) (head : Bool := false) :
    List (List Nat) :=
  (List.range 150).map fun i => split fonts (turned pre stretch (300 + 2 * i) head)

/-- Whether a split leaves one line of a paragraph alone on a page while another page holds more. -/
private def lone (s : List Nat) : Bool :=
  let held := s.filter (0 < ·)
  1 < held.length && held.contains 1

/-- TeX's page builder ends a page at the least cost: badness and penalty (tex.web §1005); a club
or widow line costs 150 and stands where moving it costs more, as where the page has no stretch. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let tight := splits oneFace "" 0
  let loose := splits oneFace "" 40
  t "page turns: a page with no stretch keeps a club or widow line, as TeX does"
    (tight.any lone)
  -- The stretch stands on the first page, so only a paragraph turning from it may use it.
  let fromFirst := loose.filter fun s => 0 < s.headD 0 && 1 < (s.filter (0 < ·)).length
  t "page turns: a page with room to stretch keeps no club or widow line"
    (!fromFirst.isEmpty && !fromFirst.any lone)
  let forbidden := splits oneFace "\\clubpenalty=10000\n\\widowpenalty 10000\\relax\n" 0
  t "page turns: a declared club and widow penalty of 10000 leaves no lone line on a tight page"
    (forbidden.any (fun s => 1 < (s.filter (0 < ·)).length) && !forbidden.any lone)
  let headed := splits oneFace "" 40 (head := true)
  t "page turns: a paragraph after a heading leaves the heading its first two lines"
    (headed.all fun s => match s.dropWhile (· == 0) with
      | 0 :: _ | 1 :: _ => false
      | _ => true)
  -- An equation between a heading and its paragraph sets a paragraph, which frees the one after it.
  let shown := (List.range 120).map fun i => split oneFace ("\\documentclass{article}\n" ++
    s!"\\begin\{document}\n\\section\{Lima}\n\\vspace\{{360 + 3 * i}pt plus 40pt}\n" ++
    "\\begin{equation} x = y \\end{equation}\n\n" ++ String.join (List.replicate 60 "Kilo ") ++
    "Kilo.\n\nMike words.\n\\end{document}\n")
  t "page turns: an equation after a heading frees the paragraph after it to keep no club"
    (shown.any (fun s => 1 < (s.filter (0 < ·)).length) && !shown.any lone)
  -- A table between a heading and its paragraph frees the paragraph, as its cell's paragraph does.
  let meets (between : String) : List (Option Nat × Option Nat) := (List.range 100).map fun i =>
    let out := (fittedOf oneFace (elabStr (prose 20 (4 * i) ("\\section{Lima}\n" ++ between))).1).out
    let pageOf (w : String) := out.pages.findIdx? fun p => p.lines.any fun l => hasStr (lineText l) w
    (pageOf "Lima", pageOf "Kilo")
  t "page turns: a table after a heading frees the paragraph after it to move whole"
    ((meets "\\begin{center}\n\\begin{tabular}{l}Oscar\\end{tabular}\n\\end{center}\n").any
      fun (h, k) => h.isSome && k.isSome && h != k)
  let src := turned "\\widowpenalty=10000\n" 0 400
  let (doc, ds) := elabStr src
  t "page turns: a preamble's \\widowpenalty assignment ships, read as the page's penalty"
    (ds.all (fun d => d.kind != .E0313 && d.kind != .W0301) && doc.page.penalties.widow == 10000 &&
      doc.page.penalties.club == 150)
  -- TeX's `\parskip` stretches a point, so a page turns between paragraphs before inside one.
  let peers (cls : String) : String :=
    s!"\\documentclass\{{cls}}\n\\begin\{document}\n" ++
      String.join ((List.range 80).map fun i =>
        s!"Zulu {i} " ++ String.join (List.replicate 14 "Kilo ") ++ "Kilo.\n\n") ++ "\\end{document}\n"
  for cls in ["article", "report"] do
    let pages := (fittedOf oneFace (elabStr (peers cls)).1).out.pages
    t s!"page turns: a {cls}'s pages of short paragraphs turn between them"
      (1 < pages.size && pages.all fun p => p.lines[0]?.all fun l => hasStr (lineText l) "Zulu")
  -- TeX's `\predisplaypenalty` keeps a display on the page of the line before it.
  let shownAt (pre : String) (high : Nat) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n\\noindent\\rule{1pt}{100pt}\\par\n" ++
      s!"\\noindent\\rule\{1pt}\{{high}pt}\\par\n" ++ String.join (List.replicate 30 "Kilo ") ++
      "Yankee\n\\[ x = y \\]\nMike " ++ String.join (List.replicate 30 "Kilo ") ++ "Kilo.\n\\end{document}\n"
  -- Each sweep: whether it turned a page, opened one with the display, or with the line before it.
  let sweep (pre : String) : List (Bool × Bool × Bool) := (List.range 75).map fun i =>
    let pages := (fittedOf oneFace (elabStr (shownAt pre (300 + 4 * i))).1).out.pages
    let opening (w : String) := (pages.extract 1 pages.size).any fun p =>
      p.lines[0]?.any fun l => hasStr (lineText l) w && !hasStr (lineText l) "Mike"
    (decide (1 < pages.size), opening "=", opening "Yankee")
  let shown := sweep ""
  t "page turns: no page opens with a display its paragraph's lines stand before"
    (shown.any (·.1) && !shown.any (·.2.1))
  -- The line before a display costs `\displaywidowpenalty` (50) to leave alone on a page.
  let widowed := sweep "\\displaywidowpenalty=10000\n"
  t "page turns: the line before a display opens a page at 50, never at a declared 10000"
    (shown.any (·.2.2) && widowed.any (·.1) && !widowed.any (·.2.2) && !widowed.any (·.2.1))
  let (pdoc, pds) := elabStr ("\\documentclass{article}\n\\displaywidowpenalty=10000\n" ++
    "\\interlinepenalty=200\n\\predisplaypenalty=0\n\\begin{document}\nKilo.\n\\end{document}\n")
  t "page turns: a preamble's display and interline penalties ship as the page's"
    (pds.all (fun d => d.kind != .E0313 && d.kind != .W0301) &&
      pdoc.page.penalties.displayWidow == 10000 && pdoc.page.penalties.interline == 200 &&
      pdoc.page.penalties.predisplay == 0)

end Tests.PageTurns
