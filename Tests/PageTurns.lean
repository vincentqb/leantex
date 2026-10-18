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
  t "page turns: a declared club and widow penalty of 10000 leaves no lone line on a tight page"
    (!(splits oneFace "\\clubpenalty=10000\n\\widowpenalty 10000\\relax\n" 0).any lone)
  let headed := splits oneFace "" 40 (head := true)
  t "page turns: a paragraph after a heading leaves the heading its first two lines"
    (headed.all fun s => match s.dropWhile (· == 0) with
      | 0 :: _ | 1 :: _ => false
      | _ => true)
  let src := turned "\\widowpenalty=10000\n" 0 400
  let (doc, ds) := elabStr src
  t "page turns: a preamble's \\widowpenalty assignment ships, read as the page's penalty"
    (ds.all (fun d => d.kind != .E0313 && d.kind != .W0301) && doc.page.penalties.widow == 10000 &&
      doc.page.penalties.club == 150)

end Tests.PageTurns
