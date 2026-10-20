module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ListGaps

/-- An article whose body is `body`. -/
private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def linesOf (oneFace : Font.FontSet) (src : String) : Array Layout.LineOut :=
  bodyLines (layoutOf oneFace (elabStr src).1)

/-- How far below the first line holding `a` the first line holding `b` stands. -/
private def gap (ls : Array Layout.LineOut) (a b : String) : Option Dim.Length :=
  match ls.find? (fun l => hasStr (lineText l) a), ls.find? (fun l => hasStr (lineText l) b) with
  | some x, some y => some (y.y - x.y)
  | _, _ => none

/-- A trivlist's paragraphs, a small quotation's and a small description's lines, and a float's
skips after its caption stand as lualatex sets them. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- lualatex: a trivlist's paragraph break 12pt, its next item 16pt, the itemsep 4pt on it.
  let triv := linesOf oneFace (article "" ("Alpha words.\n\\begin{trivlist}\n\\item Bravo words.\n\n" ++
    "Charlie words.\n\\item Delta words.\n\\item[Echo] Foxtrot words.\n\\end{trivlist}"))
  t s!"list gaps: a trivlist's paragraph break stands its parsep, its items an itemsep more: {triv.map lineText}"
    (gap triv "Bravo" "Charlie" == some (Dim.pt 12) && gap triv "Charlie" "Delta" == some (Dim.pt 16) &&
      gap triv "Delta" "Foxtrot" == some (Dim.pt 16))
  -- lualatex: under small, a quotation's paragraphs 13pt apart (11pt and small's 2pt parsep), a
  -- description's wrapped lines 11pt, its label in small.
  let words := String.intercalate " " (List.replicate 24 "golf")
  let small := linesOf oneFace (article "" ("Alpha words.\n{\\small\n\\begin{quote}\nHotel words.\n\n" ++
    "India words.\n\\end{quote}\n\\begin{description}\n\\item[Kilo] Lima " ++ words ++ " mike.\n" ++
    "\\end{description}\n\\par}"))
  let wrapped := small.filter fun l => hasStr (lineText l) "golf"
  t s!"list gaps: a small quotation's paragraphs stand small's parsep apart: {small.map lineText}"
    (gap small "Hotel" "India" == some (Dim.pt 13))
  t s!"list gaps: a small description's lines lead at small's baselineskip: {wrapped.map lineText}"
    (match wrapped.toList with
      | a :: b :: _ => b.y - a.y == Dim.pt 11
      | _ => false)
  -- lualatex: a 4pt vspace after the caption adds 4pt below the float, inside or outside a center
  -- or with no center, whatever stands between; one before the caption stays above it.
  let fig (inner : String) : Option Dim.Length :=
    gap (linesOf oneFace (article "" ("Alpha words.\n\n\\begin{figure}[h]\n" ++ inner ++
      "\n\\end{figure}\n\nBravo words."))) "Figure" "Bravo"
  let object := "\\rule{2cm}{1cm}\n"
  let caption := "\\caption{Charlie words.}\n"
  let centred (s : String) := "\\begin{center}\n" ++ s ++ "\\end{center}\n"
  let plus4 (a b : Option Dim.Length) : Bool := match a, b with
    | some a, some b => b - a == Dim.pt 4
    | _, _ => false
  t "list gaps: a skip after a center closing after its caption stands below the float"
    (plus4 (fig (centred (object ++ caption))) (fig (centred (object ++ caption) ++ "\\vspace{4pt}")))
  t "list gaps: a skip after the caption inside its center stands below the float"
    (plus4 (fig (centred (object ++ caption))) (fig (centred (object ++ caption ++ "\\vspace{4pt}\n"))))
  t "list gaps: a skip after the caption and its label stands below a centering float"
    (plus4 (fig ("\\centering\n" ++ object ++ caption ++ "\\label{fig:a}\n"))
      (fig ("\\centering\n" ++ object ++ caption ++ "\\label{fig:a}\n\\vspace{4pt}")))
  t "list gaps: a skip before the caption stands above it"
    (fig ("\\centering\n" ++ object ++ caption) == fig ("\\centering\n" ++ object ++ "\\vspace{4pt}\n" ++ caption))

end Tests.ListGaps
