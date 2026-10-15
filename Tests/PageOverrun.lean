module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.PageOverrun

private def deck (body : String) : String :=
  "\\documentclass{beamer}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def article (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

/-- The codes of a source's run through the overflow ladder, as the driver sets it. -/
private def codes (fonts : Font.FontSet) (src : String) : Array DiagCode :=
  ((fittedOf fonts (elabStr src).1).out.diags.map (·.kind)).filter fun c =>
    c == .W0358 || c == .W0384 || c == .W0400

/-- The index of the first page with a line reading `text`. -/
private def pageOf (out : Layout.Out) (text : String) : Option Nat :=
  out.pages.findIdx? fun p => p.lines.any fun l => (lineText l).trimAscii.toString == text

/-- The codes a source's run names, any code. -/
private def allCodes (fonts : Font.FontSet) (src : String) : Array DiagCode :=
  (fittedOf fonts (elabStr src).1).out.diags.map (·.kind)

/-- `n` rows of a tabular whose cells name their row, each cell's word distinct. -/
private def rows (n : Nat) (cols : List String) : String :=
  String.join ((List.range n).map fun i =>
    " & ".intercalate (cols.map fun c => s!"{c} {i}") ++ " \\\\\n")

/-- A box no break can help stands past its page's floor named, a frame's or a flow page's alike;
the ladder names what it moves, and what fits is named by nothing. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- A row that does not fit moves whole, each of its cells breaking with the row.
  let longTab := article ("\\begin{tabular}{lll}\n" ++ rows 120 ["Kilo", "Lima", "Mike"] ++
    "\\end{tabular}")
  let longOut := (fittedOf oneFace (elabStr longTab).1).out
  let split := (List.range 120).filter fun i =>
    let ps := ["Kilo", "Lima", "Mike"].map fun c => pageOf longOut s!"{c} {i}"
    ps.any (· != ps.head!) || ps.any (·.isNone)
  t "page overrun: a long tabular breaks between rows, every row's cells on one page, named by nothing"
    (split.isEmpty && 1 < longOut.pages.size && !(allCodes oneFace longTab).contains .W0358)
  let frameTab := deck ("\\begin{frame}[allowframebreaks]{Kilo}\n\\begin{tabular}{ll}\n" ++
    rows 40 ["Lima", "Mike"] ++ "\\end{tabular}\n\\end{frame}")
  let frameOut := (fittedOf oneFace (elabStr frameTab).1).out
  t "page overrun: a tabular in a frame with declared breaks breaks between rows, named by nothing"
    ((List.range 40).all (fun i => pageOf frameOut s!"Lima {i}" == pageOf frameOut s!"Mike {i}") &&
      !(allCodes oneFace frameTab).contains .W0358)
  let fillers := String.join ((List.range 53).map fun i => s!"Kilo filler {i}.\\\\\n")
  let lines (w : String) := String.join ((List.range 12).map fun i => s!"{w} line {i}.\n\n")
  let minis := article ("\\noindent " ++ fillers ++ "\n\\begin{minipage}[t]{0.45\\textwidth}\n" ++
    lines "Lima" ++ "\\end{minipage}\\hfill\\begin{minipage}[t]{0.45\\textwidth}\n" ++
    lines "Mike" ++ "\\end{minipage}")
  let miniOut := (fittedOf oneFace (elabStr minis).1).out
  t "page overrun: two minipages at a page's foot move together, named by nothing"
    (pageOf miniOut "Lima line 0." == pageOf miniOut "Mike line 0." &&
      !(allCodes oneFace minis).contains .W0358)
  t "page overrun: a float taller than the text block is named once"
    ((allCodes oneFace (article ("Kilo words.\n\\begin{figure}[h]\n\\rule{1cm}{30cm}\n" ++
      "\\caption{Lima caption.}\n\\end{figure}\nMike words."))).filter (· == .W0358) == #[.W0358])
  t "page overrun: an untitled frame whose rule overruns names the rule, not its note"
    ((allCodes oneFace (deck "\\begin{frame}\n\\rule{1cm}{12cm}\\footnote{Kilo note.}\n\\end{frame}")).filter
      (fun c => c == .W0358 || c == .W0372) == #[.W0358])
  t "page overrun: an untitled frame's overrunning rule on its second step names it once"
    (codes oneFace (deck ("\\begin{frame}\n\\only<1>{Mike words.}\n\\only<2>{\\rule{1cm}{12cm}}\n" ++
      "\\end{frame}")) == #[.W0358])
  t "page overrun: an untitled frame's rule taller than its page is named once (W0358)"
    (codes oneFace (deck "\\begin{frame}\n\\rule{1cm}{12cm}\n\\end{frame}") == #[.W0358])
  t "page overrun: a titled frame's rule taller than its page stands below the title, named once"
    (codes oneFace (deck "\\begin{frame}{Kilo}\n\\rule{1cm}{12cm}\n\\end{frame}") == #[.W0358])
  t "page overrun: a flow page's rule taller than the text block is named once (W0358)"
    (codes oneFace (article "Lima words.\n\n\\rule{1cm}{30cm}\n\nMike words.") == #[.W0358])
  t "page overrun: a rule opening the document taller than the text block is named once"
    (codes oneFace (article "\\rule{1cm}{30cm}\n\nMike words.") == #[.W0358])
  t "page overrun: a frame whose rule fits names nothing"
    ((codes oneFace (deck "\\begin{frame}\n\\rule{1cm}{3cm}\n\\end{frame}")).isEmpty)
  t "page overrun: a flow rule that fits names nothing"
    ((codes oneFace (article "Lima words.\n\n\\rule{1cm}{15cm}\n\nMike words.")).isEmpty)

end Tests.PageOverrun
