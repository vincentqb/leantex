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

/-- A box no break can help stands past its page's floor named, a frame's or a flow page's alike;
the ladder names what it moves, and what fits is named by nothing. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  t "page overrun: an untitled frame's rule taller than its page is named once (W0358)"
    (codes oneFace (deck "\\begin{frame}\n\\rule{1cm}{12cm}\n\\end{frame}") == #[.W0358])
  t "page overrun: a titled frame continues (W0384) and its rule still overruns, named (W0358)"
    (let cs := codes oneFace (deck "\\begin{frame}{Kilo}\n\\rule{1cm}{12cm}\n\\end{frame}")
     cs.contains .W0384 && cs.contains .W0358 && cs.size == 2)
  t "page overrun: a flow page's rule taller than the text block is named once (W0358)"
    (codes oneFace (article "Lima words.\n\n\\rule{1cm}{30cm}\n\nMike words.") == #[.W0358])
  t "page overrun: a rule opening the document taller than the text block is named once"
    (codes oneFace (article "\\rule{1cm}{30cm}\n\nMike words.") == #[.W0358])
  t "page overrun: a frame whose rule fits names nothing"
    ((codes oneFace (deck "\\begin{frame}\n\\rule{1cm}{3cm}\n\\end{frame}")).isEmpty)
  t "page overrun: a flow rule that fits names nothing"
    ((codes oneFace (article "Lima words.\n\n\\rule{1cm}{15cm}\n\nMike words.")).isEmpty)

end Tests.PageOverrun
