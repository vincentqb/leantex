module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.TexBodies

/-- The shared `\keywords` definition arxiv.sty, preprint.sty and curvenote.sty make, invented
names aside. -/
private def keywordsDef : String :=
  "\\def\\zzkeywordname{{\\bfseries \\emph{Keywords}}}%\n" ++
  "\\def\\zzkeywords#1{\\par\\addvspace\\medskipamount{\\rightskip=0pt plus1cm\n" ++
  "\\def\\and{\\ifhmode\\unskip\\nobreak\\fi\\ $\\cdot$\n" ++
  "}\\noindent\\zzkeywordname\\enspace\\ignorespaces#1\\par}}\n"

/-- An article with preamble `pre` and body `body`. -/
private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

/-- `\addvspace` takes the larger of its skip and the one before and `\ignorespaces` sets nothing, so
the shared `\keywords` definition sets its line. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (src : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabStr src
    (censusOf #[] (layoutOf oneFace doc), ds)
  let lead := "Lead paragraph."
  let (plain, _) := page (article "" (lead ++ "\n\nTail paragraph."))
  for arg in ["\\medskipamount", "{\\medskipamount}", "{6pt plus 2pt minus 2pt}"] do
    let (spaced, ds) := page (article "" (lead ++ "\n\\par\\addvspace" ++ arg ++ "\nTail paragraph."))
    let drop := (lineYOf spaced 0 "Tail").bind fun a => (lineYOf plain 0 "Tail").map (a - ·)
    t s!"addvspace {arg}: a medium skip after a paragraph ({drop.map (·.toSp)})"
      (ds.all (·.code != "W0301") && drop.any fun d => (d - Dim.pt 6).abs ≤ Dim.Length.ofSp 64)
  let (once, _) := page (article "" (lead ++ "\n\\par\\addvspace{1cm}\nTail paragraph."))
  let (twice, _) := page (article "" (lead ++ "\n\\par\\addvspace{1cm}\\addvspace{1cm}\nTail paragraph."))
  let (larger, _) := page (article "" (lead ++ "\n\\par\\addvspace{2cm}\\addvspace{1cm}\nTail paragraph."))
  let (two, _) := page (article "" (lead ++ "\n\\par\\addvspace{2cm}\nTail paragraph."))
  t "addvspace: a second takes the larger skip, never the sum, as latex.ltx's does"
    ((lineYOf once 0 "Tail").isSome && lineYOf once 0 "Tail" == lineYOf twice 0 "Tail" &&
      (lineYOf two 0 "Tail").isSome && lineYOf larger 0 "Tail" == lineYOf two 0 "Tail")
  let (c, ds) := page (article keywordsDef "Lead.\n\\zzkeywords{placeholders, flows}\nTail.")
  t s!"keywords: the shared definition sets its line, no command unread ({ds.filter (·.severity != .note) |>.map (·.message)})"
    (pageHas c 0 "Keywords" && pageHas c 0 "placeholders, flows" && ds.all (·.severity != .error) &&
      ds.all (·.code != "W0301"))
  let width (body : String) : Option Dim.Length :=
    let (c, _) := page (article keywordsDef body)
    (c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "alpha").map (·.width)
  -- the local `\and` sets a space, a centred dot and a space between the words, as lualatex does
  t "keywords: its local \\and sets a dot between words, wider than a space"
    ((width "\\zzkeywords{alpha \\and beta}").any fun w => (width "\\zzkeywords{alpha beta}").any (w > ·))

end Tests.TexBodies
