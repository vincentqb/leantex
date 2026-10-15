module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.DeclaredLadder

/-- `\Large` and `\tiny` declared as a venue declares them, absolute sizes in points. -/
private def ladder (large tiny : String) : String :=
  "\\makeatletter\n" ++
    s!"\\renewcommand\{\\Large}\{\\@setfontsize\\Large\{{large}}\{19.8}}\n" ++
    s!"\\renewcommand\{\\tiny}\{\\@setfontsize\\tiny\{{tiny}}\{7.92}}\n" ++ "\\makeatother\n"

private def sizesOf (out : Layout.Out) (text : String) : Array Dim.Sp :=
  (out.pages.flatMap (·.lines)).filterMap fun l =>
    if hasStr (lineText l) text then some l.size else none

/-- The sizes of the runs whose glyphs spell `word`. -/
private def runSizesOf (out : Layout.Out) (word : String) : Array Dim.Sp :=
  (out.pages.flatMap (·.lines)).flatMap fun l => l.segs.filterMap fun s =>
    match s with
    | .run _ _ _ _ glyphs size _ _ _ _ _ =>
      if hasStr (String.ofList (glyphs.toList.map (·.2.1))) word then some size else none
    | _ => none

/-- The headings, plain frame titles, standout and footline a document's class sets, and its inline
size switches, resolve on the ladder it declares, in the pages, the stylesheet and the contrast judge. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let article := "\\documentclass{article}\n" ++ ladder "16" "5" ++ "\\begin{document}\n" ++
    "\\section{Kilo heading}\nLima words. {\\Large Mike words.}\n\\end{document}\n"
  let (adoc, _) := elabStr article
  let aout := layoutOf oneFace adoc
  t "declared ladder: a section heading sets at the declared \\Large, 16 pt"
    (sizesOf aout "Kilo heading" == #[Dim.pt 16])
  t "declared ladder: an inline \\Large sets at the declared size too"
    (!(runSizesOf aout "Mike").isEmpty && (runSizesOf aout "Mike").all (· == Dim.pt 16))
  let ahtml := (HtmlDoc.emit {} adoc).1
  t "declared ladder: the HTML h2 rule carries the declared \\Large"
    (hasStr ahtml "h2 { font-size: 1.600rem; }" && !hasStr ahtml "h2 { font-size: 1.440rem; }")
  let twelve := "\\documentclass[12pt]{article}\n" ++ ladder "18" "6" ++
    "\\begin{document}\n\\section{Kilo heading}\nLima words.\n\\end{document}\n"
  t "declared ladder: a declared size is absolute over a 12 pt body"
    (sizesOf (layoutOf oneFace (elabStr twelve).1) "Kilo heading" == #[Dim.pt 18])
  let deck (theme : String) := "\\documentclass{beamer}\n" ++ theme ++ ladder "16.5" "6.6" ++
    "\\begin{document}\n\\begin{frame}{Kilo title}\nLima words.\n\\end{frame}\n" ++
    "\\begin{frame}[standout]\nStandout words.\n\\end{frame}\n\\end{document}\n"
  let (ddoc, _) := elabStr (deck "")
  let dout := layoutOf oneFace ddoc
  let large : Dim.Sp := Dim.pt 33 / 2
  t "declared ladder: a plain frame title sets at the declared \\Large, 16.5 pt"
    (sizesOf dout "Kilo title" == #[large])
  t "declared ladder: a standout frame sets at the declared \\Large"
    (sizesOf dout "Standout words" == #[large])
  let dhtml := (HtmlDoc.emit {} ddoc).1
  t "declared ladder: the deck's frame title rule carries the declared \\Large"
    (hasStr dhtml "section.slide > header h2 { font-size: 1.500rem; }" &&
      !hasStr dhtml "section.slide > header h2 { font-size: 1.440rem; }")
  let (mdoc, _) := elabStr (deck "\\usetheme{moloch}\n")
  let mout := layoutOf oneFace mdoc
  let foot := (mout.pages.flatMap (·.lines)).filterMap fun l =>
    if l.furniture && lineText l == "1" then some l.size else none
  t "declared ladder: the footline sets at the declared \\tiny, 6.6 pt"
    (!foot.isEmpty && foot.all (· == Dim.pt 33 / 5))
  t "declared ladder: the footline sets at Ir.footlineSize, the one size the judge also reads"
    (foot.all (· == Ir.footlineSize mdoc.page.scale mdoc.page.fontSize))
  -- A heading the declared ladder sets below large-scale text owes the ordinary text threshold.
  let judged (decl : String) : Array Diag :=
    Contrast.docDiags (elabStr ("\\documentclass{article}\n\\usepackage{xcolor}\n" ++ decl ++
      "\\definecolor{mid}{HTML}{808080}\n\\begin{document}\n" ++
      "\\section{\\textcolor{mid}{Kilo heading}}\nLima words.\n\\end{document}\n")).1
  let small := "\\makeatletter\n\\renewcommand{\\Large}{\\@setfontsize\\Large{12}{14}}\n\\makeatother\n"
  let script := "\\documentclass{article}\n\\makeatletter\n" ++
    "\\renewcommand{\\scriptsize}{\\@setfontsize\\scriptsize{5}{6}}\n\\makeatother\n" ++
    "\\begin{document}\nKilo words.\\footnote{Lima note.}\n\\end{document}\n"
  let marks := ((layoutOf oneFace (elabStr script).1).pages.flatMap (·.lines)).flatMap fun l =>
    if hasStr (lineText l) "Kilo words" then l.segs.filterMap fun s => match s with
      | .run _ _ _ _ glyphs size _ _ _ _ _ =>
        if String.ofList (glyphs.toList.map (·.2.1)) == "1" then some size else none
      | _ => none
    else #[]
  t "declared ladder: a note mark keeps the script size a declared \\scriptsize does not move"
    (marks == #[Ir.noteMarkSize (Dim.pt 10)])
  t "declared ladder: the contrast judge reads a heading at the size the declared ladder sets it"
    ((judged small).any (·.code == "W0315") && !(judged "").any (·.code == "W0315"))

end Tests.DeclaredLadder
