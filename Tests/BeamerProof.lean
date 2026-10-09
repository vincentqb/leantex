module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- Beamer's implicit AMS packages and its opt-out must use the ordinary
package loader. Recognition, headings, and QED marks are checked on shipped
PDF lines and the typed HTML tree, including named and nested proofs.

Beamer's `noamsthm` option disables both AMS packages; `notheorems` only
disables its automatic theorem declarations. The option is a key, even
when its unused value says `false` (beamerbasetheorems.sty and
beamer.cls, Beamer 3.77). Explicit package loads remain independent. -/
def beamerProofChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | t "beamer proof: fixture fonts load" false
  let cases : Array (String × String × String × String × Bool × Bool) := #[
    ("default", "{beamer}", "", "", true, true),
    ("class options", "[11pt,aspectratio=169]{beamer}", "", "", true, true),
    ("no automatic theorems", "[notheorems]{beamer}", "", "", true, true),
    ("disabled", "[noamsthm]{beamer}", "", "", false, false),
    ("spaced option", "[11pt, no amsthm, aspectratio=169]{beamer}", "", "", false, false),
    ("braced option", "[{noamsthm}]{beamer}", "", "", false, false),
    ("unused value", "[noamsthm=false]{beamer}", "", "", false, false),
    ("nested value", "[other={left,noamsthm,right}]{beamer}", "", "", true, true),
    ("early class pass", "{beamer}", "\\PassOptionsToClass{noamsthm}{beamer}", "", false, false),
    ("unrelated class pass", "{beamer}", "\\PassOptionsToClass{noamsthm}{article}", "", true, true),
    ("late class pass", "{beamer}", "", "\\PassOptionsToClass{noamsthm}{beamer}", true, true),
    ("explicit after opt-out", "[noamsthm]{beamer}", "", "\\usepackage{amsthm}", true, false),
    ("explicit", "{beamer}", "", "\\usepackage{amsthm}", true, true),
    ("bare article", "{article}", "", "", false, false),
    ("explicit article", "{article}", "", "\\usepackage{amsthm}", true, false)]
  let bodies : Array (String × String × String) := #[
    ("prose", "Proof", "\\begin{proof}Alder concludes.\\end{proof}"),
    ("named display", "Argument",
      "\\begin{proof}[Argument]Alder concludes.\\[1=1\\]\\end{proof}"),
    ("nested display", "Proof",
      "\\begin{block}{Claim}\\begin{proof}Alder concludes.\\[1=1\\]\\end{proof}\\end{block}")]
  let count (text needle : String) : Nat := (text.splitOn needle).length - 1
  for (name, cls, before, after, enabled, math) in cases do
    let queries := "\\IfPackageLoadedTF{amsthm}{Theoremloaded}{Theoremabsent} " ++
      "\\IfPackageLoadedTF{amsmath}{Mathloaded}{Mathabsent}"
    for (shape, heading, body) in bodies do
      if cls != "{article}" || shape != "nested display" then
        let body := body ++ queries
        let content := if hasStr cls "beamer" then
          "\\begin{frame}{Reasoning}" ++ body ++ "\\end{frame}" else body
        let source := before ++ "\n\\documentclass" ++ cls ++ "\n" ++ after ++
          "\n\\begin{document}\n" ++ content ++ "\n\\end{document}"
        let (doc, ds) := elabStr source
        let pdfText := String.join ((allLines (layoutOf fonts doc)).toList.map lineText)
        let (_, tree, _) := HtmlDoc.emitTree { fonts := some fonts } doc
        let htmlText := shownTextList "" tree.toList
        let label := "beamer proof " ++ name ++ " " ++ shape
        t (label ++ ": no error") (!ds.any (·.severity == .error))
        t (label ++ ": environment recognition")
          ((ds.any fun d => d.code == "W0302" && d.subject == some "env:proof") == !enabled)
        for (surface, text) in #[("PDF", pdfText), ("HTML", htmlText)] do
          t (label ++ " " ++ surface ++ ": source text once") (count text "Alder concludes." == 1)
          t (label ++ " " ++ surface ++ ": generated heading")
            (count text (heading ++ ".") == if enabled then 1 else 0)
          t (label ++ " " ++ surface ++ ": QED")
            (count text "□" == if enabled then 1 else 0)
          t (label ++ " " ++ surface ++ ": theorem package query")
            (hasStr text (if enabled then "Theoremloaded" else "Theoremabsent"))
          t (label ++ " " ++ surface ++ ": math package query")
            (hasStr text (if math then "Mathloaded" else "Mathabsent"))
  let pre := "\\documentclass{beamer}\\theoremstyle{definition}"
  let tail := "\\newtheorem{claim}{Claim}\\begin{document}\\begin{frame}{Reasoning}" ++
    "\\begin{claim}Uprightword.\\end{claim}\\end{frame}\\end{document}"
  let (once, onceDs) := elabStr (pre ++ tail)
  let (repeated, repeatedDs) := elabStr (pre ++ "\\usepackage{amsthm}" ++ tail)
  let (head, tree, _) := HtmlDoc.emitTree {} once
  let (repeatHead, repeatTree, _) := HtmlDoc.emitTree {} repeated
  t "beamer proof repeated implicit package: both builds recognised"
    (!(onceDs ++ repeatedDs).any (fun d => d.severity != .note))
  t "beamer proof repeated implicit package: theorem style survives in PDF"
    (reprStr (layoutOf fonts once).pages == reprStr (layoutOf fonts repeated).pages)
  t "beamer proof repeated implicit package: theorem style survives in HTML"
    (Html.document (once.info.language.getD "en") head tree ==
      Html.document (repeated.info.language.getD "en") repeatHead repeatTree)

end Tests
