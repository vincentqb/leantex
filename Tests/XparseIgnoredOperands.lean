import Tests.Support

open LeanTex.Core

namespace Tests

/-- An ignored provision has no executable operands: a deferred hook in its
replacement text or optional default cannot run, or receive its own note.
The existing meaning ships the PDF bytes and typed HTML of the document
without the provision, with exactly one discard accounting. Hooks outside
the ignored operands still execute. -/
def xparseIgnoredOperandsChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let article (pre body : String) :=
    "\\documentclass{article}\\usepackage{xparse}\\usepackage{etoolbox}" ++ pre ++
      "\\begin{document}" ++ body ++ "\\end{document}"
  let artifacts (source : String) :=
    let (doc, ds) := elabStr source
    let out := layoutOf fonts doc
    let (head, tree, hds) := HtmlDoc.emitTree {} doc
    (ds ++ hds, out, tree, Html.document "en" head tree,
      Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages doc.info)
  let bindings : Array (String × String × String × String) := #[
    ("LaTeX", "providedprobe", "\\newcommand{\\providedprobe}{Kept}",
      "\\providedprobe{} Tail"),
    ("xparse", "providedprobe", "\\NewDocumentCommand{\\providedprobe}{}{Kept}",
      "\\providedprobe{} Tail"),
    ("earlier provision", "providedprobe", "\\ProvideDocumentCommand{\\providedprobe}{}{Kept}",
      "\\providedprobe{} Tail"),
    ("builtin", "textbf", "", "\\textbf{Kept} Tail")]
  for (label, cmd, binding, call) in bindings do
    let (controlDs, controlOut, _, controlHtml, controlPdf) := artifacts (article binding call)
    t s!"ignored operands {label}: control has no loss"
      (controlDs.all (·.severity == .note))
    t s!"ignored operands {label}: control ships the kept meaning"
      ((bodyLines controlOut).any fun line => hasStr (lineText line) "Kept Tail")
    for definer in #["ProvideDocumentCommand", "providecommand"] do
      for hook in #["AtBeginDocument", "AtEndPreamble"] do
        for inDefault in #[false, true] do
          let operand := if inDefault then "default" else "body"
          let name := s!"ignored operands {label} {definer} {hook} {operand}"
          let effect := "\\" ++ hook ++ "{Leaked }"
          let operands := if definer == "ProvideDocumentCommand" then
              if inDefault then "{O{" ++ effect ++ "}}{Unused}"
              else "{}{" ++ effect ++ "}"
            else if inDefault then "[1][" ++ effect ++ "]{Unused}"
            else "{" ++ effect ++ "}"
          let provision := "\\" ++ definer ++ "{\\" ++ cmd ++ "}" ++ operands
          let (ds, out, tree, html, pdf) := artifacts (article (binding ++ provision) call)
          t (name ++ ": no loss") (ds.all (·.severity == .note))
          t (name ++ ": shipped PDF unchanged") (pdf == controlPdf)
          t (name ++ ": typed HTML unchanged") (html == controlHtml)
          t (name ++ ": layout ships the kept meaning")
            ((bodyLines out).any fun line => hasStr (lineText line) "Kept Tail")
          t (name ++ ": HTML ships the kept meaning")
            (hasStr (shownTextList "" tree.toList) "Kept Tail")
          let discardKey := some ("ctrl:nothing:" ++ definer ++ ":" ++ cmd)
          t (name ++ ": provision accounted once")
            ((ds.filter fun d => d.code == "N0100" && d.subject == discardKey).size == 1)
          let keptDs := ds.filter (·.subject != discardKey)
          t (name ++ ": ignored operands have no accounting")
            (keptDs.map (fun d => (d.code, d.subject, d.message)) ==
              controlDs.map (fun d => (d.code, d.subject, d.message)))
  for hook in #["AtBeginDocument", "AtEndPreamble"] do
    -- Preamble hooks may declare a command, but cannot ship body text there.
    let (pre, body) := if hook == "AtEndPreamble" then
        ("\\AtEndPreamble{\\newcommand{\\activeprobe}{Active}}", "\\activeprobe{} Tail")
      else ("\\AtBeginDocument{Active }", "Tail")
    let (ds, out, tree, html, pdf) := artifacts (article pre body)
    let (_, _, _, controlHtml, controlPdf) := artifacts (article "" "Active Tail")
    let (_, _, _, bareHtml, barePdf) := artifacts (article "" "Tail")
    t s!"ignored operands {hook}: active hook has no loss" (ds.all (·.severity == .note))
    t s!"ignored operands {hook}: active hook reaches PDF" (pdf == controlPdf && pdf != barePdf)
    t s!"ignored operands {hook}: active hook reaches HTML"
      (html == controlHtml && html != bareHtml)
    t s!"ignored operands {hook}: active layout witness"
      ((bodyLines out).any fun line => hasStr (lineText line) "Active Tail")
    t s!"ignored operands {hook}: active HTML witness"
      (hasStr (shownTextList "" tree.toList) "Active Tail")

end Tests
