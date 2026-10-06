import Tests.Artifact

open LeanTex.Core

namespace Tests.Regression

/-- Both artifacts from one complete, invented document and one font set. -/
structure Artifact where
  doc : Ir.Doc
  fonts : Font.FontSet
  geom : Layout.Geom
  out : Layout.Out
  head : Array Html.Node
  body : Array Html.Node
  pdf : ByteArray
  diags : Array Diag

/-- Each document names the artifact facts that distinguish its template.
Expected warnings are checked in both directions; errors are never accepted. -/
structure Case where
  path : String
  warnings : Array DiagCode := #[]
  check : IO.Ref (List String) → Artifact → IO Unit

/-- Compile local inputs through the same expansion used by document tests,
then emit each backend once. Fonts come from the checked-in fixture set. -/
def compile (fonts : Font.FontSet) (path : String) : IO Artifact := do
  let (doc, ds) ← elabInputSrc path (← IO.FS.readFile path)
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fonts doc geom
  let cfg : HtmlDoc.Config :=
    { fonts := some fonts, labelMetric := Layout.labelMetric geom fonts }
  let (head, body, htmlDs) := HtmlDoc.emitTree cfg doc
  return {
    doc, fonts, geom, out, head, body
    pdf := driverPdf fonts geom doc out
    diags := ds ++ out.diags ++ htmlDs }

/-- Check publication validity before the document-specific visible facts.
Resource closure is checked over the actual tree, including embedded fonts. -/
def runCase (ref : IO.Ref (List String)) (fonts : Font.FontSet) (c : Case) : IO Unit := do
  let a ← compile fonts c.path
  for d in a.diags do
    check ref s!"{c.path}: unexpected {d.code}: {d.message}"
      (d.severity != .error &&
        (d.severity != .warning || c.warnings.contains d.kind))
  for code in c.warnings do
    check ref s!"{c.path}: expected warning {code.code} no longer fires"
      (a.diags.any fun d => d.kind == code && d.severity == .warning)
  check ref s!"{c.path}: ships PDF pages" (!a.out.pages.isEmpty)
  check ref s!"{c.path}: PDF cross-references resolve" (checkXref a.pdf).isOk
  match readArtifact a.pdf with
  | .error e => check ref s!"{c.path}: PDF reader: {e}" false
  | .ok pages =>
    check ref s!"{c.path}: emitted PDF page census" (pages.size == a.out.pages.size)
  let cfg : HtmlDoc.Config :=
    { fonts := some fonts, labelMetric := Layout.labelMetric a.geom fonts }
  match HtmlResource.close (HtmlDoc.resources cfg) #[] HtmlDoc.deckScript
      (a.doc.info.language.getD "en") a.head a.body with
  | .error e => check ref s!"{c.path}: HTML is self-contained: {e}" false
  | .ok _ => pure ()
  c.check ref a

end Tests.Regression
