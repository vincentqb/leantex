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

/-- The fixture environment keeps text variants, mathematical coverage,
and a real fixed-pitch code face independent of host font discovery. -/
def fontSet : IO (Option Font.FontSet) := do
  let some fs ← serifFacesSet | return none
  let path := testFonts ++ "/SourceCodePro-Regular.otf"
  unless ← System.FilePath.pathExists path do return none
  let .ok mono := Font.parse (← IO.FS.readBinFile path) | return none
  return some { fs with
    fonts := fs.fonts.push mono
    index := (fs.index.filter (fun e => e.1.1 != 2)).push
      ((2, 400, false), fs.fonts.size) }

private def htmlConfig (fonts : Font.FontSet) (geom : Layout.Geom) : HtmlDoc.Config := {
  fonts := some fonts
  labelMetric := Layout.labelMetric geom fonts
  cancelMetric := fun measures ss st spec body value =>
    Layout.cancelMetric geom fonts ss st spec body value (some measures)
  mathEm := fun measures ss st => Layout.mathEm geom fonts ss st (some measures)
  mathTextEm := fun measures ss st => Layout.mathTextEm geom fonts ss st (some measures) }

/-- Expand local inputs once, then elaborate with measured labels and emit
both backends using the driver's font callbacks. Fonts are bundled, so the
test cannot silently substitute a host-dependent or unmeasured layout. -/
def compile (fonts : Font.FontSet) (path : String) : IO Artifact := do
  let (tokens, lexDs) := Lex.lex path (← IO.FS.readFile path)
  let (raws, parseDs) := Parse.parse path tokens
  let (executed, inputDs, _) ← LeanTex.Cli.Input.expandInputs path raws
  let earlier := lexDs ++ parseDs ++ inputDs
  let prepared := Elab.prepareExecuted path executed
  let geom := Layout.Geom.ofPage (Elab.runPrepared path prepared earlier).1.page
  let (doc, ds, _) := Elab.runPrepared path prepared earlier (Layout.labelMetric geom fonts)
  let (doc, alphabetDs) := Ir.resolveMathAlphas fonts.mathAlphabets "math face" doc
  let out := layoutOf fonts doc geom
  let (head, body, htmlDs) := HtmlDoc.emitTree (htmlConfig fonts geom) doc
  return {
    doc, fonts, geom, out, head, body
    pdf := driverPdf fonts geom doc out
    diags := ds ++ alphabetDs ++ out.diags ++ htmlDs }

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
  match HtmlResource.close (HtmlDoc.resources (htmlConfig fonts a.geom)) #[] HtmlDoc.deckScript
      (a.doc.info.language.getD "en") a.head a.body with
  | .error e => check ref s!"{c.path}: HTML is self-contained: {e}" false
  | .ok _ => pure ()
  c.check ref a

end Tests.Regression
