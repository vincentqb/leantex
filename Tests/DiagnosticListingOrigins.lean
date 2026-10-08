module

public import Tests.Artifact
public import LeanTex.Cli.Render

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

private def listingSourceExact (file source : String) (d : Diag) : Bool := Id.run do
  let some span := d.span | return false
  let some trigger := d.trigger | return false
  let some line := (source.splitOn "\n")[span.pos.line - 1]? | return false
  return span.file == file && span.pos.line > 0 && span.pos.col > 0 &&
    !trigger.isEmpty &&
    (String.ofList (line.toList.drop (span.pos.col - 1))).startsWith trigger

/-- Listing diagnostics carry source coordinates, independently of tab
expansion, generated line numbers, line endings and lexical paint. Both the
human and machine record identify text actually present at those coordinates;
adding that evidence leaves shipped layout and PDF/HTML bytes unchanged. -/
def diagnosticListingOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok font => pure font
    | .error err => throw (IO.userError s!"listing origins: {name}: {err}")
  let sans ← load "OpenSans-Regular.ttf"
  let code ← load "SourceCodePro-Regular.otf"
  let fs : Font.FontSet := {
    fonts := #[sans, code]
    index := ([0, 1, 2].flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 0),
       ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray
    fallback := #[('∀', 1)] }
  let file := "synthetic/listing-origins.tex"
  let cases : Array (String × String × String × Bool) := #[
    ("plain", "\\begin{verbatim}", "prefix ∀ value", false),
    ("highlighted", "\\begin{minted}{lean4}", "let α\tresult := ∀ value", true),
    ("numbered", "\\begin{minted}[tabsize=8,linenos]{lean4}",
      "let α\tresult := ∀ value", true)]
  for (name, opening, line, highlighted) in cases do
    for newline in ["\n", "\r\n"] do
      let ending := if highlighted then "\\end{minted}" else "\\end{verbatim}"
      let source := String.intercalate newline [
        "\\documentclass{article}", "\\begin{document}", opening, line,
        ending, "\\end{document}"]
      let prepared := Elab.prepare file (Parse.parse file (Lex.lex file source).1).1
      let (doc, ds, _) := Elab.runPrepared file prepared
      let geom := Layout.Geom.ofPage doc.page
      let out := Layout.run geom fs none doc
      let losses := (out.diags.filter (·.kind == .W0009)).map
        prepared.sourceTriggers.attribute
      let label := name ++ (if newline == "\n" then "/LF" else "/CRLF")
      t s!"listing origins {label}: fallback names exact source text"
        (ds.all (·.severity != .error) && losses.size == 1 &&
          losses.all (listingSourceExact file source))
      if highlighted then
        let col := line.toList.takeWhile (· != '∀') |>.length |>.succ
        t s!"listing origins {label}: tab and Unicode count authored scalars"
          (losses.all fun d => d.trigger == some "∀" &&
            d.span.any fun span => span.pos.line == 4 && span.pos.col == col)
      t s!"listing origins {label}: rendered record includes its evidence"
        (losses.all fun d => d.span.any fun span => d.trigger.any fun trigger =>
          hasStr (Render.human false d)
            s!"{file}:{span.pos.line}:{span.pos.col} - {trigger}" &&
          hasStr (Render.porcelainDiag d) "\"trigger\":")
      let bare := Ir.eraseLocations doc
      let bareOut := Layout.run geom fs none bare
      t s!"listing origins {label}: provenance preserves PDF paint and bytes"
        (reprStr out.pages == reprStr bareOut.pages &&
          driverPdf fs geom doc out == driverPdf fs geom bare bareOut)
      let (head, body, _) := HtmlDoc.emitTree {} doc
      let (bareHead, bareBody, _) := HtmlDoc.emitTree {} bare
      t s!"listing origins {label}: provenance preserves serialized HTML"
        (Html.document "en" head body == Html.document "en" bareHead bareBody)
  for env in ["verbatim", "lstlisting"] do
    let line := "  build\t" ++ "".pushn 'W' 96
    let source := String.intercalate "\n" [
      "\\documentclass{article}", "\\begin{document}", "\\begin{" ++ env ++ "}",
      line, "\\end{" ++ env ++ "}", "\\end{document}"]
    let prepared := Elab.prepare file (Parse.parse file (Lex.lex file source).1).1
    let (doc, _, _) := Elab.runPrepared file prepared
    let geom : Layout.Geom := {
      pageW := Dim.pt 160, pageH := Dim.pt 400, hmargin := Dim.pt 12, vmargin := Dim.pt 12
      fontSize := Dim.pt 10, justify := false, hyphenate := false }
    let out := Layout.run geom fs none doc
    let losses := (out.diags.filter (·.kind == .W0005)).map
      prepared.sourceTriggers.attribute
    t s!"listing origins {env}: overflow cannot inherit the environment opener"
      (losses.size == 1 && losses.all fun d =>
        listingSourceExact file source d && d.trigger != some "\\begin" &&
          d.span.any fun span => span.pos.line == 4)

end Tests
