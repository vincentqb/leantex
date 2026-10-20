module

public import Tests.Artifact
public import LeanTex.Cli.Render

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- The diagnostic stands where `text` is written in `source` and names no construct. -/
private def listingSourceExact (file source text : String) (d : Diag) : Bool := Id.run do
  let some span := d.span | return false
  let some line := (source.splitOn "\n")[span.pos.line - 1]? | return false
  return span.file == file && span.pos.line > 0 && span.pos.col > 0 && d.trigger.isNone &&
    (String.ofList (line.toList.drop (span.pos.col - 1))).startsWith text

/-- Listing diagnostics carry source coordinates whatever the tab expansion, line numbering, line
endings and paint, quote no code, and leave layout and bytes unchanged. -/
def diagnosticListingOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font := do
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
      -- A plain line is one token; a highlighted line stands at the token holding the scalar.
      t s!"listing origins {label}: fallback stands at its source text"
        (ds.all (·.severity != .error) && losses.size == 1 &&
          losses.all (listingSourceExact file source (if highlighted then "∀" else "prefix")))
      if highlighted then
        let col := line.toList.takeWhile (· != '∀') |>.length |>.succ
        t s!"listing origins {label}: tab and Unicode count authored scalars"
          (losses.all fun d => d.span.any fun span => span.pos.line == 4 && span.pos.col == col)
      t s!"listing origins {label}: rendered record leads with its location"
        (losses.all fun d => d.span.any fun span =>
          (Render.human false d).startsWith s!"{file}:{span.pos.line}:{span.pos.col}: " &&
          !hasStr (Render.porcelainDiag d) "\"trigger\":")
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
    t s!"listing origins {env}: overflow stands at its line and names no opener"
      (losses.size == 1 && losses.all fun d =>
        listingSourceExact file source "  build" d && d.span.any fun span => span.pos.line == 4)
  -- A highlighted line's indentation is its own token, which lays down no ink.
  for (lang, indent) in [("python", "    "), ("lean4", "  "), ("bash", "\t ")] do
    let line := indent ++ "build_all(" ++ "".pushn 'W' 96 ++ ")"
    let source := String.intercalate "\n" [
      "\\documentclass{article}", "\\begin{document}", "\\begin{minted}{" ++ lang ++ "}",
      line, "\\end{minted}", "\\end{document}"]
    let prepared := Elab.prepare file (Parse.parse file (Lex.lex file source).1).1
    let (doc, _, _) := Elab.runPrepared file prepared
    let geom : Layout.Geom := {
      pageW := Dim.pt 160, pageH := Dim.pt 400, hmargin := Dim.pt 12, vmargin := Dim.pt 12
      fontSize := Dim.pt 10, justify := false, hyphenate := false }
    let out := Layout.run geom fs none doc
    let losses := (out.diags.filter (·.kind == .W0005)).map
      prepared.sourceTriggers.attribute
    t s!"listing origins minted {lang}: an indented overflow stands at its first inked token"
      (losses.size == 1 && losses.all fun d =>
        listingSourceExact file source "build_all" d &&
          d.span.any fun span => span.pos.line == 4 && span.pos.col == indent.length + 1)

end Tests
