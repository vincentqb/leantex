import Tests.Artifact
import LeanTex.Cli.Render

open LeanTex.Core LeanTex.Cli

namespace Tests

private def literalRaws (file source : String) : Array Parse.Raw :=
  (Parse.parse file (Lex.lex file source).1).1

private def literalSources (file source : String) : Compat.SourceTriggers :=
  (Compat.execute file (literalRaws file source)).sourceTriggers

/-- Delayed diagnostics can originate at plain text or a special character.
Their source is the original lexical spelling and coordinates, including
when normalization changes the rendered word. Synthetic surface values do
not supply evidence merely by resembling authored text. -/
def diagnosticLiteralOriginChecks (ref : IO.Ref (List String))
    (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let file := "synthetic/literal-origins.tex"
  let cases : Array (String × Array (Nat × Nat × String)) := #[
    ("\n  Alpha & beta", #[(2, 3, "Alpha"), (2, 9, "&"), (2, 11, "beta")]),
    ("\n{Alpha}\n", #[(2, 2, "Alpha")]),
    ("[word]", #[(1, 1, "["), (1, 2, "word"), (1, 6, "]")]),
    ("Café tail", #[(1, 1, "Café"), (1, 7, "tail")])]
  for (source, sites) in cases do
    let sources := literalSources file source
    for (line, col, spelling) in sites do
      t s!"literal origins: exact authored token {spelling} at {line}:{col}"
        (sources[(file, line, col)]? == some spelling)
      let d := Diag.of .N0200 "The page uses its declared shrink."
        (some ⟨file, { line, col }⟩)
      let attributed := sources.attribute d
      t s!"literal origins: delayed token {spelling} preserves the entire record"
        (attributed.trigger == some spelling &&
          { attributed with trigger := d.trigger } == d &&
          decide (attributed.span = d.span))
      let foreign := { d with span := some ⟨file ++ ".other", { line, col }⟩ }
      t s!"literal origins: token {spelling} never borrows another file"
        ((sources.attribute foreign).trigger.isNone)
  let child := "synthetic/literal-child.tex"
  let sources := (Compat.execute file
    (#[.env (Parse.inputEnv child) (literalRaws child "\n  Child") {}] ++
      literalRaws file "\n  Parent")).sourceTriggers
  t "literal origins: includes retain different written words at equal coordinates"
    (sources[(file, 2, 3)]? == some "Parent" &&
      sources[(child, 2, 3)]? == some "Child")
  for raw in [Parse.Raw.word "invented" { line := 2, col := 3 },
      .sym '*' { line := 2, col := 3 }] do
    let sources := (Compat.execute file #[raw]).sourceTriggers
    let d := Diag.of .N0200 "The page uses its declared shrink."
      (some ⟨file, { line := 2, col := 3 }⟩)
    t "literal origins: synthetic values cannot invent written evidence"
      (sources.isEmpty && (sources.attribute d).trigger.isNone)
    let explicit := { d with trigger := some "\\authored" }
    t "literal origins: existing producer evidence survives a synthetic surface"
      (sources.attribute explicit == explicit)

  -- U+0344 expands to two combining scalars under NFC. A control consumes the
  -- first; the remaining fragment has no original boundary of its own.
  for source in ["\\\u0344_", "\\\u0344$x$"] do
    let tokens := (Lex.lex file source).1
    let sources := literalSources file source
    let fragments := tokens.filter fun token =>
      token.pos.command.isNone && match token.tok with
        | .word _ => true
        | _ => false
    t "literal origins: normalization preserves semantic tokens"
      (tokens.map (·.tok) == ((Lex.lex file (Nfc.normalize source)).1).map (·.tok))
    t "literal origins: expanded control leaves one unmapped fragment"
      (fragments.size == 1)
    for token in fragments do
      let d := Diag.of .N0200 "The page uses its declared shrink."
        (some ⟨file, token.pos⟩)
      t "literal origins: an unmapped fragment cannot borrow a neighboring token"
        ((sources.attribute d).trigger.isNone &&
          (sources.atSource file token.pos d).trigger.isNone)
      let explicit := { d with trigger := some "\\authored" }
      t "literal origins: failed mapping preserves explicit producer evidence"
        (sources.attribute explicit == explicit &&
          sources.atSource file token.pos explicit == explicit)

  let shrinkSource :=
    "\\documentclass{article}\\page{height=127pt,margin=20pt}\\begin{document}\n" ++
    "First.\n\n\\vspace{20pt minus 8pt}\nSecond.\n\n" ++
    "\\vspace{20pt minus 8pt}\nThird.\n\\end{document}"
  let prepared := Elab.prepare file (literalRaws file shrinkSource)
  let (doc, ds, _) := Elab.runPrepared file prepared
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom fs none doc
  let notes := (out.diags.filter (·.kind == .N0200)).map prepared.sourceTriggers.attribute
  t "literal origins: page compression reports the actual plaintext box"
    (ds.all (·.severity != .error) && out.pages.size == 1 && notes.size == 1 &&
      notes.all fun d =>
        d.span.any (fun s => s.file == file && s.pos.line == 8 && s.pos.col == 1) &&
        d.trigger == some "Third.")
  t "literal origins: human and JSON compression records name the written text"
    (notes.any fun d =>
      hasStr (Render.human false d) "literal-origins.tex:8:1 - Third." &&
      hasStr (Render.porcelainDiag d) "\"trigger\":\"Third.\"")
  let bare := Ir.eraseLocations doc
  let bareOut := Layout.run geom fs none bare
  t "literal origins: source evidence preserves shipped layout and PDF bytes"
    (reprStr out.pages == reprStr bareOut.pages &&
      driverPdf fs geom doc out == driverPdf fs geom bare bareOut)
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let (bareHead, bareBody, _) := HtmlDoc.emitTree {} bare
  t "literal origins: source evidence preserves the serialized HTML"
    (Html.document "en" head body == Html.document "en" bareHead bareBody)

  let word := "".pushn 'W' 96
  let source := "\\documentclass{article}\\begin{document}\n  " ++ word ++
    "\n\\end{document}"
  let prepared := Elab.prepare file (literalRaws file source)
  let (doc, _, _) := Elab.runPrepared file prepared
  let geom : Layout.Geom := {
    pageW := Dim.pt 160, pageH := Dim.pt 400, hmargin := Dim.pt 12, vmargin := Dim.pt 12
    fontSize := Dim.pt 10, justify := false, hyphenate := false }
  let out := Layout.run geom fs none doc
  let warnings := (out.diags.filter (·.kind == .W0005)).map prepared.sourceTriggers.attribute
  t "literal origins: unbreakable text reports its exact written word"
    (warnings.size == 1 && warnings.all fun d =>
      d.span.any (fun s => s.file == file && s.pos.line == 2 && s.pos.col == 3) &&
      d.trigger == some word)

end Tests
