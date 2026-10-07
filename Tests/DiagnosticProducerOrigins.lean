import Tests.Support
import Lean.Data.Json.Parser

open LeanTex.Core LeanTex.Cli

namespace Tests

private def producerRowCases : Array (String × String × String) := #[
  ("env:minipage-row",
    "\\begin{minipage}{.4\\textwidth}Left\\end{minipage}\\hfill" ++
      "\\begin{minipage}{.4\\textwidth}Right\\end{minipage}", "\\begin"),
  ("env:box-picture-row",
    "\\parbox[t]{.2\\textwidth}{Label} " ++
      "\\begin{tikzpicture}\\node at (0,0) {Node};\\end{tikzpicture}", "\\parbox")]

private def producerRoutedPicture : String :=
  "\\begin{tikzpicture}\\node[text width=4cm] at (0,0) " ++
    "{Upper\\par\\smallskip Lower};\\end{tikzpicture}"

private def producerParse (file text : String) : Array Parse.Raw :=
  (Parse.parse file (Lex.lex file text).1).1

private def producerAt (d : Diag) (expected : Span) (trigger : String) : Bool :=
  d.trigger == some trigger && d.span.any fun actual =>
    actual == expected && actual.pos.origins == expected.pos.origins &&
      actual.pos.command == expected.pos.command

private def producerRun (file text : String) : IO (Ir.Doc × Array Diag) := do
  let (tokens, lexDs) := Lex.lex file text
  let (raws, parseDs) := Parse.parse file tokens
  let (executed, inputDs, _) ← Input.expandInputs file raws
  let (doc, ds, _) := Elab.runPrepared file (Elab.prepareExecuted file executed)
    (lexDs ++ parseDs ++ inputDs)
  return (doc, ds)

/-- Late compatibility diagnostics obey the same input-file stack as the
rewrite that precedes them. Coordinates, source spelling and ancestry remain
attached to the row; returning from an include restores the surrounding file.
The oracle reads each complete record and the emitted HTML tree, not an IR dump.
The root deliberately has an unrelated input command at the child's coordinates:
attributing a wrong filename must not pass just because a trigger is nonempty. -/
def diagnosticProducerOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    let child := (dir / "child.tex").toString
    let deep := (dir / "deep.tex").toString
    let sibling := (dir / "sibling.tex").toString
    let opening := "\\documentclass{article}\n\\begin{document}\n"
    let closing := "\n\\end{document}"
    for (subject, row, trigger) in producerRowCases do
      IO.FS.writeFile child ("% child\n\n  " ++ row ++ "\n\n")
      let (directDoc, directDs) ← producerRun file (opening ++ "  " ++ row ++ closing)
      let (childDoc, childDs) ← producerRun file
        (opening ++ "  \\input{child}" ++ closing)
      for (label, ds, expected) in [
          ("direct", directDs, file), ("included", childDs, child)] do
        let rows := ds.filter fun d => d.kind == .N0100 && d.subject == some subject
        t s!"producer origins: {subject}/{label} has exactly one correctly attributed row"
          (rows.size == 1 && rows.all (producerAt ·
            ⟨expected, { line := 3, col := 3, command := some trigger }⟩ trigger))
        t s!"producer origins: {subject}/{label} completes without errors"
          (ds.all (·.severity != .error))
      let (directHead, directBody, _) := HtmlDoc.emitTree {} directDoc
      let (childHead, childBody, _) := HtmlDoc.emitTree {} childDoc
      t s!"producer origins: {subject} input provenance preserves both HTML projections"
        (!directBody.isEmpty && Html.document "en" directHead directBody ==
          Html.document "en" childHead childBody)

      IO.FS.writeFile deep ("% deep\n\n\n    " ++ row ++ "\n\n")
      IO.FS.writeFile child
        ("% child\n\n  " ++ row ++ "\n\n\\input{deep}\n\n   " ++ row ++ "\n\n")
      IO.FS.writeFile sibling ("% sibling\n\n     " ++ row ++ "\n\n")
      let (nestedDoc, nestedDs) ← producerRun file
        (opening ++ "  \\input{child}\n\n\\input{sibling}\n\n      " ++ row ++ closing)
      let rows := nestedDs.filter fun d => d.kind == .N0100 && d.subject == some subject
      let expected : Array Span := #[
        ⟨child, { line := 3, col := 3, command := some trigger }⟩,
        ⟨deep, { line := 4, col := 5, command := some trigger }⟩,
        ⟨child, { line := 7, col := 4, command := some trigger }⟩,
        ⟨sibling, { line := 3, col := 6, command := some trigger }⟩,
        ⟨file, { line := 7, col := 7, command := some trigger }⟩]
      t s!"producer origins: {subject} keeps all five nested and sibling notes"
        (rows.size == expected.size && nestedDs.all (·.severity != .error))
      for h : i in [:expected.size] do
        t s!"producer origins: {subject} attributes source site {i} exactly once"
          ((rows.filter (producerAt · expected[i] trigger)).size == 1)
      let (flatDoc, _) ← producerRun file
        (opening ++ String.intercalate "\n\n" (List.replicate 5 row) ++ closing)
      let (nestedHead, nestedBody, _) := HtmlDoc.emitTree {} nestedDoc
      let (flatHead, flatBody, _) := HtmlDoc.emitTree {} flatDoc
      t s!"producer origins: {subject} nested file switches do not repaint the HTML"
        (!flatBody.isEmpty && Html.document "en" nestedHead nestedBody ==
          Html.document "en" flatHead flatBody)

      let origin : MacroOrigin := ⟨29, "syntheticrow"⟩
      let marked := Parse.markMacroList origin #[] (producerParse child ("\n  " ++ row)).toList
      let closingRaws := producerParse file closing
      let raws := producerParse file opening ++
        #[.env (Parse.inputEnv child) #[.group marked { line := 9, col := 2 }]
          { line := 3, col := 3 }] ++ closingRaws
      let (_, markedDs, _) := Elab.runRawsSpanned file raws
      let markedRows := markedDs.filter fun d => d.kind == .N0100 && d.subject == some subject
      t s!"producer origins: {subject} retains ancestry through a group inside an input"
        (markedRows.size == 1 && markedRows.all (producerAt ·
          ⟨child, { line := 2, col := 3, origins := [origin], command := some trigger }⟩ trigger))

/-- Every aggregation input uses lexical attribution once it becomes a final
diagnostic. A record without source evidence remains unlocated. Apart from the
trigger, the record (including ancestry and command, which Pos.BEq ignores)
must survive unchanged. These guards exercise completePrepared via runPrepared. -/
def diagnosticAggregationOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let file := "synthetic-aggregation.tex"
  let source := "\\documentclass{article}\n\\begin{document}\n    \\textbf{Body}\n\\end{document}"
  let prepared := Elab.prepare file (producerParse file source)
  let position : Pos :=
    { line := 3, col := 5, origins := [⟨31, "syntheticearly"⟩], command := some "\\textbf" }
  let earlier := Diag.of .N0020 "an earlier phase read a local theme"
    (some ⟨file, position⟩) (help := "synthetic action") (subject := "producer:earlier")
    (refused := "synthetic name") (recovery := some .ignored) (output := some .html)
  let compat := { earlier with subject := some "producer:compat" }
  let absent := Diag.of .N0020 "an unlocated earlier note" (subject := "producer:unlocated")
  let explicit := { absent with subject := some "producer:explicit", trigger := some "\\recorded" }
  let (_, ds, _) := Elab.runPrepared file
    { prepared with compatDiags := prepared.compatDiags.push compat }
    #[earlier, absent, explicit]
  for d in [earlier, compat, absent, explicit] do
    let found := ds.filter (·.subject == d.subject)
    let expected := if d.span.isSome then { d with trigger := some "\\textbf" } else d
    t s!"producer aggregation: {d.subject.getD ""} survives once with exact attribution"
      (found.size == 1 && found.all fun actual =>
        actual == expected && if let some sp := d.span then producerAt actual sp "\\textbf"
          else actual.span.isNone && actual.trigger == expected.trigger)

private def producerJsonAt (j : Lean.Json) (file : String) (line col : Nat)
    (trigger : String) : Bool :=
  j.getObjValAs? String "file" == .ok file &&
    j.getObjValAs? Nat "line" == .ok line && j.getObjValAs? Nat "col" == .ok col &&
    j.getObjValAs? String "trigger" == .ok trigger

/-- Full Driver pipeline guards. The caller supplies an already-built binary;
this check never starts a build. A private synthetic renderer reports its
version, then refuses with a log, so N0419 is a real withdrawal note without
depending on TeX, a browser or global caches. Local theme notes are produced
after elaboration. Direct and included inputs must emit the same HTML bytes. -/
def diagnosticPipelineOriginChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex")
    (font : System.FilePath := "testdata/corpus/fonts/OpenSans-Regular.ttf") : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath binary
  let font ← IO.FS.realPath font
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    let tool := dir / "lualatex"
    IO.FS.writeFile tool
      "#!/bin/sh\n\
      if [ \"$1\" = --version ]; then\n\
        printf '%s\\n' 'synthetic provenance renderer 1'\n\
        exit 0\n\
      fi\n\
      printf '%s\\n' 'synthetic picture refusal' > pic.log\n\
      exit 17\n"
    IO.setAccessRights tool { user := ⟨true, true, true⟩ }
    IO.FS.writeFile (dir / "beamerthemeSourceProbe.sty") "% synthetic local theme\n"
    let file := (dir / "host.tex").toString
    let look := (dir / "look.tex").toString
    let body := (dir / "body.tex").toString
    IO.FS.writeFile look "% local look\n\n   \\usetheme{SourceProbe}\n"
    for (subject, row, trigger) in producerRowCases do
      let mut directHtml : Option String := none
      for included in [false, true] do
        IO.FS.writeFile body ("% local body\n\n  " ++ row ++ "\n\n    " ++ producerRoutedPicture)
        let preamble := if included then "   \\input{look}" else "   \\usetheme{SourceProbe}"
        let content := if included then "  \\input{body}"
          else "  " ++ row ++ "\n\n    " ++ producerRoutedPicture
        IO.FS.writeFile file ("\\documentclass{article}\n\\output{formats=html}\n" ++
          "\\pictures{tool=lualatex}\n" ++ preamble ++
          "\n\\begin{document}\n\n" ++ content ++ "\n\\end{document}\n")
        let output := dir / s!"{if included then "included" else "direct"}.html"
        let result ← IO.Process.output {
          cmd := binary.toString
          args := #[file, "-o", output.toString, "--porcelain", "-v"]
          env := #[("PATH", some (dir.toString ++ ":" ++ path)),
            ("XDG_CACHE_HOME", some (dir / "cache").toString),
            ("LEANTEX_FONT", some font.toString)] }
        let lines := (result.stdout.splitOn "\n").filter (!·.isEmpty)
        let decoded := lines.map Lean.Json.parse
        let records := decoded.filterMap (·.toOption)
        t s!"producer pipeline: {subject}/{included} builds and reports valid JSONL"
          (result.exitCode == 0 && !lines.isEmpty && decoded.all (·.isOk) &&
            (← output.pathExists))
        for (code, expectedFile, line, col, written) in [
            ("N0020", if included then look else file, if included then 3 else 4, 4, "\\usetheme"),
            ("N0100", if included then body else file, if included then 3 else 7, 3, trigger),
            ("N0419", if included then body else file, if included then 5 else 9, 5, "\\begin")] do
          let found := records.filter fun j => j.getObjValAs? String "code" == .ok code &&
            (code != "N0100" || j.getObjValAs? String "subject" == .ok subject)
          t s!"producer pipeline: {subject}/{included}/{code} survives once at its real source"
            (found.length == 1 && found.all (producerJsonAt · expectedFile line col written))
        let html := (← (IO.FS.readFile output).toBaseIO).toOption
        if included then
          t s!"producer pipeline: {subject} include attribution leaves HTML bytes unchanged"
            (directHtml.isSome && directHtml == html)
        else
          directHtml := html

end Tests
