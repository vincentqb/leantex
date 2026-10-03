import Tests.Support
import Lean.Data.Json.Parser

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- A diagnostic's first line carries its effective severity, declared loss,
stable code and optional source position. Continuations belong to that one
record, even when a tool or filename supplies terminal control characters.
These are output assertions, independent of the diagnostics golden. -/
def diagnosticFormatTextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let span : Span := ⟨"chapters/example file.tex", { line := 4, col := 7 }⟩
  let d := Diag.of .W0301 "unknown command '\\oddity'; its text is kept"
    (some span) (help := "define '\\oddity' before using it") (subject := "ctrl:oddity")
  let plain := "Warning - Degraded [W0301] - chapters/example file.tex:4:7\n  " ++
    "unknown command '\\oddity'; its text is kept\n  suggestion: define '\\oddity' before using it"
  t "diagnostic format: location and fixed category on the first line"
    (Render.human false d == plain)
  t "diagnostic format: no invented location or suggestion"
    (Render.human false (Diag.of .E0001 "cannot read input") ==
      "Error - Dropped [E0001]\n  cannot read input")
  let unicodeSpan : Span := ⟨"résumé [draft].tex", { line := 2, col := 3 }⟩
  t "diagnostic format: Unicode and punctuation in a path survive"
    (Render.human false { d with span := some unicodeSpan, help := none } ==
      "Warning - Degraded [W0301] - résumé [draft].tex:2:3\n  " ++
      "unknown command '\\oddity'; its text is kept")
  for (kind, head) in [(DiagCode.E0101, "Error - Dropped [E0101]"),
      (.W0307, "Warning - Pending [W0307]"), (.W0301, "Warning - Degraded [W0301]"),
      (.W0201, "Warning - Standard [W0201]"), (.W0101, "Warning - Config [W0101]"),
      (.N0100, "Note - Info [N0100]")] do
    t s!"diagnostic format: {kind.code} displays its declared category"
      (Render.human false (Diag.of kind "detail") == head ++ "\n  detail")
  -- Future registry entries must take the same projection, including an
  -- accepted error whose effective severity is a note but code stays E….
  for kind in DiagCode.all do
    let raw := Diag.of kind "detail"
    for resolved in [raw, (Diag.accept #[raw.code] false raw).1] do
      let head := s!"{resolved.severity.label.capitalize} - {kind.loss.label.capitalize} [{raw.code}]"
      t s!"diagnostic format: registry/policy projection {raw.code}/{resolved.severity.label}"
        (Render.human false resolved == head ++ "\n  detail")
  let accepted := (Diag.accept #["W0301"] false d).1
  t "diagnostic format: accepted loss retains code and category"
    (Render.human false accepted == plain.replace "Warning - " "Note - ")
  t "diagnostic format: repeated sites keep their total"
    (Render.human false { d with sites := 3 } ==
      plain.replace "4:7\n" "4:7 (3 sites)\n")
  t "diagnostic format: a non-carrier does not acquire a false site count"
    (Render.human false { d with sites := 0 } == plain)
  let multi := Diag.of .E0001 "first\r\nError - not another record\n\nlast\rline\tend\x1b[31m"
    (some ⟨"part\nforged\r\x1b.tex", { line := 1, col := 2 }⟩)
    (help := "run <red>{command}</red>\r\nthen retry\n")
  t "diagnostic format: multiline text is indented and controls cannot forge a record"
    (Render.human false multi ==
      "Error - Dropped [E0001] - part\\nforged\\r\\x1b.tex:1:2\n  " ++
      "first\n  Error - not another record\n  \n  last\\rline\\tend\\x1b[31m\n" ++
      "  suggestion: run <red>{command}</red>\n    then retry\n    ")
  let controls := String.ofList ['\x00', '\x07', '\x08', '\x7f', '\x85', '\x9b']
  t "diagnostic format: terminal controls are visible text"
    (Render.human false (Diag.of .E0001 controls) ==
      "Error - Dropped [E0001]\n  \\x00\\x07\\x08\\x7f\\x85\\x9b")
  let statusControls := String.ofList ((List.range 32 ++ (List.range 33).map (· + 127) ++
    [0x2028, 0x2029]).map Char.ofNat)
  for color in [false, true] do
    let unstyle := fun (s : String) =>
      ["\x1b[1;32m", "\x1b[1;31m", "\x1b[2m", "\x1b[0m"].foldl
        (fun text code => text.replace code "") s
    let statuses : List (String × (String → String) × (String → String)) :=
      [("summary success", (fun path => Render.humanSummary color path 0 7),
          (fun path => s!"✔ {path} (7 ms)")),
       ("summary error", (fun path => Render.humanSummary color path 2 7),
          (fun path => s!"✖ {path} — 2 errors (7 ms)")),
       ("done", (fun path => Render.humanDone color path (path ++ ".pdf") 1 7),
          (fun path => s!"✔ {path} → {path}.pdf — 1 page (7 ms)")),
       ("done with notes", (fun path => Render.humanDone color path (path ++ ".html") 2 7 1),
          (fun path => s!"✔ {path} → {path}.html — 2 pages (7 ms) · 1 note (-v)")),
       ("werror", (fun path => Render.humanWerror color path 2 7),
          (fun path => s!"✖ {path} — 2 warnings (--werror) (7 ms)"))]
    for (name, render, expected) in statuses do
      for (path, visible) in
          [("", ""), ("résumé [draft]\\part", "résumé [draft]\\part"),
           ("\r\n\t\x1b[0m\x9b0m\u2028\u2029", "\\r\\n\\t\\x1b[0m\\x9b0m\\u2028\\u2029")] do
        let actual := render path
        t s!"diagnostic format: {name} preserves visible paths, color={color}"
          (unstyle actual == expected visible && actual.contains '\x1b' == color)
      t s!"diagnostic format: {name} is one safe physical line, color={color}"
        (!(unstyle (render statusControls)).toList.any fun c => c.toNat < 0x20 ||
          (0x7F ≤ c.toNat && c.toNat ≤ 0x9F) || c == '\u2028' || c == '\u2029')
  -- Strip only the SGR sequences the renderer emits, not arbitrary escapes
  -- in a diagnostic. The latter must have been spelled out as data.
  for sample in [d, multi, { d with sites := 3 }, accepted] do
    let colored := Render.human true sample
    let stripped := ["\x1b[1;31m", "\x1b[1;33m", "\x1b[1;36m", "\x1b[1;34m",
      "\x1b[1m", "\x1b[0m"].foldl (fun s code => s.replace code "") colored
    t "diagnostic format: color adds no information or untrusted SGR"
      (colored.contains '\x1b' && stripped == Render.human false sample &&
       !(Render.human false sample).contains '\x1b')
  let machine : Diag := { d with
    message := "bad \"quote\"\nline\r\t\x1b"
    help := some "fix\nretry"
    sites := 3 }
  let json := "{\"event\":\"diagnostic\",\"severity\":\"warning\",\"code\":\"W0301\"," ++
    "\"loss\":\"degraded\",\"message\":\"bad \\\"quote\\\"\\nline\\r\\t\\u001b\"," ++
    "\"file\":\"chapters/example file.tex\",\"line\":4,\"col\":7," ++
    "\"help\":\"fix\\nretry\",\"subject\":\"ctrl:oddity\",\"sites\":3}"
  t "diagnostic format: porcelain remains byte-identical"
    (Render.porcelainDiag machine == json)
  t "diagnostic format: porcelain acceptance changes only effective severity"
    (Render.porcelainDiag (Diag.accept #[machine.code] false machine).1 ==
      json.replace "\"severity\":\"warning\"" "\"severity\":\"note\"")

/-- The record carries source spelling, actual recovery and suggested action
independently. Scope is identity: one artifact's notices cannot count or
accept losses in another. Empty and hostile payloads are ordinary data. -/
def diagnosticRecordChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let d := Diag.of .W0301 "command is unknown"
    (some ⟨"example.tex", { line := 4, col := 7 }⟩)
    (help := "define the command") (subject := "ctrl:oddity")
    (refused := "oddity") (trigger := "\\oddity")
    (recovery := some (.replacedBy "its argument text")) (output := some .html)
  let header := "Warning - Degraded [W0301] (HTML) - example.tex:4:7 - \\oddity"
  t "diagnostic record: header, reason, recovery and action are separate"
    (Render.human false d == header ++ "\n  command is unknown\n" ++
      "  replaced by: its argument text\n  suggestion: define the command")
  for (recovery, line) in [(Diag.Recovery.ignored, "ignored"),
      (.skipped, "skipped"), (.replacedBy "plain text", "replaced by: plain text")] do
    t "diagnostic record: recovery without a suggestion occupies only its own line"
      (Render.human false { d with recovery := some recovery, help := none } ==
        header ++ "\n  command is unknown\n  " ++ line)
  t "diagnostic record: suggestion alone is not recovery"
    (Render.human false { d with recovery := none } ==
      header ++ "\n  command is unknown\n  suggestion: define the command")
  t "diagnostic record: no trigger is inferred from subject, refused name or prose"
    (Render.human false { d with
        trigger := none
        recovery := none
        help := none
        output := none
        message := "replaced by: this is only a reason" } ==
      "Warning - Degraded [W0301] - example.tex:4:7\n  replaced by: this is only a reason")
  let empty := Diag.of .W0301 "" (help := "") (trigger := "")
  t "diagnostic record: absent or empty optional text adds no blank lines"
    (Render.human false empty == "Warning - Degraded [W0301]" &&
      Render.human false { empty with recovery := some (.replacedBy "") } ==
        "Warning - Degraded [W0301]\n  replaced")
  let payload := "\\oddity\r\nError - forged\t\x1b[31m\x9b0m\u2028\u2029"
  let safe := "\\oddity\\r\\nError - forged\\t\\x1b[31m\\x9b0m\\u2028\\u2029"
  let hostile := { d with
    trigger := some payload
    recovery := some (.replacedBy payload)
    help := none }
  t "diagnostic record: trigger cannot create a line or terminal escape"
    ((Render.human false hostile).splitOn "\n" ==
      ["Warning - Degraded [W0301] (HTML) - example.tex:4:7 - " ++ safe,
        "  command is unknown", "  replaced by: \\oddity",
        "    Error - forged\\t\\x1b[31m\\x9b0m\\u2028\\u2029"])
  for sample in [d, hostile, empty] do
    let stripped := ["\x1b[1;31m", "\x1b[1;33m", "\x1b[1;36m", "\x1b[1;34m",
      "\x1b[1m", "\x1b[0m"].foldl (fun s code => s.replace code "") (Render.human true sample)
    t "diagnostic record: styling does not change structured content"
      (stripped == Render.human false sample && !stripped.contains '\x1b')
  let json := Render.porcelainDiag d
  t "diagnostic record: new JSON keys are additive, recovery is structured"
    (json == "{\"event\":\"diagnostic\",\"severity\":\"warning\",\"code\":\"W0301\"," ++
      "\"loss\":\"degraded\",\"message\":\"command is unknown\",\"file\":\"example.tex\"," ++
      "\"line\":4,\"col\":7,\"help\":\"define the command\",\"subject\":\"ctrl:oddity\"," ++
      "\"trigger\":\"\\\\oddity\",\"recovery\":{\"kind\":\"replacedBy\",\"replacement\":\"its argument text\"}," ++
      "\"output\":\"html\"}")
  for (recovery, kind) in [(Diag.Recovery.ignored, "ignored"), (.skipped, "skipped")] do
    let parsed := Lean.Json.parse (Render.porcelainDiag { empty with recovery := some recovery })
    let actual := parsed.bind fun j => (j.getObjVal? "recovery").bind fun r =>
      (r.getObjVal? "kind").bind Lean.Json.getStr?
    t "diagnostic record: each recovery has its own JSON kind" (actual.toOption == some kind)
  -- Round-trip every serialized text field empty, then with all terminal
  -- control bytes and both Unicode line separators, through a real JSON reader.
  let controls := String.ofList ((List.range 32 ++ (List.range 33).map (· + 127) ++
    [0x2028, 0x2029]).map Char.ofNat)
  for text in ["", "\"\\" ++ controls] do
    let sample := Diag.of .W0301 text
      (some ⟨text, { line := 0, col := 0 }⟩) (help := text) (subject := text)
      (trigger := text) (recovery := some (.replacedBy text)) (output := some .pdf)
    let encoded := Render.porcelainDiag sample
    let parsed := Lean.Json.parse encoded
    for key in ["message", "file", "help", "subject", "trigger"] do
      let actual := parsed.bind fun j => (j.getObjVal? key).bind Lean.Json.getStr?
      t s!"diagnostic record: JSON round-trip {key}" (actual.toOption == some text)
    let actual := parsed.bind fun j => (j.getObjVal? "recovery").bind fun r =>
      (r.getObjVal? "replacement").bind Lean.Json.getStr?
    t "diagnostic record: JSON round-trip empty or hostile replacement"
      (actual.toOption == some text)
    let output := parsed.bind fun j => (j.getObjVal? "output").bind Lean.Json.getStr?
    t "diagnostic record: JSON retains output scope" (output.toOption == some "pdf")
    t "diagnostic record: JSON is one safe physical line"
      (!encoded.toList.any fun c => c.toNat < 0x20 ||
        (0x7F ≤ c.toNat && c.toNat ≤ 0x9F) || c == '\u2028' || c == '\u2029')
  let pdf := { d with output := some .pdf }
  let html := { d with output := some .html }
  let common := { d with output := none }
  let ds := #[pdf, html, pdf, common, html]
  t "diagnostic record: scopes are distinct loss identities"
    (!Diag.sameLoss pdf html && !Diag.sameLoss pdf common &&
      !Diag.sameLoss html common && Diag.sameLoss pdf pdf)
  t "diagnostic record: census cannot merge output-specific losses"
    ((Diag.tallySites ds).map (·.sites) == #[2, 2, 0, 1, 0])
  t "diagnostic record: output projection preserves order and unscoped records"
    (Diag.forOutputs #[.pdf] ds == #[pdf, pdf, common] &&
      Diag.forOutputs #[.html] ds == #[html, common, html] &&
      Diag.forOutputs #[.pdf, .html] ds == ds && Diag.forOutputs #[] ds == #[common])
  for outputs in [#[], #[Diag.Output.pdf], #[.html], #[.pdf, .html], #[.html, .html]] do
    let projected := Diag.forOutputs outputs ds
    t "diagnostic record: projecting again neither drops nor duplicates records"
      (Diag.forOutputs outputs projected == projected)
    t "diagnostic record: output filtering commutes with site census"
      (Diag.forOutputs outputs (Diag.tallySites ds) == Diag.tallySites projected)
  let projected := Diag.forOutputs #[.pdf] #[html]
  let resolved := Diag.resolveAll #[] false projected
  t "diagnostic record: excluded output contributes no firing, warning or acceptance"
    (resolved.diags.isEmpty && resolved.fired.isEmpty && resolved.accepted.isEmpty &&
      resolved.errors == 0 && resolved.warnings == 0)
  for raw in [pdf, html, common, Diag.demote d] do
    for all in [false, true] do
      for allowed in [#[], #[raw.code]] do
        let resolved := (Diag.accept allowed all raw).1
        t "diagnostic record: acceptance preserves the entire payload"
          (Diag.demote resolved == Diag.demote raw)
    t "diagnostic record: explicit demotion agrees with acceptance"
      (Diag.demote raw == (Diag.accept #[raw.code] true raw).1)
  for (raw, counted) in ds.toList.zip (Diag.tallySites ds).toList do
    t "diagnostic record: census preserves the entire payload"
      ({ counted with sites := raw.sites } == raw)
  t "diagnostic record: HTML driver failures are scoped to HTML"
    ((DriverDiag.boundarySvgMissing "unavailable").output == some .html &&
      (DriverDiag.htmlResourceUnavailable "missing resource").output == some .html)

/-- Exercise the emitted stderr, stream routing and exits of the built CLI.
The malformed synthetic inputs stop before fonts or external tools are
needed. In particular the warning must still fire beside a fatal error,
and accepting it changes visibility only under the existing verbosity rule. -/
def diagnosticFormatCliChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"diagnostic format: CLI builds: {build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode != 0 then return
  let run (args : Array String) := IO.Process.output {
    cmd := ".lake/build/bin/leantex", args := args }
  IO.FS.withTempDir fun dir => do
    let file := (dir / "invalid.tex").toString
    IO.FS.writeBinFile file ⟨#[0xFF]⟩
    let bad ← run #["dump", file, "--color=never"]
    t "diagnostic format: emitted error separates location, reason and suggestion and keeps failure exit"
      (bad.exitCode == 1 && bad.stdout.isEmpty && bad.stderr ==
        s!"Error - Dropped [E0002] - {file}:1:1\n  invalid UTF-8: invalid start byte 0xFF at byte offset 0\n" ++
        "  suggestion: every input is read as UTF-8; `iconv -t utf-8` re-encodes the file\n")
    let porcelain ← run #["dump", file, "--porcelain"]
    t "diagnostic format: emitted porcelain stays JSONL on stdout"
      (porcelain.exitCode == 1 && porcelain.stderr.isEmpty && porcelain.stdout ==
        "{\"event\":\"diagnostic\",\"severity\":\"error\",\"code\":\"E0002\",\"loss\":\"dropped\"," ++
        "\"message\":\"invalid UTF-8: invalid start byte 0xFF at byte offset 0\",\"file\":\"" ++ file ++
        "\",\"line\":1,\"col\":1,\"help\":\"every input is read as UTF-8; `iconv -t utf-8` re-encodes the file\"}\n")
    let usage ← run #["--not-a-flag"]
    t "diagnostic format: parser-independent argument errors keep their established output"
      (usage.exitCode == 3 && usage.stdout.isEmpty && usage.stderr ==
        "leantex: unknown flag '--not-a-flag'\ntry 'leantex --help'\n")
    let machineUsage ← run #["--porcelain", "--not-a-flag"]
    t "diagnostic format: argument errors preserve porcelain-mode stderr"
      (machineUsage.exitCode == 3 && machineUsage.stdout.isEmpty && machineUsage.stderr ==
        "leantex: unknown flag '--not-a-flag'\ntry 'leantex --help'\n")
    let output := (dir / "output.bad").toString
    let dest ← run #[file, "-o", output, "--color=never"]
    t "diagnostic format: parser-independent output preflight keeps its established output"
      (dest.exitCode == 3 && dest.stdout.isEmpty && dest.stderr ==
        s!"leantex: cannot tell the output format of '{output}'; name it *.pdf or *.html, or pass a directory\n")
    let machineDest ← run #[file, "-o", output, "--porcelain"]
    t "diagnostic format: output preflight preserves porcelain-mode stderr"
      (machineDest.exitCode == 3 && machineDest.stdout.isEmpty && machineDest.stderr ==
        s!"leantex: cannot tell the output format of '{output}'; name it *.pdf or *.html, or pass a directory\n")
    let source := (dir / "example.tex").toString
    for allow in [false, true] do
      IO.FS.writeFile source ("\\documentclass{article}\n" ++
        (if allow then "\\allow{W0301}\n" else "\n") ++
        "\\begin{document}\n\\oddity{kept}\n}\n\\end{document}\n")
      for verbose in [false, true] do
        let result ← run (#[source, "--color=never"] ++
          if verbose then #["-v"] else #["-q"])
        let lines := result.stderr.splitOn "\n"
        let expected := s!"{if allow then "Note" else "Warning"} - Degraded [W0301] - {source}:4:1\n  " ++
          "unknown command '\\oddity'; its {...} arguments were kept as text"
        t s!"diagnostic format: emitted warning and acceptance {allow}/{verbose}"
          (result.exitCode == 1 && result.stdout.isEmpty &&
           if !allow || verbose then (result.stderr.splitOn expected).length == 2 &&
             lines.contains "  suggestion: \\define \\name(...) {body} declares it"
           else lines.all fun line => (line.splitOn "[W0301]").length ≤ 1)
        t s!"diagnostic format: fatal error is never suppressed {allow}/{verbose}"
          (lines.any (·.startsWith s!"Error - Dropped [E0202] - {source}:5:1"))

/-- Output scope is resolved by the real output plan before warning counts,
acceptance and printing. A static raster makes these driver probes independent
of installed SVG converters or a TeX engine. -/
def diagnosticOutputCliChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let font ← IO.FS.realPath (testFonts ++ "/OpenSans-Regular.ttf")
  let image ← IO.FS.readBinFile "tests/corpus/rects.png"
  IO.FS.withTempDir fun dir => do
    IO.FS.writeBinFile (dir / "animation-probe.png") image
    let file := dir / "scope.tex"
    for (name, scopes) in [("pdf", ["pdf"]), ("html", ["html"]),
        ("both", ["pdf", "html"])] do
      for allow in [false, true] do
        let formats := String.intercalate "," scopes
        IO.FS.writeFile file ("\\documentclass{article}\n" ++
          "\\output{formats=" ++ formats ++ "}\n" ++
          (if allow then "\\allow{W0110}\n" else "\n") ++
          "\\begin{document}\n" ++
          "\\animategraphics[width=32pt,alt={Moving square},autoplay,loop,controls]" ++
          "{17}{animation-probe}{}{}\n\\end{document}\n")
        let output := dir / s!"{name}-{allow}"
        IO.FS.createDir output
        let result ← IO.Process.output {
          cmd := ".lake/build/bin/leantex"
          args := #[file.toString, "-o", output.toString, "--porcelain", "--werror"]
          env := #[("LEANTEX_FONT", some font.toString)] }
        let records := (result.stdout.splitOn "\n").filterMap fun line =>
          (Lean.Json.parse line).toOption
        let losses := records.filter fun record =>
          record.getObjValAs? String "code" == .ok "W0110"
        t s!"diagnostic output: only selected scopes reach the CLI {name}/{allow}"
          (losses.length == scopes.length && scopes.all fun scope =>
            (losses.filter fun record =>
              record.getObjValAs? String "output" == .ok scope).length == 1)
        t s!"diagnostic output: source and trigger survive the CLI {name}/{allow}"
          (losses.all fun record =>
            record.getObjValAs? String "file" == .ok file.toString &&
            record.getObjValAs? Nat "line" == .ok 5 &&
            record.getObjValAs? String "trigger" == .ok "\\animategraphics")
        t s!"diagnostic output: output filtering precedes exit policy {name}/{allow}"
          (result.exitCode == (if allow then 0 else 1) && result.stderr.isEmpty)
        if allow then
          let accepted := records.filter fun record =>
            record.getObjValAs? String "event" == .ok "accepted"
          t s!"diagnostic output: acceptance counts only selected scopes {name}"
            (accepted.length == 1 && accepted.all fun record =>
              record.getObjValAs? Nat "count" == .ok scopes.length)
        else
          let verdicts := records.filter fun record =>
            (record.getObjVal? "warnings").isOk
          t s!"diagnostic output: warning count includes only selected scopes {name}"
            (verdicts.length == 1 && verdicts.all fun record =>
              record.getObjValAs? Nat "warnings" == .ok scopes.length)
      -- Repeated notices become notes in elaboration. The human footer and
      -- porcelain projection must count the same requested-output records.
      let source ← IO.FS.readFile file
      let animation := "\\animategraphics[width=32pt,alt={Moving square},autoplay,loop,controls]" ++
        "{17}{animation-probe}{}{}\n"
      IO.FS.writeFile file ((source.replace "\\allow{W0110}" "").replace
        "\\end{document}" (animation ++ "\\end{document}"))
      let args := #[file.toString, "-o", (dir / name).toString]
      IO.FS.createDirAll (dir / name)
      let machine ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := args.push "--porcelain", env := #[("LEANTEX_FONT", some font.toString)] }
      let notes := (machine.stdout.splitOn "\n").filter fun line =>
        ((Lean.Json.parse line).bind (·.getObjValAs? String "severity")) == .ok "note"
      let human ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := args.push "--color=never", env := #[("LEANTEX_FONT", some font.toString)] }
      let hint := s!" · {notes.length} {if notes.length == 1 then "note" else "notes"} (-v)"
      t s!"diagnostic output: human note count follows the requested outputs {name}"
        (machine.exitCode == 0 && human.exitCode == 0 && !notes.isEmpty &&
          (human.stderr.splitOn hint).length == 2)

/-- Suite entrypoint: pure text contracts and actual CLI emissions. -/
def diagnosticFormatChecks (ref : IO.Ref (List String)) : IO Unit := do
  diagnosticFormatTextChecks ref
  diagnosticRecordChecks ref
  diagnosticFormatCliChecks ref
  diagnosticOutputCliChecks ref

end Tests
