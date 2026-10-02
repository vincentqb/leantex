import Tests.Support

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
  let plain := "Warning - Degraded [W0301] - chapters/example file.tex:4:7 - " ++
    "unknown command '\\oddity'; its text is kept\n  help: define '\\oddity' before using it"
  t "diagnostic format: location and fixed category on the first line"
    (Render.human false d == plain)
  t "diagnostic format: no invented location or help"
    (Render.human false (Diag.of .E0001 "cannot read input") ==
      "Error - Dropped [E0001] - cannot read input")
  let unicodeSpan : Span := ⟨"résumé [draft].tex", { line := 2, col := 3 }⟩
  t "diagnostic format: Unicode and punctuation in a path survive"
    (Render.human false { d with span := some unicodeSpan, help := none } ==
      "Warning - Degraded [W0301] - résumé [draft].tex:2:3 - " ++
      "unknown command '\\oddity'; its text is kept")
  for (kind, head) in [(DiagCode.E0101, "Error - Dropped [E0101]"),
      (.W0307, "Warning - Pending [W0307]"), (.W0301, "Warning - Degraded [W0301]"),
      (.W0201, "Warning - Standard [W0201]"), (.W0101, "Warning - Config [W0101]"),
      (.N0100, "Note - Info [N0100]")] do
    t s!"diagnostic format: {kind.code} displays its declared category"
      (Render.human false (Diag.of kind "detail") == head ++ " - detail")
  -- Future registry entries must take the same projection, including an
  -- accepted error whose effective severity is a note but code stays E….
  for kind in DiagCode.all do
    let raw := Diag.of kind "detail"
    for resolved in [raw, (Diag.accept #[raw.code] false raw).1] do
      let head := s!"{resolved.severity.label.capitalize} - {kind.loss.label.capitalize} [{raw.code}]"
      t s!"diagnostic format: registry/policy projection {raw.code}/{resolved.severity.label}"
        (Render.human false resolved == head ++ " - detail")
  let accepted := (Diag.accept #["W0301"] false d).1
  t "diagnostic format: accepted loss retains code and category"
    (Render.human false accepted == plain.replace "Warning - " "Note - ")
  t "diagnostic format: repeated sites keep their total"
    (Render.human false { d with sites := 3 } ==
      plain.replace "its text is kept\n" "its text is kept (3 sites)\n")
  t "diagnostic format: a non-carrier does not acquire a false site count"
    (Render.human false { d with sites := 0 } == plain)
  let multi := Diag.of .E0001 "first\r\nError - not another record\n\nlast\rline\tend\x1b[31m"
    (some ⟨"part\nforged\r\x1b.tex", { line := 1, col := 2 }⟩)
    (help := "run <red>{command}</red>\r\nthen retry\n")
  t "diagnostic format: multiline text is indented and controls cannot forge a record"
    (Render.human false multi ==
      "Error - Dropped [E0001] - part\\nforged\\r\\x1b.tex:1:2 - " ++
      "first\n  Error - not another record\n  \n  last\\rline\\tend\\x1b[31m\n" ++
      "  help: run <red>{command}</red>\n    then retry\n    ")
  let controls := String.ofList ['\x00', '\x07', '\x08', '\x7f', '\x85', '\x9b']
  t "diagnostic format: terminal controls are visible text"
    (Render.human false (Diag.of .E0001 controls) ==
      "Error - Dropped [E0001] - \\x00\\x07\\x08\\x7f\\x85\\x9b")
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
    t "diagnostic format: emitted error has inline location, help, newline and failure exit"
      (bad.exitCode == 1 && bad.stdout.isEmpty && bad.stderr ==
        s!"Error - Dropped [E0002] - {file}:1:1 - invalid UTF-8: invalid start byte 0xFF at byte offset 0\n" ++
        "  help: every input is read as UTF-8; `iconv -t utf-8` re-encodes the file\n")
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
        let expected := s!"{if allow then "Note" else "Warning"} - Degraded [W0301] - {source}:4:1 - " ++
          "unknown command '\\oddity'; its {...} arguments were kept as text"
        t s!"diagnostic format: emitted warning and acceptance {allow}/{verbose}"
          (result.exitCode == 1 && result.stdout.isEmpty &&
           if !allow || verbose then lines.contains expected &&
             lines.contains "  help: \\define \\name(...) {body} declares it"
           else lines.all fun line => (line.splitOn "[W0301]").length ≤ 1)
        t s!"diagnostic format: fatal error is never suppressed {allow}/{verbose}"
          (lines.any (·.startsWith s!"Error - Dropped [E0202] - {source}:5:1 - "))

/-- Suite entrypoint: pure text contracts and actual CLI emissions. -/
def diagnosticFormatChecks (ref : IO.Ref (List String)) : IO Unit := do
  diagnosticFormatTextChecks ref
  diagnosticFormatCliChecks ref

end Tests
