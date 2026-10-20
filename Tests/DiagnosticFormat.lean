module

public import Tests.Support
public import Lean.Data.Json.Parser
public import Lean.Data.Json

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- The bidirectional formatting characters a terminal line must not carry
raw. -/
private def bidiControls : List Nat :=
  [0x061C, 0x200E, 0x200F] ++ (List.range 5).map (· + 0x202A) ++ (List.range 4).map (· + 0x2066)

private def bidi (c : Char) : Bool := bidiControls.contains c.toNat

/-- A diagnostic's first line carries its effective severity, stable code and optional position, its
continuations one record whatever control characters they carry. -/
def diagnosticFormatTextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let span : Span := ⟨"chapters/example file.tex", { line := 4, col := 7 }⟩
  let d := Diag.of .W0301 "undefined command \\oddity"
    (some span) (help := "define '\\oddity' before using it") (subject := "ctrl:oddity")
  let plain := "chapters/example file.tex:4:7: warning: undefined command \\oddity [W0301]\n" ++
    "  note: define '\\oddity' before using it"
  t "diagnostic format: severity, code and location on the first line"
    (Render.human false d == plain)
  t "diagnostic format: no invented location or suggestion"
    (Render.human false (Diag.of .E0001 "unreadable file doc.tex") ==
      "error: unreadable file doc.tex [E0001]")
  let unicodeSpan : Span := ⟨"résumé [draft].tex", { line := 2, col := 3 }⟩
  t "diagnostic format: Unicode and punctuation in a path survive"
    (Render.human false { d with span := some unicodeSpan, help := none } ==
      "résumé [draft].tex:2:3: warning: undefined command \\oddity [W0301]")
  for (kind, head) in [(DiagCode.E0101, "error"),
      (.W0307, "warning"), (.W0301, "warning"),
      (.W0201, "warning"), (.W0101, "warning"),
      (.N0100, "info")] do
    t s!"diagnostic format: {kind.code} displays severity without an internal category"
      (Render.human false (Diag.of kind "detail") == s!"{head}: detail [{kind.code}]")
  -- Every registry entry takes the same projection, an accepted error's code staying E….
  for kind in DiagCode.all do
    let raw := Diag.of kind "detail"
    for resolved in [raw, (Diag.accept #[raw.code] false raw).1] do
      t s!"diagnostic format: registry/policy projection {raw.code}/{resolved.severity.label}"
        (Render.human false resolved == s!"{resolved.severity.label}: detail [{raw.code}]")
  let accepted := (Diag.accept #["W0301"] false d).1
  t "diagnostic format: accepted loss displays the information icon and retains its code"
    (Render.human false accepted == plain.replace " warning: " " info: ")
  t "diagnostic format: repeated sites keep their total"
    (Render.human false { d with sites := 3 } ==
      plain.replace "[W0301]\n" "[W0301] (3 sites)\n")
  t "diagnostic format: a non-carrier does not acquire a false site count"
    (Render.human false { d with sites := 0 } == plain)
  let multi := Diag.of .E0001 "first\r\nError - not another record\n\nlast\rline\tend\x1b[31m"
    (some ⟨"part\nforged\r\x1b.tex", { line := 1, col := 2 }⟩)
    (help := "run <red>{command}</red>\r\nthen retry\n")
  t "diagnostic format: multiline text is indented and controls cannot forge a record"
    (Render.human false multi ==
      "part\\nforged\\r\\x1b.tex:1:2: error: " ++
      "first\\nError - not another record\\n\\nlast\\rline\\tend\\x1b[31m [E0001]\n" ++
      "  note: run <red>{command}</red>\n    then retry\n    ")
  let controls := String.ofList ['\x00', '\x07', '\x08', '\x7f', '\x85', '\x9b']
  t "diagnostic format: terminal controls are visible text"
    (Render.human false (Diag.of .E0001 controls) ==
      "error: \\x00\\x07\\x08\\x7f\\x85\\x9b [E0001]")
  let statusControls := String.ofList ((List.range 32 ++ (List.range 33).map (· + 127) ++
    [0x2028, 0x2029] ++ bidiControls).map Char.ofNat)
  for color in [false, true] do
    let unstyle := fun (s : String) =>
      ["\x1b[1;32m", "\x1b[1;31m", "\x1b[2m", "\x1b[0m"].foldl
        (fun text code => text.replace code "") s
    let statuses : List (String × (String → String) × (String → String)) :=
      [("summary success", (fun path => Render.humanSummary color path 0 7),
          (fun path => s!"✔ {path} (7 ms)")),
       ("summary error", (fun path => Render.humanSummary color path 2 7),
          (fun path => s!"✖ {path} — 2 errors (7 ms)")),
       ("done", (fun path => Render.humanDone color path (path ++ ".pdf") (some 1) 7),
          (fun path => s!"✔ {path} → {path}.pdf — 1 page (7 ms)")),
       ("done with notes", (fun path => Render.humanDone color path (path ++ ".html") (some 2) 7 1),
          (fun path => s!"✔ {path} → {path}.html — 2 pages (7 ms) · 1 info (-v)")),
       ("done unpaged", (fun path => Render.humanDone color path (path ++ ".html") none 7),
          (fun path => s!"✔ {path} → {path}.html (7 ms)")),
       ("werror", (fun path => Render.humanWerror color path 2 7),
          (fun path => s!"✖ {path} — 2 warnings (--werror) (7 ms)"))]
    for (name, render, expected) in statuses do
      for (path, visible) in
          [("", ""), ("résumé [draft]\\part", "résumé [draft]\\part"),
           ("\r\n\t\x1b[0m\x9b0m\u2028\u2029", "\\r\\n\\t\\x1b[0m\\x9b0m\\u2028\\u2029"),
           ("\u202Etxt.exe\u2066x\u2069\u200F", "\\u202Etxt.exe\\u2066x\\u2069\\u200F")] do
        let actual := render path
        t s!"diagnostic format: {name} preserves visible paths, color={color}"
          (unstyle actual == expected visible && actual.contains '\x1b' == color)
      t s!"diagnostic format: {name} is one safe physical line, color={color}"
        (!(unstyle (render statusControls)).toList.any fun c => c.toNat < 0x20 ||
          (0x7F ≤ c.toNat && c.toNat ≤ 0x9F) || c == '\u2028' || c == '\u2029' || bidi c)
  -- Only the SGR sequences the renderer emits are stripped; other escapes are spelled out as data.
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
      json.replace "\"severity\":\"warning\"" "\"severity\":\"info\"")

/-- The record carries source spelling, recovery and suggested action independently; scope is
identity, and empty or hostile payloads are ordinary data. -/
def diagnosticRecordChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let d := Diag.of .W0301 "command is unknown"
    (some ⟨"example.tex", { line := 4, col := 7 }⟩)
    (help := "define the command") (subject := "ctrl:oddity")
    (refused := "oddity") (trigger := "\\oddity")
    (recovery := some (.replacedBy "its argument text")) (output := some .html)
  let header := "example.tex:4:7: warning: command is unknown [W0301]"
  t "diagnostic record: one line, then the one note: the suggestion over the recovery"
    (Render.human false d == header ++ "\n  note: define the command")
  for (recovery, line) in [(Diag.Recovery.ignored, ""),
      (.skipped, ""), (.replacedBy "plain text", "\n  note: plain text")] do
    t "diagnostic record: without a suggestion, only a replacement is a note"
      (Render.human false { d with recovery := some recovery, help := none } == header ++ line)
  t "diagnostic record: a detail is the note over a suggestion"
    (Render.human false { d with detail := some "at the second site" } ==
      header ++ "\n  note: at the second site")
  t "diagnostic record: no trigger is inferred from subject, refused name or prose"
    (Render.human false { d with
        trigger := none
        recovery := none
        help := none
        output := none
        message := "replaced by: this is only a reason" } ==
      "example.tex:4:7: warning: replaced by: this is only a reason [W0301]")
  let empty := Diag.of .W0301 "" (help := "") (trigger := "")
  t "diagnostic record: absent or empty optional text adds no blank lines"
    (Render.human false empty == "warning: [W0301]" &&
      Render.human false { empty with recovery := some (.replacedBy "") } ==
        "warning: [W0301]")
  let payload := "\\oddity\r\nError - forged\t\x1b[31m\x9b0m\u2028\u2029"
  let hostile := { d with
    trigger := Diag.Spelling.ofWritten? payload
    recovery := some (.replacedBy payload)
    help := none }
  t "diagnostic record: a header names no text that is not one construct token"
    ((Diag.Spelling.ofWritten? payload).isNone &&
      (Render.human false hostile).splitOn "\n" ==
        [header, "  note: \\oddity",
          "    Error - forged\\t\\x1b[31m\\x9b0m\\u2028\\u2029"])
  -- A control symbol is one token whatever follows its backslash; the line names it only in words.
  for (c, shown) in [('\x1b', "\\x1b"), ('\r', "\\r"), ('\n', "\\n"),
      ('\x9b', "\\x9b"), ('\u2028', "\\u2028"), ('\u2029', "\\u2029")] do
    let symbol := "\\".push c
    let carried := { d with trigger := Diag.Spelling.ofWritten? symbol, recovery := none, help := none }
    t s!"diagnostic record: a control symbol's trigger {shown} stays out of the line"
      ((Diag.Spelling.ofWritten? symbol).isSome &&
        (Render.human false carried).splitOn "\n" == [header])
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
  -- Every text field round-trips empty and with all terminal controls through a real JSON reader.
  let controls := String.ofList ((List.range 32 ++ (List.range 33).map (· + 127) ++
    [0x2028, 0x2029] ++ bidiControls).map Char.ofNat)
  for text in ["", "\"\\" ++ controls] do
    let sample := Diag.of .W0301 text
      (some ⟨text, { line := 0, col := 0 }⟩) (help := text) (subject := text)
      (trigger := text) (recovery := some (.replacedBy text)) (output := some .pdf)
      (detail := text)
    let encoded := Render.porcelainDiag sample
    let parsed := Lean.Json.parse encoded
    for key in ["message", "file", "help", "subject", "detail"] do
      let actual := parsed.bind fun j => (j.getObjVal? key).bind Lean.Json.getStr?
      t s!"diagnostic record: JSON round-trip {key}" (actual.toOption == some text)
    t "diagnostic record: text that spells no construct is no trigger"
      ((parsed.bind fun j => j.getObjVal? "trigger").toOption.isNone)
    let actual := parsed.bind fun j => (j.getObjVal? "recovery").bind fun r =>
      (r.getObjVal? "replacement").bind Lean.Json.getStr?
    t "diagnostic record: JSON round-trip empty or hostile replacement"
      (actual.toOption == some text)
    let output := parsed.bind fun j => (j.getObjVal? "output").bind Lean.Json.getStr?
    t "diagnostic record: JSON retains output scope" (output.toOption == some "pdf")
    t "diagnostic record: JSON is one safe physical line"
      (!encoded.toList.any fun c => c.toNat < 0x20 ||
        (0x7F ≤ c.toNat && c.toNat ≤ 0x9F) || c == '\u2028' || c == '\u2029' || bidi c)
  let pdf := { d with output := some .pdf }
  let html := { d with output := some .html }
  let common := { d with output := none }
  let ds := #[pdf, html, pdf, common, html]
  for raw in [pdf, html, common, Diag.demote d] do
    let plain := Render.human false raw
    let scope := raw.output.map (fun output => s!" ({output.label.toUpper})") |>.getD ""
    let expected := plain.replace s!"[{raw.code}]" s!"[{raw.code}]{scope}"
    t "diagnostic record: only multi-output presentation adds a format label"
      (Render.human false raw (showOutput := false) == plain &&
        Render.human false raw (showOutput := true) == expected)
    let colored := Render.human true raw (showOutput := true)
    let stripped := ["\x1b[1;31m", "\x1b[1;33m", "\x1b[1;36m", "\x1b[1;34m",
      "\x1b[1m", "\x1b[0m"].foldl (fun s code => s.replace code "") colored
    t "diagnostic record: multi-output color adds no content"
      (stripped == expected && !stripped.contains '\x1b')
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
    ((DriverDiag.boundarySvgMissing "leantex-pic:probe" (.unconverted "unavailable")).output ==
        some .html &&
      (DriverDiag.htmlResourceUnavailable "missing resource").output == some .html)

/-- The built CLI's stderr, stream routing and exits on malformed synthetic inputs; a warning fires
beside a fatal error. -/
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
    -- Only an unreadable input stops the run before anything is written: bytes never do.
    let unreadable := (dir / "folder.tex").toString
    IO.FS.createDir unreadable
    let bad ← run #["dump", unreadable, "--color=never"]
    t "diagnostic format: an unreadable input separates the code from its reason and keeps failure exit"
      (bad.exitCode == 1 && bad.stdout.isEmpty &&
        bad.stderr.startsWith s!"error: unreadable file {unreadable} [E0001]\n  note: " &&
        (bad.stderr.splitOn "\n").length == 3)
    let porcelain ← run #["dump", unreadable, "--porcelain"]
    let records := (porcelain.stdout.splitOn "\n").filter (!·.isEmpty)
    t "diagnostic format: emitted porcelain stays JSONL on stdout"
      (porcelain.exitCode == 1 && porcelain.stderr.isEmpty && records.length == 1 &&
        records.all fun line => (Lean.Json.parse line).toOption.any fun j =>
          j.getObjValAs? String "code" == .ok "E0001" &&
          j.getObjValAs? String "severity" == .ok "error")
    -- A replaced byte is no construct, so the header quotes no text.
    let face ← IO.FS.realPath (testFonts ++ "/OpenSans-Regular.ttf")
    let runFace (args : Array String) := IO.Process.output {
      cmd := ".lake/build/bin/leantex", args := args
      env := #[("LEANTEX_FONT", some face.toString)] }
    let shipped := (dir / "invalid.html").toString
    let human ← runFace #[file, "-o", shipped, "--color=never", "-q"]
    let words := Diag.say .W0002 .character (obj := some (some .file, Diag.Name.of file))
    t "diagnostic format: a located loss is one line, its detail the one note"
      (human.exitCode == 0 && human.stdout.isEmpty && human.stderr.startsWith
        (s!"{file}:1:1: warning: {words} [W0002]\n" ++
          "  note: not text in UTF-8: byte 0xFF at offset 0\n"))
    let machine ← runFace #[file, "-o", shipped, "--porcelain"]
    t "diagnostic format: a located loss stays JSONL on stdout"
      (machine.exitCode == 0 && machine.stderr.isEmpty && machine.stdout.startsWith
        ("{\"event\":\"diagnostic\",\"severity\":\"warning\",\"code\":\"W0002\"," ++
          "\"loss\":\"degraded\",\"message\":\"" ++
            Diag.say .W0002 .character (obj := some (some .file, Diag.Name.of file)) ++ "\"," ++
          "\"file\":\"" ++ file ++ "\",\"line\":1,\"col\":1,"))
    let usage ← run #["--not-a-flag"]
    t "diagnostic format: parser-independent argument errors keep their established output"
      (usage.exitCode == 3 && usage.stdout.isEmpty && usage.stderr ==
        "leantex: unknown flag '--not-a-flag'\ntry 'leantex --help'\n")
    let machineUsage ← run #["--porcelain", "--not-a-flag"]
    t "diagnostic format: argument errors preserve porcelain-mode stderr"
      (machineUsage.exitCode == 3 && machineUsage.stdout.isEmpty && machineUsage.stderr ==
        "leantex: unknown flag '--not-a-flag'\ntry 'leantex --help'\n")
    -- An output name no format reads is a typed refusal, not an argument error.
    let output := (dir / "output.bad").toString
    let dest ← run #[file, "-o", output, "--color=never"]
    t "diagnostic format: an output name no format reads renders as E0006 and keeps usage exit"
      (dest.exitCode == 3 && dest.stdout.isEmpty && dest.stderr.startsWith
        (s!"error: unsupported output {output} [E0006]\n" ++
          "  note: name an output file ending in '.pdf', '.html' or '.md' with -o, " ++
          "or a directory ending in '/'\n"))
    let machineDest ← run #[file, "-o", output, "--porcelain"]
    let destRecords := (machineDest.stdout.splitOn "\n").filter (!·.isEmpty)
    t "diagnostic format: an output name no format reads stays JSONL on stdout"
      (machineDest.exitCode == 3 && machineDest.stderr.isEmpty &&
        destRecords.all (fun line => (Lean.Json.parse line).toOption.isSome) &&
        (destRecords.filter fun line => (Lean.Json.parse line).toOption.any fun j =>
          j.getObjValAs? String "code" == .ok "E0006").length == 1)
    let triggered := dir / "triggered.tex"
    IO.FS.writeFile triggered ("\\documentclass{article}\n\\directlua{local value = 1}\n" ++
      "\\begin{document}\n}\n\\end{document}\n")
    let human ← run #[triggered.toString, "--color=never"]
    t "diagnostic format: a compatibility warning leads with its location"
      (human.exitCode == 1 && (human.stderr.splitOn "\n").any fun line =>
        line.startsWith s!"{triggered}:2:1: warning: " && (line.splitOn "[W0104]").length == 2 &&
          (line.splitOn "\\directlua").length == 2)
    t "diagnostic format: a run shipping beside its errors counts the pages it wrote"
      ((human.stderr.splitOn "\n").any fun l =>
        l.startsWith s!"✖ {triggered} — 1 error; wrote " && (l.splitOn ".pdf, 1 page (").length == 2)
    let machine ← run #[triggered.toString, "--porcelain"]
    t "diagnostic format: the porcelain summary of a run shipping beside its errors counts its pages"
      ((machine.stdout.splitOn "\n").any fun line => (Lean.Json.parse line).toOption.any fun j =>
        j.getObjValAs? String "event" == .ok "summary" && j.getObjValAs? Nat "pages" == .ok 1 &&
          j.getObjValAs? Nat "errors" == .ok 1)
    let warnings := (machine.stdout.splitOn "\n").filterMap fun line =>
      (Lean.Json.parse line).toOption |>.filter (·.getObjValAs? String "code" == .ok "W0104")
    t "diagnostic format: a compatibility warning preserves structured source evidence"
      (machine.exitCode == 1 && warnings.length == 1 && warnings.all fun record =>
        record.getObjValAs? String "file" == .ok triggered.toString &&
        record.getObjValAs? Nat "line" == .ok 2 &&
        record.getObjValAs? String "trigger" == .ok "\\directlua")
    let font ← IO.FS.realPath (testFonts ++ "/OpenSans-Regular.ttf")
    for command in ["\\style{itemize}{marker={\\includegraphics{missing.png}}}",
        "\\setbeamertemplate{itemize item}{\\includegraphics{missing.png}}"] do
      let marker := dir / "marker.tex"
      IO.FS.writeFile marker ("\\documentclass{article}\n\n" ++ command ++ "\n" ++
        "\\begin{document}\\begin{itemize}\\item body\\end{itemize}\\end{document}")
      let result ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := #[marker.toString, "-o", (dir / "marker.html").toString, "--porcelain"]
        env := #[("LEANTEX_FONT", some font.toString)] }
      let records := (result.stdout.splitOn "\n").filterMap fun line =>
        (Lean.Json.parse line).toOption
      let trigger := (command.splitOn "{").head!
      for code in ["W0331", "W0601"] do
        let losses := records.filter (·.getObjValAs? String "code" == .ok code)
        t s!"diagnostic format: delayed marker loss keeps its written declaration {trigger}/{code}"
          (result.exitCode == 0 && losses.length == 1 && losses.all fun record =>
            record.getObjValAs? String "file" == .ok marker.toString &&
            record.getObjValAs? Nat "line" == .ok 3 &&
            record.getObjValAs? String "trigger" == .ok trigger)
    let source := (dir / "example.tex").toString
    for allow in [false, true] do
      IO.FS.writeFile source ("\\documentclass{article}\n" ++
        (if allow then "\\allow{W0301}\n" else "\n") ++
        "\\begin{document}\n\\oddity{kept}\n}\n\\end{document}\n")
      for verbose in [false, true] do
        let result ← run (#[source, "--color=never"] ++
          if verbose then #["-v"] else #["-q"])
        let lines := result.stderr.splitOn "\n"
        let expected := s!"{source}:4:1: {if allow then "info" else "warning"}: " ++
          "unknown command '\\oddity'; its {...} arguments were kept as text [W0301]"
        t s!"diagnostic format: emitted warning and acceptance {allow}/{verbose}"
          (result.exitCode == 1 && result.stdout.isEmpty &&
           if !allow || verbose then (result.stderr.splitOn expected).length == 2 &&
             lines.contains "  note: \\define \\name(...) {body} declares it"
           else lines.all fun line => (line.splitOn "[W0301]").length ≤ 1)
        t s!"diagnostic format: fatal error is never suppressed {allow}/{verbose}"
          (lines.any fun line =>
            line.startsWith s!"{source}:5:1: error: " && (line.splitOn "[E0202]").length == 2)

/-- Output scope is resolved by the real output plan before warning counts, acceptance and printing. -/
def diagnosticOutputCliChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let font ← IO.FS.realPath (testFonts ++ "/OpenSans-Regular.ttf")
  let image ← IO.FS.readBinFile "testdata/corpus/rects.png"
  IO.FS.withTempDir fun dir => do
    IO.FS.writeBinFile (dir / "animation-probe.png") image
    let file := dir / "scope.tex"
    for (name, formats, scopes) in [("pdf", ["pdf"], ["pdf"]),
        ("html", ["html"], ["html"]), ("both", ["pdf", "html"], ["pdf", "html"]),
        ("pdf-markdown", ["pdf", "md"], ["pdf"]),
        ("html-markdown", ["html", "md"], ["html"])] do
      for allow in [false, true] do
        let formats := String.intercalate "," formats
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
      -- The human footer and the porcelain projection count the same requested-output records.
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
        ((Lean.Json.parse line).bind (·.getObjValAs? String "severity")) == .ok "info"
      let human ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := args.push "--color=never", env := #[("LEANTEX_FONT", some font.toString)] }
      let hint := s!" · {notes.length} info (-v)"
      t s!"diagnostic output: summary counts hidden notes for the requested outputs {name}"
        (machine.exitCode == 0 && human.exitCode == 0 && !notes.isEmpty &&
          (human.stderr.splitOn hint).length == 2)
      let headers := (human.stderr.splitOn "\n").filter fun line =>
        line.startsWith s!"{file}:5:1: warning: " && (line.splitOn "[W0110]").length == 2
      t s!"diagnostic output: only a multi-output run labels its warnings by format {name}"
        (headers.length == scopes.length && scopes.all fun scope =>
          headers.any fun line =>
            let labelled := (line.splitOn s!"[W0110] ({scope.toUpper})").length == 2
            if formats.length > 1 then labelled else !labelled)
      t s!"diagnostic output: routine notes stay hidden without verbose output {name}"
        (!(human.stderr.splitOn "\n").any fun line => (line.splitOn ": info: ").length > 1)
      let verbose ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := args ++ #["--color=never", "-v"]
        env := #[("LEANTEX_FONT", some font.toString)] }
      t s!"diagnostic output: verbose output shows notes instead of the hidden-note count {name}"
        (verbose.exitCode == 0 &&
          ((verbose.stderr.splitOn "\n").filter fun line =>
            (line.splitOn ": info: ").length > 1).length == notes.length &&
          (verbose.stderr.splitOn " (-v)").length == 1)

/-- Suite entrypoint: pure text contracts and actual CLI emissions. -/
def diagnosticFormatChecks (ref : IO.Ref (List String)) : IO Unit := do
  diagnosticFormatTextChecks ref
  diagnosticRecordChecks ref
  diagnosticFormatCliChecks ref
  diagnosticOutputCliChecks ref

end Tests
