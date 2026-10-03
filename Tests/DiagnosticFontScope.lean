import Tests.Artifact
import Lean.Data.Json.Parser

namespace Tests

private def fontScopeString (j : Lean.Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

private def fontScopeCount (j : Lean.Json) (key : String) : Nat :=
  (j.getObjValAs? Nat key).toOption.getD 0

/-- Native glyph decisions describe the PDF alone. The CLI must filter them
before refusal, acceptance and `--werror` counts; HTML and Markdown retain
Unicode even when a native face cannot paint it. Read the emitted paragraph
and the PDF's painted text, not IR or diagnostic silence alone.

E0405 uses the single vendored `LEANTEX_FONT` override. W0009 needs two faces
(the override deliberately has no fallback): every slot variant is explicitly
bound to one of two vendored faces, and every input scalar is covered there.
No Main import: registration may use the default binary; fail-first runs can
pass a saved integration executable. -/
def diagnosticFontScopeChecks (ref : IO.Ref (List String))
    (executable : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let binary ← IO.FS.realPath executable
  let corpus ← IO.FS.realPath "tests/corpus/fonts"
  IO.FS.withTempDir fun dir => do
    let fonts := dir / "fonts"
    IO.FS.createDirAll fonts
    for file in ["OpenSans-Regular.ttf", "SourceCodePro-Regular.otf"] do
      IO.FS.writeBinFile (fonts / file) (← IO.FS.readBinFile (corpus / file))
    let variants := [("body", "OpenSans-Regular"), ("mono", "SourceCodePro-Regular")].flatMap
      fun (slot, face) => ["upright", "bold", "italic", "bolditalic"].map
        fun variant => s!"{slot}.{variant}=\"{face}\""
    let declaration := "\\fonts{dir=\"fonts\", body=\"Open Sans\", mono=\"Source Code Pro\", " ++
      String.intercalate ", " variants ++ "}"
    let outputs : List (String × String × List String) := [
      ("pdf", "formats=pdf", ["pdf"]),
      ("embedded", "formats=html, fonts=embedded", ["html"]),
      ("own", "formats=html, css=own", ["html"]),
      ("none", "formats=html, fonts=none", ["html"]),
      ("md", "formats=md", ["md"]),
      ("mixed", "formats=pdf, html, fonts=embedded", ["pdf", "html"])]
    for fallback in [false, true] do
      let code := if fallback then "W0009" else "E0405"
      let glyph := if fallback then "∀" else "⟨"
      let paragraph := s!"Before {glyph} after."
      for (name, output, formats) in outputs do
        -- Two acceptance pairs suffice: a real PDF loss and a stale HTML allow.
        for allow in (if name == "mixed" || name == "embedded" then [false, true]
            else [false]) do
          let before := (← ref.get).length
          let label := s!"{code}/{name}/{if allow then "allow" else "strict"}"
          let t := fun why ok => check ref s!"diagnostic fonts {label}: {why}" ok
          let stem := s!"{code}-{name}-{if allow then "allow" else "strict"}"
          let source := dir / (stem ++ ".tex")
          let outDir := dir / (stem ++ "-out")
          IO.FS.writeFile source (String.intercalate "\n" [
            "\\documentclass{article}", if fallback then declaration else "",
            "\\output{" ++ output ++ "}", if allow then "\\allow{" ++ code ++ "}" else "",
            "\\begin{document}", paragraph, "\\end{document}", ""])
          let p ← IO.Process.output {
            cmd := binary.toString
            args := #[source.toString, "-o", outDir.toString ++ "/", "--porcelain", "--werror"]
            cwd := some dir
            env := #[("LEANTEX_FONT", some (fonts / "OpenSans-Regular.ttf").toString),
              ("LEANTEX_FONT_PATH", none), ("XDG_CACHE_HOME", some (dir / "cache").toString),
              ("HOME", some (dir / "home").toString), ("PATH", some (dir / "no-tools").toString)] }
          let lines := p.stdout.splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
          let records := lines.filterMap (Lean.Json.parse · |>.toOption)
          t "all stdout records parse" (lines.length == records.length)
          let diags := records.filter (fontScopeString · "event" == "diagnostic")
          let native := formats.contains "pdf"
          let stale := allow && !native
          let blocked := native && !fallback && !allow
          let warnings := if stale || (native && fallback && !allow) then 1 else 0
          let reports := diags.filter (fontScopeString · "code" == code)
          t "only requested PDF glyph decisions are reported"
            (reports.length == (if native then 1 else 0) &&
             diags.length == (if native || stale then 1 else 0) &&
             (!stale || diags.all (fontScopeString · "code" == "W0013")))
          t "native records have PDF scope and the real triggering source"
            (reports.all fun d => fontScopeString d "output" == "pdf" &&
              fontScopeString d "file" == source.toString && fontScopeCount d "line" == 6 &&
              fontScopeCount d "col" == 8 && fontScopeString d "trigger" == glyph &&
              fontScopeString d "severity" == (if allow then "note"
                else if fallback then "warning" else "error"))
          let accepted := records.filter (fontScopeString · "event" == "accepted")
          t "acceptance counts only a requested PDF loss"
            (accepted.length == (if native && allow then 1 else 0) && accepted.all fun a =>
              let codes := (a.getObjValAs? (Array Lean.Json) "codes").toOption.getD #[]
              fontScopeCount a "count" == 1 && codes.size == 1 && codes.all
                (fun c => fontScopeString c "code" == code && fontScopeCount c "count" == 1))
          let summary := (records.filter (fontScopeString · "event" == "summary")).getLast?
          let failed := blocked || warnings > 0
          t "exit and final counts follow scope before policy"
            (p.exitCode == (if failed then 1 else 0) &&
              (summary.bind fun s => (s.getObjValAs? Bool "ok").toOption) == some (!failed) &&
              (summary.bind fun s => (s.getObjValAs? Nat "errors").toOption) ==
                some (if blocked then 1 else 0) &&
              (summary.map (fontScopeCount · "warnings")).getD 0 == warnings)
          for format in formats do
            let artifact := outDir / (stem ++ "." ++ format)
            let written ← artifact.pathExists
            t s!"{format} publication precedes werror but follows error refusal" (written == !blocked)
            if written && !blocked then
              if format == "pdf" then
                match readArtifact (← IO.FS.readBinFile artifact) with
                | .error err => t s!"PDF painted-text reader: {err}" false
                | .ok pages =>
                  let text := pages.foldl (fun acc page =>
                    page.runs.foldl (fun s run => s ++ run.text) acc) ""
                  t "PDF paints surrounding words and exactly the available glyph"
                    (hasStr text "Before" && hasStr text "after." && hasStr text glyph == fallback)
              else
                let text ← IO.FS.readFile artifact
                t s!"{format} retains the Unicode paragraph"
                  (hasStr text (if format == "html" then ">" ++ paragraph ++ "</p>" else paragraph))
                if format == "html" then
                  t "HTML uses the declared embedding policy"
                    (hasStr text "@font-face" == hasStr output "fonts=embedded")
          if (← ref.get).length > before then
            IO.eprintln s!"diagnostic fonts {label}: exit={p.exitCode}\n{p.stdout}{p.stderr}"

end Tests
