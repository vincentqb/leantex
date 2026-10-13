import Tests.PackageOptions

/-! Package-option oracle: literal option scheduling over a real local .sty, judged on Layout.Out
and HTML, and the same invented styles under LuaLaTeX.
Usage: lake build Tests.PackageOptions && lake env lean --run scripts/package-options.lean [--engine-only] -/

open LeanTex.Core

private def referenceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let version ← IO.Process.output { cmd := "lualatex", args := #["--version"] }
  if version.exitCode != 0 then
    throw <| IO.userError "lualatex --version failed"
  IO.println ((version.stdout.splitOn "\n").headD "LuaLaTeX")
  IO.FS.withTempDir fun root => do
    let cache := root / "cache"
    IO.FS.createDirAll cache
    let env := #[("TEXMFCACHE", some cache.toString), ("TEXMFVAR", some cache.toString)]
    let buildSource (name style source : String) := do
      let dir := root / name
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir / "pkgoptionsprobe.sty") (Tests.packageOptionStyle style)
      IO.FS.writeFile (dir / "pkgoptionschild.sty") Tests.packageOptionChildStyle
      IO.FS.writeFile (dir / "host.tex") source
      let result ← IO.Process.output {
        cmd := "lualatex"
        args := #["-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "host.tex"]
        cwd := some dir
        env }
      return (dir, result)
    let build (name style passed body : String) :=
      buildSource name style (Tests.packageOptionSource passed body)
    let checkText (name expected : String) (dir : System.FilePath) := do
      let text ← IO.Process.output {
        cmd := "pdftotext"
        args := #["-enc", "UTF-8", (dir / "host.pdf").toString, "-"] }
      -- Only the extractor's page separator and trailing newline go; inner spaces are significant.
      let actual := (text.stdout.replace "\x0c" "").trimAscii.toString
      t s!"LuaLaTeX {name}: PDF text '{actual}' = '{expected}'"
        (text.exitCode == 0 && actual == expected)
    for c in Tests.packageOptionCases do
      let (dir, result) ← build c.name c.style c.passed c.body
      t s!"LuaLaTeX {c.name}: builds" (result.exitCode == 0)
      if result.exitCode == 0 then
        checkText c.name c.expected dir
      else
        IO.eprintln result.stdout
    for c in Tests.packageOptionDiagCases do
      let (dir, result) ← buildSource ("diag-" ++ c.name) c.style (Tests.packageOptionDiagSource c)
      if c.unhandled.isEmpty then
        t s!"LuaLaTeX {c.name}: no unknown-option error" (result.exitCode == 0)
        if result.exitCode == 0 then checkText c.name c.expected dir
        else IO.eprintln result.stdout
      else
        t s!"LuaLaTeX {c.name}: unknown option is rejected"
          (result.exitCode != 0 && hasStr result.stdout "Unknown option")
    IO.println s!"LuaLaTeX: {Tests.packageOptionCases.size} scheduling cases; \
{Tests.packageOptionDiagCases.size} diagnostic/lifecycle cases"

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty || args == ["--engine-only"] do
    IO.eprintln "usage: lake env lean --run scripts/package-options.lean [--engine-only]"
    return 2
  let ref ← IO.mkRef (← Tests.packageOptionFailures)
  let engineFailures := (← ref.get).length
  IO.println s!"Layout/HTML: {Tests.packageOptionCases.size} scheduling cases, \
3 selected and 3 unselected refusal cases, \
{Tests.packageOptionDiagCases.size} diagnostic/lifecycle cases; {engineFailures} failed assertions"
  unless args.contains "--engine-only" do referenceChecks ref
  let failed := (← ref.get).reverse
  for failure in failed do IO.eprintln failure
  IO.println s!"package options: {failed.length} failed assertions"
  return if failed.isEmpty then 0 else 1
