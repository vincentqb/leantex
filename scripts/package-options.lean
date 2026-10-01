import Tests.PackageOptions

/-!
Synthetic package-option oracle, independent of installed style packages.
Build the imports before running:

  lake build Tests.PackageOptions
  lake env lean --run scripts/package-options.lean [--engine-only]

The engine check loads a real local .sty and judges Layout.Out and typed
HTML. The reference check builds the same invented styles with LuaLaTeX
and reads their PDF text with pdftotext. Both compare against committed
expectations, never against an answer produced by the resolver. TeX needs
only its kernel/article class; all package files and caches are temporary.

This checks literal scheduling, not arbitrary TeX expansion, CurrentOption,
global class options or PassOptionsToPackage. Unknown caller options without
a handler, or left unprocessed, must raise W0110 in the engine. LuaLaTeX
rejects those sources; the engine ships the independently specified control
page with that loss named, rather than claiming an error-free TeX build.
-/

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
      -- Remove only the extractor's page separator and trailing newline;
      -- spaces within the rendered text remain significant.
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
