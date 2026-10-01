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
global class options or PassOptionsToPackage. Unknown caller options with
no catch-all are a measured API gap: LuaLaTeX errors, but the current
array-only resolver cannot return a diagnostic. The negative reference
probe below records that boundary without certifying silent omission.
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
    let build (name style passed body : String) := do
      let dir := root / name
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir / "pkgoptionsprobe.sty") (Tests.packageOptionStyle style)
      IO.FS.writeFile (dir / "host.tex") (Tests.packageOptionSource passed body)
      let result ← IO.Process.output {
        cmd := "lualatex"
        args := #["-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "host.tex"]
        cwd := some dir
        env }
      return (dir, result)
    for c in Tests.packageOptionCases do
      let (dir, result) ← build c.name c.style c.passed c.body
      t s!"LuaLaTeX {c.name}: builds" (result.exitCode == 0)
      if result.exitCode == 0 then
        let text ← IO.Process.output {
          cmd := "pdftotext"
          args := #["-enc", "UTF-8", (dir / "host.pdf").toString, "-"] }
        -- Remove only the extractor's page separator and trailing newline;
        -- spaces within the rendered text remain significant.
        let actual := (text.stdout.replace "\x0c" "").trimAscii.toString
        t s!"LuaLaTeX {c.name}: PDF text '{actual}' = '{c.expected}'"
          (text.exitCode == 0 && actual == c.expected)
      else
        IO.eprintln result.stdout
    let (_, result) ← build "unknown-without-catch-all"
      (Tests.packageOptionDeclare "a" "A" ++ "\\ProcessOptions\\relax") "u" "Tail"
    t "LuaLaTeX unknown option without catch-all: error"
      (result.exitCode != 0 && hasStr result.stdout "Unknown option")
    IO.println s!"LuaLaTeX: {Tests.packageOptionCases.size} positive cases; \
1 unknown-option error boundary"

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty || args == ["--engine-only"] do
    IO.eprintln "usage: lake env lean --run scripts/package-options.lean [--engine-only]"
    return 2
  let some bytes ← findFont | throw <| IO.userError "shipped fixture font is missing"
  let .ok font := Font.parse bytes | throw <| IO.userError "shipped fixture font is invalid"
  let ref ← IO.mkRef ([] : List String)
  Tests.packageOptionChecks ref (oneFaceOf font)
  let engineFailures := (← ref.get).length
  IO.println s!"Layout/HTML: {Tests.packageOptionCases.size} scheduling cases, \
3 selected and 3 unselected refusal cases; {engineFailures} failed assertions"
  unless args.contains "--engine-only" do referenceChecks ref
  let failed := (← ref.get).reverse
  for failure in failed do IO.eprintln failure
  IO.println s!"package options: {failed.length} failed assertions"
  return if failed.isEmpty then 0 else 1
