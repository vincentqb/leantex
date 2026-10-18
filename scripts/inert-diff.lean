import Tests.InertProbes

/-! Inert-row oracle: each asWithout row set by LuaLaTeX with, without and against a contrast,
word boxes compared, colour and ink without words unseen.
Usage: lake build Tests.InertProbes && lake env lean --run scripts/inert-diff.lean -/

open LeanTex.Core

/-- The word boxes and page count of a PDF, as Poppler's `-bbox` reads them, metadata aside. -/
def wordBoxes (pdf : System.FilePath) : IO String := do
  let r ← IO.Process.output { cmd := "pdftotext", args := #["-bbox", pdf.toString, "-"] }
  if r.exitCode != 0 then throw <| IO.userError s!"pdftotext failed on {pdf}"
  return "\n".intercalate ((r.stdout.splitOn "\n").filter fun l =>
    !(l.trimAscii.toString.startsWith "<meta") && !(l.trimAscii.toString.startsWith "<title"))

/-- One build of `src` in `dir`, its word boxes or why it failed. -/
def build (dir : System.FilePath) (src : String) (env : Array (String × Option String)) :
    IO (Except String String) := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "probe.tex") src
  let r ← IO.Process.output {
    cmd := "lualatex"
    args := #["-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "probe.tex"]
    cwd := some dir
    env }
  if r.exitCode != 0 then return .error s!"lualatex exited {r.exitCode}"
  -- A second run resolves the references the first wrote.
  let r ← IO.Process.output {
    cmd := "lualatex"
    args := #["-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "probe.tex"]
    cwd := some dir
    env }
  if r.exitCode != 0 then return .error s!"lualatex exited {r.exitCode}"
  return .ok (← wordBoxes (dir / "probe.pdf"))

def main : IO UInt32 := do
  IO.FS.withTempDir fun root => do
    let cache := root / "cache"
    IO.FS.createDirAll cache
    let env := #[("TEXMFCACHE", some cache.toString), ("TEXMFVAR", some cache.toString)]
    let mut differ : Array String := #[]
    let mut failed : Array String := #[]
    for (p, i) in Tests.inertProbes.zipIdx do
      let a ← build (root / s!"{i}-with") p.withIt env
      let b ← build (root / s!"{i}-without") p.without env
      let label := s!"{p.reader} [{p.setting}]"
      let c ← match p.contrast with
        | some src => (some ·) <$> build (root / s!"{i}-contrast") src env
        | none => pure none
      match a, b with
      | .ok x, .ok y =>
        let seen := match c with
          | some (.ok z) => if z == y then " (its contrast is unseen)" else " (its contrast differs)"
          | some (.error e) => s!" (its contrast failed: {e})"
          | none => ""
        if x == y then IO.println s!"same    {label}{seen}"
        else
          IO.println s!"DIFFERS {label}"
          differ := differ.push label
      | .error e, _ | _, .error e =>
        IO.println s!"FAILED  {label}: {e}"
        failed := failed.push label
    IO.println s!"inert-diff: {Tests.inertProbes.length} probes, {differ.size} differ, {failed.size} failed"
    return (if differ.isEmpty && failed.isEmpty then 0 else 1)
