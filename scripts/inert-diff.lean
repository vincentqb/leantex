import Tests.InertProbes

/-! Inert-row oracle: each asWithout row and inline site set by LuaLaTeX with, without and against a
contrast, judged by word boxes and visualdiff; minted runs under the restricted shell escape.
Usage: lake env lean --run scripts/inert-diff.lean [--python <path>] [--only <reader>] -/

open LeanTex.Core

/-- The word boxes and page count of a PDF, as Poppler's `-bbox` reads them, metadata aside. -/
def wordBoxes (pdf : System.FilePath) : IO String := do
  let r ← IO.Process.output { cmd := "pdftotext", args := #["-bbox", pdf.toString, "-"] }
  if r.exitCode != 0 then throw <| IO.userError s!"pdftotext failed on {pdf}"
  return "\n".intercalate ((r.stdout.splitOn "\n").filter fun l =>
    !(l.trimAscii.toString.startsWith "<meta") && !(l.trimAscii.toString.startsWith "<title"))

/-- One build of `src` in `dir`: its PDF and word boxes, or why it failed. -/
def build (dir : System.FilePath) (src : String) (env : Array (String × Option String))
    (minted : Bool) : IO (Except String (System.FilePath × String)) := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "probe.tex") src
  let shell := if minted then "-shell-restricted" else "-no-shell-escape"
  let run : IO UInt32 := do
    let r ← IO.Process.output {
      cmd := "lualatex"
      args := #["-interaction=nonstopmode", "-halt-on-error", shell, "probe.tex"]
      cwd := some dir
      env }
    return r.exitCode
  if (← run) != 0 then return .error "lualatex failed"
  -- A second run resolves the references the first wrote.
  if (← run) != 0 then return .error "lualatex failed"
  return .ok (dir / "probe.pdf", ← wordBoxes (dir / "probe.pdf"))

/-- Two builds' verdict: the same page (the same word boxes, no visible difference), a page set
apart with visualdiff's summary, or why the judge failed. -/
inductive Verdict where
  | same
  | apart (why : String)
  | failed (why : String)

def judge (a b : System.FilePath × String) : IO Verdict := do
  if a.2 != b.2 then return .apart "word boxes"
  let r ← IO.Process.output { cmd := ".lake/build/bin/visualdiff", args := #[a.1.toString, b.1.toString] }
  let last := ((r.stdout.trimAscii.toString.splitOn "\n").getLast?).getD ""
  return match r.exitCode with
    | 0 => .same
    | 1 => .apart last
    | _ => .failed s!"visualdiff exited {r.exitCode}: {r.stderr.trimAscii}"

/-- `--python <path>` names the python3 latexminted runs under, and `--only` a reader to probe alone. -/
def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Option String → Option String → IO (Option String × Option String)
    | [], py, only => pure (py, only)
    | "--python" :: p :: rest, _, only => opts rest (some p) only
    | "--only" :: r :: rest, py, _ => opts rest py (some r)
    | _, _, _ => throw <| IO.userError "usage: inert-diff [--python <path>] [--only <reader>]"
  let (python, only) ← opts args none none
  let probes := Tests.inertProbes.filter fun p => only.all (p.reader.startsWith ·)
  IO.FS.withTempDir fun root => do
    let cache := root / "cache"
    IO.FS.createDirAll cache
    let path := (← IO.getEnv "PATH").getD ""
    let path ← match python with
      | some p =>
        let shim := root / "python"
        IO.FS.createDirAll shim
        let abs ← IO.FS.realPath p
        let quoted := "'" ++ abs.toString.replace "'" "'\\''" ++ "'"
        IO.FS.writeFile (shim / "python3") s!"#!/bin/sh\nexec {quoted} \"$@\"\n"
        IO.setAccessRights (shim / "python3") { user := { read := true, write := true, execution := true } }
        pure s!"{shim}:{path}"
      | none => pure path
    let env := #[("TEXMFCACHE", some cache.toString), ("TEXMFVAR", some cache.toString),
      ("PATH", some path)]
    let mut differ : Array String := #[]
    let mut failed : Array String := #[]
    for (p, i) in probes.zipIdx do
      let a ← build (root / s!"{i}-with") p.withIt env p.minted
      let b ← build (root / s!"{i}-without") p.without env p.minted
      let label := s!"{p.reader} [{p.setting}]"
      let c ← match p.contrast with
        | some src => (some ·) <$> build (root / s!"{i}-contrast") src env p.minted
        | none => pure none
      match a, b with
      | .ok x, .ok y =>
        let seen ← match c with
          | some (.ok z) => do
            let v ← judge z y
            pure <| match v with
            | .same => " (its contrast is unseen)"
            | .apart _ => " (its contrast differs)"
            | .failed e => s!" (its contrast's judge failed: {e})"
          | some (.error e) => pure s!" (its contrast failed: {e})"
          | none => pure ""
        match ← judge x y with
        | .same => IO.println s!"same    {label}{seen}"
        | .apart why =>
          IO.println s!"DIFFERS {label}: {why}"
          differ := differ.push label
        | .failed e =>
          IO.println s!"FAILED  {label}: {e}"
          failed := failed.push label
      | .error e, _ | _, .error e =>
        IO.println s!"FAILED  {label}: {e}"
        failed := failed.push label
    IO.println s!"inert-diff: {probes.length} probes, {differ.size} differ, {failed.size} failed"
    return (if differ.isEmpty && failed.isEmpty then 0 else 1)
