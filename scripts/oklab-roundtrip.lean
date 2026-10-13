/-
Round-trip oracle for the integer Oklab pipeline, its pass cached under `.lake/` by its inputs'
content; `--force` re-runs the walk (scripts/oklab-walk.lean, about 30 minutes).
Usage: lake env lean --run scripts/oklab-roundtrip.lean [--force]
-/

/-- The files whose content the cached verdict is a claim about. -/
def cacheDeps : List System.FilePath :=
  ["LeanTex/Core/Oklab.lean", "LeanTex/Core/Color.lean", "LeanTex/Core/Ir.lean",
   "lean-toolchain"]

def cachePath : System.FilePath := ".lake/oklab-roundtrip.cache"

def inputsHash : IO UInt64 := do
  let mut h : UInt64 := 7
  for f in cacheDeps do
    h := mixHash (mixHash h (hash f.toString)) (hash (← IO.FS.readFile f))
  return h

/-- The recorded pass, if the cache file exists and parses: input hash, date earned and
result line; anything else is a miss. -/
def readCache : IO (Option (UInt64 × String × String)) := do
  try
    let s ← IO.FS.readFile cachePath
    match s.splitOn "\n" with
    | h :: date :: result :: _ =>
      return (h.toNat?).map fun n => (UInt64.ofNat n, date, result)
    | _ => return none
  catch _ =>
    return none

def utcNow : IO String := do
  let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
  return out.stdout.trimAscii.toString

def main (args : List String) : IO Unit := do
  let force := args.contains "--force"
  let h ← inputsHash
  if !force then
    if let some (ch, date, result) ← readCache then
      if ch == h then
        IO.println s!"oklab-roundtrip: CACHED pass — the walk did not run now."
        IO.println s!"  earned {date} on input hash {h}: {result}"
        IO.println s!"  (--force re-runs the full walk)"
        return
    IO.println s!"oklab-roundtrip: cache miss for input hash {h}; running the full walk"
  else
    IO.println s!"oklab-roundtrip: --force; running the full walk (input hash {h})"
  (← IO.getStdout).flush
  let out ← IO.Process.output
    { cmd := "lean", args := #["--run", "scripts/oklab-walk.lean"] }
  IO.print out.stdout
  IO.eprint out.stderr
  if out.exitCode != 0 then
    IO.Process.exit 1
  match (out.stdout.splitOn "\n").head? with
  | some result =>
    IO.FS.createDirAll ".lake"
    IO.FS.writeFile cachePath s!"{h}\n{← utcNow}\n{result}\n"
  | none =>
    IO.Process.exit 1
