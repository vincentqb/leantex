/-
Benchmark leantex against lualatex on the bench corpus. Run from the
repository root after `lake build`:

  lake env lean --run scripts/bench.lean

Reference point, not a fair fight: lualatex loads formats and fonts per run,
and does far more. Median of N runs (env var `N`, default 5), milliseconds.
-/

def leantex := ".lake/build/bin/leantex"

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def runMs (cmd : String) (args : Array String) : IO Nat := do
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output { cmd, args }
  let t1 ← IO.monoMsNow
  if out.exitCode != 0 then
    die s!"benchmark command failed: {cmd} {String.intercalate " " args.toList}"
  return t1 - t0

def median (times : Array Nat) : Nat :=
  let sorted := times.qsort (· < ·)
  sorted.getD ((sorted.size + 1) / 2 - 1) 0

def padRight (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

def padLeft (s : String) (w : Nat) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

def bench (n : Nat) (label : String) (cmd : String) (args : Array String) : IO Unit := do
  let mut times : Array Nat := #[]
  for _ in [0:n] do
    times := times.push (← runMs cmd args)
  IO.println s!"{padRight label 42} {padLeft (toString (median times)) 6} ms (median of {n})"

def hasCmd (cmd : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd, args := #["--version"] }
    return out.exitCode == 0
  catch _ =>
    return false

def main : IO UInt32 := do
  let n := ((← IO.getEnv "N").bind (·.toNat?)).getD 5
  let genLorem ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "--run", "scripts/gen-lorem.lean"] }
  if genLorem.exitCode != 0 then
    die s!"gen-lorem failed:\n{genLorem.stderr}"
  let haveLualatex ← hasCmd "lualatex"
  for doc in ["tests/corpus/paragraphs.tex", "bench/lorem.tex", "bench/underline.tex"] do
    let base := (doc.splitOn "/").getLastD doc
    bench n s!"leantex  {base}" leantex #["-q", "build", doc]
    if haveLualatex then
      let workdir ← IO.FS.createTempDir
      IO.FS.writeBinFile (workdir / base) (← IO.FS.readBinFile doc)
      bench n s!"lualatex {base}" "lualatex"
        #["--interaction=batchmode", s!"--output-directory={workdir}", (workdir / base).toString]
      IO.FS.removeDirAll workdir
  -- The theme/roles/chrome and recovery passes run only on a themed deck,
  -- and the HTML backend was off the measured path entirely; leantex-only
  -- (lualatex does not build the native theme declarations).
  let outDir ← IO.FS.createTempDir
  bench n "leantex  themed.tex" leantex
    #["-q", "build", "tests/corpus/themed.tex", "-o", (outDir / "themed.pdf").toString]
  bench n "leantex  themed.tex -o html" leantex
    #["-q", "build", "tests/corpus/themed.tex", "-o", (outDir / "themed.html").toString]
  IO.FS.removeDirAll outDir
  return 0
