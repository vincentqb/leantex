namespace Lint

/-- The sequential stages: the build every check reads, then the fast whole-tree
convention pass; a failure stops the run. -/
def first : Array (String × Array String) := #[
  ("lake", #["build", "--wfail", "precommit", "proofcheck", "cites"]),
  (".lake/build/bin/proofcheck", #["--build"]),
  (".lake/build/bin/precommit", #["--tree", "--conventions"])]

/-- The checks over that build, run concurrently and reported in stage order. -/
def concurrent : Array (String × Array String) := #[
  (".lake/build/bin/proofcheck", #["--check"]),
  (".lake/build/bin/proofcheck", #["--selftest"]),
  (".lake/build/bin/precommit", #["--selftest"]),
  (".lake/build/bin/cites", #["--selftest"]),
  (".lake/build/bin/cites", #["--check"])]

def check : IO UInt32 := do
  for (cmd, args) in first do
    let code ← (← IO.Process.spawn { cmd, args }).wait
    if code != 0 then return code
  let runs ← concurrent.mapM fun (cmd, args) =>
    IO.asTask (IO.Process.output { cmd, args }) .dedicated
  let mut status : UInt32 := 0
  for (run, (cmd, args)) in runs.zip concurrent do
    let code ← match run.get with
      | .ok out => do
        IO.print out.stdout
        IO.eprint out.stderr
        pure out.exitCode
      | .error e => do
        IO.eprintln s!"lint: {cmd} {" ".intercalate args.toList} did not start: {e}"
        pure 1
    if status == 0 then status := code
  return status

end Lint

def main : IO UInt32 := Lint.check
