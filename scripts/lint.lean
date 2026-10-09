namespace Lint

/-- What every check reads, built in order, then the cheap whole-tree
convention pass, so a failure there is reported in seconds. Each is an
ordinary child process; a failed one stops the run with its exit status. -/
def first : Array (String × Array String) := #[
  ("lake", #["build", "--wfail", "precommit", "proofcheck", "cites"]),
  (".lake/build/bin/proofcheck", #["--build"]),
  (".lake/build/bin/precommit", #["--tree", "--conventions"])]

/-- The checks over that build: child processes that only read what it
built, so they run at once. The source audit is the long one; the
self-tests and the citation check finish inside it. -/
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
  -- Every check is joined and printed in stage order; the first failure in
  -- that order is the run's status, so no passing check can conceal it.
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
