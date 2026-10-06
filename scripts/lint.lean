namespace Lint

/-- Verification stages are ordinary child processes. A failed stage stops
the run; no later successful check can conceal its exit status. -/
def run (cmd : String) (args : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args }
  child.wait

def check : IO UInt32 := do
  let stages := #[
    ("lake", #["build", "--wfail", "precommit", "proofcheck", "cites"]),
    (".lake/build/bin/precommit", #["--tree", "--conventions"]),
    (".lake/build/bin/proofcheck", #["--check"]),
    (".lake/build/bin/proofcheck", #["--selftest"]),
    (".lake/build/bin/precommit", #["--selftest"]),
    (".lake/build/bin/cites", #["--selftest"]),
    (".lake/build/bin/cites", #["--check"])]
  for (cmd, args) in stages do
    let code ← run cmd args
    if code != 0 then return code
  return 0

end Lint

def main : IO UInt32 := Lint.check
