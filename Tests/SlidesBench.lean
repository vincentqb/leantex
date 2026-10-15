module

public import Tests.Support

public section

namespace Tests

/-- The slides bench's selftest passes, its fixture builds included: every input it times builds
without a warning. -/
def slidesBenchChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (lean, leanPath) ← leanChild "the slides bench's checks"
  let root ← IO.FS.realPath (← IO.currentDir)
  let run ← childRun 20000 lean.toString #["--run", "scripts/bench.lean", "--slides-selftest"] root
    (env := #[("LEAN_PATH", some leanPath), ("LEANTEX_BENCH_BINARY", none)])
  check ref s!"slides bench: the selftest passes and every fixture builds clean ({run.err})"
    (run.complete && run.ran == .exited 0 && run.out.contains "slides fixtures: 12 cold builds clean")

end Tests
