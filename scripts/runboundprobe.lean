import LeanTex.Cli.ImageAssets

/-! Drive the real `ImageAssets.runBounded` against one tool under a small
budget, and report how it ended and how long it took. The cache IO oracle
(`scripts/conv-cache-io.lean`) uses this against a stub whose descendant
holds the pipes open and ignores `SIGTERM`, to prove the group `SIGKILL`
escalation and the bounded drains defeat it: the probe must return in far
under the descendant's own sleep, and no stub process may survive. The tool
is argv[1]; the budget and grace are small so the test is quick. -/

def main (argv : List String) : IO UInt32 := do
  let tool := argv.headD "false"
  let t0 ← IO.monoMsNow
  let ended ← LeanTex.Cli.ImageAssets.runBounded tool #[] (← IO.currentDir)
    (budgetMs := 400) (graceMs := 300)
  let dt := (← IO.monoMsNow) - t0
  IO.println s!"RAN {repr ended.ran} {dt}"
  return 0
