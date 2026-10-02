import LeanTex.Cli.RunBounded

open LeanTex.Cli

-- Completion means exit plus EOF on both pipes. A descendant must not make
-- an exit-0 leader look complete, nor survive the budget by holding a pipe.
def main : IO UInt32 := do
  let failures ← IO.mkRef (#[] : Array String)
  let check (label : String) (ok : Bool) : IO Unit := do
    unless ok do failures.modify (·.push label)
  IO.FS.withTempDir fun dir => do
    let cases := #[
      ("clean", "printf complete; printf reason >&2; exit 7", PicCache.Ran.exited 7),
      ("held-pipe", "sh -c 'trap \"\" TERM; echo $$ > child.pid; sleep 5' &\nexit 0",
        PicCache.Ran.overran 0),
      ("timeout", "trap '' TERM\nsh -c 'trap \"\" TERM; echo $$ > child.pid; sleep 5' &\nsleep 5",
        PicCache.Ran.overran 0)]
    for (label, script, want) in cases do
      let marker := dir / "child.pid"
      try IO.FS.removeFile marker catch _ => pure ()
      let start ← IO.monoMsNow
      let got ← RunBounded.runBounded "/bin/sh" #["-c", script] dir 150 100
      let elapsed := (← IO.monoMsNow) - start
      check s!"{label}: honest completion" (got.ran == want)
      check s!"{label}: bounded wall time" (elapsed < 2000)
      if label == "clean" then
        check "clean: both streams complete" (got.out == "complete" && got.err == "reason")
      else
        let pid ← IO.FS.readFile marker
        let live ← IO.Process.output {
          cmd := "/bin/ps", args := #["-o", "stat=", "-p", pid.trimAscii.toString] }
        let state := live.stdout.trimAscii.toString
        check s!"{label}: descendant stopped" (state.isEmpty || state.startsWith "Z")
        -- The baseline runner leaves this descendant alive; clean it up too.
        discard <| IO.Process.output { cmd := "/bin/kill", args := #["-KILL", pid.trimAscii.toString] }
  let exact ← RunBounded.runBounded "/bin/sh" #["-c", "head -c 1024 /dev/zero"]
    (← IO.currentDir) 1000 100 1024
  check "capture: exact byte allowance reaches EOF" (exact.complete && exact.out.utf8ByteSize == 1024)
  let excess ← RunBounded.runBounded "/bin/sh" #["-c", "head -c 1025 /dev/zero"]
    (← IO.currentDir) 1000 100 1024
  check "capture: excess is incomplete, never a reusable prefix" (!excess.complete)
  let failed ← failures.get
  for failure in failed do IO.eprintln s!"FAIL: {failure}"
  IO.println s!"bounded conversion checks: {failed.size} failures"
  return if failed.isEmpty then 0 else 1
