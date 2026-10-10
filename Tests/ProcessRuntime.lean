module

public import LeanTex.Cli.RunBounded
public import Tests.Support

public section

open LeanTex.Cli

namespace Tests

private def exitWithin (child : IO.Process.Child cfg) (ms : Nat) : IO (Option UInt32) := do
  for _ in [:ms / 10 + 1] do
    if let some code ← child.tryWait then return some code
    IO.sleep 10
  return none

private def doneWithin (task : Task α) (ms : Nat) : BaseIO Bool := do
  for _ in [:ms / 10 + 1] do
    if ← IO.hasFinished task then return true
    IO.sleep 10
  IO.hasFinished task

/-- What the runtime does at the process boundary, read on the real runtime.
The exec and working-directory failures, a shell's exit for a program it
cannot find, and the signal encoding are what `ImageAssets.runChecked`,
`PicCache.probed` and `PicCache.outcome` decide on;
a converter's own exit 255 must stay distinguishable, so its empty stderr is
asserted too. `Child.kill` sends SIGKILL to a setsid child's whole process
group, though Lean's docstring says SIGTERM, so a TERM trap never runs and a
reaped leader's descendant dies with the group. `RunBounded`'s overrun rests
on that kill alone and returns once the group's pipes close. -/
def processRuntimeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let absent := "leantex-premise-absent-tool"
  let line := s!"could not execute external process '{absent}'"
  -- A child that fails at exec leaves through exit(), which writes out the
  -- standard output it inherited buffered from this process.
  (← IO.getStdout).flush
  let direct ← IO.Process.output { cmd := absent, args := #["--version"] }
  t "process runtime: an unexecutable command exits 255 with the runtime's one line"
    (direct.exitCode == 255 && direct.stdout.isEmpty &&
      direct.stderr.trimAscii.toString == line)
  let bounded ← RunBounded.runBounded absent #["--version"] (← IO.currentDir) 5000 100
  t "process runtime: the bounded runner reads the same exit and line"
    (bounded.complete && bounded.ran == .exited 255 && bounded.err.trimAscii.toString == line)
  let missing := "/leantex-premise-no-such-directory"
  let lost ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "exit 0"], cwd := missing }
  t "process runtime: a working directory the child cannot enter exits 255 with its own line"
    (lost.exitCode == 255 && lost.stderr.trimAscii.toString == s!"could not change directory to {missing}")
  let signalled ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "kill -TERM $$"] }
  t "process runtime: a child a signal ended exits 128 plus the signal"
    (signalled.exitCode == 143)
  let unfound ← IO.Process.output { cmd := "/bin/sh", args := #["-c", absent] }
  t "process runtime: a shell that cannot find the program it was asked for exits 127 and says so"
    (unfound.exitCode == 127 && !unfound.stderr.trimAscii.isEmpty)
  let own ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "exit 255"] }
  t "process runtime: a tool's own exit 255 carries no runtime line"
    (own.exitCode == 255 && own.stderr.isEmpty)
  let trapped ← IO.Process.spawn {
    cmd := "/bin/sh", setsid := true, stdin := .null, stdout := .piped, stderr := .null
    args := #["-c", "trap 'echo trapped; exit 7' TERM\necho ready\nwhile :; do /bin/sleep 1; done"] }
  let ready ← trapped.stdout.getLine
  trapped.kill
  let code ← exitWithin trapped 5000
  let rest ← IO.asTask trapped.stdout.readToEnd Task.Priority.dedicated
  let said := if ← doneWithin rest 5000 then (rest.get.toOption.getD "?") else "?"
  t s!"process runtime: Child.kill sends SIGKILL, so a setsid child's TERM trap never runs ({code}, '{said}')"
    (ready.trimAscii.toString == "ready" && code == some 137 && said.isEmpty)
  let group ← IO.Process.spawn {
    cmd := "/bin/sh", setsid := true, stdin := .null, stdout := .piped, stderr := .null
    args := #["-c", "/bin/sh -c 'trap \"\" TERM; echo ready; exec /bin/sleep 30' &\nexit 0"] }
  let heard ← group.stdout.getLine
  let leader ← exitWithin group 5000
  group.kill
  let drained ← IO.asTask group.stdout.readToEnd Task.Priority.dedicated
  t "process runtime: Child.kill ends the TERM-ignoring descendant of a reaped leader"
    (heard.trimAscii.toString == "ready" && leader == some 0 && (← doneWithin drained 5000))
  let start ← IO.monoMsNow
  let over ← RunBounded.runBounded "/bin/sh"
    #["-c", "trap '' TERM\n/bin/sh -c 'trap \"\" TERM; exec /bin/sleep 30' &\nexec /bin/sleep 30"]
    (← IO.currentDir) 200 10000
  let elapsed := (← IO.monoMsNow) - start
  t s!"process runtime: an overrun returns as its killed group's pipes close, not after the grace ({elapsed} ms)"
    (over.ran == .overran 0 && !over.complete && elapsed < 5200)

end Tests
