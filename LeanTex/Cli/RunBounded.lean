module

public import LeanTex.Cli.PicCache

namespace LeanTex.Cli.RunBounded

-- Operational ceilings: one minute per conversion, two seconds for a killed
-- process group's pipes to close, and 16 MiB per textual stream (including
-- xmllint's SAX dump).
public def convBudgetMs : Nat := 60000
public def convGraceMs : Nat := 2000
public def maxCaptureBytes : Nat := 16 * 1024 * 1024

structure Capture where
  text : String := ""
  complete : Bool := false

public structure Ended where
  ran : PicCache.Ran
  out : String
  err : String
  complete : Bool
  spawnError : Option IO.Error := none

private def capture (h : IO.FS.Handle) (limit : Nat) : IO Capture := do
  let mut bytes := ByteArray.empty
  -- Every nonempty read consumes at least one byte of the capture allowance;
  -- one extra byte distinguishes EOF at the limit from truncated output.
  for _ in [:limit + 1] do
    let chunk ← h.read (min 65536 (limit + 1 - bytes.size)).toUSize
    if chunk.isEmpty then
      return match String.fromUTF8? bytes with
        | some text => { text, complete := true }
        | none => {}
    bytes := bytes ++ chunk
    if bytes.size > limit then break
  return {}

private def finishedBad (t : Task (Except IO.Error Capture)) : BaseIO Bool := do
  if ← IO.hasFinished t then
    return match t.get with
      | .ok c => !c.complete
      | .error _ => true
  return false

public def runBounded (tool : String) (args : Array String) (cwd : System.FilePath)
    (budgetMs : Nat := convBudgetMs) (graceMs : Nat := convGraceMs)
    (captureLimit : Nat := maxCaptureBytes)
    (env : Array (String × Option String) := #[]) : IO Ended := do
  let spawned ← (IO.Process.spawn {
    cmd := tool, args, cwd, env, setsid := true,
    stdin := .null, stdout := .piped, stderr := .piped }).toBaseIO
  let child ← match spawned with
    | .ok child => pure child
    | .error e => return { ran := .unstarted (toString e), out := "", err := "", complete := false, spawnError := some e }
  let outT ← IO.asTask (capture child.stdout captureLimit) Task.Priority.dedicated
  let errT ← IO.asTask (capture child.stderr captureLimit) Task.Priority.dedicated
  let start ← IO.monoMsNow
  let mut code : Option UInt32 := none
  let mut complete := false
  for _ in [:budgetMs / 10 + 2] do
    if code.isNone then code := (← child.tryWait.toBaseIO).toOption.getD none
    if (← finishedBad outT) || (← finishedBad errT) then break
    if code.isSome && (← IO.hasFinished outT) && (← IO.hasFinished errT) then
      -- Finished task results are stable; use the captures we will return,
      -- since either task could have failed after `finishedBad` observed it.
      complete := outT.get.toOption.any (·.complete) &&
        errT.get.toOption.any (·.complete)
      break
    let elapsed := (← IO.monoMsNow) - start
    if elapsed ≥ budgetMs then break
    IO.sleep (min 10 (budgetMs - elapsed)).toUInt32
  unless complete do
    -- `Child.kill` sends SIGKILL to a setsid child's whole process group, a
    -- reaped leader's descendants included, so nothing that stays in the
    -- group can trap it.
    discard <| child.kill.toBaseIO
    let stop ← IO.monoMsNow
    let mut reaped := code.isSome
    for _ in [:graceMs / 10 + 2] do
      unless reaped do reaped := (← child.tryWait.toBaseIO).toOption.any (·.isSome)
      if reaped && (← IO.hasFinished outT) && (← IO.hasFinished errT) then break
      if (← IO.monoMsNow) - stop ≥ graceMs then break
      IO.sleep 10
  let read (t : Task (Except IO.Error Capture)) : BaseIO String := do
    if ← IO.hasFinished t then return (t.get.toOption.getD {}).text
    return ""
  return {
    ran := if complete then .exited (code.getD 0).toNat else .overran (budgetMs / 1000),
    out := ← read outT, err := ← read errT, complete }

public def output (args : IO.Process.SpawnArgs) : IO IO.Process.Output := do
  let got ← runBounded args.cmd args.args (args.cwd.getD (← IO.currentDir))
    (env := args.env)
  match got.ran with
  | .exited code => return { exitCode := code.toUInt32, stdout := got.out, stderr := got.err }
  | .overran _ => throw <| IO.userError s!"{args.cmd}: incomplete output or exceeded {convBudgetMs} ms conversion budget"
  | .unstarted err => throw <| got.spawnError.getD (IO.userError s!"{args.cmd}: {err}")

end LeanTex.Cli.RunBounded
