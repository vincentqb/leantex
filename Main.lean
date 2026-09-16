import LeanTex

open LeanTex.Core LeanTex.Cli

structure Ui where
  cfg : Config
  color : Bool
  errStream : IO.FS.Stream
  outStream : IO.FS.Stream

def Ui.mk' (cfg : Config) : IO Ui := do
  let errStream ← IO.getStderr
  let color ← match cfg.color with
    | .always => pure true
    | .never => pure false
    | .auto => do
      let noColor := (← IO.getEnv "NO_COLOR").isSome
      let tty ← errStream.isTty
      pure (!noColor && tty)
  return ⟨cfg, color, errStream, ← IO.getStdout⟩

def Ui.diag (ui : Ui) (d : Diag) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDiag d)
  else
    ui.errStream.putStrLn (Render.human ui.color d)

def Ui.phase (ui : Ui) (name detail : String) (ms : Nat) : IO Unit := do
  if ui.cfg.porcelain then
    if ui.cfg.verbosity ≥ 1 then
      ui.outStream.putStrLn (Render.porcelainPhase name detail ms)
  else if ui.cfg.verbosity ≥ 1 then
    ui.errStream.putStrLn s!"{name}: {detail} ({ms} ms)"

def Ui.summary (ui : Ui) (file : String) (errors ms : Nat) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainSummary file (errors == 0) errors ms)
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanSummary ui.color file errors ms)

def since (t0 : Nat) : IO Nat := do
  return (← IO.monoMsNow) - t0

def build (ui : Ui) (file : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let bytes ← try
    pure (some (← IO.FS.readBinFile file))
  catch e =>
    ui.diag { severity := .error, code := "E0001", message := s!"cannot read '{file}': {e}" }
    pure none
  let some bytes := bytes | do
    ui.summary file 1 (← since t0)
    return 1
  ui.phase "read" s!"{bytes.size} bytes" (← since t0)
  match LeanTex.Core.Utf8.validate bytes with
  | some err =>
    ui.diag (err.toDiag file)
    ui.summary file 1 (← since t0)
    return 1
  | none =>
    ui.phase "utf8" "valid" (← since t0)
    let d : Diag := {
      severity := .error
      code := "E0000"
      message := "the pipeline ends here: parsing is not implemented yet (M1)"
      span := some ⟨file, {}⟩
      help := "see PLAN.md for the milestone ladder"
    }
    ui.diag d
    ui.summary file 1 (← since t0)
    return 4

def main (argv : List String) : IO UInt32 := do
  match parse argv with
  | .error msg =>
    let stderr ← IO.getStderr
    stderr.putStrLn s!"leantex: {msg}"
    stderr.putStrLn "try 'leantex --help'"
    return 3
  | .ok cfg =>
    match cfg.cmd with
    | .help =>
      IO.println helpText
      return 0
    | .version =>
      IO.println s!"leantex {LeanTex.version}"
      return 0
    | .build file =>
      build (← Ui.mk' cfg) file
