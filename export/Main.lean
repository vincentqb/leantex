import LeantexExport.Header
import LeantexExport.Program

/-! `lake exe leantex-export <modules>`: each module's facts, where leantex reads them, under the
project's `.lake/build/leantex`. -/

open LeantexExport

/-- A module's source: the first of Lake's source directories, then the project's, that holds it. -/
def sourceOf (module : String) : IO (Option System.FilePath) := do
  let rel := "/".intercalate (module.splitOn ".") ++ ".lean"
  let dirs := (((← IO.getEnv "LEAN_SRC_PATH").getD "").splitOn ":").filter (!·.isEmpty)
  for d in dirs ++ ["."] do
    let p := System.FilePath.mk d / rel
    if ← p.pathExists then return some (← IO.FS.realPath p)
  return none

/-- Where a source's facts stand: its path under the project, `.lean` made `.facts`, beneath
`.lake/build/leantex`, or its module's path where the source stands outside the project. -/
def factsPath (root : System.FilePath) (module : String) (src : System.FilePath) :
    System.FilePath :=
  let r := root.toString ++ "/"
  let rel := if src.toString.startsWith r then ofChars (src.toString.toList.drop r.length)
    else "/".intercalate (module.splitOn ".") ++ ".lean"
  let stem := if rel.endsWith ".lean" then ofChars (rel.toList.take (rel.length - 5)) else rel
  root / ".lake" / "build" / "leantex" / (stem ++ ".facts")

/-- One module's facts written, or why not: the export runs as the project's `lean` reads it from
standard input, so its own module's name is the same wherever the project stands. -/
def exportOne (root : System.FilePath) (module : String) : IO (Except String System.FilePath) := do
  let some src ← sourceOf module | return .error s!"no source for {module} on Lake's source path"
  let some imports := imports? (← IO.FS.readFile src)
    | return .error s!"{module} is a prelude file, which elaborates without Init, which the export needs"
  let out := factsPath root module src
  if let some dir := out.parent then IO.FS.createDirAll dir
  let lean := (← IO.getEnv "LEAN").getD "lean"
  let child ← IO.Process.spawn {
    cmd := lean, args := #["-DElab.async=false", "--stdin"], cwd := root
    stdin := .piped, stdout := .piped, stderr := .piped
    env := #[("LEANTEX_LEAN_FILE", some src.toString), ("LEANTEX_LEAN_SOURCE", some src.toString),
      ("LEANTEX_LEAN_MODULE", some module), ("LEANTEX_LEAN_ANSWER", some out.toString)] }
  let (stdin, child) ← child.takeStdin
  stdin.putStr (source imports)
  stdin.flush
  let said ← IO.asTask child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code == 0 then return .ok out
  let printed := match said.get with
    | .ok text => text
    | .error _ => ""
  return .error s!"{module}: lean exited with {code}\n{printed}{err}"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake exe leantex-export <module>..."
    return 2
  let root ← IO.FS.realPath (← IO.currentDir)
  let mut status : UInt32 := 0
  for module in args do
    match ← exportOne root module with
    | .ok out => IO.println s!"leantex-export: {module} → {out}"
    | .error why =>
      IO.eprintln s!"leantex-export: {why}"
      status := 1
  return status
