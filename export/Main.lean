import LeantexExport.Header
import LeantexExport.Program

/-! `lake exe leantex-export <module or file>...`: each one's facts, where leantex reads them,
beneath the `.lake/build/leantex` of the nearest directory above its source that holds a lakefile. -/

open LeantexExport

/-- A path made real, or kept as given where it does not resolve. -/
def realOr (p : System.FilePath) : IO System.FilePath := do
  try IO.FS.realPath p catch _ => pure p

/-- The exporter's own package, the directory its binary's `.lake/build/bin` stands in. -/
def ownPackage : IO System.FilePath := do
  let app ← IO.appPath
  realOr ((app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)).getD ".")

/-- Where a module's source is looked for: Lake's source directories beneath the workspace, then
the workspace itself, then the rest of Lake's, the exporter's own package left out. -/
def sourceDirs (root : System.FilePath) : IO (Array System.FilePath) := do
  let own ← ownPackage
  let packages := (root / ".lake").toString ++ "/"
  let mut mine := #[]
  let mut others := #[]
  for d in (((← IO.getEnv "LEAN_SRC_PATH").getD "").splitOn ":").filter (!·.isEmpty) do
    let real ← realOr d
    let s := real.toString ++ "/"
    if real == own then continue
    if real == root then continue
    if s.startsWith (root.toString ++ "/") && !s.startsWith packages then mine := mine.push real
    else others := others.push real
  return mine.push root ++ others

/-- A module's source: the first source directory holding it. -/
def sourceOf (dirs : Array System.FilePath) (module : String) : IO (Option System.FilePath) := do
  let rel := "/".intercalate (module.splitOn ".") ++ ".lean"
  for d in dirs do
    let p := d / rel
    if ← p.pathExists then return some (← IO.FS.realPath p)
  return none

/-- A path's place beneath a directory, none outside it. -/
def beneath (dir path : System.FilePath) : Option String :=
  let d := dir.toString ++ "/"
  if path.toString.startsWith d then some (ofChars (path.toString.toList.drop d.length)) else none

/-- A place with `.lean` dropped. -/
def stemOf (rel : String) : String :=
  if rel.endsWith ".lean" then ofChars (rel.toList.take (rel.length - 5)) else rel

/-- A source's module: its place beneath the deepest source directory holding it, else its file's
name. -/
def moduleOf (dirs : Array System.FilePath) (src : System.FilePath) : String :=
  let places := dirs.filterMap (beneath · src)
  let rel := places.foldl (fun best r => if r.length < best.length then r else best)
    (places[0]?.getD (src.fileName.getD ""))
  ".".intercalate ((stemOf rel).splitOn "/")

/-- Whether a directory holds a lakefile, a regular file. -/
def holdsLakefile (dir : System.FilePath) : IO Bool := do
  for n in ["lakefile.lean", "lakefile.toml"] do
    if let .ok md ← (dir / n).metadata.toBaseIO then
      if md.type == .file then return true
  return false

/-- The nearest directory at or above a source's own that holds a lakefile, else the source's
own: the project leantex finds for the file. -/
def projectOf (src : System.FilePath) : IO System.FilePath := do
  let own := src.parent.getD "/"
  let mut dir := own
  for _ in [0:src.components.length] do
    if ← holdsLakefile dir then return dir
    match dir.parent with
    | some p => dir := p
    | none => break
  return own

/-- Where leantex reads a source's facts: its place beneath its project, `.lean` made `.facts`,
under the project's `.lake/build/leantex`. -/
def factsPath (project src : System.FilePath) : System.FilePath :=
  let rel := (beneath project src).getD (src.fileName.getD "")
  project / ".lake" / "build" / "leantex" / (stemOf rel ++ ".facts")

/-- The module and source an argument names: a file by its path ending in `.lean`, else a module
by its name. -/
def resolve (root : System.FilePath) (dirs : Array System.FilePath) (arg : String) :
    IO (Except String (String × System.FilePath)) := do
  if arg.endsWith ".lean" then
    let p : System.FilePath := if arg.startsWith "/" then arg else root / arg
    if !(← p.pathExists) then return .error s!"no file {arg}"
    let src ← IO.FS.realPath p
    return .ok (moduleOf dirs src, src)
  match ← sourceOf dirs arg with
  | some src => return .ok (arg, src)
  | none => return .error s!"no source for {arg} on Lake's source path"

/-- One module's or file's facts written, or why not: the export runs as the project's `lean`
reads it from standard input, so its own module's name is the same wherever the project stands. -/
def exportOne (root : System.FilePath) (dirs : Array System.FilePath) (arg : String) :
    IO (Except String System.FilePath) := do
  match ← resolve root dirs arg with
  | .error why => return .error why
  | .ok (module, src) =>
    let some imports := imports? (← IO.FS.readFile src)
      | return .error s!"{arg} is a prelude file, which elaborates without Init, which the export needs"
    let out := factsPath (← projectOf src) src
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
    return .error s!"{arg}: lean exited with {code}\n{printed}{err}"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake exe leantex-export <module or file.lean>..."
    return 2
  let root ← IO.FS.realPath (← IO.currentDir)
  let dirs ← sourceDirs root
  let mut status : UInt32 := 0
  for arg in args do
    match ← (exportOne root dirs arg).toBaseIO with
    | .ok (.ok out) => IO.println s!"leantex-export: {arg} → {out}"
    | .ok (.error why) =>
      IO.eprintln s!"leantex-export: {why}"
      status := 1
    | .error e =>
      IO.eprintln s!"leantex-export: {arg}: {e}"
      status := 1
  return status
