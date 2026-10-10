import LeanTex.Cli.TexFontTrees
import LeanTex.Cli.FontDiscovery
import Tests.Support

open LeanTex.Core LeanTex.Cli LeanTex.Cli.World

/-! The fonts the TeX font-tree rule (`TexFontTrees.roots`) finds, against
the fonts kpsewhich's font paths reach — the driver's source of TeX fonts
before the rule. A report, never a gate: it needs the host's TeX. Build the
imports, then run from the repository root:

  lake build LeanTex.Cli.TexFontTrees LeanTex.Cli.FontDiscovery Tests.Support
  lake env lean --run scripts/texfonts-report.lean

For every directory on `PATH` holding a `kpsewhich`, that one put first on
`PATH`: kpsewhich's `--show-path=.otf` and `--show-path=.ttf`, read as the
driver read them, against the rule's directories under the same `PATH`, and
the font faces each set of directories holds. Every face kpsewhich's
directories reach that the rule's miss is listed, and every face only the
rule finds; so is every directory kpsewhich names that the rule never looks
at, whether or not it exists, since an empty tree on this host may hold
fonts on another. Exit 0 when the rule misses no face, 1 when it misses any,
2 when there is no kpsewhich to compare with. -/

/-- The directories of `PATH` holding a `kpsewhich`, one per program they
resolve to, in `PATH` order. -/
def kpsewhichDirs (path : String) : IO (Array String) := do
  let mut seen : Array String := #[]
  let mut dirs : Array String := #[]
  for e in path.splitOn ":" do
    if e.isEmpty then continue
    match ← Host.answer (.stat (ToolPath.join e "kpsewhich")) with
    | .ok st =>
      if st.kind == .file && !seen.contains st.real then
        seen := seen.push st.real
        dirs := dirs.push e
    | .error _ => pure ()
  return dirs

/-- kpsewhich's directories for one font format, run by its bare name under
`path` and read as the driver read them: absolute elements, `!!` and
trailing `/`s removed. -/
def kpsewhichRoots (path ext : String) : IO (List String) := do
  let out ← IO.Process.output {
    cmd := "kpsewhich", args := #["--show-path=" ++ ext], env := #[("PATH", some path)] }
  if out.exitCode != 0 then
    throw (IO.userError s!"kpsewhich --show-path={ext} exited {out.exitCode}: {out.stderr}")
  return (out.stdout.trimAscii.toString.splitOn ":").filterMap fun p =>
    let p := if p.startsWith "!!" then String.ofList (p.toList.drop 2) else p
    let p := String.ofList (p.toList.reverse.dropWhile (· == '/')).reverse
    if p.startsWith "/" then some p else none

/-- One spelling per directory: repeated separators name the same place. -/
def normal (p : String) : String :=
  (if p.startsWith "/" then "/" else "") ++ "/".intercalate ((p.splitOn "/").filter (!·.isEmpty))

def main : IO UInt32 := do
  let path := (← IO.getEnv "PATH").getD ""
  let home ← IO.getEnv "HOME"
  let dirs ← kpsewhichDirs path
  if dirs.isEmpty then
    IO.println "texfonts-report: no kpsewhich on PATH to compare with"
    return 2
  let cwd := (← IO.currentDir).toString
  let mut missedAny := false
  for dir in dirs do
    let first := dir ++ ":" ++ path
    let old := ((← kpsewhichRoots first ".otf") ++ (← kpsewhichRoots first ".ttf")).eraseDups
    let program ← Tests.World.under first (.ok cwd) (TexFontTrees.programIn TexFontTrees.programs)
    let new ← Tests.World.under first (.ok cwd) (TexFontTrees.roots home)
    let asked := ((program.map fun p => TexFontTrees.fontDirs (TexFontTrees.trees p home)).getD []).map
      normal
    let unasked := old.filter fun d => !asked.contains (normal d)
    let oldFaces ← FontDiscovery.scanRootsIn none old
    let newFaces ← FontDiscovery.scanRootsIn none new
    let newPaths := newFaces.map (·.path)
    let oldPaths := oldFaces.map (·.path)
    let missed := oldFaces.filter fun f => !newPaths.contains f.path
    let extra := newFaces.filter fun f => !oldPaths.contains f.path
    let existing ← old.filterM fun r => (System.FilePath.mk r).isDir
    IO.println s!"texfonts-report: [{dir}/kpsewhich] TeX program {program.getD "(none)"}"
    IO.println s!"  kpsewhich's directories that exist: {existing}"
    IO.println s!"  the rule's directories: {new}"
    IO.println s!"  kpsewhich's directories the rule never looks at: {unasked}"
    IO.println s!"  faces: kpsewhich's {oldFaces.size}, the rule's {newFaces.size}, \
missed {missed.size}, only the rule's {extra.size}"
    for f in missed do IO.println s!"  MISSED: {f.family} ({f.path})"
    for f in extra do IO.println s!"  only the rule's: {f.family} ({f.path})"
    if !missed.isEmpty then missedAny := true
  return if missedAny then 1 else 0
