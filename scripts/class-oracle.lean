/-
The leantex classes' samples set by lualatex and by the engine, judged by visualdiff; a report.
Usage: lake build leantex visualdiff && lake env lean --run scripts/class-oracle.lean [sample]
-/

/-- Run a tool in `cwd` with `env`, its exit code and its standard output. -/
def run (cmd : String) (args : Array String) (cwd : System.FilePath)
    (env : Array (String × Option String) := #[]) : IO (UInt32 × String) := do
  try
    let out ← IO.Process.output { cmd, args, cwd, env }
    return (out.exitCode, out.stdout)
  catch e => return (127, toString e)

/-- One visualdiff line's `key=value` field. -/
def field (line key : String) : Option String :=
  ((line.splitOn " ").find? (·.startsWith (key ++ "="))).map fun t => (t.drop (key.length + 1)).toString

def main (args : List String) : IO UInt32 := do
  let root ← IO.FS.realPath "."
  let samples := root / "testdata" / "classes"
  let scratch := root / ".lake" / "class-oracle"
  IO.FS.createDirAll scratch
  let tex := (root / "tex").toString
  let env := #[("TEXINPUTS", some s!"{tex}//:"), ("LUAINPUTS", some s!"{tex}//:"),
    ("SOURCE_DATE_EPOCH", some "0"), ("FORCE_SOURCE_DATE", some "1")]
  let stems := ((← samples.readDir).filter (·.fileName.endsWith ".tex")).map
    (·.fileName.dropEnd 4 |>.toString) |>.qsort (· < ·)
  let stems := match args with
    | [one] => stems.filter (· == one)
    | _ => stems
  let mut equal := 0
  let mut pages := 0
  IO.println "sample\tpages\tno visible difference\tverdicts"
  for stem in stems do
    let src := samples / (stem ++ ".tex")
    IO.FS.writeFile (scratch / (stem ++ ".tex")) (← IO.FS.readFile src)
    let latex := #["-interaction=nonstopmode", "-halt-on-error", "-jobname", stem ++ ".ref",
      stem ++ ".tex"]
    let (c1, _) ← run "lualatex" latex scratch env
    let (c2, _) ← if c1 == 0 then run "lualatex" latex scratch env else pure (c1, "")
    if c2 != 0 then
      IO.println s!"{stem}\t-\t-\tlualatex refuses the sample (exit {c2}); see {scratch}/{stem}.ref.log"
      continue
    let (e, _) ← run (root / ".lake/build/bin/leantex").toString
      #[stem ++ ".tex", "-o", stem ++ ".lt.pdf", "-q"] scratch
    if e != 0 then
      IO.println s!"{stem}\t-\t-\tthe engine did not build the sample (exit {e})"
      continue
    let (_, out) ← run (root / ".lake/build/bin/visualdiff").toString
      #[stem ++ ".ref.pdf", stem ++ ".lt.pdf"] scratch
    let verdicts := (out.splitOn "\n").filter (·.startsWith "visualdiff: page=")
    let same := verdicts.filter fun l => field l "verdict" != some "visible"
    equal := equal + same.length
    pages := pages + verdicts.length
    let shown := verdicts.map fun l => s!"{(field l "page").getD "?"}:{(field l "verdict").getD "?"}"
    IO.println s!"{stem}\t{verdicts.length}\t{same.length}\t{" ".intercalate shown}"
  IO.println s!"class-oracle: {equal} of {pages} pages with no visible difference"
  return 0
