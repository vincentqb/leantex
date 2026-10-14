module

public section

/-! The data generators' shared steps: failing, finding a TeX file, reading TeX source and loading
Pygments. -/

namespace GenData

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

/-- Where kpsewhich finds `file`; with no kpsewhich the run fails saying `hint`. -/
def locate (file : String) (hint : String := s!"it locates {file}") : IO String := do
  let out ← try
    IO.Process.output { cmd := "kpsewhich", args := #[file] }
  catch _ =>
    die s!"kpsewhich not found; {hint}"
  let path := out.stdout.trimAscii.toString
  if out.exitCode != 0 || path.isEmpty then
    die s!"kpsewhich could not find {file}"
  return path

/-- A line with its TeX comment removed. -/
def uncomment (line : String) : String := Id.run do
  let mut out := ""
  let mut prev := ' '
  for c in line.toList do
    if c == '%' && prev != '\\' then return out
    out := out.push c
    prev := c
  return out

/-- The file with every TeX comment removed, its lines kept. -/
def uncommented (text : String) : String :=
  String.join ((text.splitOn "\n").map (uncomment · ++ "\n"))

/-- The balanced group opening at `cs[i]`: its body and the index after it. -/
def groupAt (cs : Array Char) (i : Nat) : Option (String × Nat) := Id.run do
  if cs[i]? != some '{' then return none
  let mut depth := 0
  let mut body := ""
  let mut j := i
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c =>
      if c == '{' then
        depth := depth + 1
        if depth > 1 then body := body.push c
      else if c == '}' then
        depth := depth - 1
        if depth == 0 then return some (body, j + 1)
        body := body.push c
      else body := body.push c
      j := j + 1
    | none => return none
  return none

/-- Python that imports Pygments, else the wheel beside latexminted, with its plugins off; the bridge
imports `pathlib`, `shutil` and `sys` before it. -/
def pygmentsLoader : String := r#"try:
    import pygments
except ModuleNotFoundError as error:
    if error.name != 'pygments':
        raise
    launcher = shutil.which('latexminted')
    if launcher is None:
        raise SystemExit('no Pygments: no installed module and no latexminted launcher')
    wheels = sorted(pathlib.Path(launcher).resolve().parent.glob('pygments-*.whl'))
    if len(wheels) != 1:
        raise SystemExit('no Pygments: expected one wheel beside latexminted')
    sys.path.insert(0, str(wheels[0]))
    import pygments
import pygments.plugin
pygments.plugin.iter_entry_points = lambda group: ()
"#

end GenData
