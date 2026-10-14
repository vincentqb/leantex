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

/-- The Pygments release the generated lexer and style data are read from. -/
def pygmentsRelease : String := "2.21.0"

/-- Pygments' licence as that release ships it, named by every module derived from it. -/
def pygmentsLicence : String := "testdata/highlight/LICENSE-Pygments"

/-- `pygmentsLoader`, refusing a Pygments other than `pygmentsRelease` before a lexer or style is
read. -/
def pygmentsPinned : String :=
  pygmentsLoader ++ s!"pinned = '{pygmentsRelease}'\n" ++ r#"if pygments.__version__ != pinned:
    raise SystemExit(f'Pygments {pygments.__version__} ({pygments.__file__}) is not {pinned}, the '
                     'release the data are read from: pass --python naming an interpreter that imports '
                     'it, such as DIR/bin/python3 after python3 -m venv DIR and DIR/bin/pip install '
                     f'pygments=={pinned}')
"#

/-- A generator's `--selftest`: its bridge, run under a Python whose only Pygments is a stub of
another release, refuses it naming both releases. -/
def pinSelftest (name bridge : String) : IO UInt32 := do
  let dir ← IO.FS.createTempDir
  try
    let venv := dir / "venv"
    let made ← IO.Process.output
      { cmd := "python3", args := #["-m", "venv", "--without-pip", venv.toString] }
    let python := (venv / "bin" / "python3").toString
    let site ← if made.exitCode == 0 then
        IO.Process.output
          { cmd := python, args := #["-I", "-c", "import sysconfig; print(sysconfig.get_path('purelib'))"] }
      else pure made
    let lib := site.stdout.trimAscii.toString
    unless site.exitCode == 0 && lib.startsWith venv.toString do
      IO.eprintln s!"{name} --selftest: python3 made no venv to stub:\n{site.stderr}"
      return 1
    let stub := System.FilePath.mk lib / "pygments"
    IO.FS.createDirAll stub
    IO.FS.writeFile (stub / "__init__.py") "__version__ = '0.0.0'\n"
    IO.FS.writeFile (stub / "plugin.py") ""
    let out ← IO.Process.output { cmd := python, args := #["-I", "-B", "-c", bridge] }
    let says (s : String) := (out.stderr.splitOn s).length > 1
    if out.exitCode != 0 && says "Pygments 0.0.0" && says s!"is not {pygmentsRelease}" then
      IO.println s!"{name} --selftest: ok (Pygments 0.0.0 refused for {pygmentsRelease})"
      return 0
    IO.eprintln s!"{name} --selftest: Pygments 0.0.0 was not refused for {pygmentsRelease}:\n{out.stderr}"
    return 1
  finally
    IO.FS.removeDirAll dir

end GenData
