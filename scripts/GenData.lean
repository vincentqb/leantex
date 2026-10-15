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

/-- The Python the generated lexer data are read under, whose `re` classes and Unicode they record. -/
def pygmentsPython : String := "3.13.14"

/-- Pygments' licence as that release ships it, named by every module generated from or porting it. -/
def pygmentsLicence : String := "testdata/highlight/LICENSE-Pygments"

/-- `pygmentsLoader`, refusing first any Python but `python` when one is given, then any Pygments
but `release`, each refusal naming what to make instead. -/
def pinnedLoader (python : Option String := none) (release : String := pygmentsRelease) : String :=
  let pinnedPython := (python.map fun v => "'" ++ v ++ "'").getD "None"
  s!"pinned = '{release}'\npinned_python = {pinnedPython}\n" ++ r#"if pinned_python is not None and sys.version.split()[0] != pinned_python:
    raise SystemExit(f'Python {sys.version.split()[0]} ({sys.executable}) is not {pinned_python}, '
                     'the Python the committed data were generated under: pass --python naming a '
                     f'Python {pinned_python} that imports Pygments {pinned}, such as DIR/bin/python3 '
                     f'after python{pinned_python.rsplit(".", 1)[0]} -m venv DIR and DIR/bin/pip '
                     f'install pygments=={pinned}')
"# ++ pygmentsLoader ++ r#"if pygments.__version__ != pinned:
    raise SystemExit(f'Pygments {pygments.__version__} ({pygments.__file__}) is not {pinned}, the '
                     'release the committed data were generated from: pass --python naming an '
                     'interpreter that imports it, such as DIR/bin/python3 after '
                     f'{sys.executable} -m venv DIR and DIR/bin/pip install pygments=={pinned}')
"#

/-- A generator's `--selftest`: under a venv whose only Pygments is a stub, `pinnedLoader` passes
exactly its own release and Python, and the generator's bridge refuses the stub by its pins. -/
def pinSelftest (name bridge : String) (python : Option String := none) : IO UInt32 :=
  IO.FS.withTempDir fun dir => do
    let venv := dir / "venv"
    let made ← IO.Process.output
      { cmd := "python3", args := #["-m", "venv", "--without-pip", venv.toString] }
    let exe := (venv / "bin" / "python3").toString
    let site ← if made.exitCode == 0 then
        IO.Process.output { cmd := exe, args := #["-I", "-c",
          "import sys, sysconfig; print(sysconfig.get_path('purelib')); print(sys.version.split()[0])"] }
      else pure made
    let (lib, own) := match site.stdout.trimAscii.toString.splitOn "\n" with
      | [lib, own] => (lib, own)
      | _ => ("", "")
    unless site.exitCode == 0 && lib.startsWith venv.toString do
      IO.eprintln s!"{name} --selftest: python3 made no venv to stub:\n{site.stderr}"
      return 1
    let stub := System.FilePath.mk lib / "pygments"
    IO.FS.createDirAll stub
    IO.FS.writeFile (stub / "__init__.py") "__version__ = '1.0.0'\n"
    IO.FS.writeFile (stub / "plugin.py") ""
    let run (code : String) := IO.Process.output { cmd := exe, args := #["-I", "-B", "-c", code] }
    let preamble := "import pathlib\nimport shutil\nimport sys\n"
    let passes (code : String) : IO Bool := do
      let o ← run (preamble ++ code ++ "print('read')\n")
      return o.exitCode == 0 && o.stdout == "read\n"
    let refuses (code found pin : String) : IO Bool := do
      let o ← run code
      return o.exitCode != 0 && (o.stderr.splitOn found).length > 1 &&
        (o.stderr.splitOn s!"is not {pin}").length > 1
    let (found, pin) := match python with
      | some v => if v != own then (s!"Python {own}", v) else ("Pygments 1.0.0", pygmentsRelease)
      | none => ("Pygments 1.0.0", pygmentsRelease)
    let mut ok := true
    let mut count := 0
    for (what, held) in [("its own release passes", ← passes (pinnedLoader none "1.0.0")),
        ("an older release is refused",
          ← refuses (preamble ++ pinnedLoader none "1.0.1") "Pygments 1.0.0" "1.0.1"),
        ("a newer release is refused",
          ← refuses (preamble ++ pinnedLoader none "0.9.9") "Pygments 1.0.0" "0.9.9"),
        ("its own Python passes", ← passes (pinnedLoader (some own) "1.0.0")),
        ("another Python is refused",
          ← refuses (preamble ++ pinnedLoader (some "0.0.0") "1.0.0") s!"Python {own}" "0.0.0"),
        (s!"the bridge refuses the stub naming {found} and {pin}", ← refuses bridge found pin)] do
      count := count + 1
      unless held do
        IO.eprintln s!"{name} --selftest: not so: {what}"
        ok := false
    if ok then IO.println s!"{name} --selftest: ok ({count} cases)"
    return if ok then 0 else 1

end GenData
