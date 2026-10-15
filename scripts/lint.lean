import Lean.Data.Json

open Lean (Json)

namespace Lint

/-- The sequential stages: the build every check reads, then the fast whole-tree
convention pass; a failure stops the run. -/
def first : Array (String × Array String) := #[
  ("lake", #["build", "--wfail", "precommit", "proofcheck", "cites"]),
  (".lake/build/bin/proofcheck", #["--build"]),
  (".lake/build/bin/precommit", #["--tree", "--conventions"])]

/-- The checks over that build, run concurrently and reported in stage order. -/
def concurrent : Array (String × Array String) := #[
  (".lake/build/bin/proofcheck", #["--check"]),
  (".lake/build/bin/proofcheck", #["--selftest"]),
  (".lake/build/bin/precommit", #["--selftest"]),
  (".lake/build/bin/cites", #["--selftest"]),
  (".lake/build/bin/cites", #["--check"]),
  (".lake/build/bin/lint", #["--linters"])]

def check : IO UInt32 := do
  for (cmd, args) in first do
    let code ← (← IO.Process.spawn { cmd, args }).wait
    if code != 0 then return code
  let runs ← concurrent.mapM fun (cmd, args) =>
    IO.asTask (IO.Process.output { cmd, args }) .dedicated
  let mut status : UInt32 := 0
  for (run, (cmd, args)) in runs.zip concurrent do
    let code ← match run.get with
      | .ok out => do
        IO.print out.stdout
        IO.eprint out.stderr
        pure out.exitCode
      | .error e => do
        IO.eprintln s!"lint: {cmd} {" ".intercalate args.toList} did not start: {e}"
        pure 1
    if status == 0 then status := code
  return status

/-- A configured linter option, a file that option makes Lean warn on, and the option the
warning's note names. -/
structure Probe where
  option : String
  note : String
  source : String

/-- The linters the lakefile's `leanOptions` turns on, exactly, each with its probes. -/
def probes : Array Probe := #[
  { option := "linter.unusedVariables", note := "linter.unusedVariables"
    source := "def probe (used unused : Nat) : Nat := used\n" },
  { option := "linter.unusedVariables", note := "linter.unusedVariables"
    source := "def probe : Nat → Nat\n  | unused => 0\n" },
  { option := "linter.unusedVariables.analyzeTactics", note := "linter.unusedVariables"
    source := "theorem probe (n : Nat) : n = n := by\n  have unused : n = n := rfl\n  rfl\n" },
  { option := "linter.extra", note := "linter.extra.dupNamespace"
    source := "def Probe.Probe.x : Nat := 1\n" },
  { option := "linter.extra", note := "linter.extra.unnecessarySeqFocus"
    source := "example : True := by skip <;> trivial\n" },
  { option := "linter.extra", note := "linter.extra.unreachableTactic"
    source := "example : True := by first | trivial | skip\n" },
  { option := "linter.extra", note := "linter.extra.unusedDecidableInType"
    source := "theorem probe {α : Type} [DecidableEq α] (a : α) : a = a := rfl\n" },
  { option := "linter.omit", note := "linter.omit"
    source := "variable (k : Nat) in\nomit k in\ntheorem probe : True := trivial\n" }]

/-- The note Lean ends a warning of the linter `o` with. -/
def noteOf (o : String) : String :=
  s!"Note: This linter can be disabled with `set_option {o} false`"

/-- How many times `pat` occurs in `s`. -/
def count (s pat : String) : Nat := (s.splitOn pat).length - 1

/-- The options every compiled module must have been given: each probed option, on, by name. -/
def expected : List (String × Json) :=
  ((probes.map (·.option)).toList.eraseDups.map (·, Json.bool true)).mergeSort (·.1 ≤ ·.1)

/-- The compiled modules' recorded `lean` setups, by source path, skipping a setup whose
source is gone. -/
def recorded : IO (Array (String × Json)) := do
  let root := ".lake/build/ir"
  let ext := ".setup.json"
  let mut out := #[]
  for p in ← System.FilePath.walkDir root do
    let s := p.toString
    unless s.startsWith s!"{root}/" && s.endsWith ext do continue
    let src := (s.drop (root.length + 1) |>.dropEnd ext.length).toString ++ ".lean"
    if ← System.FilePath.pathExists src then
      match Json.parse (← IO.FS.readFile p) with
      | .ok j => out := out.push (src, j)
      | .error e => throw (IO.userError s!"{s}: {e}")
  return out

/-- The text Lean prints compiling `source` under `setup`, both written to `dir` as `name`. -/
def compile (dir : System.FilePath) (name source : String) (setup : Json) : IO String := do
  IO.FS.writeFile (dir / s!"{name}.lean") source
  IO.FS.writeFile (dir / s!"{name}.setup.json") setup.compress
  let args := #[(dir / s!"{name}.lean").toString, "--setup", (dir / s!"{name}.setup.json").toString]
  let out ← IO.Process.output { cmd := "lean", args }
  return out.stdout ++ out.stderr

/-- A setup with no imports and the given options. -/
def bare (options : Json) : Json :=
  Json.mkObj [("name", "LinterProbe"), ("package", "leantex"), ("isModule", false),
    ("importArts", Json.mkObj []), ("dynlibs", Json.arr #[]), ("plugins", Json.arr #[]),
    ("options", options)]

/-- The option a source line turns off with a set_option command, if a probe names it. -/
def disables (l : String) : Option String :=
  let named := probes.toList.flatMap fun p => [p.option, p.note]
  let rec go : List String → Option String
    | "set_option" :: o :: "false" :: _ =>
      if named.contains o || o.startsWith "linter.unusedVariables" then some o else none
    | _ :: rest => go rest
    | [] => none
  go ((l.splitOn " ").filter (!·.isEmpty))

/-- Every compiled module ran exactly the probed linters: each probe warns under them and not
with its option off, an unused parameter added to each library's smallest module draws exactly
that warning, and no source turns one off. -/
def linters : IO UInt32 := do
  let dir : System.FilePath := ".lake/build/lint"
  IO.FS.createDirAll dir
  let mut bad : Array String := #[]
  let setups ← recorded
  if setups.isEmpty then bad := bad.push "no compiled module under .lake/build/ir: build first"
  let optionsOf (j : Json) : Json := j.getObjValD "options"
  for (src, j) in setups do
    let got := (((optionsOf j).getObj?.toOption.map (·.toList)).getD []).filter fun (k, _) =>
      k.startsWith "linter." || k.startsWith "weak."
    unless got == expected do
      bad := bad.push s!"{src} was compiled with linter options {(Json.mkObj got).compress}, \
        not {(Json.mkObj expected).compress}"
  let on := (setups[0]?.map (optionsOf ·.2)).getD (Json.mkObj expected)
  let runs ← probes.zipIdx.mapM fun (p, i) => IO.asTask do
    let a ← compile dir s!"probe{i}" p.source (bare on)
    let b ← compile dir s!"probe{i}off" p.source (bare (on.setObjVal! p.option (Json.bool false)))
    return (p, a, b)
  for r in runs do
    match r.get with
    | .error e => bad := bad.push s!"a probe did not run: {e}"
    | .ok (p, a, b) =>
      if count a (noteOf p.note) == 0 then
        bad := bad.push s!"{p.option} drew no {p.note} warning on its probe:\n{p.source}{a}"
      if count b (noteOf p.note) != 0 then
        bad := bad.push s!"the probe for {p.option} warns with it off:\n{p.source}"
  for lib in ["LeanTex/", "Tests/", "scripts/"] do
    let mut least : Option (String × Json × Nat) := none
    for (src, j) in setups do
      if src.startsWith lib then
        let n := (← IO.FS.readFile src).length
        if least.all (n < ·.2.2) then least := some (src, j, n)
    let some (src, j, _) := least
      | bad := bad.push s!"no compiled module under {lib}"
    let out ← compile dir "mutant" ((← IO.FS.readFile src) ++
      "\ndef unusedParameterMutant (used unused : Nat) : Nat := used\n") j
    unless count out ": warning: " == 1 && count out (noteOf "linter.unusedVariables") == 1
        && count out "`unused`" ≥ 1 do
      bad := bad.push s!"{src} with an unused parameter added drew not just that warning:\n{out}"
  let mut sources : Array System.FilePath := #["Main.lean"]
  for root in ["LeanTex", "Tests", "scripts"] do
    sources := sources ++ (← System.FilePath.walkDir root).filter (·.toString.endsWith ".lean")
  for f in sources do
    for (l, k) in ((← IO.FS.readFile f).splitOn "\n").zipIdx do
      if let some o := disables l then bad := bad.push s!"{f}:{k + 1} turns {o} off"
  if bad.isEmpty then
    IO.println s!"lint: linters live in {setups.size} modules: {probes.size} probes, 3 mutants"
    return 0
  for m in bad do IO.eprintln s!"lint: {m}"
  return 1

end Lint

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => Lint.check
  | ["--linters"] => Lint.linters
  | _ => do
    IO.eprintln "usage: lint [--linters]"
    return 2
