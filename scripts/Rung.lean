module

/- The construct-support vocabulary the tiers share: the rungs, and the compat-index row,
its verdicts and the index's one reader. -/
public section

/-- The support rungs, per construct, lowest first, each a reading of the diagnostics
whose subject names the construct; above `rewritten` the order is the coverage cut. -/
inductive Rung where
  /-- Nothing was measured: every shape produced only diagnostics about the probe's own
  malformed arguments. -/
  | unprobed
  /-- Nothing answers the name and its arguments survive as text: W0301/W0302, or W0012
  for a name the math parser does not know. -/
  | unknown
  /-- Recognised, and the construct earns a `dropped` code: the content is
  gone and no plan owns it. -/
  | fails
  /-- Recognised, and the construct earns a `config` code or is consumed with nothing to
  show for it: no content operand, the content's meaning survives. -/
  | skipped
  /-- Recognised, and the construct earns a `degraded` or `pending` code:
  the content is kept, but not as declared, or it is owed. -/
  | degraded
  /-- Translated onto a native construct: an `info` code, the conservation of the
  translation owed; a rewrite onto nothing is `skipped`. -/
  | rewritten
  /-- Implemented natively: no code, and the usage differs from the same usage under an
  unknown name. -/
  | native
  /-- The construct's one-construct probe holds at P3 or better against lualatex; nothing
  here awards it. -/
  | verified
deriving Inhabited, BEq, Repr

def Rung.level : Rung → Nat
  | .unprobed => 0
  | .unknown => 1
  | .fails => 2
  | .skipped => 3
  | .degraded => 4
  | .rewritten => 5
  | .native => 6
  | .verified => 7

def Rung.word : Rung → String
  | .unprobed => "unprobed"
  | .unknown => "unknown"
  | .fails => "fails"
  | .skipped => "skipped"
  | .degraded => "degraded"
  | .rewritten => "rewritten"
  | .native => "native"
  | .verified => "verified"

/-- Every rung, for the report's buckets. -/
def Rung.all : List Rung :=
  [.unprobed, .unknown, .fails, .skipped, .degraded, .rewritten, .native, .verified]

/-- One row of `testdata/compat-index/<pkg>.txt`: `<place> <verdict> <call>`, a documented
command with the verdict the engine owes it. -/
structure IndexRow where
  place : String
  verdict : String
  call : String
deriving Inhabited

/-- A row, or `none` for a blank or `#` line. -/
def IndexRow.parse? (line : String) : Option IndexRow :=
  let l := line.trimAscii.toString
  if l.isEmpty || l.startsWith "#" then none
  else
    let place := (l.splitOn " ").headD ""
    let rest := (l.drop place.length).toString.trimAscii.toString
    let verdict := (rest.splitOn " ").headD ""
    some { place, verdict, call := (rest.drop verdict.length).toString.trimAscii.toString }

/-- Whether a compat-index row is implemented: `impl`, or `inert:` for a recognised
command that legitimately moves no ink. -/
def IndexRow.implemented (r : IndexRow) : Bool :=
  r.verdict == "impl" || r.verdict.startsWith "inert:"

/-- The exact, non-empty code of a `refuse:<code>` verdict. -/
def IndexRow.refusalCode? (r : IndexRow) : Option String :=
  match r.verdict.splitOn ":" with
  | ["refuse", code] => if code.isEmpty then none else some code
  | _ => none

def IndexRow.refused (r : IndexRow) : Bool := r.refusalCode?.isSome

def compatIndexDir : System.FilePath := "testdata/compat-index"

/-- Every package index under `dir`, in file-name order; missing input or no rows at all
is a measurement fault. -/
def readCompatIndexAt (dir : System.FilePath) : IO (Array (String × Array IndexRow)) := do
  unless ← dir.isDir do
    throw <| IO.userError s!"compat index: {dir} is missing"
  let mut out : Array (String × Array IndexRow) := #[]
  for entry in (← dir.readDir).map (·.fileName) |>.qsort (· < ·) do
    unless entry.endsWith ".txt" do continue
    let text ← IO.FS.readFile (dir / entry)
    out := out.push ((entry.dropEnd ".txt".length).toString,
      ((text.splitOn "\n").filterMap IndexRow.parse?).toArray)
  if out.isEmpty then
    throw <| IO.userError s!"compat index: {dir} contains no .txt files"
  if out.all (fun p => p.2.isEmpty) then
    throw <| IO.userError s!"compat index: {dir} contains no rows"
  return out

/-- Every package's rows, in file-name order. -/
def readCompatIndex : IO (Array (String × Array IndexRow)) :=
  readCompatIndexAt compatIndexDir
