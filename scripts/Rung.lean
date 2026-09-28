/-
The construct-support vocabulary the tiers share: the rungs — one ladder for
`coverage`, which reads a construct's rung off its probe, and `diagaudit`,
which records the rung a diagnostic code's verdict targets — and the verdict
a compat-index row declares, which `compat` counts and `coverage` judges
with. The readings (`rungOfLoss`, the coverage cut) stay with the tier that
makes them; only the words, their order and the index's one reader live
here, so no two tiers can mean different things by one word.
-/
/-- The support rungs, per construct, lowest first. Words, not numbers:
`P0`–`P5` and R name the parity ladder's per-document levels, `L0`–`L2`
the theorem layers, and `L3` also names LaTeX3, so numbering the rungs too
would be one meaning per label too many.

Each rung is a reading of the diagnostics whose subject names the
construct, so the ladder derives from `Loss` in one place exactly as
`Loss.severity`, `Loss.floor` and `Loss.censused` do — `config` and
`dropped` losses have rungs here, which the numbered draft of this ladder
left with none.

The order below `rewritten` is a reporting convention and not a claim that
a skipped construct is worse than a degraded one: it decides only which
word gets published for a name that earns two, and nothing reads it as a
judgement. Above `rewritten` the order is load-bearing — it is the
coverage cut. -/
inductive Rung where
  /-- Nothing was measured: every shape produced only diagnostics about the
  probe's own malformed arguments. Not a gap we owe; a probe we owe. -/
  | unprobed
  /-- Nothing answers the name; its arguments survive as text.
  W0301/W0302, and W0012 for a name the math parser does not know. -/
  | unknown
  /-- Recognised, and the construct earns a `dropped` code: the content is
  gone and no plan owns it. -/
  | fails
  /-- Recognised, and the construct earns a `config` code: no content
  operand, nothing modelled, the meaning of the content survives. Also the
  reading for a construct recognised and consumed with nothing to show for
  it: the engine's own note that it rewrote the construct to nothing
  (`ctrl:nothing:<name>`), or no code at all and no difference from the
  same usage under a name nothing knows. -/
  | skipped
  /-- Recognised, and the construct earns a `degraded` or `pending` code:
  the content is kept, but not as declared, or it is owed. -/
  | degraded
  /-- Translated onto a native construct: an `info` code, the conservation
  of the translation owed. A rewrite onto nothing is `skipped`. -/
  | rewritten
  /-- Implemented natively: no code, and the usage differs from the same
  usage under a name nothing knows. That difference shows the construct
  consumed what it was given, not that anything came of it — a deletion
  comparison would ask more, and it demotes `\setcounter` and `\textwidth`,
  whose effect needs a later construct to show. The effect is the parity
  ladder's to witness. -/
  | native
  /-- The construct's own one-construct probe holds at P3 or better against
  lualatex. The rung that joins this ladder to the parity ladder; it is the
  only one that needs a rendered page, so nothing here can award it and
  this script never does. -/
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

/-- One row of `tests/compat-index/<pkg>.txt`: `<place> <verdict> <call>`,
one documented command of a package with the verdict the engine owes it.
The format is `lake test`'s (`compatIndexChecks` probes every row); this is
the one reader the tiers count with. -/
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

/-- **One definition of "implemented" for a compat-index row**: `impl`, or
`inert:` — a recognised command that legitimately moves no ink, with the
reason reviewed in the row itself. The `compat` tier counts with it and the
`coverage` tiers judge with it; the two once disagreed on the four
`refuse:N0102` rows, which is the drift one shared predicate exists to stop. -/
def IndexRow.implemented (r : IndexRow) : Bool :=
  r.verdict == "impl" || r.verdict.startsWith "inert:"

def IndexRow.refused (r : IndexRow) : Bool := r.verdict.startsWith "refuse:"

/-- A **decided divergence**: `divergence:<code>`, a row where the engine
differs from LaTeX by a decision, not by a gap it owes — the user's
decision (PLAN, the human gates: a new deliberate divergence from LaTeX).
`lake test` holds it to the refusal's rule, so `<code>` fires wherever the
divergence happens and it is never silent. It leaves every tier's
denominator and is listed instead: a gap that becomes a divergence is a
`<p>.rows` fall, which the ratchet takes only from a human-written
`# lowered:` line. -/
def IndexRow.decided (r : IndexRow) : Bool := r.verdict.startsWith "divergence:"

/-- A row still open or implemented: what a tier's denominator counts. -/
def IndexRow.scored (r : IndexRow) : Bool := !r.decided

def compatIndexDir : System.FilePath := "tests/compat-index"

/-- Every package's rows, in file-name order. -/
def readCompatIndex : IO (Array (String × Array IndexRow)) := do
  let mut out : Array (String × Array IndexRow) := #[]
  if !(← compatIndexDir.isDir) then return out
  for entry in (← compatIndexDir.readDir).map (·.fileName) |>.qsort (· < ·) do
    unless entry.endsWith ".txt" do continue
    let text ← IO.FS.readFile (compatIndexDir / entry)
    out := out.push ((entry.dropEnd ".txt".length).toString,
      ((text.splitOn "\n").filterMap IndexRow.parse?).toArray)
  return out
