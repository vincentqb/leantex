/-
The construct-support rungs: one vocabulary for the two tiers that rank
constructs — `coverage`, which reads a construct's rung off its probe, and
`diagaudit`, which records the rung a diagnostic code's verdict targets.
The readings (`rungOfLoss`, the coverage cut) stay with the tier that makes
them; only the words and their order live here.
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
