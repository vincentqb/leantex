import LeanTex.Core.Diag

/-! The boundary cache's vocabulary, as values: how one picture request's
attempt ended, whether that ending is the tool's own verdict, and what the
next run does about it — IO-free, so the one-attempt-per-request invariant
is checked without a tool installed. Main.lean reads and writes the files
named here and supplies the process results; the policy is all here, where
it can be stated. -/

namespace LeanTex.Cli.PicCache

/-- How one boundary process ended. `exited` is the tool's own exit — it
ran to a decision; `overran` is the wall-clock budget spent with the
process killed; `unstarted` is a spawn that raised. The last two say
nothing about the request, only about the machine. -/
inductive Ran where
  | exited (code : Nat)
  | overran (seconds : Nat)
  | unstarted (err : String)
  deriving BEq, Repr

/-- What the tool left behind of one attempt: its log's last words, or no
log at all. A tool that never ran writes nothing — a spawn that reached
`exec` and failed there still comes back as an exit code — so the log's
presence is the platform-independent evidence that the tool formed an
opinion rather than that the machine lacks it. -/
inductive Log where
  | absent
  | says (tail : String)
  deriving BEq, Repr

/-- The log's last words, empty when there is no log. -/
def Log.tail : Log → String
  | .absent => ""
  | .says t => t

/-- What the tool answered about one request. `drawn` is a PDF; `refused`
is the tool's own no, carrying its last words verbatim; `inconclusive` is
an attempt that never reached an answer. -/
inductive Outcome where
  | drawn
  | refused (says : String)
  | inconclusive (says : String)
  deriving BEq, Repr

/-- One attempt read as a verdict: the process's ending, whether a PDF
landed, and what the tool left in its log. An exit the tool chose *and
left a log for* is a verdict — nonzero with its last words, or zero with
nothing drawn. A budget kill, a failed spawn, and a nonzero exit that left
no log at all are not: each says something about the machine, and a machine
without the tool installed must not be able to make a picture look
unrenderable. -/
def outcome (ran : Ran) (drew : Bool) (log : Log) : Outcome :=
  let said (fallback : String) : String :=
    if log.tail.isEmpty then fallback else log.tail
  match ran with
  | .exited 0 => if drew then .drawn else .refused "no PDF was produced"
  | .exited c =>
    match log with
    | .absent => .inconclusive s!"exit code {c}"
    | .says _ => .refused (said s!"exit code {c}")
  | .overran s => .inconclusive (said s!"no result within {s} s; killed")
  | .unstarted e => .inconclusive (said e)

/-- What the cache keeps of an outcome: the tool's own refusal, and
nothing else. A drawn picture is kept as its PDF, and an inconclusive
attempt is kept not at all — so the next build retries it. -/
def remembers : Outcome → Option String
  | .drawn => none
  | .refused says => some says
  | .inconclusive _ => none

/-- The cache slot one request takes: its content hash and the tool's
version, so an edited picture reads a different slot and is retried, and a
tool upgrade retries every one. -/
def stem (key version : String) : String := key ++ "-" ++ version

/-- The drawn PDF's name in the slot. -/
def pdfName (key version : String) : String := stem key version ++ ".pdf"

/-- The remembered refusal's name in the slot, beside the PDF: one slot
per request, whichever way the tool answered. -/
def failName (key version : String) : String := stem key version ++ ".fail"

/-- What a run does about one request. -/
inductive Step where
  | serve
  | replay (says : String)
  | run
  deriving BEq, Repr

/-- The cache decides in one place: a drawn PDF serves, else a remembered
refusal replays with the tool's own words, else the tool runs. -/
def step (drawn : Bool) (refusal : Option String) : Step :=
  if drawn then .serve
  else match refusal with
    | some says => .replay says
    | none => .run

/-- **A remembered verdict is never re-attempted.** The tool runs exactly
when the slot holds neither a drawn PDF nor a remembered refusal — the
invariant whose absence made every unrenderable picture pay a fresh
process on every build, forever, while a renderable one paid once. -/
theorem step_cold_exact (drawn : Bool) (refusal : Option String) :
    step drawn refusal = .run ↔ (drawn = false ∧ refusal = none) := by
  unfold step
  cases drawn with
  | true => simp
  | false => cases refusal <;> simp

/-- **A replay carries the tool's own words.** What a remembered refusal
reports is the string the tool gave, never a stand-in: the diagnostic
reads the same on the second build as on the first. -/
theorem replay_says_exact (says : String) :
    step false (some says) = .replay says := rfl

/-- **Only the tool's own refusal is remembered.** A verdict is written
exactly when the tool reached one and said no; a kill and a failed spawn
write nothing, so nothing the machine did can be mistaken for something
the request is. -/
theorem remembers_verdict_exact (o : Outcome) (says : String) :
    remembers o = some says ↔ o = .refused says := by
  cases o <;> simp [remembers]

/-- **A killed attempt is retried.** The composition of the two halves, at
the shape that matters: a budget overrun leaves the slot as it found it, so
the next build runs the tool again. -/
theorem overrun_retried_exact (s : Nat) (drew : Bool) (log : Log) :
    remembers (outcome (.overran s) drew log) = none := rfl

/-- **A tool that left no log is retried.** The other half of the same
guard, and the one a machine without the tool installed lands on: a spawn
that reached `exec` and failed there comes back as an exit code like any
other failure, so the absent log is what separates it from a verdict. Its
diagnostic still fires — the loss is named on every build — but the slot
stays empty, so installing the tool is all it takes. -/
theorem unlogged_retried_exact (c : Nat) (hc : c ≠ 0) (drew : Bool) :
    remembers (outcome (.exited c) drew .absent) = none := by
  unfold outcome remembers
  cases c with
  | zero => exact absurd rfl hc
  | succ _ => rfl

end LeanTex.Cli.PicCache
