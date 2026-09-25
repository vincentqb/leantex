/-
The landing procedure's pure core: a state machine over observations, whose
only outputs are actions. No IO lives here, so every refusal, every
ordering constraint, and the one property that matters — a ref others read
is never touched on an unproven run — is decidable from values and
provable, with git and lake nowhere in sight.

The defect this exists to make impossible: a coordinating agent reported
three merges, a push and three worktrees that did not exist, because it
read tool narration instead of repository state. So an observation here is
never prose. A sha is a sha only if it reads as forty hex digits
(`isSha`), and anything the boundary could not parse arrives as
`Obs.garbled`, which halts. Truncation is thereby a *failure*, not a
silently-shortened success — the shape the driver's file-backed probes feed.
-/

namespace Land

/-- A commit name, as read back from `git rev-parse`. -/
abbrev Sha := String

/-- Forty lowercase hex digits and nothing else. A truncated, padded,
decorated or empty read fails here, which is how garbled output becomes a
refusal rather than a comparison between two wrong strings. -/
def isSha (s : String) : Bool :=
  s.length == 40 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- What a finished run says on its last line. `checked` is `land check`'s
verdict: the gates ran and passed, and nothing was landed. -/
inductive Verdict where
  | landed
  | checked
  | refused
  | failed
  /-- `land new` succeeded. -/
  | created
  /-- `land retire` succeeded. -/
  | retired
  /-- `land status` printed its listing. -/
  | listed
  deriving DecidableEq, Repr, Inhabited

def Verdict.name : Verdict → String
  | .landed => "landed"
  | .checked => "checked"
  | .refused => "refused"
  | .failed => "failed"
  | .created => "created"
  | .retired => "retired"
  | .listed => "listed"

/-- Which command the run is: a landing may mutate refs, a check never
reaches the stage that can. -/
inductive Mode where
  | land
  | check
  deriving DecidableEq, Repr, Inhabited

/-- Where the run stands; the order is the procedure's order. -/
inductive Stage where
  | preMain
  | preBranch
  | rebasing
  | gating
  | ffing
  | verifying
  | ledgering
  | pushing
  | verifyPush
  | done
  deriving DecidableEq, Repr, Inhabited

def Stage.name : Stage → String
  | .preMain => "pre-main"
  | .preBranch => "pre-branch"
  | .rebasing => "rebase"
  | .gating => "gate"
  | .ffing => "fast-forward"
  | .verifying => "verify"
  | .ledgering => "ledger"
  | .pushing => "push"
  | .verifyPush => "verify-push"
  | .done => "done"

/-- What the boundary reports. Every constructor is a parsed fact; the
`garbled` arm is what the boundary sends when it could not produce one. -/
inductive Obs where
  /-- `git status --porcelain` in the main worktree read back empty. -/
  | mainStatus (clean : Bool)
  /-- The branch: does it exist, how far ahead and behind `main`, and is its
  own worktree clean. -/
  | branchStatus (present : Bool) (ahead behind : Nat) (clean : Bool)
  | rebaseOk
  | rebaseConflict (files : Array String)
  | gateOk (name : String)
  | gateFail (name : String)
  /-- The gate's program is not built. A concurrently-built sibling gate is
  the one permitted absence; it is recorded, and is not a gate observation. -/
  | gateAbsent (name : String)
  | ffOk
  /-- The branch tip and `main`'s tip, read back after the fast-forward. -/
  | tips (branchTip mainTip : Sha)
  | ledgerOk
  | ledgerFail
  | pushOk
  /-- `origin/main` and `main`, read back after the push. -/
  | originTips (originTip mainTip : Sha)
  /-- The boundary could not parse what a command produced. -/
  | garbled (what : String)
  deriving Repr, Inhabited

/-- One gate's outcome, as recorded in the run. An absent gate does not
appear here: an absence is not an observation that a gate passed. -/
structure GateObs where
  name : String
  ok : Bool
  deriving DecidableEq, Repr, Inhabited

/-- What the core asks the boundary to do next. `halt` ends the run. -/
inductive Act where
  | probeMain
  | probeBranch
  | rebase
  | gate (name : String)
  | fastForward
  | readTips
  | writeLedger
  | push
  | readOrigin
  /-- Stop. `abortRebase` asks the boundary to leave the branch worktree as
  it found it before reporting. -/
  | halt (v : Verdict) (code : UInt32) (why : String) (abortRebase : Bool)
  deriving Repr, Inhabited

/-- The two actions that change a ref another worktree or remote reads: the
fast-forward of `main`, and the push. Everything else is a read, a build, or
a write confined to the branch's own worktree or to the ledger. -/
def Act.mutates : Act → Bool
  | .fastForward => true
  | .push => true
  | _ => false

structure State where
  name : String
  mode : Mode
  stage : Stage
  /-- Every gate observation the run has made, in order. -/
  gates : Array GateObs
  /-- Gates whose program was absent. -/
  skipped : Array String
  /-- Gate names not yet run, in order. -/
  pending : Array String
  wantPush : Bool
  landedTip : Sha
  verdict : Option Verdict
  deriving Repr, Inhabited

/-- Was every gate observation in the run ok? -/
def State.gatesOk (s : State) : Bool := s.gates.all (·.ok)

/-- The run has earned a ref change: at least one gate was observed, and
every observation was ok. The second half alone is vacuously true of a run
in which no gate ever ran, which is the other way this property could hold
while proving nothing. -/
def State.proven (s : State) : Bool := !s.gates.isEmpty && s.gatesOk

def State.init (name : String) (mode : Mode) (gates : Array String)
    (wantPush : Bool) : State :=
  { name, mode, stage := .preMain, gates := #[], skipped := #[],
    pending := gates, wantPush, landedTip := "", verdict := none }

private def refuse (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .refused },
   .halt .refused 2 why false)

private def internal (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .failed },
   .halt .failed 3 why false)

private def gateFailed (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .failed },
   .halt .failed 1 why false)

private def succeed (s : State) (v : Verdict) : State × Act :=
  ({ s with stage := .done, verdict := some v }, .halt v 0 "" false)

/-- The gates are done. Either the check ends here, or the fast-forward is
proposed — and only under the guard, written out rather than argued for. -/
private def afterGates (s : State) : State × Act :=
  if s.proven then
    match s.mode with
    | .check => succeed s .checked
    | .land => ({ s with stage := .ffing }, .fastForward)
  else
    gateFailed s "no gate observation in this run, or one was not ok"

private def nextGate (s : State) : State × Act :=
  match s.pending[0]? with
  | some g => ({ s with pending := s.pending.extract 1 s.pending.size }, .gate g)
  | none => afterGates s

/-- One observation, one action. Every pair the procedure does not expect is
an internal failure: a state machine driven off its own transitions is
exactly the condition under which narration got believed. -/
def step (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | _, .garbled what => internal s s!"unparseable output: {what}"
  | .preMain, .mainStatus clean =>
    if clean then ({ s with stage := .preBranch }, .probeBranch)
    else refuse s "the main worktree is dirty"
  | .preBranch, .branchStatus present ahead _ clean =>
    if !present then refuse s s!"no branch agent/{s.name}"
    else if ahead == 0 then refuse s s!"agent/{s.name} is not ahead of main"
    else if !clean then refuse s s!"the worktree of agent/{s.name} is dirty"
    else ({ s with stage := .rebasing }, .rebase)
  | .rebasing, .rebaseOk => nextGate { s with stage := .gating }
  | .rebasing, .rebaseConflict files =>
    ({ s with stage := .done, verdict := some .refused },
     .halt .refused 2 s!"rebase conflict: {String.intercalate " " files.toList}" true)
  | .gating, .gateOk g => nextGate { s with gates := s.gates.push ⟨g, true⟩ }
  | .gating, .gateFail g =>
    gateFailed { s with gates := s.gates.push ⟨g, false⟩ } s!"gate {g} failed"
  | .gating, .gateAbsent g => nextGate { s with skipped := s.skipped.push g }
  | .ffing, .ffOk => ({ s with stage := .verifying }, .readTips)
  | .verifying, .tips bt mt =>
    if isSha bt && isSha mt && bt == mt then
      ({ s with stage := .ledgering, landedTip := mt }, .writeLedger)
    else internal s "main did not read back at the branch tip"
  | .ledgering, .ledgerOk =>
    if s.wantPush then
      if s.proven then ({ s with stage := .pushing }, .push)
      else gateFailed s "no gate observation in this run, or one was not ok"
    else succeed s .landed
  | .ledgering, .ledgerFail => internal s "the ledger was not written"
  | .pushing, .pushOk => ({ s with stage := .verifyPush }, .readOrigin)
  | .verifyPush, .originTips ot mt =>
    if isSha ot && isSha mt && ot == mt then succeed s .landed
    else internal s "origin/main did not read back at main"
  | st, ob => internal s s!"{st.name}: unexpected {reprStr ob}"

/-- Drive the core through a scripted observation sequence, collecting the
actions it proposed. The selftest's harness, and the shape the run-level
corollary quantifies over. -/
def run (s : State) : List Obs → State × Array Act
  | [] => (s, #[])
  | o :: os =>
    let (s', a) := step s o
    let (s'', as) := run s' os
    (s'', #[a] ++ as)

-- ## The theorem
--
-- The brief's property, and the two ways it could have held vacuously.

/-- **No ref another party reads is touched on a run whose gates were not
all ok.** Stated over the step function: whenever `step` proposes the
fast-forward or the push, the resulting state is `proven` — at least one
gate was observed, and every gate observation in the run was ok. -/
theorem step_mutates_gated (s : State) (o : Obs) :
    ((step s o).2).mutates = true → (step s o).1.proven = true := by
  intro h
  unfold step at h ⊢
  repeat' first
    | split at h
    | (unfold nextGate at h ⊢)
    | (unfold afterGates at h ⊢)
  all_goals
    simp_all [Act.mutates, refuse, internal, gateFailed, succeed, State.proven,
      State.gatesOk]

/-- Unfolded: every gate observation the run made was ok. The brief's words,
as a corollary of the statement above. -/
theorem step_mutates_all_gates_ok (s : State) (o : Obs) :
    ((step s o).2).mutates = true → (step s o).1.gates.all (·.ok) = true := by
  intro h
  have := step_mutates_gated s o h
  simp_all [State.proven, State.gatesOk]

/-- And at least one gate was observed: the guard is not satisfied by a run
that skipped the gates entirely. -/
theorem step_mutates_needs_a_gate (s : State) (o : Obs) :
    ((step s o).2).mutates = true → (step s o).1.gates.isEmpty = false := by
  intro h
  have := step_mutates_gated s o h
  simp_all [State.proven]

/-- The fast-forward is proposed only with no gate left to run: the gate
list is exhausted, not merely unfalsified. -/
theorem step_ff_gates_complete (s : State) (o : Obs) :
    (step s o).2 = .fastForward → (step s o).1.pending.isEmpty = true := by
  intro h
  unfold step at h ⊢
  repeat' first
    | split at h
    | (unfold nextGate at h ⊢)
    | (unfold afterGates at h ⊢)
  all_goals simp_all [refuse, internal, gateFailed, succeed, State.proven]

end Land
