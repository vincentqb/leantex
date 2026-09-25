/-
The landing procedure's pure core: a state machine over observations, whose
only outputs are actions. No IO lives here, so every refusal, every
ordering constraint, and the two properties that matter — a ref others read
is never touched on an unproven run, and a reported landing is a landing of
the commit the gates ran on — are decidable from values and provable, with
git and lake nowhere in sight.

The defect this exists to make impossible: a coordinating agent reported
three merges, a push and three worktrees that did not exist, because it
read tool narration instead of repository state. So an observation here is
never prose. A sha is a sha only if it reads as forty hex digits
(`isSha`), and anything the boundary could not parse arrives as
`Obs.garbled`, which halts. Truncation is thereby a *failure*, not a
silently-shortened success — the shape the driver's file-backed probes feed.

The second defect, reproduced through the first draft of this tool: a
`landed` row and a `pushed` row while `main` and the remote never moved,
because the run compared two live refs with each other instead of against
the commit under test. So a sha travels *with* the run. The rebase reports
the tip it produced, that tip is what the gates are held to, that tip is
what the fast-forward names, and every later read-back is compared to it —
never to whatever another ref happens to say by then.
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
  /-- The fast-forward held and was verified; the push was rejected. `main`
  moved, the remote did not. -/
  | landedUnpushed
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
  | .landedUnpushed => "landed-unpushed"
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

/-- Why the branch could not be read. Two facts, because one message for
both once reported a branch with no worktree as "no branch". -/
inductive BranchMiss where
  | noBranch
  | noWorktree
  deriving DecidableEq, Repr, Inhabited

def BranchMiss.why (name : String) : BranchMiss → String
  | .noBranch => s!"no branch agent/{name}"
  | .noWorktree => s!"agent/{name} has no worktree"

/-- Where the run stands; the order is the procedure's order. -/
inductive Stage where
  | preMain
  | preBranch
  | rebasing
  | gating
  /-- After the gates: is the branch still the commit they ran on, and is
  its worktree still clean? -/
  | postGate
  /-- Before the merge: is the main worktree still on `main`, still at the
  tip this run read at the start? -/
  | preMerge
  /-- The write-ahead ledger row, naming the gated tip before any ref moves. -/
  | announcing
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
  | .postGate => "post-gate"
  | .preMerge => "pre-merge"
  | .announcing => "announce"
  | .ffing => "fast-forward"
  | .verifying => "verify"
  | .ledgering => "ledger"
  | .pushing => "push"
  | .verifyPush => "verify-push"
  | .done => "done"

/-- What the boundary reports. Every constructor is a parsed fact; the
`garbled` arm is what the boundary sends when it could not produce one.

A gate observation carries the *index* the core dispatched and no name: the
name is the plan's to know, so a gate cannot be reported under another
gate's name and an absence cannot be claimed for a gate that may not be
absent. -/
inductive Obs where
  /-- The main worktree: is `HEAD` on `main`, is the tree clean, and what is
  its tip. Two bools rather than one, because a single conjunction reported
  "not on main" as "the main worktree is dirty". -/
  | mainStatus (onMain : Bool) (clean : Bool) (tip : Sha)
  | branchAbsent (miss : BranchMiss)
  /-- The branch: how far ahead and behind `main`, is its own worktree
  clean, and what is its tip before the rebase. -/
  | branchStatus (ahead behind : Nat) (clean : Bool) (tip : Sha)
  /-- The rebase succeeded and the branch now reads at this tip. This is the
  commit the gates run on and the only commit that may land. -/
  | rebaseOk (tip : Sha)
  /-- The rebase failed. `files` are the unmerged paths, empty when the
  rebase stopped for another reason; the remaining three fields are the
  read-back of the branch worktree *after* the boundary aborted. -/
  | rebaseFailed (files : Array String) (headTip : Sha) (onBranch clean : Bool)
  | gateOk (idx : Nat)
  | gateFail (idx : Nat)
  /-- The gate's program is not built. Permitted only where the plan says
  so; it is recorded, and it is not a gate observation. -/
  | gateAbsent (idx : Nat)
  /-- The branch, re-read after the gates. -/
  | branchRecheck (tip : Sha) (clean : Bool)
  /-- The main worktree, re-read before the merge. -/
  | mainRecheck (onMain : Bool) (tip : Sha)
  | ffOk
  | ffRejected
  /-- `refs/heads/main`, read back after the fast-forward. -/
  | mainTip (tip : Sha)
  | ledgerOk
  | ledgerFail
  | pushOk
  | pushRejected
  /-- The remote's `refs/heads/main`, read from `git ls-remote`. -/
  | remoteTip (tip : Sha)
  /-- The boundary could not parse what a command produced. -/
  | garbled (what : String)
  deriving Repr, Inhabited

/-- One gate in the plan. `mayAbsent` is the whole permission to skip: the
core grants it from here and from nowhere else. -/
structure GateSpec where
  name : String
  mayAbsent : Bool
  deriving DecidableEq, Repr, Inhabited

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
  /-- Run the gate at this index of the plan; the name is for the log. -/
  | gate (idx : Nat) (name : String)
  | recheckBranch
  | recheckMain
  /-- The write-ahead row: this run is about to move `main` to this tip. -/
  | writeLanding
  /-- Fast-forward `main` to exactly this commit — the tip the gates ran on,
  never a branch name that may have moved since. -/
  | fastForward (tip : Sha)
  | readMain
  | writeLanded
  | push
  | readRemote
  | halt (v : Verdict) (code : UInt32) (why : String)
  deriving Repr, Inhabited

/-- The two actions that change a ref another worktree or remote reads: the
fast-forward of `main`, and the push. Everything else is a read, a build, or
a write confined to the branch's own worktree or to the ledger. -/
def Act.mutates : Act → Bool
  | .fastForward _ => true
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
  /-- The gates to run, in order, with their permission to be absent. -/
  plan : Array GateSpec
  /-- How many of the plan's gates have been observed. Also the index the
  next observation must carry. -/
  gateIdx : Nat
  wantPush : Bool
  /-- `main`'s tip when the run started. The merge refuses unless `main` is
  still here. -/
  prevMainTip : Sha
  /-- The branch's tip before the rebase, so a failed rebase's read-back has
  a sha to be compared against. -/
  branchTip : Sha
  /-- The commit the rebase produced: what the gates ran on, what the merge
  names, what every later read-back is compared to. -/
  gatedTip : Sha
  /-- `main`, as read back after the fast-forward. Empty until then. -/
  mainAt : Sha
  verdict : Option Verdict
  deriving Repr, Inhabited

/-- Was every gate observation in the run ok? -/
def State.gatesOk (s : State) : Bool := s.gates.all (·.ok)

/-- The run has earned a ref change: at least one gate was observed, and
every observation was ok. The second half alone is vacuously true of a run
in which no gate ever ran, which is the other way this property could hold
while proving nothing. -/
def State.proven (s : State) : Bool := !s.gates.isEmpty && s.gatesOk

/-- Is the run at or past the fast-forward's verification? -/
def State.atOrPastFF (s : State) : Bool :=
  s.stage == .ledgering || s.stage == .pushing || s.stage == .verifyPush

/-- Does the run claim a landing? -/
def State.landedVerdict (s : State) : Bool :=
  s.verdict == some .landed || s.verdict == some .landedUnpushed

/-- The `main` this run read back is the commit the gates ran on, and that
commit is a real sha — so the equality is not two empty strings agreeing. -/
def State.landedIsGated (s : State) : Bool :=
  s.mainAt == s.gatedTip && isSha s.gatedTip

/-- From the fast-forward's verification onward, and under any verdict that
claims a landing, the landing is the gated commit's — and a verdict claiming
a landing appears only at `done`, which is what keeps the gated tip from
being rewritten under a live claim. Spelled as one boolean formula rather
than a match over stages: the invariant is proved against every transition,
and a match there multiplies each proof by the number of stages. -/
def State.pinned (s : State) : Bool :=
  (!(s.atOrPastFF || s.landedVerdict) || s.landedIsGated)
    && (!s.landedVerdict || s.stage == .done)

def State.init (name : String) (mode : Mode) (plan : Array GateSpec)
    (wantPush : Bool) : State :=
  { name, mode, stage := .preMain, gates := #[], skipped := #[], plan, gateIdx := 0,
    wantPush, prevMainTip := "", branchTip := "", gatedTip := "", mainAt := "",
    verdict := none }

private def refuse (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .refused }, .halt .refused 2 why)

private def internal (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .failed }, .halt .failed 3 why)

private def gateFailed (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .failed }, .halt .failed 1 why)

private def succeed (s : State) (v : Verdict) : State × Act :=
  ({ s with stage := .done, verdict := some v }, .halt v 0 "")

/-- The gates are done. Either the check ends here, or the branch is
re-read — and only under the guard, written out rather than argued for. -/
private def afterGates (s : State) : State × Act :=
  if s.proven then
    match s.mode with
    | .check => succeed s .checked
    | .land => ({ s with stage := .postGate }, .recheckBranch)
  else
    gateFailed s "no gate observation in this run, or one was not ok"

private def nextGate (s : State) : State × Act :=
  match s.plan[s.gateIdx]? with
  | some g => (s, .gate s.gateIdx g.name)
  | none => afterGates s

/-- The preconditions and the rebase: `preMain`, `preBranch`, `rebasing`.
Split out from `step` so a theorem about the merge half unfolds none of it —
the whole machine in one match walled every proof off behind a heartbeat
limit, and a limit raised is not a factorization. -/
private def stepPre (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .preMain, .mainStatus onMain clean tip =>
    if !onMain then refuse s "the main worktree is not on main"
    else if !clean then refuse s "the main worktree is dirty"
    else if !isSha tip then internal s "main's tip did not read back as a sha"
    else ({ s with stage := .preBranch, prevMainTip := tip }, .probeBranch)
  | .preBranch, .branchAbsent m => refuse s (m.why s.name)
  | .preBranch, .branchStatus ahead _ clean tip =>
    if ahead == 0 then refuse s s!"agent/{s.name} is not ahead of main"
    else if !clean then refuse s s!"the worktree of agent/{s.name} is dirty"
    else if !isSha tip then internal s "the branch tip did not read back as a sha"
    else ({ s with stage := .rebasing, branchTip := tip }, .rebase)
  | .rebasing, .rebaseOk tip =>
    if !isSha tip then internal s "the rebased tip did not read back as a sha"
    else nextGate { s with stage := .gating, gatedTip := tip }
  | .rebasing, .rebaseFailed files headTip onBranch clean =>
    -- The boundary has already aborted; this is the read-back of what it
    -- left behind, and the only thing that may be reported.
    if !(onBranch && clean && headTip == s.branchTip && isSha headTip) then
      internal s s!"agent/{s.name} was left mid-rebase"
    else if !files.isEmpty then
      refuse s s!"rebase conflict: {String.intercalate " " files.toList}"
    else refuse s "the rebase failed and was aborted"
  | st, ob => internal s s!"{st.name}: unexpected {reprStr ob}"

/-- The gate phase. An observation carries the index the core dispatched and
no name: a gate cannot answer under another gate's name, and an absence is
permitted only where the plan says so. -/
private def stepGate (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .gating, .gateOk i =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        nextGate { s with gates := s.gates.push ⟨g.name, true⟩, gateIdx := s.gateIdx + 1 }
  | .gating, .gateFail i =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        gateFailed { s with gates := s.gates.push ⟨g.name, false⟩, gateIdx := s.gateIdx + 1 }
          s!"gate {g.name} failed"
  | .gating, .gateAbsent i =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        if !g.mayAbsent then gateFailed s s!"gate {g.name} is not built"
        else nextGate { s with skipped := s.skipped.push g.name, gateIdx := s.gateIdx + 1 }
  | st, ob => internal s s!"{st.name}: unexpected {reprStr ob}"

/-- The merge half: the two re-reads that pin the run to the commit the
gates saw, the write-ahead row, the fast-forward, and the push. Both
mutating actions live here, and both are guarded in this function alone. -/
private def stepMerge (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .postGate, .branchRecheck tip clean =>
    if tip != s.gatedTip then refuse s s!"agent/{s.name} moved during the gates"
    else if !clean then refuse s s!"the gates left the worktree of agent/{s.name} dirty"
    else ({ s with stage := .preMerge }, .recheckMain)
  | .preMerge, .mainRecheck onMain tip =>
    if !onMain then refuse s "the main worktree left main during the gates"
    else if tip != s.prevMainTip then refuse s "main moved during the gates"
    else ({ s with stage := .announcing }, .writeLanding)
  | .announcing, .ledgerOk =>
    -- The guard is re-asserted here rather than inherited from `afterGates`:
    -- three stages now stand between that guard and the mutation, so the
    -- one place the fast-forward is proposed states its own condition.
    if s.proven && s.gateIdx == s.plan.size then
      ({ s with stage := .ffing }, .fastForward s.gatedTip)
    else gateFailed s "the gates did not complete in this run"
  | .announcing, .ledgerFail => internal s "the ledger was not written"
  | .ffing, .ffOk => ({ s with stage := .verifying }, .readMain)
  | .ffing, .ffRejected => refuse s "the fast-forward was rejected"
  | .verifying, .mainTip mt =>
    if mt == s.gatedTip && isSha s.gatedTip then
      ({ s with stage := .ledgering, mainAt := mt }, .writeLanded)
    else internal s "main did not read back at the gated tip"
  | .ledgering, .ledgerOk =>
    if s.wantPush then
      if s.proven then ({ s with stage := .pushing }, .push)
      else gateFailed s "no gate observation in this run, or one was not ok"
    else succeed s .landed
  | .ledgering, .ledgerFail => internal s "the ledger was not written"
  | .pushing, .pushOk => ({ s with stage := .verifyPush }, .readRemote)
  | .pushing, .pushRejected =>
    -- `main` moved and was verified; only the remote did not. Reporting
    -- this as a failure hid a landing that had happened.
    ({ s with stage := .done, verdict := some .landedUnpushed },
     .halt .landedUnpushed 1 "the push was rejected; main is landed")
  | .verifyPush, .remoteTip ot =>
    if isSha ot && ot == s.mainAt then succeed s .landed
    else internal s "the remote's main did not read back at the landed tip"
  | st, ob => internal s s!"{st.name}: unexpected {reprStr ob}"

/-- Which phase owns a stage. A function of the stage alone, so a proof
about every transition splits this free variable once instead of splitting
`s.stage` inside a goal that also mentions `s` three more times — which is
where the whole-machine proof hit its heartbeat wall. -/
private def phaseOf : Stage → (State → Obs → State × Act)
  | .preMain | .preBranch | .rebasing => stepPre
  | .gating => stepGate
  | _ => stepMerge

/-- One observation, one action. Every pair the procedure does not expect is
an internal failure: a state machine driven off its own transitions is
exactly the condition under which narration got believed. -/
def step (s : State) (o : Obs) : State × Act :=
  match o with
  | .garbled what => internal s s!"unparseable output: {what}"
  | o => phaseOf s.stage s o

-- The run-level pinning statement at the end of this file quantifies over
-- this function; the citation gate cannot resolve a name from this module,
-- so it is named there in a comment rather than backticked here.
/-- Drive the core through a scripted observation sequence, collecting the
actions it proposed. The selftest's harness. -/
def run (s : State) : List Obs → State × Array Act
  | [] => (s, #[])
  | o :: os =>
    let (s', a) := step s o
    let (s'', as) := run s' os
    (s'', #[a] ++ as)

-- ## The theorems
--
-- Two properties, and the ways each could have held vacuously. Each is
-- proved per phase first: `step` dispatches on the stage, so a phase lemma
-- unfolds one match rather than the whole machine.

/-- Neither precondition phase can propose a ref change: the two mutating
actions are spelled in `stepMerge` alone. -/
private theorem stepPre_no_mutate (s : State) (o : Obs) :
    ((stepPre s o).2).mutates = false := by
  unfold stepPre
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals simp_all [Act.mutates, refuse, internal, gateFailed, succeed]

private theorem stepGate_no_mutate (s : State) (o : Obs) :
    ((stepGate s o).2).mutates = false := by
  unfold stepGate
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals simp_all [Act.mutates, internal, gateFailed, succeed]

private theorem stepMerge_mutates_gated (s : State) (o : Obs) :
    ((stepMerge s o).2).mutates = true → (stepMerge s o).1.proven = true := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals
    simp_all [Act.mutates, refuse, internal, gateFailed, succeed, State.proven,
      State.gatesOk]

private theorem stepMerge_ff_covers (s : State) (o : Obs) (t : Sha) :
    (stepMerge s o).2 = .fastForward t →
      (stepMerge s o).1.gateIdx = (stepMerge s o).1.plan.size := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals simp_all [refuse, internal, gateFailed, succeed]

private theorem stepPre_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepPre s o).1.pinned = true := by
  intro _
  unfold stepPre
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals simp_all +decide [refuse, internal, gateFailed, succeed, State.pinned, State.atOrPastFF, State.landedVerdict, State.landedIsGated]

private theorem stepGate_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepGate s o).1.pinned = true := by
  intro h
  unfold stepGate
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals simp_all +decide [internal, gateFailed, succeed, State.pinned, State.atOrPastFF, State.landedVerdict, State.landedIsGated]

private theorem stepMerge_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepMerge s o).1.pinned = true := by
  intro h
  unfold stepMerge
  repeat' split
  all_goals
    simp_all +decide [refuse, internal, gateFailed, succeed, State.pinned, State.atOrPastFF,
      State.landedVerdict, State.landedIsGated]

attribute [irreducible] stepPre stepGate stepMerge

/-- Each phase, lifted to the dispatch: the two mutating actions are
spelled in `stepMerge`, so the other phases discharge by contradiction. -/
private theorem phaseOf_mutates_gated (st : Stage) (s : State) (o : Obs) :
    ((phaseOf st s o).2).mutates = true → (phaseOf st s o).1.proven = true := by
  intro h
  unfold phaseOf at h ⊢
  split at h
  all_goals first
    | exact stepMerge_mutates_gated _ _ h
    | (exfalso; have hn := stepPre_no_mutate s o; simp_all; done)
    | (exfalso; have hn := stepGate_no_mutate s o; simp_all; done)

private theorem phaseOf_ff_covers (st : Stage) (s : State) (o : Obs) (t : Sha) :
    (phaseOf st s o).2 = .fastForward t →
      (phaseOf st s o).1.gateIdx = (phaseOf st s o).1.plan.size := by
  intro h
  unfold phaseOf at h ⊢
  split at h
  all_goals first
    | exact stepMerge_ff_covers _ _ _ h
    | (exfalso; have hn := stepPre_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn)
    | (exfalso; have hn := stepGate_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn)

private theorem phaseOf_pinned (st : Stage) (s : State) (o : Obs) :
    s.pinned = true → (phaseOf st s o).1.pinned = true := by
  intro h
  unfold phaseOf
  split
  all_goals first
    | exact stepPre_pinned _ _ h
    | exact stepGate_pinned _ _ h
    | exact stepMerge_pinned _ _ h

/-- **No ref another party reads is touched on a run whose gates were not
all ok.** Whenever `step` proposes the fast-forward or the push, the
resulting state is `proven` — at least one gate was observed, and every gate
observation in the run was ok. -/
theorem step_mutates_gated (s : State) (o : Obs) :
    ((step s o).2).mutates = true → (step s o).1.proven = true := by
  intro h
  unfold step at h ⊢
  split at h
  · simp_all [Act.mutates, internal]
  · exact phaseOf_mutates_gated _ _ _ h

/-- **Every gate in the plan was observed.** The fast-forward is proposed
only with the gate index at the plan's size. A gate observation is accepted
only at the index the core dispatched (`i != s.gateIdx` is an internal
failure), each accepted observation advances that index by exactly one, and
an observation carries no name — so a gate cannot have answered under
another gate's name, and an absence is permitted only where the plan says
so. -/
theorem step_ff_covers (s : State) (o : Obs) (t : Sha) :
    (step s o).2 = .fastForward t → (step s o).1.gateIdx = (step s o).1.plan.size := by
  intro h
  unfold step at h ⊢
  split at h
  · simp_all [internal]
  · exact phaseOf_ff_covers _ _ _ _ h

/-- The pinning invariant is preserved by every transition. -/
theorem step_pinned (s : State) (o : Obs) :
    s.pinned = true → (step s o).1.pinned = true := by
  intro h
  unfold step
  split
  · simp +decide [internal, State.pinned, State.atOrPastFF, State.landedVerdict,
      State.landedIsGated]
  · exact phaseOf_pinned _ _ _ h

/-- **A landing is a landing of the gated commit.** If the state a step
reaches claims a landing, the `main` it read back after the fast-forward is
exactly the tip the rebase produced and the gates ran on. This is the
statement the two false records reproduced through the first draft would
have failed: both compared two live refs with each other, and neither
carried the gated tip at all. -/
theorem step_landed_exact (s : State) (o : Obs) (h : s.pinned = true)
    (hv : (step s o).1.landedVerdict = true) :
    (step s o).1.landedIsGated = true := by
  have hp := step_pinned s o h
  unfold State.pinned at hp
  simp only [hv, Bool.or_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hp
  exact hp.1

/-- The run-level form: whatever observation sequence a run was fed, a
verdict claiming a landing at the end of it implies the same equality. -/
theorem run_landed_exact (s : State) (os : List Obs) (h : s.pinned = true)
    (hv : (Land.run s os).1.landedVerdict = true) :
    (Land.run s os).1.landedIsGated = true := by
  induction os generalizing s with
  | nil =>
    unfold Land.run at hv ⊢
    unfold State.pinned at h
    simp only [hv, Bool.or_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    exact h.1
  | cons o os ih =>
    unfold Land.run at hv ⊢
    exact ih (step s o).1 (step_pinned s o h) hv

/-- A fresh run satisfies the invariant, so the run-level statement above
applies to every run the driver starts. -/
theorem init_pinned (name : String) (m : Mode) (plan : Array GateSpec) (p : Bool) :
    (State.init name m plan p).pinned = true := by
  simp [State.init, State.pinned, State.atOrPastFF, State.landedVerdict]

end Land
