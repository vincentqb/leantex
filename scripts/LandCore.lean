/-
The landing procedure's pure core: a state machine from parsed observations to actions, so that
only a proven run moves a shared ref, only to the gated commit, and a landing writes what it
owns.
-/

namespace Land

/-- A commit name, as read back from `git rev-parse`. -/
abbrev Sha := String

/-- Forty lowercase hex digits and nothing else, so a garbled read is a refusal rather
than a comparison of two wrong strings. -/
def isSha (s : String) : Bool :=
  s.length == 40 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- What a finished run says on its last line; `checked` is `land check`'s verdict: the
gates passed and nothing was landed. -/
inductive Verdict where
  | landed
  /-- The fast-forward held and was verified; the push was rejected or the remote did not
  read back at the landed tip. -/
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
  /-- `land push` published the last landing, and the remote read back at it. -/
  | pushed
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
  | .pushed => "pushed"

/-- Which command the run is: a landing may move refs, a check never reaches the stage
that can. -/
inductive Mode where
  | land
  | check
  deriving DecidableEq, Repr, Inhabited

/-- Why the branch could not be read. -/
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
  /-- The gate tree is being made: a detached worktree at the branch tip this run read,
  which only this run writes. -/
  | treeing
  /-- The gate tree is being rebased onto `main` as this run read it. -/
  | rebasing
  /-- The rebase's net content is being compared with the branch's. -/
  | netting
  | gating
  /-- After the gates: does the branch still name the tip this run read? -/
  | postGate
  /-- Before the merge: is the main worktree still on `main`, at the tip this run read at
  the start? -/
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
  | .treeing => "gate-tree"
  | .rebasing => "rebase"
  | .netting => "net"
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

/-- What the boundary reports, each constructor a parsed fact and `garbled` what it sends
when it could not parse one; a gate observation carries the dispatched index and the gate
tree as read back after it. -/
inductive Obs where
  /-- The main worktree: whether `HEAD` is on `main`, whether the tree is clean, and its
  tip. -/
  | mainStatus (onMain : Bool) (clean : Bool) (tip : Sha)
  | branchAbsent (miss : BranchMiss)
  /-- The branch: how far ahead and behind `main`, whether its worktree is clean, its tip,
  and an earlier landing's read tip (`landedFrom`), commit (`landedAs`) and whether `main`
  holds it (`landedOnMain`). -/
  | branchStatus (ahead behind : Nat) (clean : Bool) (tip : Sha) (landedFrom landedAs : Sha)
      (landedOnMain : Bool)
  /-- The gate tree this run made, read back: its `HEAD` and whether it is clean. -/
  | treeReady (head : Sha) (clean : Bool)
  /-- The rebase in the gate tree succeeded: the tree's `HEAD` after it, the only commit
  that may land, and whether the tree is clean and detached. -/
  | rebaseOk (tip : Sha) (clean : Bool)
  /-- The rebase in the gate tree failed; `files` are the unmerged paths, empty when it
  stopped for another reason. -/
  | rebaseFailed (files : Array String)
  /-- The two listings the net comparison reads, as `git diff --no-renames -U0 --binary`
  printed them: the branch's own change and the rebase's. -/
  | netDiffs (before after : String)
  /-- The gate at this index passed; the gate tree read back after it. -/
  | gateOk (idx : Nat) (head : Sha) (clean : Bool)
  /-- The gate at this index failed; the gate tree read back after it. -/
  | gateFail (idx : Nat) (head : Sha) (clean : Bool)
  /-- The gate's program is not built: permitted only where the plan says so, and recorded
  apart from gate observations. -/
  | gateAbsent (idx : Nat)
  /-- The branch ref, re-read after the gates. -/
  | branchRecheck (tip : Sha)
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

/-- The constructor, for a message. -/
def Obs.tag : Obs → String
  | .mainStatus .. => "mainStatus"
  | .branchAbsent .. => "branchAbsent"
  | .branchStatus .. => "branchStatus"
  | .treeReady .. => "treeReady"
  | .rebaseOk .. => "rebaseOk"
  | .rebaseFailed .. => "rebaseFailed"
  | .netDiffs .. => "netDiffs"
  | .gateOk .. => "gateOk"
  | .gateFail .. => "gateFail"
  | .gateAbsent .. => "gateAbsent"
  | .branchRecheck .. => "branchRecheck"
  | .mainRecheck .. => "mainRecheck"
  | .ffOk => "ffOk"
  | .ffRejected => "ffRejected"
  | .mainTip .. => "mainTip"
  | .ledgerOk => "ledgerOk"
  | .ledgerFail => "ledgerFail"
  | .pushOk => "pushOk"
  | .pushRejected => "pushRejected"
  | .remoteTip .. => "remoteTip"
  | .garbled .. => "garbled"

/-- One file's net change: its `diff --git` line and every line of its section but hunk
headers and `index` lines, which record where rather than what. -/
abbrev FileNet := String × Array String

/-- Parse a `git diff --no-renames -U0 --binary` listing into one net change per file, in
listing order. -/
def netOf (diff : String) : Array FileNet := Id.run do
  let text := if diff.endsWith "\n" then (diff.dropEnd 1).toString else diff
  let mut out : Array FileNet := #[]
  let mut key := ""
  let mut body : Array String := #[]
  for l in text.splitOn "\n" do
    if l.startsWith "diff --git " then
      if !key.isEmpty then out := out.push (key, body)
      key := l
      body := #[]
    else if !key.isEmpty && !l.startsWith "@@" && !l.startsWith "index " then
      body := body.push l
  if !key.isEmpty then out := out.push (key, body)
  return out

/-- The path a `diff --git a/<p> b/<p>` line names, or the line itself for another
shape. -/
def pathOfKey (k : String) : String :=
  let pre := "diff --git a/"
  let rest := (k.drop pre.length).toString
  let p := (rest.take ((rest.length - 3) / 2)).toString
  if k.startsWith pre && rest == s!"{p} b/{p}" then p else k

/-- The files whose net change differs between two listings, a file in only one included,
by path in first-seen order; empty exactly when every file's change survived. -/
def netDrift (before after : Array FileNet) : Array String := Id.run do
  let find (xs : Array FileNet) (k : String) : Option (Array String) :=
    (xs.find? (·.1 == k)).map (·.2)
  let mut out : Array String := #[]
  for (k, _) in before.append after do
    if find before k != find after k then
      let p := pathOfKey k
      if !out.contains p then out := out.push p
  return out

/-- The sha `git ls-remote` printed for exactly `ref`, or empty when no line or more than
one names it, since a pattern also matches refs ending in it. -/
def lsRemoteTip (out ref : String) : Sha :=
  let hits := (out.splitOn "\n").filterMap fun l =>
    match l.splitOn "\t" with
    | [sha, r] => if r == ref then some sha else none
    | _ => none
  match hits with
  | [t] => t
  | _ => ""

/-- One gate in the plan; `mayAbsent` is the whole permission to skip it. -/
structure GateSpec where
  name : String
  mayAbsent : Bool
  deriving DecidableEq, Repr, Inhabited

/-- One gate's recorded outcome, with the gate tree as read back after it; an absence is
not recorded. -/
structure GateObs where
  name : String
  ok : Bool
  head : Sha
  clean : Bool
  deriving DecidableEq, Repr, Inhabited

/-- What the core asks the boundary to do next; `halt` ends the run. -/
inductive Act where
  | probeMain
  | probeBranch
  /-- Make the gate tree: a detached worktree at exactly this commit, which only this run
  writes, removed when the run ends. -/
  | makeTree (tip : Sha)
  /-- Rebase the gate tree from exactly `tip` onto exactly `onto`: two shas and no ref, so
  its input cannot move under it. -/
  | rebase (tip onto : Sha)
  /-- List the two net changes: the branch's, from its fork point with `newBase` to
  `oldTip`, and the rebase's, from `newBase` to `newTip`. -/
  | netDiff (oldTip newBase newTip : Sha)
  /-- Run the gate at this index of the plan in the gate tree; the name is for the log. -/
  | gate (idx : Nat) (name : String)
  | recheckBranch
  | recheckMain
  /-- The write-ahead row: this run is about to move `main` to this tip. -/
  | writeLanding
  /-- Fast-forward `refs/heads/main`, by that name, to exactly this commit, the tip the
  gates ran on. -/
  | fastForward (tip : Sha)
  | readMain
  | writeLanded
  /-- Push exactly this commit to the remote's `main` as a fast-forward, never forced and
  never the local `main`. -/
  | push (tip : Sha)
  | readRemote
  | halt (v : Verdict) (code : UInt32) (why : String)
  deriving Repr, Inhabited

/-- Where an action writes, declared for every action with no wildcard. -/
inductive Writes where
  /-- The run's gate tree: the detached worktree it made, git's administrative files for
  it, and what a gate writes inside it. -/
  | gateTree
  | ledger
  /-- `refs/heads/main`, by that name, fast-forward only, to this commit, and the worktree
  that has `main` checked out only through git's own sync. -/
  | mainTo (tip : Sha)
  /-- The remote's `refs/heads/main`, by a push of this commit that is never forced. -/
  | remoteTo (tip : Sha)
  /-- A branch another party owns, only by compare-and-swap from `old`, the tip this run
  read. -/
  | branchCas (old new : Sha)
  /-- A ref or a worktree another party owns, written without a compare-and-swap against a
  sha this run read. -/
  | foreign
  /-- The landing queue's file in the common directory, rewritten whole under the queue's own
  lock. -/
  | queue
  /-- The landing lock's owner record, and the gate tree of a holder that died, whose gates'
  results no run reads. -/
  | lockRecord
  deriving DecidableEq, Repr, Inhabited

def Act.writes : Act → List Writes
  | .probeMain => []
  | .probeBranch => []
  | .makeTree _ => [.gateTree]
  | .rebase _ _ => [.gateTree]
  | .netDiff _ _ _ => []
  | .gate _ _ => [.gateTree]
  | .recheckBranch => []
  | .recheckMain => []
  | .writeLanding => [.ledger]
  | .fastForward t => [.mainTo t]
  | .readMain => []
  | .writeLanded => [.ledger]
  | .push t => [.remoteTo t]
  | .readRemote => []
  -- The halt writes the run's last ledger row and removes its gate tree.
  | .halt .. => [.ledger, .gateTree]

/-- Does this write change a ref or a worktree another party reads? -/
def Writes.shared : Writes → Bool
  | .gateTree => false
  | .ledger => false
  | .mainTo _ => true
  | .remoteTo _ => true
  | .branchCas .. => true
  | .foreign => true
  | .queue => false
  | .lockRecord => false

/-- The actions that change a ref or a worktree another party reads, read off the declared
writes. -/
def Act.mutates (a : Act) : Bool := a.writes.any Writes.shared

structure State where
  name : String
  mode : Mode
  stage : Stage
  /-- Every gate observation the run has recorded, in order. -/
  gates : Array GateObs
  /-- Gates whose program was absent. -/
  skipped : Array String
  /-- The gates to run, in order, with their permission to be absent. -/
  plan : Array GateSpec
  /-- How many of the plan's gates have been observed, and the index the next observation
  must carry. -/
  gateIdx : Nat
  wantPush : Bool
  /-- `main`'s tip when the run started; the merge refuses unless `main` is still here. -/
  prevMainTip : Sha
  /-- The branch's tip as this run read it: where the gate tree was made, what the rebase
  started from, and what the branch must still name after the gates. -/
  branchTip : Sha
  /-- The commit the rebase produced, read from the gate tree: what the gates ran on and
  the merge and push name. -/
  gatedTip : Sha
  /-- Whether the rebase kept every file's net change. -/
  netSame : Bool
  /-- `main` as read back after the fast-forward, empty until then. -/
  mainAt : Sha
  verdict : Option Verdict
  deriving Repr, Inhabited

/-- Was every gate observation in the run ok? -/
def State.gatesOk (s : State) : Bool := s.gates.all (·.ok)

/-- The run has earned a ref change: the rebase kept the branch's net content, at least
one gate was observed, and every observation was ok. -/
def State.proven (s : State) : Bool := s.netSame && !s.gates.isEmpty && s.gatesOk

/-- The gates' evidence is about `t`: a sha at which the gate tree read back clean after
every recorded gate. -/
def State.gatedAt (s : State) (t : Sha) : Bool :=
  isSha t && s.gates.all (fun g => g.head == t && g.clean)

/-- Whether a write is the run's, given the state it was proposed from: the tree, the ledger,
the queue and the lock's record always, `main` and the remote only to the gated tip on a
proven run, a foreign branch only by compare-and-swap from the tip this run read. -/
def Writes.owned (s : State) : Writes → Bool
  | .gateTree => true
  | .ledger => true
  | .mainTo t => t == s.gatedTip && s.gatedAt t && s.proven
  | .remoteTo t => t == s.gatedTip && t == s.mainAt && s.gatedAt t && s.proven
  | .branchCas old _ => isSha old && old == s.branchTip && s.proven
  | .foreign => false
  | .queue => true
  | .lockRecord => true

/-- Is the run at or past the fast-forward's verification? -/
def State.atOrPastFF (s : State) : Bool :=
  s.stage == .ledgering || s.stage == .pushing || s.stage == .verifyPush

/-- Is the run before any gate could have been recorded? -/
def State.preTree (s : State) : Bool :=
  s.stage == .preMain || s.stage == .preBranch || s.stage == .treeing
    || s.stage == .rebasing || s.stage == .netting

/-- Is the run past the rebase, and not yet done? -/
def State.rebased (s : State) : Bool :=
  s.stage == .netting || s.stage == .gating || s.stage == .postGate
    || s.stage == .preMerge || s.stage == .announcing || s.stage == .ffing
    || s.stage == .verifying || s.atOrPastFF

/-- Does the run claim a landing? -/
def State.landedVerdict (s : State) : Bool :=
  s.verdict == some .landed || s.verdict == some .landedUnpushed

/-- The `main` this run read back is the commit the gates ran on, and that commit is a
real sha. -/
def State.landedIsGated (s : State) : Bool :=
  s.mainAt == s.gatedTip && isSha s.gatedTip

/-- The run's invariant, kept by each transition: past the fast-forward's verification and
under a landing verdict (only at `done`), `main` is the gated tip; no gate precedes the
rebase verdict; each gate read the tree clean at that tip, a sha after the rebase. -/
def State.pinned (s : State) : Bool :=
  (!(s.atOrPastFF || s.landedVerdict) || s.landedIsGated)
    && (!s.landedVerdict || s.stage == .done)
    && (!s.preTree || s.gates.isEmpty)
    && s.gates.all (fun g => g.head == s.gatedTip && g.clean)
    && (!s.rebased || isSha s.gatedTip)

def State.init (name : String) (mode : Mode) (plan : Array GateSpec)
    (wantPush : Bool) : State :=
  { name, mode, stage := .preMain, gates := #[], skipped := #[], plan, gateIdx := 0,
    wantPush, prevMainTip := "", branchTip := "", gatedTip := "", netSame := false,
    mainAt := "", verdict := none }

private def refuse (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .refused }, .halt .refused 2 why)

private def internal (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .failed }, .halt .failed 3 why)

private def gateFailed (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .failed }, .halt .failed 1 why)

/-- `main` moved and was verified at the gated tip, the remote not known to hold it; exit
4. -/
private def landedNotPushed (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .landedUnpushed }, .halt .landedUnpushed 4 why)

private def succeed (s : State) (v : Verdict) : State × Act :=
  ({ s with stage := .done, verdict := some v }, .halt v 0 "")

/-- The gates are done: the check ends here, or the branch is re-read under the guard. -/
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

/-- Whether an earlier landing bars this branch: only while the branch carries the tip
that landing read and `main` as this run read it holds the commit it landed as. -/
def landedBars (landedFrom : Sha) (landedOnMain : Bool) : Bool :=
  !landedFrom.isEmpty && landedOnMain

/-- The refusal of a landed branch: the next unit starts on a new branch from `main`, and
commits made on the branch since are named as a range and left where they are. -/
def landedWhy (name : String) (landedFrom landedAs tip : Sha) : String :=
  s!"agent/{name} is already landed, as {landedAs}, which main holds: a landed branch \
takes no further landing, so start the next unit on a new branch from main (land new <name>)"
    ++ (if landedFrom == tip then "" else
      s!"; its commits since, {landedFrom}..{tip}, stay on agent/{name}")

/-- The stages before a gate runs: preconditions, the gate tree, the rebase in it and the
net comparison. -/
private def stepPre (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .preMain, .mainStatus onMain clean tip =>
    if !onMain then refuse s "the main worktree is not on main"
    else if !clean then refuse s "the main worktree is dirty"
    else if !isSha tip then internal s "main's tip did not read back as a sha"
    else ({ s with stage := .preBranch, prevMainTip := tip }, .probeBranch)
  | .preBranch, .branchAbsent m => refuse s (m.why s.name)
  | .preBranch, .branchStatus ahead _ clean tip landedFrom landedAs onMain =>
    if ahead == 0 then refuse s s!"agent/{s.name} is not ahead of main"
    else if !clean then refuse s s!"the worktree of agent/{s.name} is dirty"
    else if !isSha tip then internal s "the branch tip did not read back as a sha"
    -- While `main` holds an earlier landing of this branch, the branch is landed and not continued.
    else if landedBars landedFrom onMain then refuse s (landedWhy s.name landedFrom landedAs tip)
    else ({ s with stage := .treeing, branchTip := tip }, .makeTree tip)
  | .treeing, .treeReady head clean =>
    -- A fresh tree not at its tip, or not clean, is the boundary's or the repository's fault.
    if !isSha head then internal s "the gate tree's HEAD did not read back as a sha"
    else if head != s.branchTip then internal s "the gate tree did not read back at the branch tip"
    else if !clean then internal s "the gate tree was dirty when it was made"
    else if !isSha s.prevMainTip then internal s "main's tip is not a sha"
    else ({ s with stage := .rebasing }, .rebase head s.prevMainTip)
  | .rebasing, .rebaseOk tip clean =>
    if !isSha tip then internal s "the rebased tip did not read back as a sha"
    else if !clean then internal s "the gate tree was dirty or on a branch after the rebase"
    else ({ s with stage := .netting, gatedTip := tip }, .netDiff s.branchTip s.prevMainTip tip)
  | .rebasing, .rebaseFailed files =>
    -- The rebase ran in the run's own tree, so there is nothing of the owner's to put back.
    if !files.isEmpty then refuse s s!"rebase conflict: {String.intercalate " " files.toList}"
    else refuse s "the rebase failed"
  | .netting, .netDiffs before after =>
    -- Every file counts, union-merged ones first: git reports no conflict for a union hunk.
    if (netDrift (netOf before) (netOf after)).isEmpty then
      nextGate { s with stage := .gating, netSame := true }
    else
      refuse s s!"the rebase changed the net content of: \
{String.intercalate " " (netDrift (netOf before) (netOf after)).toList}"
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- Record one gate's outcome with the gate tree as read back after it, and advance the
index the next observation must carry. -/
private def record (s : State) (g : GateSpec) (ok : Bool) (head : Sha) (clean : Bool) : State :=
  { s with gates := s.gates.push ⟨g.name, ok, head, clean⟩, gateIdx := s.gateIdx + 1 }

/-- The gate phase: an observation carries the dispatched index, an absence is permitted
only where the plan says so, and a gate that moved or dirtied the tree failed. -/
private def stepGate (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .gating, .gateOk i head clean =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        if head != s.gatedTip then
          gateFailed s s!"gate {g.name} moved the gate tree off the gated tip"
        else if !clean then gateFailed s s!"gate {g.name} left the gate tree dirty"
        else nextGate (record s g true head clean)
  | .gating, .gateFail i head clean =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        if head != s.gatedTip || !clean then
          gateFailed s s!"gate {g.name} failed, and left the gate tree moved or dirty"
        else gateFailed (record s g false head clean) s!"gate {g.name} failed"
  | .gating, .gateAbsent i =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        if !g.mayAbsent then gateFailed s s!"gate {g.name} is not built"
        else nextGate { s with skipped := s.skipped.push g.name, gateIdx := s.gateIdx + 1 }
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- The merge half: the two re-reads, the write-ahead row, the fast-forward and the push,
both mutating actions guarded here alone and both naming `gatedTip`. -/
private def stepMerge (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .postGate, .branchRecheck tip =>
    -- A branch that moved during the landing refuses.
    if tip != s.branchTip then refuse s s!"agent/{s.name} moved during the landing"
    else ({ s with stage := .preMerge }, .recheckMain)
  | .preMerge, .mainRecheck onMain tip =>
    if !onMain then refuse s "the main worktree left main during the gates"
    else if tip != s.prevMainTip then refuse s "main moved during the gates"
    else ({ s with stage := .announcing }, .writeLanding)
  | .announcing, .ledgerOk =>
    -- The guard is restated at the one place the fast-forward is proposed.
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
      if s.proven then ({ s with stage := .pushing }, .push s.gatedTip)
      else gateFailed s "no gate observation in this run, or one was not ok"
    else succeed s .landed
  | .ledgering, .ledgerFail => internal s "the ledger was not written"
  | .pushing, .pushOk => ({ s with stage := .verifyPush }, .readRemote)
  | .pushing, .pushRejected =>
    -- `main` moved and was verified; only the remote did not.
    landedNotPushed s "the push was rejected; main is landed"
  | .verifyPush, .remoteTip ot =>
    if isSha ot && ot == s.mainAt then succeed s .landed
    else landedNotPushed s "the remote's main did not read back at the landed tip; main is landed"
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- Which phase owns a stage, a function of the stage alone. -/
private def phaseOf : Stage → (State → Obs → State × Act)
  | .preMain | .preBranch | .treeing | .rebasing | .netting => stepPre
  | .gating => stepGate
  | _ => stepMerge

/-- One observation, one action; every pair the procedure does not expect is an internal
failure. -/
def step (s : State) (o : Obs) : State × Act :=
  match o with
  | .garbled what => internal s s!"unparseable output: {what}"
  | o => phaseOf s.stage s o

/-- Drive the core through a scripted observation sequence, collecting the actions it
proposed. -/
def run (s : State) : List Obs → State × Array Act
  | [] => (s, #[])
  | o :: os =>
    let (s', a) := step s o
    let (s'', as) := run s' os
    (s'', #[a] ++ as)

/-- Every step of a scripted run: the state it reached and the action it proposed from
there. -/
def trace (s : State) : List Obs → List (State × Act)
  | [] => []
  | o :: os => (step s o) :: trace (step s o).1 os

/-- `land push`'s commit: the last `landed` row's tip, which must also be its gated tip
and what `main` reads now. -/
def pushPlan (landedTip landedGated mainTip : Sha) : Except String Sha :=
  if !isSha landedTip then .error "the ledger has no landed row with a tip"
  else if landedGated != landedTip then .error "the last landed row's tip is not its gated tip"
  else if mainTip != landedTip then
    .error "main is not at the last landed tip: it holds a commit no landing gated"
  else .ok landedTip

/-- The verdict of `land push`: published only when the push succeeded and the remote's
`main`, read back by its exact name, is the commit pushed. -/
def pushVerdict (pushedOk : Bool) (remote tip : Sha) : Verdict :=
  if pushedOk && isSha remote && remote == tip then .pushed else .landedUnpushed

private theorem stepPre_no_mutate (s : State) (o : Obs) :
    ((stepPre s o).2).mutates = false := by
  unfold stepPre
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals
    simp_all [Act.mutates, Act.writes, Writes.shared, refuse, internal, gateFailed, succeed]

private theorem stepGate_no_mutate (s : State) (o : Obs) :
    ((stepGate s o).2).mutates = false := by
  unfold stepGate
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals simp_all [Act.mutates, Act.writes, Writes.shared, internal, gateFailed, succeed]

private theorem stepGate_no_rebase (s : State) (o : Obs) (t b : Sha) :
    (stepGate s o).2 ≠ .rebase t b := by
  unfold stepGate
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals simp_all [internal, gateFailed, succeed]

private theorem stepMerge_no_rebase (s : State) (o : Obs) (t b : Sha) :
    (stepMerge s o).2 ≠ .rebase t b := by
  unfold stepMerge
  repeat' split
  all_goals simp_all [refuse, internal, gateFailed, landedNotPushed, succeed]

private theorem stepPre_rebase_exact (s : State) (o : Obs) (t b : Sha) :
    (stepPre s o).2 = .rebase t b →
      t = (stepPre s o).1.branchTip ∧ b = (stepPre s o).1.prevMainTip
        ∧ isSha t = true ∧ isSha b = true := by
  intro h
  unfold stepPre at h ⊢
  repeat' first
    | split at h
    | (unfold nextGate at h)
    | (unfold afterGates at h)
  all_goals simp_all [refuse, internal, gateFailed, succeed]

private theorem stepMerge_mutates_gated (s : State) (o : Obs) :
    ((stepMerge s o).2).mutates = true → (stepMerge s o).1.proven = true := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals
    simp_all [Act.mutates, Act.writes, Writes.shared, refuse, internal, gateFailed,
      landedNotPushed, succeed, State.proven, State.gatesOk]

private theorem stepMerge_ff_covers (s : State) (o : Obs) (t : Sha) :
    (stepMerge s o).2 = .fastForward t →
      (stepMerge s o).1.gateIdx = (stepMerge s o).1.plan.size := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals simp_all [refuse, internal, gateFailed, landedNotPushed, succeed]

private theorem stepMerge_ff_exact (s : State) (o : Obs) (t : Sha) (hp : s.pinned = true) :
    (stepMerge s o).2 = .fastForward t →
      t = (stepMerge s o).1.gatedTip ∧ (stepMerge s o).1.gatedAt t = true := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals
    simp_all +decide [refuse, internal, gateFailed, landedNotPushed, succeed, State.pinned,
      State.gatedAt, State.rebased, State.atOrPastFF, State.preTree, State.landedVerdict,
      State.landedIsGated]

private theorem stepMerge_push_exact (s : State) (o : Obs) (t : Sha) (hp : s.pinned = true) :
    (stepMerge s o).2 = .push t →
      t = (stepMerge s o).1.gatedTip ∧ t = (stepMerge s o).1.mainAt
        ∧ (stepMerge s o).1.gatedAt t = true := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals
    simp_all +decide [refuse, internal, gateFailed, landedNotPushed, succeed, State.pinned,
      State.gatedAt, State.rebased, State.atOrPastFF, State.preTree, State.landedVerdict,
      State.landedIsGated]

private theorem stepPre_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepPre s o).1.pinned = true := by
  intro _
  unfold stepPre
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals
    simp_all +decide [refuse, internal, gateFailed, succeed, State.pinned, State.atOrPastFF,
      State.preTree, State.rebased, State.landedVerdict, State.landedIsGated]

private theorem stepGate_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepGate s o).1.pinned = true := by
  intro h
  unfold stepGate
  repeat' first
    | split
    | (unfold nextGate)
    | (unfold afterGates)
  all_goals
    simp_all +decide [internal, gateFailed, succeed, record, State.pinned, State.atOrPastFF,
      State.preTree, State.rebased, State.landedVerdict, State.landedIsGated]

private theorem stepMerge_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepMerge s o).1.pinned = true := by
  intro h
  unfold stepMerge
  repeat' split
  all_goals
    simp_all +decide [refuse, internal, gateFailed, landedNotPushed, succeed, State.pinned,
      State.atOrPastFF, State.preTree, State.rebased, State.landedVerdict,
      State.landedIsGated]

private theorem stepPre_unheld (s : State) (a b : Nat) (c : Bool) (t f g : Sha) :
    stepPre s (.branchStatus a b c t f g false)
      = stepPre s (.branchStatus a b c t "" "" false) := by
  cases hs : s.stage <;> simp [stepPre, hs, landedBars, Obs.tag]

private theorem stepGate_unheld (s : State) (a b : Nat) (c : Bool) (t f g : Sha) (m : Bool) :
    stepGate s (.branchStatus a b c t f g m) = stepGate s (.branchStatus a b c t "" "" m) := by
  cases hs : s.stage <;> simp [stepGate, hs, Obs.tag]

private theorem stepMerge_unheld (s : State) (a b : Nat) (c : Bool) (t f g : Sha) (m : Bool) :
    stepMerge s (.branchStatus a b c t f g m) = stepMerge s (.branchStatus a b c t "" "" m) := by
  cases hs : s.stage <;> simp [stepMerge, hs, Obs.tag]

private theorem stepPre_barred (s : State) (a b : Nat) (t f g : Sha) (m : Bool)
    (hs : s.stage = .preBranch) (ha : a ≠ 0) (ht : isSha t = true) :
    ((stepPre s (.branchStatus a b true t f g m)).2 = .makeTree t ↔ landedBars f m = false)
      ∧ (landedBars f m = true →
          (stepPre s (.branchStatus a b true t f g m)).2
            = .halt .refused 2 (landedWhy s.name f g t)) := by
  cases hb : landedBars f m <;> simp [stepPre, hs, ha, ht, hb, refuse]

attribute [irreducible] stepPre stepGate stepMerge

private theorem phaseOf_cases (st : Stage) :
    phaseOf st = stepPre ∨ phaseOf st = stepGate ∨ phaseOf st = stepMerge := by
  cases st <;> simp [phaseOf]

private theorem phaseOf_mutates_gated (st : Stage) (s : State) (o : Obs) :
    ((phaseOf st s o).2).mutates = true → (phaseOf st s o).1.proven = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o; simp_all
  · have hn := stepGate_no_mutate s o; simp_all
  · exact stepMerge_mutates_gated s o h

private theorem phaseOf_ff_covers (st : Stage) (s : State) (o : Obs) (t : Sha) :
    (phaseOf st s o).2 = .fastForward t →
      (phaseOf st s o).1.gateIdx = (phaseOf st s o).1.plan.size := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · have hn := stepGate_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · exact stepMerge_ff_covers s o t h

private theorem phaseOf_ff_exact (st : Stage) (s : State) (o : Obs) (t : Sha)
    (hp : s.pinned = true) :
    (phaseOf st s o).2 = .fastForward t →
      t = (phaseOf st s o).1.gatedTip ∧ (phaseOf st s o).1.gatedAt t = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · have hn := stepGate_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · exact stepMerge_ff_exact s o t hp h

private theorem phaseOf_push_exact (st : Stage) (s : State) (o : Obs) (t : Sha)
    (hp : s.pinned = true) :
    (phaseOf st s o).2 = .push t →
      t = (phaseOf st s o).1.gatedTip ∧ t = (phaseOf st s o).1.mainAt
        ∧ (phaseOf st s o).1.gatedAt t = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · have hn := stepGate_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · exact stepMerge_push_exact s o t hp h

private theorem phaseOf_rebase_exact (st : Stage) (s : State) (o : Obs) (t b : Sha) :
    (phaseOf st s o).2 = .rebase t b →
      t = (phaseOf st s o).1.branchTip ∧ b = (phaseOf st s o).1.prevMainTip
        ∧ isSha t = true ∧ isSha b = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e] at h ⊢
  · exact stepPre_rebase_exact s o t b h
  · exact absurd h (stepGate_no_rebase s o t b)
  · exact absurd h (stepMerge_no_rebase s o t b)

private theorem phaseOf_pinned (st : Stage) (s : State) (o : Obs) :
    s.pinned = true → (phaseOf st s o).1.pinned = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e]
  · exact stepPre_pinned s o h
  · exact stepGate_pinned s o h
  · exact stepMerge_pinned s o h

/-- No ref another party reads is touched on a run whose gates were not all ok. -/
theorem step_mutates_gated (s : State) (o : Obs) :
    ((step s o).2).mutates = true → (step s o).1.proven = true := by
  intro h
  unfold step at h ⊢
  split at h
  · simp_all [Act.mutates, Act.writes, Writes.shared, internal]
  · exact phaseOf_mutates_gated _ _ _ h

/-- The fast-forward is proposed only with the gate index at the plan's size. -/
theorem step_ff_covers (s : State) (o : Obs) (t : Sha) :
    (step s o).2 = .fastForward t → (step s o).1.gateIdx = (step s o).1.plan.size := by
  intro h
  unfold step at h ⊢
  split at h
  · simp_all [internal]
  · exact phaseOf_ff_covers _ _ _ _ h

theorem step_pinned (s : State) (o : Obs) :
    s.pinned = true → (step s o).1.pinned = true := by
  intro h
  unfold step
  split
  · simp_all +decide [internal, State.pinned, State.atOrPastFF, State.preTree, State.rebased,
      State.landedVerdict, State.landedIsGated]
  · exact phaseOf_pinned _ _ _ h

private theorem pinned_landed (s : State) (h : s.pinned = true)
    (hv : s.landedVerdict = true) : s.landedIsGated = true := by
  unfold State.pinned at h
  simp only [hv, Bool.or_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- The rebase starts from the branch tip and targets the `main` this run read: two shas
and no ref. -/
theorem step_rebase_exact (s : State) (o : Obs) (t b : Sha) :
    (step s o).2 = .rebase t b →
      t = (step s o).1.branchTip ∧ b = (step s o).1.prevMainTip
        ∧ isSha t = true ∧ isSha b = true := by
  intro h
  unfold step at h ⊢
  split at h
  · simp [internal] at h
  · exact phaseOf_rebase_exact _ _ _ _ _ h

/-- A landing `main` does not hold is no landing. -/
theorem step_unheld_exact (s : State) (a b : Nat) (c : Bool) (t f g : Sha) :
    step s (.branchStatus a b c t f g false) = step s (.branchStatus a b c t "" "" false) := by
  unfold step
  simp only []
  rcases phaseOf_cases s.stage with e | e | e <;> rw [e]
  · exact stepPre_unheld s a b c t f g
  · exact stepGate_unheld s a b c t f g false
  · exact stepMerge_unheld s a b c t f g false

/-- A landed branch takes no further landing, and only a landed one. -/
theorem step_barred_exact (s : State) (a b : Nat) (t f g : Sha) (m : Bool)
    (hs : s.stage = .preBranch) (ha : a ≠ 0) (ht : isSha t = true) :
    ((step s (.branchStatus a b true t f g m)).2 = .makeTree t ↔ landedBars f m = false)
      ∧ (landedBars f m = true →
          (step s (.branchStatus a b true t f g m)).2
            = .halt .refused 2 (landedWhy s.name f g t)) := by
  have e : phaseOf s.stage = stepPre := by rw [hs]; rfl
  unfold step
  simp only [e]
  exact stepPre_barred s a b t f g m hs ha ht

/-- The fast-forward names the gated tip, about which the gates' evidence is. -/
theorem step_ff_exact (s : State) (o : Obs) (t : Sha) (h : s.pinned = true)
    (ha : (step s o).2 = .fastForward t) :
    t = (step s o).1.gatedTip ∧ (step s o).1.gatedAt t = true := by
  unfold step at ha ⊢
  split at ha
  · simp [internal] at ha
  · exact phaseOf_ff_exact _ _ _ _ h ha

/-- The push names the merged, gated commit, never `main`. -/
theorem step_push_exact (s : State) (o : Obs) (t : Sha) (h : s.pinned = true)
    (ha : (step s o).2 = .push t) :
    t = (step s o).1.gatedTip ∧ t = (step s o).1.mainAt ∧ (step s o).1.gatedAt t = true := by
  unfold step at ha ⊢
  split at ha
  · simp [internal] at ha
  · exact phaseOf_push_exact _ _ _ _ h ha

/-- A landing writes only what it owns. -/
theorem step_writes_owned (s : State) (o : Obs) (h : s.pinned = true) :
    ∀ w ∈ (step s o).2.writes, w.owned (step s o).1 = true := by
  intro w hw
  have hm := step_mutates_gated s o
  have hff := step_ff_exact s o
  have hpu := step_push_exact s o
  generalize ha : (step s o).2 = a at hw hm hff hpu
  cases a
  case fastForward t =>
    simp only [Act.writes, List.mem_singleton] at hw
    subst hw
    obtain ⟨h1, h2⟩ := hff t h rfl
    have hp := hm (by simp [Act.mutates, Act.writes, Writes.shared])
    simp only [Writes.owned]
    rw [← h1]
    simp [h2, hp]
  case push t =>
    simp only [Act.writes, List.mem_singleton] at hw
    subst hw
    obtain ⟨h1, h2, h3⟩ := hpu t h rfl
    have hp := hm (by simp [Act.mutates, Act.writes, Writes.shared])
    simp only [Writes.owned]
    rw [← h1, ← h2]
    simp [h3, hp]
  all_goals
    simp only [Act.writes, List.mem_cons, List.not_mem_nil, or_false] at hw
  all_goals
    first
      | (subst hw; rfl)
      | (rcases hw with rfl | rfl <;> rfl)

/-- A landing is a landing of the gated commit. -/
theorem step_landed_exact (s : State) (o : Obs) (h : s.pinned = true)
    (hv : (step s o).1.landedVerdict = true) :
    (step s o).1.landedIsGated = true :=
  pinned_landed _ (step_pinned s o h) hv

theorem run_landed_exact (s : State) (os : List Obs) (h : s.pinned = true)
    (hv : (Land.run s os).1.landedVerdict = true) :
    (Land.run s os).1.landedIsGated = true := by
  induction os generalizing s with
  | nil =>
    unfold Land.run at hv ⊢
    exact pinned_landed _ h hv
  | cons o os ih =>
    unfold Land.run at hv ⊢
    exact ih (step s o).1 (step_pinned s o h) hv

theorem trace_pinned (s : State) (os : List Obs) (h : s.pinned = true) :
    ∀ p ∈ Land.trace s os, p.1.pinned = true := by
  induction os generalizing s with
  | nil => simp [Land.trace]
  | cons o os ih =>
    intro p hp
    simp only [Land.trace, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact step_pinned s o h
    · exact ih (step s o).1 (step_pinned s o h) p hp

theorem trace_mutates_exact (s : State) (os : List Obs) (h : s.pinned = true) :
    ∀ p ∈ Land.trace s os, ∀ t : Sha,
      (p.2 = .fastForward t → t = p.1.gatedTip ∧ p.1.gatedAt t = true)
      ∧ (p.2 = .push t → t = p.1.gatedTip ∧ t = p.1.mainAt ∧ p.1.gatedAt t = true) := by
  induction os generalizing s with
  | nil => simp [Land.trace]
  | cons o os ih =>
    intro p hp t
    simp only [Land.trace, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨step_ff_exact s o t h, step_push_exact s o t h⟩
    · exact ih (step s o).1 (step_pinned s o h) p hp t

theorem trace_writes_owned (s : State) (os : List Obs) (h : s.pinned = true) :
    ∀ p ∈ Land.trace s os, ∀ w ∈ p.2.writes, w.owned p.1 = true := by
  induction os generalizing s with
  | nil => simp [Land.trace]
  | cons o os ih =>
    intro p hp
    simp only [Land.trace, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact step_writes_owned s o h
    · exact ih (step s o).1 (step_pinned s o h) p hp

theorem init_pinned (name : String) (m : Mode) (plan : Array GateSpec) (p : Bool) :
    (State.init name m plan p).pinned = true := by
  simp [State.init, State.pinned, State.atOrPastFF, State.preTree, State.rebased,
    State.landedVerdict]

theorem pushPlan_exact (lt lg mt t : Sha) (h : pushPlan lt lg mt = .ok t) :
    t = lt ∧ t = lg ∧ t = mt ∧ isSha t = true := by
  unfold pushPlan at h
  repeat' split at h
  all_goals simp_all

theorem pushVerdict_exact (ok : Bool) (r t : Sha) (h : pushVerdict ok r t = .pushed) :
    ok = true ∧ r = t ∧ isSha r = true := by
  unfold pushVerdict at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.2, hc.1.2⟩
  · simp at h

-- ## The landing queue

/-- One waiter for the landing lock: the agent name it would land, the run that entered it last
and that run's process, and when the name arrived. -/
structure Waiter where
  name : String
  run : String
  pid : Nat
  since : String
  deriving DecidableEq, Repr, Inhabited

namespace Queue

/-- Enter `w`: a name waiting under another live run stays that run's; one waiting under a dead
run keeps its place and its arrival and takes `w`'s run and process; a name not waiting arrives
last. -/
def enter (q : List Waiter) (live : Waiter → Bool) (w : Waiter) : List Waiter :=
  if q.any (·.name == w.name) then
    q.map fun x =>
      if x.name == w.name && (x.run == w.run || !live x) then { x with run := w.run, pid := w.pid }
      else x
  else q ++ [w]

/-- The queue without `name`. -/
def leave (q : List Waiter) (name : String) : List Waiter := q.filter (·.name != name)

/-- The waiters that arrived before `name`, all of them when it is not waiting. -/
def ahead (q : List Waiter) (name : String) : List Waiter := q.takeWhile (·.name != name)

/-- Each waiter's name and arrival, in order. -/
def arrivals (q : List Waiter) : List (String × String) := q.map fun x => (x.name, x.since)

end Queue

/-- What a run asking for the landing lock does, decided under the queue's own lock. -/
inductive Turn where
  /-- Take the landing lock and leave the queue: no live waiter arrived before this run's name. -/
  | take
  /-- Wait for the lock and ask again: no live waiter arrived first, and the lock is held. -/
  | wait
  /-- Refuse with exit 2, the place kept: `head`, live, arrived first, and this run's name stands
  at `place`, counted from 1. -/
  | behind (place : Nat) (head : String)
  /-- Refuse with exit 2: this run's name waits under another live run, `run`. -/
  | held (run : String)
  /-- Refuse with exit 2: this run's name waits under no live run but a dead one, or no longer
  waits: it retired, or was made new. -/
  | gone
  deriving DecidableEq, Repr, Inhabited

/-- The turn of `run`, entered as `name`, with the lock free or held, the waiters' liveness as
read: the first live waiter ahead decides, and with none the lock does. -/
def Queue.turn (q : List Waiter) (live : Waiter → Bool) (name run : String) (free : Bool) : Turn :=
  match q.find? (·.name == name) with
  | none => .gone
  | some w =>
    if w.run != run then (if live w then .held w.run else .gone)
    else match (Queue.ahead q name).find? live with
      | some h => .behind ((Queue.ahead q name).length + 1) h.name
      | none => if free then .take else .wait

/-- What writes the queue: an ask for the lock, decided as `t`, and a name dropped when its
branch is retired or made new. -/
inductive QueueOp where
  | ask (t : Turn)
  | drop

/-- Where a queue operation writes: the queue, entered or left, and on a take the lock's record
and the abandoned row of a holder that died. -/
def QueueOp.writes : QueueOp → List Writes
  | .ask .take => [.queue, .lockRecord, .ledger]
  | .ask .wait => [.queue]
  | .ask (.behind ..) => [.queue]
  | .ask (.held _) => [.queue]
  | .ask .gone => [.queue]
  | .drop => [.queue]

/-- A queue operation writes only what its run owns, and no ref or worktree another party
reads. -/
theorem queueOp_writes_owned (s : State) (op : QueueOp) :
    ∀ w ∈ op.writes, w.owned s = true ∧ w.shared = false := by
  intro w hw
  rcases op with (_ | _ | _ | _ | _) | _ <;>
    simp only [QueueOp.writes, List.mem_cons, List.not_mem_nil, or_false] at hw
  all_goals first
    | (subst hw; exact ⟨rfl, rfl⟩)
    | (rcases hw with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩)

/-- **A run takes the landing lock exactly when it is free, its name waits under this run, and
every waiter that arrived before it is dead.** -/
theorem turn_take_exact (q : List Waiter) (live : Waiter → Bool) (name run : String)
    (free : Bool) :
    Queue.turn q live name run free = .take ↔
      free = true ∧ (∃ w, q.find? (·.name == name) = some w ∧ w.run = run)
        ∧ ∀ x ∈ Queue.ahead q name, live x = false := by
  unfold Queue.turn
  split
  · rename_i h
    simp [h]
  · rename_i w hw
    split
    · rename_i hr
      have hne : ¬ w.run = run := by simpa using hr
      have hnt : (if live w = true then Turn.held w.run else Turn.gone) ≠ .take := by
        split <;> simp
      simp only [hnt, false_iff]
      rintro ⟨_, ⟨w', hw', hr'⟩, _⟩
      rw [hw] at hw'
      cases hw'
      exact hne hr'
    · rename_i hr
      have hr' : w.run = run := by simpa using hr
      split
      · rename_i h hh
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ _ hd
        have hm := List.mem_of_find?_eq_some hh
        have hl := List.find?_some hh
        simp_all
      · rename_i hh
        rw [List.find?_eq_none] at hh
        constructor
        · intro ht
          refine ⟨?_, ⟨w, hw, hr'⟩, fun x hx => by simpa using hh x hx⟩
          cases free <;> simp_all
        · rintro ⟨hf, -, -⟩
          simp [hf]

/-- **The first live waiter's turn is never a refusal**: it waits while the lock is held and
takes it once the lock is free. -/
theorem turn_first_exact (q : List Waiter) (live : Waiter → Bool) (name run : String)
    (free : Bool) (w : Waiter) (hw : q.find? (·.name == name) = some w) (hr : w.run = run)
    (hd : ∀ x ∈ Queue.ahead q name, live x = false) :
    Queue.turn q live name run free = if free then .take else .wait := by
  have hn : (Queue.ahead q name).find? live = none :=
    List.find?_eq_none.mpr fun x hx => by simp [hd x hx]
  simp [Queue.turn, hw, hr, hn]

/-- A refusal behind the queue names a live waiter that arrived first, and the refused run's
place. -/
theorem turn_behind_mem (q : List Waiter) (live : Waiter → Bool) (name run : String)
    (free : Bool) (p : Nat) (h : String) (ht : Queue.turn q live name run free = .behind p h) :
    ∃ x ∈ Queue.ahead q name, live x = true ∧ x.name = h
      ∧ p = (Queue.ahead q name).length + 1 := by
  unfold Queue.turn at ht
  split at ht
  · simp at ht
  · split at ht
    · split at ht <;> simp at ht
    · split at ht
      · rename_i x hx
        simp only [Turn.behind.injEq] at ht
        exact ⟨x, List.mem_of_find?_eq_some hx, List.find?_some hx, ht.2, ht.1.symm⟩
      · split at ht <;> simp at ht

/-- The lock's state decides only between taking and waiting. -/
theorem turn_free_exact (q : List Waiter) (live : Waiter → Bool) (name run : String) :
    Queue.turn q live name run false =
      match Queue.turn q live name run true with
      | .take => .wait
      | t => t := by
  unfold Queue.turn
  split
  · rfl
  · split
    · split <;> rfl
    · split <;> rfl

/-- **Entering keeps every waiter's place and arrival, and puts a name not waiting last.** -/
theorem enter_arrivals_exact (q : List Waiter) (live : Waiter → Bool) (w : Waiter) :
    Queue.arrivals (Queue.enter q live w) =
      if q.any (·.name == w.name) then Queue.arrivals q
      else Queue.arrivals q ++ [(w.name, w.since)] := by
  unfold Queue.enter Queue.arrivals
  split
  · simp only [List.map_map]
    congr 1
    funext x
    simp only [Function.comp]
    split <;> rfl
  · simp

/-- Leaving keeps the others in their order. -/
theorem leave_arrivals_exact (q : List Waiter) (n : String) :
    Queue.arrivals (Queue.leave q n) = (Queue.arrivals q).filter (·.1 != n) := by
  unfold Queue.leave Queue.arrivals
  rw [List.filter_map]
  rfl

/-- A path's components: `none` unless the path is absolute and never climbs; empty and
`.` components dropped. -/
def pathParts (p : String) : Option (List String) :=
  if !p.startsWith "/" then none
  else
    let cs := (p.splitOn "/").filter fun c => !c.isEmpty && c != "."
    if cs.contains ".." then none else some cs

/-- `p` is `root` or lies inside it, compared component by component; the filesystem root
holds nothing. -/
def within (root p : String) : Bool :=
  match pathParts root, pathParts p with
  | some (r :: rs), some q => (r :: rs).isPrefixOf q
  | _, _ => false

/-- Two spellings of one absolute path. -/
def samePath (a b : String) : Bool :=
  match pathParts a, pathParts b with
  | some x, some y => x == y
  | _, _ => false

/-- `p` as read from `cwd`: unchanged when absolute. -/
def fromDir (cwd p : String) : String :=
  if p.startsWith "/" then p else s!"{cwd}/{p}"

/-- What the guard knows: the directory the run created for itself, and the bare
repositories the run created under it, the only ones a push may write. -/
structure HGuard where
  root : String
  made : List String
  deriving Repr, Inhabited

/-- One command the harness is about to run, classified; a shape the guard does not model
is `opaque`, which it refuses. -/
inductive HCall where
  /-- `git --version`: names no repository. -/
  | version
  /-- `init`, `clone`, `worktree add` or `worktree move`, run from `cwd` in the repository
  `gitDir` (empty when none), creating what its operands name, each read as a path from
  `cwd`. -/
  | create (cwd gitDir : String) (paths : List String)
  /-- A push from the repository `gitDir` to `target`, read as a path. -/
  | push (cwd gitDir target : String)
  /-- Any other command: it reads or writes the repository `gitDir` that `git rev-parse
  --absolute-git-dir` names from `cwd` in its own environment. -/
  | inRepo (cwd gitDir : String)
  /-- The tool under test, run from `cwd` in the repository `gitDir`, which may push to
  any of its `remotes`. -/
  | drive (cwd gitDir : String) (remotes : List String)
  /-- A shape the guard does not model. -/
  | opaque (why : String)
  deriving Repr, Inhabited

/-- Where a guarded command may write. -/
inductive HWrite where
  /-- The repository a command runs in. -/
  | repo (gitDir : String)
  /-- A path a command creates. -/
  | created (path : String)
  /-- A repository a push reaches over a transport. -/
  | remote (path : String)
  deriving Repr, Inhabited

/-- Every write a command may make, declared per shape with no wildcard. -/
def HCall.writes : HCall → List HWrite
  | .version => []
  | .create _ g ps => (if g.isEmpty then [] else [.repo g]) ++ ps.map .created
  | .push _ g t => [.repo g, .remote t]
  | .inRepo _ g => [.repo g]
  | .drive _ g rs => .repo g :: rs.map .remote
  | .opaque _ => []

/-- The directory a command runs from, where it names one. -/
def HCall.cwd : HCall → Option String
  | .create c _ _ | .push c _ _ | .inRepo c _ | .drive c _ _ => some c
  | .version | .opaque _ => none

/-- Whether this write is the run's: a repository or a created path only inside the root,
a remote only as a bare repository the run made there. -/
def HWrite.owned (g : HGuard) : HWrite → Bool
  | .repo d => within g.root d
  | .created p => within g.root p
  | .remote p => within g.root p && g.made.any (samePath p)

/-- The guard's decision: a modelled command, run from inside the root, every write of
which the run owns. -/
def HCall.allowed (g : HGuard) (c : HCall) : Bool :=
  match c with
  | .opaque _ => false
  | _ => c.cwd.all (within g.root) && c.writes.all (·.owned g)

/-- Why the guard refuses `c`, for the message; empty when it allows it. -/
def HCall.refusal (g : HGuard) (c : HCall) : String :=
  match c with
  | .opaque why => why
  | _ =>
    if !c.cwd.all (within g.root) then s!"it runs from outside the scratch root {g.root}"
    else match c.writes.find? (!·.owned g) with
      | some (.repo d) =>
        s!"its repository {if d.isEmpty then "(none)" else d} is outside the scratch root {g.root}"
      | some (.created p) => s!"it creates {p}, outside the scratch root {g.root}"
      | some (.remote p) => s!"it would reach {p}, which is not a bare repository this run made"
      | none => ""

/-- The words of an argv that are not options. -/
def operands (args : List String) : List String := args.filter fun a => !a.startsWith "-"

/-- Push options after which the target is not the first operand, or that name a program
to run at the target. -/
def pushTargetOpts : List String := ["--repo", "-o", "--push-option", "--receive-pack", "--exec"]

/-- Subcommands that contact a remote other than by a push. -/
def remoteContacts : List String :=
  ["fetch", "pull", "ls-remote", "send-pack", "fetch-pack", "archive", "submodule", "bundle"]

/-- Classify an argv the harness is about to run from `cwd`, given what `git rev-parse
--absolute-git-dir` named there. -/
def classify (cwd gitDir : String) (args : Array String) : HCall :=
  match args.toList with
  | [] => .opaque "an argv with no subcommand"
  | c :: rest =>
    if c == "--version" && rest.isEmpty then .version
    else if c.startsWith "-" then .opaque s!"the global option {c}"
    else if c == "init" || c == "clone" then
      let ps := (operands rest).map (fromDir cwd)
      .create cwd gitDir (if ps.isEmpty then [cwd] else ps)
    else if c == "worktree" && (rest.head? == some "add" || rest.head? == some "move") then
      .create cwd gitDir ((operands (rest.drop 1)).map (fromDir cwd))
    else if c == "push" then
      if rest.any (fun a => pushTargetOpts.any (a.startsWith ·)) then
        .opaque "a push whose target is not its first operand"
      else match operands rest with
        | t :: _ => .push cwd gitDir (fromDir cwd t)
        | [] => .opaque "a push that names no target"
    else if remoteContacts.contains c then .opaque s!"{c} contacts a remote"
    else if c == "remote" && (rest.head? != some "add" || rest.contains "-f"
        || rest.contains "--fetch") then
      .opaque "a remote subcommand other than a plain add"
    else .inRepo cwd gitDir

/-- The bare repository a successful `init --bare` created, which the run records as its
own push target. -/
def bareCreated (cwd : String) (args : Array String) : Option String :=
  match args.toList with
  | "init" :: rest =>
    if !rest.contains "--bare" then none
    else some ((operands rest).getLast?.map (fromDir cwd) |>.getD cwd)
  | _ => none

/-- Why a directory cannot be the harness's scratch root, or nothing: it must be absolute,
below `/`, and enclosed by no repository (`enclosing`, as `git rev-parse
--absolute-git-dir` names it from the root). -/
def rootFault (root enclosing : String) : Option String :=
  match pathParts root with
  | none | some [] => some s!"the scratch root {root} is not an absolute directory below /"
  | some _ =>
    if enclosing.isEmpty then none
    else some s!"the scratch root {root} is inside the checkout {enclosing}"

/-- The harness writes only what its run created: every write an allowed command may make
lies inside the scratch root, and a push reaches only a bare repository the run made
there. -/
theorem hcall_writes_owned (g : HGuard) (c : HCall) (h : c.allowed g = true) :
    ∀ w ∈ c.writes, w.owned g = true := by
  intro w hw
  unfold HCall.allowed at h
  split at h
  · simp at h
  · simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 w hw

theorem hpush_owned (g : HGuard) (cwd d t : String)
    (h : (HCall.push cwd d t).allowed g = true) :
    within g.root d = true ∧ within g.root t = true ∧ g.made.any (samePath t) = true := by
  have hd := hcall_writes_owned g _ h (.repo d) (by simp [HCall.writes])
  have ht := hcall_writes_owned g _ h (.remote t) (by simp [HCall.writes])
  simp only [HWrite.owned, Bool.and_eq_true] at hd ht
  exact ⟨hd, ht.1, ht.2⟩

-- ## The command line

def options : List String := ["--push", "--selftest", "--scratch-selftest", "--help", "-h"]

/-- The subcommand words, which are not agent names. -/
def reserved : List String := ["new", "check", "retire", "status", "push"]

/-- A command that makes a run directory. -/
inductive Run where
  | status
  | push
  | new (name : String)
  | retire (name : String)
  | land (name : String) (mode : Mode) (push : Bool)
  deriving DecidableEq, Repr

def Run.name? : Run → Option String
  | .status | .push => none
  | .new n | .retire n | .land n .. => some n

/-- What an argument vector asks for; `help` and `misuse` print the usage and
start nothing. -/
inductive Cmd where
  | help
  | misuse (why : String)
  | selftest
  | scratchSelftest
  | run (r : Run)
  deriving DecidableEq, Repr

/-- The run `k n`, when `n` can name an agent. -/
def named (n : String) (k : String → Run) : Cmd :=
  if n.isEmpty then .misuse "an agent name cannot be empty"
  else if reserved.contains n then .misuse s!"{n} is a subcommand, not an agent name"
  else .run (k n)

/-- The command an argv's words and its options, all known, spell. -/
def parseForm : List String → List String → Cmd
  | [], [] => .misuse "no command given"
  | [], ["--selftest"] => .selftest
  | [], ["--scratch-selftest"] => .scratchSelftest
  | ["status"], [] => .run .status
  | ["push"], [] => .run .push
  | ["new", n], [] => named n .new
  | ["retire", n], [] => named n .retire
  | ["check", n], [] => named n (.land · .check false)
  | [n], [] => named n (.land · .land false)
  | [n], ["--push"] => named n (.land · .land true)
  | _, _ => .misuse "no command takes these arguments"

/-- `--help` or `-h` anywhere asks for the usage, and any other argument
beginning with `-` that is not an option `land` reads is a mistake. -/
def parseArgs (argv : List String) : Cmd :=
  let opts := argv.filter (·.startsWith "-")
  if opts.contains "--help" || opts.contains "-h" then .help
  else match opts.find? (!options.contains ·) with
    | some o => .misuse s!"{o} is not an option land reads"
    | none => parseForm (operands argv) opts

theorem named_run_exact (n : String) (k : String → Run) (r : Run) (h : named n k = .run r) :
    r = k n ∧ n.isEmpty = false ∧ reserved.contains n = false := by
  unfold named at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i he hr
      simp only [Cmd.run.injEq] at h
      exact ⟨h.symm, Bool.eq_false_iff.mpr he, Bool.eq_false_iff.mpr hr⟩

private theorem named_ne_help (n : String) (k : String → Run) : named n k ≠ .help := by
  unfold named
  split
  · simp
  · split <;> simp

private theorem parseForm_ne_help (ws os : List String) : parseForm ws os ≠ .help := by
  unfold parseForm
  split <;> first | exact named_ne_help _ _ | simp

theorem parseForm_name_mem (ws os : List String) (r : Run) (n : String)
    (h : parseForm ws os = .run r) (hn : r.name? = some n) :
    n ∈ ws ∧ n.isEmpty = false ∧ reserved.contains n = false := by
  unfold parseForm at h
  split at h <;> first
    | (simp at h; done)
    | (simp only [Cmd.run.injEq] at h; subst h; simp [Run.name?] at hn)
    | (obtain ⟨rfl, he, hr⟩ := named_run_exact _ _ _ h
       simp only [Run.name?, Option.some.injEq] at hn
       subst hn
       exact ⟨by simp, he, hr⟩)

/-- **A run reads only the options `land` knows, and names its agent by a word
of the argument vector that is no subcommand.** -/
theorem parseArgs_run_exact (argv : List String) (r : Run) (h : parseArgs argv = .run r) :
    (∀ a ∈ argv, a.startsWith "-" = true → a ∈ options) ∧
      ∀ n, r.name? = some n →
        n ∈ argv ∧ n.startsWith "-" = false ∧ n.isEmpty = false ∧ reserved.contains n = false := by
  unfold parseArgs at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i hnone
      refine ⟨fun a ha hd => ?_, fun n hn => ?_⟩
      · have hk := List.find?_eq_none.mp hnone a (List.mem_filter.mpr ⟨ha, hd⟩)
        simpa using hk
      · obtain ⟨hw, he, hr⟩ := parseForm_name_mem _ _ r n h hn
        have hw' := List.mem_filter.mp hw
        exact ⟨hw'.1, by simpa using hw'.2, he, hr⟩

/-- **An argument beginning with `-` that is no option `land` reads makes no
run**: the usage is printed instead. -/
theorem parseArgs_unknown_exact (argv : List String) (a : String) (ha : a ∈ argv)
    (hd : a.startsWith "-" = true) (hu : a ∉ options) :
    parseArgs argv = .help ∨ ∃ why, parseArgs argv = .misuse why := by
  unfold parseArgs
  dsimp only
  split
  · exact .inl rfl
  · split
    · exact .inr ⟨_, rfl⟩
    · rename_i hnone
      have hk := List.find?_eq_none.mp hnone a (List.mem_filter.mpr ⟨ha, hd⟩)
      exact absurd (by simpa using hk) hu

theorem parseArgs_help_exact (argv : List String) :
    parseArgs argv = .help ↔ ("--help" ∈ argv ∨ "-h" ∈ argv) := by
  have hh : "--help".startsWith "-" = true := by decide +kernel
  have hs : "-h".startsWith "-" = true := by decide +kernel
  unfold parseArgs
  dsimp only
  split
  · rename_i hc
    simp only [Bool.or_eq_true, List.contains_iff_mem, List.mem_filter, hh, hs,
      and_true] at hc
    simpa using hc
  · rename_i hc
    simp only [Bool.or_eq_true, List.contains_iff_mem, List.mem_filter, hh, hs,
      and_true, not_or] at hc
    refine ⟨fun h => ?_, fun h => (h.elim hc.1 hc.2).elim⟩
    split at h
    · simp at h
    · exact absurd h (parseForm_ne_help _ _)

end Land
