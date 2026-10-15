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
  /-- A branch riding behind this run's is being read. -/
  | riderPre
  /-- A rider is being rebased in the gate tree onto the train's tip. -/
  | riderRebasing
  /-- A rider's rebase is being compared with its own change. -/
  | riderNetting
  /-- The gate tree is being put back at the train's tip. -/
  | retreeing
  | gating
  /-- After the gates: does the branch still name the tip this run read? -/
  | postGate
  /-- After the gates: do the riders still name the tips this run read? -/
  | ridersRecheck
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
  | .riderPre => "rider-pre"
  | .riderRebasing => "rider-rebase"
  | .riderNetting => "rider-net"
  | .retreeing => "retree"
  | .gating => "gate"
  | .postGate => "post-gate"
  | .ridersRecheck => "riders-recheck"
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
  /-- The rider at this index: its branch read as `branchStatus` reads the run's own. -/
  | riderStatus (idx ahead : Nat) (clean : Bool) (tip : Sha) (landedFrom landedAs : Sha)
      (landedOnMain : Bool)
  | riderAbsent (idx : Nat) (miss : BranchMiss)
  /-- The rider at this index rebased onto the train's tip: the tree's `HEAD` after it, and
  whether the tree is clean and detached. -/
  | riderRebaseOk (idx : Nat) (tip : Sha) (clean : Bool)
  /-- The rider's rebase failed, the unmerged paths named, and was aborted. -/
  | riderRebaseFailed (idx : Nat) (files : Array String)
  /-- The rider's own change and its rebase's, listed as `netDiffs` lists the run's own. -/
  | riderNetDiffs (idx : Nat) (before after : String)
  /-- What git reported for the rider at this index could not be parsed. -/
  | riderUnread (idx : Nat) (what : String)
  /-- Each rider's branch re-read after the gates, by index. -/
  | ridersRead (tips : Array Sha)
  /-- The gate tree put back, read back: its `HEAD` and whether it is clean. -/
  | retreed (head : Sha) (clean : Bool)
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
  | .riderStatus .. => "riderStatus"
  | .riderAbsent .. => "riderAbsent"
  | .riderRebaseOk .. => "riderRebaseOk"
  | .riderRebaseFailed .. => "riderRebaseFailed"
  | .riderNetDiffs .. => "riderNetDiffs"
  | .riderUnread .. => "riderUnread"
  | .ridersRead .. => "ridersRead"
  | .retreed .. => "retreed"
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
  /-- Read the rider at this index, by its agent name. -/
  | probeRider (idx : Nat) (name : String)
  /-- Rebase the gate tree from exactly the rider's `tip` onto exactly `onto`, the train's tip. -/
  | rebaseRider (idx : Nat) (tip onto : Sha)
  /-- List the rider's two net changes, as `netDiff` lists the run's own. -/
  | netRider (idx : Nat) (oldTip newBase newTip : Sha)
  | recheckRiders
  /-- Put the gate tree back at exactly this commit, detached, what a gate left in it discarded. -/
  | retree (tip : Sha)
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
  /-- A ref or a worktree another party owns. -/
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
  | .probeRider _ _ => []
  | .rebaseRider _ _ _ => [.gateTree]
  | .netRider _ _ _ _ => []
  | .recheckRiders => []
  | .retree _ => [.gateTree]
  | .gate _ _ => [.gateTree]
  | .recheckBranch => []
  | .recheckMain => []
  | .writeLanding => [.ledger]
  | .fastForward t => [.mainTo t]
  | .readMain => []
  | .writeLanded => [.ledger]
  | .push t => [.remoteTo t]
  | .readRemote => []
  -- The halt writes the run's last rows, removes its gate tree and settles its riders' places.
  | .halt .. => [.ledger, .gateTree, .queue]

/-- Does this write change a ref or a worktree another party reads? -/
def Writes.shared : Writes → Bool
  | .gateTree => false
  | .ledger => false
  | .mainTo _ => true
  | .remoteTo _ => true
  | .foreign => true
  | .queue => false
  | .lockRecord => false

/-- The actions that change a ref or a worktree another party reads, read off the declared
writes. -/
def Act.mutates (a : Act) : Bool := a.writes.any Writes.shared

/-- Where a branch riding behind the run's own stands. -/
inductive Standing where
  | riding
  /-- It left the train, refused for its own reason: a precondition, a conflict or a drift. -/
  | refused (why : String)
  /-- It left the train and keeps its place in the queue: it moved, or the train was red. -/
  | stays
  | landed
  deriving DecidableEq, Repr, Inhabited

/-- A branch riding behind the run's own: its agent name, the tip this run read, and its rebased
tip in the train, empty until kept. -/
structure Rider where
  name : String
  tip : Sha
  rebased : Sha
  standing : Standing
  deriving DecidableEq, Repr, Inhabited

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
  /-- The train's tip, read from the gate tree: what the gates run on and the merge and push
  name. -/
  gatedTip : Sha
  /-- The run's own rebased tip, which a red train falls back to. -/
  headTip : Sha
  /-- The branches riding behind the run's own, in train order. -/
  riders : Array Rider
  /-- The rider being read, rebased or compared. -/
  riderIdx : Nat
  /-- The rider's rebased tip while its net change is compared, before it is kept. -/
  pendingTip : Sha
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
proven run, and never a ref or a worktree another party owns. -/
def Writes.owned (s : State) : Writes → Bool
  | .gateTree => true
  | .ledger => true
  | .mainTo t => t == s.gatedTip && s.gatedAt t && s.proven
  | .remoteTo t => t == s.gatedTip && t == s.mainAt && s.gatedAt t && s.proven
  | .foreign => false
  | .queue => true
  | .lockRecord => true

/-- Whether a stage is at or past the fast-forward's verification. -/
def Stage.pastFF : Stage → Bool
  | .ledgering | .pushing | .verifyPush => true
  | .preMain | .preBranch | .treeing | .rebasing | .netting | .riderPre | .riderRebasing
  | .riderNetting | .retreeing | .gating | .postGate | .ridersRecheck | .preMerge
  | .announcing | .ffing | .verifying | .done => false

/-- Whether a stage comes before any gate could have been recorded. -/
def Stage.preTree : Stage → Bool
  | .preMain | .preBranch | .treeing | .rebasing | .netting | .riderPre | .riderRebasing
  | .riderNetting | .retreeing => true
  | .gating | .postGate | .ridersRecheck | .preMerge | .announcing | .ffing | .verifying
  | .ledgering | .pushing | .verifyPush | .done => false

/-- Whether a stage comes past the rebase, the run not yet done. -/
def Stage.rebased : Stage → Bool
  | .netting | .riderPre | .riderRebasing | .riderNetting | .retreeing | .gating | .postGate
  | .ridersRecheck | .preMerge | .announcing | .ffing | .verifying | .ledgering | .pushing
  | .verifyPush => true
  | .preMain | .preBranch | .treeing | .rebasing | .done => false

/-- Whether a step from stage `x` to stage `y`, its gates and gated tip unchanged, keeps the
pin: neither is `done`, and `y` asks no more of the run than `x` gave. -/
def Stage.allows (x y : Stage) : Bool :=
  x != .done && y != .done && (!y.pastFF || x.pastFF) && (!y.preTree || x.preTree)
    && (!y.rebased || x.rebased)

/-- Is the run at or past the fast-forward's verification? -/
def State.atOrPastFF (s : State) : Bool := s.stage.pastFF

/-- Is the run before any gate could have been recorded? -/
def State.preTree (s : State) : Bool := s.stage.preTree

/-- Is the run past the rebase, and not yet done? -/
def State.rebased (s : State) : Bool := s.stage.rebased

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
    (wantPush : Bool) (riders : Array String := #[]) : State :=
  { name, mode, stage := .preMain, gates := #[], skipped := #[], plan, gateIdx := 0,
    wantPush, prevMainTip := "", branchTip := "", gatedTip := "", headTip := "",
    riders := riders.map fun n => ⟨n, "", "", .riding⟩, riderIdx := 0, pendingTip := "",
    netSame := false, mainAt := "", verdict := none }

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

/-- Whether some rider still rides. -/
def State.anyRiding (s : State) : Bool := s.riders.any (·.standing == .riding)

/-- Read the first rider still riding from index `i` on, or start the gates. -/
private def nextRider (s : State) (i : Nat) : State × Act :=
  match (s.riders.toList.drop i).findIdx? (·.standing == .riding) with
  | some j =>
    match s.riders[i + j]? with
    | some r => ({ s with stage := .riderPre, riderIdx := i + j }, .probeRider (i + j) r.name)
    | none => nextGate { s with stage := .gating }
  | none => nextGate { s with stage := .gating }

private def setStanding (s : State) (i : Nat) (st : Standing) : State :=
  { s with riders := s.riders.modify i (fun r => { r with standing := st }) }

/-- The rider at `i` leaves the train refused before its rebase, the tree still at the train's
tip. -/
private def dropRider (s : State) (i : Nat) (why : String) : State × Act :=
  nextRider (setStanding s i (.refused why)) (i + 1)

/-- The rider at `i` leaves the train refused after its rebase moved the tree, which goes back
to the train's tip. -/
private def dropRebased (s : State) (i : Nat) (why : String) : State × Act :=
  ({ setStanding s i (.refused why) with stage := .retreeing, pendingTip := "" },
    .retree s.gatedTip)

/-- Every rider still riding stays queued in its place. -/
private def stayAll (rs : Array Rider) (from_ : Nat) : Array Rider :=
  rs.mapIdx fun i r =>
    if from_ ≤ i && r.standing == .riding then { r with standing := .stays } else r

/-- Gate `tip` afresh: the gates' evidence is reset, and the tree put back at it. -/
private def regate (s : State) (riders : Array Rider) (tip : Sha) : State × Act :=
  ({ s with
      riders := riders, gatedTip := tip, gates := #[], skipped := #[], gateIdx := 0,
      riderIdx := s.riders.size, stage := .retreeing }, .retree tip)

/-- A red train falls back to the run's own tip, every rider staying queued. -/
private def fallBack (s : State) (why : String) : State × Act :=
  if isSha s.headTip then regate s (stayAll s.riders 0) s.headTip
  else gateFailed s why

/-- The train's tip before the rider at `m`: the last rider kept before it, or the run's own. -/
def prefixTip (s : State) (m : Nat) : Sha :=
  match ((s.riders.toList.take m).filter (·.standing == .riding)).getLast? with
  | some r => r.rebased
  | none => s.headTip

/-- A rider that moved during the gates and every later one stay queued, and the train before it
is gated again. -/
private def cutAt (s : State) (m : Nat) : State × Act :=
  if isSha (prefixTip s m) then regate s (stayAll s.riders m) (prefixTip s m)
  else internal s "the train's tip before a rider that moved is not a sha"

/-- The first rider still riding whose branch reads at another tip than this run read. -/
def firstMoved (riders : Array Rider) (tips : Array Sha) : Option Nat :=
  (riders.toList.zipIdx.find? fun (r, i) => r.standing == .riding && tips[i]?.getD "" != r.tip).map
    (·.2)

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
      nextRider { s with stage := .gating, netSame := true, headTip := s.gatedTip } 0
    else
      refuse s s!"the rebase changed the net content of: \
{String.intercalate " " (netDrift (netOf before) (netOf after)).toList}"
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- Record one gate's outcome with the gate tree as read back after it, and advance the
index the next observation must carry. -/
private def record (s : State) (g : GateSpec) (ok : Bool) (head : Sha) (clean : Bool) : State :=
  { s with gates := s.gates.push ⟨g.name, ok, head, clean⟩, gateIdx := s.gateIdx + 1 }

/-- A gate that moved or dirtied the tree fails the run, or a train's falls back to the run's
own tip, the tree put back. -/
private def treeFailed (s : State) (why : String) : State × Act :=
  if s.anyRiding then fallBack s why else gateFailed s why

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
          treeFailed s s!"gate {g.name} moved the gate tree off the gated tip"
        else if !clean then treeFailed s s!"gate {g.name} left the gate tree dirty"
        else nextGate (record s g true head clean)
  | .gating, .gateFail i head clean =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        if head != s.gatedTip || !clean then
          treeFailed s s!"gate {g.name} failed, and left the gate tree moved or dirty"
        else if s.anyRiding then fallBack s s!"gate {g.name} failed"
        else gateFailed (record s g false head clean) s!"gate {g.name} failed"
  | .gating, .gateAbsent i =>
    if i != s.gateIdx then internal s "a gate answered out of turn"
    else match s.plan[i]? with
      | none => internal s "a gate answered past the plan"
      | some g =>
        if !g.mayAbsent then gateFailed s s!"gate {g.name} is not built"
        else nextGate { s with skipped := s.skipped.push g.name, gateIdx := s.gateIdx + 1 }
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- The landing's end after its rows: the push, or the verdict. -/
private def afterLanded (s : State) : State × Act :=
  if s.wantPush then
    if s.proven then ({ s with stage := .pushing }, .push s.gatedTip)
    else gateFailed s "no gate observation in this run, or one was not ok"
  else succeed s .landed

/-- The merge half: the two re-reads, the write-ahead row, the fast-forward and the push,
both mutating actions guarded here alone and both naming `gatedTip`. -/
private def stepMerge (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .postGate, .branchRecheck tip =>
    -- A branch that moved during the landing refuses.
    if tip != s.branchTip then refuse s s!"agent/{s.name} moved during the landing"
    else if s.anyRiding then ({ s with stage := .ridersRecheck }, .recheckRiders)
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
      ({ s with
          stage := .ledgering, mainAt := mt,
          riders := s.riders.map (fun r =>
            if r.standing == .riding then { r with standing := .landed } else r) }, .writeLanded)
    else internal s "main did not read back at the gated tip"
  | .ledgering, .ledgerOk => afterLanded s
  | .ledgering, .ledgerFail => internal s "the ledger was not written"
  | .pushing, .pushOk => ({ s with stage := .verifyPush }, .readRemote)
  | .pushing, .pushRejected =>
    -- `main` moved and was verified; only the remote did not.
    landedNotPushed s "the push was rejected; main is landed"
  | .verifyPush, .remoteTip ot =>
    if isSha ot && ot == s.mainAt then succeed s .landed
    else landedNotPushed s "the remote's main did not read back at the landed tip; main is landed"
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- A rider whose branch is missing leaves the train. -/
private def rideAbsent (s : State) (i : Nat) (m : BranchMiss) : State × Act :=
  if i != s.riderIdx then internal s "a rider answered out of turn"
  else match s.riders[i]? with
    | none => internal s "a rider answered past the train"
    | some r => dropRider s i (m.why r.name)

/-- A rider read: it leaves the train unless it is ahead, clean, a sha and not landed, else its
rebase onto the train's tip starts. -/
private def rideStatus (s : State) (i ahead : Nat) (clean : Bool) (tip landedFrom landedAs : Sha)
    (onMain : Bool) : State × Act :=
  if i != s.riderIdx then internal s "a rider answered out of turn"
  else match s.riders[i]? with
    | none => internal s "a rider answered past the train"
    | some r =>
      if ahead == 0 then dropRider s i s!"agent/{r.name} is not ahead of main"
      else if !clean then dropRider s i s!"the worktree of agent/{r.name} is dirty"
      else if !isSha tip then dropRider s i s!"the tip of agent/{r.name} did not read back as a sha"
      else if landedBars landedFrom onMain then
        dropRider s i (landedWhy r.name landedFrom landedAs tip)
      else if !isSha s.gatedTip then internal s "the train's tip is not a sha"
      else
        ({ s with
            stage := .riderRebasing, riders := s.riders.modify i fun r => { r with tip := tip } },
          .rebaseRider i tip s.gatedTip)

/-- A rider whose git output could not be parsed leaves the train, the tree put back when its
rebase had moved it. -/
private def rideUnread (s : State) (i : Nat) (what : String) : State × Act :=
  if i != s.riderIdx then internal s "a rider answered out of turn"
  else match s.riders[i]? with
    | none => internal s "a rider answered past the train"
    | some r =>
      if s.stage == .riderNetting then dropRebased s i s!"agent/{r.name} could not be read: {what}"
      else dropRider s i s!"agent/{r.name} could not be read: {what}"

/-- A rider rebased: its net change is compared next, unless the tree did not read back clean
and detached at a sha, when the rider leaves the train and the tree is put back. -/
private def rideRebased (s : State) (i : Nat) (tip : Sha) (clean : Bool) : State × Act :=
  if i != s.riderIdx then internal s "a rider answered out of turn"
  else match s.riders[i]? with
    | none => internal s "a rider answered past the train"
    | some r =>
      if !isSha tip then dropRebased s i s!"agent/{r.name}'s rebased tip did not read back as a sha"
      else if !clean then
        dropRebased s i s!"the gate tree was dirty or on a branch after agent/{r.name}'s rebase"
      else ({ s with stage := .riderNetting, pendingTip := tip }, .netRider i r.tip s.gatedTip tip)

/-- A rider whose rebase failed leaves the train. -/
private def rideConflict (s : State) (i : Nat) (files : Array String) : State × Act :=
  if i != s.riderIdx then internal s "a rider answered out of turn"
  else if !files.isEmpty then
    dropRebased s i s!"rebase conflict: {String.intercalate " " files.toList}"
  else dropRebased s i "the rebase failed"

/-- A rider compared: kept, its rebased tip the train's, when its net change is unchanged. -/
private def rideNet (s : State) (i : Nat) (before after : String) : State × Act :=
  if i != s.riderIdx then internal s "a rider answered out of turn"
  else if !(netDrift (netOf before) (netOf after)).isEmpty then
    dropRebased s i s!"the rebase changed the net content of: \
{String.intercalate " " (netDrift (netOf before) (netOf after)).toList}"
  else if !isSha s.pendingTip then internal s "a rider's rebased tip is not a sha"
  else nextRider { s with
      riders := s.riders.modify i (fun r => { r with rebased := s.pendingTip }),
      gatedTip := s.pendingTip, pendingTip := "" } (i + 1)

/-- The tree put back at the train's tip after a rider left. -/
private def rideRetreed (s : State) (head : Sha) (clean : Bool) : State × Act :=
  if !isSha head then internal s "the gate tree's HEAD did not read back as a sha"
  else if head != s.gatedTip then internal s "the gate tree did not read back at the train's tip"
  else if !clean then internal s "the gate tree was dirty when put back"
  else nextRider s (s.riderIdx + 1)

/-- The riders re-read after the gates: a moved rider cuts the train before it. -/
private def rideRecheck (s : State) (tips : Array Sha) : State × Act :=
  match firstMoved s.riders tips with
  | none => ({ s with stage := .preMerge }, .recheckMain)
  | some m => cutAt s m

/-- The riders' stages: each rider read, rebased onto the train's tip and compared, the tree put
back after a rider leaves, and the riders re-read after the gates. -/
private def stepRide (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .riderPre, .riderAbsent i m => rideAbsent s i m
  | .riderPre, .riderStatus i ahead clean tip landedFrom landedAs onMain =>
    rideStatus s i ahead clean tip landedFrom landedAs onMain
  | .riderRebasing, .riderRebaseOk i tip clean => rideRebased s i tip clean
  | .riderRebasing, .riderRebaseFailed i files => rideConflict s i files
  | .riderNetting, .riderNetDiffs i before after => rideNet s i before after
  | .riderPre, .riderUnread i what | .riderNetting, .riderUnread i what => rideUnread s i what
  | .retreeing, .retreed head clean => rideRetreed s head clean
  | .ridersRecheck, .ridersRead tips => rideRecheck s tips
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- Which phase owns a stage, a function of the stage alone. -/
private def phaseOf : Stage → (State → Obs → State × Act)
  | .preMain | .preBranch | .treeing | .rebasing | .netting => stepPre
  | .riderPre | .riderRebasing | .riderNetting | .retreeing | .ridersRecheck => stepRide
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

private theorem pinned_parts (s : State) (h : s.pinned = true) :
    (!(s.atOrPastFF || s.landedVerdict) || s.landedIsGated) = true
      ∧ (!s.landedVerdict || s.stage == .done) = true
      ∧ (!s.preTree || s.gates.isEmpty) = true
      ∧ s.gates.all (fun g => g.head == s.gatedTip && g.clean) = true
      ∧ (!s.rebased || isSha s.gatedTip) = true := by
  simp only [State.pinned, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The pin of a state mid-run: not landed, not past the fast-forward, no gate before the
rebase, every gate at the gated tip, and that tip a sha past the rebase. -/
private theorem pinned_mid (s : State) (hv : s.landedVerdict = false)
    (hf : s.atOrPastFF = true → s.landedIsGated = true)
    (hc : (!s.preTree || s.gates.isEmpty) = true)
    (hd : s.gates.all (fun g => g.head == s.gatedTip && g.clean) = true)
    (he : (!s.rebased || isSha s.gatedTip) = true) : s.pinned = true := by
  cases ha : s.atOrPastFF <;> simp_all [State.pinned]

/-- A run's halt keeps the pin: its gates' evidence is unchanged, and a landing verdict comes
only with `main` read back at the gated tip. -/
private theorem pinned_halt (s : State) (v : Verdict) (h : s.pinned = true)
    (hl : (v == .landed || v == .landedUnpushed) = true → s.landedIsGated = true) :
    ({ s with stage := .done, verdict := some v } : State).pinned = true := by
  obtain ⟨-, -, -, hd, -⟩ := pinned_parts s h
  cases v <;> simp_all [State.pinned, State.atOrPastFF, State.preTree, State.rebased,
    Stage.pastFF, Stage.preTree, Stage.rebased, State.landedVerdict, State.landedIsGated]

/-- A run not at `done` claims no landing. -/
private theorem pinned_open (s : State) (h : s.pinned = true) (hs : s.stage ≠ .done) :
    s.landedVerdict = false := by
  obtain ⟨-, hb, -⟩ := pinned_parts s h
  cases hv : s.landedVerdict <;> simp_all

/-- A run past the fast-forward's verification has `main` read back at the gated tip. -/
private theorem pinned_pastFF (s : State) (h : s.pinned = true) (hs : s.atOrPastFF = true) :
    s.landedIsGated = true := by
  obtain ⟨ha, -⟩ := pinned_parts s h
  simp_all

private theorem refuse_pinned (s : State) (h : s.pinned = true) (why : String) :
    (refuse s why).1.pinned = true := pinned_halt s .refused h (by simp)

private theorem internal_pinned (s : State) (h : s.pinned = true) (why : String) :
    (internal s why).1.pinned = true := pinned_halt s .failed h (by simp)

private theorem gateFailed_pinned (s : State) (h : s.pinned = true) (why : String) :
    (gateFailed s why).1.pinned = true := pinned_halt s .failed h (by simp)

private theorem landedNotPushed_pinned (s : State) (why : String) (h : s.pinned = true)
    (hs : s.atOrPastFF = true) : (landedNotPushed s why).1.pinned = true :=
  pinned_halt s .landedUnpushed h fun _ => pinned_pastFF s h hs

private theorem succeed_pinned (s : State) (v : Verdict) (h : s.pinned = true)
    (hl : (v == .landed || v == .landedUnpushed) = true → s.landedIsGated = true) :
    (succeed s v).1.pinned = true := pinned_halt s v h hl

private theorem refuse_snd (s : State) (why : String) : (refuse s why).2 = .halt .refused 2 why :=
  rfl

private theorem internal_snd (s : State) (why : String) :
    (internal s why).2 = .halt .failed 3 why :=
  rfl

private theorem gateFailed_snd (s : State) (why : String) :
    (gateFailed s why).2 = .halt .failed 1 why := rfl

private theorem landedNotPushed_snd (s : State) (why : String) :
    (landedNotPushed s why).2 = .halt .landedUnpushed 4 why := rfl

private theorem succeed_snd (s : State) (v : Verdict) : (succeed s v).2 = .halt v 0 "" := rfl

/-- Every halt the core proposes writes the ledger, the gate tree and the queue alone. -/
private theorem halt_quiet (v : Verdict) (c : UInt32) (why : String) :
    (Act.halt v c why).mutates = false := by
  simp [Act.mutates, Act.writes, Writes.shared]

private theorem afterGates_mutates (s : State) : (afterGates s).2.mutates = false := by
  unfold afterGates
  split
  · split <;> simp [succeed, Act.mutates, Act.writes, Writes.shared]
  · simp [gateFailed, Act.mutates, Act.writes, Writes.shared]

private theorem afterGates_rebase (s : State) (t b : Sha) : (afterGates s).2 ≠ .rebase t b := by
  unfold afterGates
  split
  · split <;> simp [succeed]
  · simp [gateFailed]

private theorem afterGates_pinned (s : State) (h : s.pinned = true) (hs : s.stage = .gating) :
    (afterGates s).1.pinned = true := by
  obtain ⟨-, -, -, hd, he⟩ := pinned_parts s h
  have hv := pinned_open s h (by simp [hs])
  unfold afterGates
  split
  · split
    · exact succeed_pinned s .checked h (by simp)
    · apply pinned_mid <;> simp_all [State.atOrPastFF, State.preTree, State.rebased,
        Stage.pastFF, Stage.preTree, Stage.rebased, State.landedVerdict]
  · exact gateFailed_pinned s h _

private theorem nextGate_mutates (s : State) : (nextGate s).2.mutates = false := by
  unfold nextGate
  split
  · simp [Act.mutates, Act.writes, Writes.shared]
  · exact afterGates_mutates s

private theorem nextGate_rebase (s : State) (t b : Sha) : (nextGate s).2 ≠ .rebase t b := by
  unfold nextGate
  split
  · simp
  · exact afterGates_rebase s t b

private theorem nextGate_pinned (s : State) (h : s.pinned = true) (hs : s.stage = .gating) :
    (nextGate s).1.pinned = true := by
  unfold nextGate
  split
  · exact h
  · exact afterGates_pinned s h hs

private theorem nextRider_mutates (s : State) (i : Nat) : (nextRider s i).2.mutates = false := by
  unfold nextRider
  split
  · split
    · simp [Act.mutates, Act.writes]
    · exact nextGate_mutates _
  · exact nextGate_mutates _

private theorem nextRider_rebase (s : State) (i : Nat) (t b : Sha) :
    (nextRider s i).2 ≠ .rebase t b := by
  unfold nextRider
  split
  · split
    · simp
    · exact nextGate_rebase _ t b
  · exact nextGate_rebase _ t b

/-- Reading the next rider, or starting the gates, keeps the pin of a run with no gate yet and a
sha for the train's tip. -/
private theorem nextRider_pinned (s : State) (i : Nat) (hv : s.landedVerdict = false)
    (hc : s.gates.isEmpty = true) (he : isSha s.gatedTip = true) :
    (nextRider s i).1.pinned = true := by
  have hg : ({ s with stage := .gating } : State).pinned = true := by
    apply pinned_mid <;> simp_all [State.atOrPastFF, State.preTree, State.rebased, Stage.pastFF,
      Stage.preTree, Stage.rebased, State.landedVerdict]
  unfold nextRider
  split
  · split
    · apply pinned_mid <;> simp_all [State.atOrPastFF, State.preTree, State.rebased,
        Stage.pastFF, Stage.preTree, Stage.rebased, State.landedVerdict]
    · exact nextGate_pinned _ hg rfl
  · exact nextGate_pinned _ hg rfl

private theorem dropRider_mutates (s : State) (i : Nat) (why : String) :
    (dropRider s i why).2.mutates = false := nextRider_mutates _ _

private theorem dropRider_rebase (s : State) (i : Nat) (why : String) (t b : Sha) :
    (dropRider s i why).2 ≠ .rebase t b := nextRider_rebase _ _ t b

private theorem dropRider_pinned (s : State) (i : Nat) (why : String)
    (hv : s.landedVerdict = false) (hc : s.gates.isEmpty = true) (he : isSha s.gatedTip = true) :
    (dropRider s i why).1.pinned = true :=
  nextRider_pinned _ _ (by simpa [setStanding, State.landedVerdict] using hv)
    (by simpa [setStanding] using hc) (by simpa [setStanding] using he)

private theorem dropRebased_mutates (s : State) (i : Nat) (why : String) :
    (dropRebased s i why).2.mutates = false := by
  simp [dropRebased, Act.mutates, Act.writes, Writes.shared]

private theorem dropRebased_rebase (s : State) (i : Nat) (why : String) (t b : Sha) :
    (dropRebased s i why).2 ≠ .rebase t b := by
  simp [dropRebased]

private theorem dropRebased_pinned (s : State) (i : Nat) (why : String)
    (hv : s.landedVerdict = false) (hc : s.gates.isEmpty = true) (he : isSha s.gatedTip = true) :
    (dropRebased s i why).1.pinned = true := by
  apply pinned_mid <;> simp_all [dropRebased, setStanding, State.atOrPastFF, State.preTree,
    State.rebased, Stage.pastFF, Stage.preTree, Stage.rebased, State.landedVerdict]

private theorem regate_pinned (s : State) (rs : Array Rider) (tip : Sha)
    (hv : s.landedVerdict = false) (ht : isSha tip = true) : (regate s rs tip).1.pinned = true := by
  apply pinned_mid <;> simp_all [regate, State.atOrPastFF, State.preTree, State.rebased,
    Stage.pastFF, Stage.preTree, Stage.rebased, State.landedVerdict]

private theorem fallBack_mutates (s : State) (why : String) :
    (fallBack s why).2.mutates = false := by
  unfold fallBack
  split <;> simp [regate, gateFailed, Act.mutates, Act.writes, Writes.shared]

private theorem fallBack_rebase (s : State) (why : String) (t b : Sha) :
    (fallBack s why).2 ≠ .rebase t b := by
  unfold fallBack
  split <;> simp [regate, gateFailed]

private theorem fallBack_pinned (s : State) (why : String) (h : s.pinned = true)
    (hv : s.landedVerdict = false) : (fallBack s why).1.pinned = true := by
  unfold fallBack
  split
  · exact regate_pinned s _ _ hv ‹_›
  · exact gateFailed_pinned s h _

private theorem treeFailed_mutates (s : State) (why : String) :
    (treeFailed s why).2.mutates = false := by
  unfold treeFailed
  split
  · exact fallBack_mutates s why
  · simp [gateFailed, Act.mutates, Act.writes, Writes.shared]

private theorem treeFailed_rebase (s : State) (why : String) (t b : Sha) :
    (treeFailed s why).2 ≠ .rebase t b := by
  unfold treeFailed
  split
  · exact fallBack_rebase s why t b
  · simp [gateFailed]

private theorem treeFailed_pinned (s : State) (why : String) (h : s.pinned = true)
    (hv : s.landedVerdict = false) : (treeFailed s why).1.pinned = true := by
  unfold treeFailed
  split
  · exact fallBack_pinned s why h hv
  · exact gateFailed_pinned s h _

private theorem cutAt_mutates (s : State) (m : Nat) : (cutAt s m).2.mutates = false := by
  unfold cutAt
  split <;> simp [regate, internal, Act.mutates, Act.writes, Writes.shared]

private theorem cutAt_rebase (s : State) (m : Nat) (t b : Sha) : (cutAt s m).2 ≠ .rebase t b := by
  unfold cutAt
  split <;> simp [regate, internal]

private theorem cutAt_pinned (s : State) (m : Nat) (h : s.pinned = true)
    (hv : s.landedVerdict = false) : (cutAt s m).1.pinned = true := by
  unfold cutAt
  split
  · exact regate_pinned s _ _ hv ‹_›
  · exact internal_pinned s h _

private theorem afterLanded_mutates_gated (s : State) :
    (afterLanded s).2.mutates = true → (afterLanded s).1.proven = true := by
  unfold afterLanded
  split
  · split
    · intro _; simp_all [State.proven, State.gatesOk]
    · simp [gateFailed, Act.mutates, Act.writes, Writes.shared]
  · simp [succeed, Act.mutates, Act.writes, Writes.shared]

private theorem afterLanded_pinned (s : State) (h : s.pinned = true) (hs : s.atOrPastFF = true) :
    (afterLanded s).1.pinned = true := by
  have hm := pinned_pastFF s h hs
  have hv := pinned_open s h (by
    intro hd; simp [State.atOrPastFF, hd, Stage.pastFF] at hs)
  obtain ⟨-, -, -, hd, -⟩ := pinned_parts s h
  unfold afterLanded
  split
  · split
    · simp_all [State.pinned, State.atOrPastFF, State.preTree, State.rebased, Stage.pastFF,
        Stage.preTree, Stage.rebased, State.landedVerdict, State.landedIsGated]
    · exact gateFailed_pinned s h _
  · exact succeed_pinned s .landed h fun _ => hm

private theorem afterLanded_push (s : State) (t : Sha) (h : s.pinned = true)
    (hs : s.atOrPastFF = true) (ha : (afterLanded s).2 = .push t) :
    t = (afterLanded s).1.gatedTip ∧ t = (afterLanded s).1.mainAt
      ∧ (afterLanded s).1.gatedAt t = true := by
  have hm := pinned_pastFF s h hs
  obtain ⟨-, -, -, hd, -⟩ := pinned_parts s h
  unfold afterLanded at ha ⊢
  split at ha
  · split at ha
    · simp only [Act.push.injEq] at ha
      subst ha
      simp_all [State.landedIsGated, State.gatedAt]
    · simp [gateFailed] at ha
  · simp [succeed] at ha

private theorem afterLanded_quiet (s : State) (t b : Sha) :
    (afterLanded s).2 ≠ .rebase t b ∧ (afterLanded s).2 ≠ .fastForward t := by
  unfold afterLanded
  repeat' split
  all_goals simp [gateFailed, succeed]

private theorem record_stage (s : State) (g : GateSpec) (ok : Bool) (head : Sha) (clean : Bool) :
    (record s g ok head clean).stage = s.stage := rfl

/-- A step that leaves every field the pin reads as it was keeps it. -/
private theorem pinned_congr (s s' : State) (h : s.pinned = true) (hs : s'.stage = s.stage)
    (hv : s'.verdict = s.verdict) (hg : s'.gates = s.gates) (ht : s'.gatedTip = s.gatedTip)
    (hm : s'.mainAt = s.mainAt) : s'.pinned = true := by
  have e : s'.pinned = s.pinned := by
    simp only [State.pinned, State.atOrPastFF, State.preTree, State.rebased, State.landedVerdict,
      State.landedIsGated, hs, hv, hg, ht, hm]
  rw [e]; exact h

attribute [irreducible] refuse internal gateFailed landedNotPushed succeed afterGates nextGate
  nextRider setStanding dropRider dropRebased stayAll regate fallBack treeFailed prefixTip cutAt
  afterLanded record State.pinned

/-- The stages' simp set for a state a transition builds. -/
local macro "stage_simp" : tactic =>
  `(tactic| simp_all [State.atOrPastFF, State.preTree, State.rebased, Stage.pastFF,
    Stage.preTree, Stage.rebased, State.landedVerdict, State.landedIsGated, record, State.gatedAt])

/-- What the pin gives at a known stage: no gate before the rebase, a sha past it, and no landing
claimed before `done`. -/
private theorem pinned_facts {x : Stage} (s : State) (h : s.pinned = true) (hs : s.stage = x) :
    (x.preTree = true → s.gates.isEmpty = true) ∧ (x.rebased = true → isSha s.gatedTip = true)
      ∧ (x ≠ .done → s.landedVerdict = false) := by
  obtain ⟨-, hb, hc, -, he⟩ := pinned_parts s h
  subst hs
  refine ⟨fun hp => by simpa [State.preTree, hp] using hc,
    fun hr => by simpa [State.rebased, hr] using he,
    fun hd => ?_⟩
  cases hl : s.landedVerdict <;> simp_all

/-- A step that moves the stage alone among the fields the pin reads keeps it, where the stages
allow. -/
private theorem pinned_restage {x y : Stage} (s s' : State) (h : s.pinned = true)
    (hs : s.stage = x) (hs' : s'.stage = y) (hv : s'.verdict = s.verdict) (hg : s'.gates = s.gates)
    (ht : s'.gatedTip = s.gatedTip) (hm : s'.mainAt = s.mainAt) (hxy : Stage.allows x y = true) :
    s'.pinned = true := by
  obtain ⟨ha, -, -, hd, -⟩ := pinned_parts s h
  obtain ⟨hc, he, hl⟩ := pinned_facts s h hs
  simp only [Stage.allows, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hxy
  obtain ⟨⟨⟨⟨hx, -⟩, hf⟩, hp⟩, hr⟩ := hxy
  have hl' := hl hx
  apply pinned_mid
  · simpa [State.landedVerdict, hv] using hl'
  · intro hff
    have : s.atOrPastFF = true := by
      simp only [State.atOrPastFF, hs', hs] at hff ⊢; cases hf <;> simp_all
    simp only [State.landedVerdict] at hl'
    simp_all [State.landedIsGated, State.landedVerdict]
  · cases hp with
    | inl hp => simp [State.preTree, hs', hp]
    | inr hp => simp [hg, hc hp]
  · simpa [hg, ht] using hd
  · cases hr with
    | inl hr => simp [State.rebased, hs', hr]
    | inr hr => simp [ht, he hr]

/-- A step to a stage before any gate that sets a new gated tip, a sha, keeps the pin. -/
private theorem pinned_retip {x y : Stage} (s s' : State) (h : s.pinned = true) (hs : s.stage = x)
    (hs' : s'.stage = y) (hv : s'.verdict = s.verdict) (hg : s'.gates = s.gates)
    (ht : isSha s'.gatedTip = true) (hxy : (x.preTree && y.preTree && x != .done) = true) :
    s'.pinned = true := by
  obtain ⟨hc, -, hl⟩ := pinned_facts s h hs
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hxy
  have hl' := hl hxy.2
  have he := hc hxy.1.1
  apply pinned_mid
  · simpa [State.landedVerdict, hv] using hl'
  · intro hf
    have hp : y.pastFF = false := by cases y <;> simp_all [Stage.preTree, Stage.pastFF]
    simp [State.atOrPastFF, hs', hp] at hf
  · simp [hg, he]
  · simp [hg, Array.isEmpty_iff.mp he]
  · simp [ht]

/-- Recording a gate at the gated tip, the tree clean, keeps the pin. -/
private theorem pinned_record (s : State) (h : s.pinned = true) (hs : s.stage = .gating)
    (g : GateSpec) (ok : Bool) (head : Sha) (clean : Bool) (hh : head = s.gatedTip)
    (hc : clean = true) : (record s g ok head clean).pinned = true := by
  obtain ⟨-, -, -, hd, -⟩ := pinned_parts s h
  obtain ⟨-, he, hl⟩ := pinned_facts s h hs
  apply pinned_mid
  · simpa [record, State.landedVerdict] using hl (by simp)
  · simp [record, State.atOrPastFF, hs, Stage.pastFF]
  · simp [record, State.preTree, hs, Stage.preTree]
  · simp_all [record]
  · have e : isSha s.gatedTip = true := he rfl
    simp [record, e]

/-- The step that reads `main` back at the gated tip, a sha, keeps the pin. -/
private theorem pinned_verified (s s' : State) (h : s.pinned = true) (hs : s.stage = .verifying)
    (hs' : s'.stage = .ledgering) (hv : s'.verdict = s.verdict) (hg : s'.gates = s.gates)
    (ht : s'.gatedTip = s.gatedTip) (hm : s'.mainAt = s.gatedTip) (hsha : isSha s.gatedTip = true) :
    s'.pinned = true := by
  obtain ⟨-, -, -, hd, -⟩ := pinned_parts s h
  obtain ⟨-, -, hl⟩ := pinned_facts s h hs
  apply pinned_mid
  · simpa [State.landedVerdict, hv] using hl (by simp)
  · intro _; simp [State.landedIsGated, hm, ht, hsha]
  · simp [State.preTree, hs', Stage.preTree]
  · simpa [hg, ht] using hd
  · simp [ht, hsha]

private theorem stepPre_no_mutate (s : State) (o : Obs) :
    ((stepPre s o).2).mutates = false := by
  unfold stepPre
  repeat' split
  all_goals first
    | exact nextRider_mutates _ _
    | simp [refuse, internal, Act.mutates, Act.writes, Writes.shared]

private theorem stepPre_rebase_exact (s : State) (o : Obs) (t b : Sha) :
    (stepPre s o).2 = .rebase t b →
      t = (stepPre s o).1.branchTip ∧ b = (stepPre s o).1.prevMainTip
        ∧ isSha t = true ∧ isSha b = true := by
  intro h
  unfold stepPre at h ⊢
  repeat' split at h
  all_goals first
    | exact absurd h (nextRider_rebase _ _ t b)
    | simp_all [refuse, internal]

private theorem stepPre_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepPre s o).1.pinned = true := by
  intro h
  unfold stepPre
  repeat' split
  all_goals first
    | (simp only [refuse_pinned s h, internal_pinned s h]; done)
    | (obtain ⟨hc, he, hl⟩ := pinned_facts s h (‹s.stage = .netting›)
       exact nextRider_pinned _ _ (hl (by simp)) (hc rfl) (he rfl))
    | exact pinned_retip s _ h ‹s.stage = .rebasing› rfl rfl rfl
        (by simpa using ‹¬(!isSha _) = true›) rfl
    | exact pinned_restage s _ h ‹_› rfl rfl rfl rfl rfl rfl

private theorem stepGate_no_mutate (s : State) (o : Obs) :
    ((stepGate s o).2).mutates = false := by
  unfold stepGate
  repeat' split
  all_goals first
    | exact nextGate_mutates _
    | exact fallBack_mutates _ _
    | exact treeFailed_mutates _ _
    | simp [internal, gateFailed, Act.mutates, Act.writes, Writes.shared]

private theorem stepGate_no_rebase (s : State) (o : Obs) (t b : Sha) :
    (stepGate s o).2 ≠ .rebase t b := by
  unfold stepGate
  repeat' split
  all_goals first
    | exact nextGate_rebase _ t b
    | exact fallBack_rebase _ _ t b
    | exact treeFailed_rebase _ _ t b
    | simp [internal, gateFailed]

private theorem stepGate_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepGate s o).1.pinned = true := by
  intro h
  unfold stepGate
  repeat' split
  all_goals first
    | (simp only [internal_pinned s h, gateFailed_pinned s h]; done)
    | exact gateFailed_pinned _ (pinned_record s h ‹_› _ _ _ _ (by simp_all) (by simp_all)) _
    | exact fallBack_pinned s _ h ((pinned_facts s h ‹_›).2.2 (by simp))
    | exact treeFailed_pinned s _ h ((pinned_facts s h ‹_›).2.2 (by simp))
    | exact nextGate_pinned _ (pinned_record s h ‹_› _ _ _ _ (by simp_all) (by simp_all))
        ((record_stage s _ _ _ _).trans ‹_›)
    | exact nextGate_pinned _ (pinned_congr s _ h rfl rfl rfl rfl rfl) ‹_›

private theorem stepMerge_no_rebase (s : State) (o : Obs) (t b : Sha) :
    (stepMerge s o).2 ≠ .rebase t b := by
  unfold stepMerge
  repeat' split
  all_goals first
    | exact (afterLanded_quiet _ t b).1
    | simp [refuse, internal, gateFailed, landedNotPushed, succeed]

private theorem stepMerge_mutates_gated (s : State) (o : Obs) :
    ((stepMerge s o).2).mutates = true → (stepMerge s o).1.proven = true := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals first
    | (simp only [refuse_snd, internal_snd, gateFailed_snd, landedNotPushed_snd, succeed_snd,
        halt_quiet] at h; simp at h; done)
    | (simp only [Act.mutates, Act.writes, Writes.shared, List.any_cons, List.any_nil,
        Bool.or_false] at h; simp at h; done)
    | (rw [ite_eq_left ‹_›]; exact ((Bool.and_eq_true _ _).mp ‹_›).1)
    | exact afterLanded_mutates_gated _ h

private theorem stepMerge_ff_covers (s : State) (o : Obs) (t : Sha) :
    (stepMerge s o).2 = .fastForward t →
      (stepMerge s o).1.gateIdx = (stepMerge s o).1.plan.size := by
  intro h
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals first
    | exact absurd h (afterLanded_quiet _ t t).2
    | simp_all [refuse, internal, gateFailed, landedNotPushed, succeed]

private theorem stepMerge_ff_exact (s : State) (o : Obs) (t : Sha) (hp : s.pinned = true) :
    (stepMerge s o).2 = .fastForward t →
      t = (stepMerge s o).1.gatedTip ∧ (stepMerge s o).1.gatedAt t = true := by
  intro h
  obtain ⟨-, -, -, hd, he⟩ := pinned_parts s hp
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals first
    | exact absurd h (afterLanded_quiet _ t t).2
    | simp_all [refuse, internal, gateFailed, landedNotPushed, succeed, State.gatedAt,
        State.rebased, Stage.rebased]

private theorem stepMerge_push_exact (s : State) (o : Obs) (t : Sha) (hp : s.pinned = true) :
    (stepMerge s o).2 = .push t →
      t = (stepMerge s o).1.gatedTip ∧ t = (stepMerge s o).1.mainAt
        ∧ (stepMerge s o).1.gatedAt t = true := by
  intro h
  obtain ⟨_, _, _, hd, _⟩ := pinned_parts s hp
  unfold stepMerge at h ⊢
  repeat' split at h
  all_goals first
    | (apply afterLanded_push _ t _ (by stage_simp) h
       simp_all [State.pinned, State.atOrPastFF, State.preTree, State.rebased, Stage.pastFF,
         Stage.preTree, Stage.rebased, State.landedVerdict, State.landedIsGated])
    | simp_all [refuse, internal, gateFailed, landedNotPushed, succeed]

private theorem stepMerge_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepMerge s o).1.pinned = true := by
  intro h
  unfold stepMerge
  repeat' split
  all_goals first
    | (simp only [refuse_pinned s h, internal_pinned s h, gateFailed_pinned s h]; done)
    | exact pinned_restage s _ h ‹_› rfl rfl rfl rfl rfl rfl
    | exact landedNotPushed_pinned s _ h (by simp [State.atOrPastFF, ‹s.stage = _›, Stage.pastFF])
    | exact succeed_pinned s _ h fun _ =>
        pinned_pastFF s h (by simp [State.atOrPastFF, ‹s.stage = _›, Stage.pastFF])
    | exact afterLanded_pinned s h (by simp [State.atOrPastFF, ‹s.stage = _›, Stage.pastFF])
    | exact pinned_verified s _ h ‹_› rfl rfl rfl rfl (by simp_all) (by simp_all)

/-- At a rider stage the run has no gate yet, a sha for the train's tip and no landing. -/
private theorem pinned_riding (s : State) (h : s.pinned = true) (hp : s.stage.preTree = true)
    (hr : s.stage.rebased = true) :
    s.gates.isEmpty = true ∧ isSha s.gatedTip = true ∧ s.landedVerdict = false := by
  obtain ⟨hc, he, hl⟩ := pinned_facts s h rfl
  exact ⟨hc hp, he hr, hl fun hd => by simp [hd, Stage.preTree] at hp⟩

private theorem rideAbsent_pinned (s : State) (i : Nat) (m : BranchMiss) (h : s.pinned = true)
    (hs : s.stage = .riderPre) : (rideAbsent s i m).1.pinned = true := by
  obtain ⟨hc, he, hl⟩ := pinned_riding s h (by rw [hs]; rfl) (by rw [hs]; rfl)
  unfold rideAbsent
  repeat' split
  all_goals first
    | exact internal_pinned s h _
    | exact dropRider_pinned s _ _ hl hc he

private theorem rideStatus_pinned (s : State) (i a : Nat) (c : Bool) (t f g : Sha) (m : Bool)
    (h : s.pinned = true) (hs : s.stage = .riderPre) :
    (rideStatus s i a c t f g m).1.pinned = true := by
  obtain ⟨hc, he, hl⟩ := pinned_riding s h (by rw [hs]; rfl) (by rw [hs]; rfl)
  unfold rideStatus
  repeat' split
  all_goals first
    | exact internal_pinned s h _
    | exact dropRider_pinned s _ _ hl hc he
    | exact pinned_restage s _ h hs rfl rfl rfl rfl rfl rfl

private theorem rideUnread_pinned (s : State) (i : Nat) (w : String) (h : s.pinned = true)
    (hp : s.stage.preTree = true) (hr : s.stage.rebased = true) :
    (rideUnread s i w).1.pinned = true := by
  obtain ⟨hc, he, hl⟩ := pinned_riding s h hp hr
  unfold rideUnread
  repeat' split
  all_goals first
    | exact internal_pinned s h _
    | exact dropRebased_pinned s _ _ hl hc he
    | exact dropRider_pinned s _ _ hl hc he

private theorem rideRebased_pinned (s : State) (i : Nat) (t : Sha) (c : Bool) (h : s.pinned = true)
    (hs : s.stage = .riderRebasing) : (rideRebased s i t c).1.pinned = true := by
  obtain ⟨hc, he, hl⟩ := pinned_riding s h (by rw [hs]; rfl) (by rw [hs]; rfl)
  unfold rideRebased
  repeat' split
  all_goals first
    | exact internal_pinned s h _
    | exact dropRebased_pinned s _ _ hl hc he
    | exact pinned_restage s _ h hs rfl rfl rfl rfl rfl rfl

private theorem rideConflict_pinned (s : State) (i : Nat) (fs : Array String) (h : s.pinned = true)
    (hs : s.stage = .riderRebasing) : (rideConflict s i fs).1.pinned = true := by
  obtain ⟨hc, he, hl⟩ := pinned_riding s h (by rw [hs]; rfl) (by rw [hs]; rfl)
  unfold rideConflict
  repeat' split
  all_goals first
    | exact internal_pinned s h _
    | exact dropRebased_pinned s _ _ hl hc he

private theorem rideNet_pinned (s : State) (i : Nat) (b a : String) (h : s.pinned = true)
    (hs : s.stage = .riderNetting) : (rideNet s i b a).1.pinned = true := by
  obtain ⟨hc, he, hl⟩ := pinned_riding s h (by rw [hs]; rfl) (by rw [hs]; rfl)
  unfold rideNet
  repeat' split
  all_goals first
    | exact internal_pinned s h _
    | exact dropRebased_pinned s _ _ hl hc he
    | exact nextRider_pinned _ _ hl hc (by simpa using ‹¬(!isSha s.pendingTip) = true›)

private theorem rideRetreed_pinned (s : State) (t : Sha) (c : Bool) (h : s.pinned = true)
    (hs : s.stage = .retreeing) : (rideRetreed s t c).1.pinned = true := by
  obtain ⟨hc, he, hl⟩ := pinned_riding s h (by rw [hs]; rfl) (by rw [hs]; rfl)
  unfold rideRetreed
  repeat' split
  all_goals first
    | exact internal_pinned s h _
    | exact nextRider_pinned _ _ hl hc he

private theorem rideRecheck_pinned (s : State) (ts : Array Sha) (h : s.pinned = true)
    (hs : s.stage = .ridersRecheck) : (rideRecheck s ts).1.pinned = true := by
  unfold rideRecheck
  split
  · exact pinned_restage s _ h hs rfl rfl rfl rfl rfl rfl
  · exact cutAt_pinned s _ h ((pinned_facts s h hs).2.2 (by simp))

private theorem stepRide_no_mutate (s : State) (o : Obs) :
    ((stepRide s o).2).mutates = false := by
  unfold stepRide rideAbsent rideStatus rideUnread rideRebased rideConflict rideNet rideRetreed
    rideRecheck
  repeat' split
  all_goals first
    | exact dropRider_mutates _ _ _
    | exact dropRebased_mutates _ _ _
    | exact nextRider_mutates _ _
    | exact cutAt_mutates _ _
    | simp [internal, Act.mutates, Act.writes, Writes.shared]

private theorem stepRide_no_rebase (s : State) (o : Obs) (t b : Sha) :
    (stepRide s o).2 ≠ .rebase t b := by
  unfold stepRide rideAbsent rideStatus rideUnread rideRebased rideConflict rideNet rideRetreed
    rideRecheck
  repeat' split
  all_goals first
    | exact dropRider_rebase _ _ _ t b
    | exact dropRebased_rebase _ _ _ t b
    | exact nextRider_rebase _ _ t b
    | exact cutAt_rebase _ _ t b
    | simp [internal]

private theorem stepRide_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepRide s o).1.pinned = true := by
  intro h
  unfold stepRide
  split
  · exact rideAbsent_pinned s _ _ h ‹_›
  · exact rideStatus_pinned s _ _ _ _ _ _ _ h ‹_›
  · exact rideRebased_pinned s _ _ _ h ‹_›
  · exact rideConflict_pinned s _ _ h ‹_›
  · exact rideNet_pinned s _ _ _ h ‹_›
  · exact rideUnread_pinned s _ _ h (by rw [‹s.stage = _›]; rfl) (by rw [‹s.stage = _›]; rfl)
  · exact rideUnread_pinned s _ _ h (by rw [‹s.stage = _›]; rfl) (by rw [‹s.stage = _›]; rfl)
  · exact rideRetreed_pinned s _ _ h ‹_›
  · exact rideRecheck_pinned s _ h ‹_›
  · exact internal_pinned s h _

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

private theorem stepRide_unheld (s : State) (a b : Nat) (c : Bool) (t f g : Sha) (m : Bool) :
    stepRide s (.branchStatus a b c t f g m) = stepRide s (.branchStatus a b c t "" "" m) := by
  cases hs : s.stage <;> simp [stepRide, hs, Obs.tag]

attribute [irreducible] stepPre stepGate stepMerge stepRide

private theorem phaseOf_cases (st : Stage) :
    phaseOf st = stepPre ∨ phaseOf st = stepGate ∨ phaseOf st = stepMerge
      ∨ phaseOf st = stepRide := by
  cases st <;> simp [phaseOf]

private theorem phaseOf_mutates_gated (st : Stage) (s : State) (o : Obs) :
    ((phaseOf st s o).2).mutates = true → (phaseOf st s o).1.proven = true := by
  intro h
  rcases phaseOf_cases st with e | e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o; simp_all
  · have hn := stepGate_no_mutate s o; simp_all
  · exact stepMerge_mutates_gated s o h
  · have hn := stepRide_no_mutate s o; simp_all

private theorem phaseOf_ff_covers (st : Stage) (s : State) (o : Obs) (t : Sha) :
    (phaseOf st s o).2 = .fastForward t →
      (phaseOf st s o).1.gateIdx = (phaseOf st s o).1.plan.size := by
  intro h
  rcases phaseOf_cases st with e | e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · have hn := stepGate_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · exact stepMerge_ff_covers s o t h
  · have hn := stepRide_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn

private theorem phaseOf_ff_exact (st : Stage) (s : State) (o : Obs) (t : Sha)
    (hp : s.pinned = true) :
    (phaseOf st s o).2 = .fastForward t →
      t = (phaseOf st s o).1.gatedTip ∧ (phaseOf st s o).1.gatedAt t = true := by
  intro h
  rcases phaseOf_cases st with e | e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · have hn := stepGate_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · exact stepMerge_ff_exact s o t hp h
  · have hn := stepRide_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn

private theorem phaseOf_push_exact (st : Stage) (s : State) (o : Obs) (t : Sha)
    (hp : s.pinned = true) :
    (phaseOf st s o).2 = .push t →
      t = (phaseOf st s o).1.gatedTip ∧ t = (phaseOf st s o).1.mainAt
        ∧ (phaseOf st s o).1.gatedAt t = true := by
  intro h
  rcases phaseOf_cases st with e | e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · have hn := stepGate_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn
  · exact stepMerge_push_exact s o t hp h
  · have hn := stepRide_no_mutate s o
    rw [h] at hn; simp [Act.mutates, Act.writes, Writes.shared] at hn

private theorem phaseOf_rebase_exact (st : Stage) (s : State) (o : Obs) (t b : Sha) :
    (phaseOf st s o).2 = .rebase t b →
      t = (phaseOf st s o).1.branchTip ∧ b = (phaseOf st s o).1.prevMainTip
        ∧ isSha t = true ∧ isSha b = true := by
  intro h
  rcases phaseOf_cases st with e | e | e | e <;> rw [e] at h ⊢
  · exact stepPre_rebase_exact s o t b h
  · exact absurd h (stepGate_no_rebase s o t b)
  · exact absurd h (stepMerge_no_rebase s o t b)
  · exact absurd h (stepRide_no_rebase s o t b)

private theorem phaseOf_pinned (st : Stage) (s : State) (o : Obs) :
    s.pinned = true → (phaseOf st s o).1.pinned = true := by
  intro h
  rcases phaseOf_cases st with e | e | e | e <;> rw [e]
  · exact stepPre_pinned s o h
  · exact stepGate_pinned s o h
  · exact stepMerge_pinned s o h
  · exact stepRide_pinned s o h

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
  · exact internal_pinned s h _
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
  rcases phaseOf_cases s.stage with e | e | e | e <;> rw [e]
  · exact stepPre_unheld s a b c t f g
  · exact stepGate_unheld s a b c t f g false
  · exact stepMerge_unheld s a b c t f g false
  · exact stepRide_unheld s a b c t f g false

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
      | (rcases hw with rfl | rfl | rfl <;> rfl)

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

theorem init_pinned (name : String) (m : Mode) (plan : Array GateSpec) (p : Bool)
    (riders : Array String) : (State.init name m plan p riders).pinned = true := by
  simp [State.init, State.pinned, State.atOrPastFF, State.preTree, State.rebased, Stage.pastFF,
    Stage.preTree, Stage.rebased, State.landedVerdict]

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
  /-- The gate list a plain landing lands under, which a train's riders share; empty for a run
  that rides no train. -/
  fare : String
  /-- The run whose train this waiter rides, empty while it waits. -/
  train : String
  deriving DecidableEq, Repr, Inhabited

namespace Queue

/-- Whether `w` takes the place of `x`, a waiter under its name: `x` waits under `w`'s run, or
under a dead one and rides no live train but under `w`'s fare. -/
def takes (live : String → Bool) (x w : Waiter) : Bool :=
  x.run == w.run || (!live x.run && (x.train.isEmpty || !live x.train || x.fare == w.fare))

/-- Enter `w`: a name waiting under another live run, or riding a live train under another fare,
stays as it is; one it takes keeps its place, its arrival and its train and takes `w`'s run,
process and fare; a name not waiting arrives last. -/
def enter (q : List Waiter) (live : String → Bool) (w : Waiter) : List Waiter :=
  if q.any (·.name == w.name) then
    q.map fun x =>
      if x.name == w.name && takes live x w then
        { x with run := w.run, pid := w.pid, fare := w.fare }
      else x
  else q ++ [w]

/-- The queue without `name`. -/
def leave (q : List Waiter) (name : String) : List Waiter := q.filter (·.name != name)

/-- The waiters not riding a live train. -/
def waiting (q : List Waiter) (live : String → Bool) : List Waiter :=
  q.filter fun x => x.train.isEmpty || !live x.train

/-- The waiters that arrived before `name`, all of them when it is not waiting. -/
def ahead (q : List Waiter) (name : String) : List Waiter := q.takeWhile (·.name != name)

/-- Each waiter's name and arrival, in order. -/
def arrivals (q : List Waiter) : List (String × String) := q.map fun x => (x.name, x.since)

/-- The live waiters behind `w`'s name, in arrival order. -/
def behind (q : List Waiter) (live : String → Bool) (w : Waiter) : List Waiter :=
  (((waiting q live).dropWhile (·.name != w.name)).drop 1).filter (live ·.run)

/-- The riders a head entered as `w` takes into its train: the live waiters right behind it,
in arrival order, up to the first under another fare and `reach - 1` at most; none for a head
that rides no train. -/
def riders (q : List Waiter) (live : String → Bool) (w : Waiter) (reach : Nat) : List String :=
  if w.fare.isEmpty then []
  else (((behind q live w).takeWhile (·.fare == w.fare)).take (reach - 1)).map (·.name)

/-- Mark the named waiters as riding the train of run `train`. -/
def board (q : List Waiter) (rs : List String) (train : String) : List Waiter :=
  q.map fun x => if rs.contains x.name then { x with train } else x

/-- Put the named waiters back to waiting. -/
def alight (q : List Waiter) (rs : List String) : List Waiter :=
  q.map fun x => if rs.contains x.name then { x with train := "" } else x

end Queue

/-- The most branches one landing run lands together. -/
def trainCap : Nat := 4

/-- What a run asking for the landing lock does, decided under the queue's own lock. -/
inductive Turn where
  /-- Take the landing lock and leave the queue, with these riders: no live waiter arrived
  before this run's name. -/
  | take (riders : List String)
  /-- Wait and ask again: fewer live waiters than a train holds arrived first, or none and the
  lock is held. -/
  | wait
  /-- Refuse with exit 2, the place kept: `head`, live, arrived first, among a train's worth of
  live waiters, and this run's name stands at `place` among those waiting, counted from 1. -/
  | behind (place : Nat) (head : String)
  /-- Refuse with exit 2: this run's name waits under another live run, or rides its train under
  another fare, `run`. -/
  | held (run : String)
  /-- Wait for the verdict of the live run `train`, whose train this run's name rides. -/
  | rides (train : String)
  /-- Refuse with exit 2: this run's name waits under no live run but a dead one, or no longer
  waits: it landed, retired, or was made new. -/
  | gone
  deriving DecidableEq, Repr, Inhabited

/-- The turn of `run`, entered as `name`, with the lock free or held, a train taking `reach`
branches, the runs' liveness as read: the live waiters ahead decide, and with none the lock
does. -/
def Queue.turn (q : List Waiter) (live : String → Bool) (name run : String) (free : Bool)
    (reach : Nat) : Turn :=
  match q.find? (·.name == name) with
  | none => .gone
  | some w =>
    if w.run != run then
      (if live w.run then .held w.run
       else if !w.train.isEmpty && live w.train then .held w.train else .gone)
    else if !w.train.isEmpty && live w.train then .rides w.train
    else match (Queue.ahead (Queue.waiting q live) name).filter (live ·.run) with
      | [] => if free then .take (Queue.riders q live w reach) else .wait
      | h :: rest =>
        if rest.length + 1 < reach then .wait
        else .behind ((Queue.ahead (Queue.waiting q live) name).length + 1) h.name

/-- What writes the queue: an ask for the lock, decided as `t`, and a name dropped when its
branch is retired or made new. -/
inductive QueueOp where
  | ask (t : Turn)
  | drop

/-- Where a queue operation writes: the queue, entered, boarded or left, and on a take the
lock's record and the abandoned row of a holder that died. -/
def QueueOp.writes : QueueOp → List Writes
  | .ask (.take _) => [.queue, .lockRecord, .ledger]
  | .ask .wait => [.queue]
  | .ask (.behind ..) => [.queue]
  | .ask (.held _) => [.queue]
  | .ask (.rides _) => [.queue]
  | .ask .gone => [.queue]
  | .drop => [.queue]

/-- A queue operation writes only what its run owns, and no ref or worktree another party
reads. -/
theorem queueOp_writes_owned (s : State) (op : QueueOp) :
    ∀ w ∈ op.writes, w.owned s = true ∧ w.shared = false := by
  intro w hw
  rcases op with (_ | _ | _ | _ | _ | _) | _ <;>
    simp only [QueueOp.writes, List.mem_cons, List.not_mem_nil, or_false] at hw
  all_goals first
    | (subst hw; exact ⟨rfl, rfl⟩)
    | (rcases hw with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩)

/-- **A run takes the landing lock, with its train's riders, exactly when the lock is free, its
name waits under this run and rides no live train, and every waiting waiter that arrived before
it is dead.** -/
theorem turn_take_exact (q : List Waiter) (live : String → Bool) (name run : String)
    (free : Bool) (reach : Nat) (rs : List String) :
    Queue.turn q live name run free reach = .take rs ↔
      free = true ∧ ∃ w, q.find? (·.name == name) = some w ∧ w.run = run
        ∧ (w.train.isEmpty = true ∨ live w.train = false)
        ∧ (∀ x ∈ Queue.ahead (Queue.waiting q live) name, live x.run = false)
        ∧ rs = Queue.riders q live w reach := by
  unfold Queue.turn
  split
  · rename_i h
    simp [h]
  · rename_i w hw
    split
    · rename_i hr
      have hne : ¬ w.run = run := by simpa using hr
      constructor
      · intro h
        split at h <;> (try split at h) <;> simp at h
      · rintro ⟨-, w', hw', hr', -⟩
        rw [hw] at hw'
        cases hw'
        exact absurd hr' hne
    · rename_i hr
      have hr' : w.run = run := by simpa using hr
      split
      · rename_i htr
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at htr
        simp only [reduceCtorEq, false_iff]
        rintro ⟨-, w', hw', -, ht', -⟩
        rw [hw] at hw'
        cases hw'
        cases ht' <;> simp_all
      · rename_i htr
        split
        · rename_i hf
          rw [List.filter_eq_nil_iff] at hf
          have ht : w.train.isEmpty = true ∨ live w.train = false := by
            cases h1 : w.train.isEmpty <;> cases h2 : live w.train <;> simp_all
          constructor
          · intro h
            cases free
            · simp at h
            · simp at h
              exact ⟨rfl, w, hw, hr', ht, fun x hx => by simpa using hf x hx, h.symm⟩
          · rintro ⟨rfl, w', hw', -, -, -, rfl⟩
            rw [hw] at hw'
            cases hw'
            rfl
        · rename_i x rest hf
          have hx : x ∈ (Queue.ahead (Queue.waiting q live) name).filter (live ·.run) := by
            rw [hf]; exact List.mem_cons_self
          simp only [List.mem_filter] at hx
          have hnt : (if rest.length + 1 < reach then Turn.wait
              else Turn.behind ((Queue.ahead (Queue.waiting q live) name).length + 1) x.name)
                ≠ .take rs := by split <;> simp
          simp only [hnt, false_iff]
          rintro ⟨-, w', -, -, -, hd, -⟩
          have := hd x hx.1
          simp_all

/-- **The first live waiting waiter's turn is never a refusal**: it waits while the lock is held
and takes it once free, with its train's riders. -/
theorem turn_first_exact (q : List Waiter) (live : String → Bool) (name run : String)
    (free : Bool) (reach : Nat) (w : Waiter) (hw : q.find? (·.name == name) = some w)
    (hr : w.run = run) (ht : w.train.isEmpty = true ∨ live w.train = false)
    (hd : ∀ x ∈ Queue.ahead (Queue.waiting q live) name, live x.run = false) :
    Queue.turn q live name run free reach
      = if free then .take (Queue.riders q live w reach) else .wait := by
  have hn : (Queue.ahead (Queue.waiting q live) name).filter (live ·.run) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by simp [hd x hx]
  have htr : (!w.train.isEmpty && live w.train) = false := by
    cases ht <;> simp_all
  simp [Queue.turn, hw, hr, hn, htr]

/-- A refusal behind the queue names a live waiter that arrived first, comes only past a train's
worth of live waiters, and names the refused run's place. -/
theorem turn_behind_mem (q : List Waiter) (live : String → Bool) (name run : String)
    (free : Bool) (reach p : Nat) (h : String)
    (ht : Queue.turn q live name run free reach = .behind p h) :
    ∃ x ∈ Queue.ahead (Queue.waiting q live) name, live x.run = true ∧ x.name = h
      ∧ reach ≤ ((Queue.ahead (Queue.waiting q live) name).filter (live ·.run)).length
      ∧ p = (Queue.ahead (Queue.waiting q live) name).length + 1 := by
  unfold Queue.turn at ht
  split at ht
  · simp at ht
  · split at ht
    · split at ht <;> (try split at ht) <;> simp at ht
    · split at ht
      · simp at ht
      · split at ht
        · split at ht <;> simp at ht
        · rename_i x rest hf
          split at ht
          · simp at ht
          · rename_i hlt
            simp only [Turn.behind.injEq] at ht
            have hx : x ∈ (Queue.ahead (Queue.waiting q live) name).filter (live ·.run) := by
              rw [hf]; exact List.mem_cons_self
            simp only [List.mem_filter] at hx
            refine ⟨x, hx.1, hx.2, ht.2, ?_, ht.1.symm⟩
            rw [hf]
            simp only [List.length_cons]
            omega

/-- The lock's state decides only between taking and waiting. -/
theorem turn_free_exact (q : List Waiter) (live : String → Bool) (name run : String)
    (reach : Nat) :
    Queue.turn q live name run false reach =
      match Queue.turn q live name run true reach with
      | .take _ => .wait
      | t => t := by
  unfold Queue.turn
  split
  · rfl
  · rename_i w _
    split
    · cases live w.run <;> cases (!w.train.isEmpty && live w.train) <;> rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

/-- **A train's riders are the live waiters right behind its head, in arrival order, under its
fare, a train's worth at most**: no live waiter between the head and a rider is passed over. -/
theorem riders_mem (q : List Waiter) (live : String → Bool) (w : Waiter) (reach : Nat) :
    (Queue.riders q live w reach).length + 1 ≤ max reach 1
      ∧ Queue.riders q live w reach <+: (Queue.behind q live w).map (·.name)
      ∧ ∀ n ∈ Queue.riders q live w reach, w.fare.isEmpty = false ∧
          ∃ x ∈ Queue.behind q live w, x.name = n ∧ live x.run = true ∧ x.fare = w.fare := by
  unfold Queue.riders
  split
  · simp only [List.length_nil, Nat.zero_add, List.nil_prefix, List.not_mem_nil, false_implies,
      implies_true, and_true]
    omega
  · rename_i hf
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_map, List.length_take]
      omega
    · exact ((List.take_prefix _ _).trans (List.takeWhile_prefix _)).map _
    · intro n hn
      simp only [List.mem_map] at hn
      obtain ⟨x, hx, rfl⟩ := hn
      have hw := List.mem_of_mem_take hx
      have hp := List.all_eq_true.mp (List.all_takeWhile (p := (·.fare == w.fare))) x hw
      have hb := List.takeWhile_subset _ hw
      have hl : live x.run = true := by
        unfold Queue.behind at hb
        exact (List.mem_filter.mp hb).2
      exact ⟨by simpa using hf, x, hb, rfl, hl, by simpa using hp⟩

/-- **Entering keeps every waiter's place and arrival, and puts a name not waiting last.** -/
theorem enter_arrivals_exact (q : List Waiter) (live : String → Bool) (w : Waiter) :
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

/-- **Entering leaves a waiter under another run as it was while that run lives, or while it
rides a live train under another fare.** -/
theorem enter_kept (q : List Waiter) (live : String → Bool) (w x : Waiter) (hx : x ∈ q)
    (hr : x.run ≠ w.run)
    (hl : live x.run = true ∨ (x.train.isEmpty = false ∧ live x.train = true ∧ x.fare ≠ w.fare)) :
    x ∈ Queue.enter q live w := by
  have hk : Queue.takes live x w = false := by
    unfold Queue.takes
    rcases hl with hl | ⟨he, ht, hf⟩ <;> simp_all
  unfold Queue.enter
  split
  · exact List.mem_map.mpr ⟨x, hx, by simp [hk]⟩
  · exact List.mem_append_left _ hx

/-- Leaving keeps the others in their order. -/
theorem leave_arrivals_exact (q : List Waiter) (n : String) :
    Queue.arrivals (Queue.leave q n) = (Queue.arrivals q).filter (·.1 != n) := by
  unfold Queue.leave Queue.arrivals
  rw [List.filter_map]
  rfl

/-- Boarding a train and alighting from one keep every waiter's place and arrival. -/
theorem board_arrivals_exact (q : List Waiter) (rs : List String) (train : String) :
    Queue.arrivals (Queue.board q rs train) = Queue.arrivals q
      ∧ Queue.arrivals (Queue.alight q rs) = Queue.arrivals q := by
  unfold Queue.board Queue.alight Queue.arrivals
  simp only [List.map_map]
  constructor <;> congr 1 <;> funext x <;> simp only [Function.comp] <;> split <;> rfl

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
