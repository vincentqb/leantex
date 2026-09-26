/-
The landing procedure's pure core: a state machine over observations, whose
only outputs are actions. No IO lives here, so every refusal, every
ordering constraint, and the properties that matter — a ref others read is
never touched on an unproven run, every ref a landing moves is moved to the
commit the gates ran on, and a landing writes only what it owns — are
decidable from values and provable, with git and lake nowhere in sight.

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
the tip it produced, read from the run's own tree; the fast-forward and the
push both name that tip; and every later read-back is compared to it —
never to whatever another ref happens to say by then.

The third, reproduced against the second draft: the gates ran in the
branch's own worktree while only the branch *ref* was pinned, so a worktree
switched to another branch mid-landing had its tree gated and the pinned
tip landed; and the push named `main`, publishing whatever `main` was at
push time. The gate tree is the answer to the first — nobody else writes
it, and its `HEAD` is read back around every gate — and `.push` carrying a
sha is the answer to the second.

The fourth, found by a landing rather than a reviewer: a rebase through a
`merge=union` file kept a heading line the branch had deleted, git reported
no conflict, and every gate passed. So the rebase is judged by what it
produced: each file's net change after it — the diff from the new base to
the rebased tip — must be the branch's net change before it, line for line
with positions dropped (`netDrift`), and `proven` requires the comparison to
have held.

The fifth, reproduced against the fourth draft: the rebase ran in the
branch owner's worktree, so a drift was answered by putting the branch back
at the tip read before the rebase — and a commit the owner made while the
rebase ran was erased from the branch and from the owner's worktree. The
restore was the one step that deleted work, and a wildcard had classified
it as writing nothing another party reads. So the gate tree is made first,
detached at the tip the run read, and the rebase runs there (`Act.rebase`
names both shas); a drift refuses with nothing to put back; the branch is
not written at all; and every action declares what it writes
(`Act.writes`, no wildcard), with the statement that a landing writes only
what it owns proved over the step function.
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
  /-- The fast-forward held and was verified; the push was rejected, or the
  remote did not read back at the landed tip. `main` moved; the remote is
  not known to hold it. -/
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
  /-- The gate tree is being made: a detached worktree at the branch's tip
  as this run read it, which only this run writes. -/
  | treeing
  /-- The gate tree is being rebased onto `main` as this run read it. -/
  | rebasing
  /-- The rebase's net content is being compared with the branch's. -/
  | netting
  | gating
  /-- After the gates: does the branch still name the tip this run read? -/
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

/-- What the boundary reports. Every constructor is a parsed fact; the
`garbled` arm is what the boundary sends when it could not produce one.

A gate observation carries the *index* the core dispatched and no name: the
name is the plan's to know, so a gate cannot be reported under another
gate's name and an absence cannot be claimed for a gate that may not be
absent. It also carries the gate tree as read back after the gate ran, so
the evidence each gate produced is tied to the commit it was about. -/
inductive Obs where
  /-- The main worktree: is `HEAD` on `main`, is the tree clean, and what is
  its tip. Two bools rather than one, because a single conjunction reported
  "not on main" as "the main worktree is dirty". -/
  | mainStatus (onMain : Bool) (clean : Bool) (tip : Sha)
  | branchAbsent (miss : BranchMiss)
  /-- The branch: how far ahead and behind `main`, is its own worktree
  clean, and what is its tip. `landedFrom` is the tip an earlier landing of
  this branch read, when that landing rebased it and the branch still
  carries that tip — the ledger's `branch` field — and `landedAs` the commit
  it landed as; both empty otherwise. `landedOnMain` is whether `main`, at
  the tip this run read, holds `landedAs`: the core counts the row only
  then (`landedBars`), so a landing undone by putting `main` back is no
  landing. -/
  | branchStatus (ahead behind : Nat) (clean : Bool) (tip : Sha) (landedFrom landedAs : Sha)
      (landedOnMain : Bool)
  /-- The gate tree this run made, read back: its `HEAD`, and whether it is
  clean. -/
  | treeReady (head : Sha) (clean : Bool)
  /-- The rebase in the gate tree succeeded: the tree's `HEAD` after it, and
  whether the tree is clean and still detached. This is the commit the gates
  run on and the only commit that may land. -/
  | rebaseOk (tip : Sha) (clean : Bool)
  /-- The rebase in the gate tree failed. `files` are the unmerged paths,
  empty when the rebase stopped for another reason. The tree is the run's,
  so there is nothing of anyone else's to put back. -/
  | rebaseFailed (files : Array String)
  /-- The two listings the net comparison reads, as `git diff --no-renames
  -U0 --binary` printed them: the branch's own change (from its fork point
  to its tip) and the rebase's (from the base it was replayed onto to the
  rebased tip). Raw text, so the parse is the core's. -/
  | netDiffs (before after : String)
  /-- The gate at this index passed; the gate tree read back after it. -/
  | gateOk (idx : Nat) (head : Sha) (clean : Bool)
  /-- The gate at this index failed; the gate tree read back after it. -/
  | gateFail (idx : Nat) (head : Sha) (clean : Bool)
  /-- The gate's program is not built. Permitted only where the plan says
  so; it is recorded, and it is not a gate observation. -/
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

/-- The constructor, for a message: an observation can carry two whole diff
listings, which do not belong in a `why`. -/
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

/-- One file's net change: the `diff --git` line naming it, and every line of
its section except the two kinds that record *where* rather than *what* —
hunk headers (line numbers) and `index` lines (blob names). The same change
applied to two different bases differs in exactly those, so what is left is
the change itself, in order. -/
abbrev FileNet := String × Array String

/-- Parse a `git diff --no-renames -U0 --binary` listing into one net change
per file, in the listing's order. A content line always carries its `+`,
`-` or `\` prefix and a binary patch line starts with a length letter, so
neither can be mistaken for a header. -/
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

/-- The path a `diff --git a/<p> b/<p>` line names, for the report; the line
itself when it has another shape (a quoted path). -/
def pathOfKey (k : String) : String :=
  let pre := "diff --git a/"
  let rest := (k.drop pre.length).toString
  let p := (rest.take ((rest.length - 3) / 2)).toString
  if k.startsWith pre && rest == s!"{p} b/{p}" then p else k

/-- The files whose net change differs between two listings — a file in one
and not in the other included — by path, first-seen order, each once. Empty
exactly when every file's change survived. -/
def netDrift (before after : Array FileNet) : Array String := Id.run do
  let find (xs : Array FileNet) (k : String) : Option (Array String) :=
    (xs.find? (·.1 == k)).map (·.2)
  let mut out : Array String := #[]
  for (k, _) in before.append after do
    if find before k != find after k then
      let p := pathOfKey k
      if !out.contains p then out := out.push p
  return out

/-- The sha `git ls-remote` printed for exactly `ref`. It prints one
`<sha><TAB><refname>` line per ref, and a pattern argument matches every
ref whose name *ends* with it at a `/`, so a query for `refs/heads/main`
also answers with `refs/heads/a/refs/heads/main` — which sorts first.
Empty when no line names `ref` exactly, or more than one does. -/
def lsRemoteTip (out ref : String) : Sha :=
  let hits := (out.splitOn "\n").filterMap fun l =>
    match l.splitOn "\t" with
    | [sha, r] => if r == ref then some sha else none
    | _ => none
  match hits with
  | [t] => t
  | _ => ""

/-- One gate in the plan. `mayAbsent` is the whole permission to skip: the
core grants it from here and from nowhere else. -/
structure GateSpec where
  name : String
  mayAbsent : Bool
  deriving DecidableEq, Repr, Inhabited

/-- One gate's outcome, as recorded in the run. An absent gate does not
appear here: an absence is not an observation that a gate passed. `head`
and `clean` are the gate tree as read back after the gate; the core records
an outcome only when the tree was still the gated tip and clean, so every
recorded outcome is evidence about that commit. -/
structure GateObs where
  name : String
  ok : Bool
  head : Sha
  clean : Bool
  deriving DecidableEq, Repr, Inhabited

/-- What the core asks the boundary to do next. `halt` ends the run. -/
inductive Act where
  | probeMain
  | probeBranch
  /-- Make the gate tree: a detached worktree at exactly this commit — the
  branch's tip as this run read it — which only this run writes, removed
  when the run ends. -/
  | makeTree (tip : Sha)
  /-- Rebase the gate tree, starting from exactly `tip`, onto exactly
  `onto` — `main` as this run read it. Two shas and no ref: the rebase's
  input cannot move under it, and the only `HEAD` it writes is the tree's. -/
  | rebase (tip onto : Sha)
  /-- List the two net changes: the branch's, from its fork point with
  `newBase` to `oldTip`, and the rebase's, from `newBase` to `newTip`. -/
  | netDiff (oldTip newBase newTip : Sha)
  /-- Run the gate at this index of the plan, in the gate tree; the name is
  for the log. -/
  | gate (idx : Nat) (name : String)
  | recheckBranch
  | recheckMain
  /-- The write-ahead row: this run is about to move `main` to this tip. -/
  | writeLanding
  /-- Fast-forward `refs/heads/main`, by that name, to exactly this commit —
  the tip the gates ran on, never a branch name that may have moved since,
  and never whatever ref the main worktree's `HEAD` happens to name. -/
  | fastForward (tip : Sha)
  | readMain
  | writeLanded
  /-- Push exactly this commit to the remote's `main`, as a fast-forward and
  never a forced update — never the local `main`, which another party may
  have moved since it was read back. -/
  | push (tip : Sha)
  | readRemote
  | halt (v : Verdict) (code : UInt32) (why : String)
  deriving Repr, Inhabited

/-- Where an action writes. Declared for every action, with no wildcard, so
a new action says what it writes where it is written: the drift restore
that erased an owner's commit was classified by a wildcard as writing
nothing another party reads, while it reset the owner's branch and
worktree. -/
inductive Writes where
  /-- The run's gate tree: the detached worktree it made, git's
  administrative files for it, and what a gate writes inside it. -/
  | gateTree
  /-- The ledger file. -/
  | ledger
  /-- `refs/heads/main`, by that name, fast-forward only, to this commit;
  and the worktree that has `main` checked out, only through git's own
  sync, which refuses a worktree with changes and then moves nothing. -/
  | mainTo (tip : Sha)
  /-- The remote's `refs/heads/main`, by a push of this commit that is never
  forced. -/
  | remoteTo (tip : Sha)
  /-- A branch another party owns, only by compare-and-swap from `old`, the
  tip this run read. -/
  | branchCas (old new : Sha)
  /-- A ref or a worktree another party owns, written without a
  compare-and-swap against a sha this run read. -/
  | foreign
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

/-- The actions that change a ref or a worktree another party reads: read
off the declared writes, so no action is exempt by omission. -/
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
  /-- How many of the plan's gates have been observed. Also the index the
  next observation must carry. -/
  gateIdx : Nat
  wantPush : Bool
  /-- `main`'s tip when the run started. The merge refuses unless `main` is
  still here. -/
  prevMainTip : Sha
  /-- The branch's tip as this run read it: where the gate tree was made,
  what the rebase started from, and what the branch must still name after
  the gates. -/
  branchTip : Sha
  /-- The commit the rebase produced, read from the gate tree: what the
  gates ran on, what the merge and the push name, what every later
  read-back is compared to. -/
  gatedTip : Sha
  /-- Did the rebase keep every file's net change? Set only where the
  comparison came back empty. -/
  netSame : Bool
  /-- `main`, as read back after the fast-forward. Empty until then. -/
  mainAt : Sha
  verdict : Option Verdict
  deriving Repr, Inhabited

/-- Was every gate observation in the run ok? -/
def State.gatesOk (s : State) : Bool := s.gates.all (·.ok)

/-- The run has earned a ref change: the rebase kept the branch's net
content, at least one gate was observed, and every observation was ok. The
gate half alone is vacuously true of a run in which no gate ever ran, which
is the other way this property could hold while proving nothing. -/
def State.proven (s : State) : Bool := s.netSame && !s.gates.isEmpty && s.gatesOk

/-- The gates' evidence is about `t`: `t` is a sha, and the gate tree read
back at `t`, clean, after every gate the run recorded. -/
def State.gatedAt (s : State) (t : Sha) : Bool :=
  isSha t && s.gates.all (fun g => g.head == t && g.clean)

/-- Is this write one the run owns, given the state it was proposed from?
The tree and the ledger are the run's. `main` and the remote only to the
gated tip, with the gates' evidence about it and the run proven; the remote
only to the `main` the run read back. A branch another party owns only by a
compare-and-swap from the tip this run read. Never anything else. -/
def Writes.owned (s : State) : Writes → Bool
  | .gateTree => true
  | .ledger => true
  | .mainTo t => t == s.gatedTip && s.gatedAt t && s.proven
  | .remoteTo t => t == s.gatedTip && t == s.mainAt && s.gatedAt t && s.proven
  | .branchCas old _ => isSha old && old == s.branchTip && s.proven
  | .foreign => false

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

/-- The `main` this run read back is the commit the gates ran on, and that
commit is a real sha — so the equality is not two empty strings agreeing. -/
def State.landedIsGated (s : State) : Bool :=
  s.mainAt == s.gatedTip && isSha s.gatedTip

/-- The run's invariant, preserved by every transition. From the
fast-forward's verification onward, and under any verdict that claims a
landing, the landing is the gated commit's, and such a verdict appears only
at `done`, which keeps the gated tip from being rewritten under a live
claim. No gate is recorded before the rebase is judged; every recorded gate
read the tree back at the gated tip, clean; and from the rebase onward the
gated tip is a sha. Spelled as one boolean formula rather than a match over
stages: it is proved against every transition, and a match there multiplies
each proof by the number of stages. -/
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

/-- `main` moved and was verified at the gated tip; the remote is not known
to hold it. Its own exit code, 4, because a failed gate (1) and a landing
that happened are different facts to a caller reading only the status. -/
private def landedNotPushed (s : State) (why : String) : State × Act :=
  ({ s with stage := .done, verdict := some .landedUnpushed }, .halt .landedUnpushed 4 why)

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

/-- Does an earlier landing bar this branch from landing again? Only while
the branch still carries the tip that landing read (`landedFrom`, empty
otherwise) and `main` as this run read it holds the commit it landed as. A
landing `main` no longer holds — `main` put back past it, before any push —
bars nothing: the branch's work is not on `main`, and landing it is how it
gets there. The ledger row alone once barred it, and the remedy the refusal
named then dropped that work from the branch. -/
def landedBars (landedFrom : Sha) (landedOnMain : Bool) : Bool :=
  !landedFrom.isEmpty && landedOnMain

/-- The refusal of a landed branch. A landed branch is never continued: its
work reached `main` as rebased copies, so the next unit starts on a new
branch from `main`. Commits made on the branch since the landing are named
as a range and left where they are — no command here writes the branch. -/
def landedWhy (name : String) (landedFrom landedAs tip : Sha) : String :=
  s!"agent/{name} is already landed, as {landedAs}, which main holds: a landed branch \
takes no further landing, so start the next unit on a new branch from main (land new <name>)"
    ++ (if landedFrom == tip then "" else
      s!"; its commits since, {landedFrom}..{tip}, stay on agent/{name}")

/-- The preconditions, the gate tree, the rebase in it and the net
comparison: every stage before a gate runs. Split out from `step` so a
theorem about the merge half unfolds none of it — the whole machine in one
match walled every proof off behind a heartbeat limit, and a limit raised is
not a factorization. -/
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
    -- An earlier landing replayed this branch onto `main` and left it where
    -- it was. While `main` holds that landing the branch is landed, and a
    -- landed branch is not continued; once `main` does not, the row bars
    -- nothing and the branch lands again.
    else if landedBars landedFrom onMain then refuse s (landedWhy s.name landedFrom landedAs tip)
    else ({ s with stage := .treeing, branchTip := tip }, .makeTree tip)
  | .treeing, .treeReady head clean =>
    -- A tree this run just made, not at the tip it was made from, or not
    -- clean, is a fault in the boundary or the repository, not the branch's.
    -- One test per fact, so each branch carries its own.
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
    -- The rebase ran in the run's own tree, which the halt removes: there is
    -- nothing of the owner's to put back.
    if !files.isEmpty then refuse s s!"rebase conflict: {String.intercalate " " files.toList}"
    else refuse s "the rebase failed"
  | .netting, .netDiffs before after =>
    -- Every file counts, a union-merged one first among them: git reports
    -- no conflict for a hunk the union driver joined, and that is exactly
    -- where a deleted line came back. A reported conflict never reaches
    -- here — it stopped the rebase above. No `let` for the drift: a bound
    -- conditional is one `split` cannot see.
    if (netDrift (netOf before) (netOf after)).isEmpty then
      nextGate { s with stage := .gating, netSame := true }
    else
      refuse s s!"the rebase changed the net content of: \
{String.intercalate " " (netDrift (netOf before) (netOf after)).toList}"
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- Record one gate's outcome, with the gate tree as read back after it, and
advance the index the next observation must carry. -/
private def record (s : State) (g : GateSpec) (ok : Bool) (head : Sha) (clean : Bool) : State :=
  { s with gates := s.gates.push ⟨g.name, ok, head, clean⟩, gateIdx := s.gateIdx + 1 }

/-- The gate phase. An observation carries the index the core dispatched and
no name: a gate cannot answer under another gate's name, and an absence is
permitted only where the plan says so. Every gate's observation carries the
gate tree as read back after it; a tree that moved or was dirtied is the
gate's failure, and its outcome is not recorded as evidence. -/
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

/-- The merge half: the two re-reads, the write-ahead row, the
fast-forward, and the push. Both mutating actions live here, both are
guarded in this function alone, and both name `gatedTip`. -/
private def stepMerge (s : State) (o : Obs) : State × Act :=
  match s.stage, o with
  | .postGate, .branchRecheck tip =>
    -- The gates ran in the run's own tree on a commit the run made, so this
    -- is not evidence about what they saw; it is whether the owner still
    -- names the tip this run read. A branch that moved on refuses rather
    -- than landing work its owner has since extended, and the branch is left
    -- as the owner left it: this run never wrote it.
    if tip != s.branchTip then refuse s s!"agent/{s.name} moved during the landing"
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
      if s.proven then ({ s with stage := .pushing }, .push s.gatedTip)
      else gateFailed s "no gate observation in this run, or one was not ok"
    else succeed s .landed
  | .ledgering, .ledgerFail => internal s "the ledger was not written"
  | .pushing, .pushOk => ({ s with stage := .verifyPush }, .readRemote)
  | .pushing, .pushRejected =>
    -- `main` moved and was verified; only the remote did not. Reporting
    -- this as a failure hid a landing that had happened.
    landedNotPushed s "the push was rejected; main is landed"
  | .verifyPush, .remoteTip ot =>
    if isSha ot && ot == s.mainAt then succeed s .landed
    else landedNotPushed s "the remote's main did not read back at the landed tip; main is landed"
  | st, ob => internal s s!"{st.name}: unexpected {ob.tag}"

/-- Which phase owns a stage. A function of the stage alone, so a proof
about every transition splits this free variable once instead of splitting
`s.stage` inside a goal that also mentions `s` three more times — which is
where the whole-machine proof hit its heartbeat wall. -/
private def phaseOf : Stage → (State → Obs → State × Act)
  | .preMain | .preBranch | .treeing | .rebasing | .netting => stepPre
  | .gating => stepGate
  | _ => stepMerge

/-- One observation, one action. Every pair the procedure does not expect is
an internal failure: a state machine driven off its own transitions is
exactly the condition under which narration got believed. -/
def step (s : State) (o : Obs) : State × Act :=
  match o with
  | .garbled what => internal s s!"unparseable output: {what}"
  | o => phaseOf s.stage s o

-- The run-level statements at the end of this file quantify over this
-- function; the citation gate cannot resolve a name from this module, so
-- they are named there in comments rather than backticked here.
/-- Drive the core through a scripted observation sequence, collecting the
actions it proposed. The selftest's harness. -/
def run (s : State) : List Obs → State × Array Act
  | [] => (s, #[])
  | o :: os =>
    let (s', a) := step s o
    let (s'', as) := run s' os
    (s'', #[a] ++ as)

/-- Every step of a scripted run: the state it reached, and the action it
proposed from there. The run-level form of the exactness statements reads
this, because an action's sha is a claim about the state it was proposed
from. -/
def trace (s : State) : List Obs → List (State × Act)
  | [] => []
  | o :: os => (step s o) :: trace (step s o).1 os

-- ## `land push`

/-- `land push`: publish the last landing. The commit is the last `landed`
row's tip, which must also be its gated tip and must be what `main` reads
now — a commit on `main` that no landing gated refuses. The push names that
sha, never `main`. -/
def pushPlan (landedTip landedGated mainTip : Sha) : Except String Sha :=
  if !isSha landedTip then .error "the ledger has no landed row with a tip"
  else if landedGated != landedTip then .error "the last landed row's tip is not its gated tip"
  else if mainTip != landedTip then
    .error "main is not at the last landed tip: it holds a commit no landing gated"
  else .ok landedTip

/-- The verdict of `land push`: published only when the push succeeded and
the remote's `main`, read back by its exact name, is the commit pushed. -/
def pushVerdict (pushedOk : Bool) (remote tip : Sha) : Verdict :=
  if pushedOk && isSha remote && remote == tip then .pushed else .landedUnpushed

-- ## The theorems
--
-- Four properties, and the ways each could have held vacuously. Each is
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

/-- The rebase is proposed by the precondition phase alone. -/
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

/-- The branch probe reads an earlier landing only through `landedBars`, so
a landing `main` does not hold reads as none, at every stage. -/
private theorem stepPre_unheld (s : State) (a b : Nat) (c : Bool) (t f g : Sha) :
    stepPre s (.branchStatus a b c t f g false)
      = stepPre s (.branchStatus a b c t "" "" false) := by
  cases hs : s.stage <;> simp [stepPre, hs, landedBars, Obs.tag]

/-- Neither later phase reads a branch probe at all. -/
private theorem stepGate_unheld (s : State) (a b : Nat) (c : Bool) (t f g : Sha) (m : Bool) :
    stepGate s (.branchStatus a b c t f g m) = stepGate s (.branchStatus a b c t "" "" m) := by
  cases hs : s.stage <;> simp [stepGate, hs, Obs.tag]

private theorem stepMerge_unheld (s : State) (a b : Nat) (c : Bool) (t f g : Sha) (m : Bool) :
    stepMerge s (.branchStatus a b c t f g m) = stepMerge s (.branchStatus a b c t "" "" m) := by
  cases hs : s.stage <;> simp [stepMerge, hs, Obs.tag]

/-- At the branch probe, past the three facts checked first, the decision is
`landedBars` and nothing else. -/
private theorem stepPre_barred (s : State) (a b : Nat) (t f g : Sha) (m : Bool)
    (hs : s.stage = .preBranch) (ha : a ≠ 0) (ht : isSha t = true) :
    ((stepPre s (.branchStatus a b true t f g m)).2 = .makeTree t ↔ landedBars f m = false)
      ∧ (landedBars f m = true →
          (stepPre s (.branchStatus a b true t f g m)).2
            = .halt .refused 2 (landedWhy s.name f g t)) := by
  cases hb : landedBars f m <;> simp [stepPre, hs, ha, ht, hb, refuse]

attribute [irreducible] stepPre stepGate stepMerge

/-- Every stage is owned by one of the three phases. The dispatch lemmas
below rewrite with this rather than trying each phase's lemma in turn: a
failed `exact` against the wrong phase unfolds the invariant on both sides
before it gives up, which is where a first draft hit the heartbeat wall. -/
private theorem phaseOf_cases (st : Stage) :
    phaseOf st = stepPre ∨ phaseOf st = stepGate ∨ phaseOf st = stepMerge := by
  cases st <;> simp [phaseOf]

/-- Each phase, lifted to the dispatch: the two mutating actions are
spelled in `stepMerge`, so the other phases discharge by contradiction. -/
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

/-- **No ref another party reads is touched on a run whose gates were not
all ok.** Whenever `step` proposes an action that changes a ref or a
worktree another party reads, the resulting state is `proven` — the rebase
kept the branch's net content, at least one gate was observed, and every
gate observation in the run was ok. -/
theorem step_mutates_gated (s : State) (o : Obs) :
    ((step s o).2).mutates = true → (step s o).1.proven = true := by
  intro h
  unfold step at h ⊢
  split at h
  · simp_all [Act.mutates, Act.writes, Writes.shared, internal]
  · exact phaseOf_mutates_gated _ _ _ h

/-- The fast-forward is proposed only with the gate index at the plan's
size. This restates the guard at the fast-forward's own site; that the index
counts accepted observations one each, and that an absence is taken only
where the plan permits it, are properties of `stepGate`'s code, checked by
the selftest's cases rather than proved here. -/
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
  · simp_all +decide [internal, State.pinned, State.atOrPastFF, State.preTree, State.rebased,
      State.landedVerdict, State.landedIsGated]
  · exact phaseOf_pinned _ _ _ h

/-- A state satisfying the invariant, and claiming a landing, read `main`
back at its gated tip. -/
private theorem pinned_landed (s : State) (h : s.pinned = true)
    (hv : s.landedVerdict = true) : s.landedIsGated = true := by
  unfold State.pinned at h
  simp only [hv, Bool.or_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- **The rebase's input is two shas the run read.** Whenever `step`
proposes the rebase, it starts from the branch's tip as the run read it —
the tip the gate tree was made at — and targets `main` as the run read it,
both shas. No ref appears in it, so a commit the owner makes meanwhile is
neither replayed nor lost: it stays on the owner's branch, which the run
does not write. -/
theorem step_rebase_exact (s : State) (o : Obs) (t b : Sha) :
    (step s o).2 = .rebase t b →
      t = (step s o).1.branchTip ∧ b = (step s o).1.prevMainTip
        ∧ isSha t = true ∧ isSha b = true := by
  intro h
  unfold step at h ⊢
  split at h
  · simp [internal] at h
  · exact phaseOf_rebase_exact _ _ _ _ _ h

/-- **A landing `main` does not hold is no landing.** Whatever the stage and
whatever else the branch probe read, an earlier landing whose commit `main`
— at the tip this run read — does not hold is the same step as no earlier
landing at all: the row counts only while `main` holds what it landed. A
landing undone before any push, by putting `main` back past it, once left
its unmoved branch refused as already landed, and told a continued one to
rebase away the work `main` no longer had. -/
theorem step_unheld_exact (s : State) (a b : Nat) (c : Bool) (t f g : Sha) :
    step s (.branchStatus a b c t f g false) = step s (.branchStatus a b c t "" "" false) := by
  unfold step
  simp only []
  rcases phaseOf_cases s.stage with e | e | e <;> rw [e]
  · exact stepPre_unheld s a b c t f g
  · exact stepGate_unheld s a b c t f g false
  · exact stepMerge_unheld s a b c t f g false

/-- **A landed branch takes no further landing, and only a landed one.** At
the branch probe, a branch ahead of `main`, with a clean worktree and a tip
that reads as a sha, goes on to a gate tree at that tip exactly when no
earlier landing bars it (`landedBars`: the branch carries the tip that
landing read, and `main` holds the commit it landed as). A barred branch is
refused with exit 2 and the refusal that sends the next unit to a new branch
from `main`, which names no command that writes this one. -/
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

/-- **The merge names the gated commit.** Whenever `step` proposes the
fast-forward, it names the run's gated tip, and the gates' evidence is about
that commit: the gate tree read back at it after every gate the run
recorded, clean each time. -/
theorem step_ff_exact (s : State) (o : Obs) (t : Sha) (h : s.pinned = true)
    (ha : (step s o).2 = .fastForward t) :
    t = (step s o).1.gatedTip ∧ (step s o).1.gatedAt t = true := by
  unfold step at ha ⊢
  split at ha
  · simp [internal] at ha
  · exact phaseOf_ff_exact _ _ _ _ h ha

/-- **The push names the merged, gated commit.** Whenever `step` proposes
the push, it names the run's gated tip; that is the `main` the run read back
after the fast-forward; and the gates' evidence is about it. The gated sha
is the merged sha is the pushed sha — the push never names `main`, which
another party may have moved since it was read back. -/
theorem step_push_exact (s : State) (o : Obs) (t : Sha) (h : s.pinned = true)
    (ha : (step s o).2 = .push t) :
    t = (step s o).1.gatedTip ∧ t = (step s o).1.mainAt ∧ (step s o).1.gatedAt t = true := by
  unfold step at ha ⊢
  split at ha
  · simp [internal] at ha
  · exact phaseOf_push_exact _ _ _ _ h ha

/-- **A landing writes only what it owns.** Every write of every action
`step` proposes, from a state satisfying the invariant, is owned in the
state it was proposed from: the run's gate tree, its ledger, `main` and the
remote only to the gated tip on a proven run, and a branch another party
owns only by a compare-and-swap from the tip the run read — which no action
proposes today, since a landing does not write the branch at all. Nothing
is written to a ref or a worktree the run does not own. -/
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

/-- **A landing is a landing of the gated commit.** If the state a step
reaches claims a landing, the `main` it read back after the fast-forward is
exactly the tip the rebase produced and the gates ran on. This is the
statement the two false records reproduced through the first draft would
have failed: both compared two live refs with each other, and neither
carried the gated tip at all. -/
theorem step_landed_exact (s : State) (o : Obs) (h : s.pinned = true)
    (hv : (step s o).1.landedVerdict = true) :
    (step s o).1.landedIsGated = true :=
  pinned_landed _ (step_pinned s o h) hv

/-- The run-level form: whatever observation sequence a run was fed, a
verdict claiming a landing at the end of it implies the same equality. -/
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

/-- Every state a run passes through keeps the invariant. -/
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

/-- The run-level form of the two exactness statements: in every run, from
any state satisfying the invariant, every fast-forward and every push the run
proposes names the gated tip of the state it was proposed from, the push
names the `main` that state read back, and the gates' evidence in that state
is about the named commit. -/
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

/-- The run-level form of the write statement: in every run from a state
satisfying the invariant, every write of every action proposed is owned in
the state it was proposed from. -/
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

/-- A fresh run satisfies the invariant, so the run-level statements above
apply to every run the driver starts. -/
theorem init_pinned (name : String) (m : Mode) (plan : Array GateSpec) (p : Bool) :
    (State.init name m plan p).pinned = true := by
  simp [State.init, State.pinned, State.atOrPastFF, State.preTree, State.rebased,
    State.landedVerdict]

/-- `land push` pushes the last landing's tip, which is its gated tip and
the `main` read, and a sha. -/
theorem pushPlan_exact (lt lg mt t : Sha) (h : pushPlan lt lg mt = .ok t) :
    t = lt ∧ t = lg ∧ t = mt ∧ isSha t = true := by
  unfold pushPlan at h
  repeat' split at h
  all_goals simp_all

/-- `land push` reports `pushed` only for a push that succeeded and a remote
that read back, by its exact name, at the commit pushed. -/
theorem pushVerdict_exact (ok : Bool) (r t : Sha) (h : pushVerdict ok r t = .pushed) :
    ok = true ∧ r = t ∧ isSha r = true := by
  unfold pushVerdict at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.2, hc.1.2⟩
  · simp at h

end Land
