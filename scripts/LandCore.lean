/-
The landing procedure's pure core: a state machine over observations, whose
only outputs are actions. No IO lives here, so every refusal, every
ordering constraint, and the properties that matter — a ref others read is
never touched on an unproven run, and every ref a landing moves is moved to
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
the tip it produced; the gates run in a detached worktree the run makes at
exactly that tip and reads back after every gate; the fast-forward and the
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
with positions dropped (`netDrift`). A run whose rebase drifted restores
the branch and refuses, and `proven` requires the comparison to have held.
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
  /-- The rebase's net content is being compared with the branch's. -/
  | netting
  /-- The rebase changed the net content; the branch is being put back at
  its pre-rebase tip. -/
  | restoring
  /-- The gate tree is being made: a detached worktree at the gated tip,
  which only this run writes. -/
  | treeing
  | gating
  /-- After the gates: is the branch still the commit they ran on? -/
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
  | .netting => "net"
  | .restoring => "restore"
  | .treeing => "gate-tree"
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
  clean, and what is its tip before the rebase. -/
  | branchStatus (ahead behind : Nat) (clean : Bool) (tip : Sha)
  /-- The rebase succeeded and the branch now reads at this tip. This is the
  commit the gates run on and the only commit that may land. -/
  | rebaseOk (tip : Sha)
  /-- The rebase failed. `files` are the unmerged paths, empty when the
  rebase stopped for another reason; the remaining three fields are the
  read-back of the branch worktree *after* the boundary aborted. -/
  | rebaseFailed (files : Array String) (headTip : Sha) (onBranch clean : Bool)
  /-- The two listings the net comparison reads, as `git diff --no-renames
  -U0 --binary` printed them: the branch's own change (from its fork point
  to its pre-rebase tip) and the rebase's (from the base it was replayed
  onto to the rebased tip). Raw text, so the parse is the core's. -/
  | netDiffs (before after : String)
  /-- The branch worktree after the boundary put the branch back at its
  pre-rebase tip: where `HEAD` reads, on the branch or not, clean or not. -/
  | branchRestored (headTip : Sha) (onBranch clean : Bool)
  /-- The gate tree this run made, read back: its `HEAD`, and whether it is
  clean. -/
  | treeReady (head : Sha) (clean : Bool)
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
  | .rebaseOk .. => "rebaseOk"
  | .rebaseFailed .. => "rebaseFailed"
  | .netDiffs .. => "netDiffs"
  | .branchRestored .. => "branchRestored"
  | .treeReady .. => "treeReady"
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
  /-- Rebase the branch onto exactly this commit — `main` as this run read it,
  never the name, so the base the net comparison reads is the base the
  commits were replayed onto. -/
  | rebase (onto : Sha)
  /-- List the two net changes: the branch's, from its fork point with
  `newBase` to `oldTip`, and the rebase's, from `newBase` to `newTip`. -/
  | netDiff (oldTip newBase newTip : Sha)
  /-- Put the branch back at `original`, only if it still reads at `rebased`
  and nothing in its worktree would be lost. -/
  | restoreBranch (rebased original : Sha)
  /-- Make the gate tree: a detached worktree at exactly this commit, which
  only this run writes, removed when the run ends. -/
  | makeTree (tip : Sha)
  /-- Run the gate at this index of the plan, in the gate tree; the name is
  for the log. -/
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
  /-- Push exactly this commit to the remote's `main`, as a fast-forward and
  never a forced update — never the local `main`, which another party may
  have moved since it was read back. -/
  | push (tip : Sha)
  | readRemote
  | halt (v : Verdict) (code : UInt32) (why : String)
  deriving Repr, Inhabited

/-- The two actions that change a ref another worktree or remote reads: the
fast-forward of `main`, and the push. Everything else is a read, a build, or
a write confined to the branch's own worktree (the rebase, and putting it
back), the run's gate tree, or the ledger. -/
def Act.mutates : Act → Bool
  | .fastForward _ => true
  | .push _ => true
  | _ => false

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
  /-- The branch's tip before the rebase, so a failed rebase's read-back has
  a sha to be compared against. -/
  branchTip : Sha
  /-- The commit the rebase produced: what the gates ran on, what the merge
  and the push name, what every later read-back is compared to. -/
  gatedTip : Sha
  /-- Did the rebase keep every file's net change? Set only where the
  comparison came back empty. -/
  netSame : Bool
  /-- The files whose net change the rebase altered, for the refusal. -/
  drift : Array String
  /-- The gate tree's `HEAD`, as read back when it was made. Empty until
  then. -/
  treeAt : Sha
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

/-- The gates' evidence is about `t`: `t` is a sha, the gate tree read back
at `t` when it was made, and it read back at `t`, clean, after every gate
the run recorded. -/
def State.gatedAt (s : State) (t : Sha) : Bool :=
  isSha t && s.treeAt == t && s.gates.all (fun g => g.head == t && g.clean)

/-- Is the run at or past the fast-forward's verification? -/
def State.atOrPastFF (s : State) : Bool :=
  s.stage == .ledgering || s.stage == .pushing || s.stage == .verifyPush

/-- Is the run before any gate could have been recorded? -/
def State.preTree (s : State) : Bool :=
  s.stage == .preMain || s.stage == .preBranch || s.stage == .rebasing
    || s.stage == .netting || s.stage == .restoring || s.stage == .treeing

/-- Is the run past the gate tree's making, and not yet done? -/
def State.pastTree (s : State) : Bool :=
  s.stage == .gating || s.stage == .postGate || s.stage == .preMerge
    || s.stage == .announcing || s.stage == .ffing || s.stage == .verifying
    || s.atOrPastFF

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
claim. No gate is recorded before the gate tree exists; every recorded gate
read the tree back at the gated tip, clean; and from the tree's making
onward the tree read back at the gated tip, a sha. Spelled as one boolean
formula rather than a match over stages: it is proved against every
transition, and a match there multiplies each proof by the number of
stages. -/
def State.pinned (s : State) : Bool :=
  (!(s.atOrPastFF || s.landedVerdict) || s.landedIsGated)
    && (!s.landedVerdict || s.stage == .done)
    && (!s.preTree || s.gates.isEmpty)
    && s.gates.all (fun g => g.head == s.gatedTip && g.clean)
    && (!s.pastTree || (isSha s.gatedTip && s.treeAt == s.gatedTip))

def State.init (name : String) (mode : Mode) (plan : Array GateSpec)
    (wantPush : Bool) : State :=
  { name, mode, stage := .preMain, gates := #[], skipped := #[], plan, gateIdx := 0,
    wantPush, prevMainTip := "", branchTip := "", gatedTip := "", netSame := false,
    drift := #[], treeAt := "", mainAt := "", verdict := none }

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

/-- The preconditions, the rebase, the net comparison and the gate tree:
every stage before a gate runs. Split out from `step` so a theorem about the
merge half unfolds none of it — the whole machine in one match walled every
proof off behind a heartbeat limit, and a limit raised is not a
factorization. -/
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
    else ({ s with stage := .rebasing, branchTip := tip }, .rebase s.prevMainTip)
  | .rebasing, .rebaseOk tip =>
    if !isSha tip then internal s "the rebased tip did not read back as a sha"
    else ({ s with stage := .netting, gatedTip := tip }, .netDiff s.branchTip s.prevMainTip tip)
  | .rebasing, .rebaseFailed files headTip onBranch clean =>
    -- The boundary has already aborted; this is the read-back of what it
    -- left behind, and the only thing that may be reported.
    if !(onBranch && clean && headTip == s.branchTip && isSha headTip) then
      internal s s!"agent/{s.name} was left mid-rebase"
    else if !files.isEmpty then
      refuse s s!"rebase conflict: {String.intercalate " " files.toList}"
    else refuse s "the rebase failed and was aborted"
  | .netting, .netDiffs before after =>
    -- Every file counts, a union-merged one first among them: git reports
    -- no conflict for a hunk the union driver joined, and that is exactly
    -- where a deleted line came back. A reported conflict never reaches
    -- here — it stopped the rebase above. No `let` for the drift: a bound
    -- conditional is one `split` cannot see.
    if (netDrift (netOf before) (netOf after)).isEmpty then
      ({ s with stage := .treeing, netSame := true }, .makeTree s.gatedTip)
    else
      ({ s with stage := .restoring, drift := netDrift (netOf before) (netOf after) },
       .restoreBranch s.gatedTip s.branchTip)
  | .restoring, .branchRestored headTip onBranch clean =>
    if !(onBranch && clean && headTip == s.branchTip && isSha headTip) then
      internal s s!"agent/{s.name} was left at the rebased tip"
    else
      refuse s s!"the rebase changed the net content of: {String.intercalate " " s.drift.toList}"
  | .treeing, .treeReady head clean =>
    -- A tree this run just made, not at the tip it was made from, or not
    -- clean, is a fault in the boundary or the repository, not the branch's.
    -- Three tests rather than one conjunction, so each branch carries its
    -- own fact.
    if !isSha head then internal s "the gate tree's HEAD did not read back as a sha"
    else if head != s.gatedTip then internal s "the gate tree did not read back at the gated tip"
    else if !clean then internal s "the gate tree was dirty when it was made"
    else nextGate { s with stage := .gating, treeAt := head }
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
    -- The gates ran in the run's own tree, so this is no longer evidence
    -- about what they saw; it is whether the author still asks for this
    -- commit. A branch that moved on refuses rather than landing a commit
    -- its owner has since replaced.
    if tip != s.gatedTip then refuse s s!"agent/{s.name} moved during the gates"
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
  | .preMain | .preBranch | .rebasing | .netting | .restoring | .treeing => stepPre
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

-- ## The theorems
--
-- Three properties, and the ways each could have held vacuously. Each is
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
    simp_all [Act.mutates, refuse, internal, gateFailed, landedNotPushed, succeed,
      State.proven, State.gatesOk]

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
      State.gatedAt, State.pastTree, State.atOrPastFF, State.preTree, State.landedVerdict,
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
      State.gatedAt, State.pastTree, State.atOrPastFF, State.preTree, State.landedVerdict,
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
      State.preTree, State.pastTree, State.landedVerdict, State.landedIsGated]

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
      State.preTree, State.pastTree, State.landedVerdict, State.landedIsGated]

private theorem stepMerge_pinned (s : State) (o : Obs) :
    s.pinned = true → (stepMerge s o).1.pinned = true := by
  intro h
  unfold stepMerge
  repeat' split
  all_goals
    simp_all +decide [refuse, internal, gateFailed, landedNotPushed, succeed, State.pinned,
      State.atOrPastFF, State.preTree, State.pastTree, State.landedVerdict,
      State.landedIsGated]

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
  · have hn := stepPre_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn
  · have hn := stepGate_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn
  · exact stepMerge_ff_covers s o t h

private theorem phaseOf_ff_exact (st : Stage) (s : State) (o : Obs) (t : Sha)
    (hp : s.pinned = true) :
    (phaseOf st s o).2 = .fastForward t →
      t = (phaseOf st s o).1.gatedTip ∧ (phaseOf st s o).1.gatedAt t = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn
  · have hn := stepGate_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn
  · exact stepMerge_ff_exact s o t hp h

private theorem phaseOf_push_exact (st : Stage) (s : State) (o : Obs) (t : Sha)
    (hp : s.pinned = true) :
    (phaseOf st s o).2 = .push t →
      t = (phaseOf st s o).1.gatedTip ∧ t = (phaseOf st s o).1.mainAt
        ∧ (phaseOf st s o).1.gatedAt t = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e] at h ⊢
  · have hn := stepPre_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn
  · have hn := stepGate_no_mutate s o; rw [h] at hn; simp [Act.mutates] at hn
  · exact stepMerge_push_exact s o t hp h

private theorem phaseOf_pinned (st : Stage) (s : State) (o : Obs) :
    s.pinned = true → (phaseOf st s o).1.pinned = true := by
  intro h
  rcases phaseOf_cases st with e | e | e <;> rw [e]
  · exact stepPre_pinned s o h
  · exact stepGate_pinned s o h
  · exact stepMerge_pinned s o h

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
  · simp_all +decide [internal, State.pinned, State.atOrPastFF, State.preTree, State.pastTree,
      State.landedVerdict, State.landedIsGated]
  · exact phaseOf_pinned _ _ _ h

/-- A state satisfying the invariant, and claiming a landing, read `main`
back at its gated tip. -/
private theorem pinned_landed (s : State) (h : s.pinned = true)
    (hv : s.landedVerdict = true) : s.landedIsGated = true := by
  unfold State.pinned at h
  simp only [hv, Bool.or_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- **The merge names the gated commit.** Whenever `step` proposes the
fast-forward, it names the run's gated tip, and the gates' evidence is about
that commit: the gate tree read back at it when it was made and after every
gate the run recorded, clean each time. -/
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

/-- A fresh run satisfies the invariant, so the run-level statements above
apply to every run the driver starts. -/
theorem init_pinned (name : String) (m : Mode) (plan : Array GateSpec) (p : Bool) :
    (State.init name m plan p).pinned = true := by
  simp [State.init, State.pinned, State.atOrPastFF, State.preTree, State.pastTree,
    State.landedVerdict]

end Land
