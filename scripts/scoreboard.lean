/-
The scoreboard: one line per goal, and a queue computed from the deficits.

  scoreboard                one porcelain line per tier; exit 1 on any regression
  scoreboard --check        the same, quietly — the landing gate
  scoreboard --check --base <rev>
                            the landing gate, plus every committed baseline held to
                            the one committed at <rev>: a fall or a vanish since
                            <rev> needs a line written since <rev>
  scoreboard --queue        ranked deficits across every tier
  scoreboard --bench        the speed report, never gated
  scoreboard --selftest     the format, the ratchet, and the malformations

A tier is discovered by convention: its name is the basename of
`tests/scoreboard/<tier>.tsv` and the root of `scripts/<tier>.lean`, and its
`--check` is `lake env lean --run scripts/<tier>.lean --check`.

What the aggregate reads is that `--check`'s **exit status** — the one
contract PLAN's spec defines, and so the only one every tier's writer was
told about. A tier may also print the porcelain line (`tierLine`), which
adds counts; it can never turn a non-zero exit into a pass. A tier that
exits 0 silently is `ok`.

The gated path is hermetic: every tier's `--check` reads committed
references and in-repo data only. `--bench` is the one mode that shells out
to another engine, and it gates nothing. `--base` reads git's copy of the
committed files at `<rev>` and nothing else.
-/
import scripts.Board

open Scoreboard


structure TierResult where
  tier : String
  items : Nat
  regressed : Nat
  improved : Nat
  result : String
  detail : String
deriving Inhabited

def natField (line key : String) : Nat :=
  (((field line key).bind (·.toNat?))).getD 0

/-- A tier's check in flight: its process, and the scratch directory holding
its two output files, removed once the result is read. -/
structure Spawn where
  child : IO.Process.Child { }
  dir : System.FilePath
  out : String
  err : String

/-- Run one tier's own `--check` and read its porcelain line back. The tier
is the authority on its own numbers; this reads the line it printed, never a
summary of it.

Each check runs in its own process writing to its own files rather than to a
pipe, so the aggregate can have every tier in flight at once without a
reader deadlocking on a full pipe — the tiers are independent, and a landing
gate that took one interpreter startup per tier in series took 17 s where
this takes one. Paths reach `sh` as positional parameters, never
interpolated into the command: a tier's name is a file basename, which is
not this tool's to trust. -/
def spawnTier (tier : String) : IO (Option Spawn) := do
  let hasTsv ← System.FilePath.pathExists (tsvPath tier)
  let hasScript ← System.FilePath.pathExists (scriptPath tier)
  if !hasTsv || !hasScript then return none
  let dir ← IO.FS.createTempDir
  let outPath := (dir / "out").toString
  let errPath := (dir / "err").toString
  let child ← IO.Process.spawn
    { cmd := "sh"
      args := #["-c", "exec lake env lean --run \"$1\" --check > \"$2\" 2> \"$3\"",
                "sh", scriptPath tier, outPath, errPath] }
  return some { child, dir, out := outPath, err := errPath }

def collectTier (tier : String) (spawned : Option Spawn) : IO TierResult := do
  match spawned with
  | none =>
    let hasTsv ← System.FilePath.pathExists (tsvPath tier)
    let hasScript ← System.FilePath.pathExists (scriptPath tier)
    let why :=
      if !hasTsv && !hasScript then "neither the baseline nor the producer exists"
      else if !hasTsv then s!"{scriptPath tier} exists but {tsvPath tier} does not"
      else s!"{tsvPath tier} exists but {scriptPath tier} does not"
    -- Absence is a pass only for a tier that has not landed yet, and only
    -- while its name is on `pendingTiers`. Anything else missing a half is
    -- a fault: deleting a landed tier used to leave the gate green.
    if pendingTiers.contains tier && !hasTsv && !hasScript then
      return { tier, items := 0, regressed := 0, improved := 0
               result := "missing", detail := s!"{why} (declared pending)" }
    return { tier, items := 0, regressed := 0, improved := 0, result := "fault", detail := why }
  | some s =>
    let code ← s.child.wait
    let stdout ← readFileOr s.out
    let stderr ← readFileOr s.err
    IO.FS.removeDirAll s.dir
    let line := ((stdout.splitOn "\n").find? (·.startsWith "scoreboard: tier=")).getD ""
    -- The spec's contract is the exit status of `--check`; a porcelain line,
    -- when the tier prints one, adds counts and can never turn a non-zero
    -- exit into a pass.
    let said := (field line "result").getD ""
    let result :=
      if code != 0 then
        (if said == "regressed" || said == "fault" || said == "stale" then said else "fail")
      else if line.isEmpty then "ok"
      else if said.isEmpty then "fault" else said
    let detail := if code != 0 && line.isEmpty
      then s!"exit {code}; {stderr.trimAscii.toString}" else stderr.trimAscii.toString
    return { tier
             items := natField line "items"
             regressed := natField line "regressed"
             improved := natField line "improved"
             result
             detail }

/-- What the aggregate can say about a committed baseline before running its
producer: the states no producer's answer could make pass, read by the
aggregate itself so they hold for every tier and not only for the tiers
built on `tierMain`. An emptied or rowless baseline has no floor, and an
emptied sibling baseline used to pass whenever its producer exited 0. A
tombstone (`# retired-tier:`) is a retired tier: it passes as `retired`
while its producer is gone, and is a fault while one still measures it.
`none` means run the producer. -/
def precheck (text : String) (hasScript : Bool) : Option (String × String) :=
  if text.trimAscii.isEmpty then
    some ("fault", "the baseline is empty, so there is no floor to check against; \
regenerate it with its producer")
  else match parse text with
    | .error e => some ("fault", s!"the baseline does not read as the scoreboard format: {e}")
    | .ok t =>
      match t.tierRetired with
      | some why =>
        if hasScript then
          some ("fault", s!"the tier is retired ({why}), but its producer still measures it; \
delete the producer")
        else some ("retired", s!"retired: {why}")
      | none =>
        if t.rows.isEmpty then
          some ("fault", "the baseline holds no rows, so there is no floor to check against")
        else none

/-- A result the aggregate passes: measured and clean, declared and not yet
landed, or retired by its tombstone. -/
def passing (result : String) : Bool :=
  result == "ok" || result == "missing" || result == "retired"

/-- Build what the tiers import, once, before any of them runs. `lake env
lean --run` builds nothing, so without this every tier measures whatever the
last build left. A failed build is a `fault` for every tier: the answer to
"is the debt going down" is unknown when the tree does not compile. -/
def buildImports : IO (Option String) := do
  let targets ← buildTargets
  if targets.isEmpty then return none
  let out ← IO.Process.output { cmd := "lake", args := #["build"] ++ targets }
  if out.exitCode == 0 then return none
  let log := (out.stdout ++ out.stderr).trimAscii.toString
  let firstErr := ((log.splitOn "\n").find? (containsSub · "error")).getD
    s!"lake build {String.intercalate " " targets.toList} exited {out.exitCode}"
  return some firstErr.trimAscii.toString

/-- Every tier's result line, and under it the reasons of any tier that does
not pass — under `--check` too, because the landing agent reads this output
and a `fault` with its reason withheld is a fault nobody can act on. `quiet`
withholds only the notes of passing tiers. -/
def aggregate (quiet : Bool) : IO UInt32 := do
  let tiers ← discover
  match ← buildImports with
  | some err =>
    IO.eprintln s!"scoreboard: the tiers' imports do not build, so no tier can be \
measured: {err}"
    for t in tiers do
      IO.println (tierLine t 0 0 0 "fault")
    return 1
  | none => pure ()
  let mut planned : Array (String × Option TierResult × Option Spawn) := #[]
  for t in tiers do
    let decided ← do
      if ← System.FilePath.pathExists (tsvPath t) then
        let text ← readFileOr (tsvPath t)
        let hasScript ← System.FilePath.pathExists (scriptPath t)
        pure ((precheck text hasScript).map fun (result, detail) =>
          { tier := t, items := 0, regressed := 0, improved := 0, result, detail : TierResult })
      else pure none
    match decided with
    | some r => planned := planned.push (t, some r, none)
    | none => planned := planned.push (t, none, ← spawnTier t)
  let mut bad := 0
  for (t, decided, s) in planned do
    let r ← match decided with
      | some r => pure r
      | none => collectTier t s
    IO.println (tierLine r.tier r.items r.regressed r.improved r.result)
    if r.result != "ok" && !r.detail.isEmpty && (!quiet || !passing r.result) then
      for l in r.detail.splitOn "\n" do
        let l := l.trimAscii.toString
        let l := if l.startsWith "scoreboard: " then (l.drop "scoreboard: ".length).toString else l
        if !l.isEmpty then IO.println s!"scoreboard:   {l}"
    if !passing r.result then bad := bad + 1
  return (if bad == 0 then 0 else 1)

-- ## The base check

def git (args : Array String) : IO (Option String) := do
  try
    let o ← IO.Process.output { cmd := "git", args }
    return (if o.exitCode == 0 then some o.stdout else none)
  catch _ => return none

/-- `--check --base <rev>`: every baseline committed at `<rev>` held to the
tree's copy (`judgeBase`). The ratchet compares committed files with a
measurement, so it cannot see a floor edited down by hand, or a baseline
deleted and regenerated from nothing: both leave file and tree agreeing.
The base can see them. A rev that names no commit fails closed, and so does
a tree that is not a git repository. -/
def baseCheck (rev : String) : IO UInt32 := do
  let some sha := (← git #["rev-parse", "--verify", "--quiet", rev ++ "^{commit}"]).map
      (·.trimAscii.toString)
    | IO.eprintln s!"scoreboard: --base {rev} names no commit here, so no baseline can be \
held to it; failing closed"
      IO.println s!"scoreboard: base={rev} result=fault"
      return 1
  let short := (sha.take 12).toString
  let some listing ← git #["ls-tree", "--name-only", sha, "tests/scoreboard/"]
    | IO.eprintln s!"scoreboard: cannot list tests/scoreboard at {short}; failing closed"
      IO.println s!"scoreboard: base={short} result=fault"
      return 1
  let files := ((listing.splitOn "\n").map (·.trimAscii.toString)).filter (·.endsWith ".tsv")
  let mut bad := 0
  for p in files do
    let tier := ((System.FilePath.mk p).fileStem).getD p
    let baseText := (← git #["show", s!"{sha}:{p}"]).getD ""
    let tipExists ← System.FilePath.pathExists p
    let (result, reasons) := judgeBase baseText tipExists (← readFileOr p)
    IO.println s!"scoreboard: base={short} tier={tier} result={result}"
    for r in reasons do IO.println s!"scoreboard:   {r}"
    if result != "ok" then bad := bad + 1
  return (if bad == 0 then 0 else 1)

-- ## The queue

/-- Grouped deficits, not a single ranking. Obligations whose blocker names
no other open obligation come first — they are the ones a proof can start on
today — and among those, the ones whose own name appears in the most other
blockers, because discharging one of those releases the most. Then the
blocker ranking a sibling commits, then every tier's worst items, ranked by
the deficit its own encoding defines.

**The order between groups is policy, not a ranking**, and the label says
so. Deficits in different tiers are in different units — a compat row is
minutes, a `_covers` over two private loops is weeks — so a cross-tier order
needs a cost model this has no data for. Reading the head as "the next thing
to do" would take a proof obligation first while any of the ready ones
remains, which is a decision and not a measurement.

What a real ranking still needs: the blocker graph as data rather than as
prose (a `blocked-by:` field naming obligations, so "names no other open
obligation" stops being a substring search over English); the per-item cost
of a deficit; and the count of documents each deficit holds back, which the
parity ladder's fixtures-held-back number would give. With those the order
becomes value over cost; with only these, it is readiness over size, inside
each group. -/
def queue (limit : Nat) : IO UInt32 := do
  let mut lines : Array String := #[]
  let (obs, malformed) ← obligations
  if !malformed.isEmpty then
    for m in malformed do
      lines := lines.push s!"queue: malformed owed record — {m}"
  let unblocks := fun (o : Ob) =>
    (obs.filter fun p => p.name != o.name && containsSub p.blocker o.name).size
  let readyObs := (ready obs).qsort fun a b =>
    if unblocks a == unblocks b then a.name < b.name else unblocks a > unblocks b
  lines := lines.push s!"queue: group 1 of 3 — obligations a proof can start on today \
({readyObs.size} of {obs.size} open); the order between groups is policy, not a ranking"
  for o in readyObs do
    let b := o.blocker
    let short := if b.length > 90 then ((b.take 90).toString) ++ "…" else b
    -- The owner file: "whose owner files are free" needs the file, not only
    -- the module name.
    lines := lines.push s!"queue: obligation {o.name} owner={o.owner} file={o.file} \
blocked-by-open=0 unblocks={unblocks o} blocker={short}"
  -- The blocker ranking a sibling commits: constructs nothing in the engine
  -- answers, ranked by the documents they alone hold back. Read when
  -- present, because the ranking data belongs to whoever measured it.
  let blockers ← readFileOr "tests/coverage/blockers.tsv"
  if blockers.isEmpty then
    lines := lines.push "queue: group 2 of 3 — no tests/coverage/blockers.tsv, so no \
construct ranking (the coverage tier writes it)"
  else
    let rows := (blockers.splitOn "\n").filterMap fun l =>
      if l.startsWith "#" || l.trimAscii.isEmpty then none
      else match l.splitOn "\t" with
        | [construct, owner, sole, share, docs] =>
          if construct == "construct" then none
          else some (construct, owner, sole, share, docs)
        | _ => none
    lines := lines.push s!"queue: group 2 of 3 — constructs nothing answers, by the \
documents they alone block ({rows.length} ranked)"
    for (construct, owner, sole, share, docs) in rows.take 5 do
      lines := lines.push s!"queue: blocker {construct} owner={owner} sole={sole} \
share={share} docs={docs}"
  lines := lines.push "queue: group 3 of 3 — each tier's worst items, in its own \
units; not comparable across tiers"
  for t in ← discover do
    let text ← readFileOr (tsvPath t)
    if text.isEmpty then continue
    match parse text with
    | .error e => lines := lines.push s!"queue: tier {t} unreadable: {e}"
    | .ok tsv =>
      -- Faults about the row set, reported here rather than only at
      -- `--check` time: a sibling's tier whose rows are not sorted parses
      -- and gates fine today (the aggregate reads its exit status), and the
      -- fault only bites the day it ports onto `tierMain`. Saying so now is
      -- cheaper than saying so then.
      for f in validate tsv do
        lines := lines.push s!"queue: tier {t} baseline fault: {f}"
      if tsv.encoding.isNone then
        lines := lines.push s!"queue: tier {t} not ranked: no `# encoding:` line"
      let ds := deficits tsv
      for i in [0:ds.size] do
        if i < 3 then
          let (item, d) := ds[i]!
          lines := lines.push s!"queue: {t} deficit={d} item={item}"
  let shown := if lines.size < limit then lines.size else limit
  for i in [0:shown] do
    IO.println lines[i]!
  IO.println s!"queue: {lines.size} lines, {shown} shown — grouped, not one ranking"
  return 0

-- ## The speed report

/-- The declared bench tolerance. Data, not a gate: `--bench` runs another
engine, so it can never be part of a hermetic check, and the numbers move
with the host. Every field is stated so a reader can say what would count as
a regression, which is the part a report usually leaves out. -/
structure BenchTolerance where
  /-- Runs per document. Odd, so the median is a measured value. -/
  samples : Nat
  /-- Runs dropped before measuring: the first is a cold page cache. -/
  discard : Nat
  /-- Percent a document's median may rise over its committed value. -/
  slackPercent : Nat
  /-- Medians, not means: one slow run on a busy host moves a mean. -/
  statistic : String
  /-- Which column the tolerance would gate, if it gated. -/
  gates : String
  /-- Which column stays a record whatever it does. -/
  records : String
deriving Inhabited

def benchTolerance : BenchTolerance :=
  { samples := 9, discard := 1, slackPercent := 15, statistic := "median"
    gates := "leantex", records := "lualatex" }

/-- The bench numbers beside the last ones PLAN.md recorded. A report: it
runs another engine, so it can never be part of a hermetic gate, and no
tolerance is enforced here. The tolerance is declared as a value
(`benchTolerance`) rather than as prose, so the day it does gate, the number
it gates at is the one written down and not one someone retypes. -/
def benchReport : IO UInt32 := do
  let plan ← readFileOr "PLAN.md"
  let recorded := (plan.splitOn "\n").filter (fun l =>
    containsSub l "scripts/bench.lean" && containsSub l "median")
  IO.println "scoreboard: bench is a report, never a gate (it runs lualatex)."
  match recorded.reverse.head? with
  | some l => IO.println s!"scoreboard: last recorded — {l.trimAscii.toString}"
  | none => IO.println "scoreboard: PLAN.md records no bench median yet"
  let t := benchTolerance
  IO.println s!"scoreboard: declared tolerance, not enforced: the {t.statistic} of \
{t.samples} runs per document (first {t.discard} discarded, cold page cache) may rise \
{t.slackPercent}% over its committed value. It would gate the {t.gates} column only; \
the {t.records} column is recorded and never compared. Noise control: pin the sample \
count, compare {t.statistic}s rather than means, and take the whole corpus in one \
batch so a busy host moves every row together — a single row moving is then a signal, \
and all rows moving is the host."
  let out ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "--run", "scripts/bench.lean"] }
  IO.print out.stdout
  if out.exitCode != 0 then IO.eprint out.stderr
  return out.exitCode

-- ## Selftest

def fixture (name : String) : String := s!"tests/scoreboard/selftest/{name}.tsv"

/-- Hand-written committed baselines, one per malformation `validate` must
name. The fixture *is* the failing input: each case names the fault it must
provoke, and the clean fixture must provoke none. -/
def malformations : List (String × String) :=
  [("unsorted", "out of order"),
   ("duplicate", "duplicate item"),
   ("noninteger", "is not an integer"),
   ("threefields", "tab-separated fields"),
   ("retired-no-reason", "gives no reason"),
   ("lowered-no-reason", "gives no reason"),
   ("lowered-malformed", "malformed lowering"),
   ("lowered-unheld", "but the committed floor is"),
   ("lowered-nofall", "names no fall"),
   ("lowered-unbaselined", "names no baselined item"),
   ("tier-retired-rows", "a retired tier still holds rows"),
   ("no-rows", "no rows")]

/-- Committed baselines `validate` must accept. Each is a state the tool
writes, or asks a human to write, on the way through a fall, a vanish, or a
tier's retirement — so refusing any of them is a wedge: a remedy the tool
prints that the tool then rejects. -/
def wellFormed : List String :=
  ["clean", "retired", "retired-pending", "lowered", "lowered-applied",
   "lowered-reauth", "lowered-second", "chain", "chain-gap", "tier-retired"]

/-- The base check's cases: the file committed at the base, the tree's file,
and the verdict. Each laundering case is a way a floor moved with no line
written for it since the base; each `ok` case is a move a line pays for. -/
def baseCases : List (String × String × String) :=
  [("clean", "clean", "ok"),
   ("clean", "raised", "ok"),
   ("clean", "dropped", "laundered"),
   ("clean", "lowered-applied", "ok"),
   ("clean", "chain", "ok"),
   ("clean", "chain-gap", "laundered"),
   ("lowered-reauth", "reauth-tip", "laundered"),
   ("clean", "disappeared", "laundered"),
   ("clean", "retired", "ok"),
   ("clean", "tier-retired", "ok"),
   ("clean", "added", "laundered"),
   ("clean", "encoding-changed", "laundered")]

def readFixture (name : String) : IO (Except String Tsv) := do
  let text ← readFileOr (fixture name)
  if text.isEmpty then return .error s!"fixture {name} is missing"
  return parse text

/-- `--base <rev>`: `none` when absent, `some none` when the revision is
missing. -/
def baseArg (args : List String) : Option (Option String) :=
  match args.dropWhile (· != "--base") with
  | [] => none
  | [_] => some none
  | _ :: rev :: _ => some (some rev)

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let no (why : String) (ok : Bool) : IO Unit := do
    unless ok do fails.modify (why :: ·)
  let joined (xs : Array String) : String := String.intercalate "; " xs.toList
  let load (name : String) : IO Tsv := do
    match ← readFixture name with
    | .ok t => pure t
    | .error e =>
      no s!"fixture {name} does not read: {e}" false
      pure default
  let withAlpha (t : Tsv) (v : Int) : Tsv :=
    { t with rows := t.rows.map fun r => if r.item == "alpha" then { r with value := v } else r }

  -- A clean baseline parses, validates, and ratchets against itself as ok.
  let base ← load "clean"
  no s!"clean fixture has faults: {joined (validate base)}" (validate base).isEmpty
  no "clean fixture has three rows" (base.rows.size == 3)
  no "clean fixture declares the headroom encoding" (base.encoding == some (.headroom 1000))
  no "a baseline against itself neither loses nor gains" (ratchet base base).changes.isEmpty

  -- Every malformation of a committed file fires its own fault, and none of
  -- them is the catch-all: the message must name the kind.
  for (name, want) in malformations do
    let got ← readFixture name
    let msgs : Array String := match got with
      | .error e => #[e]
      | .ok t => validate t
    no s!"malformation {name}: nothing fired" (!msgs.isEmpty)
    no s!"malformation {name}: fired {joined msgs}, wanted '{want}'"
      (msgs.any (containsSub · want))
  -- ... and every state the tool writes, or asks a human to write, reads.
  for name in wellFormed do
    let t ← load name
    no s!"well-formed {name}: refused as {joined (validate t)}" (validate t).isEmpty

  -- A fresh measurement is judged against the committed file it meets: a
  -- retired item that is still measured is the fault, never the committed
  -- file that holds a retirement beside its row.
  let live ← load "retired-and-live"
  no s!"fresh: a retired item still measured is a fault ({joined (validateFresh live.rows (some live))})"
    ((validateFresh live.rows (some live)).any (containsSub · "retired and also measured"))
  no "fresh: the same measurement without the retired item is clean"
    (validateFresh (live.rows.filter (·.item != "alpha")) (some live)).isEmpty
  no "fresh: an empty measurement is a fault" (validateFresh #[] none == #["no rows"])
  no "fresh: a duplicate item is a fault"
    ((validateFresh #[{ item := "a", value := 1 }, { item := "a", value := 2 }] none).any
      (containsSub · "duplicate item"))

  -- The spec's format, which a tier written without this library also
  -- speaks: no encoding line is gated and unranked, and an item may hold
  -- spaces because the row is split on its tab.
  match ← readFixture "spec-no-encoding" with
  | .error e => no s!"spec format: a baseline with no encoding line is refused: {e}" false
  | .ok t =>
    no "spec format: no encoding line reads as unranked" (t.encoding.isNone && (deficits t).isEmpty)
  match ← readFixture "spec-spaced-item" with
  | .error e => no s!"spec format: an item holding a space is refused: {e}" false
  | .ok t =>
    no "spec format: the spaced item reads whole" (t.rows.any (·.item == "alpha bravo"))

  -- The four ratchet verdicts, each against the clean baseline, read off
  -- the structured changes rather than a rendered sentence.
  let verdicts : List (String × Bool × Bool) :=
    [("dropped", true, false),
     ("disappeared", true, false),
     -- `added` under a headroom cap: an unseen item below the cap is debt
     -- arriving under a new name, so it is a fall.
     ("added", true, false),
     ("raised", false, true)]
  for (name, wantLoss, wantGain) in verdicts do
    let now ← load name
    let d := ratchet base now
    no s!"ratchet {name}: loss expected {wantLoss}, got {d.losses.size} \
({joined (d.losses.map (·.describe))})" (d.losses.isEmpty == !wantLoss)
    no s!"ratchet {name}: gain expected {wantGain}, got {d.gains.size}"
      (d.gains.isEmpty == !wantGain)
    -- The tight rule: every one of the four fails `--check`, a rise
    -- included. Before this, a rise passed and left the floor stale.
    no s!"ratchet {name}: --check must fail on any change" (!d.checkPasses)
  no "ratchet: an unchanged measurement is the only state --check passes"
    (ratchet base base).checkPasses

  -- Retirement through the tool. The request is the row beside its line, the
  -- one committed state the ratchet's retirement arm reads; regenerating
  -- drops the row and leaves the line as the record. Before this the request
  -- was malformed, so the refusal's printed remedy wedged its tier.
  let pend ← load "retired-pending"
  let gone ← load "disappeared"
  let record ← load "retired"
  no "retirement: the request is the row beside its line" (pend.pendingRetirements == #["alpha"])
  no "retirement: the requested vanish is no loss" (unauthorised pend gone).isEmpty
  no "retirement: nothing is left for regeneration to refuse" (ratchet pend gone).changes.isEmpty
  no "retirement: without the line the same vanish is a loss" (!(unauthorised base gone).isEmpty)
  no "retirement: the record is the line without its row" record.pendingRetirements.isEmpty
  no "retirement: the record against the measurement it describes is clean"
    (ratchet record gone).changes.isEmpty
  no "retirement: no lowering pays for a vanish"
    (!({ item := "alpha", old := 998, new := 0, why := "w" } : Lowered).authorises
      (.vanished "alpha" 998))

  -- A headroom item the baseline never held enters at the cap, so new debt
  -- under a new name is a fall rather than an improvement — and a request
  -- from the cap is how a human writes it.
  let added ← load "added"
  let d := ratchet base added
  no s!"headroom: an unseen item below the cap is a fall, not an entry \
({joined (d.changes.map (·.describe))})" (d.losses.size == 1 && d.gains.isEmpty)
  let atCap : Tsv := { added with
    rows := added.rows.map fun r => if (base.find? r.item).isNone then { r with value := 1000 } else r }
  let d2 := ratchet base atCap
  no "headroom: an unseen item at the cap is neither a fall nor a rise"
    (d2.losses.isEmpty && d2.gains.size == 1)
  no "raw: an unseen item still enters at its measured value"
    ((ratchet { base with encoding := some .raw } added).losses.isEmpty)
  let fromCap : Tsv := { base with lowered := #[{ item := "delta", old := 1000, new := 3, why := "w" }] }
  no s!"headroom: a request from the cap reads ({joined (validate fromCap)})" (validate fromCap).isEmpty
  no "headroom: a request from the cap authorises the new item's fall"
    (unauthorised fromCap added).isEmpty

  -- A lowering request authorises exactly one fall, once.
  let req ← load "lowered"
  let fell ← load "lowered-fresh"
  let applied ← load "lowered-applied"
  no "lowering: the fixture holds one request" (req.pendingLowerings.size == 1)
  let d := ratchet req fell
  no "lowering: the fall is still a loss the ratchet reports" (d.losses.size == 1)
  no "lowering: the request authorises it" (unauthorised req fell).isEmpty
  no "lowering: the request is spent on it" (unusedLowerings req fell).isEmpty
  no "lowering: without the request nothing authorises it" (!(unauthorised base fell).isEmpty)
  no "lowering: a request with no fall to answer is refused, not carried"
    ((unusedLowerings req base).size == 1)
  no "lowering: the file regeneration writes holds it as a record"
    (applied.lowered.size == 1 && applied.pendingLowerings.isEmpty)
  no "lowering: the file regeneration writes is the measurement" (ratchet applied fell).changes.isEmpty
  -- The re-authorization the parity review reproduced: a line carried
  -- forward must never pay for a second fall, even between the same values.
  no "record: it authorises no further fall" (!(unauthorised applied (withAlpha fell 994)).isEmpty)
  let reauth ← load "lowered-reauth"
  no "record: carried past a recovery, it does not authorise the same fall again"
    (!(unauthorised reauth fell).isEmpty)
  -- The second fall of one item — the second staging under one owner: the
  -- first record is history and is not held to today's floor, and the new
  -- request is checked against the floor the first one left.
  let second ← load "lowered-second"
  no "second fall: its request authorises it" (unauthorised second (withAlpha fell 990)).isEmpty
  match d.losses[0]? with
  | none => no "lowering: no loss to authorise" false
  | some c =>
    let w : Lowered := req.pendingLowerings[0]!
    no "lowering: the request authorises exactly this fall" (w.authorises c)
    no "lowering: a line naming other values does not"
      (!({ w with old := 998, new := 996 } : Lowered).authorises c)
    no "lowering: a line naming another item does not" (!({ w with item := "bravo" } : Lowered).authorises c)
    no "lowering: the same line as a record does not" (!({ w with state := .applied } : Lowered).authorises c)
    no "lowering: a request reads back as written"
      ((parseLowered w.render).bind (·.toOption) == some w)
    no "lowering: a record reads back as written"
      ((parseLowered { w with state := .applied }.render).bind (·.toOption) ==
        some { w with state := .applied })

  -- The base check: a floor moved since the base needs a line written since
  -- the base. Each laundering case passed `--check` before this existed.
  for (b, t, want) in baseCases do
    let (got, why) := judgeBase (← readFileOr (fixture b)) true (← readFileOr (fixture t))
    no s!"base {b} → {t}: {got} ({joined why}), wanted {want}" (got == want)
  let cleanText ← readFileOr (fixture "clean")
  no "base: a baseline gone from the tree is a fault" ((judgeBase cleanText false "").1 == "fault")
  no "base: an emptied baseline launders every row" ((judgeBase cleanText true "").1 == "laundered")
  no "base: an unreadable base is a fault" ((judgeBase "alpha\tnine\n" true cleanText).1 == "fault")
  let l (o n : Int) : Lowered := { item := "alpha", old := o, new := n, why := "w", state := .applied }
  no "reach: with no lines the floor holds" (reach [] 998 == 998)
  no "reach: two records compose, in either order"
    (reach [l 998 995, l 995 990] 998 == 990 && reach [l 995 990, l 998 995] 998 == 990)
  no "reach: a rise between two records needs no line" (reach [l 998 995, l 999 990] 998 == 990)
  no "reach: a fall between two records that no line covers is not reached"
    (reach [l 998 995, l 994 990] 998 == 995)
  no "reach: a record below the floor is not usable" (reach [l 991 990] 998 == 998)

  -- What the aggregate decides before any producer runs.
  no "aggregate: an empty baseline is a fault" ((precheck "" true).map (·.1) == some "fault")
  no "aggregate: a rowless baseline is a fault"
    ((precheck "# encoding: raw\n" true).map (·.1) == some "fault")
  no "aggregate: an unreadable baseline is a fault"
    ((precheck "alpha\tnine\n" true).map (·.1) == some "fault")
  let tomb ← readFileOr (fixture "tier-retired")
  no "aggregate: a tombstone with no producer is retired" ((precheck tomb false).map (·.1) == some "retired")
  no "aggregate: a tombstone with a producer is a fault" ((precheck tomb true).map (·.1) == some "fault")
  no "aggregate: a baseline with rows goes to its producer" (precheck cleanText true).isNone
  no "aggregate: retired passes and stale does not"
    (passing "retired" && !passing "stale" && !passing "fail" && !passing "laundered")
  no "--base: read off the arguments"
    (baseArg ["--check", "--base", "abc"] == some (some "abc") && baseArg ["--check"] == none &&
      baseArg ["--base"] == some none)

  -- The porcelain line the aggregate reads back is the one a tier prints.
  let line := tierLine "zz" 7 1 2 "regressed"
  no "porcelain: tier reads back" ((field line "tier") == some "zz")
  no "porcelain: items reads back" (natField line "items" == 7)
  no "porcelain: regressed reads back" (natField line "regressed" == 1)
  no "porcelain: improved reads back" (natField line "improved" == 2)
  no "porcelain: result reads back" ((field line "result") == some "regressed")

  -- The deficit a queue ranks by comes from the file's own encoding.
  let hd : Tsv := { provenance := #[], retired := #[], lowered := #[], encoding := some (.headroom 1000)
                    rows := #[{ item := "a", value := 998 }, { item := "b", value := 1000 }] }
  no "deficit: headroom ranks the larger debt first"
    (deficits hd == #[("a", 2)])
  let pr : Tsv := { provenance := #[], retired := #[], lowered := #[], encoding := some (.pairs "impl" "rows")
                    rows := #[{ item := "p.impl", value := 1 }, { item := "p.rows", value := 4 }] }
  no "deficit: pairs ranks the gap between depth and coverage"
    (deficits pr == #[("p", 3)])
  let rw : Tsv := { provenance := #[], retired := #[], lowered := #[], encoding := some .raw
                    rows := #[{ item := "a", value := 2 }, { item := "b", value := 5 }] }
  no "deficit: raw ranks the distance from the best item" (deficits rw == #[("a", 3)])

  -- Routed, as a row that fails in both directions: scripts/owed.lean is
  -- the owed ratchet and not this agent's file, so its identical `fieldOf`
  -- stands for now. This fails if the two readers ever disagree, and again
  -- once owed.lean drops its copy — at which point delete this block.
  let owedSrc ← readFileOr "scripts/owed.lean"
  let owedHasCopy := containsSub owedSrc "def fieldOf"
  no "routed: scripts/owed.lean no longer declares its own fieldOf — switch it to \
Gate.recordField and delete this check" owedHasCopy
  let samples : List (String × Option String) :=
    [("-- owed: t_one", some "t_one"),
     -- Leading whitespace is trimmed first, which owed.lean's own test also
     -- pins ("  -- owed: x" parses). Getting this wrong here was how this
     -- block first failed.
     ("  -- owner: M.Two", some "M.Two"),
     ("-- owner: M.Two", some "M.Two"), ("owed: x", none),
     ("-- blocker:", some "")]
  for (line, want) in samples do
    let key := if containsSub line "owner" then "owner"
      else if containsSub line "blocker" then "blocker" else "owed"
    no s!"routed: recordField disagrees with the record form on '{line}'"
      (recordField line key == want)
  -- Routed, the same way: `cites` loads no scoreboard module, so a
  -- backticked name of one of Board's theorems in any docstring reads to it
  -- as a phantom and fails the gate — which is the half of this row that
  -- fails already. This half fails once `scripts/cites.lean` loads the
  -- module; then delete the row and cite the theorems by name.
  let citesSrc ← readFileOr "scripts/cites.lean"
  no "routed: scripts/cites.lean now loads scripts.Board — delete this row, and cite \
Board's theorems by name where the prose relies on them" (!containsSub citesSrc "scripts.Board")
  -- and a pending name whose tier has landed fails here — which is what
  -- stops the pending list going stale.
  let tiers ← discover
  for t in tiers do
    let hasTsv ← System.FilePath.pathExists (tsvPath t)
    let hasScript ← System.FilePath.pathExists (scriptPath t)
    if hasTsv != hasScript then
      no s!"discovery: {t} has one half only ({if hasTsv then "a baseline and no \
producer" else "a producer and no baseline"}), which --check faults" false
    if hasTsv && hasScript && pendingTiers.contains t then
      no s!"discovery: {t} has both halves but is still on pendingTiers — remove \
its name in the same commit that lands it" false
    if !hasTsv && !hasScript && !pendingTiers.contains t then
      no s!"discovery: {t} is declared, absent, and not pending, which --check \
faults" false
  no "discovery: a fixture directory is not a tier" (!tiers.contains "clean")
  no "discovery: every pending name is declared"
    (pendingTiers.all declaredTiers.contains)

  -- Tier discovery by convention, both halves. `--check` and the selftest
  -- agree on every state: absence passes only for a declared-pending tier,

  let failed := (← fails.get).reverse
  if !failed.isEmpty then
    for f in failed do IO.eprintln s!"FAIL {f}"
    return 1
  IO.println s!"scoreboard selftest: format passed ({malformations.length} malformations, \
{wellFormed.length} states the tool writes or asks for, 4 ratchet verdicts each failing \
--check, retirement through the tool, a lowering authorising exactly one fall once, \
{baseCases.length} base-check cases, the aggregate's own faults, and the key)"
  -- Then every tier's own selftest, in parallel: one command is what a
  -- landing runs, so the fan-out lives here rather than in a procedure
  -- someone has to remember.
  let tiers ← discover
  let mut spawned : Array (String × Option (IO.Process.Child { } ×
    System.FilePath × String × String)) := #[]
  for t in tiers do
    if ← System.FilePath.pathExists (scriptPath t) then
      let dir ← IO.FS.createTempDir
      let o := (dir / "out").toString
      let e := (dir / "err").toString
      let child ← IO.Process.spawn
        { cmd := "sh"
          args := #["-c", "exec lake env lean --run \"$1\" --selftest > \"$2\" 2> \"$3\"",
                    "sh", scriptPath t, o, e] }
      spawned := spawned.push (t, some (child, dir, o, e))
  let mut bad := 0
  for (t, s) in spawned do
    match s with
    | none => pure ()
    | some (child, dir, o, e) =>
      let code ← child.wait
      if code == 0 then
        IO.println s!"scoreboard selftest: {t} passed"
      else
        bad := bad + 1
        IO.eprintln s!"FAIL tier {t} selftest: exit {code}"
        IO.eprint (← readFileOr o)
        IO.eprint (← readFileOr e)
      IO.FS.removeDirAll dir
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return (← selftest)
  if args.contains "--queue" then return (← queue 40)
  if args.contains "--bench" then return (← benchReport)
  match baseArg args with
  | none => aggregate (args.contains "--check")
  | some none =>
    IO.eprintln "scoreboard: --base needs a revision (the commit being landed onto)"
    return 2
  | some (some rev) =>
    let measured ← aggregate (args.contains "--check")
    let held ← baseCheck rev
    return (if measured == 0 && held == 0 then 0 else 1)
