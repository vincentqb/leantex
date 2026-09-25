/-
The scoreboard: one line per goal, and a queue computed from the deficits.

  scoreboard                one porcelain line per tier; exit 1 on any regression
  scoreboard --check        the same, quietly — the landing gate
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
to another engine, and it gates nothing.
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
      if code != 0 then (if said == "regressed" || said == "fault" then said else "fail")
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
  let mut spawned : Array (String × Option Spawn) := #[]
  for t in tiers do
    spawned := spawned.push (t, ← spawnTier t)
  let mut bad := 0
  for (t, s) in spawned do
    let r ← collectTier t s
    IO.println (tierLine r.tier r.items r.regressed r.improved r.result)
    if r.result != "ok" && !r.detail.isEmpty && !quiet then
      for l in r.detail.splitOn "\n" do
        if !l.trimAscii.toString.isEmpty then IO.println s!"scoreboard:   {l}"
    if r.result != "ok" && r.result != "missing" then bad := bad + 1
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

/-- Hand-written baselines, one per regression kind and one per
malformation. The fixture *is* the failing input: each case names the fault
it must provoke, and the clean fixture must provoke none. -/
def malformations : List (String × String) :=
  [("unsorted", "out of order"),
   ("duplicate", "duplicate item"),
   ("noninteger", "is not an integer"),
   ("threefields", "tab-separated fields"),
   ("retired-no-reason", "gives no reason"),
   ("retired-and-live", "retired and also measured"),
   ("lowered-no-reason", "gives no reason"),
   ("lowered-malformed", "malformed lowering"),
   ("lowered-unheld", "but the row says"),
   ("no-rows", "no rows")]

def readFixture (name : String) : IO (Except String Tsv) := do
  let text ← readFileOr (fixture name)
  if text.isEmpty then return .error s!"fixture {name} is missing"
  return parse text

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let no (why : String) (ok : Bool) : IO Unit := do
    unless ok do fails.modify (why :: ·)

  -- A clean baseline parses, validates, and ratchets against itself as ok.
  match ← readFixture "clean" with
  | .error e => no s!"clean fixture does not parse: {e}" false
  | .ok t =>
    no s!"clean fixture has faults: {String.intercalate "; " (validate t).toList}"
      (validate t).isEmpty
    no "clean fixture has three rows" (t.rows.size == 3)
    no "clean fixture declares the headroom encoding" (t.encoding == some (.headroom 1000))
    let d := ratchet t t
    no "a baseline against itself neither loses nor gains"
      d.changes.isEmpty

  -- Every malformation fires its own fault, and none of them is the
  -- catch-all: the message must name the kind.
  for (name, want) in malformations do
    let got ← readFixture name
    let msgs : Array String := match got with
      | .error e => #[e]
      | .ok t => validate t
    no s!"malformation {name}: nothing fired" (!msgs.isEmpty)
    no s!"malformation {name}: fired {String.intercalate "; " msgs.toList}, wanted \
'{want}'" (msgs.any (containsSub · want))

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
  match ← readFixture "clean" with
  | .error _ => no "clean fixture unavailable for the ratchet cases" false
  | .ok base =>
    let verdicts : List (String × Bool × Bool) :=
      [("dropped", true, false),
       ("disappeared", true, false),
       -- `added` under a headroom cap: an unseen item below the cap is debt
       -- arriving under a new name, so it is a fall.
       ("added", true, false),
       ("raised", false, true)]
    for (name, wantLoss, wantGain) in verdicts do
      match ← readFixture name with
      | .error e => no s!"ratchet fixture {name}: {e}" false
      | .ok now =>
        let d := ratchet base now
        no s!"ratchet {name}: loss expected {wantLoss}, got \
{d.losses.size} ({String.intercalate "; " (d.losses.map (·.describe)).toList})"
          (d.losses.isEmpty == !wantLoss)
        no s!"ratchet {name}: gain expected {wantGain}, got {d.gains.size}"
          (d.gains.isEmpty == !wantGain)
        -- The tight rule: every one of the four fails `--check`, a rise
        -- included. Before this, a rise passed and left the floor stale.
        no s!"ratchet {name}: --check must fail on any change" (!d.checkPasses)
    no "ratchet: an unchanged measurement is the only state --check passes"
      (ratchet base base).checkPasses
    -- Retirement is read off the *committed baseline*: the same rows as
    -- `clean`, plus the retirement line, against a measurement that no
    -- longer produces the item. Without the line this is `disappeared`,
    -- which regresses; with it, nothing fires.
    match ← readFixture "retired" with
    | .error e => no s!"ratchet fixture retired: {e}" false
    | .ok r =>
      let b : Tsv := { base with retired := r.retired }
      no "retirement: the fixture carries exactly one retirement line" (r.retired.size == 1)
      no "retirement: the baseline still holds the item it retires"
        (b.rows.any (·.item == "alpha"))
      no "retirement: the measurement no longer holds it" (!r.rows.any (·.item == "alpha"))
      let d := ratchet b r
      no s!"ratchet retired: a retired item's absence is not a loss \
({String.intercalate "; " (d.losses.map (·.describe)).toList})" d.losses.isEmpty
      let d2 := ratchet base r
      no "ratchet retired: without the retirement line the same absence is a loss"
        (!d2.losses.isEmpty)

    -- A headroom item the baseline never held enters at the cap, so new
    -- debt under a new name is a fall rather than an improvement. The
    -- `added` fixture is below the cap; a new item AT the cap is neither.
    match ← readFixture "added" with
    | .error e => no s!"ratchet fixture added: {e}" false
    | .ok now =>
      let d := ratchet base now
      no s!"headroom: an unseen item below the cap is a fall, not an entry \
({String.intercalate "; " (d.changes.map (·.describe)).toList})"
        (d.losses.size == 1 && d.gains.isEmpty)
      let atCap : Tsv := { now with
        rows := now.rows.map fun r =>
          if (base.find? r.item).isNone then { r with value := 1000 } else r }
      let d2 := ratchet base atCap
      no "headroom: an unseen item at the cap is neither a fall nor a rise"
        (d2.losses.isEmpty && d2.gains.size == 1)
      -- A tier whose encoding declares no cap keeps the plain rule.
      let raw : Tsv := { base with encoding := some .raw }
      no "raw: an unseen item still enters at its measured value"
        ((ratchet raw now).losses.isEmpty)
    match ← readFixture "lowered" with
    | .error e => no s!"ratchet fixture lowered: {e}" false
    | .ok low =>
      no "lowering: the fixture carries exactly one lowering line" (low.lowered.size == 1)
      no s!"lowering: the fixture is clean ({String.intercalate "; " (validate low).toList})"
        (validate low).isEmpty
      let d := ratchet base low
      no "lowering: the fall is still a loss the ratchet reports" (d.losses.size == 1)
      no "lowering: --check fails on it whatever the file says"
        (!d.checkPasses)
      match d.losses[0]? with
      | none => no "lowering: no loss to authorise" false
      | some c =>
        no "lowering: the committed line authorises exactly this fall"
          (low.lowered.any (·.authorises c))
        no "lowering: without the line nothing authorises it"
          (!base.lowered.any (·.authorises c))
        let wrong : Lowered := { item := "alpha", old := 998, new := 996
                                 why := "a different fall" }
        no "lowering: a line naming other values does not authorise it"
          (!wrong.authorises c)
        let other : Lowered := { low.lowered[0]! with item := "bravo" }
        no "lowering: a line naming another item does not authorise it"
          (!other.authorises c)

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
4 ratchet verdicts each failing --check, retirement both ways, and a lowering \
authorising exactly its own fall)"
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
  aggregate (args.contains "--check")
