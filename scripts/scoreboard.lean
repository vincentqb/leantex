/-
The scoreboard: one line per goal, and a queue computed from the deficits.

  scoreboard                one porcelain line per tier; exit 1 on any regression
  scoreboard --check        the same, quietly — the landing gate
  scoreboard --queue        ranked deficits across every tier
  scoreboard --bench        the speed report, never gated
  scoreboard --selftest     the format, the ratchet, and the malformations

A tier is discovered by convention: its name is the basename of
`tests/scoreboard/<tier>.tsv` and the root of `scripts/<tier>.lean`, and its
`--check` is `lake env lean --run scripts/<tier>.lean --check`. A tier
declared with only one of the two files reports `missing` — visible, and not
a failure, so a sibling's tier arriving in two commits does not break the
gate in between.

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

/-- Run one tier's own `--check` and read its porcelain line back. The tier
is the authority on its own numbers; this reads the line it printed, never a
summary of it.

Each check runs in its own process writing to its own files rather than to a
pipe, so the aggregate can have every tier in flight at once without a
reader deadlocking on a full pipe — the tiers are independent, and a landing
gate that took one interpreter startup per tier in series took 17 s where
this takes one. -/
def spawnTier (tier : String) : IO (Option (IO.Process.Child { } × String × String)) := do
  let hasTsv ← System.FilePath.pathExists (tsvPath tier)
  let hasScript ← System.FilePath.pathExists (scriptPath tier)
  if !hasTsv || !hasScript then return none
  let dir ← IO.FS.createTempDir
  let outPath := (dir / "out").toString
  let errPath := (dir / "err").toString
  let child ← IO.Process.spawn
    { cmd := "sh"
      args := #["-c", s!"lake env lean --run {scriptPath tier} --check \
> {outPath} 2> {errPath}"] }
  return some (child, outPath, errPath)

def collectTier (tier : String) (spawned : Option (IO.Process.Child { } × String × String)) :
    IO TierResult := do
  match spawned with
  | none =>
    let hasTsv ← System.FilePath.pathExists (tsvPath tier)
    let hasScript ← System.FilePath.pathExists (scriptPath tier)
    let why :=
      if !hasTsv && !hasScript then "neither the baseline nor the producer exists"
      else if !hasTsv then s!"{scriptPath tier} exists but {tsvPath tier} does not"
      else s!"{tsvPath tier} exists but {scriptPath tier} does not"
    return { tier, items := 0, regressed := 0, improved := 0, result := "missing", detail := why }
  | some (child, outPath, errPath) =>
    let code ← child.wait
    let stdout ← readFileOr outPath
    let stderr ← readFileOr errPath
    let line := ((stdout.splitOn "\n").find? (·.startsWith "scoreboard: tier=")).getD ""
    if line.isEmpty then
      return { tier, items := 0, regressed := 0, improved := 0, result := "fault"
               detail := s!"exit {code}, no porcelain line; {stderr.trimAscii.toString}" }
    return { tier
             items := natField line "items"
             regressed := natField line "regressed"
             improved := natField line "improved"
             result := ((field line "result").getD "fault")
             detail := stderr.trimAscii.toString }

def aggregate (quiet : Bool) : IO UInt32 := do
  let tiers ← discover
  let mut spawned : Array (String × Option (IO.Process.Child { } × String × String)) := #[]
  for t in tiers do
    spawned := spawned.push (t, ← spawnTier t)
  let mut bad := 0
  for (t, s) in spawned do
    let r ← collectTier t s
    IO.println (tierLine r.tier r.items r.regressed r.improved r.result)
    if r.result != "ok" && !r.detail.isEmpty && !quiet then
      for l in r.detail.splitOn "\n" do
        if !l.trimAscii.toString.isEmpty then IO.println s!"scoreboard:   {l}"
    if r.result == "regressed" || r.result == "fault" then bad := bad + 1
  return (if bad == 0 then 0 else 1)

-- ## The queue

/-- Ranked deficits. Obligations whose blocker names no other open
obligation come first — they are the ones a proof can start on today — and
among those, the ones whose own name appears in the most other blockers,
because discharging one of those releases the most. Then every tier's worst
items, ranked by the deficit its own encoding defines.

Nothing here is a list of work: each line is computed from a committed
baseline or from the staged records. What a better ranking needs, and does
not have yet: the blocker graph as data rather than as prose (a `blocked-by:`
field naming obligations, so "names no other open obligation" stops being a
substring search over English); the per-item cost of a deficit (a compat row
is minutes, a `_covers` over two private loops is weeks); and the count of
documents each deficit holds back, which is the parity ladder's
fixtures-held-back number and the blocker ranking the `coverage` tier is
building. With those three the order becomes value over cost; with only
these, it is readiness over size. -/
def queue (limit : Nat) : IO UInt32 := do
  let mut lines : Array String := #[]
  let obs ← obligations
  let unblocks := fun (o : Ob) =>
    (obs.filter fun p => p.name != o.name && containsSub p.blocker o.name).size
  let readyObs := (ready obs).qsort fun a b =>
    if unblocks a == unblocks b then a.name < b.name else unblocks a > unblocks b
  for o in readyObs do
    let b := o.blocker
    let short := if b.length > 90 then ((b.take 90).toString) ++ "…" else b
    lines := lines.push s!"queue: obligation {o.name} owner={o.owner} \
blocked-by-open=0 unblocks={unblocks o} blocker={short}"
  for t in ← discover do
    let text ← readFileOr (tsvPath t)
    if text.isEmpty then continue
    match parse text with
    | .error e => lines := lines.push s!"queue: tier {t} unreadable: {e}"
    | .ok tsv =>
      let ds := deficits tsv
      for i in [0:ds.size] do
        if i < 3 then
          let (item, d) := ds[i]!
          lines := lines.push s!"queue: {t} {item} deficit={d}"
  let shown := if lines.size < limit then lines.size else limit
  for i in [0:shown] do
    IO.println lines[i]!
  IO.println s!"queue: {lines.size} ranked items, {shown} shown"
  return 0

-- ## The speed report

/-- The bench numbers beside the last ones PLAN.md recorded. A report: it
runs another engine, so it can never be part of a hermetic gate, and no
tolerance is enforced here. -/
def benchReport : IO UInt32 := do
  let plan ← readFileOr "PLAN.md"
  let recorded := (plan.splitOn "\n").filter (fun l =>
    containsSub l "scripts/bench.lean" && containsSub l "median")
  IO.println "scoreboard: bench is a report, never a gate (it runs lualatex)."
  match recorded.reverse.head? with
  | some l => IO.println s!"scoreboard: last recorded — {l.trimAscii.toString}"
  | none => IO.println "scoreboard: PLAN.md records no bench median yet"
  IO.println "scoreboard: proposed tolerance, not enforced: a tier would gate the \
median of 9 runs at +15% per document against its committed value, with the \
lualatex column recorded and never compared. Noise control: pin the sample count, \
drop the first run (cold page cache), compare medians rather than means, and take \
the whole corpus in one process-free batch so a busy host moves every row together \
— a single row moving is then a signal, and all rows moving is the host."
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
   ("item-whitespace", "holds whitespace"),
   ("no-rows", "no rows"),
   ("no-encoding", "no `# encoding:` line")]

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
    no "clean fixture declares the headroom encoding" (t.encoding == .headroom 1000)
    let d := ratchet t t
    no "a baseline against itself neither regresses nor improves"
      (d.regressed.isEmpty && d.improved.isEmpty)

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

  -- The four ratchet verdicts, each against the clean baseline.
  match ← readFixture "clean" with
  | .error _ => no "clean fixture unavailable for the ratchet cases" false
  | .ok base =>
    let verdicts : List (String × Bool × Bool) :=
      [("dropped", true, false),
       ("disappeared", true, false),
       ("added", false, true),
       ("raised", false, true)]
    for (name, wantReg, wantImp) in verdicts do
      match ← readFixture name with
      | .error e => no s!"ratchet fixture {name}: {e}" false
      | .ok now =>
        let d := ratchet base now
        no s!"ratchet {name}: regression expected {wantReg}, got \
{d.regressed.size} ({String.intercalate "; " d.regressed.toList})"
          (d.regressed.isEmpty == !wantReg)
        no s!"ratchet {name}: improvement expected {wantImp}, got \
{d.improved.size}" (d.improved.isEmpty == !wantImp)
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
      no s!"ratchet retired: a retired item's absence is not a regression \
({String.intercalate "; " d.regressed.toList})" d.regressed.isEmpty
      let d2 := ratchet base r
      no "ratchet retired: without the retirement line the same absence regresses"
        (!d2.regressed.isEmpty)

  -- The porcelain line the aggregate reads back is the one a tier prints.
  let line := tierLine "zz" 7 1 2 "regressed"
  no "porcelain: tier reads back" ((field line "tier") == some "zz")
  no "porcelain: items reads back" (natField line "items" == 7)
  no "porcelain: regressed reads back" (natField line "regressed" == 1)
  no "porcelain: improved reads back" (natField line "improved" == 2)
  no "porcelain: result reads back" ((field line "result") == some "regressed")

  -- The deficit a queue ranks by comes from the file's own encoding.
  let hd : Tsv := { provenance := #[], retired := #[], encoding := .headroom 1000
                    rows := #[{ item := "a", value := 998 }, { item := "b", value := 1000 }] }
  no "deficit: headroom ranks the larger debt first"
    (deficits hd == #[("a", 2)])
  let pr : Tsv := { provenance := #[], retired := #[], encoding := .pairs "impl" "rows"
                    rows := #[{ item := "p.impl", value := 1 }, { item := "p.rows", value := 4 }] }
  no "deficit: pairs ranks the gap between depth and coverage"
    (deficits pr == #[("p", 3)])
  let rw : Tsv := { provenance := #[], retired := #[], encoding := .raw
                    rows := #[{ item := "a", value := 2 }, { item := "b", value := 5 }] }
  no "deficit: raw ranks the distance from the best item" (deficits rw == #[("a", 3)])

  -- Tier discovery by convention, both halves.
  let tiers ← discover
  for t in tiers do
    let hasTsv ← System.FilePath.pathExists (tsvPath t)
    let hasScript ← System.FilePath.pathExists (scriptPath t)
    if hasTsv && !hasScript then
      no s!"discovery: {t} has a baseline and no producer, which must report missing" false
  no "discovery: a fixture directory is not a tier" (!tiers.contains "clean")

  let failed := (← fails.get).reverse
  if !failed.isEmpty then
    for f in failed do IO.eprintln s!"FAIL {f}"
    return 1
  IO.println s!"scoreboard selftest: format passed ({malformations.length} malformations, \
4 ratchet verdicts and retirement both ways)"
  -- Then every tier's own selftest, in parallel: one command is what a
  -- landing runs, so the fan-out lives here rather than in a procedure
  -- someone has to remember.
  let tiers ← discover
  let mut spawned : Array (String × Option (IO.Process.Child { } × String × String)) := #[]
  for t in tiers do
    if ← System.FilePath.pathExists (scriptPath t) then
      let dir ← IO.FS.createTempDir
      let o := (dir / "out").toString
      let e := (dir / "err").toString
      let child ← IO.Process.spawn
        { cmd := "sh"
          args := #["-c", s!"lake env lean --run {scriptPath t} --selftest > {o} 2> {e}"] }
      spawned := spawned.push (t, some (child, o, e))
  let mut bad := 0
  for (t, s) in spawned do
    match s with
    | none => pure ()
    | some (child, o, e) =>
      let code ← child.wait
      if code == 0 then
        IO.println s!"scoreboard selftest: {t} passed"
      else
        bad := bad + 1
        IO.eprintln s!"FAIL tier {t} selftest: exit {code}"
        IO.eprint (← readFileOr o)
        IO.eprint (← readFileOr e)
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return (← selftest)
  if args.contains "--queue" then return (← queue 40)
  if args.contains "--bench" then return (← benchReport)
  aggregate (args.contains "--check")
