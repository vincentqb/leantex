/-
The scoreboard: one line per goal, and a queue computed from the deficits.

  scoreboard                one porcelain line per tier; exit 1 on any regression
  scoreboard --check        the same, quietly
  scoreboard --check --base <rev>
                            the gate the land tool runs: --check, plus every
                            committed baseline held to the one committed at <rev>.
                            A fall or a vanish since <rev> needs a line written
                            since <rev>, and a file still holding a request is
                            stale
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

/-- A tier's result from its exit status and the porcelain line it printed,
if any. The exit status is the contract: the porcelain word can name a
failure — `regressed`, `fault`, `stale` — and can never excuse one, so a
non-zero exit under any other word reads `fail`, and `stale` reads as
itself rather than as a generic failure the landing agent cannot act on. -/
def resultOf (code : UInt32) (line said : String) : String :=
  if code != 0 then
    (if said == "regressed" || said == "fault" || said == "stale" then said else "fail")
  else if line.isEmpty then "ok"
  else if said.isEmpty then "fault" else said

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
    let result := resultOf code line said
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
  let (tiers, misnamed) ← discover
  -- A name the rule refuses is a fault before anything runs: its producer
  -- path and its porcelain line are the name, and git quotes it.
  let misnamedResults : Array TierResult := misnamed.map fun m =>
    { tier := m, items := 0, regressed := 0, improved := 0, result := "fault"
      detail := s!"tests/scoreboard/{shownName m}.tsv names no tier: a tier's name is \
[a-z0-9-]+ (the basename of its baseline and the root of its producer), so rename both halves" }
  match ← buildImports with
  | some err =>
    IO.eprintln s!"scoreboard: the tiers' imports do not build, so no tier can be \
measured: {err}"
    for t in tiers do
      IO.println (tierLine t 0 0 0 "fault")
    for m in misnamed do
      IO.println (tierLine (shownName m) 0 0 0 "fault")
    return 1
  | none => pure ()
  let mut planned : Array (String × Option TierResult × Option Spawn) :=
    misnamedResults.map fun r => (r.tier, some r, none)
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
    IO.println (tierLine (shownName r.tier) r.items r.regressed r.improved r.result)
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

/-- git's answer, or its own first words on stderr when it gives none: a base
check that fails closed says why in the tool's words. -/
def gitRead (args : Array String) : IO (Except String String) := do
  try
    let o ← IO.Process.output { cmd := "git", args }
    if o.exitCode == 0 then return .ok o.stdout
    let said := ((o.stderr.splitOn "\n").find? (!·.trimAscii.isEmpty)).getD ""
    return .error s!"git {args[0]!} exited {o.exitCode}: {said.trimAscii.toString}"
  catch e => return .error s!"git did not run: {e}"

/-- A direct child of `tests/scoreboard/` named like a baseline, as git lists it
at the base: a regular file's blob, or anything else under such a name. -/
inductive Listed where
  | baseline (path oid : String)
  | notAFile (path mode kind : String)
deriving BEq

/-- Read `git ls-tree -z`: NUL-terminated `<mode> <type> <object>\t<path>`
entries, the path as committed. `-z` is what stops git quoting a name, and
the quoted name once slipped past the `.tsv` filter below, so its deletion
went unseen. `none` when an entry does not read: a listing half understood is
not one to pass on. -/
def readListing (listing : String) : Option (Array Listed) := Id.run do
  let mut out : Array Listed := #[]
  for e in listing.splitOn (Char.ofNat 0).toString do
    if e.isEmpty then continue
    match e.splitOn "\t" with
    | head :: rest@(_ :: _) =>
      let path := String.intercalate "\t" rest
      if !path.endsWith ".tsv" then continue
      match head.splitOn " " with
      | [mode, kind, oid] =>
        if kind == "blob" && (mode == "100644" || mode == "100755") then
          out := out.push (.baseline path oid)
        else out := out.push (.notAFile path mode kind)
      | _ => return none
    | _ => return none
  return some out

/-- `--check --base <rev>`: every baseline committed at `<rev>` held to the
tree's copy (`judgeBase`), one porcelain line per baseline,
`scoreboard: base=<sha> tier=<t> result=ok|laundered|stale|fault`. The
ratchet compares committed files with a measurement, so it cannot see a floor
edited down by hand, or a baseline deleted and regenerated from nothing: both
leave file and tree agreeing. The base can see them. A rev that names no
commit fails closed, and so does a tree that is not a git repository. -/
def baseCheck (rev : String) : IO UInt32 := do
  let some sha := (← git #["rev-parse", "--verify", "--quiet", rev ++ "^{commit}"]).map
      (·.trimAscii.toString)
    | IO.eprintln s!"scoreboard: --base {rev} names no commit here, so no baseline can be \
held to it; failing closed"
      IO.println s!"scoreboard: base={rev} result=fault"
      return 1
  let short := (sha.take 12).toString
  let some listing ← git #["ls-tree", "-z", sha, "tests/scoreboard/"]
    | IO.eprintln s!"scoreboard: cannot list tests/scoreboard at {short}; failing closed"
      IO.println s!"scoreboard: base={short} result=fault"
      return 1
  let some entries := readListing listing
    | IO.eprintln s!"scoreboard: git's listing of tests/scoreboard at {short} does not read; \
failing closed"
      IO.println s!"scoreboard: base={short} result=fault"
      return 1
  let mut bad := 0
  for e in entries do
    match e with
    | .notAFile p mode kind =>
      let tier := shownName (((System.FilePath.mk p).fileStem).getD p)
      IO.println s!"scoreboard: base={short} tier={tier} result=fault"
      IO.println s!"scoreboard:   {p} is committed at {short} as a {kind} of mode {mode}, not a \
regular file, so it holds no floor this check can read; failing closed"
      bad := bad + 1
    | .baseline p oid =>
      let tier := shownName (((System.FilePath.mk p).fileStem).getD p)
      -- A blob git cannot read is no empty base: an empty base holds no
      -- floor, so reading one as `""` passed any fall at all. `cat-file` of
      -- the listed object rather than `show`: the bytes as committed, with no
      -- textconv an attributes file could ask for.
      match ← gitRead #["cat-file", "blob", oid] with
      | .error why =>
        IO.println s!"scoreboard: base={short} tier={tier} result=fault"
        IO.println s!"scoreboard:   git cannot read {p} as committed at {short} ({why}), so no \
floor can be held to it; failing closed — fetch the base's objects, or run the check in a \
full clone"
        bad := bad + 1
      | .ok baseText =>
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
  let (tiers, misnamed) ← discover
  for m in misnamed do
    lines := lines.push s!"queue: tests/scoreboard/{shownName m}.tsv not ranked: its name is \
not a tier name ([a-z0-9-]+), which --check faults"
  for t in tiers do
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
   ("clean", "encoding-changed", "laundered"),
   ("clean", "lowered", "stale"),
   ("clean", "lowered-second", "stale"),
   ("clean", "retired-pending", "stale"),
   ("clean", "lowered-unheld", "laundered")]

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

-- ## The base check through the path that ships

/-- The environment the harness runs git and the scoreboard under: a fresh
install's — no user or system config, so `core.quotePath` and every other
default is git's own — and no variable naming another repository. git exports
`GIT_DIR` and `GIT_INDEX_FILE` to a hook, and a selftest run from one would
otherwise read the repository it checks instead of its own scratch. -/
def harnessEnv : Array (String × Option String) :=
  #[("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_NOSYSTEM", some "1"),
    ("GIT_TERMINAL_PROMPT", some "0")] ++
  (#["GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
      "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_COMMON_DIR", "GIT_NAMESPACE", "GIT_PREFIX",
      "GIT_CONFIG", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT", "GIT_IMPLICIT_WORK_TREE",
      "GIT_GRAFT_FILE", "GIT_NO_REPLACE_OBJECTS", "GIT_REPLACE_REF_BASE",
      "GIT_SHALLOW_FILE"].map fun n => (n, (none : Option String)))

/-- The tier every harness repository carries live: a producer whose `--check`
exits 0 whatever the file says, so the aggregate passes and the exit status of
`--check --base` is the base check's alone, and a raw baseline with two rows to
move. -/
def probeTier : String := "zz-probe"

def probeText : String := "# encoding: raw\nalpha\t5\nbravo\t3\n"

/-- A producer whose `--check` passes whatever its baseline says. -/
def trivialProducer : String := "def main (_ : List String) : IO UInt32 := pure 0\n"

/-- One harness case: files committed at the base beside the harness's own, the
edit that makes the tree from the base (given the repository and the base's
sha), the exit status `scoreboard --check --base <base>` must return, and lines
its output must hold (given the base's 12-digit sha). -/
structure CliCase where
  label : String
  extra : List (String × String)
  edit : System.FilePath → String → IO Unit
  exit : UInt32
  says : String → List String

/-- Replace `old` in a harness file, and fail the case when the file does not
hold it: an edit that did nothing would pass a case for the wrong reason. -/
def swapIn (dir : System.FilePath) (path old new : String) : IO Unit := do
  let s ← IO.FS.readFile (dir / path)
  unless containsSub s old do throw (IO.userError s!"{path} holds no '{old}'")
  IO.FS.writeFile (dir / path) (s.replace old new)

def harnessGit (dir : System.FilePath) (args : Array String) : IO String := do
  let o ← IO.Process.output
    { cmd := "git"
      args := #["-c", "user.name=probe", "-c", "user.email=probe@example.org",
                "-c", "init.defaultBranch=main"] ++ args
      cwd := some dir, env := harnessEnv }
  if o.exitCode != 0 then
    throw (IO.userError s!"git {String.intercalate " " args.toList} exited {o.exitCode}: \
{o.stderr.trimAscii.toString}")
  return o.stdout.trimAscii.toString

/-- Make the blob `path` holds at `sha` unreadable, as a blobless partial clone
whose promisor is out of reach leaves it: the commit and its trees still
answer, the one object does not. A fresh harness repository's objects are
loose, one file each. -/
def unreadable (dir : System.FilePath) (sha path : String) : IO Unit := do
  let oid ← harnessGit dir #["rev-parse", s!"{sha}:{path}"]
  IO.FS.removeFile (dir / ".git" / "objects" / (oid.take 2).toString / (oid.drop 2).toString)

/-- The cases. Each refusal is a way the base check once failed open or could;
each pass is a sanctioned act, so a check that refused everything fails too. -/
def cliCases : List CliCase :=
  let probe := tsvPath probeTier
  let enc := "# encoding: raw\n"
  let says (word : String) := fun (s : String) =>
    [s!"scoreboard: base={s} tier={probeTier} result={word}"]
  let request := "# lowered: alpha 5→4 — an invented reason\n"
  let trivial := trivialProducer
  let fall := fun d => swapIn d probe "alpha\t5\n" "alpha\t4\n"
  [{ label := "nothing moved", extra := [], edit := fun _ _ => pure (), exit := 0
     says := says "ok" },
   { label := "a fall edited by hand", extra := [], edit := fun d _ => fall d, exit := 1
     says := says "laundered" },
   { label := "a vanish edited by hand", extra := []
     edit := fun d _ => swapIn d probe "bravo\t3\n" "", exit := 1, says := says "laundered" },
   { label := "the baseline deleted with its producer", extra := []
     edit := fun d _ => do
       IO.FS.removeFile (d / probe)
       IO.FS.removeFile (d / scriptPath probeTier)
     exit := 1, says := says "fault" },
   { label := "an unapplied request, the floor unmoved", extra := []
     edit := fun d _ => swapIn d probe enc (enc ++ request), exit := 1, says := says "stale" },
   { label := "an unapplied request beside the fall it names", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ request)
       fall d
     exit := 1, says := says "stale" },
   { label := "a fall paid by a new record", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ "# lowered (applied): alpha 5→4 — an invented reason\n")
       fall d
     exit := 0, says := says "ok" },
   { label := "a vanish paid by a new retirement", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ "# retired: bravo — an invented reason\n")
       swapIn d probe "bravo\t3\n" ""
     exit := 0, says := says "ok" },
   { label := "a tier retired by a new tombstone", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / probe) "# retired-tier: an invented reason\n"
       IO.FS.removeFile (d / scriptPath probeTier)
     exit := 0, says := says "ok" },
   -- A base blob git cannot read — a blobless partial clone whose promisor is
   -- out of reach, simulated by deleting the loose object — once read as an
   -- empty base, and an empty base holds no floor.
   { label := "the base's blob unreadable, a fall edited by hand", extra := []
     edit := fun d sha => do
       unreadable d sha probe
       fall d
     exit := 1, says := says "fault" },
   { label := "the base's blob unreadable, nothing moved", extra := []
     edit := fun d sha => unreadable d sha probe, exit := 1, says := says "fault" },
   -- A name git quotes: `ls-tree` without `-z` printed it in quotes, the
   -- `.tsv` filter dropped it, and its deletion went unseen.
   { label := "a baseline under a name git quotes, deleted with its producer"
     extra := [(tsvPath "zzé", "# encoding: raw\nalpha\t3\n"), (scriptPath "zzé", trivial)]
     edit := fun d _ => do
       IO.FS.removeFile (d / tsvPath "zzé")
       IO.FS.removeFile (d / scriptPath "zzé")
     exit := 1, says := fun s => [s!"scoreboard: base={s} tier=zz%C3%A9 result=fault"] },
   { label := "the same deletion under an ASCII name"
     extra := [(tsvPath "zz-ascii", "# encoding: raw\nalpha\t3\n"), (scriptPath "zz-ascii", trivial)]
     edit := fun d _ => do
       IO.FS.removeFile (d / tsvPath "zz-ascii")
       IO.FS.removeFile (d / scriptPath "zz-ascii")
     exit := 1, says := fun s => [s!"scoreboard: base={s} tier=zz-ascii result=fault"] },
   { label := "a live tier under a name outside [a-z0-9-]+", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / tsvPath "zzé") "# encoding: raw\nalpha\t3\n"
       IO.FS.writeFile (d / scriptPath "zzé") trivial
     exit := 1, says := fun _ => ["scoreboard: tier=zz%C3%A9 items=0 regressed=0 improved=0 result=fault"] }]

/-- Lay out one harness repository, commit it as the base, make the tree by the
case's edit, and run the scoreboard under test there: `none` when it answered as
the case says. Every declared tier is a tombstone in the harness, so the
aggregate passes without spawning their producers. -/
def runCliCase (bin toolchain : String) (c : CliCase) : IO (Option String) := do
  let dir ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (dir / "tests" / "scoreboard")
    IO.FS.createDirAll (dir / "scripts")
    IO.FS.writeFile (dir / "lean-toolchain") toolchain
    for t in declaredTiers do
      IO.FS.writeFile (dir / tsvPath t) "# retired-tier: a synthetic harness, nothing measured\n"
    IO.FS.writeFile (dir / scriptPath probeTier) trivialProducer
    IO.FS.writeFile (dir / tsvPath probeTier) probeText
    for (p, text) in c.extra do IO.FS.writeFile (dir / p) text
    let _ ← harnessGit dir #["init", "-q", "."]
    let _ ← harnessGit dir #["add", "-A"]
    let tree ← harnessGit dir #["write-tree"]
    let sha ← harnessGit dir #["commit-tree", tree, "-m", s!"harness base: {c.label}"]
    c.edit dir sha
    let o ← IO.Process.output
      { cmd := bin, args := #["--check", "--base", sha], cwd := some dir, env := harnessEnv }
    let lines := (o.stdout.splitOn "\n").map (·.trimAscii.toString)
    let shown := String.intercalate "\n    " ((lines.filter (containsSub · "zz")).take 8)
    if o.exitCode != c.exit then
      return some s!"cli {c.label}: exit {o.exitCode}, wanted {c.exit}\n    {shown}"
    for l in c.says (sha.take 12).toString do
      unless lines.contains l do
        return some s!"cli {c.label}: no line '{l}'\n    {shown}"
    return none
  catch e =>
    return some s!"cli {c.label}: the harness could not run: {e}"
  finally
    IO.FS.removeDirAll dir

/-- Every case, in parallel, against this binary: `IO.appPath` is the scoreboard
under test, so the cases drive `main`, the listing, the blob reads and the
count exactly as a landing does. Run interpreted, this process is `lean`, which
has no `--base`; the selftest then says so rather than test another binary. -/
def cliFailures : IO (Array String) := do
  let bin ← IO.appPath
  if bin.fileName != some "scoreboard" then
    return #[s!"cli: the selftest drives its own binary and this process is {bin}; run \
the compiled one: lake build scoreboard && .lake/build/bin/scoreboard --selftest"]
  let toolchain ← readFileOr "lean-toolchain"
  let mut tasks := #[]
  for c in cliCases do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) (runCliCase bin.toString toolchain c))
  let mut out := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok none => pure ()
    | .ok (some why) => out := out.push why
    | .error e => out := out.push s!"cli: {e}"
  return out

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

  -- The tool's own remedies, followed to the end through the path a tier
  -- ships (`tierMainAt`), twice for each kind — the probe shape that found
  -- the wedges: a second fall of one item, a retirement, and a carried
  -- record asked to pay again.
  let flowDir ← IO.FS.createTempDir
  try
    let p := (flowDir / "flow.tsv").toString
    let rowsNow ← IO.mkRef (#[] : Array Row)
    let set (alpha : Option Int) : IO Unit :=
      let first : Array Row := match alpha with
        | some v => #[{ item := "alpha", value := v }]
        | none => #[]
      rowsNow.set (first.push { item := "bravo", value := 1000 })
    let run (args : List String) : IO UInt32 := do
      let (_, code) ← IO.FS.withIsolatedStreams
        (tierMainAt p "flow" (.headroom 1000) (do return (#[], ← rowsNow.get)) (pure 0) args)
      return code
    let add (line : String) : IO Unit := do
      let ls := (← IO.FS.readFile p).splitOn "\n"
      IO.FS.writeFile p (String.intercalate "\n" (ls.take 2 ++ [line] ++ ls.drop 2))
    let del (line : String) : IO Unit := do
      let ls := (← IO.FS.readFile p).splitOn "\n"
      IO.FS.writeFile p (String.intercalate "\n" (ls.filter (· != line)))
    let says (frag : String) : IO Bool := return containsSub (← IO.FS.readFile p) frag
    set (some 998)
    no "flow: regeneration starts from nothing" ((← run []) == 0)
    no "flow: the floor is the measurement" ((← run ["--check"]) == 0)
    set (some 997)
    no "flow: a fall fails --check" ((← run ["--check"]) == 1)
    no "flow: regeneration refuses the fall" ((← run []) == 1)
    add "# lowered: alpha 998→997 — the first fall, an invented reason"
    no "flow: a file holding a request is stale under --check" ((← run ["--check"]) == 1)
    no "flow: regeneration applies the request" ((← run []) == 0)
    no "flow: the request went back as a record"
      ((← says "# lowered (applied): alpha 998→997") && !(← says "# lowered: alpha"))
    no "flow: --check passes on what regeneration wrote" ((← run ["--check"]) == 0)
    -- A request no fall answers: the one committed state only the request
    -- arm of `stale` sees, since nothing else in the file has moved.
    let unanswered := "# lowered: alpha 997→995 — a request no fall answers, an invented reason"
    add unanswered
    no "flow: a committed request no fall answers is stale under --check" ((← run ["--check"]) == 1)
    no "flow: regeneration refuses to carry it" ((← run []) == 1)
    del unanswered
    no "flow: without it --check passes again" ((← run ["--check"]) == 0)
    set (some 996)
    no "flow: a second fall is refused, the record pays nothing" ((← run []) == 1)
    add "# lowered: alpha 997→996 — the second fall, an invented reason"
    no "flow: the second request applies" ((← run []) == 0)
    no "flow: and --check passes after it" ((← run ["--check"]) == 0)
    set (some 998)
    no "flow: the item recovers and the rise is recorded" ((← run []) == 0)
    set (some 997)
    no "flow: the same fall again is refused, between the same values" ((← run []) == 1)
    set none
    no "flow: a vanish is refused" ((← run []) == 1)
    add "# retired: alpha — the measurement stopped, an invented reason"
    no "flow: a retirement beside its row is stale under --check" ((← run ["--check"]) == 1)
    no "flow: regeneration applies the retirement" ((← run []) == 0)
    no "flow: the row is gone and the line stays"
      ((← says "# retired: alpha") && !(← says "alpha\t"))
    no "flow: --check passes after the retirement" ((← run ["--check"]) == 0)
    set (some 998)
    no "flow: a retired item measured again is a fault" ((← run ["--check"]) == 2)
  finally
    IO.FS.removeDirAll flowDir

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
  -- The same check through the path that ships: `scoreboard --check --base`
  -- spawned in throwaway repositories. Mutants that made `main` ignore the
  -- base check, or the base check list nothing or count nothing, passed every
  -- line above.
  for why in ← cliFailures do no why false

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
  no "aggregate: a stale tier reads stale, not fail" (resultOf 1 "x" "stale" == "stale")
  no "aggregate: a non-zero exit under an ok line is a failure" (resultOf 3 "x" "ok" == "fail")
  no "aggregate: a named failure keeps its name"
    (resultOf 1 "x" "regressed" == "regressed" && resultOf 2 "x" "fault" == "fault")
  no "aggregate: a silent zero exit is ok, a zero exit with a wordless line a fault"
    (resultOf 0 "" "" == "ok" && resultOf 0 "x" "" == "fault")
  no "--base: read off the arguments"
    (baseArg ["--check", "--base", "abc"] == some (some "abc") && baseArg ["--check"] == none &&
      baseArg ["--base"] == some none)

  -- The HTML freshness key, over a synthetic one-fixture corpus: a function
  -- of the files, and moved by a sentence.
  let dir ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "OpenSans-Regular.ttf")
      (← IO.FS.readBinFile "tests/corpus/fonts/OpenSans-Regular.ttf")
    let src := "\\documentclass{article}\n\\begin{document}\nAn invented sentence.\n\\end{document}\n"
    IO.FS.writeFile (dir / "probe.tex") src
    let k1 ← Hermetic.corpusKey dir
    let k2 ← Hermetic.corpusKey dir
    IO.FS.writeFile (dir / "probe.tex") (src.replace "invented" "different")
    let k3 ← Hermetic.corpusKey dir
    match k1, k2, k3 with
    | .ok a, .ok b, .ok c =>
      no "key: the same files give the same key" (a == b)
      no "key: a changed sentence moves it" (a != c)
    | _, _, _ => no "key: the synthetic corpus builds to HTML" false
  finally
    IO.FS.removeDirAll dir

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
  -- Tier discovery by convention, both halves. `--check` and the selftest
  -- agree on every state: absence passes only for a declared-pending tier,
  -- and a pending name whose tier has landed fails here — which is what
  -- stops the pending list going stale.
  let (tiers, misnamed) ← discover
  for m in misnamed do
    no s!"discovery: tests/scoreboard/{shownName m}.tsv is not a tier name ([a-z0-9-]+), \
which --check faults" false
  for t in tiers do
    let hasTsv ← System.FilePath.pathExists (tsvPath t)
    let hasScript ← System.FilePath.pathExists (scriptPath t)
    -- A tombstone is a retired tier's whole record: its producer is gone by
    -- design, so one half is the state it must be in.
    let tomb := hasTsv &&
      ((parse (← readFileOr (tsvPath t))).toOption.bind (·.tierRetired)).isSome
    if hasTsv != hasScript && !tomb then
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
  no "discovery: every declared name is a tier name" (declaredTiers.all tierNameOk)
  -- The name rule, and the listing that no longer lets git quote a name.
  no "name: the shipped names pass" (["compat", "zz-probe", "p5", "a-b"].all tierNameOk)
  no "name: anything outside [a-z0-9-]+ does not"
    (!(["", "zzé", "Compat", "a b", "a.b", "a_b", "a\tb"].any tierNameOk))
  no "name: a refused name prints as one token"
    (shownName "zzé" == "zz%C3%A9" && shownName "a b" == "a%20b" && shownName "compat" == "compat")
  let nul := (Char.ofNat 0).toString
  let listing := String.intercalate nul
    ["100644 blob 1111\ttests/scoreboard/compat.tsv", "040000 tree 2222\ttests/scoreboard/selftest",
     "100644 blob 3333\ttests/scoreboard/zzé.tsv", "120000 blob 4444\ttests/scoreboard/zz-link.tsv",
     "040000 tree 5555\ttests/scoreboard/zz-dir.tsv", "100644 blob 6666\ttests/scoreboard/notes.md", ""]
  no s!"listing: -z entries read as committed, and only a regular file is a baseline"
    (readListing listing == some #[.baseline "tests/scoreboard/compat.tsv" "1111",
      .baseline "tests/scoreboard/zzé.tsv" "3333",
      .notAFile "tests/scoreboard/zz-link.tsv" "120000" "blob",
      .notAFile "tests/scoreboard/zz-dir.tsv" "040000" "tree"])
  no "listing: an entry that does not read fails the whole listing"
    ((readListing s!"100644 blob\ttests/scoreboard/compat.tsv{nul}").isNone &&
      (readListing s!"tests/scoreboard/compat.tsv{nul}").isNone)

  let failed := (← fails.get).reverse
  if !failed.isEmpty then
    for f in failed do IO.eprintln s!"FAIL {f}"
    return 1
  IO.println s!"scoreboard selftest: format passed ({malformations.length} malformations, \
{wellFormed.length} states the tool writes or asks for, 4 ratchet verdicts each failing \
--check, retirement through the tool, a lowering authorising exactly one fall once, \
{baseCases.length} base-check cases, {cliCases.length} more through `--check --base` in \
throwaway repositories, the aggregate's own faults, the tool's printed remedies \
followed to the end, and the key)"
  -- Then every tier's own selftest, in parallel: one command is what a
  -- landing runs, so the fan-out lives here rather than in a procedure
  -- someone has to remember.
  let (tiers, _) ← discover
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
