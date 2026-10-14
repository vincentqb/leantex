/-
The scoreboard: one porcelain line per tier from its own `--check` exit status, the base check
against a revision, the deficit queue, and the reports.
Usage: scoreboard [--check [--base <rev>] | --queue | --bench | --selftest | --key <dir>]
-/
import scripts.Board
import scripts.GitGuard

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

/-- A tier's check in flight: its process, and the scratch directory holding its two
output files. -/
structure Spawn where
  child : IO.Process.Child { }
  dir : System.FilePath
  out : String
  err : String

/-- Run one tier's own `--check` in its own process writing to its own files, so every
tier runs at once without a pipe deadlock; paths reach `sh` as positional parameters. -/
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

/-- A tier's result from its exit status and porcelain line: the porcelain word can name a
failure but never excuse one, so a non-zero exit under any other word reads `fail`. -/
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
    -- Absence passes only for a tier on `pendingTiers`; anything else missing a half is a fault.
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
    -- The exit status is the contract; a porcelain line only adds counts.
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

/-- What the aggregate decides from a baseline before running its producer: an empty or
rowless baseline is a fault, and a tombstone passes as `retired` while no producer
measures it; `none` means run the producer. -/
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

/-- A result the aggregate passes: measured and clean, declared and not yet landed, or
retired by its tombstone. -/
def passing (result : String) : Bool :=
  result == "ok" || result == "missing" || result == "retired"

/-- Build what the tiers import, once, before any runs, since `lake env lean --run` builds
nothing; a failed build is a `fault` for every tier. -/
def buildImports : IO (Option String) := do
  let targets ← buildTargets
  if targets.isEmpty then return none
  let out ← IO.Process.output { cmd := "lake", args := #["build"] ++ targets }
  if out.exitCode == 0 then return none
  let log := (out.stdout ++ out.stderr).trimAscii.toString
  let firstErr := ((log.splitOn "\n").find? (containsSub · "error")).getD
    s!"lake build {String.intercalate " " targets.toList} exited {out.exitCode}"
  return some firstErr.trimAscii.toString

/-- A reason or credit under a porcelain line, spelled by `printable`, since its text
comes from files and producers this tool did not write. -/
def printReason (l : String) : IO Unit :=
  IO.println s!"scoreboard:   {printable l}"

/-- Every tier's result line, with the reasons of any tier that does not pass, under
`--check` too; `quiet` withholds only passing tiers' notes. -/
def aggregate (quiet : Bool) : IO UInt32 := do
  let (tiers, misnamed) ← discover
  -- A name the rule refuses is a fault before anything runs.
  let misnamedResults : Array TierResult := misnamed.map fun m =>
    { tier := m, items := 0, regressed := 0, improved := 0, result := "fault"
      detail := s!"testdata/scoreboard/{shownName m}.tsv names no tier: a tier's name is \
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
        if !l.isEmpty then printReason l
    if !passing r.result then bad := bad + 1
  return (if bad == 0 then 0 else 1)

/-- git as the base check runs it, with replacement objects off, so a replace ref cannot
stand in for a committed object; git's answer, or its first words on stderr. -/
def gitRead (args : Array String) : IO (Except String String) := do
  try
    let o ← IO.Process.output { cmd := "git", args := #["--no-replace-objects"] ++ args }
    if o.exitCode == 0 then return .ok o.stdout
    let said := ((o.stderr.splitOn "\n").find? (!·.trimAscii.isEmpty)).getD ""
    return .error s!"git {args[0]!} exited {o.exitCode}: {said.trimAscii.toString}"
  catch e => return .error s!"git did not run: {e}"

def git (args : Array String) : IO (Option String) := do
  return (← gitRead args).toOption

/-- A direct child of a committed baseline directory: a regular file's blob, or anything
else under such a name. -/
inductive Listed where
  | baseline (path oid : String)
  | notAFile (path mode kind : String)
deriving BEq

def Listed.path : Listed → String
  | .baseline p _ | .notAFile p _ _ => p

/-- A baseline's path under `baselineDir`, so a tier keeps its identity in a base that
filed it elsewhere. -/
def currentBaselinePath (p : String) : String :=
  s!"{baselineDir}/{((System.FilePath.mk p).fileName).getD p}"

/-- Read `git ls-tree -z` entries, paths as committed; `none` when an entry does not
read. -/
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

/-- The tree's copy of a baseline: `none` where there is none, and a fault where the name
holds anything but a regular file. -/
def treeCopy (p : String) : IO (Except String (Option String)) := do
  let md? ← try some <$> (System.FilePath.mk p).symlinkMetadata catch _ => pure none
  let some md := md? | return .ok none
  let what := match md.type with
    | .file => none
    | .dir => some "a directory"
    | .symlink => some "a symlink"
    | .other => some "a special file"
  if let some w := what then
    return .error s!"{p} is {w} in the tree, not a regular file, so it holds no floor this \
check can read; failing closed — commit the tier's baseline as a file"
  return .ok (some (← IO.FS.readFile p))

/-- The tree's direct-child baselines, spelled as the base's listing spells them,
sorted. -/
def treeBaselines : IO (Array String) := do
  let dir : System.FilePath := baselineDir
  let mut out : Array String := #[]
  if ← dir.isDir then
    for e in ← dir.readDir do
      if e.fileName.endsWith ".tsv" then out := out.push s!"{baselineDir}/{e.fileName}"
  return out.qsort (· < ·)

/-- `--check --base <rev>`: every baseline committed at `<rev>` held to the tree's copy
(`judgeBase`) and every tier file the tree adds judged alone (`judgeNew`), one porcelain
line each; a rev naming no commit, or no git repository, fails closed. -/
def baseCheck (rev : String) : IO UInt32 := do
  let some sha := (← git #["rev-parse", "--verify", "--quiet", rev ++ "^{commit}"]).map
      (·.trimAscii.toString)
    | IO.eprintln s!"scoreboard: --base {rev} names no commit here, so no baseline can be \
held to it; failing closed"
      IO.println s!"scoreboard: base={rev} result=fault"
      return 1
  let short := (sha.take 12).toString
  let some listing ← git #["ls-tree", "-z", sha, s!"{baselineDir}/", "tests/scoreboard/"]
    | IO.eprintln s!"scoreboard: cannot list committed baselines at {short}; failing closed"
      IO.println s!"scoreboard: base={short} result=fault"
      return 1
  let some entries := readListing listing
    | IO.eprintln s!"scoreboard: git's listing of committed baselines at {short} does not read; \
failing closed"
      IO.println s!"scoreboard: base={short} result=fault"
      return 1
  let mut bad := 0
  let mut known : Array String := #[]
  for e in entries do
    let current := currentBaselinePath e.path
    if known.contains current then
      let tier := shownName (((System.FilePath.mk current).fileStem).getD current)
      IO.println s!"scoreboard: base={short} tier={tier} result=fault"
      printReason s!"{tier} occurs in both committed baseline directories at {short}; \
one tier must have one floor"
      bad := bad + 1
      continue
    known := known.push current
    match e with
    | .notAFile p mode kind =>
      let tier := shownName (((System.FilePath.mk p).fileStem).getD p)
      IO.println s!"scoreboard: base={short} tier={tier} result=fault"
      printReason s!"{p} is committed at {short} as a {kind} of mode {mode}, not a \
regular file, so it holds no floor this check can read; failing closed"
      bad := bad + 1
    | .baseline p oid =>
      let tier := shownName (((System.FilePath.mk p).fileStem).getD p)
      -- An unreadable blob is no empty base; `cat-file` reads the bytes as committed.
      match ← gitRead #["cat-file", "blob", oid] with
      | .error why =>
        IO.println s!"scoreboard: base={short} tier={tier} result=fault"
        printReason s!"git cannot read {p} as committed at {short} ({why}), so no \
floor can be held to it; failing closed — fetch the base's objects, or run the check in a \
full clone"
        bad := bad + 1
      | .ok baseText =>
        match ← treeCopy current with
        | .error why =>
          IO.println s!"scoreboard: base={short} tier={tier} result=fault"
          printReason why
          bad := bad + 1
        | .ok copy =>
          let tipText := copy.getD ""
          let (result, reasons) := judgeBase baseText copy.isSome tipText
          IO.println s!"scoreboard: base={short} tier={tier} result={result}"
          for r in reasons do printReason r
          -- A pass prints what it credited, where a human sanctions each weakening.
          if result == "ok" then
            for c in creditsOf baseText tipText do printReason c
          if result != "ok" then bad := bad + 1
  -- Every tier file the base does not carry, judged alone.
  for p in ← treeBaselines do
    if known.contains p then continue
    let tier := shownName (((System.FilePath.mk p).fileStem).getD p)
    let (result, reasons) := match ← treeCopy p with
      | .error why => ("fault", #[why])
      | .ok none => ("fault", #[s!"{p} was listed in the tree and could not be read"])
      | .ok (some text) => judgeNew text
    IO.println s!"scoreboard: base={short} tier={tier} result={result}"
    printReason "new since the base: no floor there to hold it to, so it is judged alone — \
its format, and any request it still holds"
    for r in reasons do printReason r
    if result != "ok" then bad := bad + 1
  return (if bad == 0 then 0 else 1)

/-- Constructs held back and per-tier deficits, which have no single cross-tier
ranking. -/
def queue (limit : Nat) : IO UInt32 := do
  let mut lines : Array String := #[]
  -- The committed blocker ranking, read when present.
  let blockers ← readFileOr "testdata/coverage/blockers.tsv"
  if blockers.isEmpty then
    lines := lines.push "queue: group 1 of 2 — no testdata/coverage/blockers.tsv, so no \
construct ranking (the coverage tier writes it)"
  else
    -- blockers.tsv rows: `kind⇥construct⇥owner⇥sole⇥share⇥docs`, untrimmed; others stop the queue.
    let mut rows : Array (String × String × String × Nat × Nat × Nat) := #[]
    let mut faults : Array String := #[]
    let mut lineNo := 0
    for l in blockers.splitOn "\n" do
      lineNo := lineNo + 1
      if l.startsWith "#" || l.isEmpty then continue
      match l.splitOn "\t" with
      | ["kind", "construct", "owner", "sole", "share", "docs"] => continue
      | [kind, construct, owner, sole, share, docs] =>
        match sole.toNat?, share.toNat?, docs.toNat? with
        | some s, some h, some d =>
          if !["ctrl", "env", "aggregate"].contains kind then
            faults := faults.push s!"line {lineNo}: kind '{kind}' is not ctrl, env or aggregate"
          else if construct.isEmpty || owner.isEmpty then
            faults := faults.push s!"line {lineNo}: an empty construct or owner"
          else rows := rows.push (kind, construct, owner, s, h, d)
        | _, _, _ => faults := faults.push s!"line {lineNo}: sole, share and docs must be integers"
      | fs => faults := faults.push s!"line {lineNo}: {fs.length} tab-separated field(s), want 6"
    if !faults.isEmpty then
      for f in faults do IO.eprintln s!"queue: testdata/coverage/blockers.tsv {f}"
      IO.eprintln "queue: the blocker table is malformed, so no queue is printed from it"
      return 2
    let named := rows.filter (·.1 != "aggregate")
    lines := lines.push s!"queue: group 1 of 2 — constructs nothing answers, by the \
documents they alone block ({named.size} ranked; {rows.size - named.size} aggregate \
row(s) of names the table does not publish)"
    for (kind, construct, owner, sole, share, docs) in named.toList.take 5 do
      lines := lines.push s!"queue: blocker {kind}:{construct} owner={owner} sole={sole} \
share={share} docs={docs}"
  lines := lines.push "queue: group 2 of 2 — each tier's worst items, in its own \
units; not comparable across tiers"
  let (tiers, misnamed) ← discover
  for m in misnamed do
    lines := lines.push s!"queue: testdata/scoreboard/{shownName m}.tsv not ranked: its name is \
not a tier name ([a-z0-9-]+), which --check faults"
  for t in tiers do
    let text ← readFileOr (tsvPath t)
    if text.isEmpty then continue
    match parse text with
    | .error e => lines := lines.push s!"queue: tier {t} unreadable: {e}"
    | .ok tsv =>
      -- Faults about a tier's row set, reported in the queue too.
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

/-- The modules a source imports: its `import` lines before its first line of code. -/
def headerImports (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut depth := 0
  for line in text.splitOn "\n" do
    let t := ((line.splitOn " --").headD "").trimAscii.toString
    if depth > 0 || t.startsWith "/-" then
      depth := depth + ((t.splitOn "/-").length - 1) - ((t.splitOn "-/").length - 1)
      continue
    if t.isEmpty || t.startsWith "--" || t == "module" then continue
    let words := (t.splitOn " ").filter (!·.isEmpty)
    unless words.contains "import" do break
    if let some m := words.getLast? then out := out.push m
  return out

/-- What `lake build`'s default targets leave built: the toolchain's modules and the
`LeanTex` library. -/
def defaultBuilt (m : String) : Bool :=
  ["Init", "Std", "Lean", "Lake", "LeanTex"].any fun r => m == r || m.startsWith (r ++ ".")

/-- Delegate to the benchmark driver, after `lake build`: the comparison with lualatex,
then the reference documents' cost; neither is a gate. -/
def benchReport : IO UInt32 := do
  IO.println "scoreboard: bench is a report, never a gate (it runs lualatex and times this host)."
  let built ← IO.Process.output { cmd := "lake", args := #["build"] }
  if built.exitCode != 0 then
    IO.eprint built.stdout
    IO.eprint built.stderr
    IO.eprintln "scoreboard: lake build failed, so the bench has nothing to time"
    return 1
  let mut code : UInt32 := 0
  for mode in [#[], #["--doc-cost"]] do
    let out ← IO.Process.output
      { cmd := "lake", args := #["env", "lean", "--run", "scripts/bench.lean"] ++ mode }
    IO.print out.stdout
    if out.exitCode != 0 then
      IO.eprint out.stderr
      code := out.exitCode
  return code

def fixture (name : String) : String := s!"testdata/scoreboard/selftest/{name}.tsv"

/-- Hand-written committed baselines, each naming the fault `validate` must find in it. -/
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

/-- Committed baselines `validate` must accept, each a state the tool writes or asks a
human to write. -/
def wellFormed : List String :=
  ["clean", "retired", "retired-pending", "lowered", "lowered-applied",
   "lowered-reauth", "lowered-second", "chain", "chain-gap", "tier-retired"]

/-- The base check's cases: the base's file, the tree's file, and the verdict. -/
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
   ("clean", "lowered-unheld", "fault"),
   ("clean", "duplicate", "fault"),
   -- A request the base holds is unspent there, so the regeneration's record pays.
   ("lowered", "lowered-applied", "ok"),
   ("retired-pending", "retired", "ok"),
   ("lowered", "lowered", "stale"),
   ("lowered", "clean", "ok")]

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

/-- The tier every harness repository carries: a producer whose `--check` always exits 0,
so the exit status is the base check's alone, over a raw baseline of two rows. -/
def probeTier : String := "zz-probe"

def probeText : String := "# encoding: raw\nalpha\t5\nbravo\t3\n"

/-- A producer whose `--check` passes whatever its baseline says. -/
def trivialProducer : String := "def main (_ : List String) : IO UInt32 := pure 0\n"

/-- A producer whose `--check` passes only when git refuses a network transport before
connecting. -/
def nonetProducer : String :=
  "def main (_ : List String) : IO UInt32 := do\n" ++
  "  let o ← IO.Process.output\n" ++
  "    { cmd := \"git\", args := #[\"ls-remote\", \"https://127.0.0.1:9/probe.git\"]\n" ++
  "      env := #[(\"http_proxy\", none), (\"https_proxy\", none), (\"HTTP_PROXY\", none),\n" ++
  "        (\"HTTPS_PROXY\", none), (\"ALL_PROXY\", none), (\"all_proxy\", none)] }\n" ++
  "  return if (o.stderr.splitOn \"transport 'https' not allowed\").length > 1 then 0 else 1\n"

/-- One harness case: files committed at the base, the edit making the tree, the exit
status `scoreboard --check --base <base>` must return, and lines its output must hold. -/
structure CliCase where
  label : String
  extra : List (String × String)
  /-- Commit the baselines here, then move them to the current root before editing. -/
  baseRoot : String := baselineDir
  edit : System.FilePath → String → IO Unit
  exit : UInt32
  says : String → List String
  /-- Fragments no line of the output may hold. -/
  absent : List String := []

/-- Replace `old` in a harness file, failing the case when the file does not hold it. -/
def swapIn (dir : System.FilePath) (path old new : String) : IO Unit := do
  let s ← IO.FS.readFile (dir / path)
  unless containsSub s old do throw (IO.userError s!"{path} holds no '{old}'")
  IO.FS.writeFile (dir / path) (s.replace old new)

/-- git in a harness repository through the guard (`hgitRun`): its output, or an error. -/
def harnessGit (dir : System.FilePath) (args : Array String) : IO String := do
  let o ← hgitRun args dir.toString
  if o.exitCode != 0 then
    throw (IO.userError s!"git {String.intercalate " " args.toList} exited {o.exitCode}: \
{o.stderr.trimAscii.toString}")
  return o.stdout.trimAscii.toString

/-- Make the blob `path` holds at `sha` unreadable, as an unreachable promisor leaves
it. -/
def unreadable (dir : System.FilePath) (sha path : String) : IO Unit := do
  let oid ← harnessGit dir #["rev-parse", s!"{sha}:{path}"]
  IO.FS.removeFile (dir / ".git" / "objects" / (oid.take 2).toString / (oid.drop 2).toString)

/-- `git replace <old> <new>` in a harness repository, read back through replacement-on
git so the case cannot pass without it. -/
def replaceIn (dir : System.FilePath) (old new : String) (probe : Array String)
    (holds : String → Bool) : IO Unit := do
  let _ ← harnessGit dir #["replace", old, new]
  unless holds (← harnessGit dir probe) do
    throw (IO.userError s!"the replace ref {old} → {new} is not in effect")

/-- The cases: each refusal a way the base check could fail open, each pass a sanctioned
act. -/
def cliCases : List CliCase :=
  let probe := tsvPath probeTier
  let enc := "# encoding: raw\n"
  let says (word : String) := fun (s : String) =>
    [s!"scoreboard: base={s} tier={probeTier} result={word}"]
  let request := "# lowered: alpha 5→4 — an invented reason\n"
  let trivial := trivialProducer
  let fall := fun d => swapIn d probe "alpha\t5\n" "alpha\t4\n"
  -- A passing run prints each weakening and each new line paying for one.
  let credits (lines : List String) := fun (s : String) =>
    says "ok" s ++ lines.map (s!"scoreboard:   " ++ ·)
  let record := "# lowered (applied): alpha 5→4 — an old reason\n"
  [{ label := "nothing moved", extra := [], edit := fun _ _ => pure (), exit := 0
     says := says "ok", absent := ["credited:", "moved:"] },
   { label := "baseline directory moved", extra := [], baseRoot := "tests/scoreboard"
     edit := fun _ _ => pure (), exit := 0, says := says "ok"
     absent := ["new since the base:"] },
   { label := "directory move cannot reset a floor", extra := [], baseRoot := "tests/scoreboard"
     edit := fun d _ => fall d, exit := 1, says := says "laundered" },
   { label := "directory move cannot hide a deleted tier", extra := []
     baseRoot := "tests/scoreboard"
     edit := fun d _ => do
       IO.FS.removeFile (d / probe)
       IO.FS.removeFile (d / scriptPath probeTier)
     exit := 1, says := says "fault" },
   { label := "two committed roots cannot define one tier"
     extra := [("tests/scoreboard/zz-probe.tsv", probeText)]
     edit := fun _ _ => pure (), exit := 1, says := says "fault" },
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
   -- A request naming a floor the file no longer holds does not validate.
   { label := "an unapplied request beside the fall it names", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ request)
       fall d
     exit := 1, says := says "fault" },
   { label := "a fall paid by a new record", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ "# lowered (applied): alpha 5→4 — an invented reason\n")
       fall d
     exit := 0
     says := credits ["moved: alpha 5 → 4",
       "credited: # lowered (applied): alpha 5→4 — an invented reason"] },
   { label := "a vanish paid by a new retirement", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ "# retired: bravo — an invented reason\n")
       swapIn d probe "bravo\t3\n" ""
     exit := 0
     says := credits ["moved: bravo 3 → gone", "credited: # retired: bravo — an invented reason"] },
   { label := "a tier retired by a new tombstone", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / probe) "# retired-tier: an invented reason\n"
       IO.FS.removeFile (d / scriptPath probeTier)
     exit := 0
     says := credits ["moved: the tier's 2 rows → gone", "credited: # retired-tier: an invented reason"] },
   -- Two credits a human decides on: a copied base record, and a line naming another fall.
   { label := "a fall paid by a copy of a record the base carries"
     extra := [(probe, enc ++ record ++ "alpha\t5\nbravo\t3\n")]
     edit := fun d _ => do
       swapIn d probe record (record ++ record)
       fall d
     exit := 0
     says := credits ["moved: alpha 5 → 4",
       "credited: # lowered (applied): alpha 5→4 — an old reason (the same text as a line \
the base carries)"] },
   { label := "a fall paid by a line naming another fall", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ "# lowered (applied): alpha 1000→0 — an invented reason\n")
       fall d
     exit := 0
     says := credits ["moved: alpha 5 → 4",
       "credited: # lowered (applied): alpha 1000→0 — an invented reason"] },
   -- Text a file supplies reaches the screen as text, terminal controls spelled out.
   { label := "a fall paid by a record whose reason carries terminal controls", extra := []
     edit := fun d _ => do
       swapIn d probe enc (enc ++ "# lowered (applied): alpha 5→4 — x\x1b[1A\x1b[2K\x9bforged\n")
       fall d
     exit := 0
     says := credits ["moved: alpha 5 → 4",
       "credited: # lowered (applied): alpha 5→4 — x\\u{1b}[1A\\u{1b}[2K\\u{9b}forged"]
     absent := ["\x1b", "\x9b"] },
   { label := "a producer that fails printing terminal controls", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / scriptPath "zz-noisy")
         "def main (_ : List String) : IO UInt32 := do\n  IO.eprintln \"x\\x1b[2Ky\"\n  pure 1\n"
       IO.FS.writeFile (d / tsvPath "zz-noisy") (enc ++ "alpha\t5\n")
     exit := 1, says := fun _ => ["scoreboard:   exit 1; x\\u{1b}[2Ky"], absent := ["\x1b"] },
   -- A base blob git cannot read, simulated by deleting the loose object.
   { label := "the base's blob unreadable, a fall edited by hand", extra := []
     edit := fun d sha => do
       unreadable d sha probe
       fall d
     exit := 1, says := says "fault" },
   { label := "the base's blob unreadable, nothing moved", extra := []
     edit := fun d sha => unreadable d sha probe, exit := 1, says := says "fault" },
   -- A name git quotes, deleted with its producer.
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
     exit := 1, says := fun _ => ["scoreboard: tier=zz%C3%A9 items=0 regressed=0 improved=0 result=fault"] },
   -- A directory named like a baseline at the base holds no floor to read.
   { label := "a directory named like a baseline at the base"
     extra := [("testdata/scoreboard/zz-dir.tsv/inner", "an invented file\n")]
     edit := fun d _ => IO.FS.removeDirAll (d / "testdata/scoreboard/zz-dir.tsv")
     exit := 1, says := fun s => [s!"scoreboard: base={s} tier=zz-dir result=fault"] },
   -- A producer the harness starts reaches git with no network transport.
   { label := "a producer's git cannot use a network transport"
     extra := [(tsvPath "zz-nonet", "# encoding: raw\nalpha\t1\n"),
       (scriptPath "zz-nonet", nonetProducer)]
     edit := fun _ _ => pure (), exit := 0
     says := fun s => [s!"scoreboard: base={s} tier={probeTier} result=ok",
       "scoreboard: tier=zz-nonet items=0 regressed=0 improved=0 result=ok"] },
   -- A replace ref swaps a blob, a tree or a commit; one case per kind of object the check reads.
   { label := "a replace ref swaps the base's blob for one already holding the fall"
     extra := []
     edit := fun d sha => do
       let old ← harnessGit d #["rev-parse", s!"{sha}:{probe}"]
       IO.FS.writeFile (d / ".git" / "zz-stand-in") "# encoding: raw\nalpha\t4\nbravo\t3\n"
       let new ← harnessGit d #["hash-object", "-w", ".git/zz-stand-in"]
       replaceIn d old new #["cat-file", "blob", old] (containsSub · "alpha\t4")
       fall d
     exit := 1, says := says "laundered" },
   { label := "a replace ref swaps the base's tree for one without a deleted baseline"
     extra := [(tsvPath "zz-del", "# encoding: raw\nalpha\t3\n"), (scriptPath "zz-del", trivial)]
     edit := fun d sha => do
       let old ← harnessGit d #["rev-parse", s!"{sha}:testdata/scoreboard"]
       let _ ← harnessGit d #["rm", "--cached", "-q", tsvPath "zz-del"]
       let new ← harnessGit d #["write-tree", "--prefix=testdata/scoreboard/"]
       replaceIn d old new #["ls-tree", "--name-only", sha, "testdata/scoreboard/"]
         (!containsSub · "zz-del")
       IO.FS.removeFile (d / tsvPath "zz-del")
       IO.FS.removeFile (d / scriptPath "zz-del")
     exit := 1, says := fun s => [s!"scoreboard: base={s} tier=zz-del result=fault"] },
   { label := "a replace ref swaps the base commit for one already holding the fall"
     extra := []
     edit := fun d sha => do
       fall d
       let _ ← harnessGit d #["add", probe]
       let tree ← harnessGit d #["write-tree"]
       let new ← harnessGit d #["commit-tree", tree, "-m", "a stand-in for the base"]
       replaceIn d sha new #["cat-file", "blob", s!"{sha}:{probe}"] (containsSub · "alpha\t4")
     exit := 1, says := says "laundered" },
   -- A tier file the base does not carry must still read as the format and hold no request.
   { label := "an unapplied request in a tier new since the base", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / scriptPath "zz-new") trivial
       IO.FS.writeFile (d / tsvPath "zz-new") (enc ++ request ++ "alpha\t5\n")
     exit := 1, says := fun s => [s!"scoreboard: base={s} tier=zz-new result=stale"] },
   { label := "a retirement beside its row in a tier new since the base", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / scriptPath "zz-new") trivial
       IO.FS.writeFile (d / tsvPath "zz-new")
         (enc ++ "# retired: alpha — an invented reason\nalpha\t5\nbravo\t2\n")
     exit := 1, says := fun s => [s!"scoreboard: base={s} tier=zz-new result=stale"] },
   { label := "a duplicate row in a tier new since the base", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / scriptPath "zz-new") trivial
       IO.FS.writeFile (d / tsvPath "zz-new") (enc ++ "alpha\t5\nalpha\t4\n")
     exit := 1, says := fun s => [s!"scoreboard: base={s} tier=zz-new result=fault"] },
   { label := "a clean tier new since the base", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / scriptPath "zz-new") trivial
       IO.FS.writeFile (d / tsvPath "zz-new") (enc ++ "alpha\t5\n")
     exit := 0
     says := fun s => [s!"scoreboard: base={s} tier=zz-new result=ok",
       "scoreboard:   new since the base: no floor there to hold it to, so it is judged \
alone — its format, and any request it still holds"] },
   -- The tree's own copy reads as the format too: a duplicated item hides a fall.
   { label := "a fall hidden behind a duplicate row", extra := []
     edit := fun d _ => swapIn d probe "alpha\t5\n" "alpha\t5\nalpha\t4\n"
     exit := 1, says := says "fault" },
   -- Only a regular file is a floor git commits; a symlink is refused.
   { label := "the tree's copy of a baseline is a symlink to the same text", extra := []
     edit := fun d _ => do
       IO.FS.writeFile (d / "zz-elsewhere.tsv") probeText
       IO.FS.removeFile (d / probe)
       let o ← IO.Process.output
         { cmd := "ln", args := #["-s", "../../zz-elsewhere.tsv", probe], cwd := some d }
       unless o.exitCode == 0 do throw (IO.userError s!"ln exited {o.exitCode}")
     exit := 1, says := says "fault" },
   -- A request the base holds stales every landing until spent, and spending it passes.
   { label := "a request the base holds, the tree unchanged"
     extra := [(probe, enc ++ request ++ "alpha\t5\nbravo\t3\n")]
     edit := fun _ _ => pure (), exit := 1, says := says "stale" },
   { label := "a request the base holds, spent as the tool spends it"
     extra := [(probe, enc ++ request ++ "alpha\t5\nbravo\t3\n")]
     edit := fun d _ => do
       swapIn d probe request "# lowered (applied): alpha 5→4 — an invented reason\n"
       fall d
     exit := 0
     says := credits ["moved: alpha 5 → 4",
       "credited: # lowered (applied): alpha 5→4 — an invented reason (spends the request the \
base carries)"] },
   { label := "a request the base holds, deleted"
     extra := [(probe, enc ++ request ++ "alpha\t5\nbravo\t3\n")]
     edit := fun d _ => swapIn d probe request "", exit := 0
     says := says "ok", absent := ["credited:", "moved:"] },
   { label := "a retirement the base holds, spent as the tool spends it"
     extra := [(probe, enc ++ "# retired: bravo — an invented reason\nalpha\t5\nbravo\t3\n")]
     edit := fun d _ => swapIn d probe "bravo\t3\n" "", exit := 0
     says := credits ["moved: bravo 3 → gone",
       "credited: # retired: bravo — an invented reason (spends the request the base carries)"] }]

/-- Lay out one harness repository in `dir`, under the guarded root, commit the base, make the
tree by the case's edit, and run the scoreboard under test there: `none` when it answered as
the case says. -/
def runCliCase (bin toolchain : String) (dir : System.FilePath) (c : CliCase) :
    IO (Option String) := do
  try
    IO.FS.createDirAll (dir / baselineDir)
    IO.FS.createDirAll (dir / "scripts")
    IO.FS.writeFile (dir / "lean-toolchain") toolchain
    for t in declaredTiers do
      IO.FS.writeFile (dir / tsvPath t) "# retired-tier: a synthetic harness, nothing measured\n"
    IO.FS.writeFile (dir / scriptPath probeTier) trivialProducer
    IO.FS.writeFile (dir / tsvPath probeTier) probeText
    for (p, text) in c.extra do
      if let some parent := (dir / p).parent then IO.FS.createDirAll parent
      IO.FS.writeFile (dir / p) text
    if c.baseRoot != baselineDir then
      if let some parent := (dir / c.baseRoot).parent then IO.FS.createDirAll parent
      IO.FS.rename (dir / baselineDir) (dir / c.baseRoot)
    let _ ← harnessGit dir #["init", "-q", "-b", "main", "."]
    let _ ← harnessGit dir #["config", "user.name", "probe"]
    let _ ← harnessGit dir #["config", "user.email", "probe@example.org"]
    let _ ← harnessGit dir #["add", "-A"]
    let tree ← harnessGit dir #["write-tree"]
    let sha ← harnessGit dir #["commit-tree", tree, "-m", s!"harness base: {c.label}"]
    if c.baseRoot != baselineDir then
      IO.FS.rename (dir / c.baseRoot) (dir / baselineDir)
    c.edit dir sha
    let o ← runToolRun bin dir.toString #["--check", "--base", sha] #[]
    let lines := (o.stdout.splitOn "\n").map (·.trimAscii.toString)
    let shown := String.intercalate "\n    " ((lines.filter (containsSub · "zz")).take 8)
    if o.exitCode != c.exit then
      return some s!"cli {c.label}: exit {o.exitCode}, wanted {c.exit}\n    {shown}"
    for l in c.says (sha.take 12).toString do
      unless lines.contains l do
        return some s!"cli {c.label}: no line '{l}'\n    {shown}"
    for frag in c.absent do
      if lines.any (containsSub · frag) then
        return some s!"cli {c.label}: a line holds '{frag}'\n    {shown}"
    return none
  catch e =>
    return some s!"cli {c.label}: the harness could not run: {e}"
  finally
    IO.FS.removeDirAll dir

/-- This binary, the scoreboard under test; interpreted, the process is `lean`, and the
selftest says so. -/
def selfBinary : IO (Except String String) := do
  let bin ← IO.appPath
  if bin.fileName == some "scoreboard" then return .ok bin.toString
  return .error s!"the selftest drives its own binary and this process is {bin}; run the \
compiled one: lake build scoreboard && .lake/build/bin/scoreboard --selftest"

/-- Every case, in parallel, against this binary, each in its own directory under `root`. -/
def cliFailures (root : System.FilePath) : IO (Array String) := do
  let bin ← match ← selfBinary with
    | .ok b => pure b
    | .error e => return #[s!"cli: {e}"]
  let toolchain ← readFileOr "lean-toolchain"
  let mut tasks := #[]
  for (c, i) in cliCases.zipIdx do
    tasks := tasks.push
      (← IO.asTask (prio := .dedicated) (runCliCase bin toolchain (root / s!"case-{i}") c))
  let mut out := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok none => pure ()
    | .ok (some why) => out := out.push why
    | .error e => out := out.push s!"cli: {e}"
  return out

/-- The HTML key of a corpus directory as this binary's `--key` computes it, under the
environment as it stands and under one that looks nothing alike. -/
def keyUnderHosts (dir : System.FilePath) : IO (Except String (String × String)) := do
  let bin ← match ← selfBinary with
    | .ok b => pure b
    | .error e => return .error e
  let host ← IO.FS.createTempDir
  try
    let other := host / "elsewhere.otf"
    IO.FS.writeBinFile other (← IO.FS.readBinFile "testdata/corpus/fonts/SourceSerifPro-Regular.otf")
    let keyUnder (env : Array (String × Option String)) : IO String := do
      let o ← IO.Process.output { cmd := bin, args := #["--key", dir.toString], env }
      return if o.exitCode == 0 then o.stdout.trimAscii.toString
        else s!"exit {o.exitCode}: {o.stderr.trimAscii.toString}"
    let ambient ← keyUnder #[]
    let hostile ← keyUnder #[("LEANTEX_FONT", some other.toString),
      ("LEANTEX_FONT_PATH", some host.toString), ("HOME", some host.toString),
      ("XDG_CACHE_HOME", some host.toString), ("PATH", some host.toString),
      ("TZ", some "Pacific/Kiritimati"), ("LC_ALL", some "C"), ("LANG", some "C")]
    return .ok (ambient, hostile)
  finally
    IO.FS.removeDirAll host

/-- This binary's `--selftest` with its scratch parent inside a checkout made under `root`:
why it did not refuse to start or left the checkout or the parent changed; `none` when it held. -/
def enclosedRootFailure (root : System.FilePath) : IO (Option String) := do
  let bin ← match ← selfBinary with
    | .ok b => pure b
    | .error e => return some s!"enclosed root: {e}"
  let victim := root / "victim"
  IO.FS.createDirAll victim
  let _ ← harnessGit victim #["init", "-q", "-b", "main", "."]
  let _ ← harnessGit victim #["config", "user.name", "probe"]
  let _ ← harnessGit victim #["config", "user.email", "probe@example.org"]
  IO.FS.writeFile (victim / "base.txt") "base\n"
  let _ ← harnessGit victim #["add", "base.txt"]
  let _ ← harnessGit victim #["commit", "-qm", "Base"]
  let inside := victim / "scratch"
  IO.FS.createDirAll inside
  let state : IO (String × String × String) := do
    return (← harnessGit victim #["for-each-ref", "--format=%(objectname) %(refname)"],
      ← harnessGit victim #["status", "--porcelain", "--untracked-files=all"],
      ← IO.FS.readFile (victim / ".git" / "config"))
  let before ← state
  let o ← runToolRun bin victim.toString #["--selftest"]
    #[("SCOREBOARD_SCRATCH_DIR", some inside.toString), ("SCOREBOARD_NESTED", some "1")]
  let after ← state
  let left := (← inside.readDir).size
  let refused := containsSub (o.stdout ++ o.stderr) "is inside the checkout"
  if o.exitCode == 2 && refused && before == after && left == 0 then return none
  return some s!"enclosed root: exit {o.exitCode} refused={refused} left={left} \
unchanged={before == after}"

/-- The selftest's checks, every repository it makes under the guarded `root`. -/
def selftestIn (root : System.FilePath) : IO UInt32 := do
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

  -- Every malformation fires its own fault, named by kind.
  for (name, want) in malformations do
    let got ← readFixture name
    let msgs : Array String := match got with
      | .error e => #[e]
      | .ok t => validate t
    no s!"malformation {name}: nothing fired" (!msgs.isEmpty)
    no s!"malformation {name}: fired {joined msgs}, wanted '{want}'"
      (msgs.any (containsSub · want))
  -- Every state the tool writes, or asks a human to write, reads.
  for name in wellFormed do
    let t ← load name
    no s!"well-formed {name}: refused as {joined (validate t)}" (validate t).isEmpty
  -- A request held to another floor names its remedy.
  let unheld ← load "lowered-unheld"
  no s!"malformation lowered-unheld: names no remedy ({joined (validate unheld)})"
    ((validate unheld).any fun m =>
      containsSub m "mark it `# lowered (applied):`" && containsSub m "correct or delete it")

  -- A retired item still measured is the fault, not the retirement beside its row.
  let live ← load "retired-and-live"
  no s!"fresh: a retired item still measured is a fault ({joined (validateFresh live.rows (some live))})"
    ((validateFresh live.rows (some live)).any (containsSub · "retired and also measured"))
  no "fresh: the same measurement without the retired item is clean"
    (validateFresh (live.rows.filter (·.item != "alpha")) (some live)).isEmpty
  no "fresh: an empty measurement is a fault" (validateFresh #[] none == #["no rows"])
  no "fresh: a duplicate item is a fault"
    ((validateFresh #[{ item := "a", value := 1 }, { item := "a", value := 2 }] none).any
      (containsSub · "duplicate item"))

  -- The spec's format: no encoding line is gated and unranked, and an item may hold spaces.
  match ← readFixture "spec-no-encoding" with
  | .error e => no s!"spec format: a baseline with no encoding line is refused: {e}" false
  | .ok t =>
    no "spec format: no encoding line reads as unranked" (t.encoding.isNone && (deficits t).isEmpty)
  match ← readFixture "spec-spaced-item" with
  | .error e => no s!"spec format: an item holding a space is refused: {e}" false
  | .ok t =>
    no "spec format: the spaced item reads whole" (t.rows.any (·.item == "alpha bravo"))

  -- The four ratchet verdicts against the clean baseline, read off the structured changes.
  let verdicts : List (String × Bool × Bool) :=
    [("dropped", true, false),
     ("disappeared", true, false),
     -- `added` under a headroom cap: an unseen item below the cap is a fall.
     ("added", true, false),
     ("raised", false, true)]
  for (name, wantLoss, wantGain) in verdicts do
    let now ← load name
    let d := ratchet base now
    no s!"ratchet {name}: loss expected {wantLoss}, got {d.losses.size} \
({joined (d.losses.map (·.describe))})" (d.losses.isEmpty == !wantLoss)
    no s!"ratchet {name}: gain expected {wantGain}, got {d.gains.size}"
      (d.gains.isEmpty == !wantGain)
    -- Every one of the four fails `--check`, a rise included.
    no s!"ratchet {name}: --check must fail on any change" (!d.checkPasses)
  no "ratchet: an unchanged measurement is the only state --check passes"
    (ratchet base base).checkPasses

  -- Retirement through the tool: regenerating drops the row and leaves the line as the record.
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

  -- A headroom item new to the baseline enters at the cap, so new debt is a fall.
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
  -- A line carried forward never pays for a second fall, even between the same values.
  no "record: it authorises no further fall" (!(unauthorised applied (withAlpha fell 994)).isEmpty)
  let reauth ← load "lowered-reauth"
  no "record: carried past a recovery, it does not authorise the same fall again"
    (!(unauthorised reauth fell).isEmpty)
  -- A second fall: the first record is history; the new request meets the floor it left.
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

  -- The tool's own remedies followed to the end through `tierMainAt`, twice for each kind.
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
    -- A request no fall answers, which only the request arm of `stale` sees.
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

  -- The base check: a floor moved since the base needs a line written since the base.
  for (b, t, want) in baseCases do
    let (got, why) := judgeBase (← readFileOr (fixture b)) true (← readFileOr (fixture t))
    no s!"base {b} → {t}: {got} ({joined why}), wanted {want}" (got == want)
  let cleanText ← readFileOr (fixture "clean")
  no "base: a baseline gone from the tree is a fault" ((judgeBase cleanText false "").1 == "fault")
  let emptied := judgeBase cleanText true ""
  no s!"base: an emptied baseline is a fault that still names every row it would launder \
({joined emptied.2})"
    (emptied.1 == "fault" && (emptied.2.filter (containsSub · "is gone")).size == 3)
  no "base: an unreadable base is a fault" ((judgeBase "alpha\tnine\n" true cleanText).1 == "fault")
  -- A tier file new since the base is judged alone.
  let newVerdict (name : String) : IO String := return (judgeNew (← readFileOr (fixture name))).1
  no "new: a clean file new since the base passes" ((← newVerdict "clean") == "ok")
  no "new: a request it still holds is stale" ((← newVerdict "lowered") == "stale")
  no "new: a retirement beside its row is stale" ((← newVerdict "retired-pending") == "stale")
  no "new: a duplicate row is a fault" ((← newVerdict "duplicate") == "fault")
  no "new: a request naming a floor the file does not hold is a fault"
    ((← newVerdict "lowered-unheld") == "fault")
  no "new: an empty file is a fault" ((judgeNew "").1 == "fault")
  no "new: a tombstone passes" ((← newVerdict "tier-retired") == "ok")
  let l (o n : Int) : Lowered := { item := "alpha", old := o, new := n, why := "w", state := .applied }
  no "reach: with no lines the floor holds" (reach [] 998 == 998)
  no "reach: two records compose, in either order"
    (reach [l 998 995, l 995 990] 998 == 990 && reach [l 995 990, l 998 995] 998 == 990)
  no "reach: a rise between two records needs no line" (reach [l 998 995, l 999 990] 998 == 990)
  no "reach: a fall between two records that no line covers is not reached"
    (reach [l 998 995, l 994 990] 998 == 995)
  no "reach: a record below the floor is not usable" (reach [l 991 990] 998 == 998)
  -- What a pass prints: weakening only, and the new lines, carried ones not.
  let credit (b t : String) : IO (Array String) :=
    return creditsOf (← readFileOr (fixture b)) (← readFileOr (fixture t))
  no "credits: a rise is no weakening" (← credit "clean" "raised").isEmpty
  no "credits: a fall, and the record new since the base that pays it"
    ((← credit "clean" "lowered-applied") == #["moved: alpha 998 → 995",
      "credited: # lowered (applied): alpha 998→995 — an invented reason, so the fixture is \
self-contained"])
  no "credits: a record carried from the base is not credited"
    ((← credit "lowered-reauth" "reauth-tip") == #["moved: alpha 998 → 995"])
  no "credits: a new item below the cap is a weakening"
    ((← credit "clean" "added") == #["moved: delta entered at 3, below the cap 1000"])
  -- A record or dropped row spending a base request is credited, naming it.
  no s!"credits: a record spending the base's request ({joined (← credit "lowered" "lowered-applied")})"
    ((← credit "lowered" "lowered-applied") == #["moved: alpha 998 → 995",
      "credited: # lowered (applied): alpha 998→995 — an invented reason, so the fixture is \
self-contained (spends the request the base carries)"])
  no s!"credits: a row dropped for the base's retirement ({joined (← credit "retired-pending" "retired")})"
    ((← credit "retired-pending" "retired") == #["moved: alpha 998 → gone",
      "credited: # retired: alpha — the measurement it stood for is no longer made (spends \
the request the base carries)"])
  -- A request the landing did not add says so.
  let inherited := judgeBase (← readFileOr (fixture "lowered")) true (← readFileOr (fixture "lowered"))
  no s!"held: a request the base holds too says so ({joined inherited.2})"
    (inherited.2.any (containsSub · "the base holds it too"))
  let own := judgeBase cleanText true (← readFileOr (fixture "lowered"))
  no s!"held: a request new since the base does not ({joined own.2})"
    (own.2.size == 1 && !own.2.any (containsSub · "the base holds it too"))
  -- What the scoreboard prints of text it did not write.
  no "printable: a control is spelled out" (printable "a\x1bb\tc" == "a\\u{1b}b\\u{9}c")
  no "printable: a C1 control and DEL are spelled out" (printable "\x9b\x7f" == "\\u{9b}\\u{7f}")
  no "printable: a bidirectional override and a zero-width space are spelled out"
    (printable "a\u202Eb\u200Bc" == "a\\u{202e}b\\u{200b}c")
  no "printable: everything else passes unchanged"
    (printable "alpha 5→4 — é, 字" == "alpha 5→4 — é, 字")
  -- The same check through `scoreboard --check --base` in throwaway repositories.
  for why in ← cliFailures root do no why false
  let guarded ← try
      let _ ← harnessGit root #["-c", "core.pager=cat", "--version"]
      pure false
    catch _ => pure true
  no "harness: the cases' git runs through the guard, which refuses a global option" guarded
  unless (← IO.getEnv "SCOREBOARD_NESTED").isSome do
    if let some why ← enclosedRootFailure root then no why false

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

  -- The HTML key over a one-fixture corpus: a function of the files, moved by a sentence.
  let dir ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "OpenSans-Regular.ttf")
      (← IO.FS.readBinFile "testdata/corpus/fonts/OpenSans-Regular.ttf")
    let src := "\\documentclass{article}\n\\begin{document}\nAn invented sentence.\n\\end{document}\n"
    IO.FS.writeFile (dir / "probe.tex") src
    let k1 ← Hermetic.corpusKey dir
    let k2 ← Hermetic.corpusKey dir
    let keyed ← keyUnderHosts dir
    IO.FS.writeFile (dir / "probe.tex") (src.replace "invented" "different")
    let k3 ← Hermetic.corpusKey dir
    match k1, k2, k3 with
    | .ok a, .ok b, .ok c =>
      no "key: the same files give the same key" (a == b)
      no "key: a changed sentence moves it" (a != c)
      match keyed with
      | .error e => no s!"key: {e}" false
      | .ok (ambient, hostile) =>
        no s!"key: the binary's --key is the key ({ambient}, wanted {a})" (ambient == a)
        no s!"key: another host's environment moves it ({hostile}, wanted {a})" (hostile == a)
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

  -- Tier discovery: absence passes only while pending, and a landed pending name fails.
  let (tiers, misnamed) ← discover
  for m in misnamed do
    no s!"discovery: testdata/scoreboard/{shownName m}.tsv is not a tier name ([a-z0-9-]+), \
which --check faults" false
  for t in tiers do
    let hasTsv ← System.FilePath.pathExists (tsvPath t)
    let hasScript ← System.FilePath.pathExists (scriptPath t)
    -- A tombstone is a retired tier's whole record.
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
  -- The name rule, and a listing in which git quotes no name.
  no "name: the shipped names pass" (["compat", "zz-probe", "p5", "a-b"].all tierNameOk)
  no "name: anything outside [a-z0-9-]+ does not"
    (!(["", "zzé", "Compat", "a b", "a.b", "a_b", "a\tb"].any tierNameOk))
  no "name: a refused name prints as one token"
    (shownName "zzé" == "zz%C3%A9" && shownName "a b" == "a%20b" && shownName "compat" == "compat")
  let nul := (Char.ofNat 0).toString
  let listing := String.intercalate nul
    ["100644 blob 1111\ttestdata/scoreboard/compat.tsv", "040000 tree 2222\ttestdata/scoreboard/selftest",
     "100644 blob 3333\ttestdata/scoreboard/zzé.tsv", "120000 blob 4444\ttestdata/scoreboard/zz-link.tsv",
     "040000 tree 5555\ttestdata/scoreboard/zz-dir.tsv", "100644 blob 6666\ttestdata/scoreboard/notes.md", ""]
  no s!"listing: -z entries read as committed, and only a regular file is a baseline"
    (readListing listing == some #[.baseline "testdata/scoreboard/compat.tsv" "1111",
      .baseline "testdata/scoreboard/zzé.tsv" "3333",
      .notAFile "testdata/scoreboard/zz-link.tsv" "120000" "blob",
      .notAFile "testdata/scoreboard/zz-dir.tsv" "040000" "tree"])
  no "listing: an entry that does not read fails the whole listing"
    ((readListing s!"100644 blob\ttestdata/scoreboard/compat.tsv{nul}").isNone &&
      (readListing s!"testdata/scoreboard/compat.tsv{nul}").isNone)

  -- The bench imports only what `lake build` makes.
  no "bench: lake build's default targets are not the library and executable the bench's \
imports are judged against"
    (((← readFileOr "lakefile.toml").splitOn "\n").contains
      "defaultTargets = [\"LeanTex\", \"leantex\"]")
  let benchImports := headerImports (← readFileOr "scripts/bench.lean")
  let unbuilt := benchImports.filter (!defaultBuilt ·)
  no s!"bench: scripts/bench.lean imports {unbuilt}, which lake build does not build, so after \
the build its header asks for it fails, or runs a stale module"
    (!benchImports.isEmpty && unbuilt.isEmpty)
  no "bench: the import reader and its judge"
    (headerImports "/- a\n-/\nimport A\npublic import B.C -- why\n\ndef x := 1\nimport D\n" ==
        #["A", "B.C"] && !defaultBuilt "scripts.DocBench" && defaultBuilt "LeanTex.Core.Image" &&
      !defaultBuilt "LeanTexExtra" && defaultBuilt "Lean.Data.Json")

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
  -- Then every tier's own selftest, in parallel, after building their imports.
  if let some err ← buildImports then
    IO.eprintln s!"FAIL the tiers' imports do not build, so no tier's selftest can run: {err}"
    return 1
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

/-- The selftest under a fresh scratch root no repository encloses, in `SCOREBOARD_SCRATCH_DIR`
(else `/tmp`); exit 2 when none can be made. -/
def selftest : IO UInt32 := do
  let parent := (← IO.getEnv "SCOREBOARD_SCRATCH_DIR").getD "/tmp"
  match ← guardRoot parent "scoreboard-selftest" with
  | .error (.unmade p) =>
    IO.eprintln s!"scoreboard: no fresh scratch root could be made under {p}"
    return 2
  | .error (.enclosed _ why) =>
    IO.eprintln s!"scoreboard: {why}"
    return 2
  | .ok root =>
    try selftestIn (System.FilePath.mk root) finally
      try IO.FS.removeDirAll root catch _ => pure ()

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return (← selftest)
  if args.contains "--queue" then return (← queue 40)
  if args.contains "--bench" then return (← benchReport)
  match args.dropWhile (· != "--key") with
  | _ :: dir :: _ =>
    match ← Hermetic.corpusKey dir with
    | .ok k =>
      IO.println k
      return 0
    | .error e =>
      IO.eprintln s!"scoreboard: {e}"
      return 1
  | [_] =>
    IO.eprintln "scoreboard: --key needs a corpus directory"
    return 2
  | [] => pure ()
  match baseArg args with
  | none => aggregate (args.contains "--check")
  | some none =>
    IO.eprintln "scoreboard: --base needs a revision (the commit being landed onto)"
    return 2
  | some (some rev) =>
    let measured ← aggregate (args.contains "--check")
    let held ← baseCheck rev
    return (if measured == 0 && held == 0 then 0 else 1)
