/-
The performance histories under `testdata/perf/`: what a measurement produced,
appended run by run and committed, so a trend is a file and a regression is a
diff. The one history today is document builds' (`documents.tsv`, written by
`bench --doc-cost --record`). The format is meant to serve code builds' times
too, so that one reader reads them all; no such history exists yet, and its
rows will need the required `binary` field, an executable's hash, to name
something a module build has:

  # <provenance>
  run<TAB>commit<TAB>binary<TAB>host<TAB>item<TAB>value<TAB>unit

`run` is the UTC second the run started (`2026-10-09T03:12:45Z`), shared by
every row it wrote; `commit` is the measured tree's abbreviated commit, with
`+` when the tree held uncommitted changes — in the committed history, always a
clean commit `main` holds, so the row names a state anyone can check out after
the branch that measured it is gone (`recordable`); `binary` is the first twelve hex digits of the
SHA-256 of the executable measured, which a commit alone cannot name (a saved
or stale binary measures as some other tree); `host` names the class of
machine — system, architecture and logical cores — never the machine or its
processor; `value` is an integer in `unit`. A run's rows stand together, name
one commit, binary and host, and measure an item once. Nothing here gates:
these numbers depend on the host, and the scoreboard holds only the hermetic
ones. What a run is compared with is the latest earlier run on its host class
(`lastRun`), and a count near-deterministic enough to hold to a band is held to
±3% of it (`withinBand`) — a report, never a gate.
-/
import Std.Async.System

namespace PerfHistory

/-- `pct` is a ratio in hundredths: a growth of 3.8x is 380. -/
def units : List String := ["ms", "KiB", "B", "instr", "pct"]

structure Row where
  run : String
  commit : String
  binary : String
  host : String
  item : String
  value : Int
  unit : String
deriving BEq, Repr, Inhabited

def fieldOk (s : String) : Bool :=
  !s.isEmpty && !s.any fun c => c == '\t' || c == '\n' || c == '\r'

/-- `YYYY-MM-DDTHH:MM:SSZ`, which sorts as the time it names. -/
def runOk (s : String) : Bool :=
  let cs := s.toList.toArray
  cs.size == 20 && (List.range 20).all fun i =>
    let c := cs[i]!
    if i == 4 || i == 7 then c == '-'
    else if i == 10 then c == 'T'
    else if i == 13 || i == 16 then c == ':'
    else if i == 19 then c == 'Z'
    else c.isDigit

def hexOk (s : String) : Bool := s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

def commitOk (s : String) : Bool :=
  let core := if s.endsWith "+" then (s.dropEnd 1).toString else s
  7 ≤ core.length && core.length ≤ 40 && hexOk core

/-- Rows the committed history may hold: each names a clean commit. Which
commits `main` holds is git's to say at recording time (`onMain`). -/
def recordable (rows : Array Row) : Array String :=
  (rows.filter (·.commit.endsWith "+")).map fun r =>
    s!"run {r.run} measured a tree with uncommitted changes ({r.commit})"

def binaryOk (s : String) : Bool := s.length == 12 && hexOk s

def Row.faults (r : Row) : Array String := Id.run do
  let mut out := #[]
  for (name, v) in [("run", r.run), ("commit", r.commit), ("binary", r.binary), ("host", r.host),
      ("item", r.item), ("unit", r.unit)] do
    unless fieldOk v do out := out.push s!"{name} '{v}' is empty or holds a tab or line break"
  unless runOk r.run do out := out.push s!"run '{r.run}' is not YYYY-MM-DDTHH:MM:SSZ"
  unless commitOk r.commit do out := out.push s!"commit '{r.commit}' is not an abbreviated sha"
  unless binaryOk r.binary do
    out := out.push s!"binary '{r.binary}' is not twelve hex digits of a SHA-256"
  unless units.contains r.unit do
    out := out.push s!"unit '{r.unit}' is not one of {String.intercalate ", " units}"
  return out

/-- A row as its line, refused rather than written when it would not read back. -/
def Row.render (r : Row) : Except String String :=
  match r.faults.toList with
  | [] => .ok (String.intercalate "\t"
      [r.run, r.commit, r.binary, r.host, r.item, toString r.value, r.unit])
  | f :: _ => .error f

def parseRow (line : String) : Except String Row := do
  match line.splitOn "\t" with
  | [run, commit, binary, host, item, value, unit] =>
    let some value := value.toInt? | throw s!"value '{value}' is not an integer"
    let r : Row := { run, commit, binary, host, item, value, unit }
    match r.faults.toList with
    | [] => return r
    | f :: _ => throw f
  | fs => throw s!"{fs.length} tab-separated fields, want 7"

structure History where
  provenance : Array String
  rows : Array Row
deriving Inhabited

/-- Each run's rows together, naming one commit, binary and host, each item
once per run. Runs need not be in time order: two branches that each record a
run merge by union (`.gitattributes`), which keeps each side's run whole but
may put the later one first. -/
def check (rows : Array Row) : Array String := Id.run do
  let mut out := #[]
  let mut seen : Array String := #[]
  let mut closed : Array String := #[]
  for i in [0:rows.size] do
    let r := rows[i]!
    if i > 0 && rows[i-1]!.run != r.run then
      closed := closed.push rows[i-1]!.run
      seen := #[]
      if closed.contains r.run then out := out.push s!"run {r.run} resumes after another run began"
    if i > 0 && rows[i-1]!.run == r.run then
      let p := rows[i-1]!
      if p.commit != r.commit || p.binary != r.binary || p.host != r.host then
        out := out.push s!"run {r.run} names more than one commit, binary or host"
    if seen.contains r.item then out := out.push s!"run {r.run} measures '{r.item}' twice"
    seen := seen.push r.item
  return out

def parse (text : String) : Except String History := do
  let mut provenance := #[]
  let mut rows := #[]
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    if line.startsWith "#" then
      provenance := provenance.push line
      continue
    match parseRow line with
    | .ok r => rows := rows.push r
    | .error e => throw s!"line {n}: {e}"
  match (check rows).toList with
  | [] => return { provenance, rows }
  | f :: _ => throw f

/-- Read the history at `path`; a file not yet written is an empty history. -/
def read (path : System.FilePath) : IO (Except String History) := do
  let text ← if ← path.pathExists then IO.FS.readFile path else pure ""
  return (parse text).mapError fun e => s!"{path} does not read: {e}"

/-- Append one run's rows to the history at `path`, writing `header` first
when the file is new. The file must read before, and the run with it after: a
run that would not writes nothing. -/
def append (path : System.FilePath) (header : Array String) (run : Array Row) :
    IO (Except String Nat) := do
  let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
  let prior ← match parse old with
    | .ok h => pure h
    | .error e => return .error s!"{path} does not read: {e}"
  let mut lines : Array String := #[]
  for r in run do
    match r.render with
    | .ok l => lines := lines.push l
    | .error e => return .error s!"refusing to record {r.item}: {e}"
  match (check (prior.rows ++ run)).toList with
  | f :: _ => return .error s!"refusing to record the run: {f}"
  | [] => pure ()
  let head := if old.isEmpty then String.intercalate "\n" header.toList ++ "\n" else ""
  let sep := if old.isEmpty || old.endsWith "\n" then "" else "\n"
  IO.FS.writeFile path (old ++ sep ++ head ++ String.intercalate "\n" lines.toList ++ "\n")
  return .ok run.size

/-! ## Comparing runs -/

/-- The latest run in `rows` measured on `host`, other than `run`: its rows,
empty when there is none. Run names are UTC seconds, which sort as time. -/
def lastRun (rows : Array Row) (host run : String) : Array Row := Id.run do
  let mut best : Option String := none
  for r in rows do
    if r.host == host && r.run != run && (best.all (· < r.run)) then best := some r.run
  match best with
  | some b => rows.filter (·.run == b)
  | none => #[]

/-- `new` against `old` in basis points of `old`, rounded toward zero; `none`
when `old` is not positive, which no ratio can be read against. -/
def changeBp (old new : Int) : Option Int :=
  if old ≤ 0 then none else
    let mag : Int := ((new - old).natAbs * 10000 / old.toNat : Nat)
    some (if new ≥ old then mag else -mag)

/-- The band a near-deterministic count is held to: 3% of the earlier run's.
The noise it stands above: three sealed warm builds of the invented deck
spread their user-space instructions by under 0.5%, the other reference
documents' by under 0.2%. -/
def bandBp : Nat := 300

def withinBand (old new : Int) : Bool :=
  match changeBp old new with
  | some c => c.natAbs ≤ bandBp
  | none => false

/-- Basis points as a percentage to two places, `1.25%`. -/
def bpMag (bp : Nat) : String :=
  let frac := toString (bp % 100)
  s!"{bp / 100}.{if frac.length < 2 then "0" ++ frac else frac}%"

/-- Basis points as a signed percentage to two places, `+1.25%`. -/
def bpText (bp : Int) : String := (if bp < 0 then "-" else "+") ++ bpMag bp.natAbs

/-! ## What a run names -/

/-- The class of machine a run measured on, from the platform's own answers:
system, architecture and logical cores — what a reading of milliseconds or
parallel peaks needs — never a name, a processor model or a memory size that
would say more about the machine than that. -/
def host : IO String := do
  let system ← try
      let info ← Std.Async.System.getSystemInfo
      pure s!"{info.name.toLower} {info.machine}"
    catch _ => pure "unknown system"
  let cores ← try pure (← Std.Async.System.getCPUInfo).size catch _ => pure 0
  let clean := fun (s : String) => s.map fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c
  return clean s!"{system}; {cores} logical cores"

/-- The measured tree: `git`'s abbreviated head, `+` when anything is uncommitted. -/
def commit : IO (Option String) := do
  let head ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short=12", "HEAD"] }
  let status ← IO.Process.output { cmd := "git", args := #["status", "--porcelain"] }
  if head.exitCode != 0 || status.exitCode != 0 then return none
  let sha := head.stdout.trimAscii.toString
  return some (if status.stdout.trimAscii.isEmpty then sha else sha ++ "+")

/-- Whether `main` holds the checked-out commit, so a row naming it stays
checkable once the branch that measured it is rebased and gone. -/
def onMain : IO Bool := do
  for base in ["refs/heads/main", "refs/remotes/origin/main"] do
    let r ← IO.Process.output { cmd := "git", args := #["merge-base", "--is-ancestor", "HEAD", base] }
    if r.exitCode == 0 then return true
  return false

/-- The first twelve hex digits of the executable's SHA-256, from the
platform's own checksum tool (`sha256sum`, or `shasum -a 256` where that is
the one shipped): hashing a large executable in interpreted code would cost
more than the builds it names. -/
def binaryKey (path : System.FilePath) : IO (Option String) := do
  for (cmd, args) in [("sha256sum", #["--", path.toString]),
      ("shasum", #["-a", "256", "--", path.toString])] do
    try
      let out ← IO.Process.output { cmd, args }
      let digest := (out.stdout.splitOn " ").headD ""
      if out.exitCode == 0 && digest.length == 64 && hexOk digest then
        return some (digest.take 12).toString
    catch _ => pure ()
  return none

/-- The UTC second, from the system clock's own formatter. -/
def now : IO (Option String) := do
  let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
  let s := out.stdout.trimAscii.toString
  return if out.exitCode == 0 && runOk s then some s else none

/-- The format's own judges, each made to fail once: a row reads back as
itself; every field refused empty, with a tab, or malformed; a run split by
another, an item measured twice in one run and a run naming two binaries
refused; two whole runs accepted in either order; the comparison picks the
latest earlier run on the same host class, and the band holds 3% exactly. -/
def selftest : Array String := Id.run do
  let mut fails := #[]
  let r : Row := { run := "2026-10-09T03:12:45Z", commit := "0123456789ab", binary := "a1b2c3d4e5f6",
                   host := "linux x86_64; 8 logical cores", item := "deck-64/pdf/warm", value := 412,
                   unit := "ms" }
  match r.render with
  | .ok l =>
    match parseRow l with
    | .ok back => if back != r then fails := fails.push "a rendered row reads back changed"
    | .error e => fails := fails.push s!"a rendered row does not read back: {e}"
  | .error e => fails := fails.push s!"a valid row was refused: {e}"
  let empties : List Row := [{ r with run := "" }, { r with commit := "" }, { r with binary := "" },
    { r with host := "" }, { r with item := "" }, { r with unit := "" }]
  for e in empties do
    if e.render.toOption.isSome then fails := fails.push s!"an empty field rendered: {repr e}"
  let bad : List Row := [{ r with host := "a\tb" }, { r with item := "a\nb" },
    { r with run := "2026-10-09 03:12:45" }, { r with commit := "xyz" },
    { r with commit := "0123+" }, { r with binary := "a1b2c3" },
    { r with binary := "A1B2C3D4E5F6" }, { r with unit := "s" }]
  for e in bad do
    if e.render.toOption.isSome then fails := fails.push s!"a malformed field rendered: {repr e}"
  if (parseRow "a\tb").toOption.isSome then fails := fails.push "a short line read"
  if (parseRow "2026-10-09T03:12:45Z\t0123456\ta1b2c3d4e5f6\th\ti\tten\tms").toOption.isSome then
    fails := fails.push "a non-integer value read"
  if (parseRow "2026-10-09T03:12:45Z\t0123456\th\ti\t10\tms").toOption.isSome then
    fails := fails.push "a row without a binary read"
  let later := { r with run := "2026-10-10T00:00:00Z" }
  if !(check #[r, { r with item := "other" }, later]).isEmpty then
    fails := fails.push "two runs in order were refused"
  if !(check #[later, r]).isEmpty then
    fails := fails.push "two whole runs merged out of time order were refused"
  if (check #[r, later, { r with item := "other" }]).isEmpty then
    fails := fails.push "a run resumed after another was accepted"
  if (check #[r, r]).isEmpty then fails := fails.push "an item measured twice in one run was accepted"
  if (check #[r, { r with item := "other", binary := "f6e5d4c3b2a1" }]).isEmpty then
    fails := fails.push "a run naming two binaries was accepted"
  let dirty := { r with commit := "0123456789ab+" }
  if dirty.render.toOption.isNone then fails := fails.push "a tree with changes could not be named"
  if !(recordable #[r]).isEmpty || (recordable #[r, dirty]).isEmpty then
    fails := fails.push "the committed history's rule on uncommitted trees reads wrong"
  match parse s!"# provenance\n{(r.render.toOption.getD "")}\n" with
  | .ok h => if h.rows != #[r] || h.provenance.size != 1 then fails := fails.push "parse lost a line"
  | .error e => fails := fails.push s!"a valid history was refused: {e}"
  match parse "# provenance only\n" with
  | .ok h => if !h.rows.isEmpty then fails := fails.push "an empty history read rows"
  | .error e => fails := fails.push s!"an empty history was refused: {e}"
  let other := { r with run := "2026-10-11T00:00:00Z", host := "darwin arm64; 8 logical cores" }
  let rows := #[r, { r with item := "x" }, later, other]
  if lastRun rows r.host "2026-10-12T00:00:00Z" != #[later] then
    fails := fails.push "the comparison did not pick the latest run on the host class"
  if lastRun rows r.host later.run != #[r, { r with item := "x" }] then
    fails := fails.push "the comparison read the run it compares, or not all of an earlier one"
  if !(lastRun rows "linux aarch64; 8 logical cores" "2026-10-12T00:00:00Z").isEmpty then
    fails := fails.push "the comparison read another host class"
  if !(withinBand 1000 1030 && withinBand 1000 970 && !withinBand 1000 1031 &&
      !withinBand 1000 969 && !withinBand 0 0) then
    fails := fails.push "the band is not 3% exactly, both ways"
  if changeBp 1000 1031 != some 310 || changeBp 1000 969 != some (-310) || changeBp 0 5 != none then
    fails := fails.push "a change in basis points reads wrong"
  if bpText 125 != "+1.25%" || bpText (-7) != "-0.07%" || bpText 0 != "+0.00%" ||
      bpMag 72 != "0.72%" then
    fails := fails.push "a change prints wrong"
  return fails

end PerfHistory
