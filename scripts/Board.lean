/-
The scoreboard's core: one committed baseline per goal, each under a
ratchet. A tier is a file plus its only writer — `tests/scoreboard/<tier>.tsv`
and `scripts/<tier>.lean` — and the file is the whole claim: `#` lines for
provenance (tool versions, a date, the encoding; data, never gated), then
`item<TAB>integer` rows, higher is better, sorted and unique.

The ratchet, stated once here so every tier obeys the same one:

* a value that drops is a regression;
* a baselined item that disappears is a regression, unless the committed
  baseline already retires it by a `# retired: <item> — <why>` line;
* a new item enters at its measured value, and counts as an improvement;
* a value that rises is an improvement.

Retirement lives in the committed file rather than in a producer, because
only a human knows *why* a measurement stopped being worth making; a
producer carries the retirement lines forward untouched when it regenerates.

The encoding line is read by the queue, so a deficit is computed rather
than declared: `# encoding: headroom cap=<n>` means the value is
`cap - count` and the deficit is the count; `# encoding: pairs <part>/<whole>`
means items come in `<key>.<part>` / `<key>.<whole>` pairs and the deficit is
the gap; `# encoding: raw` means the value is the measurement and the
deficit is the distance from the tier's best item.

A "shrink is good" metric is encoded as headroom rather than as a raw count
because a ratchet can only point one way: with `higher is better` fixed for
every tier, one comparison serves all of them and no tier can quietly
invert the test.
-/
import scripts.Gate

namespace Scoreboard

/-- The headroom ceiling. Large enough that no debt this repository tracks
approaches it, so `cap - count` stays positive and a reader can subtract in
their head. Raising it would raise every headroom item at once, which the
ratchet would read as a fleet-wide improvement — so it is a constant, not a
knob. -/
def debtCap : Int := 1000

structure Row where
  item : String
  value : Int
deriving BEq, Inhabited

/-- How a tier's values relate to its measurements. Read off the `#
encoding:` line; the queue needs it to rank deficits. -/
inductive Encoding where
  | headroom (cap : Int)
  | pairs (part whole : String)
  | raw
deriving BEq, Inhabited

def Encoding.render : Encoding → String
  | .headroom cap => s!"headroom cap={cap}"
  | .pairs p w => s!"pairs {p}/{w}"
  | .raw => "raw"

structure Tsv where
  provenance : Array String
  rows : Array Row
  retired : Array (String × String)
  encoding : Encoding
deriving Inhabited

def tsvPath (tier : String) : String := s!"tests/scoreboard/{tier}.tsv"

def scriptPath (tier : String) : String := s!"scripts/{tier}.lean"

/-- The item's spelling: one token, so a porcelain line stays parseable by
splitting on whitespace. -/
def itemFaults (item : String) : Option String :=
  if item.isEmpty then some "an empty item name"
  else if item.toList.any (fun c => c == ' ' || c == '\t') then
    some s!"item '{item}' holds whitespace"
  else none

/-- `# retired: <item> — <why>`. The em dash is the separator the repository
already uses for a reason clause, and requiring it is what makes a
retirement with no reason a malformation rather than an item named
"foo — ". -/
def parseRetired (l : String) : Option (Except String (String × String)) :=
  let pre := "# retired:"
  if !l.startsWith pre then none
  else
    let rest := ((l.drop pre.length).toString).trimAscii.toString
    let parts := rest.splitOn "—"
    match parts with
    | [item, why] =>
      let item := item.trimAscii.toString
      let why := why.trimAscii.toString
      if item.isEmpty then some (.error "a retirement naming no item")
      else if why.isEmpty then some (.error s!"retirement of '{item}' gives no reason")
      else some (.ok (item, why))
    | _ => some (.error s!"malformed retirement '{rest}' (want `<item> — <why>`)")

def parseEncoding (l : String) : Option (Except String Encoding) :=
  let pre := "# encoding:"
  if !l.startsWith pre then none
  else
    let toks := (((l.drop pre.length).toString).splitOn " ").filter (!·.isEmpty)
    match toks with
    | ["raw"] => some (.ok .raw)
    | ["headroom", cap] =>
      match (cap.splitOn "cap=") with
      | ["", n] => match n.toInt? with
        | some v => some (.ok (.headroom v))
        | none => some (.error s!"headroom cap '{n}' is not an integer")
      | _ => some (.error s!"malformed headroom encoding '{cap}' (want `cap=<n>`)")
    | ["pairs", spec] =>
      match spec.splitOn "/" with
      | [p, w] =>
        if p.isEmpty || w.isEmpty then some (.error "pairs encoding names an empty part")
        else some (.ok (.pairs p w))
      | _ => some (.error s!"malformed pairs encoding '{spec}' (want `<part>/<whole>`)")
    | _ => some (.error s!"unknown encoding '{String.intercalate " " toks}'")

/-- Parse a baseline. Faults that stop a value being read at all throw;
faults about the *set* of rows are `validate`'s, so a caller can report
every one of them at once. -/
def parse (text : String) : Except String Tsv := do
  let mut provenance : Array String := #[]
  let mut rows : Array Row := #[]
  let mut retired : Array (String × String) := #[]
  let mut encoding : Option Encoding := none
  for raw in text.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty then continue
    if l.startsWith "#" then
      provenance := provenance.push l
      if let some r := parseRetired l then
        retired := retired.push (← r)
      if let some e := parseEncoding l then
        if encoding.isSome then throw "two `# encoding:` lines"
        encoding := some (← e)
      continue
    let fields := raw.splitOn "\t"
    match fields with
    | [item, value] =>
      let item := item.trimAscii.toString
      if let some f := itemFaults item then throw f
      match (value.trimAscii.toString).toInt? with
      | some v => rows := rows.push { item, value := v }
      | none => throw s!"item '{item}': value '{value.trimAscii.toString}' is not an integer"
    | _ => throw s!"'{l}' is not `item<TAB>integer` ({fields.length} tab-separated fields)"
  match encoding with
  | none => throw "no `# encoding:` line"
  | some enc => return { provenance, rows, retired, encoding := enc }

/-- Faults about the row set: order, uniqueness, and a retirement that
contradicts a live row. Reported together so one run names them all. -/
def validate (t : Tsv) : Array String := Id.run do
  let mut out : Array String := #[]
  if t.rows.isEmpty then out := out.push "no rows"
  for i in [1:t.rows.size] do
    let prev := t.rows[i-1]!.item
    let cur := t.rows[i]!.item
    if prev == cur then out := out.push s!"duplicate item '{cur}'"
    else if !(prev < cur) then
      out := out.push s!"item '{cur}' is out of order (after '{prev}')"
  let mut seenRetired : Array String := #[]
  for (item, _) in t.retired do
    if seenRetired.contains item then
      out := out.push s!"item '{item}' is retired twice"
    seenRetired := seenRetired.push item
    if t.rows.any (·.item == item) then
      out := out.push s!"item '{item}' is retired and also measured"
  return out

def Tsv.find? (t : Tsv) (item : String) : Option Int :=
  (t.rows.find? (·.item == item)).map (·.value)

def Tsv.isRetired (t : Tsv) (item : String) : Bool :=
  t.retired.any (·.1 == item)

/-- One verdict of the ratchet. -/
structure Delta where
  regressed : Array String
  improved : Array String
deriving Inhabited

/-- Compare a fresh measurement against the committed baseline. Retirement
is read off the *baseline*: the committed file is where a human writes why
a measurement stopped being made. -/
def ratchet (base now : Tsv) : Delta := Id.run do
  let mut regressed : Array String := #[]
  let mut improved : Array String := #[]
  for r in base.rows do
    match now.find? r.item with
    | some v =>
      if v < r.value then
        regressed := regressed.push s!"{r.item}: {r.value} → {v}"
      else if v > r.value then
        improved := improved.push s!"{r.item}: {r.value} → {v}"
    | none =>
      if !base.isRetired r.item then
        regressed := regressed.push s!"{r.item}: baselined at {r.value}, now absent"
  for r in now.rows do
    if (base.find? r.item).isNone then
      improved := improved.push s!"{r.item}: new at {r.value}"
  return { regressed, improved }

/-- Render a baseline: provenance first (retirement lines among it, carried
forward), then the sorted rows. -/
def render (provenance : Array String) (rows : Array Row) : String := Id.run do
  let sorted := rows.qsort (fun a b => a.item < b.item)
  let mut out := ""
  for p in provenance do
    out := out ++ p ++ "\n"
  for r in sorted do
    out := out ++ r.item ++ "\t" ++ toString r.value ++ "\n"
  return out

/-- The porcelain line a tier's `--check` prints and the aggregate reads
back. One line, one tier, parsed by splitting on whitespace — the same
discipline the repository applies to a claim about a page: read the
artifact, never the narration. -/
def tierLine (tier : String) (items regressed improved : Nat) (result : String) : String :=
  s!"scoreboard: tier={tier} items={items} regressed={regressed} \
improved={improved} result={result}"

def field (line key : String) : Option String :=
  let toks := (line.splitOn " ").filter (!·.isEmpty)
  (toks.find? (·.startsWith (key ++ "="))).map (fun t =>
    ((t.drop (key.length + 1)).toString))

/-- The tiers the scoreboard expects to exist. A name here with no `.tsv`
or no `scripts/<name>.lean` is reported `missing` rather than passed over:
a tier that vanishes is exactly the failure the whole file guards against.
Names beyond the ones this agent shipped are the siblings' tiers, declared
ahead of their arrival so their absence is visible. -/
def declaredTiers : List String :=
  ["commonmark", "compat", "coverage", "diagdebt", "htmlreader", "obligations",
   "parity", "purity"]

/-- Every tier: the declared names, plus any baseline committed under
`tests/scoreboard/` that no one declared (a sibling's tier, landed before
its name reached this list). Direct children only — a subdirectory holds
the selftest fixtures, which are inputs and not tiers. -/
def discover : IO (Array String) := do
  let mut names : Array String := declaredTiers.toArray
  let dir : System.FilePath := "tests/scoreboard"
  if ← dir.isDir then
    for e in ← dir.readDir do
      let p := e.fileName
      if p.endsWith ".tsv" then
        let name := (p.dropEnd ".tsv".length).toString
        if !names.contains name then names := names.push name
  return names.qsort (· < ·)

/-- A deficit per item, from the tier's own encoding. The ranking is
computed from committed data; nothing here is a list of what to do. -/
def deficits (t : Tsv) : Array (String × Int) := Id.run do
  let mut out : Array (String × Int) := #[]
  match t.encoding with
  | .headroom cap =>
    for r in t.rows do
      let d := cap - r.value
      if d > 0 then out := out.push (r.item, d)
  | .pairs part whole =>
    for r in t.rows do
      if r.item.endsWith ("." ++ whole) then
        let key := (r.item.dropEnd (whole.length + 1)).toString
        let got := (t.find? (key ++ "." ++ part)).getD 0
        let d := r.value - got
        if d > 0 then out := out.push (key, d)
  | .raw =>
    let mut best : Int := 0
    for r in t.rows do
      if r.value > best then best := r.value
    for r in t.rows do
      let d := best - r.value
      if d > 0 then out := out.push (r.item, d)
  return out.qsort (fun a b => a.2 > b.2)

-- ## Obligations, read as records

/-- The value of `-- <key>: <value>` when the line is one. The same five-field
form `scripts/owed.lean` reads; this is a second reader of it, because the
scoreboard is a library and that gate is an executable root. Routed: the
field reader belongs in `scripts/Gate.lean` beside `bannedWord`, which is
where the repository already puts a predicate two gates must agree on. -/
def fieldOf (l key : String) : Option String :=
  let t := l.trimAscii.toString
  let pre := "-- " ++ key ++ ":"
  if t.startsWith pre then some (((t.drop pre.length).toString).trimAscii.toString)
  else none

structure Ob where
  name : String
  owner : String
  blocker : String
  file : String
deriving Inhabited

/-- Every owed record staged under the obligations path. -/
def obligations : IO (Array Ob) := do
  let mut files : Array String := #[]
  if ← System.FilePath.pathExists "Obligations.lean" then
    files := files.push "Obligations.lean"
  if ← System.FilePath.isDir "Obligations" then
    for p in ← System.FilePath.walkDir "Obligations" do
      if p.toString.endsWith ".lean" then files := files.push p.toString
  let mut out : Array Ob := #[]
  for f in files do
    let lines := ((← IO.FS.readFile f).splitOn "\n").toArray
    for i in [0:lines.size] do
      if let some name := (lines[i]?).bind (fieldOf · "owed") then
        let owner := ((lines[i+1]?).bind (fieldOf · "owner")).getD "?"
        let blocker := ((lines[i+3]?).bind (fieldOf · "blocker")).getD "?"
        out := out.push { name, owner, blocker, file := f }
  return out

/-- Obligations whose blocker names no other open obligation: the ones a
proof attempt can start on today. Computed from the records, not listed. -/
def ready (obs : Array Ob) : Array Ob :=
  obs.filter fun o =>
    !obs.any fun p => p.name != o.name && containsSub o.blocker p.name

def today : IO String := do
  try
    let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d"] }
    return out.stdout.trimAscii.toString
  catch _ => return "unknown"

def readFileOr (p : String) : IO String := do
  if ← System.FilePath.pathExists p then IO.FS.readFile p else return ""

/-- The three modes every tier producer shares, so no tier can differ in
what its `--check` means:

* no argument — regenerate the baseline from a fresh measurement, carry the
  retirement lines forward, then report the ratchet against what was there
  before and exit non-zero if a value fell. Accepting a fall is a
  deliberate act: the writer sees the red exit beside the diff.
* `--check` — measure, compare against the committed baseline, write
  nothing. The gated mode: hermetic, in-repo data only.
* `--selftest` — the tier's own predicates against hand-written inputs.

`measure` returns the provenance lines specific to this tier (tool versions,
counts, whatever sizes the claim) and the rows. -/
def tierMain (tier : String) (enc : Encoding)
    (measure : IO (Array String × Array Row)) (selftest : IO UInt32)
    (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return (← selftest)
  let path := tsvPath tier
  let old := (← readFileOr path)
  let baseline : Option Tsv ←
    if old.isEmpty then pure none
    else match parse old with
      | .ok t =>
        let faults := validate t
        if faults.isEmpty then pure (some t)
        else
          IO.eprintln s!"scoreboard: {path} is malformed:"
          for f in faults do IO.eprintln s!"  {f}"
          return 2
      | .error e =>
        IO.eprintln s!"scoreboard: {path}: {e}"
        return 2
  let (extra, rows) ← measure
  let fresh : Tsv :=
    { provenance := #[], rows := rows.qsort (fun a b => a.item < b.item)
      retired := (baseline.map (·.retired)).getD #[], encoding := enc }
  let freshFaults := validate fresh
  if !freshFaults.isEmpty then
    IO.eprintln s!"scoreboard: the fresh {tier} measurement is malformed:"
    for f in freshFaults do IO.eprintln s!"  {f}"
    return 2
  if !args.contains "--check" then
    let mut header : Array String := #[
      s!"# generated by scripts/{tier}.lean — do not hand-edit; regenerate: \
lake env lean --run scripts/{tier}.lean",
      s!"# encoding: {enc.render}",
      s!"# date: {← today}"]
    for e in extra do header := header.push e
    for (item, why) in fresh.retired do
      header := header.push s!"# retired: {item} — {why}"
    IO.FS.writeFile path (render header fresh.rows)
    IO.println s!"scoreboard: wrote {path} ({fresh.rows.size} items)"
  let d : Delta := match baseline with
    | none =>
      { regressed := #[]
        improved := fresh.rows.map (fun r => s!"{r.item}: new at {r.value}") }
    | some b => ratchet b fresh
  for r in d.regressed do IO.eprintln s!"scoreboard: {tier} regressed: {r}"
  for i in d.improved do IO.println s!"scoreboard: {tier} improved: {i}"
  IO.println (tierLine tier fresh.rows.size d.regressed.size d.improved.size
    (if d.regressed.isEmpty then "ok" else "regressed"))
  return (if d.regressed.isEmpty then 0 else 1)

end Scoreboard
