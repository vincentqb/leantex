/-
The scoreboard's core: one committed baseline per goal, each under a
ratchet. A tier is a file plus its only writer — `tests/scoreboard/<tier>.tsv`
and `scripts/<tier>.lean` — and the file is the whole claim: `#` lines for
provenance (tool versions, a date, the encoding; data, never gated), then
`item<TAB>integer` rows, higher is better, sorted and unique.

The tier contract is the exit status of `--check`, and nothing else. That is
what PLAN's spec defines, so it is the only thing every tier's writer was
told about, and four writers built to it in parallel. Two things this
library likes are therefore optional, never gating:

* the porcelain line (`tierLine`) adds counts when a tier prints one, and
  can never turn a non-zero exit into a pass;
* the `# encoding:` line is a ranking hint — a baseline without one is
  gated like any other and the queue reports it as unranked.

An item may hold spaces: a row is split on its tab, and no consumer splits
an item on whitespace.

The ratchet, stated once here so every tier obeys the same one:

* a value that drops is a regression;
* a baselined item that disappears is a regression, unless the committed
  baseline already retires it by a `# retired: <item> — <why>` line;
* a value that **rises** fails `--check` too, unrecorded: record it by
  regenerating, in the commit that earned it. A floor allowed to lag the
  tree is a floor that admits a silent fall back to it, and the queue,
  which ranks from committed files, ranks on the stale number. It is the
  rule `subjectDebt` and `siteAccounting` already live under — read in both
  directions, so a row is a migration step and not a parking space;
* a new item enters at its measured value.

Regeneration is the only mode that writes, and it refuses to write a fall
unless the committed file carries a human-written
`# lowered: <item> <old>→<new> — <why>` line authorising exactly that fall.
Retirement and lowering both live in the committed file rather than in a
producer, because only a human knows *why* a measurement stopped being
worth making or a floor stopped being holdable; a producer carries both
kinds of line forward untouched.

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

/-- `# lowered: <item> <old>→<new> — <why>`. A fall is a human act: this
line is what lets a producer write one, and it authorises exactly the fall
it names. The item may hold spaces, so the arrow pair is read as the last
token before the reason. -/
structure Lowered where
  item : String
  old : Int
  new : Int
  why : String
deriving BEq, Inhabited

structure Tsv where
  provenance : Array String
  rows : Array Row
  retired : Array (String × String)
  /-- The falls a human authorised, each naming its own old and new value.
  Carried forward when a producer regenerates, so the file reads as the
  history of why its floor moved. -/
  lowered : Array Lowered
  /-- `none`: the tier declares no encoding. It is gated like any other tier
  and the queue does not rank it — a missing hint for a report, not a
  malformed baseline. -/
  encoding : Option Encoding
deriving Inhabited

def tsvPath (tier : String) : String := s!"tests/scoreboard/{tier}.tsv"

def scriptPath (tier : String) : String := s!"scripts/{tier}.lean"

/-- The item's spelling. A row is split on its tab, so an item may hold
spaces — the spec permits them and two sibling tiers use them — and the
porcelain line never carries an item, so nothing downstream splits one on
whitespace. Only an empty name is a fault. -/
def itemFaults (item : String) : Option String :=
  if item.isEmpty then some "an empty item name" else none

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

/-- Read a `# lowered:` line: see `Lowered`. -/
def parseLowered (l : String) : Option (Except String Lowered) :=
  let pre := "# lowered:"
  if !l.startsWith pre then none
  else
    let rest := ((l.drop pre.length).toString).trimAscii.toString
    match rest.splitOn "—" with
    | [lhs, why] =>
      let why := why.trimAscii.toString
      let toks := ((lhs.trimAscii.toString).splitOn " ").filter (!·.isEmpty)
      match toks.reverse with
      | [] => some (.error "a lowering naming no item")
      | arrow :: itemRev =>
        let item := String.intercalate " " itemRev.reverse
        match arrow.splitOn "→" with
        | [o, n] =>
          match o.toInt?, n.toInt? with
          | some o, some n =>
            if item.isEmpty then some (.error "a lowering naming no item")
            else if why.isEmpty then
              some (.error s!"lowering of '{item}' gives no reason")
            else some (.ok { item, old := o, new := n, why })
          | _, _ => some (.error s!"lowering of '{item}': '{arrow}' is not `<old>→<new>`")
        | _ => some (.error s!"malformed lowering '{rest}' (want `<item> <old>→<new> — <why>`)")
    | _ => some (.error s!"malformed lowering '{rest}' (want `<item> <old>→<new> — <why>`)")

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
  let mut lowered : Array Lowered := #[]
  let mut encoding : Option Encoding := none
  for raw in text.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty then continue
    if l.startsWith "#" then
      provenance := provenance.push l
      if let some r := parseRetired l then
        retired := retired.push (← r)
      if let some w := parseLowered l then
        lowered := lowered.push (← w)
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
  return { provenance, rows, retired, lowered, encoding }

/-- Faults about the row set: order, uniqueness, a retirement that
contradicts a live row, and a lowering the rows do not bear out. Reported
together so one run names them all. -/
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
  for w in t.lowered do
    if w.new > w.old then
      out := out.push s!"lowering of '{w.item}' names a rise ({w.old}→{w.new})"
    match (t.rows.find? (·.item == w.item)).map (·.value) with
    | some v =>
      -- The line stays true as the item recovers, and false only where the
      -- file claims a floor its own rows do not hold.
      if v < w.new then
        out := out.push s!"lowering of '{w.item}' says {w.new} but the row says {v}"
    | none =>
      if !t.retired.any (·.1 == w.item) then
        out := out.push s!"lowering of '{w.item}' names no measured or retired item"
  return out

def Tsv.find? (t : Tsv) (item : String) : Option Int :=
  (t.rows.find? (·.item == item)).map (·.value)

def Tsv.isRetired (t : Tsv) (item : String) : Bool :=
  t.retired.any (·.1 == item)

/-- One change the ratchet saw, as a value: a judge reads these fields, not
a rendered sentence. -/
inductive Change where
  | fell (item : String) (old new : Int)
  | rose (item : String) (old new : Int)
  | vanished (item : String) (old : Int)
  | entered (item : String) (value : Int)
deriving BEq, Inhabited

def Change.item : Change → String
  | .fell i _ _ | .rose i _ _ | .vanished i _ | .entered i _ => i

/-- A fall or an unretired vanish: the floor moved the wrong way. -/
def Change.isLoss : Change → Bool
  | .fell _ _ _ | .vanished _ _ => true
  | .rose _ _ _ | .entered _ _ => false

def Change.describe : Change → String
  | .fell i o n => s!"{i}: {o} → {n}"
  | .rose i o n => s!"{i}: {o} → {n}"
  | .vanished i o => s!"{i}: baselined at {o}, now absent"
  | .entered i v => s!"{i}: new at {v}"

/-- One verdict of the ratchet. -/
structure Delta where
  changes : Array Change
deriving Inhabited

def Delta.losses (d : Delta) : Array Change := d.changes.filter (·.isLoss)

def Delta.gains (d : Delta) : Array Change := d.changes.filter (!·.isLoss)

/-- Is this tier's committed floor the measurement? The one rule, for every
tier: any change at all — a loss *or* an unrecorded gain — fails `--check`.

Tight in both directions, as the suite already reads `subjectDebt` and
`siteAccounting`: a floor allowed to lag the tree is a floor that admits a
silent fall back to it, and the queue, which ranks from committed files,
ranks on the stale number. So a gain is recorded by regenerating, in the
commit that earned it. -/
def Delta.checkPasses (d : Delta) : Bool := d.changes.isEmpty

/-- Does a committed lowering authorise this change? Exactly the fall it
names, by both values — a second fall of the same item needs a second
line. -/
def Lowered.authorises (w : Lowered) : Change → Bool
  | .fell i o n => w.item == i && w.old == o && w.new == n
  | .vanished i o => w.item == i && w.old == o
  | _ => false

/-- Compare a fresh measurement against the committed baseline. Retirement
is read off the *baseline*: the committed file is where a human writes why
a measurement stopped being made.

In a `headroom` tier an item the baseline has never seen is compared
against the **cap**, not treated as new: the cap is what "no debt" means
there, so debt arriving under a name the file never held is a fall. Without
that, staging an obligation under a new owner module read as an
improvement — "is the debt going down" answered by the owner field's
spelling, a typo included — while the same obligation under an existing
owner was a regression. The rule is the encoding's, so it holds for every
headroom tier at once. -/
def ratchet (base now : Tsv) : Delta := Id.run do
  let mut changes : Array Change := #[]
  let implicit : Option Int := match base.encoding with
    | some (.headroom cap) => some cap
    | _ => none
  for r in base.rows do
    match now.find? r.item with
    | some v =>
      if v < r.value then changes := changes.push (.fell r.item r.value v)
      else if v > r.value then changes := changes.push (.rose r.item r.value v)
    | none =>
      if !base.isRetired r.item then
        changes := changes.push (.vanished r.item r.value)
  for r in now.rows do
    if (base.find? r.item).isNone then
      match implicit with
      | some cap =>
        if r.value < cap then changes := changes.push (.fell r.item cap r.value)
        else if r.value > cap then changes := changes.push (.rose r.item cap r.value)
        else changes := changes.push (.entered r.item r.value)
      | none => changes := changes.push (.entered r.item r.value)
  return { changes }

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

/-- The tiers the scoreboard expects to exist. A name here missing either
half — `tests/scoreboard/<name>.tsv` or `scripts/<name>.lean` — is a
**fault**, not a pass: a tier that vanishes is exactly the failure this
file guards against, and before this list existed a landed tier could be
deleted outright and the gate stayed green.

Names beyond the ones this agent shipped are the siblings' tiers, declared
ahead of their arrival so their absence is visible. -/
def declaredTiers : List String :=
  ["commonmark", "compat", "coverage", "diagdebt", "htmlreader", "obligations",
   "parity", "purity"]

/-- The declared tiers that have not landed yet: only these may be absent,
and their absence reports `missing`, which the aggregate does not gate — so
a sibling's tier can arrive in two commits without breaking the gate in
between.

The list cannot go stale, because the selftest fails a name on it that has
both halves: landing a tier and removing its name here are one commit. That
is what makes the permission narrow rather than a hole the size of
`declaredTiers`. -/
def pendingTiers : List String :=
  ["commonmark", "coverage", "parity"]

/-- The lake targets a tier's `--check` imports. `lake env lean --run` uses
whatever `.olean` the last build left and builds nothing itself, so without
this the whole scoreboard measures a stale tree: a module edited and not
rebuilt still reports its old value, and this branch's own `lake build`
passed over a syntactically broken `Board.lean` because
`defaultTargets = ["leantex"]` covers neither `BoardLib` nor `scoreboard`.

The aggregate builds these once before fanning out, and a failed build is a
`fault` — the honest answer when the thing to measure did not compile.
`ParityLib` is a sibling's, named ahead of its arrival so it is built the
moment that tier lands; a name no `lakefile.toml` declares is skipped
rather than failed, so the list can run ahead of the tree. -/
def tierImports : List String :=
  ["BoardLib", "GateLib", "TestsModules", "ParityLib"]

/-- The `tierImports` this tree actually declares. Read off `lakefile.toml`,
so a name that has not arrived yet is skipped instead of failing the build
it was meant to guard. -/
def buildTargets : IO (Array String) := do
  let lakefile ← if ← System.FilePath.pathExists "lakefile.toml"
    then IO.FS.readFile "lakefile.toml" else pure ""
  let pre := "name = \""
  let mut declared : Array String := #[]
  for l in lakefile.splitOn "\n" do
    let t := l.trimAscii.toString
    if t.startsWith pre then
      let rest := (t.drop pre.length).toString
      match rest.splitOn "\"" with
      | n :: _ => declared := declared.push n
      | [] => pure ()
  return tierImports.toArray.filter declared.contains

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
  | none => pure ()
  | some (.headroom cap) =>
    for r in t.rows do
      let d := cap - r.value
      if d > 0 then out := out.push (r.item, d)
  | some (.pairs part whole) =>
    for r in t.rows do
      if r.item.endsWith ("." ++ whole) then
        let key := (r.item.dropEnd (whole.length + 1)).toString
        let got := (t.find? (key ++ "." ++ part)).getD 0
        let d := r.value - got
        if d > 0 then out := out.push (key, d)
  | some .raw =>
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

def readFileOr (p : String) : IO String := do
  if ← System.FilePath.pathExists p then IO.FS.readFile p else return ""

/-- The three modes every tier producer shares, so no tier can differ in
what its `--check` means:

* no argument — regenerate the baseline from a fresh measurement, carrying
  the retirement and lowering lines forward. A fall is written only where a
  committed `# lowered: <item> <old>→<new> — <why>` line authorises exactly
  that fall; otherwise nothing is written and the exact line to add is
  printed. Weakening a statement is a human act, so a human writes the
  reason, in the file.
* `--check` — measure, compare against the committed baseline, write
  nothing. The gated mode: hermetic, in-repo data only. An absent or empty
  baseline is a **fault** here: with nothing to compare against every row
  reads as new, so emptying the file used to pass the gate and silently
  discard the floor. Only regeneration may start from nothing. Any change
  fails, a rise included — record it by regenerating.
* `--selftest` — the tier's own predicates against hand-written inputs.

`measure` returns the provenance lines specific to this tier (tool versions,
counts, whatever sizes the claim) and the rows. -/
def tierMain (tier : String) (enc : Encoding)
    (measure : IO (Array String × Array Row)) (selftest : IO UInt32)
    (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return (← selftest)
  let path := tsvPath tier
  let old := (← readFileOr path)
  let checking := args.contains "--check"
  if old.trimAscii.isEmpty && checking then
    IO.eprintln s!"scoreboard: {path} is absent or empty, so there is no floor to \
check against; regenerate: lake env lean --run scripts/{tier}.lean"
    IO.println (tierLine tier 0 0 0 "fault")
    return 2
  let baseline : Option Tsv ←
    if old.isEmpty then pure none
    else match parse old with
      | .ok t =>
        let faults := validate t
        if faults.isEmpty then pure (some t)
        else
          IO.eprintln s!"scoreboard: {path} is malformed:"
          for f in faults do IO.eprintln s!"  {f}"
          IO.println (tierLine tier 0 0 0 "fault")
          return 2
      | .error e =>
        IO.eprintln s!"scoreboard: {path}: {e}"
        IO.println (tierLine tier 0 0 0 "fault")
        return 2
  let (extra, rows) ← measure
  let fresh : Tsv :=
    { provenance := #[], rows := rows.qsort (fun a b => a.item < b.item)
      retired := (baseline.map (·.retired)).getD #[]
      lowered := (baseline.map (·.lowered)).getD #[], encoding := some enc }
  let freshFaults := validate fresh
  if !freshFaults.isEmpty then
    IO.eprintln s!"scoreboard: the fresh {tier} measurement is malformed:"
    for f in freshFaults do IO.eprintln s!"  {f}"
    IO.println (tierLine tier 0 0 0 "fault")
    return 2
  let d : Delta := match baseline with
    | none => { changes := fresh.rows.map (fun r => .entered r.item r.value) }
    | some b => ratchet b fresh
  if !checking then
    -- A fall is written only where the committed file already authorises
    -- exactly that fall. Writing one silently is how a floor gets weakened
    -- with no reason anyone can read later.
    let unauthorised := d.losses.filter fun c =>
      !(fresh.lowered.any (·.authorises c))
    if !unauthorised.isEmpty then
      IO.eprintln s!"scoreboard: refusing to write {path}: \
{unauthorised.size} value(s) would fall with nothing authorising it."
      for c in unauthorised do
        IO.eprintln s!"scoreboard:   {c.describe}"
        match c with
        | .fell i o n => IO.eprintln s!"scoreboard:   add: # lowered: {i} {o}→{n} — <why>"
        | .vanished i o =>
          IO.eprintln s!"scoreboard:   add: # retired: {i} — <why>  \
(or # lowered: {i} {o}→<new> — <why>)"
        | _ => pure ()
      IO.println (tierLine tier fresh.rows.size d.losses.size d.gains.size "regressed")
      return 1
    let mut header : Array String := #[
      s!"# generated by scripts/{tier}.lean — do not hand-edit; regenerate: \
lake env lean --run scripts/{tier}.lean",
      s!"# encoding: {enc.render}"]
    for e in extra do header := header.push e
    for (item, why) in fresh.retired do
      header := header.push s!"# retired: {item} — {why}"
    for w in fresh.lowered do
      header := header.push s!"# lowered: {w.item} {w.old}→{w.new} — {w.why}"
    IO.FS.writeFile path (render header fresh.rows)
    IO.println s!"scoreboard: wrote {path} ({fresh.rows.size} items)"
  for c in d.losses do IO.eprintln s!"scoreboard: {tier} regressed: {c.describe}"
  for c in d.gains do IO.println s!"scoreboard: {tier} improved: {c.describe}"
  -- `stale`, not `regressed`: the tree is ahead of its own floor. The
  -- aggregate gates it all the same, because a floor that lags admits a
  -- silent fall back to it.
  let result :=
    if !checking || d.checkPasses then "ok"
    else if d.losses.isEmpty then "stale" else "regressed"
  if checking && !d.gains.isEmpty && d.losses.isEmpty then
    IO.eprintln s!"scoreboard: {tier}: the floor is behind the measurement; \
record it: lake env lean --run scripts/{tier}.lean"
  IO.println (tierLine tier fresh.rows.size d.losses.size d.gains.size result)
  if checking then return (if d.checkPasses then 0 else 1)
  -- Regenerating with every fall authorised is the intended act, so it is
  -- a clean exit: the reason is in the file the writer just committed.
  return 0

end Scoreboard
