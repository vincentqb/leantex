/-
The scoreboard's core: one committed baseline per goal, each under a
ratchet. A tier is a file plus its only writer — `tests/scoreboard/<tier>.tsv`
and `scripts/<tier>.lean` — and the file is the whole claim: `#` lines for
provenance (tool versions, the encoding; data, never gated), then
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

* a value that drops is a regression, unless a lowering request authorises
  exactly that fall (below);
* a baselined item that disappears is a regression, unless a `# retired:`
  line retires it;
* a value that **rises** fails `--check` too, unrecorded: record it by
  regenerating, in the commit that earned it. A floor allowed to lag the
  tree is a floor that admits a silent fall back to it, and the queue,
  which ranks from committed files, ranks on the stale number. It is the
  rule `subjectDebt` and `siteAccounting` already live under — read in both
  directions, so a row is a migration step and not a parking space;
* a new item enters at its measured value — in a `headroom` tier, against
  the cap.

Weakening is a human act with a written reason, in the committed file, and
each line authorises one act, once. The state of every line is decidable
from the file alone, which is what keeps every mode hermetic:

* `# lowered: <item> <old>→<new> — <why>` is a **request**. It authorises
  exactly the fall from the committed value `<old>` to the measured `<new>`,
  and the regeneration that writes that fall writes the line back as
  `# lowered (applied): <item> <old>→<new> — <why>`, a **record**. A record
  authorises nothing, ever: a line carried forward cannot let the same item
  fall a second time, even between the same two values. A second fall needs
  a second request, checked against the floor the first one left.
* `# retired: <item> — <why>` beside the item's row is a request; the
  regeneration that stops writing the row leaves the same line as the
  record. A measurement that still produces a retired item is malformed:
  re-admitting one means deleting its line.
* `# retired-tier: <why>` in place of every row retires a whole tier: the
  file stays as its tombstone and the producer is deleted.

A committed file still carrying a request is `stale` under `--check`: it is
not what a regeneration wrote. `scoreboard --check --base <rev>` holds the
tree's files to the ones committed at `<rev>` (`judgeBase`), read with git's
replacement objects off: a fall or a vanish there needs a line that is new
since `<rev>` — a record spending a request `<rev>` holds is new, since the
spend is — which is what stops a hand-edited value, or a baseline deleted and
regenerated from nothing, from laundering one. Every tier file in the tree,
one new since `<rev>` included (`judgeNew`), must read as the format
(`validate`), and one still carrying a request is `stale` there too, whatever
its producer answers.

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
import LeanTex
import scripts.Gate

namespace Scoreboard

/-- The headroom ceiling. Large enough that no debt this repository tracks
approaches it, so `cap - count` stays positive and a reader can subtract in
their head. Raising it would raise every headroom item at once, which the
ratchet would read as a fleet-wide improvement — so it is a constant, not a
knob. -/
def debtCap : Int := 1000

/-- The lowest value a `raw` tier's item can hold and still be ranked. A
negative value is how a tier says "outside the denominator" — `parity`
writes `refuses -1` for a fixture the reference engine cannot build — and
such an item is not the tier's worst, it is not in the running. -/
def rawFloor : Int := 0

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

/-- A lowering line's standing: a human's request, which authorises one
fall in the next regeneration, or the record regeneration leaves once it has
written that fall, which authorises nothing. -/
inductive LowerState where
  | pending
  | applied
deriving DecidableEq, Inhabited, Repr

def LowerState.tag : LowerState → String
  | .pending => "# lowered:"
  | .applied => "# lowered (applied):"

/-- `# lowered: <item> <old>→<new> — <why>`, or its applied record. The item
may hold spaces, so the arrow pair is read as the last token before the
reason. A literal built without a `state` is a request. -/
structure Lowered where
  item : String
  old : Int
  new : Int
  why : String
  state : LowerState := .pending
deriving BEq, Inhabited

def Lowered.render (w : Lowered) : String :=
  s!"{w.state.tag} {w.item} {w.old}→{w.new} — {w.why}"

/-- The same text whatever its standing: a request and the record it became
are one human act of writing. Spending the request is another act, so the
base check cancels a line only against one of the same standing
(`newLowerings`) and reads this only to say which base line a new one shares
its text with. -/
def Lowered.sameLine (a b : Lowered) : Bool :=
  a.item == b.item && a.old == b.old && a.new == b.new && a.why == b.why

structure Tsv where
  provenance : Array String
  rows : Array Row
  retired : Array (String × String)
  /-- Every lowering line, requests and records, in file order. Carried
  forward when a producer regenerates, so the file reads as the history of
  why its floor moved. -/
  lowered : Array Lowered
  /-- `none`: the tier declares no encoding. It is gated like any other tier
  and the queue does not rank it — a missing hint for a report, not a
  malformed baseline. -/
  encoding : Option Encoding
  /-- `# retired-tier: <why>`: the file is the tombstone of a retired tier. -/
  tierRetired : Option String := none
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

/-- Read a lowering line, either standing: see `Lowered`. -/
def parseLowered (l : String) : Option (Except String Lowered) :=
  match [LowerState.applied, .pending].find? (fun s => l.startsWith s.tag) with
  | none => none
  | some state =>
    let rest := ((l.drop state.tag.length).toString).trimAscii.toString
    let bad := s!"malformed lowering '{rest}' (want `<item> <old>→<new> — <why>`)"
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
            else some (.ok { item, old := o, new := n, why, state })
          | _, _ => some (.error s!"lowering of '{item}': '{arrow}' is not `<old>→<new>`")
        | _ => some (.error bad)
    | _ => some (.error bad)

/-- `# retired-tier: <why>`. -/
def parseTierRetired (l : String) : Option (Except String String) :=
  let pre := "# retired-tier:"
  if !l.startsWith pre then none
  else
    let why := ((l.drop pre.length).toString).trimAscii.toString
    if why.isEmpty then some (.error "a tier retirement gives no reason")
    else some (.ok why)

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
  let mut tierRetired : Option String := none
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
      if let some t := parseTierRetired l then
        if tierRetired.isSome then throw "two `# retired-tier:` lines"
        tierRetired := some (← t)
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
  return { provenance, rows, retired, lowered, encoding, tierRetired }

def Tsv.find? (t : Tsv) (item : String) : Option Int :=
  (t.rows.find? (·.item == item)).map (·.value)

def Tsv.isRetired (t : Tsv) (item : String) : Bool :=
  t.retired.any (·.1 == item)

/-- The cap an unseen item is compared against: the `headroom` encoding's,
and none for any other. -/
def Tsv.cap? (t : Tsv) : Option Int :=
  match t.encoding with
  | some (.headroom cap) => some cap
  | _ => none

/-- The lowering requests no regeneration has applied yet. -/
def Tsv.pendingLowerings (t : Tsv) : Array Lowered :=
  t.lowered.filter (·.state == .pending)

/-- The items the file retires while still holding their rows: retirement
requests no regeneration has applied yet. -/
def Tsv.pendingRetirements (t : Tsv) : Array String :=
  t.retired.filterMap fun (i, _) => if t.rows.any (·.item == i) then some i else none

/-- Faults of a **committed** baseline: order and uniqueness of its rows,
and the human-written lines judged against the rows they sit beside.

A lowering request must name the fall from the floor this file commits — its
`<old>` is the item's committed value, or the cap for an item a `headroom`
tier has not baselined — because that is the only fall it can authorise. A
record is history and is never held to today's rows: a record that had to
stay true against every later floor is what wedged a second fall of one item
(the second staging under one owner module). A retirement beside its row is a
request, which regeneration applies; `validateFresh` is where a retired item
that is still measured is a fault. -/
def validate (t : Tsv) : Array String := Id.run do
  let mut out : Array String := #[]
  match t.tierRetired with
  | some _ =>
    if !t.rows.isEmpty then
      out := out.push "a retired tier still holds rows (`# retired-tier:` beside a measurement)"
  | none =>
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
  for w in t.lowered do
    if w.old ≤ w.new then
      out := out.push s!"lowering of '{w.item}' names no fall ({w.old}→{w.new})"
    else if w.state == .pending then
      -- The remedy is part of the message: a request carried after the fall it
      -- asked for was written reads exactly like this.
      let remedy := "; if it records a fall already written, mark it `# lowered (applied):`, \
otherwise correct or delete it"
      match t.find? w.item, t.cap? with
      | some v, _ =>
        if v != w.old then
          out := out.push s!"lowering of '{w.item}' says {w.old}→{w.new} but the \
committed floor is {v}{remedy}"
      | none, some cap =>
        if cap != w.old then
          out := out.push s!"lowering of '{w.item}' says {w.old}→{w.new}, but the item \
is not baselined, so it enters from the cap {cap}{remedy}"
      | none, none =>
        out := out.push s!"lowering of '{w.item}' names no baselined item{remedy}"
  return out

/-- Faults of a **fresh measurement**, sorted by the caller, judged against
the committed file it will be compared with. A measured item the committed
file retires is one: the retirement said the measurement stopped, and it did
not. Re-admitting the item is deleting its line — a human act, like
retiring it. -/
def validateFresh (rows : Array Row) (committed : Option Tsv) : Array String := Id.run do
  let mut out : Array String := #[]
  if rows.isEmpty then out := out.push "no rows"
  for r in rows do
    if let some f := itemFaults r.item then out := out.push f
  for i in [1:rows.size] do
    if rows[i-1]!.item == rows[i]!.item then
      out := out.push s!"duplicate item '{rows[i]!.item}'"
  if let some t := committed then
    for (item, _) in t.retired do
      if rows.any (·.item == item) then
        out := out.push s!"item '{item}' is retired and also measured; delete its \
`# retired:` line to measure it again"
  return out

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

/-- Does a lowering line authorise this change? A request authorises exactly
the fall it names, by item and both values; a record authorises nothing; and
no lowering authorises a vanish, which is retirement's to answer. -/
def Lowered.authorises (w : Lowered) : Change → Bool
  | .fell i o n => w.state == .pending && w.item == i && w.old == o && w.new == n
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
headroom tier at once.

Spelled as two `filterMap`s rather than a loop so the statements below can
read it: the monotone statement and its two companions. -/
def ratchet (base now : Tsv) : Delta :=
  { changes :=
      base.rows.filterMap (fun r =>
        match now.find? r.item with
        | some v =>
          if v < r.value then some (.fell r.item r.value v)
          else if r.value < v then some (.rose r.item r.value v)
          else none
        | none => if base.isRetired r.item then none else some (.vanished r.item r.value)) ++
      now.rows.filterMap (fun r =>
        if (base.find? r.item).isSome then none
        else match base.cap? with
          | some cap =>
            if r.value < cap then some (.fell r.item cap r.value)
            else if cap < r.value then some (.rose r.item cap r.value)
            else some (.entered r.item r.value)
          | none => some (.entered r.item r.value)) }

/-- The losses no request in the committed file authorises. Regeneration
writes only when this is empty, and that one condition is what the three
statements below are about. -/
def unauthorised (base now : Tsv) : Array Change :=
  (ratchet base now).losses.filter fun c => !(base.lowered.any (·.authorises c))

/-- The requests no loss of this measurement answers: a request that
authorises nothing is refused rather than carried, or it would sit in the
file waiting to authorise some later fall nobody wrote it for. -/
def unusedLowerings (base now : Tsv) : Array Lowered :=
  let losses := (ratchet base now).losses
  base.pendingLowerings.filter fun w => !(losses.any w.authorises)

/-! ### What the ratchet guarantees

Stated over `unauthorised`, the condition regeneration writes under. -/

/-- A lowering line authorises a change exactly when it is a request and the
change is the fall it names: never a record, never a vanish, never another
item's fall or another pair of values. -/
theorem authorises_exact (w : Lowered) (c : Change) :
    w.authorises c = true ↔ (w.state = .pending ∧ c = .fell w.item w.old w.new) := by
  cases c with
  | fell i o n =>
    simp only [Lowered.authorises, Bool.and_eq_true, beq_iff_eq, Change.fell.injEq]
    constructor
    · rintro ⟨⟨⟨hs, hi⟩, ho⟩, hn⟩
      exact ⟨hs, hi.symm, ho.symm, hn.symm⟩
    · rintro ⟨hs, hi, ho, hn⟩
      exact ⟨⟨⟨hs, hi.symm⟩, ho.symm⟩, hn.symm⟩
  | rose i o n => simp [Lowered.authorises]
  | vanished i o => simp [Lowered.authorises]
  | entered i v => simp [Lowered.authorises]

private theorem authorised_of_unauthorised_empty {base now : Tsv}
    (h : unauthorised base now = #[]) {c : Change}
    (hc : c ∈ (ratchet base now).changes) (hl : c.isLoss = true) :
    ∃ w ∈ base.lowered, w.authorises c = true := by
  have hmem : c ∈ (ratchet base now).losses := Array.mem_filter.mpr ⟨hc, hl⟩
  have hnot := (Array.filter_eq_empty_iff.mp h) c hmem
  have hany : base.lowered.any (·.authorises c) = true := by simpa using hnot
  obtain ⟨i, hi, hp⟩ := Array.any_eq_true.mp hany
  exact ⟨_, Array.getElem_mem hi, hp⟩

/-- Every baselined item a regeneration may write either did not fall, or
fell by exactly the pair of values a request in the committed file names. -/
theorem ratchet_monotone (base now : Tsv) (h : unauthorised base now = #[]) :
    ∀ r ∈ base.rows, ∀ v, now.find? r.item = some v →
      r.value ≤ v ∨ ∃ w ∈ base.lowered,
        w.state = .pending ∧ w.item = r.item ∧ w.old = r.value ∧ w.new = v := by
  intro r hr v hv
  by_cases hlt : v < r.value
  · right
    have hc : Change.fell r.item r.value v ∈ (ratchet base now).changes := by
      unfold ratchet
      refine Array.mem_append.mpr (.inl (Array.mem_filterMap.mpr ⟨r, hr, ?_⟩))
      simp [hv, hlt]
    obtain ⟨w, hw, ha⟩ := authorised_of_unauthorised_empty h hc rfl
    obtain ⟨hs, heq⟩ := (authorises_exact w _).mp ha
    simp only [Change.fell.injEq] at heq
    exact ⟨w, hw, hs, heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩
  · exact .inl (Int.not_lt.mp hlt)

/-- An item a `headroom` tier has never baselined enters at or above the cap,
or at exactly the value a request names as a fall from the cap. -/
theorem ratchet_cap_monotone (base now : Tsv) (h : unauthorised base now = #[])
    {cap : Int} (hcap : base.cap? = some cap) :
    ∀ r ∈ now.rows, base.find? r.item = none →
      cap ≤ r.value ∨ ∃ w ∈ base.lowered,
        w.state = .pending ∧ w.item = r.item ∧ w.old = cap ∧ w.new = r.value := by
  intro r hr hn
  by_cases hlt : r.value < cap
  · right
    have hc : Change.fell r.item cap r.value ∈ (ratchet base now).changes := by
      unfold ratchet
      refine Array.mem_append.mpr (.inr (Array.mem_filterMap.mpr ⟨r, hr, ?_⟩))
      simp [hn, hcap, hlt]
    obtain ⟨w, hw, ha⟩ := authorised_of_unauthorised_empty h hc rfl
    obtain ⟨hs, heq⟩ := (authorises_exact w _).mp ha
    simp only [Change.fell.injEq] at heq
    exact ⟨w, hw, hs, heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩
  · exact .inl (Int.not_lt.mp hlt)

/-- An item a regeneration stops writing is paid for by a retirement line in
the committed file: no lowering can stand in for one. -/
theorem ratchet_accounts (base now : Tsv) (h : unauthorised base now = #[]) :
    ∀ r ∈ base.rows, now.find? r.item = none → base.isRetired r.item = true := by
  intro r hr hn
  cases hret : base.isRetired r.item
  · exfalso
    have hc : Change.vanished r.item r.value ∈ (ratchet base now).changes := by
      unfold ratchet
      refine Array.mem_append.mpr (.inl (Array.mem_filterMap.mpr ⟨r, hr, ?_⟩))
      simp [hn, hret]
    obtain ⟨w, _, ha⟩ := authorised_of_unauthorised_empty h hc rfl
    simp [Lowered.authorises] at ha
  · rfl

/-! ### The base check: a floor cannot move unless a new line moves it

`--check` compares the committed files with the measurement, so a floor
edited down by hand, or a baseline deleted and regenerated from nothing,
passes it: both files agree with the tree. What they cannot agree with is
the file committed at the base the branch lands onto. So `judgeBase`
compares the two committed files, and a fall between them needs lowering
lines that are **new** since the base — a record carried from the base
cannot pay twice. -/

/-- The lowering lines the tree's file carries that the base's does not, as
a multiset: one base line cancels one identical tree line **of the same
standing**. A record the tree writes for a request the base holds is new,
because spending the request is: it was never applied at the base, so the
regeneration that applies it is the act this landing adds. Cancelling across
standings once let the base's request swallow that record, and the tool's own
remedy for a base holding a request ended at `laundered`. -/
def newLowerings (base tip : Tsv) : Array Lowered :=
  let step := fun (acc : List Lowered × Array Lowered) (w : Lowered) =>
    if acc.1.any (· == w) then (acc.1.eraseP (· == w), acc.2)
    else (acc.1, acc.2.push w)
  (tip.lowered.foldl step (base.lowered.toList, #[])).2

/-- The items the tree's file retires that the base's does not record as
retired. A retirement the base only requests — its line beside the row it
retires — is unspent there, and the regeneration that drops the row spends
it, as a record spends a request (`newLowerings`). -/
def newRetirements (base tip : Tsv) : Array String :=
  tip.retired.filterMap fun (i, _) =>
    if base.isRetired i && !base.pendingRetirements.contains i then none else some i

/-- One pass: the lowest `new` among the lines usable from `m`. The value may
rise freely — rises need no line — so a line whose `old` is at or above `m`
is usable. -/
def reachStep (lines : List Lowered) (m : Int) : Int :=
  lines.foldl (fun acc w => if m ≤ w.old ∧ w.new < acc then w.new else acc) m

/-- The lowest value an item can reach from `c` when it may rise freely and
fall only along one of `lines`: the composition of the regenerations the
lines record, with any rises between them. One pass per line reaches the
fixed point, because each productive pass lands on some line's `new`. -/
def reach (lines : List Lowered) (c : Int) : Int :=
  (List.replicate lines.length ()).foldl (fun m _ => reachStep lines m) c

private theorem lowerFold_mem (lines : List Lowered) (c m : Int) :
    ∀ (l : List Lowered) (acc : Int), (∀ w ∈ l, w ∈ lines) →
      (acc = c ∨ ∃ w ∈ lines, acc = w.new) →
      (l.foldl (fun acc w => if m ≤ w.old ∧ w.new < acc then w.new else acc) acc = c ∨
        ∃ w ∈ lines,
          l.foldl (fun acc w => if m ≤ w.old ∧ w.new < acc then w.new else acc) acc =
            w.new) := by
  intro l
  induction l with
  | nil => intro acc _ h; simpa using h
  | cons x xs ih =>
    intro acc hsub h
    simp only [List.foldl_cons]
    apply ih
    · intro w hw
      exact hsub w (List.mem_cons_of_mem x hw)
    · split
      · exact .inr ⟨x, hsub x (by simp), rfl⟩
      · exact h

/-- What `reach` returns is drawn from its inputs: the start, or some line's
`new` — so nothing is reached that no line wrote. -/
theorem reach_mem (lines : List Lowered) (c : Int) :
    reach lines c = c ∨ ∃ w ∈ lines, reach lines c = w.new := by
  unfold reach
  have key : ∀ (r : List Unit) (acc : Int), (acc = c ∨ ∃ w ∈ lines, acc = w.new) →
      (r.foldl (fun m _ => reachStep lines m) acc = c ∨
        ∃ w ∈ lines, r.foldl (fun m _ => reachStep lines m) acc = w.new) := by
    intro r
    induction r with
    | nil => intro acc h; simpa using h
    | cons u us ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      unfold reachStep
      exact lowerFold_mem lines c acc lines acc (fun _ hw => hw) h
  exact key _ c (.inl rfl)

/-- One baselined item's verdict under the base check: it held `c` at the
base; `tip` is its value in the tree. It may rise, fall only as far as the
new lines reach, and vanish only where `vanishOk` says a new retirement pays
for it. -/
def itemAccepted (c : Int) (tip : Option Int) (lines : List Lowered) (vanishOk : Bool) :
    Bool :=
  match tip with
  | some v => decide (c ≤ v) || decide (reach lines c ≤ v)
  | none => vanishOk

/-- A value the base check accepts either did not fall, or fell no further
than some new line goes: every accepted fall is paid for by a line written
since the base. -/
theorem itemAccepted_monotone (c v : Int) (lines : List Lowered) (b : Bool)
    (h : itemAccepted c (some v) lines b = true) :
    c ≤ v ∨ ∃ w ∈ lines, w.new ≤ v := by
  simp only [itemAccepted, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact .inl h
  · rcases reach_mem lines c with he | ⟨w, hw, he⟩
    · exact .inl (he ▸ h)
    · exact .inr ⟨w, hw, he ▸ h⟩

/-- Every way the tree's committed file moved a floor the base's file held
without a line written since the base to pay for it. -/
def baseFaults (base tip : Tsv) : Array String := Id.run do
  let mut out : Array String := #[]
  match base.encoding, tip.encoding with
  | some a, some b =>
    if a != b then
      out := out.push s!"the encoding changed from `{a.render}` to `{b.render}`; values \
under two encodings are not comparable, so no floor can be held"
  | _, _ => pure ()
  let lines := newLowerings base tip
  let retiredNow := newRetirements base tip
  let tombstoned := tip.tierRetired.isSome && base.tierRetired.isNone
  for r in base.rows do
    let mine := (lines.filter (·.item == r.item)).toList
    let vanishOk := retiredNow.contains r.item || tombstoned
    if !itemAccepted r.value (tip.find? r.item) mine vanishOk then
      match tip.find? r.item with
      | some v =>
        out := out.push s!"{r.item} fell {r.value} → {v} and no lowering line written \
since the base reaches {v}"
      | none =>
        out := out.push s!"{r.item}, baselined at {r.value}, is gone and no `# retired:` \
line was written for it since the base"
  if let some cap := base.cap? then
    for r in tip.rows do
      if (base.find? r.item).isNone then
        let mine := (lines.filter (·.item == r.item)).toList
        if !itemAccepted cap (some r.value) mine false then
          out := out.push s!"{r.item} entered at {r.value}, below the cap {cap}, and no \
lowering line written since the base reaches it"
  return out

/-- What a passing base check credited, for the human who lands it to read:
each weakening the tree's file makes against the base's — a fall, a vanish, an
item entering a `headroom` tier below its cap, a tier retired — then each line
new since the base that can pay for one, as written. A new line whose text the
base already carries is marked. A record spending a request the base holds,
or a retirement the base requested and the tree applied, says so; any other
copy is marked because the multiset counts the extra copy as new, and whether
it should is the human's call. -/
def baseCredits (base tip : Tsv) : Array String := Id.run do
  let mut out : Array String := #[]
  if tip.tierRetired.isSome && base.tierRetired.isNone then
    if !base.rows.isEmpty then out := out.push s!"moved: the tier's {base.rows.size} rows → gone"
  else
    for r in base.rows do
      match tip.find? r.item with
      | some v => if v < r.value then out := out.push s!"moved: {r.item} {r.value} → {v}"
      | none => out := out.push s!"moved: {r.item} {r.value} → gone"
    if let some cap := base.cap? then
      for r in tip.rows do
        if (base.find? r.item).isNone && r.value < cap then
          out := out.push s!"moved: {r.item} entered at {r.value}, below the cap {cap}"
  let spends := " (spends the request the base carries)"
  for w in newLowerings base tip do
    let note :=
      if w.state == .applied && base.pendingLowerings.any (·.sameLine w) then spends
      else if base.lowered.any (·.sameLine w) then " (the same text as a line the base carries)"
      else ""
    out := out.push s!"credited: {w.render}{note}"
  let retiredNow := newRetirements base tip
  for (i, why) in tip.retired do
    if retiredNow.contains i then
      let note := if base.pendingRetirements.contains i then spends else ""
      out := out.push s!"credited: # retired: {i} — {why}{note}"
  if let some why := tip.tierRetired then
    if base.tierRetired.isNone then out := out.push s!"credited: # retired-tier: {why}"
  return out

/-- `baseCredits` from the two texts; nothing when either does not read, which
`judgeBase` has already faulted. -/
def creditsOf (baseText tipText : String) : Array String :=
  match parse baseText, parse tipText with
  | .ok b, .ok t => baseCredits b t
  | _, _ => #[]

/-- The requests a committed file still holds, as written: a `# lowered:` line
no regeneration has applied, and a `# retired:` line beside its row. A file
holding one is not what its producer writes — regeneration spends a request in
the writing — so the base check reads it as `stale` whatever the producer's
`--check` answers, for every tier file in the tree, a tier new since the base
included (`treeVerdict`): the aggregate reads a producer by its exit status
alone, and a producer need not know the request form. -/
def heldRequests (t : Tsv) : Array String :=
  t.pendingLowerings.map (·.render) ++
    t.retired.filterMap fun (i, why) =>
      if t.rows.any (·.item == i) then some s!"# retired: {i} — {why}" else none

/-- What the tree's copy of a baseline owes whatever the base holds: the
format's faults (`validate`) — a duplicated item, whose floor a first reader
picks, and a request naming a floor the file does not hold among them — and
the requests it still holds, each saying whether the base holds it too: then
main carries it, and a landing that never touched it is stale all the same.
The base check applies it to every tier file in the tree, one the base does
not carry included; reading the base's listing alone once let a new tier land
holding a request, and validating nothing let a duplicate row hide a fall. -/
def treeVerdict (base : Option Tsv) (t : Tsv) : Array String × Array String :=
  let inherited := (base.map heldRequests).getD #[]
  ((validate t).map (s!"the tree's file is malformed: {·}"),
   (heldRequests t).map fun l =>
     let also := if inherited.contains l then " — the base holds it too, so main carries it \
and every landing is stale until one spends it or deletes it" else ""
     s!"the tree's file still holds `{l}`, a request no regeneration has applied{also}; \
regenerate the tier with its producer, which spends it in the writing, or delete the line")

/-- The base check for one tier, from the two texts: the result word and its
reasons. A baseline committed at the base that the tree no longer carries is
a fault — deleting the file was the other way to discard a floor — and a
whole tier is retired only by its tombstone. A tree's file that does not read
as the format is a fault, one that moved a floor with no new line to pay for
it is `laundered`, and one still holding a request is `stale`: whatever it
would pay for, it is not a file a regeneration wrote. The base's file is held
to nothing but reading: a fault in it is main's, and no landing could clear
it. -/
def judgeBase (baseText : String) (tipExists : Bool) (tipText : String) :
    String × Array String :=
  if !tipExists then
    ("fault", #["the baseline committed at the base is gone from the tree; a tier is \
retired by a `# retired-tier: <why>` tombstone in its file, never by deleting it"])
  else
    match parse baseText, parse tipText with
    | .error e, _ => ("fault", #[s!"the base's baseline does not read: {e}"])
    | _, .error e => ("fault", #[s!"the tree's baseline does not read: {e}"])
    | .ok b, .ok t =>
      let (bad, held) := treeVerdict (some b) t
      let fs := baseFaults b t
      if !bad.isEmpty then ("fault", bad ++ fs ++ held)
      else if !fs.isEmpty then ("laundered", fs ++ held)
      else if !held.isEmpty then ("stale", held)
      else ("ok", #[])

/-- The base check for a tier file the base does not carry: no floor there to
hold it to, so it is judged alone, by `treeVerdict`. -/
def judgeNew (tipText : String) : String × Array String :=
  match parse tipText with
  | .error e => ("fault", #[s!"the tree's baseline does not read: {e}"])
  | .ok t =>
    let (bad, held) := treeVerdict none t
    if !bad.isEmpty then ("fault", bad ++ held)
    else if !held.isEmpty then ("stale", held)
    else ("ok", #[])

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
  ["commonmark", "compat", "coverage", "diagaudit", "diagdebt", "htmla11y", "htmlreader",
   "obligations", "parity", "purity", "rhythm"]

/-- The declared tiers that have not landed yet: only these may be absent,
and their absence reports `missing`, which the aggregate does not gate — so
a sibling's tier can arrive in two commits without breaking the gate in
between.

The list cannot go stale, because the selftest fails a name on it that has
both halves: landing a tier and removing its name here are one commit. That
is what makes the permission narrow rather than a hole the size of
`declaredTiers`. -/
def pendingTiers : List String :=
  []

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
rather than failed, so the list can run ahead of the tree.

No tier reads the `leantex` binary: the HTML freshness key is built
in-process from the library `BoardLib` imports (`hermeticHtmlKey`), so
building `BoardLib` is what refreshes it. A tier that starts spawning the
binary owes `leantex` a place here. -/
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

/-- A tier's name is `[a-z0-9-]+`. It is a file basename, the root of its
producer's path, a `tier=` field the porcelain splits on whitespace, and a path
git lists — and git quotes a name holding any other byte, which is how a
deleted baseline once went unseen by the base check. -/
def tierNameOk (name : String) : Bool :=
  !name.isEmpty && name.all fun c => c.isLower || c.isDigit || c == '-'

/-- A name as the porcelain prints it: every UTF-8 byte outside `[a-z0-9-]` as
`%XX`, so a name the rule refuses still reads as one token, and one that
passes reads as itself. -/
def shownName (name : String) : String := Id.run do
  if name.isEmpty then return "%"
  let hex := "0123456789ABCDEF".toList.toArray
  let mut out := ""
  for c in name.toList do
    if c.isLower || c.isDigit || c == '-' then out := out.push c
    else
      for b in c.toString.toUTF8 do
        out := (out.push '%').push hex[(b >>> 4).toNat]! |>.push hex[(b &&& 15).toNat]!
  return out

/-- Does a character act on a terminal, or hide, rather than print? The C0
controls, DEL and the C1 controls — ESC among them, whose cursor-up and
erase-line sequences once wiped a `moved:` line a passing base check printed
— and the Unicode format characters that reorder text (the bidirectional
marks, embeddings, overrides and isolates) or hide it (the zero-width ones,
the line and paragraph separators, the byte-order mark). -/
def actsOnTerminal (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7F ≤ n && n ≤ 0x9F) || n == 0x061C || (0x200B ≤ n && n ≤ 0x200F) ||
    (0x2028 ≤ n && n ≤ 0x202E) || (0x2060 ≤ n && n ≤ 0x2069) || n == 0xFEFF

/-- A line as the scoreboard prints it: every character that acts rather than
prints spelled `\u{<hex>}`, so text a file or a producer supplies reaches a
terminal as text. Everything else, `→` and `—` included, passes unchanged. -/
def printable (s : String) : String := Id.run do
  if !s.any actsOnTerminal then return s
  let mut out := ""
  for c in s.toList do
    if actsOnTerminal c then out := out ++ "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
    else out := out.push c
  return out

/-- Every tier, and apart from them every name that is not one: the declared
names, plus any baseline committed under `tests/scoreboard/` that no one
declared (a sibling's tier, landed before its name reached this list). Direct
children only — a subdirectory holds the selftest fixtures, which are inputs
and not tiers. A name outside `[a-z0-9-]+` is returned apart rather than
dropped, so no caller runs it as a tier and none can overlook it: the
aggregate faults it. -/
def discover : IO (Array String × Array String) := do
  let mut names : Array String := #[]
  let mut misnamed : Array String := #[]
  let mut found : Array String := declaredTiers.toArray
  let dir : System.FilePath := "tests/scoreboard"
  if ← dir.isDir then
    for e in ← dir.readDir do
      let p := e.fileName
      if p.endsWith ".tsv" then
        let name := (p.dropEnd ".tsv".length).toString
        if !found.contains name then found := found.push name
  for n in found do
    if tierNameOk n then names := names.push n else misnamed := misnamed.push n
  return (names.qsort (· < ·), misnamed.qsort (· < ·))

/-- A deficit per item, from the tier's own encoding. The ranking is
computed from committed data; nothing here is a list of what to do.

`raw` measures distance from the tier's best item, and skips values below
`rawFloor`: a negative value is a tier's way of saying "outside the
denominator" (`parity`'s `refuses -1` is a fixture the reference engine
cannot build), and ranking it as the worst item of the tier would put a
measurement that does not count at the head of the queue. -/
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
      if r.value < rawFloor then continue
      let d := best - r.value
      if d > 0 then out := out.push (r.item, d)
  return out.qsort (fun a b => a.2 > b.2)

-- ## Obligations, read as records

structure Ob where
  name : String
  owner : String
  blocker : String
  file : String
deriving Inhabited

/-- Every owed record staged under the obligations path. A record is five
consecutive field lines, and a run of them that is not five is **rejected**,
exactly as `scripts/owed.lean` rejects it — not counted under owner `?`.
Counting a malformed record would mean this tier and the owed gate disagree
about what is staged, and the one that is silent about it is the one you
would trust by accident. -/
def obligations : IO (Array Ob × Array String) := do
  let mut files : Array String := #[]
  if ← System.FilePath.pathExists "Obligations.lean" then
    files := files.push "Obligations.lean"
  if ← System.FilePath.isDir "Obligations" then
    for p in ← System.FilePath.walkDir "Obligations" do
      if p.toString.endsWith ".lean" then files := files.push p.toString
  let mut out : Array Ob := #[]
  let mut malformed : Array String := #[]
  for f in files do
    let lines := ((← IO.FS.readFile f).splitOn "\n").toArray
    for i in [0:lines.size] do
      if let some name := (lines[i]?).bind (fieldOf · "owed") then
        match (lines[i+1]?).bind (fieldOf · "owner"),
              (lines[i+2]?).bind (fieldOf · "source"),
              (lines[i+3]?).bind (fieldOf · "blocker"),
              (lines[i+4]?).bind (fieldOf · "goldens") with
        | some owner, some _, some blocker, some _ =>
          out := out.push { name, owner, blocker, file := f }
        | _, _, _, _ =>
          malformed := malformed.push s!"{f}: record '{name}' is not five field \
lines (owner, source, blocker, goldens)"
  return (out, malformed)

/-- Obligations whose blocker names no other open obligation: the ones a
proof attempt can start on today. Computed from the records, not listed. -/
def ready (obs : Array Ob) : Array Ob :=
  obs.filter fun o =>
    !obs.any fun p => p.name != o.name && containsSub o.blocker p.name

def readFileOr (p : String) : IO String := do
  if ← System.FilePath.pathExists p then IO.FS.readFile p else return ""

/-- A content key over named byte blobs: FNV-1a, 64-bit, hex. Order
matters, and the name is hashed with the bytes, so a file renamed or
reordered changes the key.

What it is for: a tier whose numbers describe an *artifact* measured
elsewhere — a browser's verdict on built pages, a reference engine's
output — is only as fresh as the artifact it was measured on. Recording a
key of that artifact, and faulting when a fresh one differs, is what stops
the tier reporting last week's answer about this week's engine.

`UInt64` throughout, never `Nat`: a `Nat` shift is an out-of-line bignum
call, and this runs over every byte of every page. -/
def contentKey (blobs : Array (String × ByteArray)) : String := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  let prime : UInt64 := 0x100000001b3
  for (name, bytes) in blobs do
    for c in name.toUTF8 do
      h := (h ^^^ c.toUInt64) * prime
    h := (h ^^^ 0xff) * prime
    for b in bytes do
      h := (h ^^^ b.toUInt64) * prime
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for i in [0:16] do
    let nib := ((h >>> (60 - 4 * i.toUInt64)) &&& 0xf).toNat
    out := out.push (digits[nib]!)
  return out

/-- The three modes every tier producer shares, so no tier can differ in
what its `--check` means:

* no argument — regenerate the baseline from a fresh measurement. A fall is
  written only where a request in the committed file authorises exactly
  that fall, and a vanish only where a `# retired:` line retires the item;
  otherwise nothing is written and the exact line to add is printed. A
  request no loss answers is refused too, rather than carried to authorise
  some later fall. What is written carries every line forward, each request
  it applied as a record.
* `--check` — measure, compare against the committed baseline, write
  nothing. The gated mode: hermetic, in-repo data only. An absent or empty
  baseline is a **fault** here: with nothing to compare against every row
  reads as new, so emptying the file used to pass the gate and silently
  discard the floor. Only regeneration may start from nothing. Any change
  fails, a rise included — record it by regenerating — and so does a
  committed file still carrying a request (`stale`: it is not what a
  regeneration wrote).
* `--selftest` — the tier's own predicates against hand-written inputs.

`measure` returns the provenance lines specific to this tier (tool versions,
counts, whatever sizes the claim) and the rows. The baseline is
`tests/scoreboard/<tier>.tsv`; `tierMainAt` is the same with the file named,
which is how the selftest follows the tool's own remedies end to end. -/
def tierMainAt (path tier : String) (enc : Encoding)
    (measure : IO (Array String × Array Row)) (selftest : IO UInt32)
    (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return (← selftest)
  let old := (← readFileOr path)
  let checking := args.contains "--check"
  let fault (why : Array String) : IO UInt32 := do
    for w in why do IO.eprintln w
    IO.println (tierLine tier 0 0 0 "fault")
    return 2
  if old.trimAscii.isEmpty && checking then
    return (← fault #[s!"scoreboard: {path} is absent or empty, so there is no floor \
to check against; regenerate: lake env lean --run scripts/{tier}.lean"])
  let baseline : Option Tsv ←
    if old.trimAscii.isEmpty then pure none
    else match parse old with
      | .ok t =>
        let faults := validate t
        if !faults.isEmpty then
          return (← fault (#[s!"scoreboard: {path} is malformed:"] ++ faults.map (s!"  {·}")))
        if t.tierRetired.isSome then
          return (← fault #[s!"scoreboard: {path} retires this tier (`# retired-tier:`), \
but {scriptPath tier} still measures it; delete the producer"])
        pure (some t)
      | .error e => return (← fault #[s!"scoreboard: {path}: {e}"])
  let (extra, measured) ← measure
  let rows := measured.qsort (fun a b => a.item < b.item)
  let freshFaults := validateFresh rows baseline
  if !freshFaults.isEmpty then
    -- A tier that measured nothing has already said why on stderr — a
    -- missing input, a freshness key that no longer matches. Reporting it
    -- as a malformation would bury that reason under a format complaint.
    if freshFaults == #["no rows"] then
      return (← fault #[s!"scoreboard: {tier} measured nothing, so there is no \
comparison to make; the reason is above"])
    return (← fault (#[s!"scoreboard: the fresh {tier} measurement is malformed:"] ++
      freshFaults.map (s!"  {·}")))
  let fresh : Tsv :=
    { provenance := #[], rows, retired := (baseline.map (·.retired)).getD #[]
      lowered := (baseline.map (·.lowered)).getD #[], encoding := some enc }
  let d : Delta := match baseline with
    | none => { changes := fresh.rows.map (fun r => .entered r.item r.value) }
    | some b => ratchet b fresh
  let unauth := match baseline with
    | none => #[]
    | some b => unauthorised b fresh
  let unused := match baseline with
    | none => #[]
    | some b => unusedLowerings b fresh
  let pendingL := match baseline with
    | none => #[]
    | some b => b.pendingLowerings
  let pendingR := match baseline with
    | none => #[]
    | some b => b.pendingRetirements
  let authorised := d.losses.filter (!unauth.contains ·)
  if !checking then
    -- A fall is written only where the committed file already requests
    -- exactly that fall, and the request is spent in the writing: it goes
    -- back into the file as a record, which authorises nothing again.
    if !unauth.isEmpty || !unused.isEmpty then
      if !unauth.isEmpty then
        IO.eprintln s!"scoreboard: refusing to write {path}: {unauth.size} value(s) \
would fall with nothing authorising it."
        for c in unauth do
          IO.eprintln s!"scoreboard:   {c.describe}"
          match c with
          | .fell i o n => IO.eprintln s!"scoreboard:   add: # lowered: {i} {o}→{n} — <why>"
          | .vanished i _ => IO.eprintln s!"scoreboard:   add: # retired: {i} — <why>"
          | _ => pure ()
      if !unused.isEmpty then
        IO.eprintln s!"scoreboard: refusing to write {path}: {unused.size} `# lowered:` \
request(s) authorise no fall this measurement makes; correct or delete each:"
        for w in unused do
          let now := match fresh.find? w.item with
            | some v => s!"it measures {v}"
            | none => "it is not measured"
          IO.eprintln s!"scoreboard:   {w.render}  ({now})"
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
      header := header.push { w with state := .applied }.render
    IO.FS.writeFile path (render header fresh.rows)
    IO.println s!"scoreboard: wrote {path} ({fresh.rows.size} items)"
    for c in authorised do
      IO.eprintln s!"scoreboard: {tier} lowered, as requested: {c.describe}"
    for i in pendingR do IO.println s!"scoreboard: {tier} retired: {i}"
    for c in d.gains do IO.println s!"scoreboard: {tier} improved: {c.describe}"
    IO.println (tierLine tier fresh.rows.size d.losses.size d.gains.size "ok")
    return 0
  for c in unauth do IO.eprintln s!"scoreboard: {tier} regressed: {c.describe}"
  for c in authorised do
    IO.eprintln s!"scoreboard: {tier}: {c.describe} is requested by a `# lowered:` line \
no regeneration has applied; regenerate: lake env lean --run scripts/{tier}.lean"
  for w in unused do
    IO.eprintln s!"scoreboard: {tier}: {path} carries a request no fall answers: \
{w.render}; correct or delete it"
  for i in pendingR do
    IO.eprintln s!"scoreboard: {tier}: {path} retires '{i}' and still holds its row; \
regenerate: lake env lean --run scripts/{tier}.lean"
  for c in d.gains do IO.println s!"scoreboard: {tier} improved: {c.describe}"
  -- `stale`, not `regressed`: the tree is ahead of its own floor, or the file
  -- still carries a request. The aggregate gates it all the same, because a
  -- floor that lags admits a silent fall back to it.
  let result :=
    if !unauth.isEmpty then "regressed"
    else if !d.changes.isEmpty || !pendingL.isEmpty || !pendingR.isEmpty then "stale"
    else "ok"
  if result == "stale" && !d.gains.isEmpty then
    IO.eprintln s!"scoreboard: {tier}: the floor is behind the measurement; \
record it: lake env lean --run scripts/{tier}.lean"
  IO.println (tierLine tier fresh.rows.size d.losses.size d.gains.size result)
  return (if result == "ok" then 0 else 1)

/-- A tier producer's `main`: `tierMainAt` over `tests/scoreboard/<tier>.tsv`. -/
def tierMain (tier : String) (enc : Encoding)
    (measure : IO (Array String × Array Row)) (selftest : IO UInt32)
    (args : List String) : IO UInt32 :=
  tierMainAt (tsvPath tier) tier enc measure selftest args

/-- A tier producer's `--selftest`: run `body` with a recorder, print every
failure it recorded, and exit on whether there were any. Five producers wrote
this frame out in nine identical lines each, so a producer that reported a
failure differently — or swallowed one — would have looked like the others.
One frame: a tier's selftest is its assertions and nothing else. -/
def tierSelftest (tier : String) (body : (String → Bool → IO Unit) → IO Unit) :
    IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  body fun why ok => unless ok do fails.modify (why :: ·)
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println s!"{tier} selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

end Scoreboard

/-! ## The HTML freshness key, built hermetically

A browser matrix is only as fresh as the pages it was measured on, so the
`htmlreader` tier compares a key of the HTML this tree emits with the one the
matrix recorded. The key used to rebuild the corpus through the CLI, which
reads the host: the TeX tree's fonts through `kpsewhich`, whatever boundary
tool is on `PATH`, `LEANTEX_FONT`, the user cache. With TeX off `PATH` or
`LEANTEX_FONT` exported the same tree failed its gate. So the key is built
in-process from in-repo inputs only — the corpus and its shipped faces — the
way the suite builds a golden fixture: the one shipped face in every slot,
the shipped math face where a document reaches math, a shipped fallback face
per icon scalar, images read beside the fixture, and boundary pictures left
unfulfilled (no tool runs). It then tracks the engine rather than the host,
which is what freshness is for.

It mirrors the driver's HTML path (`Main.frontend`, then the emission's
configuration) over that environment. A change to the driver's own glue is
therefore not seen by the key — routed: lift that glue into a library
function both call. -/

namespace Scoreboard.Hermetic

open LeanTex.Core LeanTex.Cli

/-- Every slot and variant on face 0 — the one-face set's index, as the
suite's `oneFaceOf` and the driver's `singleFaceIndex` spell it. -/
def oneFaceIndex : Array ((Nat × Nat × Bool) × Nat) :=
  ((List.range 3).flatMap fun slot =>
    [((slot, 400, false), 0), ((slot, 700, false), 0),
     ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray

/-- A face parsed once per run, however many fixtures load it. -/
def loadFont (cache : IO.Ref (Array (String × Font.Font))) (path : String) :
    IO (Option Font.Font) := do
  if let some (_, f) := (← cache.get).find? (·.1 == path) then return some f
  match Font.parse (← IO.FS.readBinFile path) with
  | .ok f =>
    cache.modify (·.push (path, f))
    return some f
  | .error _ => return none

def isFaceFile (name : String) : Bool :=
  name.endsWith ".ttf" || name.endsWith ".otf"

/-- The shipped faces, probed file by file in name order: no scan cache and
no environment variable, so the answer is a function of the files. -/
def shippedFaces (dir : System.FilePath) : IO (Array FontDb.Face) := do
  let mut out : Array FontDb.Face := #[]
  for e in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    if isFaceFile e.fileName then
      if let some f ← FontDb.probe e.path.toString then out := out.push f
  return out

/-- The font set a fixture's page is keyed under: the suite's shape for a
golden fixture (`fixtureFontSet`), over the shipped faces only. -/
def fontSetFor (cache : IO.Ref (Array (String × Font.Font))) (oneFace : Font.FontSet)
    (faces : Array FontDb.Face) (fontsDir : System.FilePath) (doc : Ir.Doc) :
    IO Font.FontSet := do
  let withMath (path : String) : IO Font.FontSet := do
    match ← loadFont cache path with
    | some f => pure { oneFace with fonts := oneFace.fonts.push f, math := some oneFace.fonts.size }
    | none => pure oneFace
  let fs ← if doc.fonts.math.isSome then withMath (fontsDir / "FiraMath-Regular.otf").toString
    else if (Layout.docMathScalars doc).isEmpty then pure oneFace
    else match ← FontDb.pickMathFace faces (doc.fonts.body.getD "") with
      | some (face, _) => withMath face.path
      | none => pure oneFace
  let uncovered := (Layout.docScalars doc).filter fun ch =>
    0xE000 ≤ ch.toNat && ch.toNat ≤ 0xF8FF && fs.fonts.all fun f => (f.gid ch).isNone
  if uncovered.isEmpty then return fs
  let mut fs := fs
  for (ch, path) in ← FontDb.fallbackPicks faces uncovered do
    if let some f ← loadFont cache path then
      let idx := match fs.fonts.zipIdx.find? (fun p => p.1.family == f.family) with
        | some (_, i) => i
        | none => fs.fonts.size
      let fs' := if idx == fs.fonts.size then { fs with fonts := fs.fonts.push f } else fs
      fs := { fs' with fallback := fs'.fallback.push (ch, idx) }
  return fs

/-- The document's images, read beside it through graphicx's extension
resolution, with the bytes read — the page names them, so the key hashes
them. A boundary picture has no file and stays unfulfilled. -/
def storeFor (dir : System.FilePath) (doc : Ir.Doc) :
    IO (Image.Store × Array Diag × Array (String × ByteArray)) := do
  let mut fetched : Array (String × Image.Fetch) := #[]
  let mut read : Array (String × ByteArray) := #[]
  for src in Ir.imageRefs doc do
    let mut f : Image.Fetch := .missing src
    for cand in Image.sourceCandidates src do
      let p := dir / cand
      if ← p.pathExists then
        let bytes ← IO.FS.readBinFile p
        read := read.push (cand, bytes)
        f := .decoded (if cand == src then "" else cand) (Image.decode bytes)
        break
    fetched := fetched.push (src, f)
  let (store, diags) := Image.fulfil fetched
  return (store, diags, read)

/-- One fixture's page, or `none` where the driver would refuse to write one
(an error its `\allow` does not accept). The sequence is `Main.frontend`'s:
lex, parse, `\input` and `\data` fulfilled beside the file, one preparation,
a picture label measured against the preamble's set, the bibliography
fulfilled; then the emission configured as the driver configures it. -/
def pageFor (cache : IO.Ref (Array (String × Font.Font))) (oneFace : Font.FontSet)
    (faces : Array FontDb.Face) (corpus fontsDir : System.FilePath) (name : String) :
    IO (Option (String × Array (String × ByteArray))) := do
  let file := (corpus / s!"{name}.tex").toString
  let src ← IO.FS.readFile file
  let (toks, lexDiags) := Lex.lex file src
  let (raws, parseDiags) := Parse.parse file toks
  let (raws, inputDiags, _) ← Input.expandInputs file raws
  let (raws, dataDiags) ← Input.resolveData file raws
  let prepared := Elab.prepare file raws
  let pre := Elab.preambleDoc file prepared
  let preFs ← fontSetFor cache oneFace faces fontsDir pre
  let metric := Layout.labelMetric (Layout.Geom.ofPage pre.page) preFs
  let (doc, elabDiags, spans) := Elab.runPrepared file prepared
    (lexDiags ++ parseDiags ++ inputDiags ++ dataDiags) metric
  let (doc, bibDiags) ← Input.resolveBibliography file doc spans.bib
  let fs ← fontSetFor cache oneFace faces fontsDir doc
  let (store, imgDiags, read) ← storeFor corpus doc
  if (Diag.resolveAll doc.allow false (elabDiags ++ bibDiags ++ imgDiags)).errors > 0 then
    return none
  let css : HtmlDoc.CssMode := match cssFor doc.output.css with
    | .own => .own
    | .bulma => .bulma
    | .none => .none
  let cfg : HtmlDoc.Config :=
    { css, imgs := store
      fonts := if doc.fontPolicy == .embedded then some fs else none
      fontsDir := s!"{name}.fonts", assetsDir := s!"{name}.assets" }
  return some ((HtmlDoc.emit cfg doc).1, read)

/-- The key over a corpus directory holding `<name>.tex` fixtures and a
`fonts/` directory of shipped faces: every page that builds, the images it
reads, every shipped face once, and the names of the fixtures that do not
build — a page that stopped building changes what a browser would see. -/
def corpusKey (corpus : System.FilePath) : IO (Except String String) := do
  let fontsDir := corpus / "fonts"
  if !(← corpus.isDir) then return .error s!"{corpus} is not a directory"
  if !(← fontsDir.isDir) then return .error s!"{fontsDir} is not a directory"
  let faces ← shippedFaces fontsDir
  let cache ← IO.mkRef (#[] : Array (String × Font.Font))
  let some body ← loadFont cache (fontsDir / "OpenSans-Regular.ttf").toString
    | return .error s!"{fontsDir}/OpenSans-Regular.ttf does not parse"
  let oneFace : Font.FontSet := { fonts := #[body], index := oneFaceIndex }
  let mut blobs : Array (String × ByteArray) := #[]
  let mut unbuilt : Array String := #[]
  for e in (← corpus.readDir).qsort (·.fileName < ·.fileName) do
    if e.fileName.endsWith ".tex" then
      let name := (e.fileName.dropEnd ".tex".length).toString
      let page ← try pageFor cache oneFace faces corpus fontsDir name catch _ => pure none
      match page with
      | some (html, read) =>
        blobs := blobs.push (s!"{name}.html", html.toUTF8)
        for (cand, bytes) in read do
          blobs := blobs.push (s!"{name}.assets/{cand}", bytes)
      | none => unbuilt := unbuilt.push name
  if blobs.isEmpty then return .error "no corpus fixture built to HTML"
  for e in (← fontsDir.readDir).qsort (·.fileName < ·.fileName) do
    if isFaceFile e.fileName then
      blobs := blobs.push (s!"fonts/{e.fileName}", ← IO.FS.readBinFile e.path)
  blobs := blobs.push ("unbuilt", (String.intercalate " " unbuilt.toList).toUTF8)
  return .ok (Scoreboard.contentKey blobs)

end Scoreboard.Hermetic

namespace Scoreboard

/-- The freshness key of the HTML this tree emits for `tests/corpus`, built
hermetically (`Hermetic.corpusKey`): the one function `html-oracle` records
the key through and `htmlreader --check` recomputes it with, so the number
written and the number checked cannot differ by how each was built, and
neither can differ by host. Measured on this host: see PLAN. -/
def hermeticHtmlKey : IO (Except String String) := do
  try Hermetic.corpusKey "tests/corpus"
  catch e => return .error (toString e)

end Scoreboard
