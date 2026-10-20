/-
The scoreboard core: tier baselines (`testdata/scoreboard/<tier>.tsv`), their parser and
validator, and the one ratchet every tier's `--check` and the base check apply; with the vendored
pins' faults, the checkout walk and the native PDF fixtures the tiers share.
-/
import LeanTex.Cli.FontDiscovery
import LeanTex
import LeanTex.Cli.ImageAssets
import LeanTex.Cli.BrowserFaces
import LeanTex.Cli.Publication
import LeanTex.Cli.Driver
import scripts.Gate
import Lean.Data.Json

namespace Scoreboard

/-- The headroom ceiling: a headroom item's value is `debtCap - count`; a constant, since
raising it would raise every headroom item at once. -/
def debtCap : Int := 1000

/-- The lowest value a ranked `raw` item can hold; a negative value marks an item outside
the denominator. -/
def rawFloor : Int := 0

structure Row where
  item : String
  value : Int
deriving BEq, Inhabited

/-- How a tier's values relate to its measurements, read off the `# encoding:` line. -/
inductive Encoding where
  | headroom (cap : Int)
  | pairs (part whole : String)
  | raw
deriving BEq, Inhabited

def Encoding.render : Encoding → String
  | .headroom cap => s!"headroom cap={cap}"
  | .pairs p w => s!"pairs {p}/{w}"
  | .raw => "raw"

/-- A lowering line's standing: a request, which authorises one fall in the next
regeneration, or the record of a fall written, which authorises nothing. -/
inductive LowerState where
  | pending
  | applied
deriving DecidableEq, Inhabited, Repr

def LowerState.tag : LowerState → String
  | .pending => "# lowered:"
  | .applied => "# lowered (applied):"

/-- `# lowered: <item> <old>→<new> — <why>`, or its applied record; the arrow pair is the
last token before the reason, since an item may hold spaces. -/
structure Lowered where
  item : String
  old : Int
  new : Int
  why : String
  state : LowerState := .pending
deriving BEq, Inhabited

def Lowered.render (w : Lowered) : String :=
  s!"{w.state.tag} {w.item} {w.old}→{w.new} — {w.why}"

/-- The same text, whatever the standing. -/
def Lowered.sameLine (a b : Lowered) : Bool :=
  a.item == b.item && a.old == b.old && a.new == b.new && a.why == b.why

structure Tsv where
  provenance : Array String
  rows : Array Row
  retired : Array (String × String)
  /-- Every lowering line, requests and records, in file order, carried forward on
  regeneration. -/
  lowered : Array Lowered
  /-- `none`: the tier declares no encoding; it is gated but not ranked. -/
  encoding : Option Encoding
  /-- `# retired-tier: <why>`: the file is the tombstone of a retired tier. -/
  tierRetired : Option String := none
deriving Inhabited

def baselineDir : String := "testdata/scoreboard"

def tsvPath (tier : String) : String := s!"{baselineDir}/{tier}.tsv"

def scriptPath (tier : String) : String := s!"scripts/{tier}.lean"

/-- The item's spelling faults: only an empty name, since rows split on their tab and an
item may hold spaces. -/
def itemFaults (item : String) : Option String :=
  if item.isEmpty then some "an empty item name" else none

/-- `# retired: <item> — <why>`, the em dash required so a retirement without a reason is
a malformation. -/
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

/-- Parse a baseline; faults about the set of rows are `validate`'s, so every one can be
reported at once. -/
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

/-- Faults of a committed baseline: row order and uniqueness, and each lowering request
naming the fall from the floor the file commits (or the cap, for an unbaselined headroom
item); a record is never held to the rows. -/
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

/-- Faults of a fresh measurement against the committed file: a measured item the file
retires is one. -/
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

/-- One change the ratchet saw, as a value a judge reads. -/
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

/-- Whether the committed floor is the measurement: any change, a loss or an unrecorded
gain, fails `--check`. -/
def Delta.checkPasses (d : Delta) : Bool := d.changes.isEmpty

/-- Whether a lowering line authorises a change: a request authorises exactly the fall it
names, a record nothing, and no lowering a vanish. -/
def Lowered.authorises (w : Lowered) : Change → Bool
  | .fell i o n => w.state == .pending && w.item == i && w.old == o && w.new == n
  | _ => false

/-- Compare a fresh measurement against the committed baseline, retirement read off the
baseline; in a `headroom` tier an item the baseline never saw is compared against the
cap. -/
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

/-- The losses no request in the committed file authorises; regeneration writes only when
there are none. -/
def unauthorised (base now : Tsv) : Array Change :=
  (ratchet base now).losses.filter fun c => !(base.lowered.any (·.authorises c))

/-- The requests no loss of this measurement answers, refused rather than carried. -/
def unusedLowerings (base now : Tsv) : Array Lowered :=
  let losses := (ratchet base now).losses
  base.pendingLowerings.filter fun w => !(losses.any w.authorises)

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

/-- The lowering lines the tree's file carries that the base's does not, as a multiset
cancelled only within one standing, so a record spending a base request is new. -/
def newLowerings (base tip : Tsv) : Array Lowered :=
  let step := fun (acc : List Lowered × Array Lowered) (w : Lowered) =>
    if acc.1.any (· == w) then (acc.1.eraseP (· == w), acc.2)
    else (acc.1, acc.2.push w)
  (tip.lowered.foldl step (base.lowered.toList, #[])).2

/-- The items the tree's file retires that the base's does not record as retired; a
retirement the base only requests is unspent there. -/
def newRetirements (base tip : Tsv) : Array String :=
  tip.retired.filterMap fun (i, _) =>
    if base.isRetired i && !base.pendingRetirements.contains i then none else some i

/-- One pass: the lowest `new` among the lines usable from `m`, a line usable when its
`old` is at or above `m`, since values may rise freely. -/
def reachStep (lines : List Lowered) (m : Int) : Int :=
  lines.foldl (fun acc w => if m ≤ w.old ∧ w.new < acc then w.new else acc) m

/-- The lowest value an item can reach from `c`, rising freely and falling only along
`lines`; one pass per line reaches the fixed point. -/
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

/-- One baselined item's base-check verdict: it held `c` at the base and `tip` in the
tree; it may rise, fall only as far as the new lines reach, and vanish only where
`vanishOk`. -/
def itemAccepted (c : Int) (tip : Option Int) (lines : List Lowered) (vanishOk : Bool) :
    Bool :=
  match tip with
  | some v => decide (c ≤ v) || decide (reach lines c ≤ v)
  | none => vanishOk

theorem itemAccepted_monotone (c v : Int) (lines : List Lowered) (b : Bool)
    (h : itemAccepted c (some v) lines b = true) :
    c ≤ v ∨ ∃ w ∈ lines, w.new ≤ v := by
  simp only [itemAccepted, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact .inl h
  · rcases reach_mem lines c with he | ⟨w, hw, he⟩
    · exact .inl (he ▸ h)
    · exact .inr ⟨w, hw, he ▸ h⟩

/-- Every floor the base's file held that the tree's moved without a line written since
the base. -/
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

/-- What a passing base check credited, for the human landing it: each weakening against
the base, then each new line that can pay for one, marking a line whose text the base
already carries. -/
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

/-- The requests a committed file still holds: an unapplied `# lowered:` line and a `#
retired:` line beside its row; the base check reads such a file as `stale`. -/
def heldRequests (t : Tsv) : Array String :=
  t.pendingLowerings.map (·.render) ++
    t.retired.filterMap fun (i, why) =>
      if t.rows.any (·.item == i) then some s!"# retired: {i} — {why}" else none

/-- What the tree's copy of a baseline owes whatever the base holds: the format's faults,
and the requests it still holds, each saying whether the base holds it too. -/
def treeVerdict (base : Option Tsv) (t : Tsv) : Array String × Array String :=
  let inherited := (base.map heldRequests).getD #[]
  ((validate t).map (s!"the tree's file is malformed: {·}"),
   (heldRequests t).map fun l =>
     let also := if inherited.contains l then " — the base holds it too, so main carries it \
and every landing is stale until one spends it or deletes it" else ""
     s!"the tree's file still holds `{l}`, a request no regeneration has applied{also}; \
regenerate the tier with its producer, which spends it in the writing, or delete the line")

/-- The base check for one tier, as a result word and reasons: a baseline the tree dropped
is a fault, an unreadable file a fault, a floor moved without a new line `laundered`, a
held request `stale`; the base's file is held only to reading. -/
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

/-- The porcelain line a tier's `--check` prints and the aggregate reads back, one tier
per line. -/
def tierLine (tier : String) (items regressed improved : Nat) (result : String) : String :=
  s!"scoreboard: tier={tier} items={items} regressed={regressed} \
improved={improved} result={result}"

def field (line key : String) : Option String :=
  let toks := (line.splitOn " ").filter (!·.isEmpty)
  (toks.find? (·.startsWith (key ++ "="))).map (fun t =>
    ((t.drop (key.length + 1)).toString))

/-- The tiers the scoreboard expects; a name here missing its baseline or producer is a
fault. -/
def declaredTiers : List String :=
  ["cancel", "codedoc", "commonmark", "compat", "coverage", "diagaudit", "diagdebt", "doccost",
   "external", "htmla11y", "htmlreader", "mdtwin", "palette-oracle", "parity", "pdf-native", "purity",
   "rhythm", "schemes", "svg-native", "textlayer", "tikz-native", "typeset"]

/-- The declared tiers not landed yet, whose absence reports `missing`; the selftest fails
a name here that has both halves. -/
def pendingTiers : List String :=
  []

/-- The targets built before fan-out, so interpreted producers read current modules and
`doccost` the current `leantex`. -/
def tierImports : List String :=
  ["ScriptsModules", "TestsModules", "leantex"]

/-- The `tierImports` this tree's `lakefile.toml` declares. -/
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

/-- A tier name is `[a-z0-9-]+`: a file basename, a porcelain field, and a path git lists
unquoted. -/
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

/-- Whether a character acts on a terminal or hides rather than prints: the C0 and C1
controls, DEL, and the Unicode format characters that reorder or hide text. -/
def actsOnTerminal (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7F ≤ n && n ≤ 0x9F) || n == 0x061C || (0x200B ≤ n && n ≤ 0x200F) ||
    (0x2028 ≤ n && n ≤ 0x202E) || (0x2060 ≤ n && n ≤ 0x2069) || n == 0xFEFF

/-- A line as the scoreboard prints it: every character that acts rather than prints
spelled `\u{<hex>}`, so supplied text reaches a terminal as text, and everything else (`→`
and `—` included) unchanged. -/
def printable (s : String) : String := Id.run do
  if !s.any actsOnTerminal then return s
  let mut out := ""
  for c in s.toList do
    if actsOnTerminal c then out := out ++ "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
    else out := out.push c
  return out

/-- Every tier (the declared names and any undeclared baseline directly under
`testdata/scoreboard/`), and apart from them every name that is no tier name. -/
def discover : IO (Array String × Array String) := do
  let mut names : Array String := #[]
  let mut misnamed : Array String := #[]
  let mut found : Array String := declaredTiers.toArray
  let dir : System.FilePath := baselineDir
  if ← dir.isDir then
    for e in ← dir.readDir do
      let p := e.fileName
      if p.endsWith ".tsv" then
        let name := (p.dropEnd ".tsv".length).toString
        if !found.contains name then found := found.push name
  for n in found do
    if tierNameOk n then names := names.push n else misnamed := misnamed.push n
  return (names.qsort (· < ·), misnamed.qsort (· < ·))

/-- A deficit per item from the tier's own encoding; `raw` skips values below
`rawFloor`. -/
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

def readFileOr (p : String) : IO String := do
  if ← System.FilePath.pathExists p then IO.FS.readFile p else return ""

open LeanTex.Core in
/-- A content key over named byte blobs (FNV-1a, 64-bit, hex), names and order included,
which ties a tier measured elsewhere to the artifact it measured. -/
def contentKey (blobs : Array (String × ByteArray)) : String :=
  let h := blobs.foldl (init := Flate.fnvOffset) fun h (name, bytes) =>
    Flate.fnv64 ((Flate.fnv64 h name.toUTF8 ^^^ 0xff) * Flate.fnvPrime) bytes
  (Flate.hex16 h).toLower

private def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256's round constants (FIPS 180-4 §4.2.2). -/
private def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- SHA-256 (FIPS 180-4) as 64 lowercase hex digits, computed in Lean so no tool answers
for a pin. -/
def sha256Hex (msg : ByteArray) : String := Id.run do
  let mut data := msg.push 0x80
  while data.size % 64 != 56 do
    data := data.push 0
  let bits : UInt64 := msg.size.toUInt64 * 8
  for i in [0:8] do
    data := data.push (bits >>> ((7 - i).toUInt64 * 8)).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  let mut w : Array UInt32 := Array.replicate 64 0
  for blk in [0:data.size / 64] do
    for t in [0:16] do
      let o := blk * 64 + 4 * t
      w := w.set! t ((data[o]!.toUInt32 <<< 24) ||| (data[o + 1]!.toUInt32 <<< 16)
        ||| (data[o + 2]!.toUInt32 <<< 8) ||| data[o + 3]!.toUInt32)
    for t in [16:64] do
      let x := w[t - 15]!
      let y := w[t - 2]!
      let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
      let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
      w := w.set! t (w[t - 16]! + s0 + w[t - 7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut k := h[7]!
    for t in [0:64] do
      let t1 := k + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g))
        + sha256K[t]! + w[t]!
      let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
      k := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
      h[7]! + k]
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for x in h do
    for i in [0:8] do
      out := out.push digits[((x >>> ((7 - i).toUInt32 * 4)) &&& 0xf).toNat]!
  return out

/-- One browser face the external oracle gave a reader: the exact href and content digest
it loaded, or the converter whose failure kept it from the page. -/
inductive BrowserFaceResult where
  | captured (size : Nat) (sha256 : String)
  | failed (tool : String)
deriving BEq, Repr, Inhabited

structure BrowserFace where
  fixture : String
  href : String
  result : BrowserFaceResult
deriving BEq, Repr, Inhabited

namespace BrowserFace

/-- Capture exact converted bytes under the href the generated page names. -/
def captured (fixture href : String) (bytes : ByteArray) : BrowserFace :=
  { fixture, href, result := .captured bytes.size (sha256Hex bytes) }

/-- A conversion that produced no browser face. -/
def failed (fixture tool : String) : BrowserFace :=
  { fixture, href := "!" ++ tool, result := .failed tool }

def resultText : BrowserFaceResult → String
  | .captured size pin => s!"ok:{size}:{pin}"
  | .failed tool => "fail:" ++ tool

def render (face : BrowserFace) : String :=
  s!"browser-face: {face.fixture} {face.href} {resultText face.result}"

/-- One committed capture line; its names and hrefs are generated single tokens. -/
def parse (line : String) : Option BrowserFace := do
  let toks := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  let [_, fixture, href, result] := toks | none
  if !line.trimAscii.toString.startsWith "browser-face:" then none else
  match result.splitOn ":" with
  | ["ok", size, pin] =>
    let size ← size.toNat?
    if pin.length == 64 && pin.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') then
      some { fixture, href, result := .captured size pin }
    else none
  | ["fail", tool] =>
    if tool.isEmpty then none else some { fixture, href, result := .failed tool }
  | _ => none

end BrowserFace

/-- Browser-face failures read from the CLI's structured diagnostic stream, by code fields
and the record's words or detail; an unnamed or ambiguous converter stays unattributed. -/
def browserFaceFailures (fixture log : String) : Array BrowserFace :=
  ((log.splitOn "\n").filterMap fun line => do
    let record ← (Lean.Json.parse line).toOption
    let event ← (record.getObjValAs? String "event").toOption
    if event != "diagnostic" then none else do
    let code ← (record.getObjValAs? String "code").toOption
    if !["W0605", "W0378"].contains code then none else do
    let message ← (record.getObjValAs? String "message").toOption
    let said := message ++ ((record.getObjValAs? String "detail").toOption.map ("\n" ++ ·)).getD ""
    let tools := ["rsvg-convert", "pdftocairo", "xmllint"].filter fun tool =>
      (said.splitOn tool).length > 1
    return BrowserFace.failed fixture
      (match tools with | [tool] => tool | _ => "unattributed")).toArray

/-- The committed key of browser-converted faces, over hrefs and exact-byte digests in
canonical order. -/
def browserFaceKey (faces : Array BrowserFace) : String :=
  let ordered := faces.qsort fun a b =>
    if a.fixture == b.fixture then a.href < b.href else a.fixture < b.fixture
  contentKey (ordered.map fun face =>
    (face.fixture ++ "/" ++ face.href, (BrowserFace.resultText face.result).toUTF8))

private def browserFaceField (text name : String) : Array String :=
  ((text.splitOn "\n").filterMap fun raw =>
    let line := raw.trimAscii.toString
    if line.startsWith (name ++ ":") then
      some ((line.drop (name.length + 1)).toString.trimAscii.toString)
    else none).toArray

/-- Every browser-face row, refusing one malformed row rather than keying a subset. -/
def browserFaces (text : String) : Except String (Array BrowserFace) := do
  let mut out : Array BrowserFace := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "browser-face:" then
      let some face := BrowserFace.parse line
        | throw s!"malformed browser-face record: {line}"
      out := out.push face
  return out

/-- A rendering use's compact name: its image or source ordinal and the SHA-256 of its
exact data URL. -/
def browserFaceHref (fixture role : String) (index : Nat) (href : String) : String :=
  s!"{fixture}/{role}{index}-{sha256Hex href.toUTF8}.svg"

/-- An image's position and role with only its URL's digest erased, which a hermetic page
knows before conversion. -/
def browserImageIdentity (fixture href : String) : Option String := do
  let basePath := fixture ++ "/"
  if !href.startsWith basePath || !href.endsWith ".svg" then none else
  let file := (href.drop basePath.length |>.dropEnd 4).toString
  let [ident, key] := file.splitOn "-" | none
  if !(ident.startsWith "i" || ident.startsWith "p") then none else
  let digits := (ident.drop 1).toString
  let index ← digits.toNat?
  if digits != toString index then none else
  if key.length != 64 || !key.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then none else
  some (basePath ++ ident ++ ".svg")

mutual

/-- The two image-fetch sites of a typed HTML tree, walked structurally since HTML has no
generic fold. -/
def browserRefsOne (acc : Array (String × String)) : LeanTex.Core.Html.Node → Array (String × String)
  | .elem tag attrs kids =>
    let field := if tag == "img" then some ("i", "src")
      else if tag == "source" then some ("p", "srcset") else none
    let acc := match field with
      | some (role, key) => acc.push (role, ((attrs.find? (·.1 == key)).map (·.2)).getD "")
      | none => acc
    browserRefsList acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def browserRefsList (acc : Array (String × String)) : List LeanTex.Core.Html.Node → Array (String × String)
  | [] => acc
  | node :: rest => browserRefsList (browserRefsOne acc node) rest

end

/-- One required capture per SVG rendering use; an unfulfilled picture request is a known
SVG use too. -/
def browserExpectedFaces (fixture : String) (nodes : Array LeanTex.Core.Html.Node) :
    Array (String × String) := Id.run do
  let mut image := 0
  let mut poster := 0
  let mut out := #[]
  for (role, href) in browserRefsList #[] nodes.toList do
    let index := if role == "i" then image else poster
    if role == "i" then image := image + 1 else poster := poster + 1
    if href.startsWith "data:image/svg+xml;base64," ||
        href.startsWith LeanTex.Core.Ir.picSrcPrefix then
      out := out.push (fixture, s!"{fixture}/{role}{index}.svg")
  return out

/-- Faults that stop committed pass cells certifying another set of browser faces: the
rebuilt source key and the recomputed content key must match. -/
def browserFaceFaults (text freshSourceKey : String)
    (expected : Array (String × String) := #[]) : Array String := Id.run do
  let mut faults : Array String := #[]
  let sourceKeys := browserFaceField text "browser-face-src-key"
  if sourceKeys.isEmpty then
    faults := faults.push "no `browser-face-src-key:` line"
  else if sourceKeys.size > 1 then
    faults := faults.push "more than one `browser-face-src-key:` line"
  else if sourceKeys[0]! != freshSourceKey then
    faults := faults.push s!"browser-face source key {sourceKeys[0]!}, this tree builds {freshSourceKey}"
  let declaredKeys := browserFaceField text "browser-face-key"
  let declared := if declaredKeys.size == 1 then some declaredKeys[0]! else none
  if declaredKeys.isEmpty then
    faults := faults.push "no `browser-face-key:` line"
  else if declaredKeys.size > 1 then
    faults := faults.push "more than one `browser-face-key:` line"
  match browserFaces text with
  | .error e => faults := faults.push e
  | .ok faces =>
    let mut captured : Array (String × String) := #[]
    for i in [0:faces.size] do
      let face := faces[i]!
      if (faces.extract 0 i).any fun prior =>
          prior.fixture == face.fixture && prior.href == face.href then
        faults := faults.push s!"duplicate browser face {face.fixture}/{face.href}"
      match face.result with
      | .failed tool =>
        faults := faults.push s!"{face.fixture}: {tool} produced no browser face"
      | .captured size _ =>
        if size == 0 then
          faults := faults.push s!"empty browser face {face.fixture}/{face.href}"
        match browserImageIdentity face.fixture face.href with
        | some href =>
          let identity := (face.fixture, href)
          if captured.contains identity then
            faults := faults.push s!"duplicate browser image identity {face.fixture}/{href}"
          captured := captured.push identity
          if !expected.contains identity then
            faults := faults.push s!"unexpected browser image {face.fixture}/{href}"
        | none =>
          faults := faults.push s!"unclassified browser face {face.fixture}/{face.href}"
    for (fixture, href) in expected do
      if !captured.contains (fixture, href) then
        faults := faults.push s!"missing browser image {fixture}/{href}"
    if let some key := declared then
      let actual := browserFaceKey faces
      if key != actual then
        faults := faults.push s!"browser-face key {key}, committed records give {actual}"
  return faults

/-- A file pinned by the sha256 of the bytes it held when declared, in `sha256sum`'s
`<64 hex>  <path>` format. -/
structure Entry where
  pin : String
  path : String
deriving BEq

def pinnedEntry (pin path : String) : String := pin ++ "  " ++ path

/-- The entries of the pin list `file` holds; a line that is not a pinned entry is a
fault. -/
def parsePins (file text : String) : Except String (Array Entry) := Id.run do
  let mut out : Array Entry := #[]
  let mut n := 0
  for l in text.splitOn "\n" do
    n := n + 1
    if l.trimAscii.isEmpty || l.startsWith "#" then continue
    let pin := (l.take 64).toString
    let rest := (l.drop 64).toString
    if pin.length == 64 && pin.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))
        && rest.startsWith "  " && rest.length > 2 then
      out := out.push { pin, path := (rest.drop 2).toString }
    else
      return .error s!"{file}:{n}: not `<sha256>  <path>`; every entry carries its pin"
  return .ok out

/-- Where a vendored directory stops holding upstream's bytes: a pinned file whose bytes are not
its pin's or that is gone, and a file neither a pin nor `own` names. -/
def sumFaults (dir : String) (own : List String) : IO (Array String) := do
  let sums := dir ++ "/SHA256SUMS"
  let entries ← match parsePins sums (← readFileOr sums) with
    | .ok es => pure es
    | .error e => return #[e]
  let mut faults : Array String := #[]
  for e in entries do
    let p := dir ++ "/" ++ e.path
    if e.path.startsWith "/" || (e.path.splitOn "..").length > 1 then
      faults := faults.push s!"{sums}: '{e.path}' leaves the directory"
    else if !(← System.FilePath.pathExists p) then
      faults := faults.push s!"{p}: pinned in {sums}, and absent"
    else if sha256Hex (← IO.FS.readBinFile p) != e.pin then
      faults := faults.push s!"{p}: not the bytes its pin in {sums} names"
  for f in ← System.FilePath.walkDir dir do
    unless ← f.isDir do
      let rel := (f.toString.drop (dir.length + 1)).toString
      unless own.contains rel || entries.any (·.path == rel) do
        faults := faults.push s!"{f}: in the directory, and pinned by no line of {sums}"
  return faults

/-- Whether this `lakefile.toml` declares the package `leantex`, read as a key and a value. -/
def namesLeantex (lakefile : String) : Bool :=
  (lakefile.splitOn "\n").any fun l =>
    let t := String.ofList (l.toList.filter (!·.isWhitespace))
    t == "name=\"leantex\"" || t == "name='leantex'"

/-- Whether the resolved directory `dir`, or a directory above it, is a leantex checkout. -/
def insideCheckout (dir : System.FilePath) : IO Bool := do
  let mut cur := dir
  for _ in [0:4096] do
    let lf := cur / "lakefile.toml"
    if ← lf.pathExists then
      if namesLeantex ((← (IO.FS.readFile lf).toBaseIO).toOption.getD "") then return true
    match cur.parent with
    | some p => if p == cur then break else cur := p
    | none => break
  return false

def pdfNativeDir : String := "testdata/pdf-native"

/-- The committed native PDF fixtures, in a fixed order. -/
def pdfNativeFixtures : Array String :=
  #["cairo-chart.pdf", "geometry-dialect.pdf", "leantex-strokes.pdf", "lualatex-shade.pdf",
    "lualatex-strokedtext.pdf", "lualatex-text.pdf", "matplotlib-dialect.pdf", "print-dialect.pdf",
    "text-dialect.pdf"]

/-- The three modes every tier producer shares: no argument regenerates the baseline,
writing a fall only where a committed request authorises it; `--check` compares and writes
nothing, an absent or empty baseline a fault; `--selftest` runs the tier's predicates. -/
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
    -- A tier that measured nothing has already said why on stderr.
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
    -- A fall is written only as the committed file requests it; the request becomes a record.
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
  -- `stale`: the tree is ahead of its floor or the file holds a request; gated all the same.
  let result :=
    if !unauth.isEmpty then "regressed"
    else if !d.changes.isEmpty || !pendingL.isEmpty || !pendingR.isEmpty then "stale"
    else "ok"
  if result == "stale" && !d.gains.isEmpty then
    IO.eprintln s!"scoreboard: {tier}: the floor is behind the measurement; \
record it: lake env lean --run scripts/{tier}.lean"
  IO.println (tierLine tier fresh.rows.size d.losses.size d.gains.size result)
  return (if result == "ok" then 0 else 1)

/-- A tier producer's `main`: `tierMainAt` over `testdata/scoreboard/<tier>.tsv`. -/
def tierMain (tier : String) (enc : Encoding)
    (measure : IO (Array String × Array Row)) (selftest : IO UInt32)
    (args : List String) : IO UInt32 :=
  tierMainAt (tsvPath tier) tier enc measure selftest args

/-- A tier producer's `--selftest`: run `body` with a recorder, print every recorded
failure, and exit on whether there were any. -/
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

/-! The HTML freshness keys, built hermetically from in-repo inputs only: the pages,
images and shipped faces, and for vector browser faces their exact sources, hrefs and
conversion recipe. -/

namespace Scoreboard.Hermetic

open LeanTex.Core LeanTex.Cli

/-- A face parsed once per run, however many fixtures load it. -/
def loadFont (cache : IO.Ref (Array (String × Font))) (path : String) :
    IO (Option Font) := do
  if let some (_, f) := (← cache.get).find? (·.1 == path) then return some f
  match (← FontDiscovery.faceBytes path) >>= Font.parse with
  | .ok f =>
    cache.modify (·.push (path, f))
    return some f
  | .error _ => return none

def isFaceFile (name : String) : Bool :=
  name.endsWith ".ttf" || name.endsWith ".otf"

/-- The shipped faces, probed file by file in name order, with no scan cache or
environment variable. -/
def shippedFaces (dir : System.FilePath) : IO (Array FontDb.Face) := do
  let mut out : Array FontDb.Face := #[]
  for e in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    if isFaceFile e.fileName then
      if let some f ← FontDiscovery.probe e.path.toString then out := out.push f
  return out

/-- The font set a fixture's page is keyed under: the suite's shape over the shipped faces
only. -/
def fontSetFor (cache : IO.Ref (Array (String × Font))) (oneFace : Font.FontSet)
    (faces : Array FontDb.Face) (fontsDir : System.FilePath) (doc : Ir.Doc) :
    IO Font.FontSet := do
  let withMath (path : String) : IO Font.FontSet := do
    match ← loadFont cache path with
    | some f => pure { oneFace with
        fonts := oneFace.fonts.push f
        math := some oneFace.fonts.size
        mathAlphabets := f.mathAlphabetCoverage doc.fonts.mathSources }
    | none => pure oneFace
  let fs ← if doc.fonts.math.isSome then withMath (fontsDir / "FiraMath-Regular.otf").toString
    else if (Layout.docMathScalars doc).isEmpty then pure oneFace
    else match ← FontDiscovery.pickMathFace faces (doc.fonts.body.getD "") with
      | some (face, _) => withMath face.path
      | none => pure oneFace
  let uncovered := (Layout.docScalars doc).filter fun ch =>
    0xE000 ≤ ch.toNat && ch.toNat ≤ 0xF8FF && fs.fonts.all fun f => (f.gid ch).isNone
  if uncovered.isEmpty then return fs
  let mut fs := fs
  for (ch, path) in ← FontDiscovery.fallbackPicks faces uncovered do
    if let some f ← loadFont cache path then
      let idx := match fs.fonts.zipIdx.find? (fun p => p.1.family == f.family) with
        | some (_, i) => i
        | none => fs.fonts.size
      let fs' := if idx == fs.fonts.size then { fs with fonts := fs.fonts.push f } else fs
      fs := { fs' with fallback := fs'.fallback.push (ch, idx) }
  return fs

/-- The document's images read beside it through graphicx's extension resolution, with the
bytes read; a boundary picture stays unfulfilled. -/
def storeFor (dir : System.FilePath) (doc : Ir.Doc) (fs : Option Font.FontSet := none) :
    IO (Image.Store × Array Diag × Array (String × ByteArray) × Array (String × String)) := do
  let mut fetched : Array (Image.Request × Image.Fetch) := #[]
  let mut read : Array (String × ByteArray) := #[]
  let mut svgs : Array (Option Driver.SvgFetch) := #[]
  for req in Ir.imageRequests doc do
    let src := req.src
    let mut f : Image.Fetch := .missing src
    let mut fetchedSvg : Option Driver.SvgFetch := none
    for cand in Image.sourceCandidates src do
      let p := dir / cand
      if ← p.pathExists then
        let bytes ← IO.FS.readBinFile p
        read := read.push (cand, bytes)
        -- An SVG takes the driver's native route with no converter.
        if Image.isSvg cand then
          let r ← Driver.svgFetch src bytes req.page doc.info.locale.tag none
          f := .decoded (if cand == src then "" else cand) r.res (some bytes) none (some bytes) none
          fetchedSvg := some r
          break
        let decoded := Image.decodeRequest .default bytes req
        let mut companion := none
        if req.animated && !Image.isSvg cand then
          for ext in ["svg", "SVG"] do
            let rel := (System.FilePath.mk cand).withExtension ext
            match ← (IO.FS.readBinFile (dir / rel)).toBaseIO with
            | .ok svg =>
              companion := some svg
              read := read.push (rel.toString, svg)
              break
            | .error _ => pure ()
        f := .decoded (if cand == src then "" else cand)
          (decoded.map (·.1)) none (decoded.toOption.bind (·.2)) (some bytes) companion
        break
    fetched := fetched.push (req, f)
    svgs := svgs.push fetchedSvg
  let (store, diags) := Image.fulfilRequests fetched
  let store := FigureStore.attach store (svgs.map (·.map Driver.SvgFetch.drawn))
  let titles := (store.entries.zip svgs).filterMap fun (en, r) =>
    if en.info.isSome then r.bind (·.title) |>.map (en.src, ·) else none
  let diags := diags ++ svgs.flatMap fun r => (r.map (·.diags)).getD #[]
  match fs with
  | none => return (store, diags, read, titles)
  | some fs =>
    -- The driver's shaping and still faces, over the same faces.
    let (store, notes) := FigureStore.settle fs store
    return (store, diags ++ notes.map (·.2), read, titles)

/-- A canonical spelling for the page-selection part of a browser-face
conversion request. -/
private def pageSelectionKey : PdfRead.PageSelection → String
  | .first => "first"
  | .last => "last"
  | .number n => s!"page:{n}"

/-- A deterministic stand-in for a successful conversion's bytes, keyed and projected but
never published. -/
def faceStandIn (en : Image.Loaded) (p : BrowserFaces.Plan) : ByteArray :=
  s!"browser-face:{p.key}:{HtmlDoc.resolvedSrc en}".toUTF8

/-- The driver's plan interpreted with deterministic success stand-ins. -/
def facedStore (store : Image.Store) : Image.Store :=
  { store with entries := store.entries.map fun en =>
      let p := BrowserFaces.plan en
      match p.conversion? with
      | none => en
      | some _ => BrowserFaces.apply en p { bytes := .ok (faceStandIn en p), companionOk := true } }

/-- Read both roles from the same typed projection as the emitted page. -/
def facedHrefs (name : String) (imgs : Image.Store) (k : Nat) : Option String × Option String :=
  let assets := HtmlDoc.imageAssets imgs
  let href (poster : Bool) :=
    (assets.find? fun a => a.srcIndex == k && a.poster == poster).map fun a =>
      HtmlDoc.imageAssetHref (name ++ ".assets") a.file
  (href false, href true)

/-- The key blobs of captured vector inputs, the driver's shared plan and its typed
success projection; nothing is read or converted here. -/
def browserSourceBlobs (name : String) (doc : Ir.Doc) (store : Image.Store) :
    Array (String × ByteArray) := Id.run do
  let faced := facedStore store
  let mut out : Array (String × ByteArray) := #[]
  for req in Ir.imageRequests doc do
    let some k := store.findRequest? req | continue
    let some en := store.get? k | continue
    let resolved := HtmlDoc.resolvedSrc en
    let p := BrowserFaces.plan en
    let some _ := p.conversion? | continue
    let some bytes := en.source.or en.webSvg | continue
    let (href, poster) := facedHrefs name faced k
    let physicalPage := if Image.isSvg resolved then "none" else
      match PdfRead.pageNumber bytes req.page with
      | .ok n => toString n
      | .error e => "error:" ++ e
    let descriptor := s!"source={req.src}\nresolved={resolved}\nplan={p.key}\n\
page={pageSelectionKey req.page}\nphysical-page={physicalPage}\nanimated={req.animated}\n\
href={href.getD "none"}\nposter={poster.getD "none"}\ncompanion={en.companion.isSome}"
    out := out.push (s!"{name}/{k}/request", descriptor.toUTF8)
    out := out.push (s!"{name}/{k}/source/{resolved}", bytes)
    out := out.push (s!"{name}/{k}/standin", faceStandIn en p)
    if let some svg := en.companion then
      out := out.push (s!"{name}/{k}/companion", svg)
  return out

structure PageOutput where
  html : String
  read : Array (String × ByteArray)
  browserSources : Array (String × ByteArray)
  expectedFaces : Array (String × String)

/-- The phrase a corpus document writes in its own header to declare itself
no fixture (`Tests.corpusExcludeMarker`). -/
def excludeMarker : String := "excluded from the golden set"

/-- Whether a corpus document's header declares it no fixture: the marker within its first
sixteen lines, comment markers dropped, as the suite reads it. -/
def declaresExcluded (text : String) : Bool :=
  let header := ((text.splitOn "\n").take 16).map fun line =>
    let l := line.trimAscii.toString
    if l.startsWith "%" then (l.drop 1).toString.trimAscii.toString else l
  ((" ".intercalate header).splitOn excludeMarker).length > 1

/-- A corpus file's text as the driver's decoding door reads it, for a probe
that reads a document's header before the document is built. -/
def doorText (path : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile path
  let file := path.toString
  return if LeanTex.Core.Ir.Surface.ofPath file == .tex
    then (LeanTex.Core.Encoding.readDocument file bytes).1.text
    else (LeanTex.Core.Encoding.readMarkdown file bytes).text

/-- The corpus's documents in name order: every top-level file a surface reads, not declared
excluded. -/
def corpusDocs (corpus : System.FilePath) : IO (Array (String × System.FilePath)) := do
  let mut out : Array (String × System.FilePath) := #[]
  for e in ← corpus.readDir do
    let some ext := (LeanTex.Core.Ir.Surface.inputExtensions.map ("." ++ ·)).find?
      (e.fileName.endsWith ·) | continue
    if ← e.path.isDir then continue
    if declaresExcluded (← doorText e.path) then continue
    out := out.push ((e.fileName.dropEnd ext.length).toString, e.path)
  return out.qsort (·.1 < ·.1)

/-- One fixture's page as the driver builds it, or `none` where the driver would refuse to
write one. -/
def pageFor (cache : IO.Ref (Array (String × Font))) (oneFace : Font.FontSet)
    (faces : Array FontDb.Face) (fontsDir : System.FilePath) (name : String)
    (path : System.FilePath) : IO (Option PageOutput) := do
  let corpus := path.parent.getD "."
  let file := path.toString
  let .ok bytes ← Input.readSource file | return none
  let src ← Input.readDocument file bytes
  let prepared := Elab.prepareExecuted file src.executed
  let pre := Elab.preambleDoc file prepared
  let preFs ← fontSetFor cache oneFace faces fontsDir pre
  let metric := Layout.labelMetric (Layout.Geom.ofPage pre.page) preFs
  let (doc, elabDiags, spans) := Elab.runPrepared file prepared src.diags metric
  let (doc, bibDiags, ledger) ← Input.resolveBibliography file doc
    (Bib.FieldDoor.of file prepared).read spans.labels spans.bib src.ledger spans.cites
  let bibDiags := bibDiags ++ ledger.notes
  let fs ← fontSetFor cache oneFace faces fontsDir doc
  let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
  let (doc, alphaDiags) := Ir.resolveMathAlphas fs.mathAlphabets family doc
  let (store, imgDiags, read, titles) ← storeFor corpus doc (some fs)
  -- A figure that names itself answers the alternative the document left undeclared.
  let doc := FigureAlt.titled titles doc
  let elabDiags := FigureAlt.unanswered titles doc elabDiags
  if (Diag.resolveAll doc.allow false
      (elabDiags ++ bibDiags ++ alphaDiags ++ imgDiags)).errors > 0 then
    return none
  let css : HtmlDoc.CssMode := match cssFor doc.output.css with
    | .own => .own
    | .bulma => .bulma
    | .none => .none
  let faced := facedStore store
  let cfg : HtmlDoc.Config :=
    { css, imgs := faced
      fonts := if doc.fontPolicy == .embedded then some fs else none
      footBox := fun n band => some (Layout.footBandBox (Layout.Geom.ofPage doc.page) fs faced n band) }
  let .ok cfg ← LeanTex.Cli.Publication.captureHtmlResources file cfg doc | return none
  let (head, body, _) := HtmlDoc.emitTree cfg doc
  let browserSources := browserSourceBlobs name doc store
  return some { html := Html.document (doc.info.language.getD "en") head body, read, browserSources
                expectedFaces := browserExpectedFaces name body }

structure CorpusKeys where
  html : String
  browserFaceSource : String
  expectedFaces : Array (String × String)

/-- The two freshness keys over a corpus: `html` over every hermetic page, image and
shipped face, and `browserFaceSource` also over the vector inputs, hrefs and recipe. -/
def corpusKeys (corpus : System.FilePath) : IO (Except String CorpusKeys) := do
  let fontsDir := corpus / "fonts"
  if !(← corpus.isDir) then return .error s!"{corpus} is not a directory"
  if !(← fontsDir.isDir) then return .error s!"{fontsDir} is not a directory"
  let faces ← shippedFaces fontsDir
  let cache ← IO.mkRef (#[] : Array (String × Font))
  let some body ← loadFont cache (fontsDir / "OpenSans-Regular.ttf").toString
    | return .error s!"{fontsDir}/OpenSans-Regular.ttf does not parse"
  let oneFace := Font.FontSet.ofFace body
  let mut blobs : Array (String × ByteArray) := #[]
  let mut browserSources : Array (String × ByteArray) :=
    #[("conversion-contract", ImageAssets.browserFaceContract.toUTF8)]
  let mut unbuilt : Array String := #[]
  let mut expectedFaces : Array (String × String) := #[]
  for (name, path) in ← corpusDocs corpus do
    let page ← try pageFor cache oneFace faces fontsDir name path catch _ => pure none
    match page with
    | some page =>
      blobs := blobs.push (s!"{name}.html", page.html.toUTF8)
      for (cand, bytes) in page.read do
        blobs := blobs.push (s!"{name}.assets/{cand}", bytes)
      browserSources := browserSources ++ page.browserSources
      expectedFaces := expectedFaces ++ page.expectedFaces
    | none => unbuilt := unbuilt.push name
  if blobs.isEmpty then return .error "no corpus fixture built to HTML"
  for e in (← fontsDir.readDir).qsort (·.fileName < ·.fileName) do
    if isFaceFile e.fileName then
      blobs := blobs.push (s!"fonts/{e.fileName}", ← IO.FS.readBinFile e.path)
  blobs := blobs.push ("unbuilt", (String.intercalate " " unbuilt.toList).toUTF8)
  let html := Scoreboard.contentKey blobs
  browserSources := browserSources.push ("html-key", html.toUTF8)
  return .ok { html, browserFaceSource := Scoreboard.contentKey browserSources, expectedFaces }

/-- The HTML key alone. -/
def corpusKey (corpus : System.FilePath) : IO (Except String String) := do
  return (← corpusKeys corpus).map (·.html)

end Scoreboard.Hermetic

namespace Scoreboard

/-- Both hermetic keys for the shipped corpus, computed in one traversal. -/
def hermeticHtmlKeys : IO (Except String Hermetic.CorpusKeys) := do
  try Hermetic.corpusKeys "testdata/corpus"
  catch e => return .error (toString e)

/-- The text readers' modules, whose import closure their verdicts depend on. -/
def textReaderRoots : List String := ["LeanTex.Core.HtmlRead", "LeanTex.Core.PdfTextRead"]

/-- A module's source path in this tree. -/
def modulePath (m : String) : System.FilePath :=
  System.FilePath.mk (m.replace "." "/" ++ ".lean")

/-- The modules a source imports from this tree, whatever its import modifiers. -/
def treeImports (text : String) : List String :=
  (text.splitOn "\n").filterMap fun raw =>
    let toks := (raw.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    let toks := toks.filter fun t => t != "public" && t != "meta" && t != "private"
    match toks with
    | "import" :: rest =>
      let rest := rest.filter (· != "all")
      rest.head?.filter (·.startsWith "LeanTex.")
    | _ => none

/-- The readers' sources and every module of this tree they import, sorted by path. -/
def textReaderSources : IO (Array System.FilePath) := do
  let mut seen : Array String := #[]
  let mut work := textReaderRoots
  let mut out : Array System.FilePath := #[]
  for _ in [0:4096] do
    let m :: rest := work | break
    work := rest
    if seen.contains m then continue
    seen := seen.push m
    let path := modulePath m
    unless ← path.pathExists do continue
    out := out.push path
    work := treeImports (← IO.FS.readFile path) ++ work
  unless work.isEmpty do throw (IO.userError "the text readers' imports pass every module bound")
  return out.qsort (·.toString < ·.toString)

/-- Every file under a directory, sorted by path. -/
def filesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for f in ← dir.walkDir do
    unless ← f.isDir do out := out.push f
  return out.qsort (·.toString < ·.toString)

/-- The text-layer matrix's freshness key: the readers' import closure, the oracle and the corpus
fixtures it judged, so a changed reader, oracle or fixture needs the tools again. -/
def textLayerKey : IO String := do
  let mut blobs : Array (String × ByteArray) := #[]
  for p in (← textReaderSources).push "scripts/text-oracle.lean" do
    blobs := blobs.push (p.toString, ← IO.FS.readBinFile p)
  for f in ← filesUnder "testdata/corpus" do
    blobs := blobs.push (f.toString, ← IO.FS.readBinFile f)
  return contentKey blobs

end Scoreboard
