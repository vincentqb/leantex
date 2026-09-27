/-
The diagnostics audit, as a tier and as a census. Run from the repository
root after `lake build TestsModules` (the aggregate does that for you):

  lake env lean --run scripts/diagaudit.lean                      regenerate the baseline
  lake env lean --run scripts/diagaudit.lean --check              gate against the committed one
  lake env lean --run scripts/diagaudit.lean --selftest           the arithmetic and the confinement
  lake env lean --run scripts/diagaudit.lean --census <p>...      a census of porcelain streams

The tier measures adjudication debt: the codes no `DiagAudit.registry` row binds
(`Tests/DiagAudit.lean`), encoded as headroom, so a new code with no verdict
is a fall that fails the commit adding it, and a row whose pin stops
resolving is a fault. The modules that apply each owed code are provenance
and never gated: moving an emission between modules decides nothing, and a
gate on it would fail a behaviour-preserving refactor. It measures whether a
decision is *bound*, never whether it is right — rightness stays with the
review, and a new deliberate divergence from LaTeX stays the user's.
`diagdebt` is the other ledger: accounting debt (a censused code with no
subject). A code can be accounted for and undecided, or decided and
uncounted.

The census reads porcelain streams, never documents, and never gates: the
corpus it is for is private and off-tree. It bands every line by its declared
`loss`, never by its rendered severity (a repeat site's note and an accepted
loss both print `note`), groups sites by (code, subject) and never by message
text, adds each line's `sites` (the first line of a loss carries them all),
and counts each document once however many backends built it. Its rows hold a
registered code and numbers and nothing else, so nothing a document wrote can
reach its output, wherever that output is sent.
-/
import Tests.DiagAudit
import scripts.Board

open Scoreboard LeanTex.Core DiagAudit

def measureTier : IO (Array String × Array Row) := do
  let suite ← suiteText
  let bound ← match ← auditBound suite registry with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"diagaudit: the registry is malformed: {e}")
  let owed := (DiagCode.all.filter fun c => !bound.contains c).length
  let verdicts := String.intercalate ", " (Ruling.all.filterMap fun v =>
    let n := (registry.filter (·.verdict == v)).length
    if n == 0 then none else some s!"{v.word} {n}")
  let byModule := (unboundByModule (← codeSources) bound).qsort fun a b =>
    a.2.length > b.2.length || (a.2.length == b.2.length && a.1 < b.1)
  let modules := String.intercalate ", " (byModule.toList.filterMap fun (m, u) =>
    if u.isEmpty then none else some s!"{m} {u.length}")
  return (#[s!"# codes: {DiagCode.all.length} registered, {bound.length} bound to a verdict, \
a target rung and a pin that resolves; {owed} owed",
    s!"# verdicts: {verdicts}",
    s!"# owed by the modules that apply them (a code counts in each), provenance, never gated: \
{modules}"],
    #[{ item := "verdict-debt-absent", value := debtCap - owed }])

/-! ## The census -/

/-- A porcelain line's raw string field, escapes left in place: a group key
needs identity, not the text. -/
def strField (line key : String) : Option String :=
  match line.splitOn ("\"" ++ key ++ "\":\"") with
  | [_, rest] => Id.run do
    let mut out := ""
    let mut esc := false
    for c in rest.toList do
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then return some out
      out := out.push c
    return some out
  | _ => none

def natField (line key : String) : Option Nat :=
  match line.splitOn ("\"" ++ key ++ "\":") with
  | [_, rest] => (String.ofList (rest.toList.takeWhile Char.isDigit)).toNat?
  | _ => none

/-- One code in one document: its lines, the sites they account for, the
distinct losses among them, and whether they printed at more than one
severity. -/
structure Tally where
  lines : Nat := 0
  sites : Nat := 0
  groups : Array String := #[]
  severities : Array String := #[]

/-- A census row. No field holds text: a code the registry names, and counts. -/
structure PublicRow where
  code : DiagCode
  lines : Nat
  sites : Nat
  groups : Nat
  docs : Nat
  mixed : Bool

/-- The bands, in the order the work is owed: no artifact, ink owed, a
milestone's gap, a standard the document misses, nothing owed. -/
def bandOrder : List Loss := [.dropped, .degraded, .pending, .standard, .config, .info]

def bandIndex (l : Loss) : Nat := (bandOrder.idxOf? l).getD bandOrder.length

def PublicRow.render (r : PublicRow) : String :=
  s!"{r.code.code}\t{r.code.loss.label}\t{r.lines}\t{r.sites}\t{r.groups}\t{r.docs}\t\
{if r.mixed then "mixed" else "one"}"

structure Census where
  rows : Array PublicRow
  streams : Nat
  documents : Nat
  disagreements : Nat
  misfiled : Nat
  unregistered : Nat

/-- One stream's tallies by code string, and the document it built. -/
def readStream (text : String) (fallback : String) :
    String × Array (String × Tally) × Nat × Nat := Id.run do
  let mut doc := fallback
  let mut tallies : Array (String × Tally) := #[]
  let mut misfiled := 0
  let mut unregistered := 0
  for line in text.splitOn "\n" do
    if (strField line "event") == some "summary" then
      if let some f := strField line "file" then doc := f
    if (strField line "event") != some "diagnostic" then continue
    let some code := strField line "code" | continue
    let some kind := DiagCode.ofString? code
      | unregistered := unregistered + 1; continue
    if strField line "loss" != some kind.loss.label then misfiled := misfiled + 1
    let key := match strField line "subject" with
      | some s => "s:" ++ s
      | none => match strField line "file", natField line "line", natField line "col" with
        | some f, some l, some c => s!"p:{f}:{l}:{c}"
        | _, _, _ => s!"n:{tallies.size}:{line.length}"
    let sev := (strField line "severity").getD ""
    let i := (tallies.findIdx? (·.1 == code)).getD tallies.size
    if i == tallies.size then tallies := tallies.push (code, {})
    tallies := tallies.modify i fun (c, t) => (c, { t with
      lines := t.lines + 1
      sites := t.sites + (natField line "sites").getD 1
      groups := if t.groups.contains key then t.groups else t.groups.push key
      severities := if t.severities.contains sev then t.severities else t.severities.push sev })
  return (doc, tallies, misfiled, unregistered)

/-- The census of some porcelain streams. A document built by two backends
is counted once, from its first stream; its other streams are compared line
count by line count, and a difference is a disagreement, not a sum. -/
def census (streams : Array (String × String)) : Census := Id.run do
  let mut docs : Array (String × Array (String × Tally)) := #[]
  let mut disagreements := 0
  let mut misfiled := 0
  let mut unregistered := 0
  for (name, text) in streams do
    let (doc, tallies, mis, unreg) := readStream text name
    misfiled := misfiled + mis
    unregistered := unregistered + unreg
    match docs.find? (·.1 == doc) with
    | none => docs := docs.push (doc, tallies)
    | some (_, first) =>
      let codes := (first.map (·.1) ++ tallies.map (·.1)).toList.eraseDups
      for c in codes do
        let a := ((first.find? (·.1 == c)).map (·.2.lines)).getD 0
        let b := ((tallies.find? (·.1 == c)).map (·.2.lines)).getD 0
        if a != b then disagreements := disagreements + 1
  let mut rows : Array PublicRow := #[]
  for c in DiagCode.all do
    let per := docs.filterMap fun (_, ts) => (ts.find? (·.1 == c.code)).map (·.2)
    if per.isEmpty then continue
    let sevs := per.foldl (fun acc t => t.severities.foldl
      (fun a s => if a.contains s then a else a.push s) acc) (#[] : Array String)
    rows := rows.push {
      code := c
      docs := per.size
      mixed := sevs.size > 1
      lines := per.foldl (· + ·.lines) 0
      sites := per.foldl (· + ·.sites) 0
      groups := per.foldl (· + ·.groups.size) 0 }
  let sorted := rows.qsort fun a b =>
    bandIndex a.code.loss < bandIndex b.code.loss ||
      (bandIndex a.code.loss == bandIndex b.code.loss && a.groups > b.groups)
  return { rows := sorted, streams := streams.size, documents := docs.size,
           disagreements, misfiled, unregistered }

def Census.render (c : Census) : String := Id.run do
  let mut out := s!"# streams {c.streams}, documents {c.documents}; cross-backend \
disagreements {c.disagreements}; lines whose loss disagrees with the registry {c.misfiled}; \
unregistered codes {c.unregistered}\n"
  out := out ++ "code\tloss\tlines\tsites\tgroups\tdocs\tseverities\n"
  for r in c.rows do out := out ++ r.render ++ "\n"
  for l in bandOrder do
    let rs := c.rows.filter (·.code.loss == l)
    unless rs.isEmpty do
      out := out ++ s!"# band {l.label}: {rs.size} codes, {rs.foldl (· + ·.lines) 0} lines, \
{rs.foldl (· + ·.sites) 0} sites, {rs.foldl (· + ·.groups) 0} groups\n"
  return out

def runCensus (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "diagaudit: --census needs one or more porcelain files"
    return 2
  let mut streams : Array (String × String) := #[]
  for p in paths do streams := streams.push (p, ← IO.FS.readFile p)
  IO.print (census streams).render
  return 0

/-! ## The selftest: each rule broken once -/

def selftest : IO UInt32 := tierSelftest "diagaudit" fun no => do
  let suite ← suiteText
  -- P5: a pin that holds nothing is a fault, never a quiet unbinding.
  let broken := registry ++ [⟨.W0303, .refusal, .skipped, .tier "compat" "zz-no-such.impl"⟩]
  no "a row whose pin holds nothing makes the registry malformed"
    (match ← auditBound suite broken with | .error _ => true | .ok _ => false)
  let twice := registry ++ [⟨.W0201, .keep, .native, check% measureChecks⟩]
  no "a code with two rows makes the registry malformed"
    (match ← auditBound suite twice with | .error _ => true | .ok _ => false)
  no "a theorem pin is a proof, and so resolves"
    (← (thm% Diag.tallySites_sum_exact).resolves suite)
  -- P6: a code losing its row is owed once more, and charged to every
  -- module that applies it and to no other.
  let sources ← codeSources
  match ← auditBound suite registry, ← auditBound suite (registry.drop 1) with
  | .ok all, .ok fewer =>
    let dropped := (registry.head?.map (·.code.code)).getD ""
    no "dropping a row owes exactly one more code" (fewer.length + 1 == all.length &&
      !fewer.any (·.code == dropped))
    let before := unboundByModule sources all
    let after := unboundByModule sources fewer
    no "dropping a row owes its code in every module that applies it, and nowhere else"
      ((before.zip after).all fun ((m, b), (_, a)) =>
        let applies := ((sources.find? (moduleItem ·.1 == m)).map (·.2.contains dropped)).getD false
        a.length == b.length + (if applies then 1 else 0))
    no "the dropped row's code is applied somewhere, so the drop is seen"
      (sources.any (·.2.contains dropped))
  | _, _ => no "the committed registry is well formed" false
  no "encoding: more unbound codes read as a lower value"
    (debtCap - (2 : Int) < debtCap - (1 : Int))
  no "a module's item is its path under LeanTex/, dotted"
    (moduleItem "LeanTex/Core/Elab.lean" == "Core.Elab" && moduleItem "Main.lean" == "Main")
  -- P1: nothing a document wrote reaches the census output.
  let mark := "zqleakzq"
  let leak := s!"\{\"event\":\"diagnostic\",\"severity\":\"warning\",\"code\":\"W0301\",\
\"loss\":\"degraded\",\"message\":\"unknown command '\\\\{mark}'\",\"file\":\"{mark}.tex\",\
\"line\":3,\"col\":1,\"help\":\"{mark}\",\"subject\":\"ctrl:{mark}\"}\n\
\{\"event\":\"diagnostic\",\"severity\":\"warning\",\"code\":\"W9{mark}\",\"loss\":\"info\",\
\"message\":\"{mark}\"}\n\
\{\"event\":\"summary\",\"file\":\"{mark}.tex\",\"ok\":true,\"output\":\"{mark}.pdf\"}\n"
  let leaked := (census #[(mark ++ ".porcelain", leak)]).render
  no "no string a stream carries reaches the census output" (!containsSub leaked mark)
  no "an unregistered code is counted, never printed"
    ((census #[("s", leak)]).unregistered == 1)
  -- P2 and P3: one loss at three sites, the first a warning and two notes
  -- after it, counts as one group of three sites in its declared band.
  let site (sev : String) (loss : String) (sites : String) : String :=
    s!"\{\"event\":\"diagnostic\",\"severity\":\"{sev}\",\"code\":\"W0104\",\"loss\":\"{loss}\",\
\"message\":\"m\",\"file\":\"a.tex\",\"line\":1,\"col\":1,\"subject\":\"ctrl:x\"{sites}}\n"
  let three := site "warning" "config" ",\"sites\":3" ++ site "note" "config" ",\"sites\":0" ++
    site "note" "config" ",\"sites\":0"
  let c := census #[("a.pdf.porcelain", three)]
  no "a loss printed as a warning and two notes is one row in its declared band"
    (c.rows.size == 1 && (c.rows.map fun r => (r.code.code, r.lines, r.sites, r.groups, r.mixed))
      == #[("W0104", 3, 3, 1, true)] && c.misfiled == 0)
  -- A document built twice is counted once, and a backend difference is named.
  let summary := "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":true}\n"
  let twoBuilds := census #[("a.pdf", three ++ summary), ("a.html", three ++ summary)]
  no "two builds of one document count once" (twoBuilds.documents == 1 &&
    (twoBuilds.rows.map (·.sites)) == #[3] && twoBuilds.disagreements == 0)
  let oneShort := census #[("a.pdf", three ++ summary),
    ("a.html", site "warning" "config" "" ++ summary)]
  no "a backend that reports a different count is a disagreement" (oneShort.disagreements == 1)
  no "a line whose loss disagrees with the registry is counted"
    ((census #[("s", site "warning" "degraded" "")]).misfiled == 1)

def main (args : List String) : IO UInt32 :=
  match args with
  | "--census" :: paths => runCensus paths
  | _ => tierMain "diagaudit" (.headroom debtCap) measureTier selftest args
