/-
The diagaudit tier: the codes no `DiagAudit.registry` row binds, as headroom; `--census` reads
porcelain streams into rows of registered codes and counts only.
Usage: lake build TestsModules && lake env lean --run scripts/diagaudit.lean [--check | --selftest | --census <p>...]
-/
import Lean
import Tests.DiagAudit
import scripts.Board

open Scoreboard LeanTex.Core DiagAudit

namespace DiagAudit

open Lean

/-- Whether `e` holds the code as a value: its constructor, or its name spelled whole as a
string. -/
def holdsCode (e : Expr) (ctor : Name) (code : String) : Bool :=
  (e.find? fun x => x.isConstOf ctor || x == mkStrLit code).isSome

/-- A table of the suite's: a definition in a `Tests` module that takes no
argument, so a block that names it reads its value as data. -/
def suiteTable? (env : Environment) (n : Name) : Option Expr := do
  let ci ← env.find? n
  let v ← ci.value?
  let m ← env.getModuleIdxFor? n
  let mod ← env.header.moduleNames[m.toNat]?
  guard (mod.getRoot == `Tests && !ci.type.isForall)
  pure v

/-- Does a row of `testdata/compat-index/<pkg>.txt` refuse with `code`? -/
def indexRefuses (pkg code : String) : IO Bool := do
  let p : System.FilePath := s!"testdata/compat-index/{pkg}.txt"
  unless ← p.pathExists do return false
  return ((← IO.FS.readFile p).splitOn "\n").any fun l =>
    !l.startsWith "#" && (l.splitOn " ").contains ("refuse:" ++ code)

open Elab Term Meta in
/-- `pin_faults% rows`: how many rows `rows` holds, and each whose pin is not
about its code. -/
elab "pin_faults% " rows:term : term => do
  let env ← getEnv
  let e ← elabTerm rows none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e := (e.constName?.bind fun n => (env.find? n).bind (·.value?)).getD e
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr' e fun x => do
    if x.isAppOfArity ``AuditRow.mk 4 then
      found.modify (·.push x)
      return false
    return true
  let rowsE ← found.get
  let mut faults : Array String := #[]
  for r in rowsE do
    let args := r.getAppArgs
    let some ctor := args[0]!.constName?
      | faults := faults.push s!"a row whose code is no constructor: {← ppExpr args[0]!}"
    let some (.ctorInfo _) := env.find? ctor
      | faults := faults.push s!"a row whose code is no constructor: {ctor}"
    let code := ctor.getString!
    let fault : Option String ← match args[3]!.getAppFnArgs with
      | (``Pin.thm, #[_, stmt, proof]) =>
        pure <| if holdsCode stmt ctor code then none
          else some s!"{code}: its pin {proof.getAppFn.constName?.getD `_} is a theorem \
whose statement holds neither the constructor nor \"{code}\""
      | (``Pin.check, #[_, .letE _ _ (.const blk _) _ _]) =>
        let v := ((env.find? blk).bind (·.value?)).getD (mkConst ``Unit.unit)
        pure <| if holdsCode v ctor code ||
            (v.getUsedConstants.filterMap (suiteTable? env)).any (holdsCode · ctor code) then none
          else some s!"{code}: its pin {blk} is a check whose block, and the tables of the \
suite it reads, hold neither the constructor nor \"{code}\""
      | (``Pin.tier, #[.lit (.strVal t), .lit (.strVal item)]) =>
        pure <| if t == "compat" && (← indexRefuses ((item.splitOn ".").headD "") code) then none
          else some s!"{code}: its pin {t}/{item} is a tier item whose inputs refuse no {code}"
      | _ => pure (some s!"{code}: a pin not written thm%, check% or as a tier item")
    if let some f := fault then faults := faults.push f
  return toExpr (rowsE.size, faults.toList)

end DiagAudit

/-- The committed registry's rows read for their pins, and the faults. -/
def pinAudit : Nat × List String := pin_faults% registry

def measureTier : IO (Array String × Array Row) := do
  let suite ← suiteText
  unless pinAudit.1 == registry.length do
    throw (IO.userError s!"diagaudit: {pinAudit.1} of the registry's {registry.length} rows \
were read for their pins")
  unless pinAudit.2.isEmpty do
    throw (IO.userError s!"diagaudit: the registry is malformed: {"; ".intercalate pinAudit.2}")
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
a target rung and a pin that resolves and holds the code; {owed} owed",
    s!"# verdicts: {verdicts}",
    s!"# owed by the modules that apply them (a code counts in each), provenance, never gated: \
{modules}"],
    #[{ item := "verdict-debt-absent", value := debtCap - owed }])

/-- A porcelain line's raw string field, escapes left in place. -/
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

/-- One code and output scope in one document: its lines, the sites they account for, its
distinct losses, and whether they printed at more than one severity. -/
structure Tally where
  lines : Nat := 0
  sites : Nat := 0
  groups : Array String := #[]
  severities : Array String := #[]

/-- Scope is a field, so a subject or path holding a delimiter cannot impersonate an
output. -/
abbrev Tallies := Array ((String × Option String) × Tally)

/-- A census row holding no text: a code the registry names, and counts. -/
structure PublicRow where
  code : DiagCode
  lines : Nat
  sites : Nat
  groups : Nat
  docs : Nat
  mixed : Bool

/-- The bands, in the order the work is owed. -/
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

/-- One stream's tallies by code and output scope, and the document it built. -/
def readStream (text : String) (fallback : String) :
    String × Tallies × Nat × Nat := Id.run do
  let mut doc := fallback
  let mut tallies : Tallies := #[]
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
    let bucket := (code, strField line "output")
    let i := (tallies.findIdx? (·.1 == bucket)).getD tallies.size
    if i == tallies.size then tallies := tallies.push (bucket, {})
    tallies := tallies.modify i fun (c, t) => (c, { t with
      lines := t.lines + 1
      sites := t.sites + (natField line "sites").getD 1
      groups := if t.groups.contains key then t.groups else t.groups.push key
      severities := if t.severities.contains sev then t.severities else t.severities.push sev })
  return (doc, tallies, misfiled, unregistered)

/-- The census of some porcelain streams: common losses count once, from a document's
first stream, and each new output scope adds its own; a scope no diagnostic names is
unobserved. -/
def census (streams : Array (String × String)) : Census := Id.run do
  let mut docs : Array (String × Tallies) := #[]
  let mut disagreements := 0
  let mut misfiled := 0
  let mut unregistered := 0
  for (name, text) in streams do
    let (doc, tallies, mis, unreg) := readStream text name
    misfiled := misfiled + mis
    unregistered := unregistered + unreg
    match docs.findIdx? (·.1 == doc) with
    | none => docs := docs.push (doc, tallies)
    | some i =>
      let first := docs[i]!.2
      let observed (ts : Tallies) (scope : Option String) :=
        scope.isNone || ts.any (·.1.2 == scope)
      let keys := (first.map (·.1) ++ tallies.map (·.1)).toList.eraseDups
      for key in keys do
        if observed first key.2 && observed tallies key.2 then
          let a := ((first.find? (·.1 == key)).map (·.2.lines)).getD 0
          let b := ((tallies.find? (·.1 == key)).map (·.2.lines)).getD 0
          if a != b then disagreements := disagreements + 1
      let fresh := tallies.filter fun (key, _) => !observed first key.2
      docs := docs.set! i (doc, first ++ fresh)
  let mut rows : Array PublicRow := #[]
  for c in DiagCode.all do
    let per := docs.filterMap fun (_, ts) =>
      let buckets := ts.filterMap fun (key, t) => if key.1 == c.code then some t else none
      if buckets.isEmpty then none else some buckets
    if per.isEmpty then continue
    let all := per.flatten
    let sevs := all.foldl (fun acc t => t.severities.foldl
      (fun a s => if a.contains s then a else a.push s) acc) (#[] : Array String)
    rows := rows.push {
      code := c
      docs := per.size
      mixed := sevs.size > 1
      lines := all.foldl (· + ·.lines) 0
      sites := all.foldl (· + ·.sites) 0
      groups := all.foldl (· + ·.groups.size) 0 }
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

def selftest : IO UInt32 := tierSelftest "diagaudit" fun no => do
  let suite ← suiteText
  -- A pin that holds nothing is a fault, never a quiet unbinding.
  let broken := registry ++ [⟨.W0303, .refusal, .skipped, .tier "compat" "zz-no-such.impl"⟩]
  no "a row whose pin holds nothing makes the registry malformed"
    (match ← auditBound suite broken with | .error _ => true | .ok _ => false)
  let twice := registry ++ [⟨.W0201, .keep, .native, check% measureChecks⟩]
  no "a code with two rows makes the registry malformed"
    (match ← auditBound suite twice with | .error _ => true | .ok _ => false)
  no "a theorem pin is a proof, and so resolves"
    (← (thm% Diag.tallySites_sum_exact).resolves suite)
  -- A pin is about its code: each way to fail broken once, each way to hold shown once.
  no "every code is spelled as its constructor is named"
    (DiagCode.all.all fun c => (reprStr c).endsWith ("." ++ c.code))
  no "every row of the registry is read for its pin" (pinAudit.1 == registry.length)
  no s!"every committed pin holds its code ({pinAudit.2})" pinAudit.2.isEmpty
  no "a theorem whose statement names no code holds none"
    ((pin_faults% [(⟨.W0301, .native, .native, thm% Nat.add_comm⟩ : AuditRow)]).2.length == 1)
  no "a check whose block names another code does not hold this one"
    ((pin_faults% [(⟨.W0302, .keep, .native, check% measureChecks⟩ : AuditRow)]).2.length == 1)
  no "a check does not hold a code its tables leave out"
    ((pin_faults% [(⟨.W0201, .merge, .native, check% siteAccountingChecks⟩ : AuditRow)]).2.length
      == 1)
  no "a compat item whose index refuses another code does not hold this one"
    ((pin_faults% [(⟨.W0302, .keep, .native, .tier "compat" "cancel.impl"⟩ : AuditRow)]).2.length
      == 1)
  no "a statement naming the constructor holds the code"
    (pin_faults% [(⟨.W0334, .keep, .native, thm% Picture.unreachedName_accounts⟩ :
      AuditRow)]).2.isEmpty
  no "a statement spelling the code holds it"
    (pin_faults% [(⟨.W0320, .keep, .native, thm% Ir.headings_no_skip_judged⟩ :
      AuditRow)]).2.isEmpty
  no "a check holds a code through a suite table it reads"
    (pin_faults% [(⟨.W0362, .merge, .native, check% siteAccountingChecks⟩ : AuditRow)]).2.isEmpty
  -- A code losing its row is owed once more, charged to every module that applies it and no other.
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
  -- Nothing a document wrote reaches the census output.
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
  -- One loss at three sites counts as one group of three in its declared band.
  let site (sev : String) (loss : String) (sites : String) : String :=
    s!"\{\"event\":\"diagnostic\",\"severity\":\"{sev}\",\"code\":\"W0104\",\"loss\":\"{loss}\",\
\"message\":\"m\",\"file\":\"a.tex\",\"line\":1,\"col\":1,\"subject\":\"ctrl:x\"{sites}}\n"
  let three := site "warning" "config" ",\"sites\":3" ++ site "info" "config" ",\"sites\":0" ++
    site "info" "config" ",\"sites\":0"
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
  let scopedSite (output : String) (sites : String := "") :=
    site "warning" "config" (sites ++ s!",\"output\":\"{output}\"")
  let distinct := census #[("a", scopedSite "pdf" ++ scopedSite "html" ++ summary)]
  no "one subject affecting two outputs is two losses in one stream"
    (distinct.rows.map (fun r => (r.lines, r.sites, r.groups, r.docs)) == #[(2, 2, 2, 1)])
  let separated := #[("a.pdf", three ++ scopedSite "pdf" ++ summary),
    ("a.html", three ++ scopedSite "html" ++ summary)]
  let together := ("a.both", three ++ scopedSite "pdf" ++ scopedSite "html" ++ summary)
  for streams in [separated, separated.reverse, #[together], separated.push together,
      #[together] ++ separated] do
    let observed := census streams
    no "common losses count once and each output contributes its own losses"
      (observed.documents == 1 && observed.disagreements == 0 &&
        observed.rows.map (fun r => (r.lines, r.sites, r.groups, r.docs)) == #[(5, 5, 3, 1)])
  let scopedShort := census #[("a.first", scopedSite "pdf" ++ scopedSite "pdf" ++ summary),
    ("a.again", scopedSite "pdf" ++ summary)]
  no "a repeated output with a different count still reports disagreement"
    (scopedShort.disagreements == 1)
  no "a line whose loss disagrees with the registry is counted"
    ((census #[("s", site "warning" "degraded" "")]).misfiled == 1)

def main (args : List String) : IO UInt32 :=
  match args with
  | "--census" :: paths => runCensus paths
  | _ => tierMain "diagaudit" (.headroom debtCap) measureTier selftest args
