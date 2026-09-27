import Tests.Diag
import Tests.Layout
import Tests.Themes
import Tests.FontMath
import Tests.Surface
import scripts.Rung

/-!
# The diagnostics audit: every code's decided direction, and what holds it

An audit of a document's warnings decides, per code, where it goes next —
implement the construct, keep the code, fold it into another's accounting —
and the decision is worth something only while a checker holds it. A row
here is that decision as a value: the code, the verdict, the construct rung
the verdict aims at (the vocabulary `coverage` ranks constructs in), and the
pin that fails when the decision regresses.

A row has no free-text field. The pin is written as a reference that
resolves or does not compile (`thm%`, `check%`), or as a scoreboard item
that must exist in a committed baseline, so a row can only point at what is
already in the tree — an audit of a private document cannot leave its words
here. The reasons live beside the rows, as comments, where a reviewer reads
them.

`scripts/diagaudit.lean` ratchets the rows as the `diagaudit` tier: the codes
no row binds, charged in its provenance to the modules that apply them.
-/

open LeanTex.Core

namespace DiagAudit

/-- Where an audit decided a code goes next. -/
inductive Ruling where
  /-- Implement the construct natively; the code leaves the page's census. -/
  | native
  /-- A decided divergence from LaTeX: the code stays and names it. -/
  | divergence
  /-- Refused by design: the construct stays out and the code says so. -/
  | refusal
  /-- The code is right as it stands, and its pin holds it there. -/
  | keep
  /-- One construct accounted twice: fold it into the other code's accounting. -/
  | merge
  /-- The right loss at the wrong span or key. -/
  | resite
  /-- The right loss in the wrong words: a count, an invented key, a help. -/
  | message
  deriving Repr, BEq, DecidableEq

def Ruling.word : Ruling → String
  | .native => "native"
  | .divergence => "divergence"
  | .refusal => "refusal"
  | .keep => "keep"
  | .merge => "merge"
  | .resite => "resite"
  | .message => "message"

def Ruling.all : List Ruling :=
  [.native, .divergence, .refusal, .keep, .merge, .resite, .message]

/-- What holds a verdict. A theorem pin carries the proof itself, so it is a
theorem or it does not compile; a check pin elaborates the block it names,
so it exists or it does not compile, and it binds only while the suite runs
it; a tier pin binds while the committed baseline holds the item. Whether a
pin is *about* its code is decided where the pinned declarations are
readable, by the tier (`scripts/diagaudit.lean`): the suite's binary cannot
read a declaration's statement or body. -/
inductive Pin where
  | thm (name : Lean.Name) (stmt : Prop) (proof : stmt)
  | check (name : Lean.Name) (seen : Unit)
  | tier (tier item : String)

/-- `thm% n`: a pin to the theorem `n`, checked to be a proof where it is
written. -/
syntax "thm%" ident : term
macro_rules
  | `(thm% $n) => `(DiagAudit.Pin.thm $(Lean.quote n.getId) _ @$n)

/-- `check% n`: a pin to the check block `n`, elaborated where it is
written. -/
syntax "check%" ident : term
macro_rules
  | `(check% $n) => `(DiagAudit.Pin.check $(Lean.quote n.getId) (let _ := @$n; ()))

def Pin.name : Pin → String
  | .thm n _ _ | .check n _ => n.toString
  | .tier t i => t ++ "/" ++ i

structure AuditRow where
  code : DiagCode
  verdict : Ruling
  target : Rung
  pin : Pin

/-- The decided codes. A code with no row is owed a verdict; the tier counts
the debt, and a new code adds to it. -/
def registry : List AuditRow :=
  -- The four standard codes: the page is the declaration, and the judge
  -- that fires on it is the gate.
  [⟨.W0201, .keep, .native, check% measureChecks⟩,
   ⟨.W0202, .keep, .native, check% rhythmChecks⟩,
   ⟨.W0376, .keep, .native, check% a11yChecks⟩,
   -- The covered arm warns about the engine's own default cover: realize
   -- it per role at its one resolving site instead, as N0022 does.
   ⟨.W0345, .native, .native, check% contrastChecks⟩,
   -- A fallback face substitutes where lualatex substitutes silently.
   ⟨.W0009, .keep, .degraded, check% fallbackChecks⟩,
   -- The witness that the gap theorems' side condition was taken.
   ⟨.N0200, .keep, .rewritten, check% spacingChecks⟩,
   -- One element-style field closes it.
   ⟨.W0110, .native, .native, check% themeTitleShipChecks⟩,
   -- The strike and its value as a script; the index rows are the gate.
   ⟨.W0389, .native, .native, .tier "compat" "cancel.impl"⟩,
   -- A rewrite's note beside the refusal of what it produced, and a
   -- picture's constructs beside its placeholder: the siteAccounting rows.
   ⟨.N0100, .merge, .rewritten, check% siteAccountingChecks⟩,
   ⟨.W0362, .merge, .native, check% siteAccountingChecks⟩,
   -- A boundary refusal the rendered subset stands in for: the note names
   -- the withdrawal, and the subset's own codes carry the losses.
   ⟨.N0419, .keep, .degraded, check% pictureRouteChecks⟩,
   -- A line the author ended that the measure split; the paragraph's own
   -- last line is prose and sets as many lines as it needs, unnamed.
   ⟨.W0386, .keep, .degraded, check% titleBreakChecks⟩]

/-- An engine source's tier item: `LeanTex/Core/Elab.lean` is `Core.Elab`,
`Main.lean` is `Main`. -/
def moduleItem (path : String) : String :=
  let p := if path.startsWith "LeanTex/" then (path.drop "LeanTex/".length).toString else path
  let p := if p.endsWith ".lean" then (p.dropEnd ".lean".length).toString else p
  p.replace "/" "."

/-- The suite's own code, which a check pin must be run from: the driver and
every suite module but this one, which names each pinned block once by
writing it. -/
def suiteText : IO String := do
  let mut text := stripNonCode (← IO.FS.readFile "Tests.lean")
  for f in ← System.FilePath.walkDir "Tests" do
    if f.toString.endsWith ".lean" && f.toString != "Tests/DiagAudit.lean" then
      text := text ++ stripNonCode (← IO.FS.readFile f)
  return text

/-- Does the pin hold anything? A theorem pin always does — it is a proof.
A check pin does while the suite both defines and calls the block. A tier
pin does while the tier's committed baseline has a row for the item. -/
def Pin.resolves (suite : String) : Pin → IO Bool
  | .thm .. => pure true
  | .check n _ => pure ((suite.splitOn n.toString).length ≥ 3)
  | .tier t item => do
    let path : System.FilePath := s!"tests/scoreboard/{t}.tsv"
    if !(← path.pathExists) then return false
    return ((← IO.FS.readFile path).splitOn "\n").any (·.startsWith (item ++ "\t"))

/-- The codes a registry binds, or what makes it malformed: a code with two
rows, or a pin that holds nothing. A pin that stops resolving is a fault
rather than a quiet unbinding, so a row can never outlive its gate. -/
def auditBound (suite : String) (rows : List AuditRow) : IO (Except String (List DiagCode)) := do
  let mut bound : List DiagCode := []
  for r in rows do
    if bound.contains r.code then
      return .error s!"{r.code.code} has two audit rows"
    unless ← r.pin.resolves suite do
      return .error s!"{r.code.code}: its pin {r.pin.name} holds nothing"
    bound := r.code :: bound
  return .ok bound

/-- Per engine module, the codes it applies that no row binds. -/
def unboundByModule (sources : Array (String × List String)) (bound : List DiagCode) :
    Array (String × List String) :=
  sources.filterMap fun (path, applied) =>
    if applied.isEmpty then none
    else some (moduleItem path, applied.filter fun c => !bound.any (·.code == c))

end DiagAudit

open DiagAudit in
/-- **Every audit row is held by a checker, and every code can be charged.**
The registry read in both directions: a row whose pin resolves to nothing
fails here, not only in the tier, and a code no engine module applies has no
module to owe its verdict. -/
def diagAuditChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let suite ← suiteText
  match ← auditBound suite registry with
  | .error e => t s!"diag audit: {e}" false
  | .ok bound => t s!"diag audit: {bound.length} rows, each pin resolving" true
  let sources ← codeSources
  let charged := DiagCode.all.filter fun c => !sources.any (·.2.contains c.code)
  t s!"diag audit: every code is applied by some engine module ({charged.map (·.code)})"
    charged.isEmpty
  -- The resolver itself, once each way: a block the suite runs, a block it
  -- never names, an item a baseline holds, an item none holds.
  t "diag audit: a check the suite runs resolves"
    (← (check% a11yChecks).resolves suite)
  t "diag audit: a check nothing runs does not"
    !(← (Pin.check `zzNoSuchChecks ()).resolves suite)
  t "diag audit: a committed tier item resolves"
    (← (Pin.tier "compat" "cancel.impl").resolves suite)
  t "diag audit: an item no baseline holds does not"
    !(← (Pin.tier "compat" "zz-no-such.impl").resolves suite)
