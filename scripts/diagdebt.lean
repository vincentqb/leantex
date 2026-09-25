/-
The diagnostics debt, read as Lean values. Run from the repository root
after `lake build TestsModules` (the aggregate does that for you):

  lake env lean --run scripts/diagdebt.lean              regenerate the baseline
  lake env lean --run scripts/diagdebt.lean --check      gate against the committed one
  lake env lean --run scripts/diagdebt.lean --selftest   the encoding

`subjectDebt` in `Tests/Diag.lean` is the censused codes that emit with no
subject and so sit outside `Diag.tallySites`'s census. AGENTS.md already
says that list "may fall and never rise", so the ratchet here mechanises an
existing rule. This tier imports the module and measures the *value* rather
than counting lines of source: a count read off source text drifts from the
value the suite checks the first time a row is reformatted, and nothing
would see it.

`siteAccounting` is deliberately **not** ratcheted, and this is the
correction the review found. Its rows are what AGENTS.md's obligation table
*prescribes* adding — "fold the fragment into the first code's message, or
land a `siteAccounting` row naming the file that owes the merge" — and PLAN
names that row as the shape of a routed fix. A tier that fails when the
list grows would turn a specialist's routed finding into a regression, and
rows also appear when a new probe discovers a collision rather than when
code creates one. So the count is a provenance line: data, never gated.

Encoded as headroom, so a shrinking debt reads as a rising number.

What these numbers mean, exactly: they are the registries' lengths, and the
registries equal the real debt only because `subjectCensusChecks` and
`siteAccountingChecks` hold in both directions. On a tree where `lake test`
fails, this tier measures two lists and not the debt.
-/
import Tests.Diag
import scripts.Board

open Scoreboard LeanTex.Core

def measureTier : IO (Array String × Array Row) := do
  let censused := (DiagCode.all.filter (·.censused)).length
  let debt := subjectDebt.length
  let sites := siteAccounting.length
  return (#[s!"# codes: {DiagCode.all.length} registered, {censused} censused; \
subjects owed by {debt} of them",
    s!"# site collisions with a row: {sites} — provenance, never gated: \
AGENTS.md prescribes adding a row to route a fix"], #[
    { item := "subject-debt-absent", value := debtCap - Int.ofNat debt }])

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let no (why : String) (ok : Bool) : IO Unit := do
    unless ok do fails.modify (why :: ·)
  -- The registries are read as values, so these are facts about the module
  -- and not about its formatting: a reflowed row cannot move them.
  no "subjectDebt is a non-empty list of codes" (!subjectDebt.isEmpty)
  no "subjectDebt holds no duplicate" (subjectDebt.eraseDups.length == subjectDebt.length)
  no "every code owing a subject is a registered code"
    (subjectDebt.all fun c => (DiagCode.all.map (·.code)).contains c)
  no "every code owing a subject is censused -- an uncensused code owes no subject"
    (subjectDebt.all fun c => (DiagCode.all.filter (·.censused)).any (·.code == c))
  no "siteAccounting rows name two distinct codes"
    (siteAccounting.all fun r => r.1 != r.2.1)
  no "encoding: a shorter debt list reads as a higher value"
    (debtCap - (1 : Int) > debtCap - (2 : Int))
  -- The correction this tier carries: adding a siteAccounting row is what
  -- AGENTS.md prescribes to route a fix, so the count is provenance. This
  -- fails if anyone gives it an item.
  let (prov, rows) ← measureTier
  no s!"siteAccounting is not an item ({String.intercalate ", " (rows.map (·.item)).toList})"
    (!rows.any fun r => containsSub r.item "site")
  no "the site-collision count is still reported, as provenance"
    (prov.any (containsSub · "site collisions"))
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "diagdebt selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 :=
  tierMain "diagdebt" (.headroom debtCap) measureTier selftest args
