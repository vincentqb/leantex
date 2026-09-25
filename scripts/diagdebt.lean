/-
The diagnostics debt, read as Lean values. Run from the repository root
after `lake build TestsModules`:

  lake env lean --run scripts/diagdebt.lean              regenerate the baseline
  lake env lean --run scripts/diagdebt.lean --check      gate against the committed one
  lake env lean --run scripts/diagdebt.lean --selftest   the encoding

Two registries in `Tests/Diag.lean` carry today's debt: `subjectDebt`, the
censused codes that emit with no subject and so sit outside
`Diag.tallySites`'s census, and `siteAccounting`, the spans where two codes
name one site with only one of them counted. Both are frozen baselines that
may fall and never rise, and both are *lists* — so this tier imports the
module and measures the values, rather than counting lines of source. A
count read off source text drifts from the value the suite checks the first
time a row is reformatted, and nothing would see it.

Encoded as headroom, so a shrinking debt reads as a rising number: the
`optfold` work reducing `subjectDebt` lands here as an improvement, which is
what it is.
-/
import Tests.Diag
import scripts.Board

open Scoreboard LeanTex.Core

def measureTier : IO (Array String × Array Row) := do
  let censused := (DiagCode.all.filter (·.censused)).length
  let debt := subjectDebt.length
  let sites := siteAccounting.length
  return (#[s!"# codes: {DiagCode.all.length} registered, {censused} censused; \
subjects owed by {debt} of them; {sites} site collisions with a row"], #[
    { item := "site-collisions-absent", value := debtCap - Int.ofNat sites },
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
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "diagdebt selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 :=
  tierMain "diagdebt" (.headroom debtCap) measureTier selftest args
