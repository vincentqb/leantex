/-
The diagdebt tier: `subjectDebt`'s length as headroom; `siteAccounting`'s is provenance, never
gated.
Usage: lake build TestsModules && lake env lean --run scripts/diagdebt.lean [--check | --selftest]
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

def selftest : IO UInt32 := tierSelftest "diagdebt" fun no => do
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
  -- Adding a siteAccounting row routes a fix, so its count is provenance and never an item.
  let (prov, rows) ← measureTier
  no s!"siteAccounting is not an item ({String.intercalate ", " (rows.map (·.item)).toList})"
    (!rows.any fun r => containsSub r.item "site")
  no "the site-collision count is still reported, as provenance"
    (prov.any (containsSub · "site collisions"))

def main (args : List String) : IO UInt32 :=
  tierMain "diagdebt" (.headroom debtCap) measureTier selftest args
