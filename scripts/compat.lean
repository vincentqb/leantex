/-
Documented-command coverage, per package. Run from the repository root:

  lake env lean --run scripts/compat.lean              regenerate the baseline
  lake env lean --run scripts/compat.lean --check      gate against the committed one
  lake env lean --run scripts/compat.lean --selftest   the row reader

`tests/compat-index/<pkg>.txt` carries one row per documented command of a
package, each with the verdict the engine owes it. `lake test` probes every
row; this tier commits the shape of the index, so a row cannot quietly
leave it.

Two items per package: `<p>.rows`, every documented command, and
`<p>.impl`, those the engine implements. A `divergence:<code>` verdict is
listed separately for audit but remains an unimplemented row in the
coverage denominator; naming a difference deliberate cannot raise coverage.

**Implemented** means the verdict is `impl` *or* `inert:…` — one definition,
the same one `coverage` counts, because an `inert:` row is a recognised
command that legitimately moves no ink. Two committed numbers for one fact
with two definitions (303 here against 336 there, over the same 659 rows)
is the defect `scripts/Gate.lean` exists to prevent; this is the definition
that survives when the two tiers fuse.

Not done here, deliberately: the review also asks for the `pkg/<p>.` item
prefix, so these items share `coverage`'s namespace. That renames all 134
items at once, and a rename is 134 vanishes under the ratchet — the format
has no rename line, and inventing one to pay for a cosmetic alignment is
the wrong order. It belongs to the commit that actually fuses the two
tiers, which is a coordinated landing and pays the migration once.

Correction to the brief that asked for `impl` and `refuse` counts: a refusal
count cannot be ratcheted upward, because the way a refusal improves is by
becoming an implementation — which lowers it. `rows` is the coverage claim
and `impl` the depth claim, both monotone the right way, and `refuse` stays
a provenance line: data, never gated.
-/
import scripts.Board
import scripts.Rung

open Scoreboard

structure Pkg where
  name : String
  rows : Nat
  impl : Nat
  refuse : Nat
  decided : Nat := 0
deriving Inhabited

/-- Count one index file's documented rows. `impl` and `inert:` form the
numerator; refusals and deliberate divergences remain in the denominator,
with divergences also counted for the audit. -/
def countRows (name : String) (rows : Array IndexRow) : Pkg :=
  { name, rows := rows.size, impl := (rows.filter (·.implemented)).size
    refuse := (rows.filter (·.refused)).size, decided := (rows.filter (·.decided)).size }

def readIndex (name text : String) : Pkg :=
  countRows name ((text.splitOn "\n").filterMap IndexRow.parse?).toArray

def packages : IO (Array Pkg) := do
  return (← readCompatIndex).map fun (name, rows) => countRows name rows

def measureTier : IO (Array String × Array Row) := do
  let pkgs ← packages
  let mut rows : Array Row := #[]
  let mut totalRows := 0
  let mut totalImpl := 0
  let mut totalRefuse := 0
  let mut totalDecided := 0
  for p in pkgs do
    rows := rows.push { item := s!"{p.name}.rows", value := Int.ofNat p.rows }
    rows := rows.push { item := s!"{p.name}.impl", value := Int.ofNat p.impl }
    totalRows := totalRows + p.rows
    totalImpl := totalImpl + p.impl
    totalRefuse := totalRefuse + p.refuse
    totalDecided := totalDecided + p.decided
  return (#[s!"# packages: {pkgs.size}; rows: {totalRows}; impl: {totalImpl} \
(verdict impl or inert:, the one definition the coverage tier shares); \
refuse: {totalRefuse}; other verdicts: {totalRows - totalImpl - totalRefuse} \
(including {totalDecided} decided divergences; all remain in rows)"], rows)

def selftest : IO UInt32 := tierSelftest "compat" fun no => do
  let text := "# source: an invented manual §1\n\
body impl \\zzone{x}\n\
body refuse:W0301 \\zztwo\n\
preamble impl \\zzthree\n\
body inert:binds \\zzfour\n\
\n"
  let p := readIndex "zz" text
  no s!"rows: 4 expected, got {p.rows}" (p.rows == 4)
  no s!"impl: 3 expected, got {p.impl}" (p.impl == 3)
  no s!"refuse: 1 expected, got {p.refuse}" (p.refuse == 1)
  no "header prose is not a row" ((readIndex "zz" "# only prose\n").rows == 0)
  let missing ← (readCompatIndexAt (System.FilePath.mk
    "tests/compat-index-does-not-exist")).toBaseIO
  no "a missing compat-index input fails closed"
    (match missing with | .error _ => true | .ok _ => false)
  let empty ← (readCompatIndexAt (System.FilePath.mk "LeanTex/Cli")).toBaseIO
  no "a compat-index input with no index files fails closed"
    (match empty with | .error _ => true | .ok _ => false)
  -- The one definition of implemented, shared with the coverage tier: a
  -- recognised command that legitimately moves no ink counts. Two tiers
  -- counting the same index differently is what this pins shut.
  let isImpl (v : String) : Bool := (IndexRow.mk "body" v "\\zz").implemented
  no "definition: impl counts" (isImpl "impl")
  no "definition: inert: counts -- a recognised command that moves no ink"
    (isImpl "inert:binds")
  no "definition: a refusal does not count" (!isImpl "refuse:W0301")
  no "definition: an unknown verdict does not count" (!isImpl "zz")
  no "the index's inert row is inside the impl count"
    ((readIndex "zz" "body inert:binds \\zzone\n").impl == 1)
  no "a refusal rejects an extra diagnostic-code suffix"
    (!(IndexRow.mk "body" "refuse:W0301:extra" "\\zz").refused)
  no "a divergence rejects an extra diagnostic-code suffix"
    (!(IndexRow.mk "body" "divergence:W0301:extra" "\\zz").decided)
  -- The correction this tier exists to encode: a refusal becoming an
  -- implementation must not read as a loss.
  let before := readIndex "zz" "body refuse:W0301 \\zzone\n"
  let after := readIndex "zz" "body impl \\zzone\n"
  no "a refusal becoming an implementation keeps the coverage claim"
    (before.rows == after.rows)
  no "a refusal becoming an implementation raises the depth claim"
    (after.impl > before.impl)
  no "a refusal becoming an implementation lowers the refusal count -- which \
is why it is not an item" (after.refuse < before.refuse)
  -- A deliberate divergence stays in documented-command coverage. It is
  -- counted apart for audit, but changing the verdict cannot shrink `rows`.
  let decided := readIndex "zz" "body refuse:W0389 \\zzone\nbody divergence:W0389 \\zztwo\n"
  no s!"a divergence remains in rows: 2 expected, got {decided.rows}" (decided.rows == 2)
  no s!"a divergence is counted apart: 1 expected, got {decided.decided}"
    (decided.decided == 1)
  no "a divergence is neither implemented nor refused"
    (decided.impl == 0 && decided.refuse == 1)
  let asTsv (p : Pkg) : Tsv :=
    { provenance := #[], retired := #[], lowered := #[], encoding := some (.pairs "impl" "rows"),
      rows := #[{ item := "zz.impl", value := p.impl }, { item := "zz.rows", value := p.rows }] }
  no "a gap turned into a divergence keeps the documented denominator"
    ((ratchet (asTsv before)
      (asTsv (readIndex "zz" "body divergence:W0301 \\zzone\n"))).changes.isEmpty)

def main (args : List String) : IO UInt32 :=
  tierMain "compat" (.pairs "impl" "rows") measureTier selftest args
