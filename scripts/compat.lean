/-
Documented-command coverage, per package. Run from the repository root:

  lake env lean --run scripts/compat.lean              regenerate the baseline
  lake env lean --run scripts/compat.lean --check      gate against the committed one
  lake env lean --run scripts/compat.lean --selftest   the row reader

`tests/compat-index/<pkg>.txt` carries one row per documented command of a
package, each with the verdict the engine owes it. `lake test` probes every
row; this tier commits the shape of the index, so a row cannot quietly
leave it.

Two items per package: `<p>.rows`, the commands covered at all, and
`<p>.impl`, those the engine implements. A decided divergence
(`divergence:<code>`, `IndexRow.decided`) is not a gap the engine owes, so
it is counted apart rather than in `rows`.

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

/-- Count one index file's rows. A `#` line is the header prose; every
other non-blank line is `<where> <verdict> <body…>` (`IndexRow`), counted
by the one definition of implemented the `coverage` tier shares
(`IndexRow.implemented`). A decided divergence is no gap: it leaves `rows`
and is counted apart (`IndexRow.decided`). -/
def countRows (name : String) (rows : Array IndexRow) : Pkg :=
  let scored := rows.filter (·.scored)
  { name, rows := scored.size, impl := (scored.filter (·.implemented)).size
    refuse := (scored.filter (·.refused)).size, decided := rows.size - scored.size }

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
refuse: {totalRefuse}; other verdicts: {totalRows - totalImpl - totalRefuse}; \
decided divergences, outside rows: {totalDecided}"], rows)

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
  -- A decided divergence stops scoring as a gap: it leaves `rows`, so a gap
  -- turned into one is a fall only a human `# lowered:` line admits.
  let decided := readIndex "zz" "body refuse:W0389 \\zzone\nbody divergence:W0389 \\zztwo\n"
  no s!"a divergence leaves rows: 1 expected, got {decided.rows}" (decided.rows == 1)
  no s!"a divergence is counted apart: 1 expected, got {decided.decided}"
    (decided.decided == 1)
  no "a divergence is neither implemented nor refused"
    (decided.impl == 0 && decided.refuse == 1)
  let asTsv (p : Pkg) : Tsv :=
    { provenance := #[], retired := #[], lowered := #[], encoding := some (.pairs "impl" "rows"),
      rows := #[{ item := "zz.impl", value := p.impl }, { item := "zz.rows", value := p.rows }] }
  no "a gap turned into a divergence is a fall the ratchet reports"
    ((ratchet (asTsv before) (asTsv (readIndex "zz" "body divergence:W0301 \\zzone\n"))).losses.any
      (·.item == "zz.rows"))

def main (args : List String) : IO UInt32 :=
  tierMain "compat" (.pairs "impl" "rows") measureTier selftest args
