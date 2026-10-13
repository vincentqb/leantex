/-
The compat tier: per package index, `<p>.rows` documented commands and `<p>.impl` implemented
ones (`impl` or `inert:`, as `coverage` counts them).
Usage: lake env lean --run scripts/compat.lean [--check | --selftest]
-/
import scripts.Board
import scripts.Rung

open Scoreboard

structure Pkg where
  name : String
  rows : Nat
  impl : Nat
  refuse : Nat
deriving Inhabited

/-- Count one index file's documented rows and those implemented. -/
def countRows (name : String) (rows : Array IndexRow) : Pkg :=
  { name, rows := rows.size, impl := (rows.filter (·.implemented)).size
    refuse := (rows.filter (·.refused)).size }

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
  for p in pkgs do
    rows := rows.push { item := s!"{p.name}.rows", value := Int.ofNat p.rows }
    rows := rows.push { item := s!"{p.name}.impl", value := Int.ofNat p.impl }
    totalRows := totalRows + p.rows
    totalImpl := totalImpl + p.impl
    totalRefuse := totalRefuse + p.refuse
  return (#[s!"# packages: {pkgs.size}; rows: {totalRows}; impl: {totalImpl} \
(verdict impl or inert:, the one definition the coverage tier shares); \
refuse: {totalRefuse}; other verdicts: {totalRows - totalImpl - totalRefuse} \
(all remain in rows)"], rows)

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
    "testdata/compat-index-does-not-exist")).toBaseIO
  no "a missing compat-index input fails closed"
    (match missing with | .error _ => true | .ok _ => false)
  let empty ← (readCompatIndexAt (System.FilePath.mk "LeanTex/Cli")).toBaseIO
  no "a compat-index input with no index files fails closed"
    (match empty with | .error _ => true | .ok _ => false)
  -- One definition of implemented, shared with the coverage tier.
  let isImpl (v : String) : Bool := (IndexRow.mk "body" v "\\zz").implemented
  no "definition: impl counts" (isImpl "impl")
  no "definition: inert: counts -- a recognised command that moves no ink"
    (isImpl "inert:binds")
  no "definition: a refusal does not count" (!isImpl "refuse:W0301")
  no "definition: an unknown verdict does not count" (!isImpl "zz")
  no "definition: a divergence verdict is not accepted"
    ((IndexRow.mk "body" "divergence:W0301" "\\zz").refusalCode?.isNone)
  no "the index's inert row is inside the impl count"
    ((readIndex "zz" "body inert:binds \\zzone\n").impl == 1)
  no "an empty refusal code is malformed"
    (!(IndexRow.mk "body" "refuse:" "\\zz").refused)
  no "a refusal rejects an extra diagnostic-code suffix"
    (!(IndexRow.mk "body" "refuse:W0301:extra" "\\zz").refused)
  -- A refusal becoming an implementation must not read as a loss.
  let before := readIndex "zz" "body refuse:W0301 \\zzone\n"
  let after := readIndex "zz" "body impl \\zzone\n"
  no "a refusal remains in the documented denominator" (before.rows == 1)
  no "a refusal becoming an implementation keeps the coverage claim"
    (before.rows == after.rows)
  no "a refusal becoming an implementation raises the depth claim"
    (after.impl > before.impl)
  no "a refusal becoming an implementation lowers the refusal count -- which \
is why it is not an item" (after.refuse < before.refuse)

def main (args : List String) : IO UInt32 :=
  tierMain "compat" (.pairs "impl" "rows") measureTier selftest args
