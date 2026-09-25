/-
Documented-command coverage, per package. Run from the repository root:

  lake env lean --run scripts/compat.lean              regenerate the baseline
  lake env lean --run scripts/compat.lean --check      gate against the committed one
  lake env lean --run scripts/compat.lean --selftest   the row reader

`tests/compat-index/<pkg>.txt` carries one row per documented command of a
package, each with the verdict the engine owes it. `lake test` probes every
row; this tier commits the shape of the index, so a row cannot quietly
leave it.

Two items per package: `<pkg>.rows`, the commands covered at all, and
`<pkg>.impl`, those the engine implements. Correction to the brief that
asked for `impl` and `refuse` counts: a refusal count cannot be ratcheted
upward, because the way a refusal improves is by becoming an implementation
— which lowers it. `rows` is the coverage claim and `impl` the depth claim,
both monotone the right way, and `refuse` stays a provenance line: data,
never gated.
-/
import scripts.Board

open Scoreboard

structure Pkg where
  name : String
  rows : Nat
  impl : Nat
  refuse : Nat
deriving Inhabited

/-- Read one index file. A `#` line is the header prose; every other
non-blank line is `<where> <verdict> <body…>`. -/
def readIndex (name text : String) : Pkg := Id.run do
  let mut rows := 0
  let mut impl := 0
  let mut refuse := 0
  for raw in text.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    rows := rows + 1
    let toks := (l.splitOn " ").filter (!·.isEmpty)
    let verdict := (toks[1]?).getD ""
    if verdict == "impl" then impl := impl + 1
    else if verdict.startsWith "refuse:" then refuse := refuse + 1
  return { name, rows, impl, refuse }

def packages : IO (Array Pkg) := do
  let dir : System.FilePath := "tests/compat-index"
  let mut out : Array Pkg := #[]
  if ← dir.isDir then
    for e in ← dir.readDir do
      let f := e.fileName
      if f.endsWith ".txt" then
        let name := (f.dropEnd ".txt".length).toString
        out := out.push (readIndex name (← IO.FS.readFile (dir / f)))
  return out.qsort (fun a b => a.name < b.name)

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
  return (#[s!"# packages: {pkgs.size}; rows: {totalRows}; impl: {totalImpl}; \
refuse: {totalRefuse}; other verdicts: {totalRows - totalImpl - totalRefuse}"], rows)

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let no (why : String) (ok : Bool) : IO Unit := do
    unless ok do fails.modify (why :: ·)
  let text := "# source: an invented manual §1\n\
body impl \\zzone{x}\n\
body refuse:W0301 \\zztwo\n\
preamble impl \\zzthree\n\
body inert:binds \\zzfour\n\
\n"
  let p := readIndex "zz" text
  no s!"rows: 4 expected, got {p.rows}" (p.rows == 4)
  no s!"impl: 2 expected, got {p.impl}" (p.impl == 2)
  no s!"refuse: 1 expected, got {p.refuse}" (p.refuse == 1)
  no "header prose is not a row" ((readIndex "zz" "# only prose\n").rows == 0)
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
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "compat selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 :=
  tierMain "compat" (.pairs "impl" "rows") measureTier selftest args
