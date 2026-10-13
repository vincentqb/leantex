/-
The purity tier: occurrences of the banned keywords across maintained sources, as headroom.
Usage: lake env lean --run scripts/purity.lean [--check | --selftest]
-/
import scripts.Board
import scripts.ProofSources

open Scoreboard

/-- Occurrences of the two banned keywords as code tokens, with the files holding them. -/
def countWords (files : Array String) :
    IO (Nat × Array String × Nat × Array String) := do
  let mut np := 0
  let mut hp : Array String := #[]
  let mut nh := 0
  let mut hh : Array String := #[]
  for f in files do
    let mut kp := 0
    let mut kh := 0
    for l in (← IO.FS.readFile f).splitOn "\n" do
      if containsSub l kwPartial && bannedWord kwPartial l then kp := kp + 1
      if containsSub l kwSorry && bannedWord kwSorry l then kh := kh + 1
    if kp > 0 then
      np := np + kp
      hp := hp.push s!"{f}:{kp}"
    if kh > 0 then
      nh := nh + kh
      hh := hh.push s!"{f}:{kh}"
  return (np, hp, nh, hh)

def measureTier : IO (Array String × Array Row) := do
  let files := (← ProofSources.sources ".").map (·.toString)
  let (partials, pWhere, holes, hWhere) ← countWords files
  let mut extra : Array String := #[
    s!"# scanned: {files.size} maintained .lean sources using ProofSources.sources"]
  if !pWhere.isEmpty then
    extra := extra.push s!"# {kwPartial}: {String.intercalate " " pWhere.toList}"
  if !hWhere.isEmpty then
    extra := extra.push s!"# unfinished proofs: {String.intercalate " " hWhere.toList}"
  return (extra, #[
    { item := "non-total-definitions-absent", value := debtCap - partials },
    { item := "open-holes-absent", value := debtCap - holes }])

def selftest : IO UInt32 := tierSelftest "purity" fun no => do
  no "counter: a definition is an occurrence" (bannedWord kwPartial (kwPartial ++ " def f := 0"))
  no "counter: a comment is not" (!bannedWord kwPartial ("-- a note on " ++ kwPartial))
  no "counter: a string is not" (!bannedWord kwPartial ("  let s := \"" ++ kwPartial ++ "\""))
  no "counter: a longer word is not" (!bannedWord kwPartial (kwPartial ++ "Sums := 3"))
  no "proof: an unfinished body is an occurrence"
    (bannedWord kwSorry ("theorem unfinished : True := by " ++ kwSorry))
  no "proof: a comment is not code" (!bannedWord kwSorry ("-- " ++ kwSorry))
  no "proof: a string is not code" (!bannedWord kwSorry ("def text := \"" ++ kwSorry ++ "\""))
  no "encoding: one occurrence is below the ceiling" (debtCap - (1 : Int) < debtCap)

def main (args : List String) : IO UInt32 :=
  tierMain "purity" (.headroom debtCap) measureTier selftest args
