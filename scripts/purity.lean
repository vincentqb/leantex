/-
Two counts that must stay at zero, as a tier rather than as a diff gate.
Run from the repository root:

  lake env lean --run scripts/purity.lean              regenerate the baseline
  lake env lean --run scripts/purity.lean --check      gate against the committed one
  lake env lean --run scripts/purity.lean --selftest   the counters

The pre-commit hook rejects a *newly staged* occurrence of either keyword;
that is a claim about a diff, and a diff gate is blind to what arrives by
rebase, by a merge resolution, or on a branch that never met the hook. This
tier reads the whole tree, so the number is the tree's, and it is committed.

Both items use the headroom encoding, so zero occurrences reads as the
ceiling. The keyword predicate is `bannedWord` from `scripts/Gate.lean` —
the same definition the hook uses, because two gates that must agree about
what counts as an occurrence read one definition (that module's own
implementation defines the shared lexical policy).
-/
import scripts.Board
import scripts.ProofSources

open Scoreboard

/-- Occurrences of the two banned keywords as code tokens, in one pass per
file. `containsSub` is the cheap pre-filter: a line with no such substring
cannot hold the word, and skipping the character-level strippers on it is
what makes a whole-tree scan affordable in an interpreted script. -/
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
  -- The counter counts code tokens, and agrees with the hook's predicate
  -- because it *is* the hook's predicate. One line each way.
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
