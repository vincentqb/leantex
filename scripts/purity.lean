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
docstring records the defect that taught it).
-/
import scripts.Board

open Scoreboard

/-- The keyword, composed so this file's own staged diff does not trip the
hook's gate on it — the trick `scripts/precommit.lean` uses for the same
reason, and a third copy of it. Routed: `kwPartial` belongs in
`scripts/Gate.lean` beside `kwSorry`, which is where the repository already
keeps a spelling two gates must agree on. -/
def kwPartial : String := "par" ++ "tial"

/-- Every `.lean` file in the tree. `.git` and `.lake` are not entered at
all: a walk that descends into them spends most of its time there and finds
nothing, which is where most of this tier's first runtime went. -/
def leanFiles : IO (Array String) := do
  let mut out : Array String := #[]
  let enter := fun (p : System.FilePath) => do
    let b := p.fileName.getD ""
    return b != ".git" && b != ".lake"
  for p in ← System.FilePath.walkDir "." enter do
    let s := p.toString
    let s := if s.startsWith "./" then (s.drop 2).toString else s
    if s.endsWith ".lean" then out := out.push s
  return out.qsort (· < ·)

/-- Occurrences of the two banned keywords as code tokens, in one pass per
file. `containsSub` is the cheap pre-filter: a line with no such substring
cannot hold the word, and skipping the character-level strippers on it is
what makes a whole-tree scan affordable in an interpreted script. -/
def countWords (files : Array String) (staged : String → Bool) :
    IO (Nat × Array String × Nat × Array String) := do
  let mut np := 0
  let mut hp : Array String := #[]
  let mut nh := 0
  let mut hh : Array String := #[]
  for f in files do
    let isStaged := staged f
    let mut kp := 0
    let mut kh := 0
    for l in (← IO.FS.readFile f).splitOn "\n" do
      if containsSub l kwPartial && bannedWord kwPartial l then kp := kp + 1
      if !isStaged && containsSub l kwSorry && bannedWord kwSorry l then kh := kh + 1
    if kp > 0 then
      np := np + kp
      hp := hp.push s!"{f}:{kp}"
    if kh > 0 then
      nh := nh + kh
      hh := hh.push s!"{f}:{kh}"
  return (np, hp, nh, hh)

/-- The staging area, where one open hole per owed record is the rule the
owed ratchet enforces. Counted separately so the tier's `holes` item is
about the *gated* tree only. -/
def staged (f : String) : Bool :=
  f == "Obligations.lean" || f.startsWith "Obligations/"

def measureTier : IO (Array String × Array Row) := do
  let files ← leanFiles
  let (partials, pWhere, holes, hWhere) ← countWords files staged
  let mut extra : Array String := #[
    s!"# scanned: {files.size} .lean files, .git and .lake not entered"]
  if !pWhere.isEmpty then
    extra := extra.push s!"# {kwPartial}: {String.intercalate " " pWhere.toList}"
  if !hWhere.isEmpty then
    extra := extra.push s!"# holes outside the staging area: {String.intercalate " " hWhere.toList}"
  return (extra, #[
    { item := "non-total-definitions-absent", value := debtCap - partials },
    { item := "open-holes-outside-staging-absent", value := debtCap - holes }])

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let no (why : String) (ok : Bool) : IO Unit := do
    unless ok do fails.modify (why :: ·)
  -- The counter counts code tokens, and agrees with the hook's predicate
  -- because it *is* the hook's predicate. One line each way.
  no "counter: a definition is an occurrence" (bannedWord kwPartial (kwPartial ++ " def f := 0"))
  no "counter: a comment is not" (!bannedWord kwPartial ("-- a note on " ++ kwPartial))
  no "counter: a string is not" (!bannedWord kwPartial ("  let s := \"" ++ kwPartial ++ "\""))
  no "counter: a longer word is not" (!bannedWord kwPartial (kwPartial ++ "Sums := 3"))
  no "staging: Obligations.lean is staged" (staged "Obligations.lean")
  no "staging: a nested obligation is staged" (staged "Obligations/Layout.lean")
  no "staging: a library module is not" (!staged "LeanTex/Core/Ir.lean")
  no "encoding: one occurrence is below the ceiling" (debtCap - (1 : Int) < debtCap)
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "purity selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 :=
  tierMain "purity" (.headroom debtCap) measureTier selftest args
