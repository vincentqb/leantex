/-
What does this engine not yet guarantee? One command:

  lake env lean --run scripts/owed.lean

prints every obligation staged under Obligations (type-checked theorem
statements whose proofs are open holes) with the module that will own it
once proved, the advisory that asked for it, the blocker, and whether
discharging it moves goldens. `--check` is the quiet gate mode the
pre-commit hook runs; `--selftest` exercises the predicates.

Exit is non-zero only when the ratchet is violated. The ratchet: the number
of open holes may never grow without a matching record naming the new
obligation, and every recorded name must be registered in PLAN.md
(backticked), so new debt is deliberate and named. Decreasing is always
allowed. Mechanically also checked: no file outside the staging path may
name Obligations in an import line, so the gated library
(`lake build --wfail`, `lake test`) can never depend on an unproved
statement.

Blind spot, stated as precommit.lean states its own: the hole counter
strips `--` comments but has no block-comment state — keep the keyword out
of block comments in staged files.
-/

import scripts.Gate

/-- A line that leaves a proof open, comments and strings aside — the shared
`bannedWord`, so the hook's keyword gate and this hole counter can never
disagree about what counts. -/
def holeLine (l : String) : Bool := bannedWord kwSorry l

/-- A name is registered when PLAN.md spells it backticked. -/
def registered (plan name : String) : Bool :=
  containsSub plan ("`" ++ name ++ "`")

structure Ob where
  name : String
  owner : String
  source : String
  blocker : String
  goldens : String
  file : String
  line : Nat

/-- Parse one staged file: its owed records, its hole count, and any
malformed records. A record is five consecutive comment lines:
`-- owed: name`, then owner, source, blocker, goldens. -/
def parseFile (file content : String) : Array Ob × Nat × Array String := Id.run do
  let lines := (content.splitOn "\n").toArray
  let mut obs : Array Ob := #[]
  let mut errs : Array String := #[]
  let mut holes := 0
  for i in [0:lines.size] do
    let l := (lines[i]?).getD ""
    if holeLine l then holes := holes + 1
    if let some name := fieldOf l "owed" then
      match (lines[i+1]?).bind (fieldOf · "owner"),
            (lines[i+2]?).bind (fieldOf · "source"),
            (lines[i+3]?).bind (fieldOf · "blocker"),
            (lines[i+4]?).bind (fieldOf · "goldens") with
      | some o, some s, some bk, some g =>
        obs := obs.push { name := name
                          owner := o
                          source := s
                          blocker := bk
                          goldens := g
                          file := file
                          line := i + 1 }
      | _, _, _, _ =>
        errs := errs.push s!"{file}:{i + 1}: owed record '{name}' incomplete: \
          '-- owner:', '-- source:', '-- blocker:', '-- goldens:' must follow \
          on the next four lines"
  return (obs, holes, errs)

/-- The ratchet over everything parsed: one hole per record, no duplicate
names, every name registered in PLAN.md — and no stale premise: a blocker
naming the retired non-totality story describes a tree that no longer
exists (every function terminates by a proved measure), so those words
are banned from blocker text. A dead premise once hid the live blocker
(WF kernel-irreducibility) for a whole retry. Words composed so this
file passes the hook's own keyword gate. -/
def staleBlockerWords : List String := ["par" ++ "tial", "non-total"]

def ratchetErrors (obs : Array Ob) (holes : Nat) (plan : String) :
    Array String := Id.run do
  let mut errs : Array String := #[]
  if holes != obs.size then
    errs := errs.push s!"ratchet: {holes} open holes but {obs.size} owed \
      records -- every hole is one recorded obligation, one hole per record"
  let mut seen : Array String := #[]
  for ob in obs do
    if seen.contains ob.name then
      errs := errs.push s!"{ob.file}:{ob.line}: duplicate owed name '{ob.name}'"
    seen := seen.push ob.name
    if !registered plan ob.name then
      errs := errs.push s!"{ob.file}:{ob.line}: '{ob.name}' is not registered \
        in PLAN.md -- a new hole lands with a PLAN entry naming it: add \
        `{ob.name}` under 'Owed obligations'"
    for w in staleBlockerWords do
      if containsSub ob.blocker w then
        errs := errs.push s!"{ob.file}:{ob.line}: '{ob.name}' blocker says \
          '{w}' -- the tree has no partial functions; name the live blocker, \
          not the retired one"
  return errs

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let expect (name : String) (p : String → Bool) (cases : List (String × Bool)) :
      IO Unit := do
    for (line, want) in cases do
      if p line != want then
        fails.modify (s!"{name} {if want then "missed" else "fired on"}: {line}" :: ·)

  expect "holeLine" holeLine [
    ("  " ++ kwSorry, true),
    ("theorem t : True := by " ++ kwSorry, true),
    ("-- a comment naming " ++ kwSorry ++ " does not count", false),
    -- the shared stripper: a string naming the keyword is data here exactly
    -- as it is in the hook's banned-word gate
    ("  let s := \"a string naming " ++ kwSorry ++ "\"", false),
    ("  " ++ kwSorry ++ "ing is a different word", false)]

  expect "importsObligations" importsObligations [
    ("import Obligations", true),
    ("import Obligations.Extra", true),
    ("-- import Obligations", false),
    ("import LeanTex.Core.Ir", false)]

  expect "registered" (registered "text `a_b` text") [
    ("a_b", true), ("a", false), ("c_d", false)]

  expect "fieldOf owed" (fun l => (fieldOf l "owed").isSome) [
    ("-- owed: emission_conservation_paras", true),
    ("  -- owed: x", true),
    ("-- owner: LeanTex.Core.Layout", false),
    ("owed: x", false)]

  -- End to end: a well-formed record with its hole, an unrecorded hole,
  -- and an incomplete record.
  let good := "-- owed: t_one\n-- owner: M\n-- source: S\n-- blocker: B\n" ++
    "-- goldens: no\ntheorem t_one : True := by " ++ kwSorry ++ "\n"
  let (obs, holes, errs) := parseFile "F.lean" good
  if !(obs.size == 1 && holes == 1 && errs.isEmpty) then
    fails.modify ("parseFile: well-formed record misparsed" :: ·)
  if !(ratchetErrors obs holes "registry: `t_one`").isEmpty then
    fails.modify ("ratchet: fired on a recorded, registered hole" :: ·)
  if (ratchetErrors obs holes "registry without the name").isEmpty then
    fails.modify ("ratchet: missed an unregistered obligation" :: ·)
  let bare := "theorem t_two : True := by " ++ kwSorry ++ "\n"
  let (obs2, holes2, _) := parseFile "F.lean" bare
  if (ratchetErrors obs2 holes2 "").isEmpty then
    fails.modify ("ratchet: missed a hole with no owed record" :: ·)
  let incomplete := "-- owed: t_three\n-- owner: M\ntheorem t_three : True := by " ++
    kwSorry ++ "\n"
  let (_, _, errs3) := parseFile "F.lean" incomplete
  if errs3.isEmpty then
    fails.modify ("parseFile: missed an incomplete owed record" :: ·)

  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "owed selftest: all passed"
    return 0
  for f in failed do
    IO.eprintln s!"FAIL {f}"
  return 1

def readFileOr (p : String) : IO String := do
  if ← System.FilePath.pathExists p then IO.FS.readFile p else return ""

def obligationFiles : IO (Array (String × String)) := do
  let mut out : Array (String × String) := #[]
  if ← System.FilePath.pathExists "Obligations.lean" then
    out := out.push ("Obligations.lean", ← IO.FS.readFile "Obligations.lean")
  if ← System.FilePath.isDir "Obligations" then
    for p in ← System.FilePath.walkDir "Obligations" do
      if p.toString.endsWith ".lean" then
        out := out.push (p.toString, ← IO.FS.readFile p.toString)
  return out

/-- The gated modules that must never import the staging area. -/
def libFiles : IO (Array String) := do
  let mut out : Array String := #["Main.lean", "Tests.lean", "LeanTex.lean"]
  for p in ← System.FilePath.walkDir "LeanTex" do
    if p.toString.endsWith ".lean" then out := out.push p.toString
  return out

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then
    return (← selftest)
  let plan ← readFileOr "PLAN.md"
  let mut obs : Array Ob := #[]
  let mut holes := 0
  let mut errs : Array String := #[]
  for (f, content) in (← obligationFiles) do
    let (o, h, e) := parseFile f content
    obs := obs ++ o
    holes := holes + h
    errs := errs ++ e
  errs := errs ++ ratchetErrors obs holes plan
  for f in (← libFiles) do
    let content ← readFileOr f
    let ls := (content.splitOn "\n").toArray
    for i in [0:ls.size] do
      if importsObligations ((ls[i]?).getD "") then
        errs := errs.push s!"{f}:{i + 1}: imports Obligations -- the gated \
          library must never depend on a staged statement"
  if !args.contains "--check" then
    IO.println s!"owed: {obs.size} obligations, {holes} open holes"
    let mut k := 0
    for ob in obs do
      k := k + 1
      IO.println s!"{k}. {ob.name}  [{ob.file}:{ob.line}]"
      IO.println s!"   owner:   {ob.owner}"
      IO.println s!"   source:  {ob.source}"
      IO.println s!"   blocker: {ob.blocker}"
      IO.println s!"   goldens: {ob.goldens}"
  if errs.isEmpty then
    return 0
  for e in errs do
    IO.eprintln s!"owed: {e}"
  return 1
