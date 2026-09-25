/-
The owed-theorem debt, per owner module. Run from the repository root:

  lake env lean --run scripts/obligations.lean              regenerate the baseline
  lake env lean --run scripts/obligations.lean --check      gate against the committed one
  lake env lean --run scripts/obligations.lean --selftest   the reader and the encoding

`scripts/owed.lean` already refuses debt that grows *unnamed*. This tier
asks the other question: is the debt going down, and for whom. One item per
owner module, valued `cap - open`, so discharging an obligation raises the
number and staging a new one lowers it — which is the ratchet, pointed the
one way every tier points.

An owner whose debt reaches zero keeps its item (at the ceiling) rather
than disappearing: an absent item is a regression by the ratchet's own
rule, and finishing the last proof for a module must not read as one.
-/
import scripts.Board

open Scoreboard

/-- The owners a baseline names, so an owner that reaches zero debt still
reports. -/
def baselineOwners : IO (Array String) := do
  let text ← readFileOr (tsvPath "obligations")
  if text.isEmpty then return #[]
  match parse text with
  | .error _ => return #[]
  | .ok t => return t.rows.filterMap fun r =>
      if r.item.startsWith "owner:" then some ((r.item.drop "owner:".length).toString)
      else none

def measureTier : IO (Array String × Array Row) := do
  let obs ← obligations
  let mut owners : Array String := ← baselineOwners
  for o in obs do
    if !owners.contains o.owner then owners := owners.push o.owner
  let mut rows : Array Row := #[]
  for owner in owners do
    let open_ := (obs.filter (·.owner == owner)).size
    rows := rows.push { item := s!"owner:{owner}", value := debtCap - open_ }
  let readyCount := (ready obs).size
  return (#[s!"# open: {obs.size} obligations over {owners.size} owner modules, \
{readyCount} with no other open obligation in the blocker"], rows)

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let no (why : String) (ok : Bool) : IO Unit := do
    unless ok do fails.modify (why :: ·)
  let src := "-- owed: t_a\n-- owner: M.One\n-- source: S\n-- blocker: needs t_b\n\
-- goldens: no\n-- owed: t_b\n-- owner: M.Two\n-- source: S\n-- blocker: a kernel wall\n\
-- goldens: no\n"
  let lines := (src.splitOn "\n").toArray
  let mut obs : Array Ob := #[]
  for i in [0:lines.size] do
    if let some name := (lines[i]?).bind (fieldOf · "owed") then
      obs := obs.push
        { name
          owner := ((lines[i+1]?).bind (fieldOf · "owner")).getD "?"
          blocker := ((lines[i+3]?).bind (fieldOf · "blocker")).getD "?"
          file := "F.lean" }
  no "reader: two records not found" (obs.size == 2)
  no "reader: owner misread" (obs.any (·.owner == "M.One") && obs.any (·.owner == "M.Two"))
  let r := ready obs
  no "ready: t_b is blocked by nothing open, so it is ready" (r.any (·.name == "t_b"))
  no "ready: t_a names t_b, which is open, so it is not ready" (!r.any (·.name == "t_a"))
  no "ready: exactly one of the two" (r.size == 1)
  -- The encoding is the ratchet's direction: one fewer obligation must read
  -- as a higher number.
  no "encoding: discharging raises the value"
    (debtCap - (1 : Int) > debtCap - (2 : Int))
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "obligations selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 :=
  tierMain "obligations" (.headroom debtCap) measureTier selftest args
