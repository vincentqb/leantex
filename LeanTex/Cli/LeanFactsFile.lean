module

public import LeanTex.Cli.World
public import LeanTex.Core.LeanFacts
public import LeanTex.Core.Diag

/-! A Lean file's facts, as its project's exporter wrote them: read from the file a document
declares or from the one beneath the project's `.lake/build/leantex`, never asked of Lean. -/

namespace LeanTex.Cli.LeanFactsFile

open LeanTex.Core LeanTex.Cli.World

/-- The directories from a path's own up to the root, nearest first. -/
private def ancestors (path : String) : List String :=
  let parts := (path.splitOn "/").filter (!·.isEmpty)
  let dir := parts.dropLast
  (List.range (dir.length + 1)).reverse.map fun k => "/" ++ "/".intercalate (dir.take k)

/-- The first directory among `dirs` that holds a regular file named one of `names`. -/
private def findUp (names : List String) : List String → Prog (Option String)
  | [] => .pure none
  | d :: rest => do
    for n in names do
      if ToolPath.isFile (← ask (.stat (ToolPath.join d n))) then return some d
    findUp names rest

/-- A file's place under its project's root, `.lean` dropped. -/
private def stemOf (root abs : String) : String :=
  let rel := if abs.startsWith (root ++ "/") then (abs.drop (root.length + 1)).toString else abs
  if rel.endsWith ".lean" then (rel.dropEnd 5).toString else rel

/-- A module's name from its file's place under the project root. -/
public def moduleOf (root abs : String) : String := ".".intercalate ((stemOf root abs).splitOn "/")

/-- Where the exporter writes a file's facts: its place under the project, beneath
`.lake/build/leantex`, `.lean` made `.facts`. -/
public def standardPath (root abs : String) : String :=
  ToolPath.join root s!".lake/build/leantex/{stemOf root abs}.facts"

/-- The note a page owes when no facts file stands for its file. -/
public def missing (file path cmd lost : String) : Diag :=
  Diag.of .N0032 s!"no facts for '{file}' stand at '{path}'; {lost}" (some ⟨file, {}⟩)
    (help := s!"run `{cmd}` in its project, or declare `facts = <path>`")
    (subject := some s!"lean:{file}")

/-- The warning a page owes when its file's facts no longer line up with the file. -/
public def stale (file path cmd why lost : String) : Diag :=
  Diag.of .W0433 s!"the facts for '{file}' at '{path}' {why}; {lost}" (some ⟨file, {}⟩)
    (help := s!"run `{cmd}` in its project again") (subject := some s!"lean:{file}")

/-- A Lean file's facts, from the file `declared` names, placed by its declaring document, or the
exporter's standard one, with the note a missing file owes and the warning a stale one owes. -/
public def factsFor (file text : String) (declared : Option String)
    (lost : String := "its code is set without statements") :
    Prog (Option LeanFacts.Facts × Array Diag) := do
  let cwd := (← ask .cwd).toOption
  let placed (p : String) : String :=
    if p.startsWith "/" then p else (cwd.map (ToolPath.join · p)).getD p
  let joined := placed file
  let abs := match ← ask (.stat joined) with
    | .ok st => st.real
    | .error _ => joined
  let dirs := ancestors abs
  let root := (← findUp ["lakefile.lean", "lakefile.toml"] dirs).getD (dirs.headD "/")
  let path := match declared with
    | some p => placed p
    | none => standardPath root abs
  let cmd := s!"lake exe leantex-export {moduleOf root abs}"
  match ← ask (.readFile path) with
  | .error _ => return (none, #[missing file path cmd lost])
  | .ok bytes =>
    match (String.fromUTF8? bytes).map LeanFacts.decode with
    | some (.ok facts) =>
      if LeanFacts.alignedWith facts text then return (some facts, #[])
      else return (none, #[stale file path cmd "no longer line up with it" lost])
    | some (.error why) => return (none, #[stale file path cmd s!"do not read: {why}" lost])
    | none => return (none, #[stale file path cmd "are not UTF-8" lost])

end LeanTex.Cli.LeanFactsFile
