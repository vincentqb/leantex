module

public import LeanTex.Cli.World
public import LeanTex.Core.LeanFactsRead
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

/-- A file's place under its project's root. -/
private def placeOf (root abs : String) : String :=
  if abs.startsWith (root ++ "/") then (abs.drop (root.length + 1)).toString else abs

/-- Where the exporter writes a file's facts: its place under the project, beneath
`.lake/build/leantex`, `.lean` made `.facts`. -/
public def standardPath (root abs : String) : String :=
  let rel := placeOf root abs
  let stem := if rel.endsWith ".lean" then (rel.dropEnd 5).toString else rel
  ToolPath.join root s!".lake/build/leantex/{stem}.facts"

/-- What a page's notes tell its author to run: the exporter on the file, and where the document
declares its own path, a copy of what the exporter writes to it. -/
public def helpFor (cmd standard : String) (declared : Bool) : LeanFacts.Help :=
  let copy := if declared then s!", and copy '{standard}' to the declared path" else ""
  { absent := if declared then s!"run `{cmd}` in its project{copy}"
      else s!"run `{cmd}` in its project, or declare `facts = <path>`"
    again := s!"run `{cmd}` in its project again{copy}"
    update := s!"run `lake update leantex-export`, then `{cmd}`, in its project{copy}" }

/-- A Lean file's facts, from the file `declared` names, placed by its declaring document, or the
exporter's standard one, with the note or warning `LeanFacts.judge` owes and the path read. -/
public def factsFor (file text : String) (declared : Option String)
    (lost : String := "its code is set without statements") :
    Prog (Option LeanFacts.Facts × Array Diag × Option String) := do
  let cwd := (← ask .cwd).toOption
  let placed (p : String) : String :=
    if p.startsWith "/" then p else (cwd.map (ToolPath.join · p)).getD p
  let joined := placed file
  let abs := match ← ask (.stat joined) with
    | .ok st => st.real
    | .error _ => joined
  let dirs := ancestors abs
  let root := (← findUp ["lakefile.lean", "lakefile.toml"] dirs).getD (dirs.headD "/")
  let standard := standardPath root abs
  let path := (declared.map placed).getD standard
  let help := helpFor s!"lake exe leantex-export {placeOf root abs}" standard declared.isSome
  let read := (← ask (.readFile path)).toOption
  let (facts, ds) := LeanFacts.judge file path text lost help read
  return (facts, ds, read.map fun _ => path)

end LeanTex.Cli.LeanFactsFile
