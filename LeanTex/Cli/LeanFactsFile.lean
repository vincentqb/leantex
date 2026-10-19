module

public import LeanTex.Cli.World
public import LeanTex.Core.LeanFactsRead
public import LeanTex.Core.Diag
import LeanTex.Cli.DriverDiag

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

/-- What a page's notes tell its author to run: the exporter on the file, from a project that
requires it, and where the document declares its own path, a copy of what it writes there. -/
public def helpFor (cmd standard : String) (declared : Bool) : LeanFacts.Help :=
  let copy := if declared then s!", and copy '{standard}' to the declared path" else ""
  let there := "in a project that requires leantex-export"
  { absent := if declared then s!"run `{cmd}` {there}{copy}"
      else s!"run `{cmd}` {there}, or declare `facts = <path>`"
    again := s!"run `{cmd}` again {there}{copy}"
    update := s!"run `lake update leantex-export`, then `{cmd}`, {there}{copy}"
    newer := "update leantex, or pin `leantex-export` in the project's lakefile to the revision \
of this leantex" }

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
  let help := helpFor s!"lake exe leantex-export {abs}" standard declared.isSome
  let read := (← ask (.readFile path)).toOption
  let (facts, ds) := LeanFacts.judge file path text lost help read
  return (facts, ds, read.map fun _ => path)

/-- A bibliography file a Lean file's documentation cites into: the name its document gives it, the
path it is read at, and its bytes, which its reader decodes as the document's reference list does. -/
public structure BibFile where
  name : String
  path : String
  bytes : ByteArray

/-- The bibliography a code file's documentation cites into: the files declared beside `base` (else
the file's folder), else `docs/references.bib` in its project, the nearest folder holding one of
`markers`, each named from `base` with its bytes, and W0503 at `span` for a declared one not there. -/
public def bibFor (file : String) (declared : List String) (span : Span)
    (base : Option String := none) (entry : Option String := none)
    (markers : List String := ["lakefile.lean", "lakefile.toml"]) :
    Prog (Array BibFile × Array Diag) := do
  let cwd := (← ask .cwd).toOption
  let placed (p : String) : String :=
    if p.startsWith "/" then p else (cwd.map (ToolPath.join · p)).getD p
  let joined := placed file
  -- Names are read from the document's folder, the file's as given, where it really stands, since a
  -- name climbing out of it climbs out of its real folder; the project is the real file's.
  let given := match base with
    | some b => placed b
    | none => (ancestors joined).headD "/"
  let here := match ← ask (.stat given) with
    | .ok st => st.real
    | .error _ => given
  let real := match ← ask (.stat joined) with
    | .ok st => st.real
    | .error _ => joined
  let wanted : List (String × String × Bool) ← if declared.isEmpty then do
      match ← findUp markers (ancestors real) with
      | some root =>
        let path := ToolPath.join root "docs/references.bib"
        pure [((ToolPath.relative here path).getD path, path, false)]
      | none => pure []
    else pure (declared.map fun p => (p, if p.startsWith "/" then p else ToolPath.join here p, true))
  let mut found : Array BibFile := #[]
  let mut diags : Array Diag := #[]
  for (name, path, isDeclared) in wanted do
    match ← ask (.readFile path) with
    | .ok bytes => found := found.push { name, path, bytes }
    | .error _ =>
      if isDeclared then diags := diags.push (DriverDiag.bibMissingLean name path span entry)
  return (found, diags)

end LeanTex.Cli.LeanFactsFile
