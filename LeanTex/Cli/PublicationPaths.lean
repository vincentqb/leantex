module

import Init.System.IO

/-! Publication destinations are checked before any artifact is written.
Resolve existing directory links before `..`; lexical normalization alone
would mistake two names of the same file for independent destinations.
This is a filesystem preflight, not a claim against concurrent filesystem
changes. Multiply-linked files and unresolved links cannot establish the
required independence with the portable metadata API, so they are refused. -/

namespace LeanTex.Cli.PublicationPaths

/-- Resolve an existing prefix and normalize the not-yet-created tail. -/
private def canonical (path : System.FilePath) : IO System.FilePath := do
  let absolute := (← IO.currentDir) / path
  let mut cursor : System.FilePath := "/"
  for part in absolute.components do
    if part.isEmpty || part == "." then continue
    if part == ".." then
      cursor := cursor.parent.getD cursor
    else
      let next := cursor / part
      try
        cursor ← IO.FS.realPath next
      catch err =>
        match err with
        | .noFileOrDirectory .. =>
          match ← next.symlinkMetadata.toBaseIO with
          | .error (.noFileOrDirectory ..) => cursor := next
          | .error err => throw err
          | .ok _ => throw <| IO.userError s!"cannot resolve output link '{next}'"
        | _ => throw err
  return cursor

/-- Nothing means every requested format has a distinct resolved path and
no destination has uninspectable hard-link aliases. Only multiple formats
owe this independence; one output cannot overwrite another in the run. -/
public def conflict (paths : Array (String × String)) : IO (Option String) := do
  if paths.size < 2 then return none
  try
    let mut seen : Array (String × System.FilePath) := #[]
    for (format, name) in paths do
      let path ← canonical name
      if let some (other, _) := seen.find? (·.2 == path) then
        return some s!"{other} and {format} both name '{path}'"
      match ← path.metadata.toBaseIO with
      | .ok metadata =>
        if metadata.type == .file && metadata.numLinks > 1 then
          return some s!"{format} destination '{path}' has multiple hard links"
      | .error (.noFileOrDirectory ..) => pure ()
      | .error err => throw err
      seen := seen.push (format, path)
    return none
  catch err =>
    return some s!"cannot establish output independence: {err}"

end LeanTex.Cli.PublicationPaths
