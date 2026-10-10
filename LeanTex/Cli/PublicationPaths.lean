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

/-- One path segment as a URL reads it back: each character a relative
URL's path would read as something else (`%`, `#`, `?`, `\`, `:`, white
space and the controls) percent-encoded as its UTF-8 bytes, and every other
one kept, non-ASCII included, which a URL parser encodes itself. -/
private def segmentHref (s : String) : String :=
  let hex (n : UInt8) : Char := Char.ofNat (if n < 10 then 48 + n.toNat else 55 + n.toNat)
  let byte (o : String) (b : UInt8) : String := ((o.push '%').push (hex (b >>> 4))).push (hex (b &&& 15))
  s.foldl (fun out c =>
    if c.isAlphanum || "-._~!$&'()*+,;=@".contains c || 0xA0 ≤ c.toNat then out.push c
    else (String.singleton c).toUTF8.foldl byte out) ""

/-- A path's segments read lexically, as a browser resolves a link: empty
and `.` segments dropped, and each `..` taking back the segment before it,
or kept where nothing stands before it in a relative path (the root's
parent is the root). -/
private def lexical (path : String) : List String :=
  let rooted := path.startsWith "/"
  (path.splitOn "/").foldl (fun acc s =>
    if s.isEmpty || s == "." then acc
    else if s == ".." then
      if acc.isEmpty || acc.getLast? == some ".." then (if rooted then acc else acc ++ [".."])
      else acc.dropLast
    else acc ++ [s]) []

/-- The link a page gives to a file named `name` from the page's own
directory: its segments read lexically, each percent-encoded where a URL
would read it as something else. None for an absolute name, which names
no place relative to the page, and for a name with no final file name
(empty, or ending in `.`, `..` or a separator). -/
public def nameHref (name : String) : Option String :=
  if name.startsWith "/" || (System.FilePath.mk name).fileName.isNone then none
  else some ("/".intercalate ((lexical name).map segmentHref))

/-- Where a file named `name` from directory `dir` lands: read lexically
when the page can link it (`nameHref`), so a link a `..` walks back through
is not followed and the file is where the link points; otherwise, an
absolute name or one with no final file name, `dir / name` as written. -/
public def placed (dir name : String) : String :=
  if (nameHref name).isNone then (System.FilePath.mk dir / name).toString
  else
    let joined := dir ++ "/" ++ name
    let segs := lexical joined
    if joined.startsWith "/" then "/" ++ "/".intercalate segs
    else if segs.isEmpty then "." else "/".intercalate segs

end LeanTex.Cli.PublicationPaths
