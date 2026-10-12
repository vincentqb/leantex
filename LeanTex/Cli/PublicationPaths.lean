module

import Init.System.IO

/-! Publication destinations are checked before any artifact is written.
Resolve existing directory links before `..`; lexical normalization alone
would mistake two names of the same file for independent destinations.
This is a filesystem preflight, not a claim against concurrent filesystem
changes. Multiply-linked files and unresolved links cannot establish the
required independence with the portable metadata API, so they are refused. -/

namespace LeanTex.Cli.PublicationPaths

/-- Resolve an existing prefix and normalize the not-yet-created tail, or
name the first component that is a link resolving to nothing. -/
private def resolve (path : System.FilePath) : IO (Except System.FilePath System.FilePath) := do
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
          | .ok _ => return .error next
        | _ => throw err
  return .ok cursor

/-- `resolve`, where a link resolving to nothing is an error. -/
private def canonical (path : System.FilePath) : IO System.FilePath := do
  match ← resolve path with
  | .ok resolved => return resolved
  | .error link => throw <| IO.userError s!"cannot resolve output link '{link}'"

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

/-- Why a destination cannot be written: it is a file the build reads. -/
public inductive Overwrite where
  /-- The destination resolves to the path the input resolves to. -/
  | same (format destination input : String)
  /-- The destination stands with several hard links and agrees with the
  input on every fact the portable metadata gives of a file (`mayAlias`). -/
  | linked (format destination input : String)
  /-- A file the build read cannot be resolved again, so no destination can
  be shown to be none of the inputs. -/
  | unresolved (why : String)
  deriving Repr, BEq

/-- Could two standing files be one under two names? Two names of one file
share its kind, link count, size and modification time, and its link count
is at least two. With no inode number to compare, this reading misses no
alias, and it takes an unrelated file for one only where all four agree. -/
private def mayAlias (a b : IO.FS.Metadata) : Bool :=
  a.type == .file && b.type == .file && a.numLinks > 1 && a.numLinks == b.numLinks &&
    a.byteSize == b.byteSize && a.modified == b.modified

/-- Nothing means no destination names a file the build reads (`inputs`):
none resolves to an input's own path, and none could be another name of an
input's file (`mayAlias`). An input no longer standing holds nothing a write
could destroy. A destination that does not resolve — a link to nothing, a
component that is no directory or that this user cannot search — names no
standing file a write could open either, so its write is the one that
fails, under its own path. One output owes this as much as several:
writing it would replace the document or a file it reads. -/
public def overwrite (destinations : Array (String × String)) (inputs : Array String) :
    IO (Option Overwrite) := do
  let read ← try
      let mut read : Array (String × System.FilePath × IO.FS.Metadata) := #[]
      for input in inputs do
        if read.any (·.1 == input) then continue
        match ← (System.FilePath.mk input).metadata.toBaseIO with
        | .error (.noFileOrDirectory ..) => pure ()
        | .error err => throw err
        | .ok metadata => read := read.push (input, ← IO.FS.realPath input, metadata)
      pure (Except.ok read)
    catch err => pure (.error (toString err))
  match read with
  | .error why => return some (.unresolved why)
  | .ok read =>
    for (format, name) in destinations do
      let .ok (.ok path) ← (resolve name).toBaseIO | continue
      if let some (input, _, _) := read.find? (·.2.1 == path) then
        return some (.same format name input)
      if let .ok metadata ← path.metadata.toBaseIO then
        if let some (input, _, _) := read.find? (mayAlias metadata ·.2.2) then
          return some (.linked format name input)
    return none

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
