module

import Init.System.IO
public import LeanTex.Cli.World
import Std.Data.HashSet

/-! Publication destinations, checked before any artifact is written: apart from each
other (`conflict`) and from the files the build read (`overwrite`), a preflight rather
than a claim against concurrent changes. -/

namespace LeanTex.Cli.PublicationPaths

/-- Resolve an existing prefix and normalize the not-yet-created tail, or name the first
component that is a link resolving to nothing. -/
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

/-- Nothing when every requested format has a distinct resolved path and no destination
has uninspectable hard-link aliases. -/
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
  /-- The destination and the input resolve apart, and their metadata agrees on every fact
  two hard links of one file share, a link count of at least two among them. -/
  | linked (format destination input : String)
  deriving Repr, BEq

/-- A destination that stands, as the preflight read it. -/
private structure Standing where
  format : String
  name : String
  metadata : World.Metadata
  real : String

/-- Whether two files could be one by their metadata, as two hard links of one file
are. -/
private def sameShape (a b : World.Metadata) : Bool :=
  a.kind == b.kind && a.size == b.size && a.mtimeSec == b.mtimeSec &&
    a.mtimeNsec == b.mtimeNsec && a.links == b.links

/-- The destinations that stand, each read by its metadata and real path, links followed;
one that does not stand or cannot be reached is left out. -/
private def standingGo : List (String × String) → Array Standing → World.Prog (Array Standing)
  | [], acc => .pure acc
  | (format, name) :: rest, acc =>
    .ask (.metadata name) fun
      | .error _ => standingGo rest acc
      | .ok metadata => .ask (.stat name) fun
        | .error _ => standingGo rest acc
        | .ok st => standingGo rest (acc.push { format, name, metadata, real := st.real })

/-- The first input that is a standing destination's file: one with the destination's real
path, or a multiply-linked regular file whose metadata agrees with it. -/
private def clashGo (standing : Array Standing) :
    List String → Std.HashSet String → World.Prog (Option Overwrite)
  | [], _ => .pure none
  | input :: rest, asked =>
    if asked.contains input then clashGo standing rest asked else
    .ask (.metadata input) fun
      | .error _ => clashGo standing rest (asked.insert input)
      | .ok metadata =>
        let near := standing.filter (sameShape ·.metadata metadata)
        if near.isEmpty then clashGo standing rest (asked.insert input) else
        .ask (.stat input) fun
          | .error _ => clashGo standing rest (asked.insert input)
          | .ok st =>
            match near.find? (·.real == st.real) with
            | some d => .pure (some (.same d.format d.name input))
            | none =>
              if metadata.kind == .file && metadata.links > 1 then
                .pure (near[0]?.map fun d => .linked d.format d.name input)
              else clashGo standing rest (asked.insert input)

/-- Nothing when no destination names a file the build reads (`inputs`): none resolves to
an input's path, and none shares an input's hard-link metadata (kind, size, modification
time, a link count of at least two). -/
public def overwrite (destinations : Array (String × String)) (inputs : Array String) :
    World.Prog (Option Overwrite) := do
  let standing ← standingGo destinations.toList #[]
  if standing.isEmpty then return none
  clashGo standing inputs.toList {}

/-- A question that only looks: a path's metadata or its real path. -/
@[expose] public def Inspects : World.Ask → Prop
  | .metadata _ => True
  | .stat _ => True
  | _ => False

private theorem standingGo_only (destinations : List (String × String)) (acc : Array Standing) :
    (standingGo destinations acc).Only Inspects := by
  induction destinations generalizing acc with
  | nil => exact .pure acc
  | cons d rest ih =>
    obtain ⟨format, name⟩ := d
    refine .ask (.metadata name) _ trivial fun r => ?_
    cases r with
    | error _ => exact ih acc
    | ok metadata =>
      refine .ask (.stat name) _ trivial fun r => ?_
      cases r with
      | error _ => exact ih acc
      | ok st => exact ih _

private theorem clashGo_only (standing : Array Standing) (inputs : List String)
    (asked : Std.HashSet String) : (clashGo standing inputs asked).Only Inspects := by
  induction inputs generalizing asked with
  | nil => exact .pure none
  | cons input rest ih =>
    unfold clashGo
    split
    · exact ih asked
    · refine .ask (.metadata input) _ trivial fun r => ?_
      cases r with
      | error _ => exact ih _
      | ok metadata =>
        dsimp only
        split
        · exact ih _
        · refine .ask (.stat input) _ trivial fun r => ?_
          cases r with
          | error _ => exact ih _
          | ok st =>
            dsimp only
            split
            · exact .pure _
            · split
              · exact .pure _
              · exact ih _

public theorem overwrite_only (destinations : Array (String × String)) (inputs : Array String) :
    (overwrite destinations inputs).Only Inspects := by
  unfold overwrite
  refine (standingGo_only _ _).bind fun standing => ?_
  split
  · exact .pure none
  · exact clashGo_only _ _ _

/-- One path segment as a URL reads it back: `%`, `#`, `?`, `\`, `:`, white space and the
controls percent-encoded as UTF-8 bytes, every other character kept. -/
private def segmentHref (s : String) : String :=
  let hex (n : UInt8) : Char := Char.ofNat (if n < 10 then 48 + n.toNat else 55 + n.toNat)
  let byte (o : String) (b : UInt8) : String := ((o.push '%').push (hex (b >>> 4))).push (hex (b &&& 15))
  s.foldl (fun out c =>
    if c.isAlphanum || "-._~!$&'()*+,;=@".contains c || 0xA0 ≤ c.toNat then out.push c
    else (String.singleton c).toUTF8.foldl byte out) ""

/-- A path's segments read lexically, as a browser resolves a link: empty and `.` segments
dropped, each `..` taking back the segment before it, or kept where none stands before it
in a relative path. -/
private def lexical (path : String) : List String :=
  let rooted := path.startsWith "/"
  (path.splitOn "/").foldl (fun acc s =>
    if s.isEmpty || s == "." then acc
    else if s == ".." then
      if acc.isEmpty || acc.getLast? == some ".." then (if rooted then acc else acc ++ [".."])
      else acc.dropLast
    else acc ++ [s]) []

/-- The link a page gives to a file `name` from its own directory, segments read lexically
and percent-encoded; none for an absolute name or one with no final file name. -/
public def nameHref (name : String) : Option String :=
  if name.startsWith "/" || (System.FilePath.mk name).fileName.isNone then none
  else some ("/".intercalate ((lexical name).map segmentHref))

/-- Where a file `name` from `dir` lands: where its link points when the page can link it
(`nameHref`), else `dir / name` as written. -/
public def placed (dir name : String) : String :=
  if (nameHref name).isNone then (System.FilePath.mk dir / name).toString
  else
    let joined := dir ++ "/" ++ name
    let segs := lexical joined
    if joined.startsWith "/" then "/" ++ "/".intercalate segs
    else if segs.isEmpty then "." else "/".intercalate segs

end LeanTex.Cli.PublicationPaths
