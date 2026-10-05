import LeanTex.Core.Parse
import LeanTex.Core.Decl

namespace LeanTex.Core.Tcolorbox

open Parse

/-- A tcolorbox use expressed through the native block surface. Declaration
arguments are bound by the compatibility reader before this function runs.
Keys with unsupported paint or layout effects remain explicitly accounted,
including partially supported spacing keys. -/
structure Lowered where
  raws : Array Raw
  unsupported : Array String
  deriving Repr

private def trim (rs : Array Raw) : Array Raw :=
  (rs.toList.dropWhile (· matches .space)).reverse.dropWhile
    (· matches .space) |>.reverse.toArray

private def value (rs : Array Raw) : Array Raw :=
  match (trim rs).toList with
  | [.group body _] => body
  | _ => trim rs

/-- pgfkeys separates entries at unbraced commas. The lexer leaves commas
inside word tokens; all nested raw constructs remain opaque. -/
private def entries (rs : Array Raw) : Array (Array Raw) := Id.run do
  let mut out := #[]
  let mut current := #[]
  for r in rs do
    match r with
    | .word s p =>
      let mut p := p
      let mut first := true
      for part in s.splitOn "," do
        unless first do
          out := out.push current
          current := #[]
          p := p.next false
        unless part.isEmpty do current := current.push (.word part p)
        p := { p with col := p.col + part.length }
        first := false
    | .sym ',' _ =>
      out := out.push current
      current := #[]
    | _ => current := current.push r
  return out.push current

/-- Only the first unbraced equals sign separates a key from its value.
The value is still tokens, including every subsequent equals sign. -/
private def entry (rs : Array Raw) : String × Array Raw := Id.run do
  let mut key := #[]
  for h : i in [:rs.size] do
    let r := rs[i]
    match r with
    | .word s p =>
      match s.splitOn "=" with
      | a :: b :: rest =>
        let tail := String.intercalate "=" (b :: rest)
        let right := if tail.isEmpty then #[] else
          #[Raw.word tail { p with col := p.col + a.length + 1 }]
        return (rawSrc (key.push (.word a p)),
          value (right ++ rs.extract (i + 1) rs.size))
      | _ => key := key.push r
    | .sym '=' _ =>
      return (rawSrc key, value (rs.extract (i + 1) rs.size))
    | _ => key := key.push r
  return (rawSrc key, #[])

private structure Settings where
  title : Array Raw := #[]
  fontTitle : Array Raw := #[]
  fontUpper : Array Raw := #[]
  textInk : Option (String × Array Raw) := none
  titleInk : Option (Array Raw) := none
  bodyGround : Bool := false
  titleGround : Bool := false
  before : Option String := none
  after : Option String := none
  unsupported : Array String := #[]

private def Settings.refuse (s : Settings) (key : String) : Settings :=
  if s.unsupported.contains key then s
  else { s with unsupported := s.unsupported.push key }

/-- Spacing uses the existing native glue reader. Accepted values are
lengths, so their serialized spelling cannot escape the native option head. -/
private def gap? (rs : Array Raw) : Option String :=
  let s := rawSrc rs
  match Decl.parseValue s with
  | some (.dim _) | some (.glue _) => some s
  | _ => none

/-- tcolorbox 6.9.0, manual keys `title`, `fontupper`, `fonttitle`,
`colupper`/`coltext`, `coltitle`, and `before`/`after skip`.
Decoration keys have no native block site and are accounted at the caller.
Repeated assignments have pgfkeys' last-write semantics. -/
private def settings (options : Array Raw) : Settings := Id.run do
  let mut s : Settings := {}
  for raw in entries options do
    if (rawSrc raw).isEmpty then continue
    let (key, v) := entry raw
    match key with
    | "title" => s := { s with title := v }
    | "fontupper" => s := { s with fontUpper := v }
    | "fonttitle" => s := { s with fontTitle := v }
    | "colupper" | "coltext" => s := { s with textInk := some (key, v) }
    | "coltitle" => s := { s with titleInk := some v }
    | "before skip" | "after skip" | "beforeafter skip" =>
      s := s.refuse key
      match gap? v with
      | some g =>
        if key != "after skip" then s := { s with before := some g }
        if key != "before skip" then s := { s with after := some g }
      | none => pure ()
    | "colback" => s := { s.refuse key with bodyGround := true }
    | "colframe" | "colbacktitle" | "boxed title style" =>
      s := { s.refuse key with titleGround := true }
    | _ => s := s.refuse (if key.isEmpty then rawSrc raw else key)
  -- premise: TcolorboxChecks.groundChecks — carrying a foreground after
  -- dropping its declared ground can erase readable body or title ink.
  if s.bodyGround then
    if let some (key, _) := s.textInk then
      s := { s.refuse key with textInk := none }
  if s.titleGround && s.titleInk.isSome then
    s := { s.refuse "coltitle" with titleInk := none }
  return s

/-- The native ink marker is the same surface produced for xcolor's
`\color`: its value goes through Elab's one typed colour resolver. -/
private def ink (v : Option (Array Raw)) (pos : Pos) : Array Raw :=
  match v with
  | none => #[]
  | some rs => #[.ctrl ("@ink:" ++ rawSrc rs) pos]

private def gap (v : Option String) (pos : Pos) : Array Raw :=
  match v with
  | none => #[]
  | some s =>
    #[.ctrl "block" pos, .sym '[' pos, .word ("before = " ++ s) pos,
      .sym ']' pos, .group #[] pos]

/-- Lower already-bound options and an untouched body through native block
semantics. No author text is lexed or parsed a second time. The gaps use
native block spacing; tcolorbox's addvspace/parskip collision rules and
decorations are not reimplemented. -/
def lower (options body : Array Raw) (pos : Pos) : Lowered :=
  let s := settings options
  let titleInk := ink s.titleInk pos
  let titleDecls := s.fontTitle ++ titleInk
  let title := if s.title.isEmpty || titleDecls.isEmpty then s.title
    else #[.group (titleDecls ++ s.title) pos]
  let bodyDecls := s.fontUpper ++ ink (s.textInk.map (·.2)) pos
  let block := Raw.env "block"
    #[.group title pos, .group (bodyDecls ++ body) pos] pos
  let before := gap s.before pos
  let after := gap s.after pos
  { raws := before.push block ++ after
    unsupported := s.unsupported }

/-- A raw block carries the complete ordered body after only its local
declarations. This is a surface property, before an IR exists; the native
elaborator and both emitters are exercised by the artifact checks. -/
def CarriesBody (rs body : Array Raw) (pos : Pos) : Prop :=
  ∃ title decls, Raw.env "block"
    #[.group title pos, .group (decls ++ body) pos] pos ∈ rs.toList

/-- Every option combination retains the original body verbatim in the
native block, including when an option is unsupported. -/
theorem lower_body_covers (options body : Array Raw) (pos : Pos) :
    CarriesBody (lower options body pos).raws body pos := by
  let s := settings options
  let titleInk := ink s.titleInk pos
  let titleDecls := s.fontTitle ++ titleInk
  let title := if s.title.isEmpty || titleDecls.isEmpty then s.title
    else #[.group (titleDecls ++ s.title) pos]
  refine ⟨title, s.fontUpper ++ ink (s.textInk.map (·.2)) pos, ?_⟩
  simp [lower, s, title, titleDecls, titleInk]

end LeanTex.Core.Tcolorbox
