module

public import LeanTex.Core.Parse
import LeanTex.Core.Decl

namespace LeanTex.Core.Tcolorbox

open Parse

/-- An environment binding's name in the scoped meaning table; the space keeps it apart from
authored names. -/
public def bindingName (name : String) : String := "tcolorbox " ++ name

/-- The native block environment a lowered box stands in, unspellable by a document. -/
public def boxEnv : String := "tcolorbox box"

/-- The inverse of the reserved binding spelling. -/
public def boundName? (name : String) : Option String :=
  name.dropPrefix? "tcolorbox " |>.map (·.toString)

public theorem boundName?_exact (name : String) :
    boundName? name = (name.dropPrefix? "tcolorbox ").map (·.toString) := by
  rfl

/-- A tcolorbox use expressed through the native block surface, unsupported keys accounted. -/
public structure Lowered where
  raws : Array Raw
  unsupported : Array String
  /-- The source of each refused key's value, which still names what it names. -/
  refusedValues : Array String
  /-- The keys applied in part, through the native block's spacing. -/
  inPart : Array String
  deriving Repr

private def value (rs : Array Raw) : Array Raw :=
  match (trimSpace rs).toList with
  | [.group body _] => body
  | _ => trimSpace rs

/-- A key and its value, split at the first unbraced equals sign. -/
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
  refusedValues : Array String := #[]
  inPart : Array String := #[]

private def Settings.refuse (s : Settings) (key : String) (value : String := "") : Settings :=
  let s := if value.isEmpty then s else { s with refusedValues := s.refusedValues.push value }
  if s.unsupported.contains key then s
  else { s with unsupported := s.unsupported.push key }

private def Settings.partly (s : Settings) (key : String) : Settings :=
  if s.inPart.contains key then s else { s with inPart := s.inPart.push key }

/-- A spacing value through the native glue reader. -/
private def gap? (rs : Array Raw) : Option String :=
  let s := rawSrc rs
  match Decl.parseValue s with
  | some (.dim _) | some (.glue _) => some s
  | _ => none

/-- The box keys `settings` reads (tcolorbox 6.9.0 manual), every other key refused. -/
public def readKeys : List String :=
  ["title", "fontupper", "fonttitle", "colupper", "coltext", "coltitle", "before skip",
   "after skip", "beforeafter skip", "colback", "colframe", "colbacktitle", "boxed title style"]

/-- The keys read: `title`, `fontupper`, `fonttitle`, `colupper`/`coltext`, `coltitle`,
`before`/`after skip`, last write winning. -/
private def settings (options : Array Raw) : Settings := Id.run do
  let mut s : Settings := {}
  for raw in rawEntries options do
    if (rawSrc raw).isEmpty then continue
    let (key, v) := entry raw
    if !readKeys.contains key then
      s := s.refuse (if key.isEmpty then rawSrc raw else key) (rawSrc v)
      continue
    match key with
    | "title" => s := { s with title := v }
    | "fontupper" => s := { s with fontUpper := v }
    | "fonttitle" => s := { s with fontTitle := v }
    | "colupper" | "coltext" => s := { s with textInk := some (key, v) }
    | "coltitle" => s := { s with titleInk := some v }
    | "before skip" | "after skip" | "beforeafter skip" =>
      match gap? v with
      | some g =>
        s := s.partly key
        if key != "after skip" then s := { s with before := some g }
        if key != "before skip" then s := { s with after := some g }
      | none => s := s.refuse key
    | "colback" => s := { s.refuse key (rawSrc v) with bodyGround := true }
    | "colframe" | "colbacktitle" | "boxed title style" =>
      s := { s.refuse key (rawSrc v) with titleGround := true }
    | _ => s := s.refuse (if key.isEmpty then rawSrc raw else key) (rawSrc v)
  -- premise: TcolorboxChecks.groundChecks — a foreground without its ground can erase ink
  if s.bodyGround then
    if let some (key, v) := s.textInk then
      s := { s.refuse key (rawSrc v) with textInk := none }
  if s.titleGround then
    if let some v := s.titleInk then
      s := { s.refuse "coltitle" (rawSrc v) with titleInk := none }
  return s

/-- The native ink marker, resolved through Elab's typed colour resolver as `\color` is. -/
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

/-- Selected content and declarations, apart from the keys the engine cannot apply. -/
public structure Prepared where
  title : Array Raw
  bodyDecls : Array Raw
  before : Option String
  after : Option String
  unsupported : Array String
  refusedValues : Array String
  inPart : Array String
  deriving Repr

/-- tcolorbox 6.9.0 selects its `.colorlet` colours before the font hooks, so a hook's explicit
colour wins. -/
private def Settings.prepared (s : Settings) (pos : Pos) : Prepared :=
  let titleInk := ink s.titleInk pos
  let titleDecls := titleInk ++ s.fontTitle
  { title := if s.title.isEmpty || titleDecls.isEmpty then s.title
      else #[.group (titleDecls ++ s.title) pos]
    bodyDecls := ink (s.textInk.map (·.2)) pos ++ s.fontUpper
    before := s.before
    after := s.after
    unsupported := s.unsupported
    refusedValues := s.refusedValues
    inPart := s.inPart }

/-- Select the last assignments before executing any key's value. -/
public def prepare (options : Array Raw) (pos : Pos) : Prepared :=
  (settings options).prepared pos

/-- Capture the selected colour operands at the use site before either font hook runs. -/
public def prepareM [Monad m]
    (capture : String → Array Raw → m (Option (Array Raw)))
    (options : Array Raw) (pos : Pos) : m Prepared := do
  let mut s := settings options
  if let some (key, rs) := s.textInk then
    match ← capture key rs with
    | some rs => s := { s with textInk := some (key, rs) }
    | none => s := { s.refuse key (rawSrc rs) with textInk := none }
  if let some rs := s.titleInk then
    match ← capture "coltitle" rs with
    | some rs => s := { s with titleInk := some rs }
    | none => s := { s.refuse "coltitle" (rawSrc rs) with titleInk := none }
  return s.prepared pos

public theorem prepareM_identity_exact (options : Array Raw) (pos : Pos) :
    prepareM (m := Id) (fun _ rs => pure (some rs)) options pos =
      prepare options pos := by
  unfold prepareM prepare
  generalize settings options = s
  cases s with
  | mk title fontTitle fontUpper textInk titleInk bodyGround titleGround before after unsupported
      refusedValues inPart =>
    cases textInk <;> cases titleInk <;> rfl

/-- Assemble the already-selected fields around the original body. -/
public def Prepared.lower (s : Prepared) (body : Array Raw) (pos : Pos) : Lowered :=
  let block := Raw.env boxEnv
    #[.group s.title pos, .group (s.bodyDecls ++ body) pos] pos
  let before := gap s.before pos
  let after := gap s.after pos
  { raws := before.push block ++ after
    unsupported := s.unsupported
    refusedValues := s.refusedValues
    inPart := s.inPart }

/-- Lower already-bound options and an untouched body through native block semantics. -/
public def lower (options body : Array Raw) (pos : Pos) : Lowered :=
  (prepare options pos).lower body pos

/-- A raw block carries the complete ordered body after only its local declarations. -/
@[expose] public def CarriesBody (rs body : Array Raw) (pos : Pos) : Prop :=
  ∃ title decls, Raw.env boxEnv
    #[.group title pos, .group (decls ++ body) pos] pos ∈ rs.toList

public theorem Prepared.lower_body_covers (s : Prepared) (body : Array Raw) (pos : Pos) :
    CarriesBody (s.lower body pos).raws body pos := by
  refine ⟨s.title, s.bodyDecls, ?_⟩
  simp [Prepared.lower]

public theorem lower_body_covers (options body : Array Raw) (pos : Pos) :
    CarriesBody (lower options body pos).raws body pos :=
  (prepare options pos).lower_body_covers body pos

end LeanTex.Core.Tcolorbox
