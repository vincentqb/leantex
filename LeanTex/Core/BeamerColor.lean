module

public import LeanTex.Core.Ir
import LeanTex.Core.KeyVal

namespace LeanTex.Core.BeamerColor

open Ir

/-- The internal marker the two original groups follow; a space cannot occur in a control word. -/
public def marker : String := " beamer color"
public def starMarker : String := " beamer color*"
public def standoutMarker : String := " beamer standout color"
/-- A paint site a block template reads: its element, channel and the palette entry it paints. -/
public def siteMarker : String := " beamer color site"

/-- The role an element's channel writes, from the registry row that binds it. -/
public def channelRole (name : String) (ch : Channel) : Option Role :=
  Role.all.find? fun r => r.row.beamer.contains (name, ch)

/-- Beamer's named elements with native paint sites and the roles their two channels write, in
registry order (beamercolorthemedefault.sty, beamercolorthememoloch.sty). -/
public def roles : List (String × Option Role × Option Role) :=
  let names := Role.all.flatMap fun r => r.row.beamer.map (·.1)
  (names.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []).map fun n =>
    (n, channelRole n .fg, channelRole n .bg)

/-- beamer's default colour theme's parent relationships among the modelled elements
(beamercolorthemedefault.sty). -/
private def defaultParents : String → List String
  | "framesubtitle" => ["frametitle"]
  | "frametitle" | "section title" => ["titlelike"]
  | "titlelike" => ["structure"]
  | "progress bar in section page" | "title separator" => ["progress bar"]
  | "block title" => ["structure"]
  | "block title alerted" => ["alerted text"]
  | "block title example" => ["example text"]
  | _ => []

public inductive Value where
  | source (text : String)
  | native (color : Color)
  deriving Inhabited

public structure Element where
  name : String
  fg : Option Value := none
  bg : Option Value := none
  parents : Option (List String) := none
  uses : List String := []
  reset : Bool := false
  declared : Bool := true
  span : Span := ⟨"", {}⟩
  sites : List (String × Span) := []
  deriving Inhabited

/-- A colour theme's own declarations over the default theme's, as it runs them at load
(beamercolorthememoloch.sty for moloch; none for any other theme). -/
private def themeElement (theme name : String) : Option Element :=
  if theme != "moloch" then none else
  match name with
  | "titlelike" => some { name, uses := ["normal text"], parents := some ["normal text"] }
  | "structure" =>
    some { name, uses := ["normal text"], fg := some (.source "normal text.fg") }
  | "block title" =>
    some { name, uses := ["normal text"], fg := some (.source "normal text.fg"),
           bg := some (.source "") }
  | "block title alerted" => some { name, uses := ["block title", "alerted text"] }
  | "block title example" => some { name, uses := ["block title", "example text"] }
  | "block body alerted" | "block body example" =>
    some { name, uses := ["block body"], parents := some ["block body"] }
  | "progress bar in section page" | "title separator" =>
    some { name, uses := ["progress bar"], parents := some ["progress bar"] }
  | _ => none

private def Element.site (e : Element) (key : String) : Span :=
  (e.sites.lookup key).getD e.span

public structure Issue where
  message : String
  span : Span

/-- A standout option's appended alias, read inside the inner theme's group. -/
public structure StandoutAlias where
  name : String
  source : String
  span : Span

/-- End the alias scope without discarding unrelated flow declarations. -/
public def restoreAliases (opening : Palette) (current : Palette)
    (names : List String) : Palette :=
  names.foldl (fun pal name => pal.restore opening (.color name)) current

public theorem restoreAliases_contract (opening current : Palette)
    (names : List String) (key : ColorRef) :
    (restoreAliases opening current names).lookup key =
      if key ∈ names.map ColorRef.color then opening.lookup key
      else current.lookup key := by
  induction names generalizing current with
  | nil => rfl
  | cons name names ih =>
    simp only [restoreAliases, List.foldl_cons] at *
    rw [ih]
    by_cases hm : key ∈ names.map ColorRef.color
    · simp [hm]
    · by_cases he : key = .color name
      · subst he
        simp [hm, Palette.restore_exact]
      · simp [hm, he, Palette.restore_keeps_others _ _ _ _ he]

/-- The flow palette and named declarations; `opening` keeps the native values resolution
displaced. -/
public structure State where
  current : Option Palette := none
  elements : List Element := []
  opening : Palette := {}
  painted : Array Role := #[]
  reached : List String := []
  /-- Winning authored channels, rebuilt by `resolve` in native role order. -/
  origins : Array (String × Color × Span) := #[]
  standoutAliases : List StandoutAlias := []
  /-- The colour theme in force, whose own declarations stand under the document's. -/
  theme : String := ""
  /-- Paint sites a block template reads beside the native ones: the element chain, channel and
  palette entry. -/
  sites : List (List String × String × String) := []
  deriving Inhabited

/-- Register a template's paint site, replacing one already registered for the key. -/
public def State.addSite (s : State) (chain : List String) (channel key : String) : State :=
  let site := if channel == "fg" then (chain, key, "") else (chain, "", key)
  { s with sites := s.sites.filter (fun (_, f, b) => f != key && b != key) ++ [site] }

/-- The colour names the declarations' expressions spell. -/
public def State.sourceNames (s : State) : Array String :=
  s.elements.foldl (fun acc e =>
    [e.fg, e.bg].foldl (fun acc v => match v with
      | some (.source src) => (Ir.colorNames src).foldl
          (fun acc n => if acc.contains n then acc else acc.push n) acc
      | some (.native _) | none => acc) acc) #[]

private def unbrace (s : String) : String := (KeyVal.unbrace s).trimAscii.toString

private def names (s : String) : List String := (KeyVal.items (unbrace s)).toList

/-- `key=value`, an empty value kept: beamer's `bg=` clears the channel as `bg={}` does. -/
private def entryOf (entry : String) : Option (String × String) :=
  match KeyVal.entry entry with
  | (k, some v) => if k.isEmpty then none else some (k, v)
  | (_, none) => none

/-- Update only the keys that occur; the starred form first clears both channels and both
relationships (beamerbasecolor.sty). -/
public def State.declare (s : State) (name : String) (star : Bool) (src : String)
    (span : Span) : State × List String := Id.run do
  let mut e := if star then { name := name, reset := true, span := span }
    else { ((s.elements.find? (·.name == name)).getD { name := name }) with
      span := span, declared := true }
  let mut unsupported := []
  for entry in KeyVal.items src do
    match entryOf entry with
    | some (key, v) =>
      e := { e with sites := e.sites.filter (·.1 != key) ++ [(key, span)] }
      match key with
      | "fg" => e := { e with fg := some (.source (unbrace v)) }
      | "bg" => e := { e with bg := some (.source (unbrace v)) }
      | "parent" => e := { e with parents := some (names v) }
      | "use" => e := { e with uses := names v }
      | _ => unsupported := unsupported ++ [key]
    | none => unsupported := unsupported ++ [entry]
  return ({ s with elements := s.elements.filter (·.name != name) ++ [e] }, unsupported)

/-- A native role declared later wins too; fixed colours keep their native model, CMYK included. -/
public def State.native (s : State) (key : Role) (color : Color) : State := Id.run do
  if s.elements.isEmpty then return s
  let mut s := { s with opening := s.opening.declare (.role key) color }
  for (name, fg, bg) in roles do
    if fg == some key || bg == some key then
      let e := (s.elements.find? (·.name == name)).getD
        { name := name, declared := false }
      let e := if fg == some key then { e with fg := some (.native color) }
        else { e with bg := some (.native color) }
      s := { s with elements := s.elements.filter (·.name != name) ++ [e] }
  return s

private structure Channel where
  color : Option Color
  origin : Option Span := none

private structure Reading where
  /-- `none` leaves an earlier parent alone; a channel with no colour explicitly clears it. -/
  fg : Option Channel := none
  bg : Option Channel := none
  issues : List Issue := []

private def Reading.over (a b : Reading) : Reading :=
  { fg := b.fg.or a.fg, bg := b.bg.or a.bg, issues := a.issues ++ b.issues }

private theorem Reading.over_projects (a b : Reading) :
    ((a.over b).fg.map Channel.color, (a.over b).bg.map Channel.color) =
      ((b.fg.map Channel.color).or (a.fg.map Channel.color),
       (b.bg.map Channel.color).or (a.bg.map Channel.color)) := by
  cases hfg : b.fg <;> cases hbg : b.bg <;> simp [Reading.over, hfg, hbg]

private def own (pal : Palette) (name : String) : Reading :=
  match roles.lookup name with
  | some (fg, bg) =>
    { fg := (fg.bind (Design.declared? pal)).map (fun c => ⟨some c, none⟩),
      bg := (bg.bind (Design.declared? pal)).map (fun c => ⟨some c, none⟩) }
  | none => if name == "structure" then
      { fg := (Design.declared? pal .ink).map (fun c => ⟨some c, none⟩) } else {}

/-- An element over its colour theme's declaration: the document's keys first, then the theme's. -/
private def withTheme (pal : Palette) (theme : String) (e : Element) : Element :=
  match e.reset, themeElement theme e.name with
  | false, some t =>
    let native := own pal e.name
    { e with
      fg := e.fg.orElse fun _ => if native.fg.isSome then none else t.fg
      bg := e.bg.orElse fun _ => if native.bg.isSome then none else t.bg
      uses := if (e.sites.lookup "use").isSome then e.uses else t.uses
      parents := e.parents.orElse fun _ => t.parents }
  | true, _ | false, none => e

/-- Depth-first resolution over the colour declarations, a path detecting cycles. -/
private def read (theme : String) (pal : Palette) (path : List (String × Option Span))
    (es : List Element) (name : String) : Reading := Id.run do
  if let some (_, span) := path.find? (·.1 == name) then
    let span := span.orElse fun _ =>
      (path.takeWhile (·.1 != name)).findSome? (·.2)
    return { issues := [⟨s!"colour inheritance cycle at '{name}'", span.getD ⟨"", {}⟩⟩] }
  let i := es.findIdx (·.name == name)
  if h : i < es.length then
    let e := withTheme pal theme es[i]
    let rest := es.eraseIdx i
    let mut r : Reading := {}
    let mut aliases := pal
    -- beamer@thc@docolor runs `use` before `parent`.
    for used in e.uses do
      let u := read theme aliases ((name, e.sites.lookup "use") :: path) rest used
      let fgNow := Design.printInk aliases
      let bgNow := Design.printPage aliases
      aliases := aliases.declare (.color (used ++ ".fg")) ((u.fg.bind (·.color)).getD fgNow)
      aliases := aliases.declare (.color (used ++ ".bg")) ((u.bg.bind (·.color)).getD bgNow)
      r := { r with issues := r.issues ++ u.issues }
    for parent in e.parents.getD (if e.reset then [] else defaultParents name) do
      r := r.over (read theme aliases ((name, e.sites.lookup "parent") :: path) rest parent)
    let defaults := if e.reset then ({} : Reading) else own pal name
    let channel (key : String) (v : Option Value) (fallback : Option Channel) :
        Option Channel × List Issue :=
      match v with
      | none => (fallback, [])
      | some (.native c) => (some ⟨some c, none⟩, [])
      | some (.source "") => (some ⟨none, some (e.site key)⟩, [])
      | some (.source src) =>
        match aliases.resolveSource none src with
        | .ok (some c) => (some ⟨some c, some (e.site key)⟩, [])
        | _ => (none, [⟨s!"'{name}' {key} colour '{src}' cannot be resolved", e.site key⟩])
    let (fg, fgIssues) := channel "fg" e.fg defaults.fg
    let (bg, bgIssues) := channel "bg" e.bg defaults.bg
    return { r.over { fg := fg, bg := bg } with
      issues := r.issues ++ fgIssues ++ bgIssues }
  else return {}
termination_by es.length
decreasing_by all_goals
  have h' : es.findIdx (·.name == name) < es.length := h
  rw [List.length_eraseIdx_of_lt h']
  omega

/-- The channels a paint site reads through an element. -/
private structure Open where
  fg : Bool
  bg : Bool

/-- The colour names an xcolor expression reads (`a!30!b`); a percentage
never spells an alias, so every part may be compared. -/
private def mentions : Option Value → List String
  | some (.source src) => (src.splitOn "!").map (·.trimAscii.toString)
  | _ => []

/-- The elements a paint site reading channels `o` of `name` reaches, and the aliases its
expressions name (beamerbasecolor.sty's `docolor`). -/
private def reach (theme : String) (pal : Palette) (es : List Element) (name : String)
    (o : Open) : List String × List String := Id.run do
  if !(o.fg || o.bg) then return ([], [])
  let i := es.findIdx (·.name == name)
  if h : i < es.length then
    let e := withTheme pal theme es[i]
    let rest := es.eraseIdx i
    let native := if e.reset then ({} : Reading) else own pal name
    let mut said := (if o.fg then mentions e.fg else []) ++ (if o.bg then mentions e.bg else [])
    let mut names := [name]
    let mut po : Open :=
      { fg := o.fg && e.fg.isNone && native.fg.isNone,
        bg := o.bg && e.bg.isNone && native.bg.isNone }
    for parent in (e.parents.getD (if e.reset then [] else defaultParents name)).reverse do
      let (n, m) := reach theme pal rest parent po
      names := names ++ n
      said := said ++ m
      let r := read theme pal [] rest parent
      po := { fg := po.fg && r.fg.isNone, bg := po.bg && r.bg.isNone }
    for used in e.uses do
      let (n, m) := reach theme pal rest used
        { fg := said.contains (used ++ ".fg"), bg := said.contains (used ++ ".bg") }
      names := names ++ n
      said := said ++ m
    return (names, said)
  else return ([], [])
termination_by es.length
decreasing_by all_goals
  have h' : es.findIdx (·.name == name) < es.length := h
  rw [List.length_eraseIdx_of_lt h']
  omega

/-- The colours beamer names at the document's start (beamerbasecolor.sty), readable without
`use`. -/
private def startColors : List String :=
  ["normal text", "structure", "alerted text", "example text"]

/-- Resolve the engine's sites against the declarations in force; later explicit aliases of one
site win. -/
public def State.resolve (s : State) (pal : Palette) : State × Palette × List Issue := Id.run do
  let base := s.painted.foldl (fun p key => p.restore s.opening (.role key)) pal
  let mut s := { s with origins := #[] }
  let mut out := base
  let mut issues := []
  let allNames := (roles.map (·.1)) ++ (s.sites.flatMap (·.1)) ++ ["structure", "titlelike"] ++
    s.elements.flatMap (fun e => e.parents.getD [] ++ e.uses)
  let es := allNames.foldl (fun es name =>
    if es.any (·.name == name) then es
    else es ++ [{ name := name, declared := false }]) s.elements
  -- Frame furniture starts from normal text, resolved before the sites.
  let normal := read s.theme base [] es "normal text"
  let context := [(Role.ink, normal.fg), (Role.page, normal.bg)].foldl (fun p (key, value) =>
    match value.map (·.color) with
    | none => p
    | some none => p.erase (.role key)
    | some (some c) => p.declare (.role key) c) base
  let normalFg := Design.printInk context
  let context := startColors.foldl
    (fun p name =>
      let r := read s.theme p [] es name
      (p.declare (.color (name ++ ".fg")) ((r.fg.bind (·.color)).getD (Design.printInk p))).declare
        (.color (name ++ ".bg")) ((r.bg.bind (·.color)).getD (Design.printPage p))) context
  let rank (name : String) : Nat :=
    let i := s.elements.findIdx (·.name == name)
    if i < s.elements.length then i + 1 else 0
  let ordered := roles.mergeSort fun a b => rank a.1 ≤ rank b.1
  let normalBg := Design.printPage context
  -- A template's site always paints: each channel is the latest element's that sets it, else
  -- normal text's (beamerbasecolor.sty).
  for (chain, fgKey, bgKey) in s.sites do
    let mut fg : Option Color := none
    let mut bg : Option Color := none
    for name in chain do
      if (fgKey.isEmpty || fg.isSome) && (bgKey.isEmpty || bg.isSome) then break
      let r := read s.theme context [] es name
      let (names, _) := reach s.theme context es name
        { fg := !fgKey.isEmpty && fg.isNone, bg := !bgKey.isEmpty && bg.isNone }
      s := { s with reached := s.reached ++ names }
      issues := issues ++ r.issues
      if fg.isNone then fg := r.fg.bind (·.color)
      if bg.isNone then bg := r.bg.bind (·.color)
    unless fgKey.isEmpty do out := out.declare (ColorRef.ofKey fgKey) (fg.getD normalFg)
    unless bgKey.isEmpty do out := out.declare (ColorRef.ofKey bgKey) (bg.getD normalBg)
  for (name, fgKey, bgKey) in ordered do
    let r := read s.theme context [] es name
    let (names, said) := reach s.theme context es name { fg := fgKey.isSome, bg := bgKey.isSome }
    let names := startColors.foldl (fun acc start => acc ++ (reach s.theme context es start
      { fg := said.contains (start ++ ".fg"), bg := said.contains (start ++ ".bg") }).1) names
    s := { s with reached := s.reached ++ names }
    -- A site is repainted only when a declaration reaches it.
    if names.any fun n => es.any fun e => e.name == n && e.declared then
      issues := issues ++ r.issues
      for (role, value) in [(fgKey, r.fg), (bgKey, r.bg)] do
        if let some key := role then
          let origin := value.bind (·.origin)
          let value := value.bind (·.color)
          -- An empty beamer heading inherits normal text.
          let value := if key == .frameTitleInk then value.or (some normalFg) else value
          unless s.painted.contains key do
            s := { s with opening := s.opening.restore base (.role key),
                          painted := s.painted.push key }
          let name := (ColorRef.role key).key
          s := { s with origins := s.origins.filter (·.1 != name) }
          if let (some c, some span) := (value, origin) then
            s := { s with origins := s.origins.push (name, c, span) }
          out := match value with
            | some c => out.declare (.role key) c
            | none => out.erase (.role key)
  return (s, out, issues)

end LeanTex.Core.BeamerColor
