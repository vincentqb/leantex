module

public import LeanTex.Core.Ir

namespace LeanTex.Core.BeamerColor

open Ir

/-- A space cannot occur in an author's control word. The two original
groups follow this internal marker; no author text is encoded into it. -/
public def marker : String := " beamer color"
public def starMarker : String := " beamer color*"
public def standoutMarker : String := " beamer standout color"
/-- A paint site a block template reads (`\usebeamercolor[bg]{element}` at a
rule): its element, channel and the palette entry it paints. -/
public def siteMarker : String := " beamer color site"

/-- Beamer's named elements with genuine native paint sites. In particular,
the head/foot progress placement is absent: a section rule is not that site.
Sources: beamercolorthemedefault.sty and beamercolorthememoloch.sty. -/
public def roles : List (String × String × String) :=
  [("normal text", "fg", "bg"), ("background canvas", "", "bg"),
   ("frametitle", "frametitlefg", "frametitlebg"),
   ("headline", "frametitlefg", "frametitlebg"),
   ("framesubtitle", "framesubtitlefg", ""),
   ("section title", "sectiontitlefg", ""),
   ("block title", "blocktitlefg", "blocktitlebg"),
   ("block title alerted", "alerttitlefg", "alerttitlebg"),
   ("block title example", "exampletitlefg", "exampletitlebg"),
   ("block body", "blockbodyfg", "blockbodybg"),
   ("block body alerted", "alertbodyfg", "alertbodybg"),
   ("block body example", "examplebodyfg", "examplebodybg"),
   ("alerted text", "alert", ""), ("example text", "example", ""),
   ("standout", "standoutfg", "standoutbg"),
   ("progress bar", "progressfg", "progressbg"),
   ("progress bar in section page", "sectionprogressfg", "sectionprogressbg"),
   ("title separator", "separator", ""),
   ("footline", "muted", "footlinebg"),
   ("page number in head/foot", "muted", "")]

/-- beamer's default colour theme's relationships among the modelled
elements (beamercolorthemedefault.sty): relationships, not copied colours.
The title-like elements hang on `structure` through `titlelike`, the block
titles on `structure` and the text roles, and the block bodies on nothing.
The progress-bar variants are elements the default theme does not have; the
furniture the engine draws for them everywhere inherits as moloch, which
defines them, declares. -/
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

/-- A colour theme's own declarations over the default theme's, as it runs
them at load: unstarred `\setbeamercolor`s, each keeping what it does not
name. moloch 2.1.0's (beamercolorthememoloch.sty: `\moloch@setup@text@colors`,
`\moloch@setup@block@colors` and the progress-bar parents, which its
`background=light` default runs; it loads with no `block` option):
`titlelike` hangs on normal text and `structure` takes its ink; the block
title takes normal text's ink and clears its fill, keeping its `structure`
parent, which therefore reaches neither channel; the alerted and example
titles only `use` the block title and their text role, keeping the default
theme's parents, so a fill declared on `alerted text` or `example text`
paints their bars; the alerted and example bodies inherit the block body,
which the theme leaves the default theme's empty one. Every other theme
declares none of these. The `block` option's declarations are the
document's own (`Compat.molochOptions`). -/
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

/-- A standout option's appended alias is read when the option runs,
inside the group opened by the Moloch/Metropolis inner theme. -/
public structure StandoutAlias where
  name : String
  source : String
  span : Span

/-- End the alias scope without discarding unrelated flow declarations. -/
public def restoreAliases (opening : Palette) (current : Palette)
    (names : List String) : Palette :=
  names.foldl (fun pal name => pal.restore opening name) current

/-- Every scoped name regains its opening value, including absence; every
other name keeps the closing epoch's value. This is independent of colours,
declaration order, duplicate aliases and intervening flow declarations. -/
public theorem restoreAliases_contract (opening current : Palette)
    (names : List String) (key : String) :
    (restoreAliases opening current names).find? key =
      if key ∈ names then opening.find? key else current.find? key := by
  induction names generalizing current with
  | nil => rfl
  | cons name names ih =>
    simp only [restoreAliases, List.foldl_cons] at *
    rw [ih]
    by_cases hm : key ∈ names
    · simp [hm]
    · by_cases he : key = name
      · subst name
        simp [hm, Palette.restore_exact]
      · simp [hm, he, Palette.restore_keeps_others _ _ _ _ he]

/-- Flow palette and named declarations share one elaborator state field.
`opening` remembers the native values displaced by resolution, so a later
parent update never inherits its own previously resolved result. -/
public structure State where
  current : Option Palette := none
  elements : List Element := []
  opening : Palette := {}
  painted : Array String := #[]
  reached : List String := []
  /-- Winning authored channels, rebuilt by `resolve` in native role order. -/
  origins : Array (String × Color × Span) := #[]
  standoutAliases : List StandoutAlias := []
  /-- The colour theme in force, whose own declarations (`themeElement`)
  stand under the document's. -/
  theme : String := ""
  /-- Paint sites a block template reads beside the native ones (`roles`'
  shape): the elements a rule's colour reads its channel through — each
  `\usebeamercolor` in force there, the latest first — and the palette entry
  that channel paints. -/
  sites : List (List String × String × String) := []
  deriving Inhabited

/-- Register a template's paint site: the channel the chain of elements binds
paints `key`. A site already registered for the key is replaced. -/
public def State.addSite (s : State) (chain : List String) (channel key : String) : State :=
  let site := if channel == "fg" then (chain, key, "") else (chain, "", key)
  { s with sites := s.sites.filter (fun (_, f, b) => f != key && b != key) ++ [site] }

private def unbrace (s : String) : String :=
  let s := s.trimAscii.toString
  if s.startsWith "{" && s.endsWith "}" then
    ((s.drop 1).dropEnd 1).toString.trimAscii.toString
  else s

private def names (s : String) : List String :=
  ((unbrace s).splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- `key=value`, where an empty value is kept: beamer's `bg=` clears the
channel as `bg={}` does (moloch's own block colours spell it so). -/
private def entryOf (entry : String) : Option (String × String) :=
  match entry.splitOn "=" with
  | key :: value :: more =>
    let k := key.trimAscii.toString
    if k.isEmpty then none
    else some (k, (String.intercalate "=" (value :: more)).trimAscii.toString)
  | _ => none

/-- Update only the keys that occur, except that the starred form first
clears both channels and both relationships (beamerbasecolor.sty). -/
public def State.declare (s : State) (name : String) (star : Bool) (src : String)
    (span : Span) : State × List String := Id.run do
  let mut e := if star then { name := name, reset := true, span := span }
    else { ((s.elements.find? (·.name == name)).getD { name := name }) with
      span := span, declared := true }
  let mut unsupported := []
  for entry in Decl.splitEntries src do
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

/-- A native role declared later wins too. Fixed colours retain their native
model, including CMYK; the compatibility resolver never converts them. -/
public def State.native (s : State) (key : String) (color : Color) : State := Id.run do
  if s.elements.isEmpty then return s
  let mut s := { s with opening := s.opening.declare key color }
  for (name, fg, bg) in roles do
    if key == fg || key == bg then
      let e := (s.elements.find? (·.name == name)).getD
        { name := name, declared := false }
      let e := if key == fg then { e with fg := some (.native color) }
        else { e with bg := some (.native color) }
      s := { s with elements := s.elements.filter (·.name != name) ++ [e] }
  return s

private structure Channel where
  color : Option Color
  origin : Option Span := none

private structure Reading where
  /-- `none` leaves an earlier parent alone; a channel with no colour
  explicitly clears it. Empty `fg={}` / `bg={}` still run. -/
  fg : Option Channel := none
  bg : Option Channel := none
  issues : List Issue := []

private def Reading.over (a b : Reading) : Reading :=
  { fg := b.fg.or a.fg, bg := b.bg.or a.bg, issues := a.issues ++ b.issues }

/-- Dropping origins commutes with the per-channel override decision. -/
private theorem Reading.over_projects (a b : Reading) :
    ((a.over b).fg.map Channel.color, (a.over b).bg.map Channel.color) =
      ((b.fg.map Channel.color).or (a.fg.map Channel.color),
       (b.bg.map Channel.color).or (a.bg.map Channel.color)) := by
  cases hfg : b.fg <;> cases hbg : b.bg <;> simp [Reading.over, hfg, hbg]

private def own (pal : Palette) (name : String) : Reading :=
  match roles.lookup name with
  | some (fg, bg) =>
    { fg := (pal.find? fg).map (fun c => ⟨some c, none⟩),
      bg := (pal.find? bg).map (fun c => ⟨some c, none⟩) }
  | none => if name == "structure" then
      { fg := (pal.find? "fg").map (fun c => ⟨some c, none⟩) } else {}

/-- An element as it stands over its colour theme's declaration
(`themeElement`): the document's keys, then the theme's where the document
named none — `use` and `parent` whole, as `\setbeamercolor` replaces them,
and a channel only where the palette holds no native value for it, since a
native declaration stands later than any theme's load. A starred
declaration cleared the theme's too. -/
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

/-- DFS removes the current element before descending. A path detects a
cycle, and the shrinking declaration list proves termination without fuel.
Only colour declarations are visited, never document content. -/
private def read (theme : String) (pal : Palette) (path : List (String × Option Span))
    (es : List Element) (name : String) : Reading := Id.run do
  if let some (_, span) := path.find? (·.1 == name) then
    -- Default edges have no authored site. Choose an explicit edge inside
    -- this cycle, never an unrelated channel or the path that entered it.
    let span := span.orElse fun _ =>
      (path.takeWhile (·.1 != name)).findSome? (·.2)
    return { issues := [⟨s!"colour inheritance cycle at '{name}'", span.getD ⟨"", {}⟩⟩] }
  let i := es.findIdx (·.name == name)
  if h : i < es.length then
    let e := withTheme pal theme es[i]
    let rest := es.eraseIdx i
    let mut r : Reading := {}
    let mut aliases := pal
    -- beamer@thc@docolor runs `use` before `parent`. Empty used channels
    -- bind the current foreground/background, rather than no alias.
    for used in e.uses do
      let u := read theme aliases ((name, e.sites.lookup "use") :: path) rest used
      let current := Design.ofPalette aliases
      aliases := aliases.declare (used ++ ".fg") ((u.fg.bind (·.color)).getD current.fg)
      aliases := aliases.declare (used ++ ".bg") ((u.bg.bind (·.color)).getD current.bg)
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

/-- The elements a paint site reading channels `o` of `name` reaches, and
the aliases the expressions it consumes name: what `read` resolves, as a
census of whose declarations can change the paint. A channel the element's
own value or the palette's native one fills is closed to its parents, a
later parent's to an earlier one (beamerbasecolor.sty's `docolor`, own
values last), and a `use` reaches only through a consumed expression naming
its alias. So a parent the child overrides on every channel — moloch's
block title over `structure` — is not reached, and its declaration is named
unused (`finishBeamerColors`). -/
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

/-- beamer names these at the document's start (beamerbasecolor.sty:
`\usebeamercolor{normal text}` and the starred `structure`, `alerted text`,
`example text`), so any declaration may read them without `use`. -/
private def startColors : List String :=
  ["normal text", "structure", "alerted text", "example text"]

/-- Resolve the finite set of engine sites against the declarations in force.
Later explicit aliases of one native site win. `use` makes temporary xcolor
aliases available to expressions, but contributes no inherited channel.
Missing parents contribute nothing, as in Beamer. -/
public def State.resolve (s : State) (pal : Palette) : State × Palette × List Issue := Id.run do
  let base := s.painted.foldl (fun p key => p.restore s.opening key) pal
  let mut s := { s with origins := #[] }
  let mut out := base
  let mut issues := []
  let allNames := (roles.map (·.1)) ++ (s.sites.flatMap (·.1)) ++ ["structure", "titlelike"] ++
    s.elements.flatMap (fun e => e.parents.getD [] ++ e.uses)
  let es := allNames.foldl (fun es name =>
    if es.any (·.name == name) then es
    else es ++ [{ name := name, declared := false }]) s.elements
  -- Frame furniture starts from normal text. Resolve that context before
  -- the sites, even when normal text was declared after a child.
  let normal := read s.theme base [] es "normal text"
  let context := [("fg", normal.fg), ("bg", normal.bg)].foldl (fun p (key, value) =>
    match value.map (·.color) with
    | none => p
    | some none => p.erase key
    | some (some c) => p.declare key c) base
  let normalFg := (Design.ofPalette context).fg
  let context := startColors.foldl
    (fun p name =>
      let r := read s.theme p [] es name
      let d := Design.ofPalette p
      (p.declare (name ++ ".fg") ((r.fg.bind (·.color)).getD d.fg)).declare (name ++ ".bg")
        ((r.bg.bind (·.color)).getD d.bg)) context
  let rank (name : String) : Nat :=
    let i := s.elements.findIdx (·.name == name)
    if i < s.elements.length then i + 1 else 0
  let ordered := roles.mergeSort fun a b => rank a.1 ≤ rank b.1
  let normalBg := (Design.ofPalette context).bg
  -- A template's site always paints, as beamerbasecolor.sty's
  -- `\usebeamercolor` binds `fg` and `bg`: each element binds the channels
  -- it sets and keeps the one in force where it sets none, so a channel is
  -- the latest element's that sets it, every later element read on the way,
  -- and else the colour in force there, normal text's.
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
    unless fgKey.isEmpty do out := out.declare fgKey (fg.getD normalFg)
    unless bgKey.isEmpty do out := out.declare bgKey (bg.getD normalBg)
  for (name, fgKey, bgKey) in ordered do
    let r := read s.theme context [] es name
    let (names, said) := reach s.theme context es name { fg := !fgKey.isEmpty, bg := !bgKey.isEmpty }
    let names := startColors.foldl (fun acc start => acc ++ (reach s.theme context es start
      { fg := said.contains (start ++ ".fg"), bg := said.contains (start ++ ".bg") }).1) names
    s := { s with reached := s.reached ++ names }
    -- A site is repainted only when a declaration reaches it: a declared
    -- parent its element overrides on every channel leaves it as it was.
    if names.any fun n => es.any fun e => e.name == n && e.declared then
      issues := issues ++ r.issues
      for (key, value) in [(fgKey, r.fg), (bgKey, r.bg)] do
        unless key.isEmpty do
          let origin := value.bind (·.origin)
          let value := value.bind (·.color)
          -- An empty Beamer heading inherits normal text. Erasing its
          -- native key would instead choose the title bar's inverse ink.
          let value := if key == "frametitlefg" then value.or (some normalFg) else value
          unless s.painted.contains key do
            s := { s with opening := s.opening.restore base key,
                          painted := s.painted.push key }
          s := { s with origins := s.origins.filter (·.1 != key) }
          if let (some c, some span) := (value, origin) then
            s := { s with origins := s.origins.push (key, c, span) }
          out := match value with
            | some c => out.declare key c
            | none => out.erase key
  return (s, out, issues)

end LeanTex.Core.BeamerColor
