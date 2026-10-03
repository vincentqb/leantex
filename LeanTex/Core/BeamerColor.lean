import LeanTex.Core.Ir

namespace LeanTex.Core.BeamerColor

open Ir

/-- A space cannot occur in an author's control word. The two original
groups follow this internal marker; no author text is encoded into it. -/
def marker : String := " beamer color"
def starMarker : String := " beamer color*"

/-- Beamer's named elements with genuine native paint sites. In particular,
the head/foot progress placement is absent: a section rule is not that site.
Sources: beamercolorthemedefault.sty and beamercolorthememoloch.sty. -/
def roles : List (String × String × String) :=
  [("normal text", "fg", "bg"), ("background canvas", "", "bg"),
   ("frametitle", "frametitlefg", "frametitlebg"),
   ("headline", "frametitlefg", "frametitlebg"),
   ("framesubtitle", "framesubtitlefg", ""),
   ("section title", "sectiontitlefg", ""),
   ("block title", "blocktitlefg", "blocktitlebg"),
   ("block title alerted", "alerttitlefg", "alerttitlebg"),
   ("block title example", "exampletitlefg", "exampletitlebg"),
   ("alerted text", "alert", ""), ("example text", "example", ""),
   ("standout", "standoutfg", "standoutbg"),
   ("progress bar", "progressfg", "progressbg"),
   ("progress bar in section page", "sectionprogressfg", "sectionprogressbg"),
   ("title separator", "separator", ""),
   ("footline", "muted", "footlinebg"),
   ("page number in head/foot", "muted", "")]

/-- These defaults are relationships, not copied theme colours. Moloch's
colour theme declares the progress variants with `parent`; Beamer's default
colour theme makes the frame subtitle inherit the frame title. -/
private def defaultParents : String → List String
  | "framesubtitle" => ["frametitle"]
  | "section title" => ["titlelike"]
  | "titlelike" => ["normal text"]
  | "progress bar in section page" | "title separator" => ["progress bar"]
  | _ => []

inductive Value where
  | source (text : String)
  | native (color : Color)
  deriving Inhabited

structure Element where
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

private def Element.site (e : Element) (key : String) : Span :=
  (e.sites.lookup key).getD e.span

structure Issue where
  message : String
  span : Span

/-- Flow palette and named declarations share one elaborator state field.
`opening` remembers the native values displaced by resolution, so a later
parent update never inherits its own previously resolved result. -/
structure State where
  current : Option Palette := none
  elements : List Element := []
  opening : Palette := {}
  painted : Array String := #[]
  reached : List String := []
  deriving Inhabited

private def unbrace (s : String) : String :=
  let s := s.trimAscii.toString
  if s.startsWith "{" && s.endsWith "}" then
    ((s.drop 1).dropEnd 1).toString.trimAscii.toString
  else s

private def names (s : String) : List String :=
  ((unbrace s).splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- Update only the keys that occur, except that the starred form first
clears both channels and both relationships (beamerbasecolor.sty). -/
def State.declare (s : State) (name : String) (star : Bool) (src : String)
    (span : Span) : State × List String := Id.run do
  let mut e := if star then { name := name, reset := true, span := span }
    else { ((s.elements.find? (·.name == name)).getD { name := name }) with
      span := span, declared := true }
  let mut unsupported := []
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
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
def State.native (s : State) (key : String) (color : Color) : State := Id.run do
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

private structure Reading where
  /-- `none` leaves an earlier parent alone; `some none` explicitly clears
  it. Beamer's empty `fg={}` / `bg={}` definitions still run. -/
  fg : Option (Option Color) := none
  bg : Option (Option Color) := none
  reached : List String := []
  issues : List Issue := []
  changed : Bool := false

private def Reading.over (a b : Reading) : Reading :=
  { fg := b.fg.or a.fg, bg := b.bg.or a.bg,
    reached := a.reached ++ b.reached, issues := a.issues ++ b.issues,
    changed := a.changed || b.changed }

private def own (pal : Palette) (name : String) : Reading :=
  match roles.lookup name with
  | some (fg, bg) => { fg := (pal.find? fg).map some, bg := (pal.find? bg).map some }
  | none => if name == "structure" then { fg := (pal.find? "fg").map some } else {}

/-- DFS removes the current element before descending. A path detects a
cycle, and the shrinking declaration list proves termination without fuel.
Only colour declarations are visited, never document content. -/
private def read (pal : Palette) (path : List (String × Option Span)) (es : List Element)
    (name : String) : Reading := Id.run do
  if let some (_, span) := path.find? (·.1 == name) then
    -- Default edges have no authored site. Choose an explicit edge inside
    -- this cycle, never an unrelated channel or the path that entered it.
    let span := span.orElse fun _ =>
      (path.takeWhile (·.1 != name)).findSome? (·.2)
    return { issues := [⟨s!"colour inheritance cycle at '{name}'", span.getD ⟨"", {}⟩⟩] }
  let i := es.findIdx (·.name == name)
  if h : i < es.length then
    let e := es[i]
    let rest := es.eraseIdx i
    let mut r : Reading := { changed := e.declared, reached := [name] }
    let mut aliases := pal
    -- beamer@thc@docolor runs `use` before `parent`. Empty used channels
    -- bind the current foreground/background, rather than no alias.
    for used in e.uses do
      let u := read aliases ((name, e.sites.lookup "use") :: path) rest used
      let current := Design.ofPalette aliases
      aliases := aliases.declare (used ++ ".fg") (u.fg.join.getD current.fg)
      aliases := aliases.declare (used ++ ".bg") (u.bg.join.getD current.bg)
      r := { r with reached := r.reached ++ u.reached,
                    issues := r.issues ++ u.issues }
    for parent in e.parents.getD (if e.reset then [] else defaultParents name) do
      r := r.over (read aliases ((name, e.sites.lookup "parent") :: path) rest parent)
    let defaults := if e.reset then ({} : Reading) else own pal name
    let channel (key : String) (v : Option Value) (fallback : Option (Option Color)) :
        Option (Option Color) × List Issue :=
      match v with
      | none => (fallback, [])
      | some (.native c) => (some (some c), [])
      | some (.source "") => (some none, [])
      | some (.source src) =>
        match aliases.resolveSource none src with
        | .ok (some c) => (some (some c), [])
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

/-- Resolve the finite set of engine sites against the declarations in force.
Later explicit aliases of one native site win. `use` makes temporary xcolor
aliases available to expressions, but contributes no inherited channel.
Missing parents contribute nothing, as in Beamer. -/
def State.resolve (s : State) (pal : Palette) : State × Palette × List Issue := Id.run do
  let base := s.painted.foldl (fun p key => p.restore s.opening key) pal
  let mut s := s
  let mut out := base
  let mut issues := []
  let allNames := (roles.map (·.1)) ++ ["structure", "titlelike"] ++
    s.elements.flatMap (fun e => e.parents.getD [] ++ e.uses)
  let es := allNames.foldl (fun es name =>
    if es.any (·.name == name) then es
    else es ++ [{ name := name, declared := false }]) s.elements
  -- Frame furniture starts from normal text. Resolve that context before
  -- the sites, even when normal text was declared after a child.
  let normal := read base [] es "normal text"
  let context := [("fg", normal.fg), ("bg", normal.bg)].foldl (fun p (key, value) =>
    match value with
    | none => p
    | some none => p.erase key
    | some (some c) => p.declare key c) base
  let normalFg := (Design.ofPalette context).fg
  let rank (name : String) : Nat :=
    let i := s.elements.findIdx (·.name == name)
    if i < s.elements.length then i + 1 else 0
  let ordered := roles.mergeSort fun a b => rank a.1 ≤ rank b.1
  for (name, fgKey, bgKey) in ordered do
    let r := read context [] es name
    if r.changed then
      s := { s with reached := s.reached ++ r.reached }
      issues := issues ++ r.issues
      for (key, value) in [(fgKey, r.fg), (bgKey, r.bg)] do
        unless key.isEmpty do
          -- An empty Beamer heading inherits normal text. Erasing its
          -- native key would instead choose the title bar's inverse ink.
          let value := if key == "frametitlefg" then value.join.or (some normalFg)
            else value.join
          unless s.painted.contains key do
            s := { s with opening := s.opening.restore base key,
                          painted := s.painted.push key }
          out := match value with
            | some c => out.declare key c
            | none => out.erase key
  return (s, out, issues)

end LeanTex.Core.BeamerColor
