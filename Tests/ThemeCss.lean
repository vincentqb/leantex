import LeanTex.Core.HtmlDoc
import LeanTex.Core.Theme
import Tests.Support

open LeanTex.Core

namespace Tests.ThemeCss

private def property (styles key : String) : Option String :=
  (styles.splitOn ";").foldl (fun old decl =>
    match decl.splitOn ":" with
    | [k, v] => if k.trimAscii.toString == key then some v.trimAscii.toString else old
    | _ => old) none

/-- Read only the emitted nested `var(--key, fallback)` colour grammar.
Reconstruction rejects anything outside that grammar instead of silently
normalizing it. Variables in these probes are concrete palette colours;
browser computed-style checks independently witness the cascade. -/
private def colorValue (vars : Ir.Palette) (value : String) : Option Ir.Color := do
  let choices := ((value.replace "var(" "").replace ")" "").splitOn ","
    |>.map (·.trimAscii.toString)
  let last ← choices.getLast?
  let keys := choices.dropLast
  let tail := if last.startsWith "--" then s!"var({last})" else last
  let rebuilt := keys.foldr (fun key rest => s!"var({key}, {rest})") tail
  if rebuilt != value || !keys.all (·.startsWith "--") then none else
    choices.findSome? fun key =>
      if key.startsWith "--" then vars.find? (key.drop 2).toString
      else if key.startsWith "#" then
        (({} : Ir.Palette).resolveSource none key).toOption.join
      else none

private def ruleColor (css selector key : String) (vars : Ir.Palette) :
    Option Ir.Color :=
  (property (String.intercalate ";" (cssRulesOf css selector)) key).bind
    (colorValue vars)

private def probe (pal : Ir.Palette) : Ir.Doc :=
  { docClass := .slides, palette := pal
    body := #[
      .frame #[] true .center false #[.para #[.text "STANDOUT"]],
      .frame #[] false .golden false #[.para #[.text "TITLE"]],
      .frame #[.text "HEADER"] false .top false #[.para #[.text "BODY"]]] }

private def sheet (cfg : HtmlDoc.Config) (doc : Ir.Doc) : String :=
  let (head, _, _) := HtmlDoc.emitTree cfg doc
  treeCssList "" head.toList

/-- Artifact invariant: native furniture fallbacks project `Design` even
when a palette omits a channel. Removing a flow ground preserves absence
when no native surface exists; declared CSS tokens and author rules retain
their priority. This reads the CSS and elements actually shipped. -/
public def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let dark : Ir.Color := { r := 21, g := 38, b := 55 }
  let pale : Ir.Color := { r := 231, g := 238, b := 245 }
  let empty : Ir.Palette := {}
  t "theme CSS reader rejects unsupported colour expressions"
    (colorValue empty "invalid(#ffffff)" == none &&
      colorValue empty "var(--missing)" == none &&
      colorValue empty "#fff" == some Ir.Color.white &&
      colorValue empty "var(--missing, #ffffff)" == some Ir.Color.white)
  let sparse := [
    ("bare", empty),
    ("ink-only", empty.declare "fg" dark),
    ("ground-only", empty.declare "bg" pale),
    ("pair", (empty.declare "fg" dark).declare "bg" pale)]
  let palettes := sparse ++ Theme.builtin.map fun theme => (theme.name, theme.palette)
  for (name, pal) in palettes do
    let doc := probe pal
    let css := sheet {} doc
    let d := Ir.Design.ofPalette pal
    for (key, expected) in [("background", d.standout.bg), ("color", d.standout.fg)] do
      t s!"theme CSS/{name}: standout {key} projects Design"
        (ruleColor css "section.slide.standout" key pal == some expected)
    -- Add only the activating ground: the absent ink must inherit by the
    -- same inversion the shared design declares.
    let pal := (pal.declare "frametitlebg" dark).declare "titlepagebg" dark
    let css := sheet {} (probe pal)
    let d := Ir.Design.ofPalette pal
    t s!"theme CSS/{name}: title page ink projects Design"
      (ruleColor css "section.slide.title-page" "color" pal == d.titlepage.map (·.fg))
    t s!"theme CSS/{name}: title bar ink projects Design"
      (ruleColor css "section.slide > header" "color" pal == d.frametitle.map (·.fg))
    t s!"theme CSS/{name}: palette tokens override fallback ink"
      (ruleColor css "section.slide.standout" "color"
        (pal.declare "standoutfg" pale) == some pale)
    t s!"theme CSS/{name}: palette tokens override fallback ground"
      (ruleColor css "section.slide.standout" "background"
        (pal.declare "standoutbg" dark) == some dark)
  let opening := empty.declare "bg" pale
  let reset : Ir.Doc := { palette := opening, body := #[
    .setPalette empty, .para #[.text "RESET"]] }
  for mode in [HtmlDoc.CssMode.own, .none, .bulma] do
    let (_, body, _) := HtmlDoc.emitTree { css := mode } reset
    let styles := elemStylesList #[] body.toList
    let paints := styles.filterMap fun (_, style) =>
      (property style "background").map fun bg => (style, bg)
    t "theme CSS: removing a flow ground reaches a painted sibling"
      (!paints.isEmpty && paints.all fun (style, _) =>
        property style "--bg" == some "initial")
    let vars := if mode == .own then empty.declare "surface" Contrast.light.surface else empty
    let expected := if mode == .own then some Contrast.light.surface else none
    t "theme CSS: removed ground has only the declared native surface"
      (paints.all fun (_, bg) => colorValue vars bg == expected)
  let doc := probe empty
  t "theme CSS: an undeclared title ground stays unfilled"
    ((cssRulesOf (sheet {} doc) "section.slide.title-page").all fun rule =>
      (property rule "background").isNone)
  let author := "section.slide.standout { background: #123456; color: #abcdef; }\n"
  let doc := { doc with output := { doc.output with stylesheet := some "author.css" } }
  let (head, _, _) := HtmlDoc.emitTree { stylesheet := some ("author.css", author) } doc
  t "theme CSS: the author's rule remains last"
    (treeCssList "" head.toList |>.endsWith author)
  let bulma := sheet { css := .bulma } (probe empty)
  t "theme CSS: Bulma's default accent is the native contrast palette"
    (ruleColor bulma ":root" "--bulma-primary" empty == some Contrast.light.accent)

end Tests.ThemeCss
