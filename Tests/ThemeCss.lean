module

public import LeanTex.Core.HtmlDoc
public import LeanTex.Core.Theme
public import Tests.Support

public section

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

/-- A palette declared inside a structural scope still belongs to the frame
it precedes. These authored scopes take different generic emitter paths;
the nested scope also carries the epoch through another element. -/
private def wrappedEpochSources : List (String × String) :=
  [("conditional", "\\begin{ifbackend}{html,pdf}\n", "\\end{ifbackend}\n"),
   ("centered", "\\begin{center}\n", "\\end{center}\n"),
   ("ragged", "\\begin{flushleft}\n", "\\end{flushleft}\n"),
   ("nested", "\\begin{ifbackend}{html,pdf}\n\\begin{flushleft}\n",
     "\\end{flushleft}\n\\end{ifbackend}\n")].flatMap fun (scope, start, stop) =>
    [false, true].flatMap fun background =>
      ["plain", "standout", "title"].map fun kind =>
        let name := scope ++ "-" ++
          (if background then "background" else "foreground") ++ "-" ++ kind
        let frame := if kind == "title" then "\\maketitle\n"
          else "\\begin{frame}" ++ (if kind == "standout" then "[standout]" else "") ++
            "\nEPOCH\n\\end{frame}\n"
        (name, "\\documentclass{slides}\n" ++
          "\\palette{fg=#203040,bg=#F0F4F8,alert=#203040,example=#203040," ++
          "titlepagebg=#203040,titlepagefg=#F0F4F8}\n\\title{EPOCH}\n" ++
          "\\begin{document}\n\\begin{frame}BEFORE\\end{frame}\n" ++ start ++
          (if background then "\\palette{bg=#E0E8F0}\n" else "\\palette{fg=#503010}\n") ++
          frame ++ stop ++ "\\end{document}\n")

/-- Authored palette epochs before each kind of frame. The first frame
remains in the opening palette; the second carries the changed palette.
A separate revealed paragraph (the subtitle on a title page) exercises
the stepped path without changing the marked text's own ink. Structural
scopes must preserve the same paint ownership as the direct path. -/
public def epochSources : List (String × String) :=
  let direct := ("" :: Theme.builtin.map (·.name)).flatMap fun theme =>
    [false, true].flatMap fun background =>
      ["plain", "standout", "title"].flatMap fun kind =>
        [false, true].map fun stepped =>
          let name := (if theme.isEmpty then "bare" else theme) ++ "-" ++
            (if background then "background" else "foreground") ++ "-" ++ kind ++
            (if stepped then "-steps" else "")
          let content := "EPOCH" ++
            (if stepped then "\n\n\\uncover<2>{LATER}" else "")
          let frame := if kind == "title" then "\\maketitle\n"
            else "\\begin{frame}" ++ (if kind == "standout" then "[standout]" else "") ++
              "\n" ++ content ++ "\n\\end{frame}\n"
          let source := "\\documentclass{slides}\n" ++
            (if theme.isEmpty then "" else "\\theme{" ++ theme ++ "}\n") ++
            "\\palette{fg=#203040,bg=#F0F4F8,alert=#203040,example=#203040," ++
            "titlepagebg=#203040,titlepagefg=#F0F4F8}\n\\title{EPOCH}\n" ++
            (if kind == "title" && stepped then "\\subtitle{\\uncover<2>{LATER}}\n" else "") ++
            "\\begin{document}\n" ++
            "\\begin{frame}BEFORE\\end{frame}\n" ++
            (if background then "\\palette{bg=#E0E8F0}\n" else "\\palette{fg=#503010}\n") ++
            frame ++ "\\end{document}\n"
          (name, source)
  direct ++ wrappedEpochSources

private def variables (inherited : Ir.Palette) (style : String) : Ir.Palette :=
  (style.splitOn ";").foldl (fun vars decl =>
    match decl.splitOn ":" with
    | [key, value] =>
      let key := key.trimAscii.toString
      let value := value.trimAscii.toString
      if !key.startsWith "--" then vars else
        let name := (key.drop 2).toString
        if value == "initial" then
          { vars with entries := vars.entries.filter (·.1 != name) }
        else match colorValue vars value with
          | some color => vars.declare name color
          | none => vars
    | _ => vars) inherited

private structure StagePaint where
  before : Bool
  ground : Option Ir.Color
  ink : Option Ir.Color
  deriving BEq

-- This small cascade reader handles the stage selectors the emitter ships:
-- the shared stage rule, the more specific frame kind, then inline paint.
-- Variables inherit through a slide track, but its computed color does not
-- override a declaration on the child stage. Chromium independently checks
-- the same authored artifacts in screen and print media.
mutual
  private def stagePaints (css : String) (vars : Ir.Palette) (acc : Array StagePaint) :
      List Html.Node → Array StagePaint
    | [] => acc
    | node :: rest => stagePaints css vars (stagePaint css vars acc node) rest
  private def stagePaint (css : String) (vars : Ir.Palette) (acc : Array StagePaint) :
      Html.Node → Array StagePaint
    | .elem tag attrs kids =>
      let cls := (attrs.find? (·.1 == "class")).map (·.2) |>.getD ""
      let inline := (attrs.find? (·.1 == "style")).map (·.2) |>.getD ""
      let isStage := tag == "section" && (cls.splitOn " ").contains "slide"
      let rules := if isStage then
          String.intercalate ";" (cssRulesOf css "section.slide, section.section-page") ++
          ";" ++ String.intercalate ";" (cssRulesOf css
            (if (cls.splitOn " ").contains "standout" then "section.slide.standout"
             else if (cls.splitOn " ").contains "title-page" then "section.slide.title-page"
             else "section.slide"))
        else ""
      let style := rules ++ ";" ++ inline
      let vars := variables vars style
      let acc := if isStage then
          acc.push { before := treeOccurs kids "BEFORE" > 0
                     ground := (property style "background").bind (colorValue vars)
                     ink := (property style "color").bind (colorValue vars) }
        else acc
      stagePaints css vars acc kids.toList
    | .text _ | .style _ | .script .. => acc
end

/-- Read the full-page fill and actual glyph ink of the marked frame from
native output. Every revealed page must agree; an absent fill stays absent. -/
public def epochNativePaint (out : Layout.Out) (doc : Ir.Doc) (marker : String) :
    Option (Option Ir.Color × Ir.Color) := do
  let geom := Layout.Geom.ofPage doc.page
  let pages := out.pages.filter fun page =>
    page.lines.any fun line => (lineText line false).startsWith marker
  if pages.isEmpty then none else
    let paints ← pages.toList.mapM fun page => do
      let lines := page.lines.filter fun line => (lineText line false).startsWith marker
      let inks := lines.flatMap fun line => line.segs.filterMap fun
        | .run _ color _ width glyphs .. =>
          if width > 0 && !glyphs.isEmpty then some color else none
        | _ => none
      let ink ← inks[0]?
      if !inks.all (· == ink) then none else
        let fills := page.fills.filter fun fill =>
          fill.x == 0 && fill.y == 0 && fill.w == geom.pageW && fill.h == geom.pageH
        some ((fills[0]?).map (·.color), ink)
    let paint ← paints.head?
    if paints.all (· == paint) then some paint else none

/-- A body palette declaration must reach the frame's own paint resolver.
Ordinary page paint must not override a standout/title surface, irrespective
of whether the stage stands alone, inside an overlay track, or within
structural scopes. Compare the
typed artifact's effective stage paint with shipped native page/glyph paint,
and retain the author's later rules at the same selectors. -/
public def epochChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for (name, source) in epochSources do
    let (doc, ds) := Elab.run "theme-epoch.tex" source
    let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
    let (head, body, hd) := HtmlDoc.emitTree {} doc
    let css := treeCssList "" head.toList
    let root := variables {} (String.intercalate ";" (cssRulesOf css ":root"))
    let stages := stagePaints css root #[] body.toList
    check ref s!"theme epoch/{name}: clean authored source"
      (ds.all (·.severity == .note) && hd.all (·.severity == .note) &&
        out.diags.all (·.severity == .note))
    check ref s!"theme epoch/{name}: native overlay extent"
      (out.pages.size == if name.endsWith "-steps" then 3 else 2)
    for (before, marker) in [(true, "BEFORE"), (false, "EPOCH")] do
      let native := epochNativePaint out doc marker
      let actual := stages.filter (·.before == before)
      check ref s!"theme epoch/{name}: {marker} stage paint agrees with native output"
        (actual.size == 1 && native.isSome && actual.all fun stage =>
          some stage.ground == native.map (·.1) && stage.ink == native.map (·.2))
    let author := "section.slide.standout { background: #123456; color: #abcdef; }\n"
    let doc := { doc with output := { doc.output with stylesheet := some "author.css" } }
    let (head, body, _) :=
      HtmlDoc.emitTree { stylesheet := some ("author.css", author) } doc
    let css := treeCssList "" head.toList
    if (name.splitOn "-").contains "standout" then
      let stages := stagePaints css root #[] body.toList |>.filter (!·.before)
      check ref s!"theme epoch/{name}: author stage paint retains priority"
        (stages.size == 1 && stages.all fun stage =>
          stage.ground == colorValue {} "#123456" && stage.ink == colorValue {} "#abcdef")

end Tests.ThemeCss
