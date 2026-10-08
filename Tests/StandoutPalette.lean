import Tests.Support

open LeanTex.Core

namespace Tests.StandoutPalette

private def patch (body : String) (success : String := "") : String :=
  "\\apptocmd{\\KV@beamerframe@standout}{" ++ body ++
    "}{" ++ success ++ "}{\\PackageError{probe}{Dormant failure callback}{}}"

private def aliasPatch : String := patch "\\colorlet{ProbeMuted}{ProbeOnDark}"

private def source (theme hook : String) : String :=
  "\\documentclass{beamer}" ++ theme ++
    "\\definecolor{ProbeMuted}{HTML}{596674}" ++
    "\\definecolor{ProbeOnDark}{HTML}{A7B7C6}" ++
    "\\palette{fg=#203044,bg=#F8F4ED,standoutfg=#F8F4ED,standoutbg=#203044}" ++
    "\\setbeamercolor{alerted text}{fg=ProbeMuted}" ++ hook ++
    "\\begin{document}" ++
    "\\begin{frame}\\textcolor{ProbeMuted}{BEFORE}\\end{frame}" ++
    "\\begin{frame}[standout]\\textcolor{ProbeMuted}{DARK}\\par\\alert{ALERT}\\end{frame}" ++
    "\\begin{frame}\\textcolor{ProbeMuted}{AFTER}\\par\\alert{RESTORED}\\end{frame}" ++
    "\\palette{ProbeOnDark=#BAC5CE}" ++
    "\\begin{frame}[standout]\\textcolor{ProbeMuted}{LATE}\\end{frame}" ++
    "\\end{document}"

private def shippedColor (out : Layout.Out) (word : String) (color : Ir.Color) : Bool :=
  let lines := out.pages.flatMap (·.lines) |>.filter fun line =>
    !line.furniture && (lineText line false).trimAscii.toString == word
  lines.size == 1 && lines.all fun line =>
    let inks := line.segs.filterMap fun
      | .run _ c _ w glyphs .. => if w > 0 && !glyphs.isEmpty then some c else none
      | _ => none
    !inks.isEmpty && inks.all (· == color)

private def declarations (style : String) : List (String × String) :=
  (style.splitOn ";").filterMap fun decl =>
    match decl.splitOn ":" with
    | [key, value] => some (key.trimAscii.toString, value.trimAscii.toString)
    | _ => none

private def variables (old : List (String × String)) (style : String) :
    List (String × String) :=
  (declarations style).foldl (fun vars (key, value) =>
    if key.startsWith "--" then (key, value) :: vars else vars) old

private def rootVariables (head : Array Html.Node) : List (String × String) :=
  head.foldl (fun vars node => match node with
    | .style css => ((css.splitOn ":root {").drop 1).foldl
        (fun vars block => variables vars ((block.splitOn "}").head!)) vars
    | _ => vars) []

private def cssColor (vars : List (String × String)) (value : String) : String :=
  if value.startsWith "var(" && value.endsWith ")" then
    match (((value.drop 4).dropEnd 1).toString.splitOn ",") with
    | [key, fallback] => (vars.lookup key.trimAscii.toString).getD fallback.trimAscii.toString
    | _ => value
  else value

mutual
  private def htmlPaint (vars : List (String × String)) (color : String)
      (out : Array (String × String)) : Html.Node → Array (String × String)
    | .text text => out.push (text.trimAscii.toString, color)
    | .elem _ attrs kids =>
      let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
      let vars := variables vars style
      let color := (declarations style).foldl (fun color (key, value) =>
        if key == "color" then cssColor vars value else color) color
      htmlPaintList vars color out kids.toList
    | .style _ | .script .. => out
  private def htmlPaintList (vars : List (String × String)) (color : String)
      (out : Array (String × String)) : List Html.Node → Array (String × String)
    | [] => out
    | node :: rest => htmlPaintList vars color (htmlPaint vars color out node) rest
end

private def typedColor (paint : Array (String × String)) (word : String)
    (color : Ir.Color) : Bool :=
  let hits := paint.filter (·.1 == word)
  hits.size == 1 && hits.all (·.2 == color.css)

private def artifactPair (fonts : Font.FontSet) (doc : Ir.Doc) : String × String :=
  let (head, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
  (reprStr (layoutOf fonts doc).pages, Html.document "en" head nodes)

/-- An appended colour alias is evaluated at each standout frame's opening
palette, reaches both direct text and named Beamer colours, and leaves the
following ordinary frame's aliases alone. These are shipped glyph and typed
HTML paint assertions, not elaboration snapshots. -/
def standoutPaletteChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let muted : Ir.Color := { r := 0x59, g := 0x66, b := 0x74 }
  let onDark : Ir.Color := { r := 0xA7, g := 0xB7, b := 0xC6 }
  let later : Ir.Color := { r := 0xBA, g := 0xC5, b := 0xCE }
  let ground : Ir.Color := { r := 0x20, g := 0x30, b := 0x44 }
  for (name, theme, hook) in [
      ("direct", "\\usetheme{moloch}", aliasPatch),
      ("conditional", "\\usetheme{moloch}",
        "\\ifdefined\\KV@beamerframe@standout " ++ aliasPatch ++ "\\fi"),
      ("inherited", "\\RequirePackage{beamerthememetropolis}",
        "\\ifdefined\\KV@beamerframe@standout " ++ aliasPatch ++ "\\fi"),
      ("inner", "\\theme{plain}\\RequirePackage{beamerinnerthememoloch}", aliasPatch),
      ("sequential", "\\usetheme{moloch}",
        patch "\\colorlet{ProbeRelay}{ProbeOnDark}\\colorlet{ProbeMuted}{ProbeRelay}")] do
    let (doc, ds) := Elab.run "standout-palette.tex" (source theme hook)
    check ref s!"standout palette/{name}: accepted hook has no errors"
      (ds.all (·.severity != .error))
    let out := layoutOf fonts doc
    let (head, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
    let paint := htmlPaintList (rootVariables head) "" #[] nodes.toList
    check ref s!"standout palette/{name}: four shipped frames" (out.pages.size == 4)
    for (word, expected) in [
        ("BEFORE", muted), ("DARK", onDark), ("ALERT", onDark),
        ("AFTER", muted), ("RESTORED", muted), ("LATE", later)] do
      check ref s!"standout palette/{name}: PDF {word}" (shippedColor out word expected)
      check ref s!"standout palette/{name}: HTML {word}" (typedColor paint word expected)
    for i in [1, 3] do
      check ref s!"standout palette/{name}: dark frame {i} keeps its declared ground"
        ((out.pages[i]?.map fun page => page.fills.any (·.color == ground)).getD false)

  let theme := "\\usetheme{moloch}"
  let conditional := "\\ifdefined\\KV@beamerframe@standout " ++ aliasPatch ++ "\\fi"
  for (name, withTheme, withoutHook) in [
      ("absent", "", ""),
      ("later loaded", conditional ++ theme, theme)] do
    let hook := if withTheme.isEmpty then conditional else ""
    let (doc, ds) := Elab.run "standout-palette.tex" (source withTheme hook)
    let (plain, _) := Elab.run "standout-palette.tex" (source withoutHook "")
    check ref s!"standout palette/{name}: undefined hook is skipped without errors"
      (ds.all (·.severity != .error))
    check ref s!"standout palette/{name}: skipped hook changes neither artifact"
      (artifactPair fonts doc == artifactPair fonts plain)

  let plainSource := source theme ""
  let (plain, _) := Elab.run "standout-palette.tex" plainSource
  let unchanged := artifactPair fonts plain
  for (name, input) in [
      ("patch body", source theme (patch "\\colorlet{ProbeMuted}{ProbeOnDark}LEAK")),
      ("success callback", source theme (patch "\\colorlet{ProbeMuted}{ProbeOnDark}" "LEAK")),
      ("target", source theme (aliasPatch.replace "KV@beamerframe@standout" "UnknownOption")),
      ("body", plainSource.replace "\\begin{document}" ("\\begin{document}" ++ aliasPatch))] do
    let (doc, ds) := Elab.run "standout-palette.tex" input
    check ref s!"standout palette/{name}: unsupported patch is refused once"
      ((ds.filter (·.severity == .error)).map (·.code) == #["E0111"])
    check ref s!"standout palette/{name}: patch and callbacks add no paint or ink"
      (artifactPair fonts doc == unchanged)

  -- A bare preamble group already has E0313. A scoped patch must add its
  -- own refusal once without changing that baseline or installing aliases.
  let (groupPlain, groupPlainDs) := Elab.run "standout-palette.tex" (source theme "{}")
  let (grouped, groupedDs) := Elab.run "standout-palette.tex"
    (source theme ("{" ++ aliasPatch ++ "}"))
  check ref "standout palette/group: refusal preserves the existing group error"
    ((groupedDs.filter (·.code == "E0111")).size == 1 &&
      (groupedDs.filter (fun d => d.severity == .error && d.code != "E0111")).map (·.code) ==
        (groupPlainDs.filter (·.severity == .error)).map (·.code))
  check ref "standout palette/group: scoped patch changes neither artifact"
    (artifactPair fonts grouped == artifactPair fonts groupPlain)

  -- The acceptance condition must change paint, not merely diagnostics.
  let (accepted, _) := Elab.run "standout-palette.tex" (source theme aliasPatch)
  let changed := artifactPair fonts accepted
  check ref "standout palette: accepted hook changes both artifacts"
    (changed.1 != unchanged.1 && changed.2 != unchanged.2)

  -- Alias groups are single operands, even when they contain the native
  -- declaration separator. They cannot inject a second palette entry.
  let (malformed, malformedDs) := Elab.run "standout-palette.tex"
    (source theme (patch "\\colorlet{ProbeMuted,fg}{ProbeOnDark}"))
  check ref "standout palette: malformed alias name uses the shared declaration error"
    (malformedDs.any (·.code == "E0320"))
  let out := layoutOf fonts malformed
  let (head, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } malformed
  let paint := htmlPaintList (rootVariables head) "" #[] nodes.toList
  check ref "standout palette: malformed alias cannot change either muted paint site"
    (shippedColor out "DARK" muted && shippedColor out "ALERT" muted &&
      typedColor paint "DARK" muted && typedColor paint "ALERT" muted)

end Tests.StandoutPalette
