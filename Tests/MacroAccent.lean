module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- An accent consumes its operand without visiting that raw again. The
composed text keeps the operand's semantic ancestry beneath the accent's
owners, each invocation once. Native definitions declare the expected tree;
the whole serialized typed HTML is compared, without dropping attributes,
roles or whitespace. The shared glyph comparison ignores only run/leaf
allocation, retaining placement, faces, paint, links and leading. -/
def macroAccentChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Styled controls need distinct faces even when the caller uses oneFace.
  let some styleFonts ← serifFacesSet | t "macro accent: serif faces load" false
  let native := "\\define\\wordprobe(a: content){\\a}" ++
    "\\define\\accentprobe(a: content){\\a}\\define\\outerprobe(a: content){\\a}"
  let word := "\\newcommand\\wordprobe[1]{#1}"
  let consumer := "\\newcommand\\accentprobe[1]{\\'}"
  for (label, pre, call, expected, text) in #[
      ("ungrouped operand", word,
        "\\'\\wordprobe{e}", "\\wordprobe{é}", "é"),
      ("grouped replacement", "\\newcommand\\wordprobe[1]{{#1}}",
        "\\'\\wordprobe{e}", "\\wordprobe{é}", "é"),
      ("source group", word,
        "\\'{\\wordprobe{e}}", "\\wordprobe{é}", "é"),
      ("dotless operand", "\\newcommand\\wordprobe[1]{\\i}",
        "\\'\\wordprobe{unused}", "\\wordprobe{í}", "í"),
      ("distinct consumer", consumer ++ word,
        "\\accentprobe{unused}\\wordprobe{e}", "\\accentprobe{\\wordprobe{é}}", "é"),
      ("distinct consumer grouped", consumer ++ "\\newcommand\\wordprobe[1]{{#1}}",
        "\\accentprobe{unused}\\wordprobe{e}", "\\accentprobe{\\wordprobe{é}}", "é"),
      ("same owner", "\\newcommand\\accentprobe[1]{\\'#1}",
        "\\accentprobe{e}", "\\accentprobe{é}", "é"),
      ("nested operand", word ++ "\\newcommand\\outerprobe[1]{\\'\\wordprobe{#1}}",
        "\\outerprobe{e}", "\\outerprobe{\\wordprobe{é}}", "é"),
      ("distinct invocations same spelling", word,
        "\\wordprobe{\\'}\\wordprobe{e}", "\\wordprobe{\\wordprobe{é}}", "é"),
      ("operand continuation", "\\newcommand\\wordprobe[1]{#1 X}",
        "\\'\\wordprobe{e}", "\\wordprobe{é X}", "é X"),
      ("word remainder", word,
        "\\'\\wordprobe{er}", "\\wordprobe{ér}", "ér"),
      ("plain accent", "",
        "\\'e", "é", "é")] do
    for suffix in ["/Z", " Z"] do
      for (style, opening, closing) in #[
          ("plain", "", ""),
          ("bold", "\\textbf{", "}"),
          ("painted", "\\textcolor{blue}{", "}")] do
        let fonts := if style == "plain" then fonts else styleFonts
        let source := dvDoc ("\\pagestyle{empty}" ++ pre)
          ("A" ++ opening ++ call ++ closing ++ suffix)
        let control := dvDoc ("\\pagestyle{empty}" ++ native)
          ("A" ++ opening ++ expected ++ closing ++ suffix)
        let (ds, out, html, shown) := sourceArtifacts fonts source
        let (cds, cout, chtml, cshown) := sourceArtifacts fonts control
        let name := s!"macro accent {label}, {repr suffix}, {style}"
        t (name ++ ": no source loss") (ds.all (·.severity == .note))
        t (name ++ ": no control loss") (cds.all (·.severity == .note))
        t (name ++ ": exact typed HTML") (html == chtml)
        t (name ++ ": exact visible whitespace")
          (shown == "A" ++ text ++ suffix && shown == cshown)
        t (name ++ ": exact shipped glyphs") (shippedBodyGlyphs out == shippedBodyGlyphs cout)
        t (name ++ ": exact line boundaries")
          ((bodyLines out).map (fun l => (l.x, l.y, l.setWidth, l.expand, lineText l)) ==
            (bodyLines cout).map (fun l => (l.x, l.y, l.setWidth, l.expand, lineText l)))
        let (_, bare, bareHtml, _) := sourceArtifacts fonts
          (dvDoc "\\pagestyle{empty}" ("A" ++ text ++ suffix))
        if label != "plain accent" then
          t (name ++ ": role difference remains observable") (chtml != bareHtml)
        if style != "plain" then
          t (name ++ ": authored style remains observable")
            (shippedBodyGlyphs cout != shippedBodyGlyphs bare)

end Tests
