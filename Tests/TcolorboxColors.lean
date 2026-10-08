module

public import Tests.Support
public import LeanTex.Core.Tcolorbox

public section

open LeanTex.Core

namespace TcolorboxColors

private def document (pre body : String) : String :=
  "\\documentclass{beamer}\\theme{default}" ++ pre ++
    "\\begin{document}\\begin{frame}[t]{}" ++ body ++
    "\\end{frame}\\end{document}"

private def preparedChecksAgainst (ref : IO.Ref (List String))
    (fonts : Font.FontSet) (label : String) (prepared : Tcolorbox.Prepared)
    (control : String) : IO Unit := do
  let body := (prepared.lower #[.word "Body" {}] {}).raws
  let wrapped :=
    #[.ctrl "documentclass" {}, .group #[.word "beamer" {}] {},
      .ctrl "theme" {}, .group #[.word "default" {}] {},
      .env "document"
        #[.env "frame"
          (#[.sym '[' {}, .word "t" {}, .sym ']' {}, .group #[] {}] ++ body) {}] {}]
  let (doc, ds) := Elab.runRaws "t" wrapped
  let actual := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  let (controlDs, expected, expectedHtml, _) := sourceArtifacts fonts (document "" control)
  let t := check ref
  t s!"tcolorbox colors: {label}: native control supported"
    (controlDs.all (·.severity == .note))
  t s!"tcolorbox colors: {label}: PDF pages"
    (reprStr actual.pages == reprStr expected.pages)
  t s!"tcolorbox colors: {label}: typed HTML"
    (Html.document "en" head tree == expectedHtml)
  t s!"tcolorbox colors: {label}: supported retained content"
    ((ds ++ actual.diags ++ hds).all (·.severity == .note))

/-- The capture boundary receives only selected, supported color operands.
Rejected captures stay named and cannot leak their raw arguments into either
artifact. Source lookup and hook ordering are checked separately below. -/
def tcolorboxColorPreparedChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let capture (key : String) (value : Array Parse.Raw) :
      StateM (Array (String × String)) (Option (Array Parse.Raw)) := do
    modify (·.push (key, Parse.rawSrc value))
    return some #[.word "blue" {}]
  let options : Array Parse.Raw :=
    #[.word "title=" {}, .group #[.word "Heading" {}] {},
      .word ",fontupper=" {}, .group #[.ctrl "bfseries" {}] {},
      .word ",fonttitle=" {}, .group #[.ctrl "itshape" {}] {},
      .word ",coltext=Discarded,colupper=" {}, .ctrl "colorprobe" {},
      .word ",coltitle=" {}, .ctrl "colorprobe" {},
      .word ",unknown=" {}, .ctrl "hiddenprobe" {}]
  let (prepared, calls) := (Tcolorbox.prepareM capture options {}).run #[]
  let t := check ref
  t "tcolorbox colors: capture receives only final selected operands"
    (calls == #[("colupper", "\\colorprobe"), ("coltitle", "\\colorprobe")])
  t "tcolorbox colors: capture preserves independent loss"
    (prepared.unsupported == #["unknown"])
  preparedChecksAgainst ref fonts "captured aliases"
    prepared
    ("\\begin{block}{{\\color{blue}\\itshape Heading}}" ++
      "{\\color{blue}\\bfseries Body}\\end{block}")
  for key in ["coltext", "colupper", "coltitle"] do
    let prepared := Tcolorbox.prepareM (m := Id) (fun _ _ => pure none)
      #[.word ("title=Heading," ++ key ++ "=") {}, .ctrl "hiddenprobe" {}] {}
    t s!"tcolorbox colors: rejected capture names {key}"
      (prepared.unsupported == #[key])
    preparedChecksAgainst ref fonts ("rejected " ++ key) prepared
      "\\begin{block}{Heading}Body\\end{block}"
  let (prepared, calls) := (Tcolorbox.prepareM capture
    #[.word "title=Heading,colback=black,coltext=" {}, .ctrl "hiddenprobe" {},
      .word ",colbacktitle=black,coltitle=" {}, .ctrl "hiddenprobe" {}] {}).run #[]
  t "tcolorbox colors: unsupported paint pairs never call capture" calls.isEmpty
  t "tcolorbox colors: all unsupported paint members remain named"
    (prepared.unsupported == #["colback", "colbacktitle", "coltext", "coltitle"])
  preparedChecksAgainst ref fonts "unsupported paint pairs" prepared
    "\\begin{block}{Heading}Body\\end{block}"

/-- Native controls keep the declaration scopes and compare complete shipped
PDF page models and typed HTML. No color or macro wrapper is normalized away. -/
private def caseChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label pre body control : String) (refused : Array String := #[]) : IO Unit := do
  let (ds, actual, html, _) := sourceArtifacts fonts (document pre body)
  let (controlDs, expected, expectedHtml, _) := sourceArtifacts fonts (document "" control)
  let t := check ref
  t s!"tcolorbox colors: {label}: native control supported"
    (controlDs.all (·.severity == .note))
  t s!"tcolorbox colors: {label}: PDF pages"
    (reprStr actual.pages == reprStr expected.pages)
  t s!"tcolorbox colors: {label}: typed HTML" (html == expectedHtml)
  t s!"tcolorbox colors: {label}: only declared loss"
    (ds.all fun d => d.severity == .note || (!refused.isEmpty && d.kind == .W0110))
  for key in refused do
    t s!"tcolorbox colors: {label}: {key} loss named"
      (ds.any fun d => d.kind == .W0110 && d.subject == some "tcolorbox:panel" &&
        d.trigger == some "\\begin" && hasStr d.message key)

/-- tcolorbox 6.9.0 captures color keys at each use, before executing font
hooks. Its savebox selects that captured color before the font hook, so a
hook's explicit color wins. LuaLaTeX probes of `current@color` pin both
orders, late lookup after declaration, and restoration after local font
definitions. These checks hold the actual artifacts to native controls. -/
def tcolorboxColorSourceChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  for key in ["coltext", "colupper"] do
    for colorsFirst in [true, false] do
      let colors := key ++ "=blue,coltitle=blue"
      let hooks := "fontupper={\\color{black}},fonttitle={\\color{black}}"
      caseChecks ref fonts s!"{key} before font, key order {colorsFirst}"
        ("\\newtcolorbox{panel}{title={Heading}," ++
          (if colorsFirst then colors ++ "," ++ hooks else hooks ++ "," ++ colors) ++ "}")
        "\\begin{panel}Body\\end{panel}"
        ("\\begin{block}{{\\color{blue}\\color{black}Heading}}" ++
          "{\\color{blue}\\color{black}Body}\\end{block}")
  caseChecks ref fonts "late colors at separate uses"
    ("\\newtcolorbox{panel}{" ++
      "title={Heading},coltext=\\colorprobe,coltitle=\\colorprobe}\\def\\colorprobe{blue}")
    ("\\begin{panel}First\\end{panel}\\def\\colorprobe{black}" ++
      "\\begin{panel}Second\\end{panel}")
    ("\\begin{block}{{\\color{blue}Heading}}{\\color{blue}First}\\end{block}" ++
      "\\begin{block}{{\\color{black}Heading}}{\\color{black}Second}\\end{block}")
  caseChecks ref fonts "body color captured before font definition"
    ("\\newtcolorbox{panel}{title={Heading},coltext=\\colorprobe," ++
      "fontupper={\\def\\colorprobe{black}}}\\def\\colorprobe{blue}")
    "\\begin{panel}Body\\end{panel}\\colorprobe"
    ("\\def\\colorprobe{blue}\\begin{block}{Heading}" ++
      "{\\color{blue}\\def\\colorprobe{black}Body}\\end{block}\\colorprobe")
  caseChecks ref fonts "title color captured before font definition"
    ("\\newtcolorbox{panel}{title={Heading},coltitle=\\colorprobe," ++
      "fonttitle={\\def\\colorprobe{black}}}\\def\\colorprobe{blue}")
    "\\begin{panel}Body\\end{panel}\\colorprobe"
    ("\\def\\colorprobe{blue}\\begin{block}" ++
      "{{\\color{blue}Heading}}Body\\end{block}\\colorprobe")
  caseChecks ref fonts "both colors captured before title global definition"
    ("\\newtcolorbox{panel}{title={Heading},coltext=\\colorprobe," ++
      "coltitle=\\colorprobe,fonttitle={\\global\\def\\colorprobe{black}}}" ++
      "\\def\\colorprobe{blue}")
    "\\begin{panel}Body\\end{panel}\\colorprobe"
    ("\\def\\colorprobe{black}\\begin{block}" ++
      "{{\\color{blue}Heading}}{\\color{blue}Body}\\end{block}\\colorprobe")
  for (ground, foreground, title) in [
      ("colback", "coltext", "Heading"),
      ("colback", "colupper", "Heading"),
      ("colframe", "coltitle", "Heading"),
      ("colbacktitle", "coltitle", "Heading")] do
    caseChecks ref fonts (ground ++ " refuses dependent " ++ foreground)
      ("\\newtcolorbox{panel}{title={" ++ title ++ "}," ++
        ground ++ "=black," ++ foreground ++ "=\\undefinedcolorprobe}")
      "\\begin{panel}Body\\end{panel}"
      ("\\begin{block}{" ++ title ++ "}Body\\end{block}")
      #[ground, foreground]

def tcolorboxColorChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  tcolorboxColorPreparedChecks ref fonts
  tcolorboxColorSourceChecks ref fonts

end TcolorboxColors
