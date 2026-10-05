import Tests.Support

open LeanTex.Core

namespace PictureBoundary

/-- The driver's first pass, before a missing boundary answer withdraws a
partly native picture. Request checks must inspect the request that the
driver actually tries to fulfil. -/
def firstPass (src : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
  let (toks, lds) := Lex.lex "t" src
  let (raws, pds) := Parse.parse "t" toks
  Elab.runRawsSpanned "t" raws (lds ++ pds)

private def requestText (doc : Ir.Doc) : String :=
  ((Ir.pictureRefs doc)[0]?.map (·.2)).getD ""

private def picture (body : String) : String :=
  "\\begin{tikzpicture}" ++ body ++ "\\end{tikzpicture}"

private def node (label : String) : String :=
  "\\node[text width=4cm] at (0,0) {" ++ label ++ "};"

private def canonical (src : String) : String :=
  Parse.rawSrc (Parse.parse "t" (Lex.lex "t" src).1).1

/-- Invented input for the independent LuaLaTeX acceptance check. Its
paragraph skip must reach TeX as a skip, never as the native block command;
its alert must use the text/color bridge shared with native labels. -/
def standaloneSource : String :=
  dvDoc "\\theme{moloch}\n"
    (picture (node "Upper\\par\\smallskip Lower \\alert{Bright} {\\color{blue}Blue}"))

/-- A routed picture remains TeX source while native alert/text-color
labels keep their existing artifact. No external tool is needed by these
request and typed-HTML checks. -/
def pictureBoundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for command in ["\\smallskip", "\\medskip", "\\bigskip",
      "\\vspace{2pt}", "\\vspace*{2pt}", "\\fontsize{9pt}{11pt}\\selectfont",
      "\\color{blue}"] do
    let (doc, ds, spans) := firstPass (dvDoc ""
      (picture (node ("Upper\\par{" ++ command ++ " Lower}"))))
    let req := requestText doc
    t s!"the actual picture request keeps TeX spelling: {command}"
      ((Ir.pictureRefs doc).size == 1 &&
        hasStr req (canonical command) &&
        !hasStr req "\\block" && !hasStr req "\\@fontsize:" &&
        !hasStr req "\\@ink:" &&
        ds.any (·.code == "N0023") &&
        spans.fallbacks == (Ir.pictureRefs doc).map (·.1))
  let (macroDoc, _, _) := firstPass (dvDoc "\\newcommand{\\gap}{\\smallskip}\n"
    (picture (node "Upper\\par\\gap Lower")))
  let (literalDoc, _, _) := firstPass (dvDoc ""
    (picture (node "Upper\\par\\smallskip Lower")))
  t "a macro-expanded paragraph skip keeps the literal request's TeX"
    (!(requestText literalDoc).isEmpty &&
      Ir.pictureRefs macroDoc == Ir.pictureRefs literalDoc &&
      hasStr (requestText macroDoc) "\\smallskip")
  let (scopedDoc, _, _) := firstPass (dvDoc ""
    (picture ("\\begin{scope}" ++ node "Upper\\par\\smallskip Lower" ++ "\\end{scope}")))
  t "nested picture environments inherit the TeX-preserving context"
    (hasStr (requestText scopedDoc) "\\begin{scope}" &&
      hasStr (requestText scopedDoc) "\\smallskip" &&
      !hasStr (requestText scopedDoc) "\\block")
  let (inlineDoc, _, _) := firstPass (dvDoc ""
    ("\\tikz{" ++ node "Upper\\par\\smallskip Lower" ++ "}"))
  t "inline and environment pictures preserve the same TeX request"
    (Ir.pictureRefs inlineDoc == Ir.pictureRefs literalDoc)
  let (styledDoc, _, _) := firstPass standaloneSource
  let styledReq := requestText styledDoc
  t "the fulfilment input keeps the skip and bridges alert with a declared color"
    ((Ir.pictureRefs styledDoc).size == 1 && hasStr styledReq "\\smallskip" &&
      hasStr styledReq "\\textcolor {alert}" && hasStr styledReq "\\bfseries" &&
      hasStr styledReq "\\definecolor{alert}" && hasStr styledReq "\\color {blue}" &&
      !hasStr styledReq "\\block" && !hasStr styledReq "\\@ink:")
  for (theme, label, explicit) in [
      ("\\theme{moloch}", "\\alert{Bright}", "\\textcolor{alert}{\\bfseries Bright}"),
      ("", "\\alert{Bright}", "{\\bfseries Bright}"),
      ("", "\\textcolor{blue}{Bright}", "\\textcolor{blue}{Bright}")] do
    let native (text : String) := firstPass (dvDoc theme
      (picture ("\\node at (0,0) {" ++ text ++ "};")))
    let (doc, ds, _) := native label
    let expected := (native explicit).1
    let nodes := doc.body.map (HtmlDoc.blockNode {})
    t s!"native label styling still ships its typed SVG: {theme} {label}"
      ((Ir.pictureRefs doc).isEmpty &&
        ds.all (fun d => d.severity != .error && d.code != "W0334") &&
        !nodes.isEmpty && nodes.map (Html.render · 0) ==
          (expected.body.map (HtmlDoc.blockNode {})).map (Html.render · 0) &&
        hasStr (nodeTextList "" nodes.toList) "Bright")
  let (_, outsideDs, _) := firstPass (dvDoc ""
    (picture (node "Upper\\par\\smallskip Lower") ++ "\n\\smallskip Tail"))
  t "leaving the picture restores ordinary skip rewriting"
    ((outsideDs.filter fun d => d.code == "N0100" && hasStr d.message "\\smallskip").size == 1)

end PictureBoundary
