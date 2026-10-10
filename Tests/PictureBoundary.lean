module

public import Tests.Support
public import Lean.Data.Json.Parser
public import Lean.Data.Json

public section

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

private def parseRaws (file s : String) : Array Parse.Raw :=
  (Parse.parse file (Lex.lex file s).1).1

/-- An invented deck: a local style requires a beamer theme and a beamer
add-on beside a picture package, a TikZ library, a colour and an unknown
package, and the deck loads a colour theme of its own and a presentation
tool's package beside a page-layout one; its one picture is outside the
rendered subset. -/
def wrapperDeck : Ir.Doc :=
  let sty := "\\ProvidesPackage{probestyle}\n\\RequirePackage{beamerthememoloch}\n" ++
    "\\RequirePackage{beamerprobetools}\n" ++
    "\\RequirePackage{tikz}\n\\usetikzlibrary{arrows.meta}\n\\RequirePackage{pgfplots}\n" ++
    "\\RequirePackage[scale=0.9]{fontawesome5}\n\\definecolor{probeTeal}{HTML}{1A7F7A}\n"
  let deck := "\\documentclass{beamer}\n\\usepackage{probestyle}\n" ++
    "\\usepackage{beamercolorthemeprobe}\n\\usepackage{pdfpc,pgfpages}\n" ++
    "\\begin{document}\n\\begin{frame}\n" ++
    picture "\\shade[left color=probeTeal] (0,0) circle (0.2);" ++ "\n\\end{frame}\n\\end{document}"
  let (raws, _) := Compat.applyLocalSty (parseRaws "t" deck)
    #[("probestyle", parseRaws "probestyle.sty" sty)]
  (Elab.runRawsSpanned "t" raws).1

/-- **The standalone carries what its picture reads, never the class's or the
theme's.** A theme presupposes beamer, which a standalone never is, so its
load failed the boundary on its first `\useinnertheme` and the picture fell
back to the rendered subset; an add-on named for beamer stops a standalone
the same way, and a presentation tool's package on the hyperref beamer
loads. -/
def pictureWrapperChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let req := requestText wrapperDeck
  t "a deck's picture states its boundary request" ((Ir.pictureRefs wrapperDeck).size == 1)
  t "no theme or class package reaches the standalone, through a local style or directly"
    (!hasStr req "moloch" && !hasStr req "beamerprobetools" && !hasStr req "colortheme" &&
      !hasStr req "pdfpc")
  t "a package loaded beside one of the class's still rides, alone on its line"
    (hasStr req "\\usepackage{pgfpages}")
  t "the picture's libraries, packages and colours still ride"
    (hasStr req "\\usetikzlibrary{arrows.meta}" && hasStr req "\\usepackage{pgfplots}" &&
      hasStr req "\\usepackage[scale=0.9]{fontawesome5}" && hasStr req "\\definecolor{probeTeal}")
  t "the class's own family stays out, and nothing else is refused"
    (Compat.themePackage "beamerthememoloch" && Compat.themePackage "beamercolorthemeprobe" &&
      Compat.themePackage "beamerinnerthemeprobe" && !Compat.themePackage "beamerarticle" &&
      ["beamerthememoloch", "beamerbaseoverlay", "appendixnumberbeamer", "beamerposter",
        "beamerprobetools", "pdfpc"].all Compat.classPackage &&
      ["beamerbaseoverlay", "beamerprobetools", "pdfpc"].all (!Compat.boundaryRides ·) &&
      ["beamerarticle", "pgfplots", "tikz-cd", "fontawesome5", "pgfpages"].all
        Compat.boundaryRides &&
      !Compat.boundaryRides "tikz" && !Compat.boundaryRides "")

/-- The hosts a picture ships on: a boundary tool that answers its version,
then refuses every picture with a log (`refused`) or exits 3 leaving none
(`unfinished`), or a document that keeps its pictures to the rendered subset
(`declined`, `\pictures{ tool = none }`, so no tool is asked). -/
private def shipHosts : List (String × String × String) :=
  [("refused", "", "printf '%s\\n' '! Undefined control sequence.' > pic.log\nexit 1\n"),
   ("unfinished", "", "exit 3\n"),
   ("declined", "\\pictures{ tool = none }\n", "exit 3\n")]

/-- Invented pictures, per host: one the rendered subset draws in part, with
a construct outside the subset and an expression it cannot read; one it
draws nothing of; the first shape written twice; and one the subset draws in
part standing in a table cell's line, which it never sets. Each as written in the
document, with the code its one line carries there and what that line's help
quotes: the tool's words, the machine's, or the declaration. -/
private def shipPictures : List (String × String × String × String × Nat × String) :=
  let block (body : String) : String := "\\begin{tikzpicture}" ++ body ++ "\\end{tikzpicture}\n\n"
  let part := block ("\\node at (0,0) {Alpha};\\pgfmathsetmacro{\\even}{mod(1,2)==0}" ++
    "\\shade (0,0) rectangle (1,1);")
  let twice := block "\\node at (0,0) {Alpha};\\shade (0,0) rectangle (1,1);"
  let none := block "\\shade (0,0) rectangle (1,1);"
  let inline := "\\begin{tabular}{ll} Alpha & \\tikz{\\fill (0,0) rectangle (0.2,0.2);" ++
    "\\shade (0,0) rectangle (0.1,0.1);} \\\\ Beta & words \\end{tabular}\n\n"
  [("refused", "drawn in part", "W0419", part, 1, "Undefined control sequence"),
   ("refused", "drawn by no one", "W0382", none, 1, "Undefined control sequence"),
   ("refused", "drawn in part, twice", "W0419", twice, 2, "Undefined control sequence"),
   ("refused", "in a table cell", "W0382", inline, 1, "Undefined control sequence"),
   ("unfinished", "drawn in part", "W0382", part, 1, "a rebuild asks lualatex again"),
   ("unfinished", "drawn by no one", "W0382", none, 1, "a rebuild asks lualatex again"),
   ("declined", "drawn in part", "W0419", part, 1, "tool = none"),
   ("declined", "drawn in part, twice", "W0419", twice, 2, "tool = none")]

/-- **A picture no renderer draws whole never costs the document.** The
whole driver, run on a host whose boundary tool answers its version and
then refuses every picture with a log, on one whose tool never finishes,
and on a document that declares no tool: the PDF and the HTML page are each
written, the run exits 0, and each picture's loss is one warning at its
first line, carrying the count of the places it stands — the subset's
incomplete drawing (W0419, whose message carries every construct the subset
left out) or the placeholder (W0382, which the page labels; an attempt that
never finished is never the subset's drawing, and neither is a picture in a
line, which the subset never sets) — never a refusal of the
subset's beside it, and never an error. A repeat site keeps its line as a
note, and the page's run, which reads the tool's refusal back from the
cache, names it the same way. The run once exited 1 and wrote nothing, on
the unreadable expression the subset could not evaluate or on the tool's
own refusal, and still did under the declaration. The caller supplies an
already-built binary. -/
def pictureShipChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex")
    (font : System.FilePath := "testdata/corpus/fonts/OpenSans-Regular.ttf") : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath binary
  let font ← IO.FS.realPath font
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    for (host, _, answer) in shipHosts do
      IO.FS.createDirAll (dir / host)
      let tool := dir / host / "lualatex"
      IO.FS.writeFile tool
        ("#!/bin/sh\nif [ \"$1\" = --version ]; then\n" ++
          "  printf '%s\\n' 'synthetic renderer 1'\n  exit 0\nfi\n" ++ answer)
      IO.setAccessRights tool { user := ⟨true, true, true⟩ }
    for (host, what, code, picture, copies, quoted) in shipPictures do
      let pre := ((shipHosts.find? (·.1 == host)).map (·.2.1)).getD ""
      let file := dir / host / "ship.tex"
      IO.FS.writeFile file ("\\documentclass{article}\n" ++ pre ++ "\\begin{document}\nBefore.\n\n" ++
        String.join (List.replicate copies picture) ++ "After.\n\\end{document}\n")
      let first := 5 + (pre.splitOn "\n").length - 1
      for ext in ["pdf", "html"] do
        let output := dir / host / ("ship." ++ ext)
        if ← output.pathExists then IO.FS.removeFile output
        let result ← IO.Process.output {
          cmd := binary.toString
          args := #[file.toString, "-o", output.toString, "--porcelain"]
          env := #[("PATH", some ((dir / host).toString ++ ":" ++ path)),
            ("XDG_CACHE_HOME", some (dir / host / "cache").toString),
            ("LEANTEX_FONT", some font.toString)] }
        let records := ((result.stdout.splitOn "\n").filter (!·.isEmpty)).filterMap
          fun l => (Lean.Json.parse l).toOption
        let diags := records.filter (·.getObjValAs? String "event" == .ok "diagnostic")
        let codeOf (j : Lean.Json) : String := (j.getObjValAs? String "code").toOption.getD ""
        let severityOf (j : Lean.Json) : String :=
          (j.getObjValAs? String "severity").toOption.getD ""
        let lines := diags.filter (codeOf · == code)
        let warnings := lines.filter (severityOf · == "warning")
        let art := s!"picture ship, {host}: {what}, {ext}"
        t s!"{art}: the document ships, exit 0"
          (result.exitCode == 0 && (← output.pathExists))
        t s!"{art}: its loss is one warning at the picture's first line"
          (lines.length == copies && warnings.length == 1 && warnings.all fun j =>
            j.getObjValAs? Nat "line" == .ok first &&
              (copies == 1 || j.getObjValAs? Nat "sites" == .ok copies))
        t s!"{art}: no error, and no refusal of the subset beside the line"
          (diags.all fun j => severityOf j != "error" &&
            !["W0334", "E0333", "N0419", "E0382"].contains (codeOf j))
        t s!"{art}: the line says why no renderer drew the picture whole"
          (warnings.all fun j => hasStr ((j.getObjValAs? String "help").toOption.getD "") quoted)
        if code == "W0419" then
          t s!"{art}: the line carries every construct left out"
            (warnings.all fun j =>
              let msg := (j.getObjValAs? String "message").toOption.getD ""
              hasStr msg "\\shade" && (copies > 1 || hasStr msg "'mod'"))
        if ext == "html" then
          let html ← if ← output.pathExists then IO.FS.readFile output else pure ""
          let tags := placeholderTags html
          let drawings := (html.splitOn "<svg").length - 1
          t s!"{art}: the page shows the subset's drawing or a labelled placeholder, never a request key"
            (!hasStr html (" src=\"" ++ Ir.picSrcPrefix) &&
              if code == "W0382" then tags.length == copies && tags.all labelled && drawings == 0
              else drawings == copies && tags.isEmpty)

end PictureBoundary
