import Tests.Support
import LeanTex.Core.Tcolorbox

open LeanTex.Core

namespace TcolorboxChecks

private def raws (source : String) : Array Parse.Raw :=
  (Parse.parse "probe" (Lex.lex "probe" source).1).1

private def wrap (body : Array Parse.Raw) : Array Parse.Raw :=
  raws "\\documentclass{beamer}\\theme{default}" ++
    #[.env "document"
      #[.env "frame"
        (#[.sym '[' {}, .word "t" {}, .sym ']' {}, .group #[] {}] ++ body) {}] {}]

private def lowered (options body : String) : Tcolorbox.Lowered :=
  Tcolorbox.lower (raws options) (raws body) {}

private def docOf (options body : String) : Ir.Doc × Array Diag :=
  Elab.runRaws "probe" (wrap (lowered options body).raws)

private def htmlFacts (doc : Ir.Doc) :
    Array (String × Array (String × String)) × String :=
  let (_, tree, _) := HtmlDoc.emitTree {} doc
  (elemAttrsList (fun _ => true) #[] tree.toList, nodeTextList "" tree.toList)

private def nativeDoc (source : String) : Ir.Doc :=
  (Elab.runRaws "probe" (wrap (raws source))).1

private def samePages (fonts : Font.FontSet) (a b : Ir.Doc) : Bool :=
  reprStr (layoutOf fonts a).pages == reprStr (layoutOf fonts b).pages &&
    htmlFacts a == htmlFacts b

/-- A missing body ground must not carry its dependent foreground alone.
The artifact comparison checks both the PDF page census and typed HTML. -/
def groundChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (actual, _) := docOf "colback=black,coltext=white" "ReadableBody"
  let plain := (docOf "" "ReadableBody").1
  t "tcolorbox: unsupported ground and dependent foreground stay readable"
    (samePages fonts actual plain)
  let loss := (lowered "colback=black,coltext=white" "ReadableBody").unsupported
  t "tcolorbox: both members of unsupported paint pair are named"
    (loss.contains "colback" && loss.contains "coltext")
  let (actualTitle, _) := docOf "title={ReadableTitle},colframe=white,coltitle=black"
    "ReadableBody"
  t "tcolorbox: unsupported title ground and foreground stay paired"
    (samePages fonts actualTitle (docOf "title={ReadableTitle}" "ReadableBody").1)
  let titleLoss := (lowered "colframe=white,coltitle=black" "").unsupported
  t "tcolorbox: both members of unsupported title pair are named"
    (titleLoss.contains "colframe" && titleLoss.contains "coltitle")

/-- The helper's native output is judged through actual emitters; the
declaration/argument reader is covered separately by `sourceChecks`. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (actual, ds) := docOf
    "title={Exact, title = {kept}},fontupper=\\small\\bfseries"
    "FirstBody\n\nSecondBody"
  let expected := nativeDoc
    "\\begin{block}{Exact, title = {kept}}{\\small\\bfseries FirstBody\n\nSecondBody}\\end{block}"
  t "tcolorbox: native title and styled body match both artifacts"
    (samePages fonts actual expected)
  let lines := (bodyLines (layoutOf fonts actual)).map lineText
  t "tcolorbox: title reaches the PDF page"
    (lines.any (hasStr · "Exact, title = kept"))
  t "tcolorbox: both body paragraphs reach the PDF page"
    (lines.any (hasStr · "FirstBody") && lines.any (hasStr · "SecondBody"))
  t "tcolorbox: title and both paragraphs reach typed HTML"
    (["Exact, title = kept", "FirstBody", "SecondBody"].all (hasStr (htmlFacts actual).2 ·))
  t "tcolorbox: supported native subset introduces no unknown or body errors"
    (!ds.any (fun d => d.severity == .error || d.code == "W0301" || d.code == "W0302"))
  let styled := (docOf "coltext=red,fonttitle=\\itshape,coltitle=blue,title={Heading}"
    "ColoredBody").1
  let styledNative := nativeDoc
    "\\begin{block}{{\\itshape\\color{blue}Heading}}{\\color{red}ColoredBody}\\end{block}"
  t "tcolorbox: separate title and body styles use existing native scopes"
    (samePages fonts styled styledNative)
  t "tcolorbox: scoped colour changes the rendered body"
    (!samePages fonts styled (docOf "title={Heading}" "ColoredBody").1)
  let skipped := (docOf "title={Gap},before skip=6pt,after skip=3pt"
    "SpacedBody").1
  let skippedNative := nativeDoc
    "\\block[before=6pt]{}\\begin{block}{Gap}SpacedBody\\end{block}\\block[before=3pt]{}"
  t "tcolorbox: declared gaps use the native spacing blocks"
    (samePages fonts skipped skippedNative)
  t "tcolorbox: unsupported gap collision semantics remain accounted"
    ((lowered "before skip=6pt,after skip=3pt" "").unsupported ==
      #["before skip", "after skip"])
  let invalidGap := lowered "before skip={3pt],title={Injected}}" "SafeBody"
  let (invalidGapDoc, _) := Elab.runRaws "probe" (wrap invalidGap.raws)
  t "tcolorbox: invalid spacing cannot escape into native syntax"
    (invalidGap.unsupported == #["before skip"] &&
      samePages fonts invalidGapDoc (docOf "" "SafeBody").1)
  let repeated := (docOf
    "title={Old},title={Final},fontupper=\\small,fontupper=\\bfseries" "LastWins").1
  let repeatedNative := nativeDoc "\\begin{block}{Final}{\\bfseries LastWins}\\end{block}"
  t "tcolorbox: repeated keys take their last assignment"
    (samePages fonts repeated repeatedNative)
  let unknown := lowered "enhanced,arc=2pt,left=4pt,unknown={hidden,option},arc=3pt" "Kept"
  t "tcolorbox: unsupported keys are accounted once without their values leaking"
    (unknown.unsupported == #["enhanced", "arc", "left", "unknown"])
  let (unknownDoc, _) := Elab.runRaws "probe" (wrap unknown.raws)
  t "tcolorbox: unknown decoration cannot replace or add body text"
    (samePages fonts unknownDoc (docOf "" "Kept").1)
  let (_, missing) := docOf "title={Good}" "\\begin{unimplementedpanel}{StillBody}\\end{unimplementedpanel}"
  t "tcolorbox: unknown body environment errors remain visible"
    (missing.any (fun d => d.code == "E0336"))
  groundChecks ref fonts

/-- Full declaration probes for the compatibility owner: options are
instantiated at use, including a default and a macro defined later. -/
def sourceChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let source := "\\documentclass{beamer}\\theme{default}" ++
    "\\newtcolorbox{panel}[2][Default]{title={\\later{#1}: #2},fontupper=\\small\\bfseries}" ++
    "\\newcommand{\\later}[1]{#1}" ++
    "\\begin{document}\\begin{frame}[t]{}" ++
    "\\begin{panel}{First}FirstBody\\end{panel}" ++
    "\\begin{panel}[Chosen]{Second}SecondBody\\end{panel}" ++
    "\\end{frame}\\end{document}"
  let (actual, ds) := elabStr source
  let expected := nativeDoc
    ("\\begin{block}{Default: First}{\\small\\bfseries FirstBody}\\end{block}" ++
     "\\begin{block}{Chosen: Second}{\\small\\bfseries SecondBody}\\end{block}")
  t "tcolorbox source: argument-bound native blocks match both artifacts"
    (samePages fonts actual expected)
  let lines := (bodyLines (layoutOf fonts actual)).map lineText
  t "tcolorbox source: default and supplied argument title reach PDF"
    (lines.any (hasStr · "Default: First") && lines.any (hasStr · "Chosen: Second"))
  t "tcolorbox source: both bodies reach PDF"
    (lines.any (hasStr · "FirstBody") && lines.any (hasStr · "SecondBody"))
  t "tcolorbox source: default and supplied argument title reach HTML"
    (["Default: First", "Chosen: Second"].all (hasStr (htmlFacts actual).2 ·))
  t "tcolorbox source: declaration and uses introduce no unknown body errors"
    (!ds.any (fun d => d.severity == .error || d.code == "W0301" || d.code == "W0302"))

end TcolorboxChecks
