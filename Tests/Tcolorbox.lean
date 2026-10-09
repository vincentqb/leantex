module

public import Tests.Support
public import LeanTex.Core.Tcolorbox

public section

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

/-- The control a lowering is judged against: the native block written as
the box it stands for (`boxedRaws`). -/
private def nativeDoc (source : String) : Ir.Doc :=
  (Elab.runRaws "probe" (wrap (boxedRaws #[] (raws source).toList))).1

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
declaration/argument reader is covered separately by `tcolorboxSourceChecks`. -/
def tcolorboxChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
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
    "\\begin{block}{{\\color{blue}\\itshape Heading}}{\\color{red}ColoredBody}\\end{block}"
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

/-- Source controls compare complete PDF page models and serialized typed HTML,
including fonts, positions, grouping and whitespace. A permitted loss still
needs a keyed diagnostic; permitting it cannot make a missing diagnostic pass. -/
private def sourceCaseChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label pre body control : String) (loss : Option DiagCode := none)
    (trigger : Option String := none) (subject : Option String := none)
    (boxed : Bool := true) : IO Unit := do
  let doc (p b : String) := "\\documentclass{beamer}\\theme{default}" ++ p ++
    "\\begin{document}\\begin{frame}[t]{}" ++ b ++ "\\end{frame}\\end{document}"
  let (ds, actual, html, _) := sourceArtifacts fonts (doc pre body)
  -- The control's `{block}`s stand for the boxes the source lowers to;
  -- where the source's own blocks are beamer's, they stay beamer's.
  let (controlDs, expected, expectedHtml, _) :=
    (if boxed then boxedSourceArtifacts else sourceArtifacts) fonts (doc "" control)
  let t := check ref
  t s!"tcolorbox source: {label}: native control is supported"
    (controlDs.all (·.severity == .note))
  t s!"tcolorbox source: {label}: PDF pages"
    (reprStr actual.pages == reprStr expected.pages)
  t s!"tcolorbox source: {label}: typed HTML"
    (html == expectedHtml)
  t s!"tcolorbox source: {label}: only declared loss"
    (ds.all (fun d => d.severity == .note || loss == some d.kind))
  if let some code := loss then
    t s!"tcolorbox source: {label}: loss is named"
      (ds.any (fun d => d.kind == code && d.subject.isSome))
    if let some command := trigger then
      t s!"tcolorbox source: {label}: loss belongs to written command"
        (ds.filter (·.kind == code) |>.all (·.trigger == some command))
    if let some name := subject then
      t s!"tcolorbox source: {label}: subject names authored environment"
        (ds.filter (·.kind == code) |>.all fun d =>
          d.subject.any fun s => s == name || s.endsWith (":" ++ name))

/-- Key selection precedes execution: discarded values cannot change the
body or surrounding scope. Global definitions witness effects that closing
an option group cannot hide; a local flag is observed inside the box.
Retained font declarations share the body's scope, including nested boxes,
and that scope closes before the following text. -/
def tcolorboxEffectChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let defined := "\\ifdefined\\hiddenprobe Leaked\\else Inert\\fi"
  let chosen := "\\ifchoiceprobe Chosen\\else Default\\fi"
  -- Positive controls show that the same effects are observable when
  -- executed in ordinary native block content.
  sourceCaseChecks ref fonts "global definition witness" ""
    ("\\begin{block}{Heading}{\\gdef\\hiddenprobe{Leaked}}" ++
      defined ++ "\\end{block}" ++ defined)
    "\\begin{block}{Heading}Leaked\\end{block}Leaked" (boxed := false)
  sourceCaseChecks ref fonts "local flag witness" "\\newif\\ifchoiceprobe"
    ("\\begin{block}{Heading}\\choiceprobetrue" ++ chosen ++
      "\\end{block}" ++ chosen)
    "\\begin{block}{Heading}Chosen\\end{block}Default" (boxed := false)
  sourceCaseChecks ref fonts "unsupported global definition is inert"
    "\\newtcolorbox{panel}{title={Heading},unknown={\\global\\def\\hiddenprobe{Leaked}}}"
    ("\\begin{panel}" ++ defined ++ "\\end{panel}" ++ defined)
    "\\begin{block}{Heading}Inert\\end{block}Inert"
    (some .W0110) (some "\\begin") (some "panel")
  sourceCaseChecks ref fonts "unsupported local flag cannot choose body"
    ("\\newif\\ifchoiceprobe" ++
      "\\newtcolorbox{panel}{title={Heading},unknown=\\choiceprobetrue}")
    ("\\begin{panel}" ++ chosen ++ "\\end{panel}" ++ chosen)
    "\\begin{block}{Heading}Default\\end{block}Default"
    (some .W0110) (some "\\begin") (some "panel")
  for (key, initial, final, title, body) in [
      ("title", "\\global\\def\\hiddenprobe{Leaked}Discarded", "Heading",
        "Heading", "Inert"),
      ("fontupper", "\\global\\def\\hiddenprobe{Leaked}\\bfseries", "\\small",
        "Heading", "{\\small Inert}"),
      ("fonttitle", "\\global\\def\\hiddenprobe{Leaked}\\itshape", "\\bfseries",
        "{\\bfseries Heading}", "Inert")] do
    sourceCaseChecks ref fonts ("replaced " ++ key ++ " is inert")
      ("\\newtcolorbox{panel}{title={Heading}," ++ key ++ "={" ++ initial ++
        "}," ++ key ++ "={" ++ final ++ "}}")
      ("\\begin{panel}" ++ defined ++ "\\end{panel}" ++ defined)
      ("\\begin{block}{" ++ title ++ "}" ++ body ++ "\\end{block}Inert")
  sourceCaseChecks ref fonts "empty title leaves title font inert"
    ("\\newtcolorbox{panel}{" ++
      "fonttitle={\\global\\def\\hiddenprobe{Leaked}\\bfseries}}")
    ("\\begin{panel}" ++ defined ++ "\\end{panel}" ++ defined)
    "\\begin{block}{}Inert\\end{block}Inert"
  sourceCaseChecks ref fonts "retained body font flag shares body scope"
    ("\\newif\\ifchoiceprobe" ++
      "\\newtcolorbox{panel}{title={Heading},fontupper={\\choiceprobetrue\\small}}")
    ("\\begin{panel}" ++ chosen ++ "\\end{panel}" ++ chosen)
    "\\begin{block}{Heading}{\\small Chosen}\\end{block}Default"
  sourceCaseChecks ref fonts "nested original body binds each box"
    "\\newtcolorbox{panel}[2]{title={#1},fontupper={#2}}"
    ("\\begin{panel}{Outer}{\\small}Before" ++
      "\\begin{panel}{Inner}{\\bfseries}Inside\\end{panel}" ++
      "After\\end{panel}Outside")
    ("\\begin{block}{Outer}{\\small Before" ++
      "\\begin{block}{Inner}{\\bfseries Inside}\\end{block}" ++
      "After}\\end{block}Outside")
  sourceCaseChecks ref fonts "nested original body restores font flag"
    ("\\newif\\ifchoiceprobe" ++
      "\\newtcolorbox{outerpanel}{title={Outer},fontupper=\\choiceprobetrue}" ++
      "\\newtcolorbox{innerpanel}{title={Inner},fontupper=\\choiceprobefalse}")
    ("\\begin{outerpanel}" ++ chosen ++
      "\\begin{innerpanel}" ++ chosen ++ "\\end{innerpanel}" ++ chosen ++
      "\\end{outerpanel}" ++ chosen)
    ("\\begin{block}{Outer}Chosen" ++
      "\\begin{block}{Inner}Default\\end{block}Chosen\\end{block}Default")

/-- Title hooks execute inside the title's savebox scope. Definitions leave
no inline syntax behind; uses see the binding at that point, and only a
global assignment can change the body or following text. -/
def tcolorboxTitleBindingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  for (definer, after) in [
      ("\\def", "Outer"), ("\\long\\def", "Outer"),
      ("\\global\\def", "Local"), ("\\gdef", "Local")] do
    sourceCaseChecks ref fonts (definer ++ " in title font")
      ("\\def\\headingprobe{Outer}" ++
        "\\newtcolorbox{panel}{title={\\headingprobe}," ++
        "fonttitle={" ++ definer ++ "\\headingprobe{Local}}}")
      "\\begin{panel}\\headingprobe\\end{panel}\\headingprobe"
      ("\\begin{block}{{Local}}" ++ after ++ "\\end{block}" ++ after)
  sourceCaseChecks ref fonts "title-local value precedes scoped redefinition"
    ("\\def\\headingprobe{Outer}" ++
      "\\newtcolorbox{panel}{fonttitle={\\def\\headingprobe{Local}}," ++
      "title={\\headingprobe/{\\def\\headingprobe{Inner}\\headingprobe}/\\headingprobe}}")
    "\\begin{panel}\\headingprobe\\end{panel}\\headingprobe"
    "\\begin{block}{{Local/{Inner}/Local}}Outer\\end{block}Outer"
  sourceCaseChecks ref fonts "title-local value inside native formatting"
    ("\\def\\headingprobe{Outer}" ++
      "\\newtcolorbox{panel}{fonttitle={\\def\\headingprobe{Local}}," ++
      "title={\\textbf{\\headingprobe}}}")
    "\\begin{panel}\\headingprobe\\end{panel}\\headingprobe"
    "\\begin{block}{{\\textbf{Local}}}Outer\\end{block}Outer"

/-- Preparing retained fields preserves the caller's macro orders. A refused
nested template consumes its arguments without running them and executes only
its body, once, with the original environment's scope. -/
def tcolorboxPreparationChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  for (key, replacement, title, body) in [
      ("title", "\\iftrue Copied\\else Wrong\\fi", "Copied", "Body"),
      ("fonttitle", "\\iftrue\\bfseries\\else\\small\\fi", "{\\bfseries Heading}", "Body"),
      ("fontupper", "\\iftrue\\small\\else\\bfseries\\fi", "Heading", "{\\small Body}")] do
    for nested in [false, true] do
      sourceCaseChecks ref fonts
        (key ++ if nested then " copied inside two macros" else " copied inside a macro")
        ("\\def\\originalprobe{" ++ replacement ++ "}" ++
          "\\newtcolorbox{panel}{title={Heading}," ++ key ++ "=\\aliasprobe}" ++
          "\\def\\wrapperprobe{\\let\\aliasprobe\\originalprobe" ++
            "\\begin{panel}Body\\end{panel}}" ++
          if nested then "\\def\\outerprobe{\\wrapperprobe}" else "")
        (if nested then "\\outerprobe" else "\\wrapperprobe")
        ("\\begin{block}{" ++ title ++ "}" ++ body ++ "\\end{block}")
  let ignored := "\\gdef\\discardedprobe{Leaked}"
  let kept := "\\ifbodyprobe Repeated\\else Once\\fi\\bodyprobetrue" ++
    "\\ifbodyprobe Kept\\else Missing\\fi"
  let observed := "\\ifdefined\\discardedprobe Leaked\\else Inert\\fi/" ++
    "\\ifbodyprobe LeakedScope\\else Scoped\\fi"
  let optional := "\\newtcolorbox{innerpanel}[2][" ++ ignored ++ "]{title={#1/#2}}"
  for (label, declaration, opening, bodyPrefix) in [
      ("required argument",
        "\\newtcolorbox{innerpanel}[1]{title={#1}}",
        "\\begin{innerpanel}{" ++ ignored ++ "}", ""),
      ("optional argument", optional,
        "\\begin{innerpanel}[" ++ ignored ++ "]{" ++ ignored ++ "}", ""),
      ("default argument", optional,
        "\\begin{innerpanel}{" ++ ignored ++ "}", ""),
      ("split token argument",
        "\\newtcolorbox{innerpanel}[2]{title={#1/#2}}",
        "\\begin{innerpanel}{" ++ ignored ++ "}XY", "Y"),
      ("direct options", "",
        "\\begin{tcolorbox}[title={" ++ ignored ++ "},fontupper={" ++ ignored ++ "}]", "")] do
    let name := if label == "direct options" then "tcolorbox" else "innerpanel"
    let nested := opening ++ kept ++ "\\end{" ++ name ++ "}"
    for key in ["title", "fonttitle", "fontupper"] do
      let recovered := "{" ++ bodyPrefix ++ "OnceKept}"
      let title := if key == "title" then recovered
        else if key == "fonttitle" then "{" ++ recovered ++ "Heading}" else "Heading"
      let body := if key == "fontupper" then "{" ++ recovered ++ "Inert/Scoped}"
        else "Inert/Scoped"
      sourceCaseChecks ref fonts (key ++ " refuses nested " ++ label)
        ("\\newif\\ifbodyprobe" ++ declaration ++
          "\\newtcolorbox{panel}{title={Heading}," ++ key ++ "={" ++ nested ++ "}}")
        ("\\begin{panel}" ++ observed ++ "\\end{panel}" ++ observed)
        ("\\begin{block}{" ++ title ++ "}" ++ body ++ "\\end{block}Inert/Scoped")
        (some .W0104) none (some name)
  sourceCaseChecks ref fonts "a macro cannot restart title preparation"
    ("\\newif\\ifbodyprobe\\newtcolorbox{innerpanel}[1]{title={#1}}" ++
      "\\def\\nestedprobe{\\begin{innerpanel}{" ++ ignored ++ "}" ++ kept ++
        "\\end{innerpanel}}" ++
      "\\newtcolorbox{panel}{title={\\nestedprobe}}")
    ("\\begin{panel}" ++ observed ++ "\\end{panel}" ++ observed)
    "\\begin{block}{{OnceKept}}Inert/Scoped\\end{block}Inert/Scoped"
    (some .W0104) none (some "innerpanel")

/-- tcolorbox uses ordinary environment arguments and TeX declaration scope
(tcolorbox manual, “Creation of New Environments”). Synthetic LuaLaTeX probes
also pin the less obvious cases: unused arguments stay inert, an empty optional
argument overrides its default, unbraced parameters consume one token, and a
body-local definition changes neither its title nor the surrounding scope. -/
def tcolorboxScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  for (label, pre, body, control) in [
      ("unused installer",
        "\\newcommand{\\installpanel}[1]{\\newtcolorbox{panel}{title={#1}}}",
        "\\newtcolorbox{panel}{title={Fresh}}\\begin{panel}Body\\end{panel}",
        "\\begin{block}{Fresh}Body\\end{block}"),
      ("invoked installer",
        "\\newcommand{\\installpanel}[1]{\\newtcolorbox{panel}{title={#1}}}",
        "\\installpanel{Installed}\\begin{panel}Body\\end{panel}",
        "\\begin{block}{Installed}Body\\end{block}"),
      ("skipped declaration",
        "\\iffalse\\newtcolorbox{panel}{title={Hidden}}\\fi",
        "\\newtcolorbox{panel}{title={Fresh}}\\begin{panel}Body\\end{panel}",
        "\\begin{block}{Fresh}Body\\end{block}"),
      ("late title and font lookup",
        "\\newtcolorbox{panel}{title={\\headingprobe},fontupper=\\fontprobe}" ++
          "\\def\\headingprobe{Early}\\def\\fontprobe{\\small}",
        "\\begin{panel}First\\end{panel}" ++
          "\\def\\headingprobe{Late}\\def\\fontprobe{\\bfseries}" ++
          "\\begin{panel}Second\\end{panel} Outside",
        "\\begin{block}{Early}{\\small First}\\end{block}" ++
          "\\begin{block}{Late}{\\bfseries Second}\\end{block} Outside"),
      ("conditional lookup at each use",
        "\\newif\\ifchoiceprobe" ++
          "\\newtcolorbox{panel}{title={\\headingprobe},fontupper=\\fontprobe}" ++
          "\\def\\headingprobe{\\ifchoiceprobe Chosen\\else Default\\fi}" ++
          "\\def\\fontprobe{\\ifchoiceprobe\\bfseries\\else\\small\\fi}",
        "\\begin{panel}First\\end{panel}\\choiceprobetrue" ++
          "\\begin{panel}Second\\end{panel}",
        "\\begin{block}{Default}{\\small First}\\end{block}" ++
          "\\begin{block}{Chosen}{\\bfseries Second}\\end{block}"),
      ("title before local body definition",
        "\\def\\headingprobe{Outer}\\newtcolorbox{panel}{title={\\headingprobe}}",
        "\\begin{panel}\\def\\headingprobe{Inner}\\headingprobe\\end{panel} \\headingprobe",
        "\\begin{block}{Outer}Inner\\end{block} Outer"),
      ("unused default and explicit arguments",
        "\\newif\\ifusedprobe" ++
          "\\newtcolorbox{panel}[2][\\usedprobetrue]{title={#2}}",
        "\\begin{panel}{First}DefaultBody\\end{panel}" ++
          "\\begin{panel}[\\usedprobetrue]{Second}ExplicitBody\\end{panel}" ++
          "\\ifusedprobe Leaked\\else Inert\\fi",
        "\\begin{block}{First}DefaultBody\\end{block}" ++
          "\\begin{block}{Second}ExplicitBody\\end{block}Inert"),
      ("empty optional overrides default",
        "\\newtcolorbox{panel}[2][Default]{title={#1/#2}}",
        "\\begin{panel}[]{Empty}Body\\end{panel}",
        "\\begin{block}{/Empty}Body\\end{block}"),
      ("grouped optional value",
        "\\newtcolorbox{panel}[2][Default]{title={#1/#2}}",
        "\\begin{panel}[{Chosen, x={Y}}]{Grouped}Body\\end{panel}",
        "\\begin{block}{Chosen, x={Y}/Grouped}Body\\end{block}"),
      ("unbraced token arguments",
        "\\newtcolorbox{panel}[2]{title={#1/#2}}",
        "\\begin{panel}ABTail\\end{panel}",
        "\\begin{block}{A/B}Tail\\end{block}"),
      ("control token argument",
        "\\newtcolorbox{panel}[2]{title={#1/#2}}\\def\\argprobe{Expanded}",
        "\\begin{panel}\\argprobe{Second}Body\\end{panel}",
        "\\begin{block}{Expanded/Second}Body\\end{block}"),
      ("zero arity retains first body group",
        "\\newtcolorbox{panel}[0]{title={Zero}}",
        "\\begin{panel}{\\bfseries First} Rest\\end{panel} Outside",
        "\\begin{block}{Zero}{\\bfseries First} Rest\\end{block} Outside"),
      ("parameterized font and local body styles",
        "\\newtcolorbox{panel}[2]{title={#1},fontupper={#2}}",
        "\\begin{panel}{Heading}{\\small\\bfseries}" ++
          "{\\itshape First} Rest\n\nSecond\\end{panel} Outside",
        "\\begin{block}{Heading}{\\small\\bfseries " ++
          "{\\itshape First} Rest\n\nSecond}\\end{block} Outside")] do
    sourceCaseChecks ref fonts label pre body control
  for (label, enter, leave) in [
      ("brace", "{", "}"), ("begingroup", "\\begingroup", "\\endgroup")] do
    sourceCaseChecks ref fonts (label ++ " local declaration") ""
      (enter ++ "\\newtcolorbox{localpanel}{title={Local}}" ++
        "\\begin{localpanel}Body\\end{localpanel}" ++ leave ++
        "\\newtcolorbox{localpanel}{title={Fresh}}" ++
        "\\begin{localpanel}Restored\\end{localpanel}")
      ("{\\begin{block}{Local}Body\\end{block}}" ++
        "\\begin{block}{Fresh}Restored\\end{block}")
    sourceCaseChecks ref fonts (label ++ " local redefinition")
      "\\newtcolorbox{panel}{title={Outer},fontupper=\\small}"
      (enter ++ "\\renewtcolorbox{panel}{title={Inner},fontupper=\\bfseries}" ++
        "\\begin{panel}First\\end{panel}" ++ leave ++
        "\\begin{panel}Second\\end{panel}")
      ("{\\begin{block}{Inner}{\\bfseries First}\\end{block}}" ++
        "\\begin{block}{Outer}{\\small Second}\\end{block}")
  for (key, value) in [
      ("enhanced", ""), ("arc", "=2pt"),
      ("unknown", "={\\def\\hiddenprobe{Leaked}Secret, option}")] do
    sourceCaseChecks ref fonts ("unsupported " ++ key)
      ("\\newtcolorbox{panel}{title={Heading}," ++ key ++ value ++ "}")
      ("\\begin{panel}Body\\end{panel}" ++
        "\\ifdefined\\hiddenprobe Leaked\\else Inert\\fi")
      "\\begin{block}{Heading}Body\\end{block}Inert"
      (some .W0110) (some "\\begin") (some "panel")
  -- A refused declaration preserves the existing environment and argument
  -- signature; its warning belongs to the definer, never the later body.
  for (label, pre, body, control, command) in [
      ("builtin declaration refused",
        "\\newtcolorbox{itemize}{title={Discarded},fontupper=\\small}",
        "\\begin{itemize}\\item First\\item Second\\end{itemize}",
        "\\begin{itemize}\\item First\\item Second\\end{itemize}",
        "\\newtcolorbox"),
      ("undefined renewal refused",
        "\\renewtcolorbox{panel}[1]{title={#1},fontupper=\\small}",
        "\\newtcolorbox{panel}{title={Fresh}}\\begin{panel}Body\\end{panel}",
        "\\begin{block}{Fresh}Body\\end{block}",
        "\\renewtcolorbox"),
      ("existing declaration refused",
        "\\newtcolorbox{panel}[1]{title={Original: #1},fontupper=\\small}" ++
          "\\newtcolorbox{panel}[2][Discarded]{title={#1/#2},fontupper=\\bfseries}",
        "\\begin{panel}{Kept}Body\\end{panel}",
        "\\begin{block}{Original: Kept}{\\small Body}\\end{block}",
        "\\newtcolorbox")] do
    sourceCaseChecks ref fonts label pre body control (some .W0104) (some command)
  tcolorboxEffectChecks ref fonts

/-- A generated box scope cannot become a frame title argument. Omitting
the title and explicitly declaring an empty title ship identical complete
PDF pages and typed HTML, including styles after the scope closes. -/
def tcolorboxFrameChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let pre := "\\documentclass{beamer}\\theme{default}" ++
    "\\newtcolorbox{panel}[1]{title={#1},fontupper=\\small}" ++
    "\\begin{document}"
  for (name, body) in [
      ("direct", "\\begin{tcolorbox}[title={Heading}]Body\\end{tcolorbox}After"),
      ("defined", "\\begin{panel}{Heading}Body\\end{panel}After"),
      ("nested", "\\begin{panel}{Outer}\\begin{panel}{Inner}Body\\end{panel}\\end{panel}After"),
      ("title command", "\\begin{panel}{Heading}Body\\end{panel}\\frametitle{FrameTitle}After")] do
    for options in ["", "[t]", "[plain]"] do
      let source (title : String) := pre ++ "\\begin{frame}" ++ options ++ title ++
        body ++ "\\end{frame}\\end{document}"
      let (ds, actual, html, _) := sourceArtifacts fonts (source "")
      let (controlDs, expected, expectedHtml, _) := sourceArtifacts fonts (source "{}")
      let label := "tcolorbox frame: " ++ name ++ options
      check ref (label ++ ": explicit empty title is supported")
        (controlDs.all (·.severity == .note))
      check ref (label ++ ": generated scope is not a title argument")
        (ds.all (·.severity == .note))
      check ref (label ++ ": PDF pages")
        (reprStr actual.pages == reprStr expected.pages)
      check ref (label ++ ": typed HTML") (html == expectedHtml)

/-- Full declaration probes for the compatibility owner: options are
instantiated at use, including a default and a macro defined later. -/
def tcolorboxSourceChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let later := "\\newcommand{\\later}[1]{#1}"
  let source := "\\documentclass{beamer}\\theme{default}" ++
    "\\newtcolorbox{panel}[2][Default]{title={\\later{#1}: #2},fontupper=\\small\\bfseries}" ++
    later ++
    "\\begin{document}\\begin{frame}[t]{}" ++
    "\\begin{panel}{First}FirstBody\\end{panel}" ++
    "\\begin{panel}[Chosen]{Second}SecondBody\\end{panel}" ++
    "\\end{frame}\\end{document}"
  let (actual, ds) := elabStr source
  -- Keep the helper's native style identity in the control, including
  -- its PDF run boundaries and typed HTML spans.
  let expected := nativeDoc
    (later ++
     "\\begin{block}{\\later{Default}: First}{\\small\\bfseries FirstBody}\\end{block}" ++
     "\\begin{block}{\\later{Chosen}: Second}{\\small\\bfseries SecondBody}\\end{block}")
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
  tcolorboxScopeChecks ref fonts
  tcolorboxPreparationChecks ref fonts
  tcolorboxTitleBindingChecks ref fonts
  tcolorboxFrameChecks ref fonts

end TcolorboxChecks
