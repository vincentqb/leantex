module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- A string test consumes its two inert operands and executes exactly one
branch in the caller's scope. Native controls retain complete page geometry
and the serialized typed HTML, including macro ownership and whitespace. -/
private def stringConditionalArtifacts (ref : IO.Ref (List String))
    (fonts : Font.FontSet) (label pre body control : String)
    (controlPre : Option String := none) : IO Unit := do
  let source := dvDoc ("\\pagestyle{empty}\\usepackage{etoolbox}" ++ pre) body
  let expectedSource := dvDoc
    ("\\pagestyle{empty}\\usepackage{etoolbox}" ++ controlPre.getD pre) control
  let (ds, actual, html, text) := sourceArtifacts fonts source
  let (cds, expected, expectedHtml, expectedText) := sourceArtifacts fonts expectedSource
  let t := check ref
  t s!"string conditional {label}: source supported" (ds.all (·.severity == .note))
  t s!"string conditional {label}: native control supported" (cds.all (·.severity == .note))
  t s!"string conditional {label}: shipped PDF pages" (reprStr actual.pages == reprStr expected.pages)
  t s!"string conditional {label}: typed HTML" (html == expectedHtml)
  t s!"string conditional {label}: visible text" (text == expectedText)

/-- Literal comparison witnesses measured under LuaLaTeX with etoolbox's
`\ifstrequal` (`etoolbox.sty`, string tests): both operands are detokenized
without expansion. Leading/trailing spaces and brace tokens remain, control
words carry their delimiter space, control symbols do not, and `#` doubles.
The expected branch is held by both artifacts, not an elaboration dump. -/
def stringConditionalChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let pre := "\\def\\leftprobe{Value}\\def\\rightprobe{Value}"
  for (label, left, right, equal) in #[
      ("empty", "", "", true),
      ("space is not empty", " ", "", false),
      ("same letters", "alpha", "alpha", true),
      ("different letters", "alpha", "beta", false),
      ("case sensitive", "Alpha", "alpha", false),
      ("leading space", " alpha", "alpha", false),
      ("trailing space", "alpha ", "alpha", false),
      ("interior space", "alpha beta", "alphabeta", false),
      ("lexer space token", "alpha   beta", "alpha beta", true),
      ("brace tokens", "a{b}", "ab", false),
      ("space inside braces", "{ a }", "{a}", false),
      ("same brace tokens", "{ a }", "{ a }", true),
      ("undefined control stays inert", "\\undefinedprobe", "\\undefinedprobe", true),
      ("same expansion is not same string", "\\leftprobe", "\\rightprobe", false),
      ("macro is not its expansion", "\\leftprobe", "Value", false),
      ("control word delimiters", "\\leftprobe   x", "\\leftprobe x", true),
      ("empty group is significant", "\\leftprobe{}x", "\\leftprobe x", false),
      ("control symbol preserves following space", "\\%x", "\\% x", false),
      ("same control symbol", "\\%x", "\\%x", true),
      ("parameter count", "#", "##", false),
      ("same parameter", "#", "#", true),
      ("math spelling", "$x$", "\\(x\\)", false),
      ("same math spelling", "$x$", "$x$", true)] do
    let yes := "\\textbf{Chosen}"
    let no := "\\textit{Other}"
    stringConditionalArtifacts ref fonts label pre
      ("A\\ifstrequal{" ++ left ++ "}{" ++ right ++ "}{" ++ yes ++ "}{" ++ no ++ "}Z")
      ("A" ++ (if equal then yes else no) ++ "Z")

  stringConditionalArtifacts ref fonts "operand assignments stay inert"
    "\\newif\\ifchoiceprobe"
    ("\\ifstrequal{\\choiceprobetrue}{\\choiceprobetrue}{Chosen}{Other}/" ++
      "\\ifchoiceprobe Set\\else Clear\\fi")
    "Chosen/Clear"
  stringConditionalArtifacts ref fonts "operand global definitions stay inert" ""
    ("\\ifstrequal{\\global\\def\\hiddenprobe{Leaked}}{\\global\\def\\hiddenprobe{Leaked}}" ++
      "{Chosen}{Other}/\\ifdefined\\hiddenprobe Leaked\\else Clear\\fi")
    "Chosen/Clear"
  for (label, left, right, yes, no, expected) in #[
      ("nested true branch", "x", "x", "\\ifstrequal{a}{b}{Wrong}{Chosen}", "Wrong", "Chosen"),
      ("nested false branch", "x", "y", "Wrong", "\\ifstrequal{a}{a}{Chosen}{Wrong}", "Chosen"),
      ("false branch inert", "x", "x", "Chosen", "\\global\\def\\hiddenprobe{Leaked}", "Chosen"),
      ("true branch inert", "x", "y", "\\global\\def\\hiddenprobe{Leaked}", "Chosen", "Chosen")] do
    stringConditionalArtifacts ref fonts label ""
      ("\\ifstrequal{" ++ left ++ "}{" ++ right ++ "}{" ++ yes ++ "}{" ++ no ++ "}/" ++
        "\\ifdefined\\hiddenprobe Leaked\\else Clear\\fi")
      (expected ++ "/Clear")
  stringConditionalArtifacts ref fonts "primitive conditional nesting" ""
    "\\iftrue A\\ifstrequal{x}{y}{Wrong}{Chosen}Z\\else Wrong\\fi"
    "AChosenZ"
  stringConditionalArtifacts ref fonts "unselected branch does not execute" ""
    "\\ifstrequal{x}{x}{Chosen}{\\unknownprobe{Wrong}}"
    "Chosen"
  stringConditionalArtifacts ref fonts "selected branch is not a new scope"
    "\\newif\\ifchoiceprobe"
    "\\ifstrequal{x}{x}{\\choiceprobetrue Chosen}{Wrong}/\\ifchoiceprobe Set\\else Clear\\fi"
    "Chosen/Set"
  stringConditionalArtifacts ref fonts "explicit selected group is local"
    "\\newif\\ifchoiceprobe"
    ("\\ifstrequal{x}{y}{Wrong}{{\\choiceprobetrue\\ifchoiceprobe Set\\else Wrong\\fi}}/" ++
      "\\ifchoiceprobe Wrong\\else Clear\\fi")
    "Set/Clear"
  for (left, right, yes, no) in #[
      ("x", "x", "\\gdef\\valueprobe{Chosen}", "\\def\\valueprobe{Wrong}"),
      ("x", "y", "\\def\\valueprobe{Wrong}", "\\gdef\\valueprobe{Chosen}")] do
    stringConditionalArtifacts ref fonts ("selected global definition " ++ right) ""
      ("{\\ifstrequal{" ++ left ++ "}{" ++ right ++ "}{" ++ yes ++ "}{" ++ no ++ "}}\\valueprobe")
      "{\\gdef\\valueprobe{Chosen}}\\valueprobe"
  stringConditionalArtifacts ref fonts "selected preamble definition"
    "\\ifstrequal{x}{y}{\\def\\valueprobe{Wrong}}{\\def\\valueprobe{Chosen}}"
    "\\valueprobe" "Chosen" (some "\\def\\valueprobe{Chosen}")
  stringConditionalArtifacts ref fonts "helper runs at each use"
    ("\\newif\\ifchoiceprobe\\def\\chooseprobe{" ++
      "\\ifstrequal{x}{x}{\\choiceprobetrue Chosen}{Wrong}}")
    ("\\chooseprobe/\\ifchoiceprobe Set\\else Wrong\\fi/" ++
      "\\choiceprobefalse\\chooseprobe/\\ifchoiceprobe Set\\else Wrong\\fi")
    "Chosen/Set/Chosen/Set"
  stringConditionalArtifacts ref fonts "parameterized title helper"
    "\\newcommand\\headingprobe[1]{\\ifstrequal{#1}{alpha}{\\textbf{Chosen}}{\\textit{Other}}}"
    "\\begin{block}{\\headingprobe{alpha}}Body\\end{block}"
    "\\begin{block}{\\headingprobe{\\textbf{Chosen}}}Body\\end{block}"
    (some "\\define\\headingprobe(a: content){\\a}")
  for (argument, title) in #[("alpha", "\\textbf{Chosen}"), ("beta", "\\textit{Other}")] do
    stringConditionalArtifacts ref fonts ("content box title " ++ argument)
      ("\\newcommand\\headingprobe[1]{" ++
        "\\ifstrequal{#1}{alpha}{\\textbf{Chosen}}{\\textit{Other}}}" ++
        "\\newtcolorbox{panel}[1]{title={\\headingprobe{#1}}}")
      ("\\begin{panel}{" ++ argument ++ "}Body\\end{panel}")
      ("\\begin{block}{\\headingprobe{" ++ title ++ "}}Body\\end{block}")
      (some "\\define\\headingprobe(a: content){\\a}")

end Tests
