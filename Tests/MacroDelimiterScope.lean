module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- Delimiter signatures follow execution scope: a real group or environment
restores its incoming locals and retains every explicit global write, even
one later shadowed locally. Input wrappers are transparent; top-level hook
definitions persist in preamble, end-hook, begin-hook, body order. A refused
call still ships its braced recovery in both complete artifacts. -/
def macroDelimiterScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let article (pre body : String) := dvDoc (r"\pagestyle{empty}" ++ pre) body
  let losses := ["W0357", "W0301"]
  let same (label : String)
      (actual expected : Array Diag × Layout.Out × String × String) : IO Unit := do
    let (ds, out, html, _) := actual
    let (cds, cout, chtml, ctext) := expected
    let named (ds : Array Diag) :=
      ds.all (fun d => d.severity == .note || losses.contains d.code)
    t (label ++ ": source has only the declared losses") (named ds)
    t (label ++ ": control has only the declared losses") (named cds)
    for code in losses do
      t (label ++ ": names " ++ code) (ds.any (·.code == code))
    t (label ++ ": control ships visible content")
      (!(bodyLines cout).isEmpty && !ctext.trimAscii.isEmpty)
    t (label ++ ": complete PDF layout agrees") (reprStr out.pages == reprStr cout.pages)
    t (label ++ ": complete typed HTML agrees") (html == chtml)
  let outer := r"\def\scanprobe#1;{#1}"
  let inner := r"\def\scanprobe#1.{#1}"
  let semicolonBody := r"Lead \scanprobe A; Tail."
  let periodBody := r"Lead \scanprobe A. Tail;"
  for (label, pre, body, cpre, cbody) in #[
      ("brace-local hook", outer ++ r"\AtBeginDocument{{" ++ inner ++ "}}",
        semicolonBody, outer ++ r"\AtBeginDocument{{}}", semicolonBody),
      ("environment-local hook",
        outer ++ r"\AtBeginDocument{\begin{center}" ++ inner ++ r"\end{center}}",
        semicolonBody, outer ++ r"\AtBeginDocument{\begin{center}\end{center}}",
        semicolonBody),
      ("body scope uses then restores", outer,
        "{" ++ inner ++ r"Inner \scanprobe X. End.} " ++ semicolonBody,
        outer, r"{Inner \scanprobe{X} End.} " ++ semicolonBody),
      ("environment scope uses then restores", outer,
        r"\begin{center}" ++ inner ++ r"Inner \scanprobe X. End.\end{center}" ++
          semicolonBody,
        outer, r"\begin{center}Inner \scanprobe{X} End.\end{center}" ++ semicolonBody),
      ("top-level hook persists", outer ++ r"\AtBeginDocument{" ++ inner ++ "}",
        periodBody, inner ++ r"\AtBeginDocument{}", periodBody),
      ("gdef escapes braces", outer ++ r"\AtBeginDocument{{\gdef\scanprobe#1.{#1}}}",
        periodBody, inner ++ r"\AtBeginDocument{{}}", periodBody),
      ("gdef escapes environment",
        outer ++ r"\AtBeginDocument{\begin{center}\gdef\scanprobe#1.{#1}\end{center}}",
        periodBody, inner ++ r"\AtBeginDocument{\begin{center}\end{center}}", periodBody),
      ("global def escapes braces",
        outer ++ r"\AtBeginDocument{{\global\def\scanprobe#1.{#1}}}",
        periodBody, inner ++ r"\AtBeginDocument{{}}", periodBody),
      ("global survives later local",
        outer ++ r"\AtBeginDocument{{\gdef\scanprobe#1.{#1}\def\scanprobe#1!{#1}}}",
        periodBody, inner ++ r"\AtBeginDocument{{}}", periodBody),
      ("global survives nested restoration",
        outer ++ r"\AtBeginDocument{{{\gdef\scanprobe#1.{#1}}\def\scanprobe#1!{#1}}}",
        periodBody, inner ++ r"\AtBeginDocument{{{}}}", periodBody),
      ("last global survives local shadow",
        outer ++ r"\AtBeginDocument{{\gdef\scanprobe#1!{#1}\gdef\scanprobe#1.{#1}" ++
          r"\def\scanprobe#1;{#1}}}",
        periodBody, inner ++ r"\AtBeginDocument{{}}", periodBody),
      ("older global does not overwrite enclosing local",
        r"\AtBeginDocument{\gdef\scanprobe#1!{#1}{" ++ outer ++ "{" ++ inner ++
          r"}Inner \scanprobe X; Tail.}}",
        r"Outer \scanprobe A! Tail.",
        r"\AtBeginDocument{\gdef\scanprobe#1!{#1}{" ++ outer ++
          r"{}Inner \scanprobe{X} Tail.}}",
        r"Outer \scanprobe A! Tail."),
      ("inert definer body cannot write globally",
        outer ++ r"\AtBeginDocument{\def\unusedprobe#1{\gdef\scanprobe##1.{##1}}}",
        semicolonBody, outer ++ r"\AtBeginDocument{\def\unusedprobe#1{}}",
        semicolonBody),
      ("phase order with scoped begin hook",
        r"\usepackage{etoolbox}" ++ inner ++
          r"\AtBeginDocument{{" ++ inner ++ r"}Begin \scanprobe B; Tail.}" ++
          r"\AtEndPreamble{}" ++ outer,
        "Body " ++ inner ++ r"\scanprobe C. Tail;",
        r"\usepackage{etoolbox}" ++ inner ++
          r"\AtBeginDocument{{}Begin \scanprobe{B} Tail.}\AtEndPreamble{}" ++ outer,
        "Body " ++ inner ++ r"\scanprobe{C} Tail;"),
      ("end-hook definition reaches begin hook and body",
        r"\usepackage{etoolbox}" ++ inner ++
          r"\AtBeginDocument{{" ++ inner ++ r"}Begin \scanprobe B; Tail.}" ++
          r"\AtEndPreamble{" ++ outer ++ "}",
        semicolonBody,
        r"\usepackage{etoolbox}" ++ outer ++
          r"\AtBeginDocument{{}Begin \scanprobe{B} Tail.}\AtEndPreamble{}",
        semicolonBody)] do
    same ("delimiter scope " ++ label)
      (sourceArtifacts fonts (article pre body))
      (sourceArtifacts fonts (article cpre cbody))
  let sub (src : String) : Array Parse.Raw := (Parse.parse "t" (Lex.lex "t" src).1).1
  for (label, raws, expected) in #[
      ("input definition persists",
        sub (r"\documentclass{article}\pagestyle{empty}" ++ outer) ++
          #[Parse.Raw.env (Parse.inputEnv "probe.tex") (sub inner) { line := 1, col := 1 }] ++
          sub (r"\begin{document}" ++ periodBody ++ r"\end{document}"),
        article inner periodBody),
      ("input respects enclosing group",
        sub (r"\documentclass{article}\pagestyle{empty}" ++ outer) ++
          #[Parse.Raw.env "document"
            (#[Parse.Raw.group
              #[Parse.Raw.env (Parse.inputEnv "probe.tex") (sub inner) { line := 1, col := 1 }]
                { line := 1, col := 1 }] ++
              sub semicolonBody ++ #[.space]) { line := 1, col := 1 }],
        article outer ("{}" ++ semicolonBody))] do
    let (doc, ds) := Elab.runRaws "t" raws
    let out := layoutOf fonts doc
    let (head, tree, hds) := HtmlDoc.emitTree {} doc
    same ("delimiter scope " ++ label)
      (ds ++ out.diags ++ hds, out, Html.document "en" head tree,
        shownTextList "" tree.toList)
      (sourceArtifacts fonts expected)

end Tests
