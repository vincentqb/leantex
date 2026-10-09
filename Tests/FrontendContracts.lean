module

public import LeanTex.Core.TitleContract

public section

open LeanTex.Core

/-- The title reader's boundary is a refused body. These contexts exercise
its nested declarative syntax and its lookahead operands; the conditional
counterexample remains in `elabTitleBoundaryChecks`. -/
def frontendTitleContextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let contexts : Array (String × String) :=
    #[("\\centering\\large\\bfseries\\hrule ", "\\hrule"),
      ("{\\large\\bfseries ", "}\\hrule"),
      ("\\begin{center}\\hrule ", "\\hrule\\end{center}"),
      ("\\vskip -", "\\hrule"),
      ("\\hrule height 4", "\\hrule")]
  let source (body : String) :=
    "\\documentclass{article}\\title{Title}\\author{Author}\\date{Date}" ++
      "\\renewcommand{\\maketitle}{" ++ body ++ "}" ++
      "\\style{titlepage}{align=right}" ++
      "\\begin{document}\\maketitle\\end{document}"
  for (aliasName, internal) in Elab.beamerInsertAlias do
    for (pre, post) in contexts do
      let left ← pure (Elab.run "probe.tex" (source (pre ++ "\\" ++ aliasName ++ post)))
      let right ← pure (Elab.run "probe.tex" (source (pre ++ "\\" ++ internal ++ post)))
      t s!"title context: {aliasName} preserves the merged style"
        (left.1.styles.find? "titlepage" == right.1.styles.find? "titlepage")
      t s!"title context: {aliasName} preserves explicit document precedence"
        (((left.1.styles.find? "titlepage").bind (·.align)) == some "right")
  -- Reading a refused body is a once-only preamble operation, including a
  -- body that declares no supported styling. Keeping that payload in the
  -- body interpreter would leave its spelling observable after its reader.
  let st : Elab.ESt :=
    { refusedTitleBody := some #[.word "no-declarative-title-style" {}] }
  t "title completion retires a body with no supported style"
    (((Elab.applyRefusedTitleStyle { ctx := { file := "probe.tex" } }).run st).2.refusedTitleBody.isNone)
  let contexts : Array Elab.TitleBodyContext :=
    #[.hole,
      .around #[.ctrl "centering" {}, .ctrl "large" {}, .ctrl "hrule" {}]
        #[.ctrl "hrule" {}] .hole,
      .group (.around #[.ctrl "bfseries" {}] #[.ctrl "hrule" {}] .hole) {},
      .env "center" (.around #[.ctrl "hrule" {}] #[.ctrl "hrule" {}] .hole) {}]
  for suffix in #["", "\\begin{tikzpicture}\\draw (0,0) -- (1,0);\\end{tikzpicture}"] do
    let src := "\\documentclass{article}\\title{Title}\\author{Author}" ++
      "\\renewcommand{\\maketitle}{\\@title}\\style{titlepage}{align=right}" ++
      "\\begin{document}\\maketitle\\ref{missing}" ++ suffix ++ "\\end{document}"
    let (tokens, lexDs) := Lex.lex "probe.tex" src
    let (raws, parseDs) := Parse.parse "probe.tex" tokens
    let prepared := Elab.prepare "probe.tex" raws
    let metric : Ir.Pic.LabelMetric := fun _ _ => {}
    let finish (body : Array Parse.Raw) := Elab.finishPreparedRuns fun withdrawn =>
      let phase := Elab.preparedPreamble "probe.tex" prepared metric withdrawn
      Elab.runPreamble "probe.tex" prepared (lexDs ++ parseDs) phase.1
        { phase.2 with refusedTitleBody := some body }
    for (aliasName, internal) in Elab.beamerInsertAlias do
      for context in contexts do
        let left ← pure (finish (context.fill (.ctrl aliasName {})))
        let right ← pure (finish (context.fill (.ctrl internal {})))
        t s!"title completion: {aliasName} preserves the whole document and final log"
          (left == right)
        t s!"title completion: {aliasName} retains final reference accounting"
          (left.2.any (fun d => d.kind == .W0349 && d.subject == some "missing"))
