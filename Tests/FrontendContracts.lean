import LeanTex.Core.Elab

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
