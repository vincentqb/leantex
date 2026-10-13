module

public import Tests.Backends

public section

/-! Guards for reported breakages whose fix landed without one, each failing on the reported
tree. -/

open LeanTex.Core

mutual

/-- The deck stages in an emitted tree, and how many stand inside another stage. -/
def stagesOne (inStage : Bool) (acc : Nat × Nat) : Html.Node → Nat × Nat
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let stage := tag == "section" &&
      (HtmlDoc.classTokens attrs).any (fun c => c == "slide" || c == "section-page")
    let acc := if stage then (acc.1 + 1, if inStage then acc.2 + 1 else acc.2) else acc
    stagesList (inStage || stage) acc kids.toList

def stagesList (inStage : Bool) (acc : Nat × Nat) : List Html.Node → Nat × Nat
  | [] => acc
  | k :: rest => stagesList inStage (stagesOne inStage acc k) rest

end

/-- A page model nests no page: a title page inside the author's own frame is one stage. -/
def nestedStageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (arts : Array GoldenArt) : IO Unit := do
  let t := check ref
  let pre := "\\title{An Invented Title}\\author{A. Placeholder}"
  let next := "\n\\begin{frame}{Next}\nx\n\\end{frame}"
  let stages (body cls : String) : Nat × Nat × Nat :=
    let (doc, _) := elabStr (cls ++ "\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ next ++
      "\n\\end{document}")
    let (_, tree, _) := HtmlDoc.emitTree {} doc
    let (n, nested) := stagesList false (0, 0) tree.toList
    (n, nested, (layoutOf oneFace doc).pages.size)
  let classes := [("slides", "\\documentclass[aspectratio=169]{slides}"),
    ("beamer", "\\documentclass{beamer}")]
  for (name, cls) in classes do
    for (idiom, body) in [("titlepage", "\\begin{frame}\n\\titlepage\n\\end{frame}"),
        ("plain titlepage", "\\begin{frame}[plain]\n\\titlepage\n\\end{frame}"),
        ("maketitle", "\\begin{frame}\n\\maketitle\n\\end{frame}")] do
      let (n, nested, pages) := stages body cls
      t s!"a {idiom} inside its own frame is one stage \
({name}: {n} stages, {nested} nested, {pages} pages)"
        (nested == 0 && n == pages && pages == 2)
  let mut seen := 0
  for a in arts do
    let (_, tree, _) := HtmlDoc.emitTree {} a.doc
    let (n, nested) := stagesList false (0, 0) tree.toList
    seen := seen + n
    t s!"{a.name}: no stage stands inside a stage ({nested} of {n})" (nested == 0)
  t s!"the corpus ships stages, so the walk above can see one ({seen})" (seen > 0)
  -- Parked on `Elab.flattenFrame`: a titled frame around the title page still nests; the row fails once it does not.
  let (n, nested, pages) := stages "\\begin{frame}{Welcome}\n\\titlepage\n\\end{frame}"
    "\\documentclass[aspectratio=169]{slides}"
  t s!"parked: a titled frame around a title page still nests a stage \
({n} stages, {nested} nested, {pages} pages)" (nested == 1)
