import Tests.Backends

/-!
# Guards for reported breakages that shipped without one

Each block reproduces one report of `Tests/Reports.lean` whose fix landed
with no check, asserted over the artifact, and failing on the tree the
report was about.
-/

open LeanTex.Core

mutual

/-- The deck stages in an emitted tree, and how many of them stand inside
another stage: a `section` classed `slide` or `section-page`, the element the
paged deck sizes to the viewport. -/
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

/-- **A page model nests no page: a title page inside the author's own frame
is one stage.** The report: a deck's HTML front page rendered nearly blank,
its title matter a full viewport down, while its PDF page was right — the
title arm opened a frame inside the frame the author wrote, and each became a
viewport-high stage. Over the typed HTML tree: for each spelling of the idiom
in both slide classes, no stage stands inside a stage and the HTML has as
many stages as the PDF has pages; and no golden fixture nests a stage. -/
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
  -- Parked, owed by `Elab.flattenFrame`: a *titled* frame around the title
  -- page keeps its nesting, so this spelling still ships a stage inside a
  -- stage (and a PDF page of its own for the outer frame, where beamer sets
  -- one page). The row fails once the flatten reaches it; delete it then.
  let (n, nested, pages) := stages "\\begin{frame}{Welcome}\n\\titlepage\n\\end{frame}"
    "\\documentclass[aspectratio=169]{slides}"
  t s!"parked: a titled frame around a title page still nests a stage \
({n} stages, {nested} nested, {pages} pages)" (nested == 1)
