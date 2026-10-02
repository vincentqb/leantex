import Tests.Support

open LeanTex.Core

namespace TitlePageLifecycle

private structure Case where
  name : String
  body : String
  pages : Array String
  folios : Array (Option Nat)

/-- Synthetic article probes, checked against LuaLaTeX: classes.dtx's
titlepage opens with thispagestyle empty and page = 1, then resets page = 1
after its closing newpage in oneside mode. Empty style expires at shipout,
not at an environment boundary or a newpage that ships nothing. -/
private def cases : Array Case := #[
  { name := "leading"
    body := "\\begin{titlepage}Title.\\end{titlepage}After.\\newpage Later."
    pages := #["Title.", "After.", "Later."]
    folios := #[none, some 1, some 2] },
  { name := "middle"
    body := "Before.\\newpage Prior.\\begin{titlepage}Title.\\end{titlepage}" ++
      "After.\\newpage Later."
    pages := #["Before.", "Prior.", "Title.", "After.", "Later."]
    folios := #[some 1, some 2, none, some 1, some 2] },
  { name := "multipage"
    body := "Before.\\begin{titlepage}Title.\\newpage Continue.\\newpage Third." ++
      "\\end{titlepage}After.\\newpage Later."
    pages := #["Before.", "Title.", "Continue.", "Third.", "After.", "Later."]
    folios := #[some 1, none, some 2, some 3, some 1, some 2] },
  { name := "empty"
    body := "Before.\\begin{titlepage}\\end{titlepage}After.\\newpage Later."
    pages := #["Before.", "After.", "Later."]
    folios := #[some 1, none, some 2] },
  { name := "leading empty"
    body := "\\begin{titlepage}\\end{titlepage}After.\\newpage Later."
    pages := #["After.", "Later."]
    folios := #[none, some 2] },
  { name := "repeated"
    body := "Before.\\begin{titlepage}First.\\end{titlepage}Between." ++
      "\\begin{titlepage}Second.\\end{titlepage}After."
    pages := #["Before.", "First.", "Between.", "Second.", "After."]
    folios := #[some 1, none, some 1, none, some 1] },
  { name := "trailing"
    body := "Before.\\begin{titlepage}Title.\\end{titlepage}"
    pages := #["Before.", "Title."]
    folios := #[some 1, none] },
  { name := "adjacent breaks"
    body := "Before.\\newpage\\begin{titlepage}\\newpage Title.\\newpage" ++
      "\\end{titlepage}\\newpage After."
    pages := #["Before.", "Title.", "After."]
    folios := #[some 1, none, some 1] }]

private def page : String :=
  "\\page{ width = 420pt, height = 600pt, hmargin = 54pt, vmargin = 48pt }\n"

private def furniture (out : Layout.Out) (i : Nat) : Array String :=
  ((out.pages[i]?.map (·.lines)).getD #[]).filterMap fun line =>
    if line.furniture then some (lineText line (gapAsSpace := false)) else none

private def bodyText (out : Layout.Out) (i : Nat) : String :=
  String.intercalate " " <|
    (((out.pages[i]?.map (·.lines)).getD #[]).filterMap fun line =>
      if line.furniture then none else some (lineText line)).toList

mutual

private def tagsOne (acc : Array String) : Html.Node → Array String
  | .text _ | .style _ | .script _ _ => acc
  | .elem tag _ kids => tagsList (acc.push tag) kids.toList

private def tagsList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | node :: rest => tagsList (tagsOne acc node) rest

end

end TitlePageLifecycle

/-- Artifact guards for article titlepage's page-local empty style and folio
resets. Running furniture is read from shipped glyphs; continuous HTML is
read as typed nodes, with every body paragraph and its order preserved. -/
def titlePageLifecycleChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for c in TitlePageLifecycle.cases do
    for custom in [false, true] do
      let label := s!"titlepage lifecycle {c.name} ({if custom then "declared" else "plain"})"
      let running := if custom then
        "\\runninghead{Head\\pagenumber}" ++
        "\\runningfoot{Foot\\pagenumber/\\pagecount}" else ""
      let (doc, ds) := elabStr (dvDoc (TitlePageLifecycle.page ++ running) c.body)
      let out := layoutOf oneFace doc
      t (label ++ ": no recovery cascade")
        (ds.all fun d => d.severity != .error &&
          !["W0301", "W0302", "E0336", "E0311"].contains d.code)
      t (label ++ ": physical page count") (out.pages.size == c.pages.size)
      for i in [0:c.pages.size] do
        t s!"{label}: body on physical page {i + 1}"
          (TitlePageLifecycle.bodyText out i == c.pages[i]!)
        let expected := match c.folios[i]! with
          | none => #[]
          | some n => if custom then #[s!"Head{n}", s!"Foot{n}/{c.pages.size}"]
            else #[toString n]
        t s!"{label}: running glyphs on physical page {i + 1}"
          (TitlePageLifecycle.furniture out i == expected)
      let (_, tree, _) := HtmlDoc.emitTree {} doc
      let control := dvDoc TitlePageLifecycle.page
        (String.intercalate "\n\n" c.pages.toList)
      let (_, controlTree, _) := HtmlDoc.emitTree {} (elabStr control).1
      t (label ++ ": continuous typed HTML preserves body and order")
        (shownTextList "" tree.toList == shownTextList "" controlTree.toList)
      t (label ++ ": continuous typed HTML keeps the control's element structure")
        (TitlePageLifecycle.tagsList #[] tree.toList ==
          TitlePageLifecycle.tagsList #[] controlTree.toList)
  -- Physical `from` gates and total pages keep their existing meaning when
  -- the folio resets: after the titlepage, page four is still physical four.
  let (gdoc, _) := elabStr (dvDoc
    (TitlePageLifecycle.page ++
      "\\runninghead[from=4]{Head\\pagenumber}" ++
      "\\runningfoot[from=5]{Foot\\pagenumber/\\pagecount}\\logo{Mark}")
    "Before.\\newpage Prior.\\begin{titlepage}Title.\\end{titlepage}After.\\newpage Later.")
  let gated := layoutOf oneFace gdoc
  t "titlepage lifecycle: physical furniture gates keep earlier pages clear"
    ((List.range 3).all fun i => TitlePageLifecycle.furniture gated i == #[])
  t "titlepage lifecycle: physical head gate reads the reset folio"
    (TitlePageLifecycle.furniture gated 3 == #["Head1"])
  t "titlepage lifecycle: physical foot and logo gates restore the running band"
    (TitlePageLifecycle.furniture gated 4 == #["Head2", "Foot2/5", "Mark"])
  let (ldoc, _) := elabStr (dvDoc
    (TitlePageLifecycle.page ++
      "\\runninghead{Head\\pagenumber}\\runningfoot{Foot\\pagenumber}\\logo{Mark}")
    "Before.\\begin{titlepage}Title.\\end{titlepage}After.")
  let logo := layoutOf oneFace ldoc
  t "titlepage lifecycle: titlepage suppresses declared head foot and logo together"
    (TitlePageLifecycle.furniture logo 1 == #[])
  t "titlepage lifecycle: titlepage restores declared head foot and logo"
    (TitlePageLifecycle.furniture logo 2 == #["Head1", "Foot1", "Mark"])
  -- Automatic pagination consumes empty style at the same shipment boundary
  -- as an explicit newpage. The title body must span at least three pages.
  let titleBody := String.intercalate "\n\n"
    ((List.range 24).map fun i => s!"Entry {i + 1}.")
  let (sdoc, _) := elabStr (dvDoc
    ("\\page{ width = 420pt, height = 180pt, hmargin = 54pt, vmargin = 48pt }\n" ++
      "\\runninghead{Head\\pagenumber}\\runningfoot{Foot\\pagenumber}")
    ("\\begin{titlepage}" ++ titleBody ++ "\\end{titlepage}After."))
  let spill := layoutOf oneFace sdoc
  t "titlepage lifecycle: synthetic overflow exercises several title pages"
    (spill.pages.size >= 4)
  t "titlepage lifecycle: first overflow page suppresses running furniture"
    (TitlePageLifecycle.furniture spill 0 == #[])
  for i in [1:spill.pages.size - 1] do
    t s!"titlepage lifecycle: overflow page {i + 1} restores advancing folio"
      (TitlePageLifecycle.furniture spill i == #[s!"Head{i + 1}", s!"Foot{i + 1}"])
  t "titlepage lifecycle: post-overflow body resets to folio one"
    (TitlePageLifecycle.bodyText spill (spill.pages.size - 1) == "After." &&
      TitlePageLifecycle.furniture spill (spill.pages.size - 1) == #["Head1", "Foot1"])
