import Tests.Support

open LeanTex.Core

namespace Tests

private def linkCall (name content : String) : String :=
  "\\" ++ name ++ "{https://example.org/probe}{" ++ content ++ "}"

private def linkRow (name left right : String) : String :=
  let leftCall := linkCall name left
  let rightCall := linkCall name right
  leftCall ++ "\\hfill" ++ rightCall

private def linkBox (text : String) : String :=
  "\\begin{minipage}{.3\\textwidth}" ++ text ++ "\\end{minipage}"

/-- The active meaning owns argument consumption. Changing only an argument
that meaning discards cannot alter the shipped glyphs or the emitted HTML
structure. Keeping the definition in the control also checks its semantic role. -/
def linkMacroLayoutChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let agree (label source control : String) : IO Unit := do
    let (ds, out, html, text) := sourceArtifacts fonts source
    let (cs, expected, expectedHtml, _) := sourceArtifacts fonts control
    t (label ++ ": no error or unknown command")
      ((ds ++ cs).all fun d => d.severity != .error && d.code != "W0301")
    t (label ++ ": replacement survives and dead argument stays absent")
      (hasStr text "TOKEN" && !hasStr text "Discarded")
    t (label ++ ": discarded argument cannot change shipped geometry")
      (!(shippedBodyGlyphs out).isEmpty &&
        out.pages.size == expected.pages.size &&
        shippedBodyGlyphs out == shippedBodyGlyphs expected)
    t (label ++ ": discarded argument cannot change HTML") (html == expectedHtml)
    t (label ++ ": discarded argument cannot report a row conversion")
      ((ds.filter (·.subject == some "env:minipage-row")).size ==
        (cs.filter (·.subject == some "env:minipage-row")).size)
  for name in #["href", "link", "hyperlink", "hypertarget"] do
    for (definer, definition) in #[
        ("renewcommand", "\\renewcommand{\\" ++ name ++ "}[2]{TOKEN}\n"),
        ("def", "\\def\\" ++ name ++ "#1#2{TOKEN}\n"),
        ("define", "\\define \\" ++ name ++ "(target: text, body: content){TOKEN}\n")] do
      let pre := "\\usepackage{hyperref}\n" ++ definition
      let body (arg : String) := "Before " ++ linkCall name arg ++ " after."
      agree s!"link meaning {name}/{definer}: block argument"
        (dvDoc pre (body "Discarded.\\par Also discarded."))
        (dvDoc pre (body "Discarded."))
      let (_, tree, _) := HtmlDoc.emitTree {} (elabStr (dvDoc pre (body "Discarded."))).1
      t s!"link meaning {name}/{definer}: replacement keeps its HTML role"
        ((tree.flatMap (attrValuesOf (fun _ => true) "class")).any fun cls =>
          (cls.splitOn " ").contains (HtmlDoc.roleClass name))
      if name == "href" || name == "hyperlink" then
        agree s!"link meaning {name}/{definer}: row arguments"
          (dvDoc pre ("Before " ++ linkRow name (linkBox "Discarded A.")
            (linkBox "Discarded B.") ++ " after."))
          (dvDoc pre ("Before " ++ linkRow name "Discarded A." "Discarded B." ++ " after."))
  -- Native rows on both sides of a local override witness source order and
  -- restoration. Only the overridden calls change their discarded arguments.
  for name in #["href", "hyperlink"] do
    let native := linkRow name (linkBox "Left.") (linkBox "Right.")
    let definition := "\\renewcommand{\\" ++ name ++ "}[2]{TOKEN}"
    let body (left right : String) := native ++ "\\par {" ++ definition ++
      "Before " ++ linkRow name left right ++ " after.}\\par " ++ native
    let source := dvDoc "\\usepackage{hyperref}\n"
      (body (linkBox "Discarded A.") (linkBox "Discarded B."))
    let control := dvDoc "\\usepackage{hyperref}\n" (body "Discarded A." "Discarded B.")
    agree s!"link meaning {name}: source order and local restoration" source control
    let (_, tree, _) := HtmlDoc.emitTree {} (elabStr source).1
    let classes := tree.flatMap (attrValuesOf (fun _ => true) "class")
    let hrefs := tree.flatMap (attrValuesOf (· == "a") "href")
    t s!"link meaning {name}: native rows remain before and after the override"
      ((classes.filter (fun cls => (cls.splitOn " ").contains "columns")).size == 2 &&
        hrefs.size == 4)
  -- A linked block body starts a fresh accumulator while retaining its
  -- macro owner. Earlier paragraphs must not become offsets in that body.
  for name in #["href", "link", "hyperlink", "hypertarget"] do
    let source := dvDoc
      ("\\usepackage{hyperref}\n\\newcommand\\scopeprobe[1]{" ++
        linkCall name "#1\\par End." ++ "}")
      "Lead.\\par\\scopeprobe{Begin.}\\par Tail."
    let control := dvDoc
      ("\\usepackage{hyperref}\n\\define \\scopeprobe(a: content){" ++
        linkCall name "\\a\\par End." ++ "}")
      "Lead.\\par\\scopeprobe{Begin.}\\par Tail."
    let (ds, out, html, _) := sourceArtifacts fonts source
    let (cs, expected, expectedHtml, _) := sourceArtifacts fonts control
    t s!"link scope {name}: no error or unknown command"
      ((ds ++ cs).all fun d => d.severity != .error && d.code != "W0301")
    t s!"link scope {name}: fresh accumulator preserves shipped geometry"
      (shippedBodyGlyphs out == shippedBodyGlyphs expected)
    t s!"link scope {name}: fresh accumulator preserves HTML ownership"
      (html == expectedHtml)

end Tests
