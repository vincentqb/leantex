import Tests.Support

open LeanTex.Core

namespace Tests

private def listSource (kind decls first second : String) : String :=
  metricDoc ("\\begin{" ++ kind ++ "}\n" ++ decls ++
    "\n\\item " ++ first ++ "\n\\item " ++ second ++
    "\n\\end{" ++ kind ++ "}\n\\par Outside.")

private def bodyTree (doc : Ir.Doc) : String :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  Html.document "en" #[] body

/-- Formatting before the first item scopes all items but no following
text. Compare the actual page and typed HTML tree with the same declaration
at the start of each item; a declaration is never itself list content. -/
def listDeclarationChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  for kind in ["itemize", "enumerate", "description"] do
    for (name, _) in Elab.declStyles do
      let decl := "\\" ++ name ++ " "
      let (doc, ds) := elabStr (listSource kind decl "Alpha" "Beta")
      let expected := (elabStr (listSource kind "" (decl ++ "Alpha") (decl ++ "Beta"))).1
      t s!"list prefix {kind}/{name}: a declaration is not stray content"
        (!ds.any (·.code == "E0310"))
      t s!"list prefix {kind}/{name}: shipped glyphs preserve the item spelling"
        (shippedBodyGlyphs (layoutOf fonts doc) ==
          shippedBodyGlyphs (layoutOf fonts expected))
      t s!"list prefix {kind}/{name}: typed HTML preserves the item spelling"
        (bodyTree doc == bodyTree expected)
  let pairs := [
    ("size overridden in one item", "\\small", "{\\Large Alpha}", "Beta",
      "\\small{\\Large Alpha}", "\\small Beta"),
    ("composed axes", "\\small\\bfseries\\itshape", "Alpha", "Beta",
      "\\small\\bfseries\\itshape Alpha", "\\small\\bfseries\\itshape Beta"),
    ("literal punctuation", "\\ttfamily", "a--b", "c---d",
      "\\ttfamily a--b", "\\ttfamily c---d"),
    ("explicit font size", "\\fontsize{12pt}{18pt}\\selectfont", "Alpha", "Beta",
      "\\fontsize{12pt}{18pt}\\selectfont Alpha",
      "\\fontsize{12pt}{18pt}\\selectfont Beta")]
  for (label, decls, first, second, expectedFirst, expectedSecond) in pairs do
    let (doc, ds) := elabStr (listSource "itemize" decls first second)
    let expected := (elabStr (listSource "itemize" "" expectedFirst expectedSecond)).1
    t s!"list prefix {label}: no stray-content error" (!ds.any (·.code == "E0310"))
    t s!"list prefix {label}: actual PDF glyphs and restoration agree"
      (shippedBodyGlyphs (layoutOf fonts doc) ==
        shippedBodyGlyphs (layoutOf fonts expected))
    t s!"list prefix {label}: typed HTML and restoration agree"
      (bodyTree doc == bodyTree expected)
  for stray in ["Stray text", "\\textbf{Stray}", "\\zzunknown{Stray}"] do
    let (_, ds) := elabStr (listSource "itemize" stray "Alpha" "Beta")
    t s!"list prefix rejects actual content: {stray}" (ds.any (·.code == "E0310"))

end Tests
