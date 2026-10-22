module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.MystDialect

/-- An invented MyST document: a front matter only MyST reads, then `body`. -/
private def myst (body : String) : String :=
  "---\ntitle: Kilo Lima\nkernelspec:\n  name: python3\n---\n\n" ++ body

/-- MyST's markdown, read where a front matter names a key only MyST reads: formulas between
dollars, its math and citation roles, and references to a heading's target set as the heading's
text, as MyST sets an unnumbered heading's. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  t "myst: a front matter key only MyST reads selects its dialect, any other the document's"
    (Md.dialectOf (myst "Body.") == .myst && Md.dialectOf "---\ntitle: K\n---\n\nBody." == .document &&
      Md.dialectOf "Body." == .document)
  let page (src : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabMd src
    (censusOf #[] (layoutOf oneFace doc), ds)
  let (c, ds) := page (myst ("(intro)=\n# Papa\n\nA formula $x^2$ and {math}`y_1`.\n\n" ++
    "See [](#intro), {ref}`intro` and {ref}`the opening <intro>`; {abbr}`Q (Quebec)`.\n"))
  -- MyST sets "See Papa, Papa and the opening", the formulas as math, the unknown role's text
  t s!"myst: formulas, roles and references to a heading's target as its text ({censusText c})"
    (pageHas c 0 "See Papa, Papa and the opening;" && !pageHas c 0 "$x" && !pageHas c 0 "{math}" &&
      !pageHas c 0 "(intro)=" && ds.any (·.subject == some "md:role:abbr"))
  let (c, _) := page "---\ntitle: Kilo\n---\n\nA price of $5 and $6.\n"
  t "myst: a document outside MyST's dialect keeps its dollars as text"
    (pageHas c 0 "A price of $5 and $6.")

end Tests.MystDialect
