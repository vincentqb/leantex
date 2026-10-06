import Tests.RegressionDecks
import Tests.RegressionDiagrams

open LeanTex.Core

namespace Tests

private def regressionCases : Array Regression.Case :=
  RegressionDecks.cases ++ RegressionDiagrams.cases

private def documentEntry (source : String) : Bool :=
  (Lex.lex "" source).1.any fun t => t.tok == .ctrl "documentclass"

private def sameInventory (registered found : Array String) : Bool :=
  !registered.isEmpty && decide registered.toList.Nodup &&
    registered.all found.contains && found.all registered.contains

/-- Every complete fixture has one artifact guard. Included fragments and
local styles are exercised through their registered document entry points. -/
def regressionDocumentChecks (ref : IO.Ref (List String)) : IO Unit := do
  check ref "regression inventory accepts a reordered complete set"
    (sameInventory #["a", "b"] #["b", "a"])
  check ref "regression inventory rejects an unchecked entry"
    (!sameInventory #["a"] #["a", "b"])
  check ref "regression inventory rejects a missing document"
    (!sameInventory #["a", "b"] #["a"])
  check ref "regression inventory rejects duplicate guards"
    (!sameInventory #["a", "a"] #["a"])
  check ref "regression inventory rejects an empty corpus"
    (!sameInventory #[] #[])
  check ref "regression entry recognizes a document declaration"
    (documentEntry "\\documentclass{article}\n\\begin{document}x\\end{document}")
  check ref "regression entry ignores a comment"
    (!documentEntry "% \\documentclass{article}\nfragment")
  check ref "regression entry ignores a code example"
    (!documentEntry "\\begin{verbatim}\n\\documentclass{article}\n\\end{verbatim}")
  let root : System.FilePath := "testdata/regression"
  let present ← root.pathExists
  check ref "regression corpus directory exists" present
  unless present do return
  let mut found : Array String := #[]
  for path in (← root.walkDir) do
    if path.extension == some "tex" then
      if documentEntry (← IO.FS.readFile path) then
        found := found.push path.toString
  let registered := regressionCases.map (·.path)
  check ref s!"regression corpus has exactly one guard per document: {registered} / {found}"
    (sameInventory registered found)
  let some fonts ← Regression.fontSet | do
    check ref "regression corpus bundled fonts load" false
    return
  check ref "regression corpus code face is fixed-pitch"
    (fonts.slotIsFixedPitch 2 && !fonts.slotCollapsed 2)
  for c in regressionCases do
    try
      Regression.runCase ref fonts c
    catch e =>
      check ref s!"{c.path}: regression compilation failed: {e}" false

end Tests
