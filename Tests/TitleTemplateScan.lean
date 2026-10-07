module

import all LeanTex.Core.TitleTemplate
import LeanTex.Core.Lex

/-! Scanner unit checks use the same-package private interface. Artifact
coverage remains in `titleSlotShipChecks`. -/

open LeanTex.Core

namespace Tests.TitleTemplateScan

private def micro (src : String) : List Picture.Tok :=
  let (raws, _) := Parse.parse "title-part-unit" (Lex.lex "title-part-unit" src).1
  (Picture.ofRaws raws).toList

public def checks (check : String → Bool → IO Unit) : IO Unit := do
  let scan := TitleTemplate.scanList [] {} {}
    (micro ("{\\bfseries\\inserttitle\\par}" ++
      "\\ifx\\insertsubtitle\\@empty\\else\\vskip0.5cm" ++
      "{\\large\\insertsubtitle\\par}\\fi"))
  check "unit: an empty-check conditional scans each datum once and no literal ink"
    (scan.data.map (·.datum) == #["title", "subtitle"] && !scan.words)
  let read := TitleTemplate.nodeStmt [] {}
    (micro "[anchor=west] at (current page.west) {\\insertauthor\\\\\\small\\insertinstitute}")
  check "unit: one source node stays one pinned reader node across style changes"
    (read.nodes.size == 1 &&
      read.nodes[0]?.any fun node => node.pinned && node.parts.size == 2)

end Tests.TitleTemplateScan
