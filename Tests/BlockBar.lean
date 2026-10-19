module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

private def blockSource (cls env role titleSize bodySize : String) : String :=
  let body := "\\begin{" ++ env ++ "}{\\" ++ titleSize ++ " Hg}\\" ++
    bodySize ++ " BODY\\end{" ++ env ++ "}"
  "\\documentclass{" ++ cls ++ "}\n\\palette{" ++ role ++
    "=#FF0000}\n\\begin{document}\n" ++
    (if cls == "beamer" then "\\begin{frame}[t]{}" ++ body ++ "\\end{frame}" else body) ++
    "\n\\end{document}"

/-- A title background's painted bottom clears the first body line's glyph hull, across sizes, block
kinds and both page models. -/
def blockBarChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let sizes := #["tiny", "scriptsize", "footnotesize", "small", "normalsize", "Large"]
  for cls in #["article", "beamer"] do
    for (env, role) in #[("block", "blocktitlebg"), ("alertblock", "alerttitlebg"),
                         ("exampleblock", "exampletitlebg")] do
      for titleSize in sizes do
        for bodySize in sizes do
          let label := s!"block bar {cls}/{env}/{titleSize}/{bodySize}"
          let (doc, ds) := elabStr (blockSource cls env role titleSize bodySize)
          let out := layoutOf fonts doc
          check ref (label ++ ": source elaborates without errors")
            (!(ds ++ out.diags).any (·.severity == .error))
          -- A painted body opens on an empty line at its ground's top.
          check ref (label ++ ": title and body share one page")
            (out.pages.size == 1 &&
              ((bodyLines out).filter (!·.segs.isEmpty)).map lineText == #["Hg", "BODY"])
          let bars := out.pages.flatMap fun p =>
            p.fills.filter fun f => f.color == { r := 255, g := 0, b := 0 : Ir.Color }
          check ref (label ++ ": exactly one title background") (bars.size == 1)
          let glyphs := shippedBodyGlyphs out
          let some first := glyphs.find? (·.scalar == 'B')
            | failures ref (label ++ ": body glyph is missing")
              continue
          let body := glyphs.filter fun g => g.page == first.page && g.line == first.line
          match bars[0]?, ShippedInk.targetInk fonts body with
          | some bar, .ok ink =>
            check ref (s!"{label}: bar bottom {reprStr (bar.y + bar.h)} <= body ink top {reprStr (-ink.top)}")
              (bar.y + bar.h ≤ -ink.top)
          | _, .error message => failures ref (label ++ ": " ++ message)
          | none, _ => failures ref (label ++ ": title background is missing")

end Tests
