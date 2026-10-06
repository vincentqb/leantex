import Tests.Support

open LeanTex.Core

namespace Tests

private def blockSource (cls env role titleSize bodySize : String) : String :=
  let body := "\\begin{" ++ env ++ "}{\\" ++ titleSize ++ " Hg}\\" ++
    bodySize ++ " BODY\\end{" ++ env ++ "}"
  "\\documentclass{" ++ cls ++ "}\n\\palette{" ++ role ++
    "=#FF0000}\n\\begin{document}\n" ++
    (if cls == "beamer" then "\\begin{frame}[t]{}" ++ body ++ "\\end{frame}" else body) ++
    "\n\\end{document}"

/-- A title background's painted bottom must clear the first body's
decoded glyph hull. Cross title/body sizes and all titled-block kinds in
both page models: a missing fill, missing body, or a spill cannot pass as
separation. The hull is read independently from the shipped face outlines. -/
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
          check ref (label ++ ": title and body share one page")
            (out.pages.size == 1 && (bodyLines out).map lineText == #["Hg", "BODY"])
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
            check ref (s!"{label}: bar bottom {bar.y + bar.h} <= body ink top {-ink.top}")
              (bar.y + bar.h ≤ -ink.top)
          | _, .error message => failures ref (label ++ ": " ++ message)
          | none, _ => failures ref (label ++ ": title background is missing")

end Tests
