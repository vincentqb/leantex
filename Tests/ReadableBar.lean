module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ReadableBar

/-- The probe's pale bar, declared alone: no ink role beside it. -/
private def pale : Ir.Color := { r := 0xEF, g := 0xEC, b := 0xE4 }

private def source (cls key body : String) : String :=
  "\\documentclass{" ++ cls ++ "}\n\\palette{" ++ key ++ "=#EFECE4}\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"

/-- The inks of every glyph run on a line reading `text`. -/
private def inksOn (out : Layout.Out) (text : String) : Array Ir.Color :=
  (allLines out).filter (lineText · == text) |>.flatMap fun l =>
    l.segs.filterMap fun
      | .run _ ink _ _ glyphs .. => if glyphs.isEmpty then none else some ink
      | _ => none

/-- **A bar's undeclared ink is legible on the bar.** A document that
declares a pale bar and no ink for it gets the first of the page and the
ink that clears WCAG 2.2's 4.5:1 there (`Role.row`'s `readable` default),
so the title ships legible and nothing warns. Before the default judged,
the page colour shipped on the bar at 1.15:1 and W0345 named a pair the
document never wrote. Read off the shipped glyph runs. -/
public def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let block := "\\begin{block}{Probe Title}Probe body.\\end{block}"
  let frame := "\\begin{frame}{Probe Title}Probe body.\\end{frame}"
  for (label, cls, key, body) in [
      ("article block title", "article", "blocktitlebg", block),
      ("article alert title", "article", "alerttitlebg",
        "\\begin{alertblock}{Probe Title}Probe body.\\end{alertblock}"),
      ("deck block title", "beamer", "blocktitlebg", "\\begin{frame}" ++ block ++ "\\end{frame}"),
      ("deck frame title", "beamer", "frametitlebg", frame)] do
    let (doc, ds) := elabStr (source cls key body)
    let out := layoutOf fonts doc
    let diags := ds ++ Contrast.docDiags doc ++ out.diags
    check ref s!"readable bar/{label}: no pairing warning"
      (!diags.any fun d => d.code == "W0315" || d.code == "W0345")
    let inks := inksOn out "Probe Title"
    check ref s!"readable bar/{label}: the title ships at 4.5:1 on its bar"
      (!inks.isEmpty && inks.all fun c => Contrast.aaText ≤ Contrast.contrastMilli c pale)
    check ref s!"readable bar/{label}: the bar is the declared one"
      (out.pages.any fun p => p.fills.any (·.color == pale))

end Tests.ReadableBar
