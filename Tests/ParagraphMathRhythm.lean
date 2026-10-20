module

public import Tests.Artifact
public import LeanTex.Core.Layout.MathRhythm

public section

open LeanTex.Core
open LeanTex.Core.Dim (Length pt)

namespace ParagraphMathRhythm

/-- A paragraph around `inline` with forced breaks, so vertical geometry is independent of line
breaking. -/
def body (inline : String) : String :=
  "An ordinary line.\\\\\nA line with " ++ inline ++
    ".\\\\\nA further ordinary line.\\\\\nThe final ordinary line."

def source (size leading : Nat) (formula : String) : String :=
  metricDoc (s!"\\fontsize\{{size}pt}\{{leading}pt}\\selectfont\n" ++
    body ("$" ++ formula ++ "$"))

/-- Outline hulls of the shipped runs plus every painted math rule or polygon, with no face-wide
ascent or descent. -/
def reach (fs : Font.FontSet) (line : Layout.LineOut) : Except String (Length × Length) := do
  let mut above := 0
  let mut below := 0
  for seg in line.segs do
    match seg with
    | .run fi _ _ _ gs size _ _ raise _ _ =>
      let f := fs.get fi
      for (g, _, _) in gs do
        let some (lo, hi) := f.yExtent g | throw "probe glyph has no outline"
        above := max above (raise + hi * size / f.unitsPerEm)
        below := max below (-raise - lo * size / f.unitsPerEm)
    | .rule _ t r _ _ | .decoration _ _ t r _ _ =>
      above := max above (r + t)
      below := max below (-r)
    | .poly points _ =>
      for (_, y) in points do
        above := max above y
        below := max below (-y)
    | .image _ _ h _ _ _ => above := max above h
    | .gap .. | .decoratedGap .. => pure ()
  return (above, below)

def gaps (lines : Array Layout.LineOut) : Array Length :=
  (lines.zip (lines.extract 1 lines.size)).map fun (a, b) => b.y - a.y

/-- A visible collision check in page coordinates, over outline hulls. -/
def clears (fs : Font.FontSet) (lines : Array Layout.LineOut) : Except String Bool := do
  for (a, b) in lines.zip (lines.extract 1 lines.size) do
    let ia ← reach fs a
    let ib ← reach fs b
    unless ia.2 + ib.1 ≤ b.y - a.y do return false
  return true

end ParagraphMathRhythm

/-- Small inline maths that fits the prose envelope does not enlarge its line box; taller maths
reserves its reach. -/
def paragraphMathRhythmChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← serifFacesSet | do
    failures ref "paragraph math rhythm: bundled faces unavailable"
    return
  let t := check ref
  let plain := bodyLines (layoutOf fs (elabStr (metricDoc (ParagraphMathRhythm.body "v"))).1)
  for formula in #["v", "w", "v+w"] do
    let out := layoutOf fs
      (elabStr (metricDoc (ParagraphMathRhythm.body ("$" ++ formula ++ "$")))).1
    t "paragraph math rhythm: inherited leading retains the prose baselines"
      ((bodyLines out).map (·.y) == plain.map (·.y))
  for (size, leading) in #[(8, 8), (8, 10), (10, 12), (10, 16), (14, 14), (14, 18)] do
    let tag := s!"paragraph math rhythm {size}/{leading}"
    for formula in #["v", "w", "v+w", "\\mathrm{v}+\\mathit{w}"] do
      let (doc, diags) := elabStr (ParagraphMathRhythm.source size leading formula)
      let out := layoutOf fs doc
      let lines := bodyLines out
      t (tag ++ ": probe elaborates") (!diags.any (·.severity == .error))
      t (tag ++ ": four lines ship") (lines.size == 4 && out.pages.size == 1)
      t (tag ++ s!": {formula} preserves the ordinary baseline gap")
        (ParagraphMathRhythm.gaps lines == Array.replicate 3 (pt leading))
      t (tag ++ ": outline intervals clear")
        (ParagraphMathRhythm.clears fs lines == .ok true)
    for formula in #["\\frac{1}{\\frac{1}{x}}", "x^{x^x}_{y_y}",
        "\\left(\\frac{x}{y}\\right)", "\\sqrt{\\frac{x}{y}}"] do
      let (doc, _) := elabStr (ParagraphMathRhythm.source size leading formula)
      let out := layoutOf fs doc
      let lines := bodyLines out
      t (tag ++ ": tall formula retains four lines") (lines.size == 4)
      t (tag ++ ": tall formula clears both neighbours")
        (ParagraphMathRhythm.clears fs lines == .ok true)
      t (tag ++ ": ordinary pair returns to the grid")
        ((ParagraphMathRhythm.gaps lines)[2]?.any (· == pt leading))
      if leading ≤ size + 2 then
        t (tag ++ ": tall formula reserves additional room")
          ((ParagraphMathRhythm.gaps lines).any (· > pt leading))
      if formula != "x^{x^x}_{y_y}" then
        t (tag ++ ": glyph-free construction carries measured bounds")
          (lines.any fun l => l.segs.any fun
            | .run _ _ _ _ gs _ metrics _ _ _ _ =>
              gs.isEmpty && metrics.math.any (fun m => m.top > 0 || m.bottom < 0)
            | _ => false)
