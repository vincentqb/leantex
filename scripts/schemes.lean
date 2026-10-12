/-
The colour schemes the corpus's web pages ship, committed as numbers. Run
from the repository root:

  lake env lean --run scripts/schemes.lean              regenerate the baseline
  lake env lean --run scripts/schemes.lean --check      gate against the committed one
  lake env lean --run scripts/schemes.lean --selftest   break each check once

Every golden fixture is elaborated in-process and judged as its web page is
emitted (`Contrast.schemeJudge`, under the page's own stylesheet mode): each
scheme the document asks its page to offer (`Ir.Doc.requestedSchemes` — a
document every scheme, a deck print, its light screen and that screen's more
contrast) is a row `<fixture>.<scheme>`, 1 where the page ships it and 0
where a colour it cannot carry legibly there drops it (W0308 names which).
A page that loses a scheme it shipped is a fall; one that gains it is a
rise to record.

Hermetic: committed inputs only — no browser, no network, no tool, no font
from the host.
-/
import Tests.HtmlA11y
import scripts.Board

open LeanTex.Core Scoreboard

/-- One page's rows: each scheme it asks for, 1 where it ships. -/
def schemeRows (n : String) (requested shipped : List Ir.Scheme) : Array Row :=
  (requested.toArray.map fun s =>
    { item := s!"{n}.{s.name}", value := if shipped.contains s then 1 else 0 }).qsort
    (·.item < ·.item)

/-- What a golden fixture's web page asks for and ships, under the
stylesheet mode its document declares: a page outside the engine's own
stylesheet ships its light screen alone. -/
def schemesOf (doc : Ir.Doc) : List Ir.Scheme × List Ir.Scheme :=
  if a11yCssOf doc == .own then (doc.requestedSchemes, (Contrast.schemeJudge doc).shipped)
  else ([.light], [.light])

def schemesMeasure : IO (Array String × Array Row) := do
  let mut rows : Array Row := #[]
  let mut totals : Array (Ir.Scheme × Nat × Nat) := Ir.Scheme.all.toArray.map (·, 0, 0)
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let (requested, shipped) := schemesOf doc
    rows := (schemeRows n requested shipped).foldl Array.push rows
    totals := totals.map fun (s, asked, ships) =>
      (s, asked + (if requested.contains s then 1 else 0),
        ships + (if shipped.contains s then 1 else 0))
  let summary := String.intercalate ", " (totals.toList.map fun (s, asked, ships) =>
    s!"{s.name} {ships} of {asked}")
  return (#[s!"# source: {goldenNames.length} golden fixtures, each judged in-process as its \
web page ships (Contrast.schemeJudge); pages shipping each scheme of those asking it: {summary}"],
    rows.qsort (·.item < ·.item))

/-- A minimal document under a declaration, its body one paragraph. -/
def schemeProbe (pre : String) (cls : String := "article") : Ir.Doc :=
  (elabStr s!"\\documentclass\{{cls}}{pre}\\begin\{document}x\\end\{document}").1

def schemesSelftest : IO UInt32 := tierSelftest "schemes" fun no => do
  let plain := schemeProbe ""
  no "an undeclared document asks every scheme and ships each"
    (schemesOf plain == (Ir.Scheme.all, Ir.Scheme.all))
  let deck := schemeProbe "" "slides"
  no "a deck asks print, its light screen and that screen's more contrast"
    ((schemesOf deck).1 == [.print, .light, .lightMore])
  -- A mid-grey page under a black ink and a white alert: no tone of either
  -- reaches the more-contrast gate on it, and the page moved for the ink
  -- leaves the alert further off, so that scheme alone drops; the colours
  -- were declared for the light screen and print, which ship them as
  -- declared.
  let grey := schemeProbe "\\palette{ bg = #767676, fg = #000000, alert = #FFFFFF }"
  no s!"a colour no tone carries drops that scheme alone: {(schemesOf grey).2.map (·.name)}"
    (!(schemesOf grey).2.contains .lightMore && (schemesOf grey).2.contains .light &&
     (schemesOf grey).2.contains .print)
  let declared := schemeProbe "\\output{ schemes = print, light }"
  no "a declared list is what the page asks"
    ((schemesOf declared).1 == [.print, .light])
  let rows := schemeRows "p" [.print, .light, .dark] [.print, .dark]
  no "rows: one per scheme asked, 1 where it ships, sorted"
    (rows.map (fun r => (r.item, r.value)) == #[("p.dark", 1), ("p.light", 0), ("p.print", 1)])
  no "rows: a scheme not asked has no row"
    (!(rows.any (·.item == "p.lightMore")))

def main (args : List String) : IO UInt32 :=
  tierMain "schemes" .raw schemesMeasure schemesSelftest args
