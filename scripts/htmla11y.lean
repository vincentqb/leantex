/-
What assistive technology is handed, committed as numbers. Run from the
repository root:

  lake env lean --run scripts/htmla11y.lean              regenerate the baseline
  lake env lean --run scripts/htmla11y.lean --check      gate against the committed one
  lake env lean --run scripts/htmla11y.lean --selftest   break each check once

Every golden fixture is elaborated and emitted to its typed HTML tree
in-process (`a11yCorpusPage`: the document's own stylesheet mode, its images
from `tests/corpus`), and `HtmlDoc.a11yFacts` — the judge `htmlA11yChecks`
reads in the suite — counts six deficits per page (`a11yDeficits`):
contrast pairings failed over both colour schemes, a page without exactly
one `<h1>`, tab stops hidden from assistive technology, images with no text
alternative, scroll containers a keyboard cannot reach, and pictures with no
accessible name. Each is committed as
headroom (`debtCap - count`), so a new deficit is a fall.

Hermetic: committed inputs only — no browser, no network, no tool, no font
from the host. What a browser makes of the same pages is axe's to say, and
axe is a report, never this gate. The suite already holds `svg`, `scroll`
and `hidden-focus` at zero on every page; `contrast` and `h1` carry defects whose fix is a
human decision (a declared ink in dark mode; which element owns `<h1>`), so
this tier holds them from getting worse until it is made.
-/
import Tests.HtmlA11y
import scripts.Board

open LeanTex.Core Scoreboard

/-- The rows for one page's deficits: `<fixture>.<check>`, as headroom. -/
def a11yRows (n : String) (ds : List (String × Nat)) : Array Row :=
  ds.toArray.map fun (check, count) =>
    { item := s!"{n}.{check}", value := debtCap - (count : Int) }

def a11yMeasure : IO (Array String × Array Row) := do
  let pages ← a11yCorpus
  let mut rows : Array Row := #[]
  let mut totals : Array (String × Nat) := #[]
  for (n, ds) in pages do
    rows := rows ++ a11yRows n ds
    for (check, count) in ds do
      totals := match totals.findIdx? (·.1 == check) with
        | some i => totals.modify i fun (c, k) => (c, k + count)
        | none => totals.push (check, count)
  let summary := String.intercalate ", " (totals.toList.map fun (c, k) => s!"{c} {k}")
  return (#[s!"# source: {pages.size} golden fixtures, their typed HTML trees built \
in-process and judged by HtmlDoc.a11yFacts; deficits: {summary}"], rows)

/-- One element, for the hand-written trees below. -/
def a11yEl (tag : String) (attrs : Array (String × String) := #[])
    (kids : Array Html.Node := #[]) : Html.Node := .elem tag attrs kids

/-- The judge over a hand-written body, the engine's own stylesheet on the
paged deck unless said otherwise. -/
def facts (body : Array Html.Node) (own : Bool := true) (deck : Bool := true) :
    HtmlDoc.A11yFacts :=
  HtmlDoc.a11yFacts own deck body

def a11ySelftest : IO UInt32 := tierSelftest "htmla11y" fun no => do
  -- h1: exactly one, and a hidden one is not handed to assistive technology.
  let h1 := a11yEl "h1" #[] #[.text "Title"]
  no "h1: none counts none" ((facts #[a11yEl "p"]).h1s == 0)
  no "h1: one counts one" ((facts #[h1]).h1s == 1)
  no "h1: two count two" ((facts #[h1, h1]).h1s == 2)
  no "h1: under aria-hidden it is not counted"
    ((facts #[a11yEl "div" #[("aria-hidden", "true")] #[h1]]).h1s == 0)
  -- img: a non-blank alt, or a declared decorative role.
  let img (attrs : Array (String × String)) := a11yEl "img" (#[("src", "a.png")] ++ attrs)
  no "img: no alt is unnamed" ((facts #[img #[]]).imgsUnnamed == 1)
  no "img: an empty alt is unnamed" ((facts #[img #[("alt", "")]]).imgsUnnamed == 1)
  no "img: a blank alt is unnamed" ((facts #[img #[("alt", "  ")]]).imgsUnnamed == 1)
  no "img: a real alt names it" ((facts #[img #[("alt", "a chart")]]).imgsUnnamed == 0)
  no "img: role=presentation declares it decorative"
    ((facts #[img #[("alt", ""), ("role", "presentation")]]).imgsUnnamed == 0)
  no "img: under aria-hidden it is not counted"
    (let f := facts #[a11yEl "div" #[("aria-hidden", "true")] #[img #[]]]
     f.imgs == 0 && f.imgsUnnamed == 0)
  -- hidden-focus: a tab stop under aria-hidden is still a keyboard stop.
  let link := a11yEl "a" #[("href", "https://example.org")] #[.text "x"]
  let hide (kids : Array Html.Node) := a11yEl "div" #[("aria-hidden", "true")] kids
  no "hidden-focus: a link under aria-hidden is a hidden tab stop"
    ((facts #[hide #[link]]).hiddenTabStops == 1)
  no "hidden-focus: a link assistive technology sees is not"
    ((facts #[link]).hiddenTabStops == 0)
  no "hidden-focus: the hiding element itself is one"
    ((facts #[a11yEl "a" #[("href", "#x"), ("aria-hidden", "true")]]).hiddenTabStops == 1)
  no "hidden-focus: tabindex=0 makes any element one"
    ((facts #[hide #[a11yEl "span" #[("tabindex", "0")]]]).hiddenTabStops == 1)
  no "hidden-focus: an anchor with no href takes no focus"
    ((facts #[hide #[a11yEl "a" #[] #[.text "x"]]]).hiddenTabStops == 0)
  no "hidden-focus: tabindex=-1 takes focus from script only"
    ((facts #[hide #[a11yEl "a" #[("href", "#x"), ("tabindex", "-1")]]]).hiddenTabStops == 0)
  no "hidden-focus: a hidden subtree is not rendered, so nothing in it takes focus"
    ((facts #[hide #[a11yEl "div" #[("hidden", "")] #[link]]]).hiddenTabStops == 0)
  -- svg: aria-label, aria-labelledby, or a <title> child with text.
  no "svg: no name is unnamed" ((facts #[a11yEl "svg" #[("role", "img")]]).svgsUnnamed == 1)
  no "svg: aria-label names it"
    ((facts #[a11yEl "svg" #[("role", "img"), ("aria-label", "a grid")]]).svgsUnnamed == 0)
  no "svg: a blank aria-label is unnamed"
    ((facts #[a11yEl "svg" #[("aria-label", " ")]]).svgsUnnamed == 1)
  no "svg: a title child names it"
    ((facts #[a11yEl "svg" #[] #[a11yEl "title" #[] #[.text "a grid"]]]).svgsUnnamed == 0)
  no "svg: an empty title child is unnamed"
    ((facts #[a11yEl "svg" #[] #[a11yEl "title"]]).svgsUnnamed == 1)
  -- scroll: a declared scroll container is focusable, and a stage is named.
  let stage (attrs : Array (String × String)) := a11yEl "section" (#[("class", "slide")] ++ attrs)
  no "scroll: a deck stage with no tab stop is unreachable"
    ((facts #[stage #[]]).scrollsUnreachable == 1)
  no "scroll: a deck stage with a tab stop and no name is unreachable"
    ((facts #[stage #[("tabindex", "0")]]).scrollsUnreachable == 1)
  no "scroll: a named deck stage with a tab stop is reachable"
    (let f := facts #[stage #[("tabindex", "0"), ("aria-label", "A slide")]]
     f.scrolls == 1 && f.scrollsUnreachable == 0)
  no "scroll: a section page is a stage"
    ((facts #[a11yEl "section" #[("class", "section-page")]]).scrollsUnreachable == 1)
  no "scroll: outside the deck a stage is not a scroller"
    ((facts #[stage #[]] (deck := false)).scrolls == 0)
  no "scroll: a code block with no tab stop is unreachable"
    ((facts #[a11yEl "pre"]).scrollsUnreachable == 1)
  no "scroll: a code block with a tab stop is reachable"
    ((facts #[a11yEl "pre" #[("tabindex", "0")]]).scrollsUnreachable == 0)
  no "scroll: under a stylesheet the engine does not own, nothing is declared"
    ((facts #[a11yEl "pre", stage #[]] (own := false)).scrolls == 0)
  -- contrast: the engine's own tokens pass both schemes; a declared ink
  -- keeps its value in dark mode and fails there; a themed deck's declared
  -- ink sits on the scheme's stage.
  let plain := (elabStr (dvDoc "" "x")).1
  no s!"contrast: an undeclared page passes both schemes: {HtmlDoc.schemeFailures true plain}"
    (HtmlDoc.schemeFailures true plain).isEmpty
  let inked := (elabStr (dvDoc "\\palette{ ink = #18181B }\n" "x")).1
  no s!"contrast: a declared ink fails dark text: {HtmlDoc.schemeFailures true inked}"
    ((HtmlDoc.schemeFailures true inked).contains ("dark", "text") &&
     !(HtmlDoc.schemeFailures true inked).any (·.1 == "light"))
  no "contrast: a stylesheet the engine does not own claims nothing"
    (HtmlDoc.schemeFailures false inked).isEmpty
  let deck := (elabStr (dvDeck "" "\\begin{frame}{T}\nx\n\\end{frame}")).1
  no s!"contrast: the default deck bundle's ink fails on the dark stage: \
{HtmlDoc.schemeFailures true deck}"
    ((HtmlDoc.schemeFailures true deck).contains ("dark", "text"))
  -- The rows: one per check per page, sorted, headroom.
  let rows := a11yRows "p" [("contrast", 2), ("h1", 1), ("img", 0)]
  no "rows: headroom is the cap less the count"
    (rows.map (·.value) == #[debtCap - 2, debtCap - 1, debtCap])
  no "rows: items are <fixture>.<check>"
    (rows.map (·.item) == #["p.contrast", "p.h1", "p.img"])

def main (args : List String) : IO UInt32 :=
  tierMain "htmla11y" (.headroom debtCap) a11yMeasure a11ySelftest args
