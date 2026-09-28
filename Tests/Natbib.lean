import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A document of `natbibSrc` calls on a page wide enough that no entry or
citation line breaks, resolved against `bib`: the shipped body lines, the
reference list's entries (each entry's lines joined), the HTML a reader
gets, and the diagnostics of both passes. -/
def natbibShip (oneFace : Font.FontSet) (bib pre style : String) (calls : List String) :
    Array String × Array String × String × Array Diag :=
  let geometry := "\n\\usepackage[paperwidth=40cm,paperheight=60cm,margin=1cm]{geometry}"
  let (doc, eds) := elabStr (natbibSrc (pre ++ geometry) style calls)
  let (doc, ds) := Bib.apply #[("refs", bib)] doc
  let lines := bodyLines (layoutOf oneFace doc)
  (lines.map lineInk,
    (bibEntryLines lines).map fun e => String.intercalate " " (e.toList.map lineInk),
    htmlVisibleText (HtmlDoc.emit {} doc).1, eds ++ ds)

/-- `\citetext` in each mode natbib reads: the preamble, the style, the
calls, the lines lualatex set for them, and how each reference-list entry
opens (TeX Live 2026, natbib 8.31b, bibtex 0.99e, through `pdftotext`). The
entries cited only inside `\citetext` are listed, at the place their first
citation gives them. -/
def citetextModes : List (String × String × List String × List String × List String) :=
  let nested := ["\\citetext{see \\citealp{delta2021}, or even better \\citealp{eps2020}}",
    "\\citep{alpha2019}"]
  let delta := "Dee Delta. Placeholder Methods."
  let eps := "Eve Epsilon and Finn Zeta. On synthetic benchmarks."
  let alpha := "Ann Alpha, Bob Beta, and Cy Gamma. A study of invented widgets."
  [("\\usepackage{natbib}", "unsrtnat", nested,
    ["L1 [see Delta, 2021, or even better Epsilon and Zeta, 2020] end.",
     "L2 [Alpha et al., 2019] end."], [delta, eps, alpha]),
   ("\\usepackage[numbers]{natbib}", "unsrtnat", nested,
    ["L1 [see 1, or even better 2] end.", "L2 [3] end."],
    ["[1] " ++ delta, "[2] " ++ eps, "[3] " ++ alpha]),
   ("\\usepackage{natbib}", "plain", nested,
    ["L1 [see 2, or even better 3] end.", "L2 [1] end."],
    ["[1] " ++ alpha, "[2] " ++ delta, "[3] " ++ eps]),
   ("\\usepackage[round]{natbib}", "plainnat",
    ["\\citetext{priv.\\ comm.}", "\\citetext{see \\citealp{delta2021}}"],
    ["L1 (priv. comm.) end.", "L2 (see Delta, 2021) end."], [delta])]

/-- **`\citetext` is natbib's `\NAT@open#1\NAT@close`** (natbib.sty:739):
its body is body text set between the citation brackets, so a citation
inside it is a citation like any other — its entry enters the reference list
at its first citation's place and its marks render under the document's
punctuation (natbib.dtx, §Extended Citation Commands: `\citetext{see
\citealp{jon90}, or even better \citealp{jam91}}`). On the shipped page and
in the HTML, in every mode, with no diagnostic: a nested citation that ships
`?` is a loss, and one no diagnostic names is a silent one. -/
def citetextChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (pre, style, calls, want, list) in citetextModes do
    let (page, entries, html, ds) := natbibShip oneFace natbibBib pre style calls
    let tag := s!"citetext {pre} + {style}"
    t s!"{tag}: no diagnostic ({ds.map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for line in want do
      t s!"{tag}: the page sets '{line}'" (page.contains line)
      t s!"{tag}: the html reads '{line}'" (hasStr html line)
    t s!"{tag}: the list holds every entry cited, in order ({entries.toList})"
      (entries.size == list.length &&
        (entries.toList.zip list).all fun (e, w) => e.startsWith w)


/-- The body of each `\nocite` placement document and of its control, the
same document without the `\nocite`: two paragraphs, or a paragraph and the
list. -/
def nocitePlacements : List (String × String × String) :=
  let first := "First paragraph words, citing \\citet{alpha2019}.\n\n"
  [("alone", first ++ "\\nocite{delta2021}\n\nSecond paragraph words.\n\n",
     first ++ "Second paragraph words.\n\n"),
   ("two", first ++ "\\nocite{delta2021} \\nocite{eps2020}\n\nSecond paragraph words.\n\n",
     first ++ "Second paragraph words.\n\n"),
   ("before the list", first ++ "\\nocite{*}\n", first)]

/-- **A `\nocite` in vertical mode starts no paragraph**: LaTeX's `\nocite`
sets no ink and a space in vertical mode is dropped, so a paragraph holding
nothing else is never begun — the page is the page of the document without
it (lualatex: 11.96 bp between the two paragraphs with and without, and the
same gap above the list). Measured on the shipped page as the baseline step
from the first paragraph to the line the next block sets (an empty
paragraph ships a glyphless line of its own, so the next line is not the
measure), and in the HTML as its paragraph count; the entries it names
still enter the list. -/
def nocitePlaceChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let build (body : String) : Array Layout.LineOut × String × Array Diag :=
    let (doc, eds) := elabStr s!"\\documentclass\{article}\n\\usepackage\{natbib}\n\
      \\bibliographystyle\{plainnat}\n\\begin\{document}\n{body}\\bibliography\{refs}\n\
      \\end\{document}\n"
    let (doc, ds) := Bib.apply #[("refs", natbibBib)] doc
    (bodyLines (layoutOf oneFace doc), (HtmlDoc.emit {} doc).1, eds ++ ds)
  let step (lines : Array Layout.LineOut) (next : String) : Option Dim.Sp :=
    match lines.find? (lineInk · |>.startsWith "First paragraph"),
        lines.find? (lineInk · |>.startsWith next) with
    | some a, some b => some (b.y - a.y)
    | _, _ => none
  let paras (html : String) : Nat := (html.splitOn "<p>").length
  for (tag, withNocite, control) in nocitePlacements do
    let (lines, html, ds) := build withNocite
    let (cLines, cHtml, _) := build control
    let next := if tag == "before the list" then "References" else "Second paragraph"
    t s!"nocite {tag}: the page steps as without it ({step lines next} vs {step cLines next})"
      ((step lines next).isSome && step lines next == step cLines next)
    t s!"nocite {tag}: the html has the control's paragraphs ({paras html} vs {paras cHtml})"
      (paras html == paras cHtml)
    t s!"nocite {tag}: its entries enter the list, with no diagnostic"
      (hasStr (htmlVisibleText html) "Dee Delta. Placeholder Methods." &&
        !ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")


/-- The styles the engine does not format, under a bare natbib: the lines
lualatex set for four calls (TeX Live 2026, natbib 8.31b, bibtex 0.99e,
through `pdftotext`). `apalike` has no natbib row, so natbib's own load
punctuation stands; `chicago`'s row is those same values; `named`, `agsm`
and `cospar` were measured over plainnat.bst copies of those names, so the
lines differ from plainnat's by natbib's row alone; a `[square]` load shuts
the door on any row. -/
def natbibRowModes : List (String × String × List String) :=
  let round := ["L1 (Alpha et al., 2019; Delta, 2021) end.", "L2 Alpha et al. (2019) end.",
    "L3 (see Alpha et al., 2019, p. 5) end.", "L4 Delta (2021); Epsilon and Zeta (2020) end."]
  [("\\usepackage{natbib}", "apalike", round),
   ("\\usepackage{natbib}", "chicago", round),
   ("\\usepackage{natbib}", "named",
    ["L1 [Alpha et al., 2019; Delta, 2021] end.", "L2 Alpha et al. [2019] end.",
     "L3 [see Alpha et al., 2019, p. 5] end.", "L4 Delta [2021]; Epsilon and Zeta [2020] end."]),
   ("\\usepackage{natbib}", "agsm",
    ["L1 (Alpha et al. 2019, Delta 2021) end.", "L2 Alpha et al. (2019) end.",
     "L3 (see Alpha et al. 2019, p. 5) end.", "L4 Delta (2021), Epsilon and Zeta (2020) end."]),
   ("\\usepackage{natbib}", "cospar",
    ["L1 /1, 2/ end.", "L2 Alpha et al. /1/ end.", "L3 /see 1, p. 5/ end.",
     "L4 Delta /2/, Epsilon and Zeta /3/ end."]),
   ("\\usepackage[square]{natbib}", "apalike",
    ["L1 [Alpha et al., 2019; Delta, 2021] end.", "L2 Alpha et al. [2019] end.",
     "L3 [see Alpha et al., 2019, p. 5] end.", "L4 Delta [2021]; Epsilon and Zeta [2020] end."])]

/-- **A style's citations take natbib's row for its name, or none**: natbib
gives a style its `\bibstyle@<name>` row whatever formats the list, and a
name it has no row for leaves its declared punctuation standing
(natbib.sty:206–234). The engine formats an unknown style's list as
unsrtnat's, which W0353 names once; its citations are natbib's, on the
shipped page and in the HTML. -/
def natbibRowChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let calls := ["\\citep{alpha2019,delta2021}", "\\citet{alpha2019}",
    "\\citep[see][p.~5]{alpha2019}", "\\citet{delta2021,eps2020}"]
  for (pre, style, want) in natbibRowModes do
    let (page, _, html, ds) := natbibShip oneFace natbibBib pre style calls
    let tag := s!"natbib row {pre} + {style}"
    t s!"{tag}: W0353 names the list, and nothing else warns ({ds.map (·.code)})"
      ((ds.filter fun d => d.code.startsWith "W" || d.code.startsWith "E").map (·.code) ==
        #["W0353"])
    for line in want do
      t s!"{tag}: the page sets '{line}'" (page.contains line)
      t s!"{tag}: the html reads '{line}'" (hasStr html line)
