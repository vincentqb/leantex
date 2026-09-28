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


/-- The calls the `sort`/`compress` rows set: the four entries cited once in
order (so their numbers are 1–4), then runs, gaps, a repeat, a textual
citation and the forms that wrap their keys without brackets. -/
def natbibSortCalls : List String :=
  ["\\citep{alpha2019} \\citep{delta2021} \\citep{eps2020} \\citep{pome2018}",
   "\\citep{eps2020,alpha2019,delta2021}", "\\citep{pome2018,alpha2019,eps2020,delta2021}",
   "\\citep{delta2021,alpha2019}", "\\citet{eps2020,alpha2019}",
   "\\citep[see][p.~5]{eps2020,alpha2019,delta2021}", "\\citep{alpha2019,delta2021,pome2018}",
   "\\citealp{alpha2019,delta2021,eps2020}", "\\citep{alpha2019,delta2021,delta2021,eps2020}",
   "\\citenum{alpha2019,delta2021,eps2020}"]

/-- One configuration per row: the preamble, the style, the calls, and the
lines lualatex set for them (TeX Live 2026, natbib 8.31b, bibtex 0.99e,
through `pdftotext`). -/
def natbibSortModes : List (String × String × List String × List String) :=
  [("\\usepackage[numbers,sort&compress]{natbib}", "unsrtnat", natbibSortCalls,
    ["[1] [2] [3] [4]", "[1–3]", "[1–4]", "[1, 2]", "Alpha et al. [1], Epsilon and Zeta [3]",
     "[see 1–3, p. 5]", "[1, 2, 4]", "1–3", "[1, 2, 2, 3]", "1–3"]),
   ("\\usepackage[numbers,sort]{natbib}", "unsrtnat", natbibSortCalls,
    ["[1] [2] [3] [4]", "[1, 2, 3]", "[1, 2, 3, 4]", "[1, 2]",
     "Alpha et al. [1], Epsilon and Zeta [3]", "[see 1, 2, 3, p. 5]", "[1, 2, 4]", "1, 2, 3",
     "[1, 2, 2, 3]", "1, 2, 3"]),
   ("\\usepackage[numbers,compress]{natbib}", "unsrtnat", natbibSortCalls,
    ["[1] [2] [3] [4]", "[3, 1, 2]", "[4, 1, 3, 2]", "[2, 1]",
     "Epsilon and Zeta [3], Alpha et al. [1]", "[see 3, 1, 2, p. 5]", "[1, 2, 4]", "1–3",
     "[1, 2, 2, 3]", "1–3"]),
   ("\\usepackage[sort]{natbib}", "plainnat",
    ["\\citep{eps2020,delta2021,alpha2019}", "\\citet{eps2020,alpha2019}"],
    ["[Alpha et al., 2019, Delta, 2021, Epsilon and Zeta, 2020]",
     "Alpha et al. [2019], Epsilon and Zeta [2020]"]),
   ("\\usepackage[sort]{natbib}", "unsrtnat",
    ["\\citep{eps2020}", "\\citep{delta2021,eps2020,alpha2019}"],
    ["[Epsilon and Zeta, 2020]", "[Epsilon and Zeta, 2020, Delta, 2021, Alpha et al., 2019]"])]

/-- **natbib's `sort` and `compress` are implemented, not named**: `sort`
sets a citation's keys in reference-list order in either mode, and
`compress` joins a numbered citation's runs of three or more — `[1–3, 5]`
— where it wraps its keys (`\citep`, `\citealp`, `\citenum`), never in a
textual one, a repeated number breaking the run (natbib.sty `\NAT@sort@cites`,
`\NAT@citexnum`). On the shipped page and in the HTML, against lualatex,
with no option named as dropped. -/
def natbibSortChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (pre, style, calls, want) in natbibSortModes do
    let (page, _, html, ds) := natbibShip oneFace natbibBib pre style calls
    let tag := s!"natbib {pre} + {style}"
    t s!"{tag}: no diagnostic ({ds.map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for w in want, k in [1:want.length + 1] do
      let line := s!"L{k} {w} end."
      t s!"{tag}: the page sets '{line}'" (page.contains line)
      t s!"{tag}: the html reads '{line}'" (hasStr html line)


/-- biblatex's citation commands, one paragraph each, over `natbibBib`: every
form the index marks implemented, a noted form of each bracket kind, and
one, two and three keys where biblatex's list separators differ from
natbib's. -/
def biblatexCalls : List String :=
  ["\\parencite{alpha2019}", "\\textcite{eps2020}", "\\citeauthor{alpha2019}",
   "\\parencite{alpha2019,delta2021}", "\\cite{delta2021}", "\\citeyear{delta2021}",
   "\\parencite[p.~5]{delta2021}", "\\parencite[see][p.~5]{delta2021}", "\\autocite{eps2020}",
   "\\textcite{delta2021,eps2020}", "\\citeauthor{pome2018}", "\\textcite[p.~5]{delta2021}",
   "\\textcite{delta2021,eps2020,pome2018}", "\\cite{alpha2019,delta2021}",
   "\\citeauthor{alpha2019,eps2020}", "\\citeyear{alpha2019,delta2021}"]

/-- One configuration per row: the load options and the lines lualatex set
for `biblatexCalls` (TeX Live 2026, biblatex 3.21, biber 2.22, through
`pdftotext`). The numeric numbers are biblatex's `nty` order, which sorts
`de Pome` under P. -/
def biblatexModes : List (String × List String) :=
  let names := "Alpha, Beta, and Gamma"
  [("style=authoryear",
    [s!"({names} 2019)", "Epsilon and Zeta (2020)", names, s!"({names} 2019; Delta 2021)",
     "Delta 2021", "2021", "(Delta 2021, p. 5)", "(see Delta 2021, p. 5)",
     "(Epsilon and Zeta 2020)", "Delta (2021) and Epsilon and Zeta (2020)", "Pome",
     "Delta (2021, p. 5)", "Delta (2021), Epsilon and Zeta (2020), and Pome (2018)",
     s!"{names} 2019; Delta 2021", s!"{names}; Epsilon and Zeta", "2019; 2021"]),
   ("style=numeric",
    ["[1]", "Epsilon and Zeta [3]", names, "[1, 2]", "[2]", "2021", "[2, p. 5]", "[see 2, p. 5]",
     "[3]", "Delta [2] and Epsilon and Zeta [3]", "Pome", "Delta [2, p. 5]",
     "Delta [2], Epsilon and Zeta [3], and Pome [4]", "[1, 2]", s!"{names}, Epsilon and Zeta",
     "2019, 2021"]),
   ("style=numeric,sorting=none",
    ["[1]", "Epsilon and Zeta [2]", names, "[1, 3]", "[3]", "2021", "[3, p. 5]", "[see 3, p. 5]",
     "[2]", "Delta [3] and Epsilon and Zeta [2]", "Pome", "Delta [3, p. 5]",
     "Delta [3], Epsilon and Zeta [2], and Pome [4]", "[1, 3]", s!"{names}, Epsilon and Zeta",
     "2019, 2021"])]

/-- **biblatex's citations are biblatex's**, not natbib's by another name: up
to three label names (`maxcitenames`), a name's von part dropped
(`useprefix=false`), the author-year name and year apart by a space
(`\nameyeardelim`), a bare author-year `\cite`, a textual list's last key
after `and`, and the list numbered in biblatex's own `nty` order — on the
shipped page and in the HTML, against lualatex and biber. Over entries that
share their names and year, biblatex's letters follow its `nyt` order (`A
later…` before `An early…`), repeat names whole, and stay out of
`\citeyear`. -/
def biblatexChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let letters := ("style=authoryear", natbibLabelBib,
    ["\\parencite{gam2019a,gam2019b}", "\\citeyear{gam2019a}", "\\textcite{gam2019a}",
     "\\parencite{gam2019b,gam2020}", "\\cite{gam2019a}"],
    ["(Gamma and Eta 2019b; Gamma and Eta 2019a)", "2019", "Gamma and Eta (2019b)",
     "(Gamma and Eta 2019a; Gamma and Eta 2020)", "Gamma and Eta 2019b"])
  for (opts, bib, calls, want) in letters :: biblatexModes.map fun (o, w) =>
      (o, natbibBib, biblatexCalls, w) do
    let body := String.join (calls.zipIdx.map fun (c, k) => s!"L{k + 1} {c} end.\n\n")
    let (doc, eds) := elabStr s!"\\documentclass\{article}\n\
      \\usepackage[paperwidth=40cm,paperheight=60cm,margin=1cm]\{geometry}\n\
      \\usepackage[{opts}]\{biblatex}\n\\addbibresource\{refs.bib}\n\\begin\{document}\n\
      {body}\\printbibliography\n\\end\{document}\n"
    let (doc, ds) := Bib.apply ((Ir.bibRefs doc).map (·, bib)) doc
    let page := (bodyLines (layoutOf oneFace doc)).map lineInk
    let html := htmlVisibleText (HtmlDoc.emit {} doc).1
    let tag := s!"biblatex {opts}"
    t s!"{tag}: no diagnostic ({(eds ++ ds).map (·.code)})"
      (!(eds ++ ds).any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for w in want, k in [1:want.length + 1] do
      let line := s!"L{k} {w} end."
      t s!"{tag}: the page sets '{line}'" (page.contains line)
      t s!"{tag}: the html reads '{line}'" (hasStr html line)


/-- `\citestyle{name}` under a bare natbib and plainnat: the lines lualatex
set for `natbibRowChecks`' four calls (TeX Live 2026, natbib 8.31b). A name
natbib has no row for leaves its load values, the door shut all the same. -/
def natbibCiteStyleModes : List (String × List String) :=
  let round := ["L1 (Alpha et al., 2019; Delta, 2021) end.", "L2 Alpha et al. (2019) end.",
    "L3 (see Alpha et al., 2019, p. 5) end.", "L4 Delta (2021); Epsilon and Zeta (2020) end."]
  [("chicago", round), ("nosuchstyle", round),
   ("named", ["L1 [Alpha et al., 2019; Delta, 2021] end.", "L2 Alpha et al. [2019] end.",
     "L3 [see Alpha et al., 2019, p. 5] end.", "L4 Delta [2021]; Epsilon and Zeta [2020] end."]),
   ("agsm", ["L1 (Alpha et al. 2019, Delta 2021) end.", "L2 Alpha et al. (2019) end.",
     "L3 (see Alpha et al. 2019, p. 5) end.", "L4 Delta (2021), Epsilon and Zeta (2020) end."])]

/-- **`\citestyle` sets natbib's row for its name, and `\shortcites` asks
nothing the engine does not already do** (natbib.sty: `\citestyle` runs
`\bibstyle@<name>` and shuts the door; `\shortcites` exempts keys from
`longnamesfirst`, and every citation here is short). On the shipped page
and in the HTML, against lualatex, with no diagnostic. -/
def natbibCiteStyleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let calls := ["\\citep{alpha2019,delta2021}", "\\citet{alpha2019}",
    "\\citep[see][p.~5]{alpha2019}", "\\citet{delta2021,eps2020}"]
  for (name, want) in natbibCiteStyleModes do
    let (page, _, html, ds) := natbibShip oneFace natbibBib
      s!"\\usepackage\{natbib}\\citestyle\{{name}}" "plainnat" calls
    let tag := s!"natbib \\citestyle\{{name}}"
    t s!"{tag}: no diagnostic ({ds.map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for line in want do
      t s!"{tag}: the page sets '{line}'" (page.contains line)
      t s!"{tag}: the html reads '{line}'" (hasStr html line)
  let (page, _, html, ds) := natbibShip oneFace natbibBib "\\usepackage{natbib}" "plainnat"
    ["\\shortcites{alpha2019} \\citet{alpha2019}"]
  t s!"natbib \\shortcites: no ink, no diagnostic ({ds.map (·.code)})"
    (page.contains "L1 Alpha et al. [2019] end." && hasStr html "L1 Alpha et al. [2019] end." &&
      !ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
