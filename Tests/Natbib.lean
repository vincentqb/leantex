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
