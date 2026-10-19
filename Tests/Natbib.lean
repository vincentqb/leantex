module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The shipped body lines, reference entries, HTML and diagnostics of `natbibSrc` calls resolved
against `bib`, on a page wide enough to break no line. -/
def natbibShip (oneFace : Font.FontSet) (bib pre style : String) (calls : List String) :
    Array String × Array String × String × Array Diag :=
  let geometry := "\n\\usepackage[paperwidth=40cm,paperheight=60cm,margin=1cm]{geometry}"
  let (doc, eds, ds) := bibResolve (natbibSrc (pre ++ geometry) style calls) #[("refs", bib)]
  let lines := bodyLines (layoutOf oneFace doc)
  (lines.map lineInk,
    (bibEntryLines lines).map fun e => String.intercalate " " (e.toList.map lineInk),
    htmlVisibleText (HtmlDoc.emit {} doc).1, eds ++ ds)

/-- Each `\citetext` mode: preamble, style, calls, the lines lualatex sets, and how each entry
opens. -/
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

/-- A shipped gap reads as one space with or without decoration, and removing the linked spaces
stays distinguishable. -/
def citationInkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, _) := bibBuild (natbibSrc "\\usepackage{natbib}" "unsrtnat"
    ["\\citep[see][p.~5]{alpha2019}"]) #[("refs", natbibBib)]
  let some line := (bodyLines (layoutOf oneFace doc)).find?
      (fun l => (lineText l).startsWith "L1 ") |
    t "citation ink: the probe ships its citation line" false
  let want := "L1 [see Alpha et al., 2019, p. 5] end."
  t "citation ink: the probe ships decorated gaps and a glyphless tie"
    (line.segs.any (fun s => match s with | .decoratedGap _ _ _ => true | _ => false) &&
      line.segs.any (fun s => match s with
        | .run _ _ _ _ gs _ _ _ _ _ _ => gs.isEmpty
        | _ => false))
  let plain := { line with segs := line.segs.map fun s => match s with
    | .decoratedGap w word _ => .gap w word
    | s => s }
  t "citation ink: plain gaps and the tie retain every reference space" (lineInk plain == want)
  t s!"citation ink: decorating gaps preserves the exact reference line ('{lineInk line}')"
    (lineInk line == want)
  let joined := { line with segs := line.segs.filter fun s => match s with
    | .decoratedGap _ _ _ => false
    | _ => true }
  t "citation ink: losing linked spaces changes the reading" (lineInk joined != want)

/-- `\citetext` sets its body between the citation brackets, so a citation inside it is a citation
like any other. -/
def citetextChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  citationInkChecks ref oneFace
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


/-- Each `\nocite` placement body and its control without the `\nocite`. -/
def nocitePlacements : List (String × String × String) :=
  let first := "First paragraph words, citing \\citet{alpha2019}.\n\n"
  [("alone", first ++ "\\nocite{delta2021}\n\nSecond paragraph words.\n\n",
     first ++ "Second paragraph words.\n\n"),
   ("two", first ++ "\\nocite{delta2021} \\nocite{eps2020}\n\nSecond paragraph words.\n\n",
     first ++ "Second paragraph words.\n\n"),
   ("before the list", first ++ "\\nocite{*}\n", first)]

/-- A `\nocite` in vertical mode starts no paragraph, and the entries it names still enter the
list. -/
def nocitePlaceChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let build (body : String) : Array Layout.LineOut × String × Array Diag :=
    let (doc, eds, ds) := bibResolve s!"\\documentclass\{article}\n\\usepackage\{natbib}\n\
      \\bibliographystyle\{plainnat}\n\\begin\{document}\n{body}\\bibliography\{refs}\n\
      \\end\{document}\n" #[("refs", natbibBib)]
    (bodyLines (layoutOf oneFace doc), (HtmlDoc.emit {} doc).1, eds ++ ds)
  let step (lines : Array Layout.LineOut) (next : String) : Option Dim.Length :=
    match lines.find? (lineInk · |>.startsWith "First paragraph"),
        lines.find? (lineInk · |>.startsWith next) with
    | some a, some b => some (b.y - a.y)
    | _, _ => none
  let paras (html : String) : Nat := (html.splitOn "<p>").length
  for (tag, withNocite, control) in nocitePlacements do
    let (lines, html, ds) := build withNocite
    let (cLines, cHtml, _) := build control
    let next := if tag == "before the list" then "References" else "Second paragraph"
    t s!"nocite {tag}: the page steps as without it ({reprStr (step lines next)} vs {reprStr (step cLines next)})"
      ((step lines next).isSome && step lines next == step cLines next)
    t s!"nocite {tag}: the html has the control's paragraphs ({paras html} vs {paras cHtml})"
      (paras html == paras cHtml)
    t s!"nocite {tag}: its entries enter the list, with no diagnostic"
      (hasStr (htmlVisibleText html) "Dee Delta. Placeholder Methods." &&
        !ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")


/-- The lines lualatex sets for four calls under each style the engine does not format, under a bare
natbib. -/
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

/-- A style's citations take natbib's row for its name, or none. -/
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


/-- The calls the `sort` and `compress` rows set: four entries cited in order, then runs, gaps, a
repeat and the bracketless forms. -/
def natbibSortCalls : List String :=
  ["\\citep{alpha2019} \\citep{delta2021} \\citep{eps2020} \\citep{pome2018}",
   "\\citep{eps2020,alpha2019,delta2021}", "\\citep{pome2018,alpha2019,eps2020,delta2021}",
   "\\citep{delta2021,alpha2019}", "\\citet{eps2020,alpha2019}",
   "\\citep[see][p.~5]{eps2020,alpha2019,delta2021}", "\\citep{alpha2019,delta2021,pome2018}",
   "\\citealp{alpha2019,delta2021,eps2020}", "\\citep{alpha2019,delta2021,delta2021,eps2020}",
   "\\citenum{alpha2019,delta2021,eps2020}"]

/-- One configuration per row: preamble, style, calls and the lines lualatex sets. -/
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

/-- natbib's `sort` and `compress` are implemented, not named. -/
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


/-- biblatex's citation commands over `natbibBib`, one paragraph each. -/
def biblatexCalls : List String :=
  ["\\parencite{alpha2019}", "\\textcite{eps2020}", "\\citeauthor{alpha2019}",
   "\\parencite{alpha2019,delta2021}", "\\cite{delta2021}", "\\citeyear{delta2021}",
   "\\parencite[p.~5]{delta2021}", "\\parencite[see][p.~5]{delta2021}", "\\autocite{eps2020}",
   "\\textcite{delta2021,eps2020}", "\\citeauthor{pome2018}", "\\textcite[p.~5]{delta2021}",
   "\\textcite{delta2021,eps2020,pome2018}", "\\cite{alpha2019,delta2021}",
   "\\citeauthor{alpha2019,eps2020}", "\\citeyear{alpha2019,delta2021}"]

/-- One configuration per row: load options and the lines lualatex and biber set for
`biblatexCalls`. -/
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

/-- biblatex's citations are biblatex's, not natbib's by another name. -/
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
    let (doc, eds, ds) := bibResolve s!"\\documentclass\{article}\n\
      \\usepackage[paperwidth=40cm,paperheight=60cm,margin=1cm]\{geometry}\n\
      \\usepackage[{opts}]\{biblatex}\n\\addbibresource\{refs.bib}\n\\begin\{document}\n\
      {body}\\printbibliography\n\\end\{document}\n" #[("refs", bib), ("refs.bib", bib)]
    let page := (bodyLines (layoutOf oneFace doc)).map lineInk
    let html := htmlVisibleText (HtmlDoc.emit {} doc).1
    let tag := s!"biblatex {opts}"
    t s!"{tag}: no diagnostic ({(eds ++ ds).map (·.code)})"
      (!(eds ++ ds).any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for w in want, k in [1:want.length + 1] do
      let line := s!"L{k} {w} end."
      t s!"{tag}: the page sets '{line}'" (page.contains line)
      t s!"{tag}: the html reads '{line}'" (hasStr html line)


/-- A body's `\@natbib` is an unknown command, its citations LaTeX's own; `\setcitestyle` reads no
key or door word it does not take; an option natbib lacks is one loss, worded alike from either
surface; the twin writes the options as declared and reads back to the same citations. -/
def citeSetupChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (page, _, html, ds) := natbibShip oneFace natbibBib "" "plain"
    ["\\cite{alpha2019}", "\\@natbib{nobibstyle numbers}"]
  t "cite setup: a body spelling '\\@natbib' leaves LaTeX's own citations"
    (page.contains "L1 [1] end." && hasStr html "L1 [1] end.")
  t s!"cite setup: and is an unknown command, its argument kept as text ({ds.map (·.code)})"
    (ds.any (fun d => d.code == "W0301") && page.contains "L2 nobibstyle numbers end.")
  let calls := ["\\citep{alpha2019,delta2021}", "\\citet{alpha2019}"]
  let (plain, _, _, _) := natbibShip oneFace natbibBib "\\usepackage{natbib}\\setcitestyle{}"
    "plainnat" calls
  let items := ["option=numbers", "citestyle=plain", "bbx=numeric", "cbx=authoryear",
    "sorting=none", "maxnames=1", "sort", "super", "mainlang=french", "biblatex", "bibstyle"]
  let (forged, _, _, fds) := natbibShip oneFace natbibBib
    s!"\\usepackage\{natbib}\\setcitestyle\{{",".intercalate items}}" "plainnat" calls
  t s!"cite setup: '\\setcitestyle' sets no option, style, scheme, flag, door or language ({forged})"
    (forged == plain && forged.contains "L1 (Alpha et al., 2019; Delta, 2021) end.")
  t "cite setup: and names each item it drops"
    (fds.any fun d => d.code == "W0101" && items.all fun i => hasStr d.message s!"'{i}'")
  let tex := (dvE (dvDoc "\\usepackage[super]{natbib}\n" "Text.")).filter (·.code == "W0104")
  let front := "---\nbibliography: works.bib\nnatbiboptions: super\n---\n\n"
  let (_, md) := mdBibBuild (front ++ "Text [@a].\n") #[("works.bib", worksBib)]
  let md := md.filter fun d => d.subject == some "md:meta:natbiboptions:super"
  t s!"cite setup: an option natbib's table lacks is one loss from either surface \
({tex.map (·.message)}, {md.map (·.message)})"
    (tex.size == 1 && md.size == 1 && tex.map (·.kind) == md.map (·.kind) &&
      tex.map (·.message) == md.map (·.message))
  let (doc, _) := bibBuild (natbibSrc "\\usepackage[sort,compress]{natbib}" "plainnat"
    ["\\citep{alpha2019}"]) #[("refs", natbibBib)]
  let twin := MarkdownDoc.emit doc
  t s!"cite setup: the twin writes natbib's options as declared ({repr twin})"
    (hasStr twin "natbiboptions: 'sort,compress'")
  let cited (d : Ir.Doc) : String := Ir.blocksText (d.body.filter (· matches .para ..))
  t "cite setup: and reads back to the same citations"
    (cited (mdBibBuild twin #[("refs.bib", natbibBib)]).1 == cited doc)

/-- `\citestyle{name}` under a bare natbib and plainnat: the lines lualatex sets for four calls. -/
def natbibCiteStyleModes : List (String × List String) :=
  let round := ["L1 (Alpha et al., 2019; Delta, 2021) end.", "L2 Alpha et al. (2019) end.",
    "L3 (see Alpha et al., 2019, p. 5) end.", "L4 Delta (2021); Epsilon and Zeta (2020) end."]
  [("chicago", round), ("nosuchstyle", round),
   ("named", ["L1 [Alpha et al., 2019; Delta, 2021] end.", "L2 Alpha et al. [2019] end.",
     "L3 [see Alpha et al., 2019, p. 5] end.", "L4 Delta [2021]; Epsilon and Zeta [2020] end."]),
   ("agsm", ["L1 (Alpha et al. 2019, Delta 2021) end.", "L2 Alpha et al. (2019) end.",
     "L3 (see Alpha et al. 2019, p. 5) end.", "L4 Delta (2021), Epsilon and Zeta (2020) end."])]

/-- `\citestyle` sets natbib's row for its name, and `\shortcites` asks nothing the engine does not
already do. -/
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
  citeSetupChecks ref oneFace
