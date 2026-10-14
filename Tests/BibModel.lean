module

public import Tests.Support
import LeanTex.Core.BibMacro

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! The bibliography's one entry model, held against bibtex and biber: name splitting, the two
views, both inheritances, and the reference lists of the BibTeX styles and biblatex's standard
families over the probes in `testdata/probes/u102`. -/

def bibProbeDir : String := "testdata/probes/u102"

/-- A reference file's lines: its `#` provenance and `pdftotext`'s page
feeds dropped. -/
def refLines (text : String) : Array String :=
  ((text.splitOn "\n").map (·.replace "\x0c" "")).filter (fun l =>
    !l.trimAscii.toString.isEmpty && !l.startsWith "#") |>.toArray

/-- Text with math italic letters read as their base letters and white space runs as one space, as
`pdftotext` reads lualatex's math. -/
def bibPlain (s : String) : String := Id.run do
  let mut out := ""
  let mut space := false
  for c in s.toList do
    let n := c.toNat
    let c :=
      if 0x1D44E ≤ n && n ≤ 0x1D467 then Char.ofNat (n - 0x1D44E + 'a'.toNat)
      else if 0x1D434 ≤ n && n ≤ 0x1D44D then Char.ofNat (n - 0x1D434 + 'A'.toNat)
      else if 0x1D6FC ≤ n && n ≤ 0x1D714 then Char.ofNat (n - 0x1D6FC + 0x03B1)
      else if c == '\u00a0' then ' ' else c
    if c == ' ' then
      unless space do out := out.push ' '
      space := true
    else
      out := out.push c
      space := false
  return out.trimAscii.toString

/-- biblatex's small-capital acronyms as the page spells them without a small-caps face, read back
as the lowercase `pdftotext` reads. -/
def bibAcros (s : String) : String :=
  ["DOI:", "URL:", "ISBN:", "ISSN:", "ISRN:"].foldl (fun s a => s.replace a a.toLower) s

/-- A build's shipped reference-list entries (each entry's lines joined)
and the text the HTML gives a reader. -/
def bibShipped (fonts : Font.FontSet) (doc : Ir.Doc) : Array String × String :=
  let lines := bodyLines (layoutOf fonts doc)
  ((bibEntryLines lines).map fun e =>
      bibAcros (bibPlain (String.intercalate " " (e.toList.map lineInk))),
    bibPlain (htmlVisibleText (HtmlDoc.emit {} doc).1))

/-- A probe document: a page wide enough that no entry breaks, the preamble
and the list's markup around a `\nocite` of the keys. -/
def bibProbeDoc (pre list keys : String) (width : String := "60cm") : String :=
  "\\documentclass{article}\n\\usepackage[paperwidth=" ++ width ++
    ",paperheight=80cm,margin=1cm]{geometry}\n" ++
    pre ++ "\n\\begin{document}\n\\nocite{" ++ keys ++ "}\n" ++ list ++ "\n\\end{document}\n"

/-- bibtex 0.99e's own splits of nineteen names (`{ff}`, `{vv}`, `{ll}`, `{jj}`, `{f.}`), a tie read
as a space. -/
def bibtexNameSplits : List (String × String × String × String × String × String) :=
  [("Jean de La Fontaine", "Jean", "de", "La Fontaine", "", "J."),
   ("Charles Louis Xavier Joseph de la Vallee Poussin", "Charles Louis Xavier Joseph", "de la",
    "Vallee Poussin", "", "C. L. X. J."),
   ("de la Vallee Poussin, Charles Louis Xavier Joseph", "Charles Louis Xavier Joseph", "de la",
    "Vallee Poussin", "", "C. L. X. J."),
   ("Jean-Paul Sartre-Smith", "Jean-Paul", "", "Sartre-Smith", "", "J.-P."),
   ("{\\'E}mile Zola", "{\\'E}mile", "", "Zola", "", "{\\'E}."),
   ("{\\o}rn Example", "", "{\\o}rn", "Example", "", ""),
   ("Ludo van der Sample", "Ludo", "van der", "Sample", "", "L."),
   ("Smith, Jr., John Quincy", "John Quincy", "", "Smith", "Jr.", "J. Q."),
   ("{Example Working Group}", "", "", "{Example Working Group}", "", ""),
   ("jean de la fontaine", "", "jean de la", "fontaine", "", ""),
   ("Maria de los {\\'A}ngeles Example", "Maria", "de los", "{\\'A}ngeles Example", "", "M."),
   ("{van den Berg}, Alex", "Alex", "", "{van den Berg}", "", "A."),
   ("Ana {\\relax Ch}ristina Example", "Ana {\\relax Ch}ristina", "", "Example", "",
    "A. {\\relax Ch}."),
   ("D{\\\"u}rer, Albrecht", "Albrecht", "", "D{\\\"u}rer", "", "A."),
   ("Alex~B. Example", "Alex B.", "", "Example", "", "A. B."),
   ("von Example, Ana", "Ana", "von", "Example", "", "A."),
   ("Ana von Example Jr", "Ana", "von", "Example Jr", "", "A."),
   ("{\\OE}rsted, Hans", "Hans", "", "{\\OE}rsted", "", "H."),
   ("{Ann Marie} Zed", "{Ann Marie}", "", "Zed", "", "A.")]

/-- Names split as bibtex.web splits them. -/
def bibNameChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let tie (s : String) : String := s.replace "~" " "
  for (s, first, von, last, jr, inits) in bibtexNameSplits do
    let n := Bib.parseName s
    t s!"names: '{s}' splits as bibtex splits it ({repr n})"
      (tie n.first == first && tie n.von == von && tie n.last == last && tie n.jr == jr)
    t s!"names: '{s}' abbreviates to '{inits}' ('{Bib.initials n.first}')"
      (tie (Bib.initials n.first) == inits)

/-- biber's date grammar: what it reads as a date and what it does not. -/
def bibDateChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let d (y : Int) (m d' : Option Nat := none) : Bib.Date := { year := y, month := m, day := d' }
  t "dates: a full date" (Bib.DateValue.parse "2021-05-03" == some { start := some (d 2021 (some 5) (some 3)) })
  t "dates: a month" (Bib.DateValue.parse "2019-07" == some { start := some (d 2019 (some 7)) })
  t "dates: a range" (Bib.DateValue.parse "2018-03-01/2018-03-05" ==
    some { start := some (d 2018 (some 3) (some 1)), stop := some (some (d 2018 (some 3) (some 5))) })
  t "dates: an open end, either spelling" (Bib.DateValue.parse "1989/" ==
      some { start := some (d 1989), stop := some none } &&
    Bib.DateValue.parse "1989/.." == some { start := some (d 1989), stop := some none })
  t "dates: an open start, either spelling" (Bib.DateValue.parse "../2015" ==
      some { start := none, stop := some (some (d 2015)) } &&
    Bib.DateValue.parse "/2015" == some { start := none, stop := some (some (d 2015)) })
  t "dates: circa and uncertain" (Bib.DateValue.parse "1990~" == some { start := some (d 1990), circa := true } &&
    Bib.DateValue.parse "1990?" == some { start := some (d 1990), uncertain := true })
  t "dates: a year before the common era" (Bib.DateValue.parse "-0044" == some { start := some (d (-44)) })
  t "dates: a year of five digits or more" (Bib.DateValue.parse "Y-12000" == some { start := some (d (-12000)) })
  t "dates: a time with its seconds is no part of the date" (Bib.DateValue.parse "2020-02-29T10:00:00" ==
    some { start := some (d 2020 (some 2) (some 29)) })
  t "dates: a season and a quarter" (Bib.DateValue.parse "2020-21" ==
      some { start := some { year := 2020, division := some "spring" } } &&
    Bib.DateValue.parse "2020-35" == some { start := some { year := 2020, division := some "Q3" } })
  let decade : Bib.DateValue :=
    { start := some (d 1990), stop := some (some (d 1999)), unspecified := some "yearindecade" }
  let months : Bib.DateValue :=
    { start := some (d 1999 (some 1)), stop := some (some (d 1999 (some 12)))
      unspecified := some "monthinyear" }
  t "dates: unspecified digits as the range they span"
    (Bib.DateValue.parse "199X" == some decade && Bib.DateValue.parse "1999-XX" == some months)
  t "dates: words, the calendar's gaps, short years and times without seconds are no date"
    ((Bib.DateValue.parse "Spring 2020").isNone && (Bib.DateValue.parse "2020-13").isNone &&
      (Bib.DateValue.parse "2021-02-31").isNone && (Bib.DateValue.parse "2019-02-29").isNone &&
      (Bib.DateValue.parse "98").isNone && (Bib.DateValue.parse "2020-02-29T10:00").isNone &&
      (Bib.DateValue.parse "").isNone && (Bib.DateValue.parse "2019/2020/2021").isNone)

/-- Entries sharing a label take `a` … `z`, then `aa`, `ab` …, as biblatex's `\mknumalph` does. -/
def bibLetterChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := String.join ((List.range 28).map fun i =>
    let n := if i + 1 < 10 then s!"0{i + 1}" else s!"{i + 1}"
    s!"@misc\{k{n}, author = \{Ann Alpha}, title = \{Work {n}}, year = 2020}\n")
  let letters : List String :=
    (List.range 26).map (fun i => String.singleton (Char.ofNat ('a'.toNat + i))) ++ ["aa", "ab"]
  let shown (pre list : String) : String :=
    let (doc, _) := bibBuild (bibProbeDoc pre list "*") #[("refs", bib)]
    bibPlain (htmlVisibleText (HtmlDoc.emit {} doc).1)
  let ay := shown "\\usepackage[style=authoryear]{biblatex}\\addbibresource{refs.bib}"
    "\\printbibliography"
  t s!"letters: biblatex sets a to z, then aa and ab ({ay})"
    (letters.all (fun l => hasStr ay s!"(2020{l}). Work") &&
      hasStr ay "(2020z). Work 26" && hasStr ay "(2020aa). Work 27" && hasStr ay "(2020ab). Work 28")
  let nat := shown "\\usepackage{natbib}" "\\bibliographystyle{plainnat}\\bibliography{refs}"
  t s!"letters: plainnat sets a to z, then aa and ab ({nat})"
    (letters.all (fun l => hasStr nat s!", 2020{l}.") &&
      hasStr nat "Work 26, 2020z." && hasStr nat "Work 27, 2020aa." && hasStr nat "Work 28, 2020ab.")

/-- One entry for the view and inheritance checks. -/
def bibEntry (kind key : String) (fields : List (String × String)) : Bib.Entry :=
  { kind, key, fields := fields.toArray, pos := {} }

/-- The two views of one entry: biber reads BibTeX's spellings under biblatex's names, a BibTeX
style the reverse, and a view's own spelling wins. -/
def bibViewChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let months := Locale.en.months
  let bt := bibEntry "phdthesis" "k"
    [("author", "Doe, Jane"), ("journal", "J"), ("address", "A"), ("school", "S"),
     ("year", "2015"), ("month", "March")]
  let bv := bt.biberView
  t "views: biber reads a thesis as @thesis of type phdthesis"
    (bv.kind == "thesis" && bv.field? "type" == some "phdthesis")
  t "views: biber reads journal, address, school under biblatex's names"
    (bv.field? "journaltitle" == some "J" && bv.field? "location" == some "A" &&
      bv.field? "institution" == some "S")
  t "views: a legacy year and month are the date biber falls back to"
    (bv.dateParts months "" == .legacy "2015" (some "3") && (bv.field? "date").isNone)
  t "views: a legacy year that is no number is the date as written"
    ((bibEntry "misc" "k" [("year", "forthcoming")]).biberView.dateParts months "" ==
      .legacy "forthcoming" none)
  t "views: the label date is the date, else the event's, the original's, the visit's"
    ((bibEntry "online" "k" [("urldate", "2022-07-08")]).biberView.labelDate months ==
      some ("url", .parsed { start := some { year := 2022, month := some 7, day := some 8 } }) &&
      ((bibEntry "misc" "k" [("title", "T")]).biberView.labelDate months).isNone)
  let bl := bibEntry "thesis" "k"
    [("type", "mathesis"), ("journaltitle", "J"), ("location", "L"), ("institution", "U"),
     ("date", "2021-05-03")]
  let tv := bl.bibtexView months
  t "views: a BibTeX style reads @thesis of type mathesis as @mastersthesis, the type no text"
    (tv.kind == "mastersthesis" && (tv.field? "type").isNone)
  t "views: a BibTeX style reads journaltitle, location, institution and date"
    (tv.field? "journal" == some "J" && tv.field? "address" == some "L" &&
      tv.field? "school" == some "U" && tv.field? "year" == some "2021" &&
      tv.field? "month" == some "May")
  let both := bibEntry "article" "k" [("journal", "BibTeX's"), ("journaltitle", "biblatex's")]
  t "views: each view's own spelling wins"
    ((both.bibtexView months).field? "journal" == some "BibTeX's" &&
      both.biberView.field? "journaltitle" == some "biblatex's")
  t "views: a date the grammar cannot read reaches a BibTeX style as written"
    (((bibEntry "misc" "k" [("date", "Spring 2020")]).bibtexView months).field? "year" ==
      some "Spring 2020")

/-- Both inheritances, and which entries enter the list. -/
def bibInheritChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let months := Locale.en.months
  let parent := bibEntry "book" "p" [("title", "Parent"), ("publisher", "P"), ("crossref", "gp"),
    ("year", "2001")]
  let child := bibEntry "inbook" "c" [("author", "A"), ("crossref", "p"), ("pages", "1--2")]
  let bt := Bib.inheritBibtex child parent
  t "inherit: BibTeX copies a missing field under its own name, never the parent's crossref"
    (bt.field? "title" == some "Parent" && bt.field? "publisher" == some "P" &&
      bt.field? "crossref" == some "p" && bt.field? "pages" == some "1--2")
  let bb := Bib.inheritBiber Bib.biblatexInheritance child.biberView parent.biberView
  t "inherit: biber lends a book's title to its chapter as the booktitle, not the title"
    (bb.field? "booktitle" == some "Parent" && (bb.field? "title").isNone &&
      bb.field? "year" == some "2001")
  t "inherit: biber withholds the parent's crossref" (bb.field? "crossref" == some "p")
  let data := bibEntry "xdata" "d" [("publisher", "Shared"), ("location", "City")]
  let user := bibEntry "book" "u" [("title", "T"), ("xdata", "d"), ("location", "Own")]
  let db := Bib.Database.read .biber months #[data, user] #["u", "d"]
  t "inherit: xdata sets its fields over the entry's own, as biber does, and is never listed"
    (((db.entries.get? "u").bind (·.field? "publisher")) == some "Shared" &&
      ((db.entries.get? "u").bind (·.field? "location")) == some "City" &&
      ((db.entries.get? "u").bind (·.field? "title")) == some "T" &&
      db.list == #["u"])
  let gp := bibEntry "book" "gp" [("series", "Grand Series")]
  let chain := Bib.Database.read .bibtex months #[child, parent, gp] #["c"]
  t "inherit: a chain reaches the grandparent"
    (((chain.entries.get? "c").bind (·.field? "series")) == some "Grand Series")
  let a := bibEntry "misc" "a" [("crossref", "b"), ("title", "A")]
  let b := bibEntry "misc" "b" [("crossref", "a"), ("note", "B")]
  let cyc := Bib.Database.read .bibtex months #[a, b] #["a"]
  t "inherit: a cycle ends, each entry taking what the other has"
    (((cyc.entries.get? "a").bind (·.field? "note")) == some "B")
  let kids := #[bibEntry "inproceedings" "k1" [("crossref", "pr"), ("title", "One")],
    bibEntry "inproceedings" "k2" [("crossref", "pr"), ("title", "Two")],
    bibEntry "proceedings" "pr" [("title", "Proc"), ("year", "2018")]]
  let two := Bib.Database.read .bibtex months kids #["k1", "k2"]
  let one := Bib.Database.read .bibtex months kids #["k1"]
  t "inherit: two cited children list their parent after the cited keys"
    (two.list == #["k1", "k2", "pr"] &&
      ((two.entries.get? "k1").bind (·.field? "crossref")) == some "pr")
  t "inherit: one child leaves it out, and under BibTeX loses its crossref"
    (one.list == #["k1"] && ((one.entries.get? "k1").bind (·.field? "crossref")).isNone &&
      ((one.entries.get? "k1").bind (·.field? "year")) == some "2018")
  -- bibtex reads the file once, in order: an uncited parent before every child is passed.
  let first := #[bibEntry "proceedings" "pr" [("title", "Proc"), ("year", "2018")],
    bibEntry "inproceedings" "k1" [("crossref", "pr"), ("title", "One")],
    bibEntry "inproceedings" "k2" [("crossref", "pr"), ("title", "Two")]]
  let order := Bib.Database.read .bibtex months first #["k1", "k2"]
  t "inherit: under BibTeX a parent written before every child is never read"
    (((order.entries.get? "k1").bind (·.field? "year")).isNone &&
      ((order.entries.get? "k1").bind (·.field? "crossref")).isNone &&
      order.list == #["k1", "k2"] &&
      order.broken.map (fun r => (r.holder, r.target, r.fault)) ==
        #[("k1", "pr", .unread), ("k2", "pr", .unread)])
  let cited := Bib.Database.read .bibtex months first #["k1", "k2", "pr"]
  t "inherit: under BibTeX a parent written first and cited is read"
    (((cited.entries.get? "k1").bind (·.field? "year")) == some "2018" && cited.broken.isEmpty)
  let between := Bib.Database.read .bibtex months
    #[first[1]!, first[0]!, first[2]!] #["k1", "k2"]
  t "inherit: under BibTeX a parent after one cited child is read for every child"
    (((between.entries.get? "k2").bind (·.field? "year")) == some "2018" &&
      between.list == #["k1", "k2", "pr"] && between.broken.isEmpty)
  let biber := Bib.Database.read .biber months first #["k1", "k2"]
  t "inherit: biber resolves a parent written first"
    (((biber.entries.get? "k1").bind (·.field? "year")) == some "2018")

/-- Seven BibTeX styles set bibtex's lists, line for line against lualatex with bibtex, on the page
and in the HTML. -/
def bibtexOracleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib ← IO.FS.readFile s!"{bibProbeDir}/bibtex.bib"
  let keys := (← IO.FS.readFile s!"{bibProbeDir}/bibtex.keys").trimAscii.toString
  for style in ["plain", "unsrt", "abbrv", "alpha", "plainnat", "unsrtnat", "abbrvnat"] do
    let want := refLines (← IO.FS.readFile s!"{bibProbeDir}/bibtex-{style}.ref.txt")
    let pre := "\\usepackage{url}" ++ (if style.endsWith "nat" then "\n\\usepackage{natbib}" else "")
    let (doc, ds) := bibBuild (bibProbeDoc pre s!"\\bibliographystyle\{{style}}\\bibliography\{bibtex}" keys)
      #[("bibtex", bib)]
    let (entries, html) := bibShipped fonts doc
    t s!"bibtex {style}: no warning or error ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    t s!"bibtex {style}: the list holds bibtex's {want.size} entries ({entries.size})"
      (entries.size == want.size)
    for (w, k) in want.zipIdx do
      -- alpha's raised `+` reads back from lualatex's page as `+ `; the engine sets it inline.
      let w := bibPlain (w.replace "+ " "+")
      let got := (entries[k]?).getD ""
      t s!"bibtex {style}: entry {k + 1} is '{w}' ('{got}')" (got == w)
      t s!"bibtex {style}: the html reads entry {k + 1}" (hasStr html w)

/-- biblatex's two standard families set biber's lists under several option sets, line for line
against lualatex with biber, on the page and in the HTML. -/
def biblatexOracleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib ← IO.FS.readFile s!"{bibProbeDir}/biblatex.bib"
  let keys := (← IO.FS.readFile s!"{bibProbeDir}/biblatex.keys").trimAscii.toString
  let runs : List (String × String) :=
    [("style=numeric", "biblatex-numeric"), ("style=authoryear", "biblatex-authoryear")] ++
    (← ["biblatex-opt1", "biblatex-opt2", "biblatex-opt3", "biblatex-opt4"].mapM fun f => do
      let first := ((← IO.FS.readFile s!"{bibProbeDir}/{f}.ref.txt").splitOn "\n").headD ""
      pure (((first.dropPrefix? "# options: ").map (·.toString)).getD "", f))
  for (opts, file) in runs do
    let want := refLines (← IO.FS.readFile s!"{bibProbeDir}/{file}.ref.txt")
    let (doc, ds) := bibBuild (bibProbeDoc s!"\\usepackage[{opts}]\{biblatex}\n\\addbibresource\{biblatex.bib}"
      "\\printbibliography" keys) #[("biblatex", bib)]
    let (entries, html) := bibShipped fonts doc
    t s!"biblatex {opts}: no warning or error ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    t s!"biblatex {opts}: the list holds biber's {want.size} entries ({entries.size})"
      (entries.size == want.size)
    for (w, k) in want.zipIdx do
      let got := (entries[k]?).getD ""
      t s!"biblatex {opts}: entry {k + 1} is '{w}' ('{got}')" (got == bibPlain w)
      t s!"biblatex {opts}: the html reads entry {k + 1}" (hasStr html (bibPlain w))
  let dates ← IO.FS.readFile s!"{bibProbeDir}/dates.bib"
  for family in ["numeric", "authoryear"] do
    let want := refLines (← IO.FS.readFile s!"{bibProbeDir}/dates-{family}.ref.txt")
    let (doc, _) := bibBuild (bibProbeDoc s!"\\usepackage[style={family}]\{biblatex}\n\\addbibresource\{dates.bib}"
      "\\printbibliography" "*") #[("dates", dates)]
    let (entries, html) := bibShipped fonts doc
    t s!"biblatex dates {family}: the list holds biber's {want.size} entries ({entries.size})"
      (entries.size == want.size)
    for (w, k) in want.zipIdx do
      let got := (entries[k]?).getD ""
      t s!"biblatex dates {family}: entry {k + 1} is '{w}' ('{got}')" (got == bibPlain w)
      t s!"biblatex dates {family}: the html reads entry {k + 1}" (hasStr html (bibPlain w))
  let calls := ["\\textcite{n1}", "\\parencite{n1}", "\\textcite{n2,n3}", "\\parencite{o1}",
    "\\textcite{p1}"]
  let cites : List (String × List String) :=
    [("style=authoryear",
      ["Example, Smith, and Example Working Group (2003)",
       "(Example, Smith, and Example Working Group 2003)", "Smith (2002a) and Smith (2002b)",
       "(An Unsigned Web Resource 2023)", "Psi (2004)"]),
     ("style=authoryear,useprefix=true",
      ["van der Example, Smith, and Example Working Group (2003)",
       "(van der Example, Smith, and Example Working Group 2003)", "Smith (2002a) and Smith (2002b)",
       "(An Unsigned Web Resource 2023)", "Psi (2004)"])]
  for (opts, want) in cites do
    let body := String.join (calls.zipIdx.map fun (c, k) => s!"L{k + 1} {c} end.\n\n")
    let (doc, _) := bibBuild ("\\documentclass{article}\n" ++
      "\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" ++
      s!"\\usepackage[{opts}]\{biblatex}\n\\addbibresource\{biblatex.bib}\n\\begin\{document}\n" ++
      body ++ "\\printbibliography\n\\end{document}\n") #[("biblatex", bib)]
    let page := (bodyLines (layoutOf fonts doc)).map (bibPlain ∘ lineInk)
    let html := bibPlain (htmlVisibleText (HtmlDoc.emit {} doc).1)
    for (w, k) in want.zipIdx do
      let line := s!"L{k + 1} {w} end."
      t s!"biblatex {opts}: the page sets '{line}'" (page.contains line)
      t s!"biblatex {opts}: the html reads '{line}'" (hasStr html line)

/-- A citation probe against biber: `{probe}.bib` cited by `{probe}.body.tex` under each reference's
options, every citation line and the list compared. -/
def biblatexCiteProbe (ref : IO.Ref (List String)) (fonts : Font.FontSet) (probe : String)
    (names : List String) (width : String := "60cm") : IO Unit := do
  let t := check ref
  let bib ← IO.FS.readFile s!"{bibProbeDir}/{probe}.bib"
  let body ← IO.FS.readFile s!"{bibProbeDir}/{probe}.body.tex"
  for name in names do
    let text ← IO.FS.readFile s!"{bibProbeDir}/{probe}-{name}.ref.txt"
    let opts := ((((text.splitOn "\n").headD "").dropPrefix? "# options: ").map (·.toString)).getD ""
    let lines := refLines text
    let split := (lines.findIdx? (· == "References")).getD lines.size
    let cites := (lines.extract 0 split).map bibPlain
    let want := (lines.extract (split + 1) lines.size).map bibPlain
    let (doc, ds) := bibBuild ("\\documentclass{article}\n" ++
      s!"\\usepackage[paperwidth={width},paperheight=80cm,margin=1cm]\{geometry}\n" ++
      s!"\\usepackage[{opts}]\{biblatex}\n\\addbibresource\{{probe}.bib}\n\\begin\{document}\n" ++
      body ++ "\\printbibliography\n\\end{document}\n") #[(probe, bib)]
    let (entries, html) := bibShipped fonts doc
    let page := (bodyLines (layoutOf fonts doc)).map (bibAcros ∘ bibPlain ∘ lineInk)
    t s!"biblatex {probe} {opts}: no warning or error ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for c in cites do
      t s!"biblatex {probe} {opts}: the page sets '{c}'" (page.contains c)
      t s!"biblatex {probe} {opts}: the html reads '{c}'" (hasStr html c)
    t s!"biblatex {probe} {opts}: the list holds biber's {want.size} entries ({entries.size})"
      (entries.size == want.size)
    for (w, k) in want.zipIdx do
      let got := (entries[k]?).getD ""
      t s!"biblatex {probe} {opts}: entry {k + 1} is '{w}' ('{got}')" (got == w)

/-- biber's uniqueness in the citations and the list, against lualatex with biber. -/
def biblatexUniqueChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  biblatexCiteProbe ref (← mathSetOf oneFace) "uniq" ["authoryear", "authoryear-init",
    "authoryear-off", "authoryear-max2", "authoryear-allfull", "authoryear-prefix", "numeric"]
  -- `giveninits` turns `uniquename=full` into `init` and `allfull` into `allinit`.
  biblatexCiteProbe ref (← mathSetOf oneFace) "ginit" ["inits", "allfull"]

/-- biber's extended name format (`family=`, `given=`, `prefix=`, `suffix=`) against lualatex with
biber. -/
def biblatexXnameChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  biblatexCiteProbe ref (← mathSetOf oneFace) "xname" ["numeric", "authoryear", "authoryear-inits"]

/-- Every field standard.bbx's drivers print is printed, line for line against lualatex with biber. -/
def biblatexFieldCoverageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  biblatexCiteProbe ref (← mathSetOf oneFace) "fields" ["numeric", "authoryear"] "120cm"

/-- biber's order under numeric and authoryear, every citation's number or year and the list,
against lualatex with biber. -/
def biblatexSortChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  biblatexCiteProbe ref (← mathSetOf oneFace) "sort" ["numeric", "authoryear"] "120cm"

/-- One label date everywhere it prints, against lualatex with biber. -/
def biblatexLabelDateChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  biblatexCiteProbe ref (← mathSetOf oneFace) "ydate" ["numeric", "authoryear"] "120cm"

/-- A post-note's page prefix under numeric and authoryear, against lualatex with biber. -/
def biblatexPostnoteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  biblatexCiteProbe ref (← mathSetOf oneFace) "cite" ["numeric", "authoryear"] "120cm"

/-- A name's letters may be any script's: citations, order and `giveninits` initials, against
lualatex with biber. -/
def biblatexUnicodeNameChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  biblatexCiteProbe ref (← mathSetOf oneFace) "uname" ["numeric", "authoryear-inits"] "120cm"

/-- A BibTeX style reads a name's letters by their case, as biber does: the splits, initials,
alpha's labels and plain's order. -/
def bibUnicodeNameChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let n := Bib.parseName "Élise Varden"
  t s!"unicode names: an accented given name is no particle ({repr n})"
    (n.first == "Élise" && n.von.isEmpty && n.last == "Varden")
  let p := Bib.parseName "Élise de la Marne"
  t s!"unicode names: an accented given name before a particle ({repr p})"
    (p.first == "Élise" && p.von == "de la" && p.last == "Marne")
  let q := Bib.parseName "ébauche Ervin, Ola"
  t s!"unicode names: a lowercase accented particle is one ({repr q})" (q.von == "ébauche" && q.last == "Ervin")
  t "unicode names: an initial is the whole letter"
    (Bib.initials "Øyvind" == "Ø." && Bib.initials "Élan" == "É." && Bib.initials "Łucja" == "Ł." &&
      Bib.initials "E\u0301mil" == "E\u0301.")
  let bib ← IO.FS.readFile s!"{bibProbeDir}/uname.bib"
  let build (style : String) := bibBuild (bibProbeDoc "\\usepackage{url}"
    s!"\\bibliographystyle\{{style}}\\bibliography\{uname}" "*" "120cm") #[("uname", bib)]
  let (adoc, _) := build "abbrv"
  let (aentries, _) := bibShipped oneFace adoc
  t s!"unicode names: abbrv abbreviates accented given names ({aentries})"
    (aentries.any (hasStr · "É. Quill and Ø. Pell") && aentries.any (hasStr · "É. Varden and Ł. Hollin") &&
      aentries.any (hasStr · "É. de la Marne"))
  let (ldoc, _) := build "alpha"
  let (lentries, _) := bibShipped oneFace ldoc
  t s!"unicode names: alpha's label reads the particle and the family ({lentries})"
    (lentries.any (hasStr · "[dlM03]") && lentries.any (hasStr · "[VH02]"))
  let (pdoc, _) := build "plain"
  let (pentries, _) := bibShipped oneFace pdoc
  let pos (s : String) := (pentries.findIdx? (hasStr · s)).getD 99
  t s!"unicode names: plain sorts an accented family with its base letter ({pentries})"
    (pos "Ana Ångvik" < pos "Öra Ärnhelm" && pos "Öra Ärnhelm" < pos "Ola ébauche Ervin" &&
      pos "Émil Ostrow" < pos "Élan Quill" && pos "Élan Quill" < pos "Ana Zorvik")

/-- A date biber cannot read prints as written and is named once (W0420). -/
def bibUnreadDateChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let bib := "@article{u1, author = {Ann Alpha}, title = {No Such Day}, journaltitle = {J},\n\
      date = {2021-02-31}}\n\
    @article{u2, author = {Bo Beta}, title = {Two Digits}, journaltitle = {J}, date = {98}}\n\
    @article{u3, author = {Cy Gamma}, title = {A Season}, journaltitle = {J}, date = {Spring 2020}}\n\
    @article{u4, author = {Di Delta}, title = {A Month}, journaltitle = {J}, year = {2001},\n\
      month = {Midsummer}}\n"
  let (doc, ds) := bibBuild ("\\documentclass{article}\n" ++
    "\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" ++
    "\\usepackage[style=authoryear]{biblatex}\n\\addbibresource{u.bib}\n\\begin{document}\n" ++
    "U1 \\cite{u1} end.\n\nU3 \\cite{u3} end.\n\n\\nocite{*}\\printbibliography\n\\end{document}\n")
    #[("u", bib)]
  let named := ((ds.filter (·.code == "W0420")).filterMap (·.subject)).qsort (· < ·)
  t s!"unread dates: each is named once ({named})"
    (named == #["bibdate:u1:date", "bibdate:u2:date", "bibdate:u3:date", "bibdate:u4:month"])
  let (entries, _) := bibShipped oneFace doc
  let page := (bodyLines (layoutOf oneFace doc)).map (bibPlain ∘ lineInk)
  t s!"unread dates: the list prints each as written ({entries})"
    (entries.any (hasStr · "Alpha, Ann (2021-02-31)") && entries.any (hasStr · "Beta, Bo (98)") &&
      entries.any (hasStr · "Gamma, Cy (Spring 2020)") && entries.any (hasStr · "(Midsummer 2001)"))
  t s!"unread dates: the citations read them as the list does ({page})"
    (page.contains "U1 Alpha 2021-02-31 end." && page.contains "U3 Gamma Spring 2020 end.")

/-- The entries every check below reads: a URL inside a field, emphasis, a
formula, an accent, a date the grammar cannot read, a declared language. -/
def bibReadingBib : String :=
  "@misc{web, author = {Gil Gamma}, title = {A Note with \\emph{Emphasis} and $\\alpha^2$},\n\
    howpublished = {\\url{https://example.org/a_b?x=1&y=2}}, year = 2017,\n\
    note = {See the {\\\"U}ber page}, url = {https://example.org/web}}\n\
  @article{dated, author = {Ann Alpha}, title = {Dated}, journaltitle = {Example Letters},\n\
    date = {2021-05-03}, volume = {3}}\n\
  @article{season, author = {Bo Beta}, title = {Seasonal}, journal = {Example Letters},\n\
    date = {Spring 2020}}\n\
  @book{foreign, author = {Cy Gamma}, title = {Ein erfundenes Buch}, publisher = {Example Press},\n\
    date = {2016}, langid = {ngerman}}\n"

/-- A field means what it means in the body: `\url`, `\emph`, `$…$` and accents through the
document's own elaborator, in both artifacts. -/
def bibFieldReadingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := bibBuild (bibProbeDoc "\\usepackage{natbib}"
    "\\bibliographystyle{plainnat}\\bibliography{refs}" "web") #[("refs", bibReadingBib)]
  let (entries, html) := bibShipped oneFace doc
  let items := doc.body.foldl (fun acc b => match b with
    | .bibliography _ _ items => acc ++ items
    | _ => acc) #[]
  let content := (items.find? (·.key == "web")).map (·.content) |>.getD #[]
  let links := Ir.foldInlines (fun acc x => match x with
    | .link u _ => acc.push u
    | _ => acc) #[] content
  t s!"field reading: the \\url in howpublished is a link to its address ({links})"
    (links.contains "https://example.org/a_b?x=1&y=2")
  t "field reading: the page and the html read the address, not the command's name"
    (entries.any (hasStr · "https://example.org/a_b?x=1&y=2") && !hasStr html "urlhttps" &&
      hasStr html "https://example.org/a_b?x=1&y=2")
  t "field reading: \\emph is emphasis" (Ir.foldInlines (fun acc x => match x with
    | .styled .emph body => acc || Ir.plainText body == "Emphasis"
    | _ => acc) false content)
  t "field reading: $…$ is a formula, not its floor" (Ir.foldInlines (fun acc x => match x with
    | .formula .. => true
    | _ => acc) false content && !ds.any (·.code == "W0012"))
  t "field reading: an accent composes" (entries.any (hasStr · "See the Über page"))

/-- What a style drops is named once, and what reaches the page is correct. -/
def bibNamedChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let build (pre list keys : String) := bibBuild (bibProbeDoc pre list keys) #[("refs", bibReadingBib)]
  let (_, plainDs) := build "\\usepackage{url}" "\\bibliographystyle{plain}\\bibliography{refs}" "web,dated"
  let urlNotes := plainDs.filter fun d => d.code == "N0029" && d.subject == some "bibfield:url"
  t s!"named: plain names the url it prints nowhere, once ({urlNotes.map (·.message)})"
    (urlNotes.size == 1 && urlNotes.all (hasStr ·.message "web"))
  let (_, natDs) := build "\\usepackage{natbib}" "\\bibliographystyle{plainnat}\\bibliography{refs}" "web"
  t "named: plainnat prints the url and names nothing about it"
    (!natDs.any fun d => d.code == "N0029" && d.subject == some "bibfield:url")
  -- plainnat prints a @misc's howpublished and not a @manual's, so the note names the type.
  let hbib := "@misc{hm, author = {Ann Alpha}, title = {Notes}, howpublished = {Handed out}, \
    year = 2001}\n@manual{hn, author = {Bo Beta}, title = {Guide}, howpublished = {Posted}, \
    year = 2002}\n"
  let (hdoc, hds) := bibBuild (bibProbeDoc "\\usepackage{natbib}"
    "\\bibliographystyle{plainnat}\\bibliography{h}" "hm,hn") #[("h", hbib)]
  let (hentries, _) := bibShipped oneFace hdoc
  let hnotes := hds.filter fun d => d.code == "N0029" && d.subject == some "bibfield:howpublished"
  t s!"named: plainnat prints a @misc's howpublished ({hentries})"
    (hentries.any (hasStr · "Handed out") && !hentries.any (hasStr · "Posted"))
  t s!"named: the note names the @manual keeping one, by its type ({hnotes.map (·.message)})"
    (hnotes.size == 1 && hnotes.all fun d =>
      hasStr d.message "no 'howpublished' field in @manual entries" && hasStr d.message "(hn)")
  let (sdoc, sds) := build "\\usepackage[style=authoryear]{biblatex}\n\\addbibresource{refs.bib}"
    "\\printbibliography" "season,dated"
  let (sentries, _) := bibShipped oneFace sdoc
  t s!"named: a date biblatex cannot read is named ({(sds.filter (·.code == "W0420")).map (·.subject)})"
    ((sds.filter (·.code == "W0420")).map (·.subject) == #[some "bibdate:season:date"])
  t s!"named: it prints as written ({sentries})" (sentries.any (hasStr · "Spring 2020"))
  t "named: an entry with a date shows it, and no n.d."
    (sentries.any (hasStr · "Alpha, Ann (May 3, 2021)") && !sentries.any (hasStr · "n.d."))
  let (ndoc, _) := bibBuild (bibProbeDoc "\\usepackage[round]{natbib}"
    "\\bibliographystyle{plainnat}\\bibliography{refs}" "dated")
    #[("refs", bibReadingBib)]
  let (nentries, nhtml) := bibShipped oneFace ndoc
  t s!"named: a BibTeX style reads a biblatex date as its year ({nentries})"
    (nentries.any (hasStr · "May 2021") && !hasStr nhtml "n.d.")
  let (fdoc, _) := build "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{refs.bib}"
    "\\printbibliography" "foreign"
  let items := fdoc.body.foldl (fun acc b => match b with
    | .bibliography _ _ items => acc ++ items
    | _ => acc) #[]
  t "named: a declared language tags its entry"
    (items.any fun it => it.content.any fun x => match x with
      | .styled (.lang "de") _ => true
      | _ => false)
  let xbib := "@xdata{d, publisher = {Shared}}\n\
    @book{b, author = {Ann Alpha}, title = {T}, xdata = {d}, date = {2001}}\n"
  let (_, xds) := bibBuild (bibProbeDoc "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{x.bib}"
    "\\printbibliography" "*") #[("x", xbib)]
  t s!"named: \\nocite\{*} cites no @xdata entry ({xds.map (·.code)})" (!xds.any (·.code == "W0351"))
  let (_, vds) := build "\\usepackage[style=authoryear-comp,sorting=anyvt]{biblatex}\n\\addbibresource{refs.bib}"
    "\\printbibliography" "dated"
  t "named: a sorting scheme the engine does not sort by is named"
    (vds.any fun d => d.code == "W0101" && hasStr d.message "sorting=anyvt")
  t "named: a citation variant's own rules are named"
    (vds.any fun d => d.code == "W0101" && hasStr d.message "authoryear-comp")
  let mbib := "@article{m, author = {Ann Alpha}, title = {T}, journal = {J}, year = 2001,\n\
    month = {Spring}}\n"
  let (mdoc, mds) := bibBuild (bibProbeDoc "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{m.bib}"
    "\\printbibliography" "m") #[("m", mbib)]
  let (mentries, _) := bibShipped oneFace mdoc
  t s!"named: a month that names no month prints as written, named ({mentries})"
    (mds.any (fun d => d.code == "W0420" && d.subject == some "bibdate:m:month") &&
      mentries.any (hasStr · "(Spring 2001)"))
  let (adoc, _) := build "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{refs.bib}"
    "\\printbibliography" "dated"
  let (aentries, _) := bibShipped oneFace adoc
  t s!"named: an article's volume and date read 'Example Letters 3 (May 3, 2021)' ({aentries})"
    (aentries.any (hasStr · "Example Letters 3 (May 3, 2021)"))
  let nbib := "@article{n1, author = {Ann Alpha}, title = {T}, journaltitle = {J}, date = {2020},\n\
    school = {Sch}}\n@book{n2, author = {Bo Beta}, title = {B}, date = {2020}, eventdate = {2019},\n\
    publisher = {P}}\n"
  let (_, nds) := bibBuild (bibProbeDoc "\\usepackage[style=authoryear]{biblatex}\n\\addbibresource{n.bib}"
    "\\printbibliography" "*") #[("n", nbib), ("n.bib", nbib)]
  let dropped := nds.filter (·.code == "N0029")
  t s!"named: a dropped field is named as the .bib spells it, a date no label reads among them \
    ({dropped.map (·.subject)})"
    (dropped.any (·.subject == some "bibfield:school") &&
      dropped.any (·.subject == some "bibfield:eventdate") &&
      !dropped.any (·.subject == some "bibfield:institution") &&
      dropped.all (hasStr ·.message "biblatex's authoryear style prints no"))

/-- A list biblatex words in another language is named once. -/
def bibLanguageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := "@article{en1, author = {Ann Alpha}, title = {One}, journaltitle = {J}, \
    date = {2021}, langid = {english}}\n\
    @article{fr1, author = {Bo Beta}, title = {Deux}, journaltitle = {J}, date = {2020}, \
    langid = {french}}\n"
  let build (pre : String) := bibBuild (bibProbeDoc (pre ++ "\n\\addbibresource{refs.bib}")
    "\\printbibliography" "*") #[("refs", bib)]
  let named (ds : Array Diag) := (ds.filter (·.code == "W0421")).map (·.subject)
  let words (doc : Ir.Doc) : Array String := doc.body.foldl (fun acc b => match b with
    | .bibliography _ _ items => acc ++ items.map (Ir.plainText ·.content)
    | _ => acc) #[]
  let (gdoc, gds) := build "\\usepackage[ngerman]{babel}\n\\usepackage[style=numeric]{biblatex}"
  t s!"language: a German document's list is named once ({named gds})"
    (named gds == #[some "bibstrings:ngerman"])
  let (_, ads) := build "\\usepackage[style=numeric]{biblatex}\n\\usepackage[ngerman]{babel}"
  t s!"language: babel loaded after biblatex names it too ({named ads})"
    (named ads == #[some "bibstrings:ngerman"])
  let (_, uds) := build "\\usepackage[american]{babel}\n\\usepackage[style=numeric]{biblatex}"
  t s!"language: babel's american is named ({named uds})" (named uds == #[some "bibstrings:american"])
  let (_, lds) := build "\\usepackage[ngerman]{babel}\n\\usepackage[style=numeric,language=english]{biblatex}"
  t s!"language: language=english names nothing ({named lds})" (named lds).isEmpty
  let (edoc, eds) := build "\\usepackage[style=numeric]{biblatex}"
  t s!"language: an English document names nothing ({named eds})" (named eds).isEmpty
  t s!"language: the German document's list is the English one ({words gdoc})"
    (words gdoc == words edoc && !(words edoc).isEmpty)
  let (_, ods) := build "\\usepackage[style=numeric,autolang=other]{biblatex}"
  t s!"language: under autolang=other the French entry is named, the English one not ({named ods})"
    (named ods == #[some "bibstrings:french"])
  let (_, bds) := build "\\usepackage[style=numeric,babel=other]{biblatex}"
  t s!"language: babel=other, autolang's former name, reads as it ({named bds})"
    (named bds == #[some "bibstrings:french"])
  let (_, nds) := bibBuild ("\\documentclass{article}\n\\usepackage[ngerman]{babel}\n" ++
    "\\usepackage[style=numeric]{biblatex}\n\\begin{document}\nx\n\\end{document}\n")
    #[("refs", bib)]
  t s!"language: a document that prints no list names nothing ({named nds})" (named nds).isEmpty

/-- A cited `@set` is named once and its members are listed each as an entry. -/
def bibSetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := "@set{st1, entryset = {m1,m2}}\n\
    @article{m1, author = {Ann Alpha}, title = {One}, journaltitle = {J}, date = {2001}}\n\
    @article{m2, author = {Bo Beta}, title = {Two}, journaltitle = {J}, date = {2002}}\n"
  let build (body : String) := bibBuild ("\\documentclass{article}\n" ++
    "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{refs.bib}\n\\begin{document}\n" ++
    body ++ "\n\\printbibliography\n\\end{document}\n") #[("refs", bib)]
  let keys (doc : Ir.Doc) : Array String := doc.body.foldl (fun acc b => match b with
    | .bibliography _ _ items => acc ++ items.map (·.key)
    | _ => acc) #[]
  let (doc, ds) := build "A \\cite{st1} B \\cite{m2} end."
  let named := (ds.filter (·.code == "W0422")).map (·.subject)
  t s!"set: a cited @set is named once ({named})" (named == #[some "bibset:st1"])
  t s!"set: its members are listed each as an entry ({keys doc})" (keys doc == #["m1", "m2"])
  t s!"set: no citation of it is unresolved ({ds.map (·.code)})" (!ds.any (·.code == "W0351"))
  let html := htmlVisibleText (HtmlDoc.emit {} doc).1
  t "set: the set cites as its first member" (hasStr html "A [1] B [2] end.")
  let (mdoc, mds) := build "B \\cite{m1} end."
  t s!"set: a member cited alone is listed alone, unnamed ({keys mdoc})"
    (keys mdoc == #["m1"] && !mds.any (·.code == "W0422"))

/-- An entry's related entries are named (W0423), not set. -/
def bibRelatedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := "@book{k, author = {Ann Alpha}, title = {A Reprint}, date = {2020}, related = {r},\n\
      relatedtype = {reprintof}}\n@book{r, author = {Ann Alpha}, title = {The Original}, date = {1990}}\n"
  let (doc, ds) := bibBuild (bibProbeDoc "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{refs.bib}"
    "\\printbibliography" "k") #[("refs", bib)]
  let keys := doc.body.foldl (fun acc b => match b with
    | .bibliography _ _ items => acc ++ items.map (·.key)
    | _ => acc) #[]
  t s!"related: the entry is listed ({keys})" (keys == #["k"])
  t s!"related: what it names is named once ({(ds.filter (·.code == "W0423")).map (·.subject)})"
    ((ds.filter (·.code == "W0423")).map (·.subject) == #[some "bibrelated:k"])

/-- A `.bib`'s `@preamble` is in force where its list is typeset and nowhere in what sorts it. -/
def bibPreambleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let bib := "@preamble{ \"\\newcommand{\\noopsort}[1]{}\" # \"\\def\\twice#1{#1#1}\" }\n\
    @preamble{ {\\providecommand{\\noopsort}[1]{#1}\\newcommand{\\both}[2]{\\twice{#1}#2}} }\n\
    @misc{late, author = {Ann Alpha}, title = {Late \\both{a}{b}}, year = {{\\noopsort{1999}}2001}}\n\
    @misc{early, author = {Ann Alpha}, title = {Early}, year = {2000}}\n"
  let (doc, ds) := bibBuild (bibProbeDoc "\\usepackage{url}"
    "\\bibliographystyle{plain}\\bibliography{refs}" "*") #[("refs", bib)]
  let (entries, _) := bibShipped oneFace doc
  t s!"preamble: its commands print as defined ({entries})"
    (entries.size == 2 && (entries[0]?.any (hasStr · "Late aab, 2001.")) &&
      (entries[1]?.any (hasStr · "Early, 2000.")))
  t s!"preamble: no command it defines is unknown ({(ds.filter (·.code == "W0301")).map (·.subject)})"
    (!ds.any (·.code == "W0301"))
  t "preamble: a use expands, its arguments in place"
    (Bib.expandMacros (Bib.preambleMacros #["\\newcommand{\\pair}[2]{(#1,#2)}"])
      "a \\pair{x}{\\pair{y}{z}} b" == "a (x,(y,z)) b")

/-- Every named `.bib` is read, and a key two files hold is the first file's. -/
def bibSourcesChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let a := "@article{a1, author = {Ann Alpha}, title = {One}, journal = {J}, year = 2001}\n\
    @article{dup, author = {Cy First}, title = {First}, journal = {J}, year = 2003}\n"
  let b := "@article{b1, author = {Bo Beta}, title = {Two}, journal = {J}, year = 2002}\n\
    @article{dup, author = {Di Second}, title = {Second}, journal = {J}, year = 2004}\n"
  let items (doc : Ir.Doc) : Array Ir.BibItem := doc.body.foldl (fun acc b => match b with
    | .bibliography _ _ items => acc ++ items
    | _ => acc) #[]
  let bad (ds : Array Diag) := ds.filter fun d => d.code.startsWith "W" || d.code.startsWith "E"
  let (ndoc, nds) := bibBuild (bibProbeDoc "\\usepackage{natbib}"
    "\\bibliographystyle{plainnat}\\bibliography{a, b}" "a1,b1,dup") #[("a", a), ("b", b)]
  t s!"sources: \\bibliography\{a, b} reads both files ({(items ndoc).map (·.key)}, {(bad nds).map (·.code)})"
    ((items ndoc).size == 3 && (["a1", "b1", "dup"].all fun k => (items ndoc).any (·.key == k)) &&
      (bad nds).isEmpty)
  t "sources: a key two files hold is the first file's"
    ((items ndoc).any fun it => it.key == "dup" && hasStr (Ir.plainText it.content) "First")
  let (missingDs, kept) ← IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "kept.bib") "@misc{k, author = {Ann Alpha}, title = {Kept}, year = 2024}\n"
    let doc := (elabStr ("\\documentclass{article}\n\\begin{document}\nA claim\\cite{k}.\n\
      \\bibliography{" ++ (dir / "kept").toString ++ ", references}\n\\end{document}\n")).1
    let (doc, ds, _) ← Input.resolveBibliography "doc.tex" doc Bib.plainReading #[]
    return (ds, items doc)
  t s!"sources: a file of several not there is named ({missingDs.map (·.code)})"
    (missingDs.any (·.code == "W0424") && !missingDs.any (·.code.startsWith "E"))
  t s!"sources: the list holds the other file's entries ({kept.map (·.key)})" (kept.map (·.key) == #["k"])
  let (bdoc, bds) := bibBuild (bibProbeDoc
    "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{a.bib}\n\\addbibresource{b.bib}"
    "\\printbibliography" "a1,b1") #[("a", a), ("b", b)]
  t s!"sources: a second \\addbibresource is read ({(items bdoc).map (·.key)}, {(bad bds).map (·.code)})"
    ((items bdoc).map (·.key) == #["a1", "b1"] && (bad bds).isEmpty)
  let (rdoc, rds) := bibBuild (bibProbeDoc
    "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{a.bib}\n\\addbibresource[location=remote]{https://example.org/b.bib}"
    "\\printbibliography" "a1") #[("a", a), ("b", b)]
  t s!"sources: a remote resource is named and skipped, the local one read ({(items rdoc).map (·.key)}, {rds.map (·.code)})"
    ((items rdoc).map (·.key) == #["a1"] && rds.any (fun d => d.code == "W0104" &&
      d.subject == some "addbibresource") && !rds.any (·.code.startsWith "E"))
  let unknown := "@article{u1, author = {Ann Alpha}, title = {A \\zzbib{} Title}, journal = {J}, year = 2001}\n\
    @article{u2, author = {Bo Beta}, title = {Another \\zzbib{} Title}, journal = {J}, year = 2002}\n"
  let (_, uds) := bibBuild (bibProbeDoc "\\usepackage{natbib}"
    "Body \\zzbib{} text.\n\\bibliographystyle{plainnat}\\bibliography{u}" "u1,u2") #[("u", unknown)]
  let counted := (Diag.tallySites uds).filter (·.subject == some "ctrl:zzbib")
  t s!"sources: a loss the fields raise counts with the body's ({counted.map (·.sites)})"
    (counted.size == 3 && (counted.map (·.sites)).foldl (· + ·) 0 == 3 &&
      (counted.map (·.sites)).toList.count 0 == 2)
  -- `Bib.demoteRepeated` before the tally: the body's site warns, the fields' are notes.
  let file := "t.tex"
  let (toks, ld) := Lex.lex file (bibProbeDoc "\\usepackage{natbib}"
    "Body \\zzbib{} text.\n\\bibliographystyle{plainnat}\\bibliography{u}" "u1,u2")
  let (raws, pd) := Parse.parse file toks
  let prepared := Elab.prepare file raws
  let (udoc, eds) := Elab.runPreparedFinal file prepared (ld ++ pd) (fun _ _ => {})
  let (_, bds) := Bib.resolve file prepared #[("u", unknown)] udoc
  let told := (Diag.tallySites (eds ++ Bib.demoteRepeated eds bds)).filter
    (·.subject == some "ctrl:zzbib")
  t s!"sources: a loss the fields repeat is told once, at the body's site \
    ({told.map fun d => (d.demoted, d.sites)})"
    (told.size == 3 && (told[0]?.any fun d => !d.demoted && d.sites == 3) &&
      (told.extract 1 told.size).all fun d => d.demoted && d.help.isNone && d.sites == 0)
  let fieldsOnly := Bib.demoteRepeated #[] bds |>.filter (·.subject == some "ctrl:zzbib")
  t "sources: with no body site, the first field's site is the warning"
    (fieldsOnly.size == 2 && (fieldsOnly[0]?.any (!·.demoted)) &&
      (fieldsOnly[1]?.any (·.demoted)))

/-- Plain field text needs no elaborator: every text `asWritten?` accepts sets as the elaborator
sets it. -/
def bibAsWrittenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := "\\documentclass{article}\n\\begin{document}\nx\n\\end{document}\n"
  let (toks, _) := Lex.lex "t.tex" src
  let (raws, _) := Parse.parse "t.tex" toks
  let p := Elab.prepare "t.tex" raws
  let full := (Bib.FieldDoor.of "t.tex" p).readFull
  let alphabet := "abcXYZ019 .,;:!?()/+=*@-\n".toList.toArray
  let mut seed : UInt64 := 0x2545F4914F6CDD1D
  let mut samples : Array String := #["Sam Roe", "A Study of Placeholders", "Low-Rank Methods",
    "e.g. (see below): yes; no!", "Vol. 2/3", "TR-9", "line\nbreak", "Example Press, Exampleville",
    "{DNA} Methods", "x {{nested}} y", "a { } b", "a{}b", "{A} {B}"]
  for _ in [0:400] do
    let mut s := ""
    seed := seed ^^^ (seed >>> 12)
    let n := (seed % 24).toNat + 1
    for _ in [0:n] do
      seed := seed ^^^ (seed <<< 25)
      seed := seed ^^^ (seed >>> 27)
      s := s.push (alphabet[((seed * 0x2545F4914F6CDD1D) >>> 40).toNat % alphabet.size]!)
    -- a third of them with a group around a stretch of their middle
    if seed % 3 == 0 && s.length > 2 then
      let a := (seed >>> 7).toNat % s.length
      let b := a + 1 + (seed >>> 17).toNat % (s.length - a)
      s := (s.take a).toString ++ "{" ++ ((s.drop a).take (b - a)).toString ++ "}" ++
        (s.drop b).toString
    samples := samples.push s
  let mut accepted := 0
  for s in samples do
    match Bib.asWritten? s.trimAscii.toString with
    | some w =>
      accepted := accepted + 1
      let (out, _) := full ⟨"refs.bib", {}⟩ s.trimAscii.toString
      let fast : Array Ir.Inline := if w.isEmpty then #[] else #[.text w]
      t s!"as written: {repr s} sets as the elaborator sets it ({repr out})" (out == fast)
    | none => pure ()
  t s!"as written: the drawn texts reach the fast path ({accepted} of {samples.size})"
    (accepted > samples.size / 2)
  t "as written: TeX's own spellings go to the elaborator"
    (["M{\\\"u}ller", "--", "a~b", "$x$", "it's", "\\emph{x}", "100\\%", "``q''", "é", "{a", "a}"].all
      (Bib.asWritten? · |>.isNone))

/-- A reference file's citation lines and its list's entries, split at its
`References` line. -/
def refParts (text : String) : Array String × Array String :=
  let lines := refLines text
  let split := (lines.findIdx? (· == "References")).getD lines.size
  ((lines.extract 0 split).map bibPlain, (lines.extract (split + 1) lines.size).map bibPlain)

/-- A probe page around `body` and a BibTeX list. -/
def bibtexPage (body list : String) (pre : String := "") : String :=
  "\\documentclass{article}\n\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" ++
    pre ++ "\n\\begin{document}\n" ++ body ++ list ++ "\n\\end{document}\n"

/-- A field's citation completes the list, and a field's citation of no entry is W0351 at the citing
entry. -/
def bibFieldCiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib ← IO.FS.readFile s!"{bibProbeDir}/fcite.bib"
  let body ← IO.FS.readFile s!"{bibProbeDir}/fcite.body.tex"
  for style in ["plain", "unsrt"] do
    let (cites, want) := refParts (← IO.FS.readFile s!"{bibProbeDir}/fcite-{style}.ref.txt")
    let (doc, ds) := bibBuild (bibtexPage body s!"\\bibliographystyle\{{style}}\\bibliography\{fcite}")
      #[("fcite", bib)]
    let (entries, html) := bibShipped fonts doc
    let page := (bodyLines (layoutOf fonts doc)).map (bibPlain ∘ lineInk)
    t s!"field cites {style}: no warning or error ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for c in cites do
      t s!"field cites {style}: the page sets '{c}'" (page.contains c)
    t s!"field cites {style}: the list holds bibtex's {want.size} entries ({entries})"
      (entries == want)
    for w in want do
      t s!"field cites {style}: the html reads '{w}'" (hasStr html w)
  biblatexCiteProbe ref fonts "fcite" ["authoryear", "numeric-none"]
  let missing := "@misc{a1, author = {Ann Alpha}, year = 2020, title = {First}, \
    note = {Reprinted as \\cite{nowhere}}}\n"
  let (doc, ds) := bibBuild (bibtexPage "Body \\cite{a1}.\n\n" "\\bibliographystyle{plain}\\bibliography{m}")
    #[("m", missing)]
  let (entries, _) := bibShipped fonts doc
  let w := ds.filter fun d => d.code == "W0351" && d.subject == some "nowhere"
  t s!"field cites: a field's citation of no entry is W0351 at the citing entry ({w.map (·.span.map (·.file))})"
    (w.size == 1 && w.all (fun d => (d.span.map (·.file)) == some "m.bib") &&
      entries == #["[1] Ann Alpha. First, 2020. Reprinted as [?]."])

/-- One `@string` store across a list's files, and a macro no `@string` defines prints its name,
named once (W0426). -/
def bibStringStoreChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bibs ← #["strings-a", "strings-b", "strings-c"].mapM fun n => do
    pure (n, ← IO.FS.readFile s!"{bibProbeDir}/{n}.bib")
  let bibs := bibs ++ bibs.map fun (n, b) => (n ++ ".bib", b)
  let runs : List (String × String × String) :=
    [("plain", "", "\\bibliographystyle{plain}\\bibliography{strings-a,strings-b,strings-c}"),
     ("numeric", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{strings-a.bib}\n\
       \\addbibresource{strings-b.bib}\n\\addbibresource{strings-c.bib}", "\\printbibliography")]
  for (name, pre, list) in runs do
    let (_, want) := refParts (← IO.FS.readFile s!"{bibProbeDir}/strings-{name}.ref.txt")
    let (doc, ds) := bibBuild (bibProbeDoc pre list "a1,b1,b2") bibs
    let (entries, _) := bibShipped fonts doc
    t s!"strings {name}: no warning or error ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    t s!"strings {name}: the list is the reference's ({entries})" (entries == want)
  let undefinedBib := "@article{u1, author = {Ann Alpha}, title = {One}, journal = nojt, year = 2001}\n\
    @article{u2, author = {Bo Beta}, title = {Two}, journal = nojt, year = 2002}\n"
  let (doc, ds) := bibBuild (bibProbeDoc "" "\\bibliographystyle{plain}\\bibliography{u}" "u1,u2")
    #[("u", undefinedBib)]
  let (entries, _) := bibShipped fonts doc
  let w := (ds.filter (·.code == "W0426"))
  t s!"strings: an undefined macro is named once, its sites counted ({w.map fun d => (d.subject, d.sites, d.demoted)})"
    (w.all (·.subject == some "bibstring:nojt") && (w.filter (!·.demoted)).size == 1 &&
      (w.map (·.sites)).foldl (· + ·) 0 == 2 && entries.all (hasStr · "nojt"))

/-- The label column holds the widest label: every entry's text starts the widest label and
`\labelsep` in. -/
def bibLabelColumnChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let bib := "@article{w1, author = {Ann Alpha and Bo Beta}, title = {Short Label}, journal = {J}, year = 2021}\n\
    @article{w2, author = {Cy de la Gamma and Di Delta and Ed Epsilon and Flo Zeta and Gus Eta}, \
      title = {A Long Label}, journal = {J}, year = 2019}\n\
    @misc{w3, author = {Hal Theta}, title = {Middle Label}, year = 2020}\n"
  for (pageDecl, tag) in [("", "article page"), ("\\usepackage[margin=1cm]{geometry}", "1 cm margins")] do
    let (doc, _) := bibBuild (bibtexPage "Text \\cite{w1}, \\cite{w2}, \\cite{w3}.\n\n"
      "\\bibliographystyle{alpha}\\bibliography{w}" pageDecl |>.replace
        "\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" "") #[("w", bib)]
    let left := (Layout.Geom.ofPage doc.page).hmargin
    let firsts := (bibEntryLines (bodyLines (layoutOf oneFace doc))).filterMap (·[0]?)
    let runs := firsts.map metricRunsAt
    let labelXs := runs.filterMap fun rs => rs[0]?.map (·.2)
    let textXs := runs.filterMap fun rs => rs[1]?.map (·.2)
    t s!"label column ({tag}): three entries, each a label and its text ({runs.map (·.size)})"
      (firsts.size == 3 && runs.all (·.size ≥ 2))
    t s!"label column ({tag}): no label starts left of the text block ({labelXs} ≥ {left})"
      (labelXs.all (· ≥ left))
    t s!"label column ({tag}): the widest label starts at the text block's edge ({labelXs})"
      (labelXs.any (· == left))
    t s!"label column ({tag}): every entry's text starts at one place ({textXs})"
      (textXs.size == 3 && textXs.all (· == textXs[0]!))

/-- biber's sort locales, line for line against biber, and a locale of another script named (W0427). -/
def biblatexLocaleSortChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  biblatexCiteProbe ref fonts "loc" ["root", "sv", "da", "nb", "fi", "dephone", "es", "estrad",
    "pl", "cs", "tr", "hu", "hr", "is", "frca", "cy"]
  let bib ← IO.FS.readFile s!"{bibProbeDir}/loc.bib"
  let (_, sv) := refParts (← IO.FS.readFile s!"{bibProbeDir}/loc-sv.ref.txt")
  let (doc, _) := bibBuild (bibProbeDoc "\\usepackage[swedish]{babel}\n\
    \\usepackage[style=numeric,language=english,autolang=hyphen]{biblatex}\n\\addbibresource{loc.bib}"
    "\\printbibliography" "*") #[("loc", bib), ("loc.bib", bib)]
  let (entries, _) := bibShipped fonts doc
  t s!"sort locale: babel's swedish sorts the list as sortlocale=sv_SE ({entries.size})"
    (entries == sv)
  let (_, ds) := bibBuild (bibProbeDoc "\\usepackage[style=numeric,sortlocale=ja_JP]{biblatex}\n\
    \\addbibresource{loc.bib}" "\\printbibliography" "*") #[("loc", bib), ("loc.bib", bib)]
  t s!"sort locale: a tailoring of another script is named ({(ds.filter (·.code == "W0427")).map (·.subject)})"
    ((ds.filter (·.code == "W0427")).map (·.subject) == #[some "bibsort:ja"])
  biblatexCiteProbe ref fonts "lang" ["clearlang", "numeric"]

/-- A reference naming no entry is named (W0425) and costs nothing else. -/
def bibRefChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let xdata := "@book{u1, author = {Ann Alpha}, title = {Xdata After Missing Keys}, date = {2020}, \
    xdata = {m1, m2, m3, d1}}\n@xdata{d1, publisher = {Shared Press}, location = {Shared City}}\n"
  let (doc, ds) := bibBuild (bibProbeDoc "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{x.bib}"
    "\\printbibliography" "u1") #[("x", xdata), ("x.bib", xdata)]
  let (entries, _) := bibShipped fonts doc
  t s!"refs: xdata past three missing keys lends the fourth's fields, as biber ({entries})"
    (entries == #["[1] Ann Alpha. Xdata After Missing Keys. Shared City: Shared Press, 2020."])
  t s!"refs: each missing xdata key is named ({(ds.filter (·.code == "W0425")).map (·.subject)})"
    ((ds.filter (·.code == "W0425")).map (·.subject) ==
      #[some "bibref:m1", some "bibref:m2", some "bibref:m3"])
  let cross := "@inbook{c1, author = {Ann Alpha}, title = {Child of a Missing Parent}, \
      crossref = {nosuch}, pages = {1--2}}\n\
    @inbook{c2, author = {Bo Beta}, title = {Child With Upper Key}, crossref = {PARENT}, pages = {3--4}}\n\
    @book{parent, editor = {Cy Gamma}, title = {The Parent Book}, publisher = {Pub}, year = 2001}\n"
  let (doc, ds) := bibBuild (bibProbeDoc "" "\\bibliographystyle{plain}\\bibliography{x}" "c1,c2")
    #[("x", cross)]
  let (entries, _) := bibShipped fonts doc
  t s!"refs: bibtex's list, the parent found whatever its key's case ({entries})"
    (entries == #["[1] Ann Alpha. Child of a Missing Parent, pages 1–2.",
      "[2] Bo Beta. Child With Upper Key, pages 3–4. Pub, 2001."])
  t s!"refs: a crossref naming no entry is named under bibtex ({(ds.filter (·.code == "W0425")).map (·.subject)})"
    ((ds.filter (·.code == "W0425")).map (·.subject) == #[some "bibref:nosuch"])
  let (_, bds) := bibBuild (bibProbeDoc "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{x.bib}"
    "\\printbibliography" "c2") #[("x", cross), ("x.bib", cross)]
  let named := bds.filter (·.code == "W0425")
  t s!"refs: biber matches keys exactly, and the help names the entry differing in case ({named.map (·.help)})"
    (named.size == 1 && named.all fun d => d.subject == some "bibref:PARENT" &&
      (d.help.any (hasStr · "'parent'")))
  let gone := (List.range 40).map (s!"gone{·}")
  let user := bibEntry "book" "u" [("title", "T"), ("xdata", ", ".intercalate (gone ++ ["d"]))]
  let data := bibEntry "xdata" "d" [("publisher", "Pub")]
  let db := Bib.Database.read .biber #[] #[user, data] #["u"]
  t "refs: forty missing keys before the data entry end no walk early"
    (((db.entries.get? "u").bind (·.field? "publisher")) == some "Pub" && db.broken.size == 40)

/-- A field's text reads as the body's: each command the body translates sets the same in a `.bib`
field. -/
def bibFieldCompatChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let snippets := ["R \\relax{}x", "M \\mbox{m b}", "K \\makebox{mk}", "B \\raisebox{1pt}{rb}",
    "F \\foreignlanguage{german}{Wort}", "Q \\enquote{q}", "S a\\space b", "{\\relax Ch}ristopher"]
  for s in snippets do
    let bib := s!"@misc\{f1, author = \{Ann Alpha}, year = 2020, title = \{T}, note = \{N1 {s} N2}}\n"
    let (doc, ds) := bibBuild (bibtexPage s!"B1 {s} B2.\n\n\\nocite\{f1}"
      "\\bibliographystyle{plain}\\bibliography{f}"
      "\\usepackage[german,english]{babel}\n\\usepackage{csquotes}") #[("f", bib)]
    let html := bibPlain (htmlVisibleText (HtmlDoc.emit {} doc).1)
    let bodyText := (((html.splitOn "B1 ")[1]?.getD "").splitOn " B2")[0]?.getD "?"
    let fieldText := (((html.splitOn "N1 ")[1]?.getD "").splitOn " N2")[0]?.getD "!"
    t s!"field compat: '{s}' sets in a field as in the body ('{fieldText}' and '{bodyText}')"
      (fieldText == bodyText)
    t s!"field compat: '{s}' raises no unknown command in the field"
      (!ds.any fun d => d.code == "W0301" && (d.span.map (·.file)) == some "f.bib")

/-- biblatex's citation commands, on the page and in the HTML, against biber under authoryear and
numeric. -/
def biblatexCiteCommandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  biblatexCiteProbe ref fonts "cmdcite" ["authoryear", "numeric"]
  let bib ← IO.FS.readFile s!"{bibProbeDir}/cmdfoot.bib"
  let body ← IO.FS.readFile s!"{bibProbeDir}/cmdfoot.body.tex"
  for style in ["authoryear", "numeric"] do
    let (cites, rest) := refParts (← IO.FS.readFile s!"{bibProbeDir}/cmdfoot-{style}.ref.txt")
    -- the list's entries, then the footnotes' lines, each its mark and text
    let notes := (rest.filter fun l => (l.toList.head?.any Char.isDigit) && !l.startsWith "[").map
      fun l => ((l.dropWhile Char.isDigit).trimAscii.toString)
    let (doc, ds) := bibBuild ("\\documentclass{article}\n\
      \\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n\
      \\usepackage[style=" ++ style ++ "]{biblatex}\n\\addbibresource{cmdfoot.bib}\n\\begin{document}\n" ++
      body ++ "\\printbibliography\n\\end{document}\n") #[("cmdfoot", bib), ("cmdfoot.bib", bib)]
    let page := (bodyLines (layoutOf fonts doc)).map (bibPlain ∘ lineInk)
    let html := bibPlain (htmlVisibleText (HtmlDoc.emit {} doc).1)
    t s!"footnote citations {style}: no warning or error ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
      (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
    for c in cites do
      t s!"footnote citations {style}: the page sets '{c}'" (page.contains c)
    t s!"footnote citations {style}: four notes measured ({notes})" (notes.size == 4)
    for n in notes do
      t s!"footnote citations {style}: a note reads '{n}'" (page.any (·.endsWith n) && hasStr html n)

/-- What a list's entry names elsewhere resolves: `ids` aliases, a field's `\ref`, and a preamble
`\bibliography{refs}`. -/
def bibElsewhereChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let ids := "@article{newkey, ids = {oldkey}, author = {Ann Alpha}, title = {Aliased}, \
    journaltitle = {J}, date = {2001}}\n"
  let (doc, ds) := bibBuild ("\\documentclass{article}\n\\usepackage[style=authoryear]{biblatex}\n\
    \\addbibresource{i.bib}\n\\begin{document}\nL1 \\textcite{oldkey} end.\n\n\\printbibliography\n\
    \\end{document}\n") #[("i", ids), ("i.bib", ids)]
  let page := (bodyLines (layoutOf fonts doc)).map (bibPlain ∘ lineInk)
  t s!"elsewhere: an ids alias cites its entry ({(ds.filter (·.code == "W0351")).map (·.subject)})"
    (page.contains "L1 Alpha (2001) end." && !ds.any (·.code == "W0351"))
  let refBib := "@misc{r1, author = {Ann Alpha}, title = {T}, year = 2020, \
    note = {See Section~\\ref{sec:two}}}\n"
  let (doc, ds) := bibBuild ("\\documentclass{article}\n\\begin{document}\n\\section{One}\nx\n\n\
    \\section{Two}\\label{sec:two}\nBody Section~\\ref{sec:two}.\n\n\\nocite{r1}\\bibliographystyle{plain}\
    \\bibliography{r}\n\\end{document}\n") #[("r", refBib)]
  let (entries, html) := bibShipped fonts doc
  t s!"elsewhere: a field's \\ref sets the body's number ({entries})"
    (entries == #["[1] Ann Alpha. T, 2020. See Section 2."] && hasStr html "See Section 2." &&
      !ds.any (·.code == "W0349"))
  let legacy := "@book{a1, author = {Ann Alpha}, title = {First}, date = {2001}, publisher = {Pub}}\n"
  let (doc, ds) := bibBuild ("\\documentclass{article}\n\\usepackage[style=numeric]{biblatex}\n\
    \\bibliography{refs}\n\\begin{document}\nL1 \\cite{a1} end.\n\n\\printbibliography\n\\end{document}\n")
    #[("refs", legacy), ("refs.bib", legacy)]
  let page := (bodyLines (layoutOf fonts doc)).map (bibPlain ∘ lineInk)
  t s!"elsewhere: biblatex's preamble \\bibliography adds its file ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
    (page.contains "L1 [1] end." && !ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")

/-- biblatex's delimiters redefined set biber's citations, and another macro's redefinition is named
(W0104). -/
def biblatexPunctChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib ← IO.FS.readFile s!"{bibProbeDir}/punct.bib"
  let body ← IO.FS.readFile s!"{bibProbeDir}/punct.body.tex"
  let (cites, want) := refParts (← IO.FS.readFile s!"{bibProbeDir}/punct-authoryear.ref.txt")
  let page (extra : String) :=
    "\\documentclass{article}\n\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n\
    \\usepackage[style=authoryear]{biblatex}\n\\addbibresource{punct.bib}\n\
    \\renewcommand*{\\nameyeardelim}{\\addcomma\\space}\n\
    \\renewcommand*{\\multicitedelim}{\\addcomma\\space}\n\
    \\renewcommand*{\\postnotedelim}{\\addcolon\\space}\n" ++ extra ++ "\\begin{document}\n" ++ body ++
    "\\printbibliography\n\\end{document}\n"
  let (doc, ds) := bibBuild (page "") #[("punct", bib), ("punct.bib", bib)]
  let (entries, html) := bibShipped fonts doc
  let lines := (bodyLines (layoutOf fonts doc)).map (bibAcros ∘ bibPlain ∘ lineInk)
  t s!"biblatex delimiters: no warning or error ({(ds.filter fun d => !d.code.startsWith "N").map (·.code)})"
    (!ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E")
  for c in cites do
    t s!"biblatex delimiters: the page sets '{c}'" (lines.contains c)
    t s!"biblatex delimiters: the html reads '{c}'" (hasStr html c)
  t s!"biblatex delimiters: the list is biber's ({entries})" (entries == want)
  let (_, ds) := bibBuild (page "\\renewcommand*{\\bibfont}{\\small}\n\
    \\renewcommand*{\\nameyeardelim}{\\addcomma}\n") #[("punct", bib), ("punct.bib", bib)]
  let named := (ds.filter (·.code == "W0104")).map (·.subject)
  t s!"biblatex delimiters: another macro, or a delimiter of another shape, is named ({named})"
    (named.contains (some "biblatexmacro:bibfont") && named.contains (some "biblatexmacro:nameyeardelim"))

/-- The URLs a field's `\url` and `\href` arguments spell, as written. -/
def urlTargets (field : String) : List String :=
  ((field.splitOn "{http").drop 1).map fun rest => "http" ++ ((rest.splitOn "}").headD "")

/-- A character TeX reserves sets as itself in a field and the build ships, one note naming it
(N0030). -/
def bibReservedChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let cases : List (String × String × Option Char) :=
    [("Research & Development", "Research & Development", some '&'),
     ("The file_name Dataset", "The file_name Dataset", some '_'),
     ("Issue #3 of the Notes", "Issue #3 of the Notes", some '#'),
     ("Two ^ Three", "Two ^ Three", some '^'),
     ("Costs $5 Only", "Costs $5 Only", some '$'),
     ("Fifty % Off Today", "Fifty % Off Today", some '%'),
     ("On $x^2$ and $a_b$ Today", "On x2 and ab Today", none),
     ("\\url{https://example.org/a_b%20c}", "https://example.org/a_b%20c", none),
     -- a URL's `$` is the URL's, never a math shift paired across it
     ("\\url{http://example.org/$a} and $x^2$ end", "http://example.org/$a and x2 end", none),
     ("\\href{http://example.org/?p=$x}{a $\\alpha$ link}", "a α link", none),
     ("\\url{http://example.org/a$b} and \\url{http://example.org/c$d}",
      "http://example.org/a$b and http://example.org/c$d", none),
     -- TeX skips the spaces before an argument, so this URL's `$` is its own
     ("\\url {http://example.org/e$f}", "http://example.org/e$f", none)]
  let lists : List (String × String × String) :=
    [("bibtex", "", "\\bibliographystyle{plain}\\bibliography{r}"),
     ("biblatex", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{r.bib}",
      "\\printbibliography")]
  for (field, shown, char?) in cases do
    let bib := s!"@misc\{k, author = \{Ann Alpha}, note = \{{field}}, year = 2020}\n"
    for (name, pre, list) in lists do
      let (doc, ds) := bibBuild (bibProbeDoc pre list "k") #[("r", bib), ("r.bib", bib)]
      let (entries, html) := bibShipped fonts doc
      let what := s!"reserved {name} {repr field}"
      t s!"{what}: the build ships with no error ({(ds.filter (·.severity == .error)).map (·.code)})"
        (!ds.any (·.severity == .error))
      t s!"{what}: the page sets '{shown}' ({entries})" (entries.any (hasStr · shown))
      t s!"{what}: the html reads '{shown}'" (hasStr html shown)
      for target in urlTargets field do
        t s!"{what}: the html links '{target}'"
          (hasStr (HtmlDoc.emit {} doc).1 s!"href=\"{target}\"")
      let notes := ds.filter (·.code == "N0030")
      match char? with
      | some c =>
        t s!"{what}: one note names the character ({notes.map (·.subject)})"
          (notes.size == 1 && notes.all (·.subject == some s!"bibfield:reserved:{c}"))
      | none => t s!"{what}: nothing is named ({notes.map (·.subject)})" notes.isEmpty

/-- xdata as biber resolves it, line for line against lualatex with biber, each unresolved reference
named (W0425), with the declared departures. -/
def biblatexXdataChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  -- Lines where biber prints an unresolved granular reference's spelling and the engine departs.
  let xdataDepart : List (Nat × String) :=
    [(8, "[9] Ivy Iota. Granular Missing Field. Own Press, 2019."),
     (9, "[10] Jo Kappa. Granular Missing Entry. Own Press, 2020."),
     (10, "[11] Kim Lambda. Granular Position Missing. Own Press, 2021."),
     (11, "[12] Lee Mu. Granular Kind Mismatch. Own Press, 2022.")]
  let runs : List (String × List (Nat × String) × Array (Option String)) :=
    [("xdata", xdataDepart, #[some "bibref:nosuch", some "bibref:xreal", some "bibref:dpress-note",
        some "bibref:nobody-note", some "bibref:dpress-editor", some "bibref:dpress-publisher",
        some "bibref:x15"]),
     ("xcycle", [], #[some "bibref:dloop1"])]
  for (probe, depart, named) in runs do
    let bib ← IO.FS.readFile s!"{bibProbeDir}/{probe}.bib"
    let body ← IO.FS.readFile s!"{bibProbeDir}/{probe}.body.tex"
    let text ← IO.FS.readFile s!"{bibProbeDir}/{probe}-numeric.ref.txt"
    let opts := ((((text.splitOn "\n").headD "").dropPrefix? "# options: ").map (·.toString)).getD ""
    let (_, biber) := refParts text
    let want := depart.foldl (init := biber) fun w (i, l) => w.modify i fun _ => l
    let (doc, ds) := bibBuild ("\\documentclass{article}\n" ++
      "\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" ++
      s!"\\usepackage[{opts}]\{biblatex}\n\\addbibresource\{{probe}.bib}\n\\begin\{document}\n" ++
      body ++ "\\printbibliography\n\\end{document}\n") #[(probe, bib)]
    let (entries, html) := bibShipped fonts doc
    t s!"xdata {probe}: the list holds biber's {want.size} entries ({entries.size})"
      (entries.size == want.size)
    for (w, k) in want.zipIdx do
      let got := (entries[k]?).getD ""
      t s!"xdata {probe}: entry {k + 1} is '{w}' ('{got}')" (got == w)
      t s!"xdata {probe}: the html reads entry {k + 1}" (hasStr html w)
    for (_, l) in depart do
      t s!"xdata {probe}: no reference's spelling reaches the page ('{l}')" (!hasStr l "xdata=")
    let w := ds.filter (·.code == "W0425")
    t s!"xdata {probe}: each unresolved reference is named once ({w.map (·.subject)})"
      (w.map (·.subject) == named)
    -- an entry naming itself is refused as biber refuses it: no @xdata entry
    if probe == "xdata" then
      t s!"xdata {probe}: the entry naming itself is no @xdata entry, as biber says"
        (w.any fun d => d.subject == some "bibref:x15" && hasStr d.message "no @xdata entry")
    t s!"xdata {probe}: the build ships with no error" (!ds.any (·.severity == .error))
  -- xdata2: biber's line where the engine matches it, the declared line
  -- where it departs
  let bib ← IO.FS.readFile s!"{bibProbeDir}/xdata2.bib"
  let body ← IO.FS.readFile s!"{bibProbeDir}/xdata2.body.tex"
  let (_, biber) := refParts (← IO.FS.readFile s!"{bibProbeDir}/xdata2-numeric.ref.txt")
  let depart : List (Nat × String) :=
    [(1, "[2] Ann Alpha, Bo Beta, and Di Delta. Two in One List. 2001."),
     (2, "[3] Hal Theta. List Then Item. Pub One, Pub Two, and Pub Three, 2006."),
     (3, "[4] Ivy Iota. Granular Date. xdata=yp-date.")]
  let want := depart.foldl (init := biber) fun w (i, l) => w.modify i fun _ => l
  let (doc, ds) := bibBuild ("\\documentclass{article}\n" ++
    "\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" ++
    "\\usepackage[style=numeric,sorting=none]{biblatex}\n\\addbibresource{xdata2.bib}\n" ++
    "\\begin{document}\n" ++ body ++ "\\printbibliography\n\\end{document}\n") #[("xdata2", bib)]
  let (entries, html) := bibShipped fonts doc
  t s!"xdata xdata2: the list holds biber's {want.size} entries ({entries.size})"
    (entries.size == want.size)
  for (w, k) in want.zipIdx do
    let got := (entries[k]?).getD ""
    t s!"xdata xdata2: entry {k + 1} is '{w}' ('{got}')" (got == w)
    t s!"xdata xdata2: the html reads entry {k + 1}" (hasStr html w)
  t s!"xdata xdata2: the data entry's crossref is inherited through, as biber's ({entries[0]?})"
    ((entries[0]?).any (· == (biber[0]?).getD "-"))
  t s!"xdata xdata2: the date is named as one biber cannot read, and no reference is unresolved \
    ({ds.map (·.subject)})"
    ((ds.filter (·.code == "W0420")).map (·.subject) == #[some "bibdate:y4:date"] &&
      !ds.any (·.code == "W0425") && !ds.any (·.severity == .error))
  let loop := "@xdata{yl1, note = {xdata=yl2-note}}\n@xdata{yl2, note = {xdata=yl1-note}}\n\
    @book{y5, title = {Granular Loop}, author = {Jo Kappa}, note = {xdata=yl1-note}, date = {2007}}\n"
  let (ldoc, lds) := bibBuild (bibProbeDoc "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{loop.bib}"
    "\\printbibliography" "y5") #[("loop", loop)]
  let (lentries, _) := bibShipped fonts ldoc
  let lw := lds.filter (·.code == "W0425")
  t s!"xdata: a granular cycle is named once, as the field it lends ({lw.map (·.message)})"
    (lw.size == 1 && lw.all fun d =>
      hasStr d.message "the note of 'yl2' takes the note of 'yl1', which closes a cycle")
  t s!"xdata: a granular cycle's spelling never reaches the page ({lentries})"
    (lentries == #["[1] Jo Kappa. Granular Loop. 2007."])

/-- The fields the compatibility pass leaves as they stand skip it and read the same. -/
def bibFieldDoorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doorOf (pre : String) : Bib.FieldDoor :=
    let src := "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\nx\n\\end{document}\n"
    let (toks, _) := Lex.lex "t.tex" src
    let (raws, _) := Parse.parse "t.tex" toks
    Bib.FieldDoor.of "t.tex" (Elab.prepare "t.tex" raws)
  let plain := doorOf ""
  for n in Bib.compatInert do
    -- a control word a preamble may redefine; a control symbol it does not
    let doors := if !n.all Char.isAlpha then [(plain, "plain")] else
      [(plain, "plain"), (doorOf s!"\\providecommand\{\\{n}}[1]\{R#1}\n\
        \\renewcommand\{\\{n}}[1]\{R#1}\n", "redefined")]
    let shapes := [s!"Pre \\{n} post", s!"Pre \\{n}\{word} post", s!"Pre \\{n}\{a}\{b} post",
      s!"Pre \\{n}[o]\{word} post", s!"Pre \{\\{n} word} post", s!"Pre \\{n} E post"]
    for (door, label) in doors do
      for shape in shapes do
        let full := door.readWith true ⟨"refs.bib", {}⟩ shape
        let fast := door.readWith false ⟨"refs.bib", {}⟩ shape
        t s!"door {label}: {repr shape} reads as the full reading reads it" (full == fast)
  -- every symbol a formula leaves as it stands, in each formula shape
  let mathNames := Bib.compatInertMath.get.toArray.qsort (· < ·)
  t s!"door: the formula symbols are the math parser's ({mathNames.size})" (mathNames.size > 100)
  for n in mathNames do
    let doors := if !n.all Char.isAlpha then [(plain, "plain")] else
      [(plain, "plain"), (doorOf s!"\\providecommand\{\\{n}}[1]\{R#1}\n\
        \\renewcommand\{\\{n}}[1]\{R#1}\n", "redefined")]
    let shapes := [s!"Pre $\\{n}$ post", s!"Pre $a \\{n} b$ post", s!"Pre $\\{n}_\{1}^\{2}$ post",
      s!"Pre $\\{n}\{x}$ post", s!"Pre \{$\\{n}$} post"]
    for (door, label) in doors do
      for shape in shapes do
        let full := door.readWith true ⟨"refs.bib", {}⟩ shape
        let fast := door.readWith false ⟨"refs.bib", {}⟩ shape
        t s!"door {label}: {repr shape} reads as the full reading reads it" (full == fast)

/-- A label the style writes sets flush left and a number right-aligned, on the page and in the
HTML. -/
def bibLabelAlignChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib := "@misc{a, author = {Ann Alpha}, title = {First}, year = 2020}\n\
    @misc{b, author = {Bo Beta and Cy Gamma}, title = {Second}, year = 2021}\n\
    @misc{c, author = {Di Delta and Ed Epsilon and Flo Zeta and Gus Eta}, title = {Third}, year = 2022}\n"
  -- each entry's first line: where it starts, where its marker ends, and
  -- where its text starts
  let edges (doc : Ir.Doc) : Array (Dim.Sp × Dim.Sp × Dim.Sp) :=
    (bibEntryLines (bodyLines (layoutOf fonts doc))).filterMap fun e => e[0]?.map fun l =>
      match l.segs[0]?, l.segs[1]? with
      | some (Layout.Seg.run _ _ _ w _ _ _ _ _ _ _), some (Layout.Seg.gap g _) =>
        (l.x, l.x + w, l.x + w + g)
      | _, _ => (l.x, l.x, l.x)
  let shortBib := bib ++ "@misc{d, author = {Hal Theta}, title = {Fourth}, year = 2023, shorthand = {HT}}\n"
  let runs : List (String × String × String × Bool × Nat) :=
    [("alpha", "", "\\bibliographystyle{alpha}\\bibliography{r}", true, 3),
     ("plain", "", "\\bibliographystyle{plain}\\bibliography{r}", false, 3),
     ("biblatex", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{r.bib}",
      "\\printbibliography", false, 4)]
  for (style, pre, list, flush, count) in runs do
    let src := if style == "biblatex" then shortBib else bib
    let (doc, _) := bibBuild (bibProbeDoc pre list "*") #[("r", src), ("r.bib", src)]
    let es := edges doc
    let html := (HtmlDoc.emit {} doc).1
    let same (f : Dim.Sp × Dim.Sp × Dim.Sp → Dim.Sp) : Bool := es.all (f · == (es[0]?.map f).getD 0)
    t s!"labels {style}: {count} entries" (es.size == count)
    if flush then
      t s!"labels {style}: every label starts at one x ({es.map (·.1)})" (same (·.1))
      t s!"labels {style}: every entry's text starts at one x ({es.map (·.2.2)})" (same (·.2.2))
      t s!"labels {style}: the labels are of more than one width" (!same (·.2.1))
      t s!"labels {style}: the html sets them flush" (hasStr html "bib-marker flush")
      t s!"labels {style}: the stylesheet sets them flush" (hasStr html ".bib-marker.flush")
    else
      t s!"labels {style}: every number ends at one x ({es.map (·.2.1)})" (same (·.2.1))
      t s!"labels {style}: the html sets them right-aligned"
        (!hasStr html "bib-marker flush" && !hasStr html ".bib-marker.flush")
  let own := "\\documentclass{article}\n\\begin{document}\nSee \\cite{a,b,c}.\n\
    \\begin{thebibliography}{Longest}\n\\bibitem[A]{a} First.\n\\bibitem[Bb]{b} Second.\n\
    \\bibitem[Longest]{c} Third.\n\\end{thebibliography}\n\\end{document}\n"
  let (doc, _) := bibBuild own #[]
  let es := edges doc
  let html := (HtmlDoc.emit {} doc).1
  let same (f : Dim.Sp × Dim.Sp × Dim.Sp → Dim.Sp) : Bool := es.all (f · == (es[0]?.map f).getD 0)
  t s!"labels own: 3 entries ({es.size})" (es.size == 3)
  t s!"labels own: every hand-written label starts at one x ({es.map (·.1)})" (same (·.1))
  t s!"labels own: every entry's text starts at one x ({es.map (·.2.2)})" (same (·.2.2))
  t s!"labels own: the labels are of more than one width" (!same (·.2.1))
  t s!"labels own: the html sets them flush" (hasStr html "bib-marker flush")

/-- `\supercite` under a numeric style sets as `\cite`, its lost superscript named once (W0428);
under author-year it is `\cite` with its notes. -/
def biblatexSuperciteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib := "@misc{a, author = {Ann Alpha}, title = {First}, date = {2020}}\n\
    @misc{b, author = {Bo Beta}, title = {Second}, date = {2021}}\n\
    @misc{c, author = {Cy Gamma}, title = {Third}, date = {2022}}\n"
  let runs : List (String × String × String × Nat × Bool) :=
    [("style=numeric,sorting=none", "One\\supercite[see][p.~5]{a,b} and \\cite{c} end.",
      "One[1, 2] and [3] end.", 3, true),
     ("style=authoryear", "One \\supercite[p.~5]{a} end.", "One Alpha 2020, p. 5 end.", 1, false)]
  for (opts, body, shown, listed, named) in runs do
    let (doc, ds) := bibBuild ("\\documentclass{article}\n" ++
      "\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" ++
      s!"\\usepackage[{opts}]\{biblatex}\n\\addbibresource\{r.bib}\n\\begin\{document}\n" ++
      body ++ "\n\\printbibliography\n\\end{document}\n") #[("r", bib), ("r.bib", bib)]
    let (entries, html) := bibShipped fonts doc
    let page := (bodyLines (layoutOf fonts doc)).map (bibAcros ∘ bibPlain ∘ lineInk)
    let w := ds.filter (·.code == "W0428")
    t s!"supercite {opts}: the page sets '{shown}' ({page})" (page.contains shown)
    t s!"supercite {opts}: the html reads '{shown}'" (hasStr html shown)
    t s!"supercite {opts}: the list holds {listed} entries ({entries})" (entries.size == listed)
    t s!"supercite {opts}: no key prints as text" (!page.any (hasStr · "supercite"))
    t s!"supercite {opts}: {if named then "one note names the superscript" else "nothing is named"} \
      ({w.map (·.subject)})"
      (if named then w.size == 1 && w.all (·.subject == some "citecmd:supercite") else w.isEmpty)
  let (_, nds) := bibBuild "\\documentclass{article}\n\\begin{document}\nOne\\supercite{a} end.\n\\end{document}\n" #[]
  t s!"supercite: without biblatex it is an unknown command, named ({nds.map (·.code)})"
    (nds.any (·.code == "W0301") && !nds.any (·.code == "W0428"))

/-- A list's `\ref` is judged as the body's: resolved against the document's labels, or `??` named
by W0349. -/
def bibFieldRefChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib := "@misc{r1, author = {Ann Alpha}, year = 2020, title = {One}, note = {See Section \\ref{nosuch}}}\n\
    @misc{r2, author = {Bo Beta}, year = 2021, title = {Two}, note = {See Section \\ref{sec:a}}}\n"
  let lists : List (String × String × String) :=
    [("bibtex", "", "\\bibliographystyle{plain}\\bibliography{r}"),
     ("biblatex", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{r.bib}",
      "\\printbibliography")]
  for (name, pre, list) in lists do
    let src := "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n\
      \\section{A}\\label{sec:a}\nBody \\ref{alsonosuch}.\n\\nocite{*}\n" ++ list ++ "\n\\end{document}\n"
    let (doc, ds) := bibBuild src #[("r", bib), ("r.bib", bib)]
    let (entries, html) := bibShipped fonts doc
    let named := (ds.filter (·.code == "W0349")).map (·.subject)
    t s!"list ref {name}: the unresolved key sets ?? ({entries})"
      (entries.any (hasStr · "See Section ??"))
    t s!"list ref {name}: the resolved key sets its number ({entries})"
      (entries.any (hasStr · "See Section 1"))
    t s!"list ref {name}: the html reads both" (hasStr html "See Section ??" && hasStr html "See Section 1")
    t s!"list ref {name}: W0349 names the list's key and the body's ({named})"
      (named.contains (some "nosuch") && named.contains (some "alsonosuch") &&
        !named.contains (some "sec:a"))

/-- `@comment` is a comment under biber, while BibTeX reads on after the word. -/
def bibCommentChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib := "@comment{ set aside: @misc{gone, author = {Cy Gamma}, title = {Set Aside}, year = 2019} }\n\
    @comment(another @misc{gone2, author = {Di Delta}, title = {Also Aside}, year = 2018})\n\
    @misc{kept, author = {Ann Alpha}, title = {Kept Entry}, year = 2020}\n"
  let lists : List (String × String × String × Nat) :=
    [("bibtex", "", "\\bibliographystyle{plain}\\bibliography{r}", 3),
     ("biblatex", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{r.bib}",
      "\\printbibliography", 1)]
  for (name, pre, list, want) in lists do
    let (doc, ds) := bibBuild (bibProbeDoc pre list "*") #[("r", bib), ("r.bib", bib)]
    let (entries, _) := bibShipped fonts doc
    t s!"comment {name}: the list holds {want} entries ({entries})" (entries.size == want)
    t s!"comment {name}: the entry outside the comment is listed" (entries.any (hasStr · "Ann Alpha"))
    t s!"comment {name}: an entry inside a comment is {if want == 1 then "not " else ""}listed"
      ((entries.any (hasStr · "Cy Gamma")) == (want != 1))
    t s!"comment {name}: the build ships with no error" (!ds.any (·.severity == .error))

/-- The corpus's own PNG and the drawing a synthetic boundary renderer returns. -/
def bibFieldPng : String := "testdata/corpus/rects.png"
def bibFieldBox : String := "testdata/corpus/figures/box.pdf"

/-- The store a build fulfils for a document's image requests through `Image.fulfilRequests`. -/
def bibFieldStore (doc : Ir.Doc) (png box face : ByteArray) : Image.Store × Array Diag :=
  let refs := Ir.pictureRefs doc
  Image.fulfilRequests ((Ir.imageRequests doc).map fun req =>
    if req.src == "img.png" then
      (req, .decoded "img.png" (Image.probe png >>= Image.plan .default) none none (some png) none)
    else if req.src.startsWith Ir.picSrcPrefix && refs.any (Ir.picSrcPrefix ++ ·.1 == req.src) then
      (req, .decoded req.src (Image.probe box >>= Image.plan .default) (some face) none (some box)
        none)
    else (req, .missing req.src))

/-- The reference list's shipped images: each image box an entry's lines set, by source, with
whether it loaded. -/
def bibEntryImages (store : Image.Store) (out : Layout.Out) : Array (String × Bool) :=
  (bibEntryLines (bodyLines out)).flatMap fun e => e.flatMap fun l => l.segs.filterMap fun s =>
    match s with
    | .image (some i) _ _ _ => store.entries[i]?.map fun en => (en.src, en.info.isSome)
    | _ => none

/-- The reference list's HTML elements: the `ul` the list is, and every
element under it. -/
def bibHtmlList (body : Array Html.Node) : Array Html.Node :=
  (elemNodesList (· == "ul") #[] body.toList).filter fun n => match n with
    | .elem _ attrs _ => ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " " |>.contains "bibliography"
    | _ => false

/-- The images the page's reference list shows, each `img`'s embedded resource decoded, or its
source and no bytes. -/
def bibListImages (body : Array Html.Node) : IO (Array (String × ByteArray)) :=
  (elemAttrsList (· == "img") #[] (bibHtmlList body).toList).mapM fun (_, a) => do
    let src := (HtmlDoc.attrOf? a "src").getD ""
    match ← (htmlDataDecode src).toBaseIO with
    | .ok r => pure r
    | .error _ => pure (src, ByteArray.empty)

/-- The note lines a page sets at its foot, their text with white space
dropped, in page order. -/
def bibNoteLines (out : Layout.Out) : Array String :=
  ((allLines out).filter fun l => l.note && hasGlyphRun l).map fun l =>
    (lineInk l).toList.filter (!·.isWhitespace) |> String.ofList

/-- The page's endnotes, by id: each `li` the doc-endnotes list holds, with
its text, white space dropped. -/
def bibEndnotes (body : Array Html.Node) : Array (String × String) :=
  (elemNodesList (· == "li") #[] body.toList).filterMap fun n => match n with
    | .elem _ attrs kids =>
      (HtmlDoc.attrOf? attrs "id").bind fun id =>
        if id.startsWith "fn" && !id.startsWith "fnref" then
          some (id, (nodeTextList "" kids.toList).toList.filter (!·.isWhitespace) |> String.ofList)
        else none
    | _ => none

/-- A field's image, picture and footnote are the body's: fulfilled, drawn and numbered where the
list stands, on the page and among its endnotes. -/
def bibFieldContentChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let png ← IO.FS.readBinFile bibFieldPng
  let box ← IO.FS.readBinFile bibFieldBox
  let face := svgDocument "<circle cx=\"10\" cy=\"10\" r=\"8\"/>"
  let lists : List (String × String × String) :=
    [("bibtex", "", "\\bibliographystyle{plain}\\bibliography{r}"),
     ("biblatex", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{r.bib}",
      "\\printbibliography")]
  let bibOf (note : String) : Array (String × String) :=
    let bib := s!"@misc\{k, author = \{Ann Alpha}, title = \{Tee}, note = \{{note}}, year = 2001}\n"
    #[("r", bib), ("r.bib", bib)]
  let pre := "\\usepackage{graphicx}\n\\usepackage{tikz}\n"
  for (name, load, list) in lists do
    let (doc, ds) := bibBuild (bibProbeDoc (pre ++ load) list "k")
      (bibOf "\\includegraphics[width=1cm]{img.png}")
    let what := s!"field content {name}: an image"
    t s!"{what}: the build raises no error" (!ds.any (·.severity == .error))
    t s!"{what}: the request reads it ({(Ir.imageRequests doc).map (·.src)})"
      ((Ir.imageRequests doc).any (·.src == "img.png"))
    let (store, fulfilled) := bibFieldStore doc png box face
    t s!"{what}: the build fulfils every request ({fulfilled.map (·.code)})" fulfilled.isEmpty
    let images := bibEntryImages store (layoutOf fonts doc (imgs := store))
    t s!"{what}: its entry sets the image, loaded ({images})" (images == #[("img.png", true)])
    let (page, _) := HtmlDoc.emitClosed { imgs := store } doc #[]
    t s!"{what}: the page publishes" page.isOk
    let (_, body, _) := HtmlDoc.emitTree { imgs := store } doc
    let shown ← bibListImages body
    t s!"{what}: the page's entry holds the image's bytes ({shown.map (·.1)})"
      (shown.size == 1 && shown.all (· == ("image/png", png)))
    let (doc, ds) := bibBuild (bibProbeDoc (pre ++ load) list "k")
      (bibOf "\\tikz \\draw (0,0) circle (2pt);")
    let what := s!"field content {name}: a picture"
    t s!"{what}: the build raises no error" (!ds.any (·.severity == .error))
    let pics := (Ir.imageRequests doc).filter (·.src.startsWith Ir.picSrcPrefix)
    t s!"{what}: the request carries the picture's body ({pics.size}, {(Ir.pictureRefs doc).size})"
      (pics.size == 1 && pics.all fun r =>
        (Ir.pictureRefs doc).any (Ir.picSrcPrefix ++ ·.1 == r.src))
    let (store, fulfilled) := bibFieldStore doc png box face
    t s!"{what}: the build fulfils every request ({fulfilled.map (·.code)})" fulfilled.isEmpty
    let images := bibEntryImages store (layoutOf fonts doc (imgs := store))
    t s!"{what}: its entry sets the drawing ({images})"
      (images.size == 1 && images.all fun (src, loaded) => src.startsWith Ir.picSrcPrefix && loaded)
    let (page, _) := HtmlDoc.emitClosed { imgs := store } doc #[face]
    t s!"{what}: the page publishes" page.isOk
    let (_, body, _) := HtmlDoc.emitTree { imgs := store } doc
    let shown ← bibListImages body
    t s!"{what}: the page's entry holds the drawing's face ({shown.map (·.1)})"
      (shown.size == 1 && shown.all (· == ("image/svg+xml", face)))
    let src := "\\documentclass{article}\n\\usepackage[paperwidth=60cm,paperheight=80cm,margin=1cm]{geometry}\n" ++
      load ++ "\n\\begin{document}\nOne\\footnote{body before}.\\nocite{k}\n" ++ list ++
      "\nTwo\\footnote{body after}.\n\\end{document}\n"
    let (doc, ds) := bibBuild src (bibOf "with\\footnote{field note} here")
    let what := s!"field content {name}: a footnote"
    t s!"{what}: the build raises no error" (!ds.any (·.severity == .error))
    let notes := bibNoteLines (layoutOf fonts doc)
    t s!"{what}: the page's foot numbers it after the body's note before the list ({notes})"
      (notes == #["1bodybefore", "2fieldnote", "3bodyafter"])
    let (_, body, _) := HtmlDoc.emitTree {} doc
    let ends := bibEndnotes body
    t s!"{what}: the page's endnotes hold it, numbered as the foot numbers it ({ends})"
      (ends.map (·.1) == #["fn1", "fn2", "fn3"] &&
        ends.map (fun e => hasStr e.2 "bodybefore" || hasStr e.2 "fieldnote" || hasStr e.2 "bodyafter")
          == #[true, true, true] &&
        hasStr (ends[1]?.map (·.2) |>.getD "") "fieldnote")
    let marks := elemAttrsList (· == "a") #[] (bibHtmlList body).toList
    t s!"{what}: the page's entry marks it, linked to its endnote"
      (marks.any fun (_, a) => HtmlDoc.attrOf? a "href" == some "#fn2")

/-- One run of the built binary over `doc` in `dir`: its exit code, whether the artifact was
written, and its diagnostics' codes and severities. -/
def bibShipRun (binary font dir : System.FilePath) (doc out : String) :
    IO (UInt32 × Bool × Array (String × String)) := do
  let path := dir / out
  if ← path.pathExists then IO.FS.removeFile path
  let r ← IO.Process.output {
    cmd := binary.toString, cwd := some dir, args := #[doc, "-o", path.toString, "--porcelain"]
    env := #[("PATH", some (dir / "bin").toString), ("XDG_CACHE_HOME", some (dir / "cache").toString),
      ("LEANTEX_FONT", some font.toString)] }
  return (r.exitCode, ← path.pathExists, porcelainCodes r.stdout)

/-- A field's image, picture and footnote ship through the driver's publication path as the body's
do. -/
def bibFieldShipChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath binary
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let box ← IO.FS.realPath bibFieldBox
  let png ← IO.FS.readBinFile bibFieldPng
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    IO.FS.createDirAll (dir / "bin")
    writeScript (dir / "bin" / "lualatex") (fakeRenderer box)
    IO.FS.writeBinFile (dir / "img.png") png
    let lists : List (String × String × (String → String)) :=
      [("bibtex", "", fun r => s!"\\bibliographystyle\{plain}\\bibliography\{{r}}"),
       ("biblatex", "\\usepackage[style=numeric]{biblatex}\n", fun _ => "\\printbibliography")]
    let cases : List (String × String) :=
      [("an image", "\\includegraphics[width=1cm]{img.png}"),
       ("a picture", "\\tikz \\pattern (0,0) rectangle (2pt,2pt);"),
       ("a footnote", "with\\footnote{a note} here")]
    let entry (note : String) : String :=
      s!"@misc\{k, author = \{Ann Alpha}, title = \{Tee}, note = \{{note}}, year = 2001}\n"
    let warned (cs : Array (String × String)) : Array String :=
      ((cs.filter fun (_, sev) => sev == "warning" || sev == "error").map (·.1)).qsort (· < ·)
    for (name, load, list) in lists do
      for (what, construct) in cases do
        IO.FS.writeFile (dir / "rf.bib") (entry construct)
        IO.FS.writeFile (dir / "rb.bib") (entry "plain")
        let docOf (r body : String) : String :=
          "\\documentclass{article}\n\\usepackage{graphicx}\n\\usepackage{tikz}\n" ++ load ++
            (if load.isEmpty then "" else s!"\\addbibresource\{{r}.bib}\n") ++
            "\\begin{document}\nText" ++ body ++ " \\cite{k}.\n" ++ list r ++ "\n\\end{document}\n"
        IO.FS.writeFile (dir / "field.tex") (docOf "rf" "")
        -- The body's spelling inside a font command's argument, a line that stays one.
        IO.FS.writeFile (dir / "body.tex") (docOf "rb" (" \\textnormal{" ++ construct ++ "}"))
        for ext in ["pdf", "html"] do
          let (fe, fw, fc) ← bibShipRun binary font dir "field.tex" s!"field.{ext}"
          let (be, bw, bc) ← bibShipRun binary font dir "body.tex" s!"body.{ext}"
          let art := s!"field ship {name}: {what}, {ext}"
          t s!"{art}: the field's and the body's both ship ({fe}, {be}; {fc})"
            (fe == 0 && be == 0 && fw && bw)
          t s!"{art}: the field's warnings are the body's ({warned fc}, {warned bc})"
            (warned fc == warned bc)
          t s!"{art}: no run refuses the page"
            (!(fc ++ bc).any (·.1 == "E0606"))

/-- Invented, balanced field texts for the reading's fuzz, drawn by a fixed linear congruential
sequence. -/
def bibFuzzFields (n : Nat) : Array String := Id.run do
  let pieces : Array String := #["word", " ", "Two words", "&", "#", "^", "_", "$", "%", "~",
    "--", "``q''", "$x^2$", "$\\alpha$", "\\'e", "\\\"o", "\\ss{}", "\\\\", "\\par ", "\\item ",
    "\\vspace{2pt}", "\\hspace{1em}", "\\section{S}", "\\subsection*{T}", "\\noindent ",
    "\\hfill ", "\\relax ", "\\def\\foo{bar}", "\\foo", "\\newcommand{\\baz}{qux}", "\\baz",
    "\\footnote{n}", "\\cite{k}", "\\label{y}", "\\ref{y}", "\\verb|v|", "\\unknowncmd{u}",
    "\\LaTeX{}", "\\end{itemize}", "\\[", "\\]", "\\(", "\\textbf",
    "\\includegraphics[width=1cm]{img.png}", "\\tikz \\draw (0,0) circle (1pt);", "}"]
  let openers : Array (String × String) := #[("\\emph{", "}"), ("\\textbf{", "}"), ("{", "}"),
    ("\\url{http://example.org/", "}"), ("\\href{http://example.org/a$b}{", "}"), ("\\mbox{", "}"),
    ("\\begin{itemize}\\item ", "\\end{itemize}"), ("\\begin{tabular}{ll}", "\\end{tabular}"),
    ("\\begin{center}", "\\end{center}"), ("\\begin{quote}", "\\end{quote}"),
    ("\\begin{unknownenv}", "\\end{unknownenv}"), ("\\begin{equation}", "\\end{equation}")]
  let mut seed : Nat := 20261010
  let mut out : Array String := #[]
  for _ in [0:n] do
    seed := (seed * 1103515245 + 12345) % 2147483648
    let len := 1 + seed / 65536 % 9
    let mut text := ""
    let mut stack : List String := []
    for _ in [0:len] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let r := seed / 65536
      if r % 4 == 0 then
        let (o, c) := openers[r / 4 % openers.size]?.getD ("{", "}")
        text := text ++ o
        stack := c :: stack
      else
        let piece := pieces[r / 4 % pieces.size]?.getD " "
        if piece == "}" then
          match stack with
          | c :: rest =>
            text := text ++ c
            stack := rest
          | [] => text := text ++ " "
        else text := text ++ piece
    for c in stack do text := text ++ c
    out := out.push text
  return out

/-- A field LaTeX sets always ships: what the inline elaborator refuses sets as its text, run into
the entry, named once (W0429). -/
def bibFieldBackstopChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let lists : List (String × String × String) :=
    [("bibtex", "", "\\bibliographystyle{plain}\\bibliography{r}"),
     ("biblatex", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{r.bib}",
      "\\printbibliography")]
  let cases : List (String × String) :=
    [("\\begin{itemize}\\item one\\end{itemize}", "one"),
     ("\\begin{tabular}{ll}a&b\\\\c&d\\end{tabular}", "a b c d"),
     ("\\def\\foo{bar}\\foo", "bar"),
     ("\\newcommand{\\baz}{qux}\\baz", "qux"),
     ("\\section{Sec}", "Sec")]
  let bibOf (field : String) : String :=
    s!"@misc\{k, author = \{Ann Alpha}, title = \{T}, note = \{{field}}, year = 2001}\n"
  for (field, shown) in cases do
    for (name, pre, list) in lists do
      let (doc, ds) := bibBuild (bibProbeDoc pre list "k") #[("r", bibOf field), ("r.bib", bibOf field)]
      let (entries, html) := bibShipped fonts doc
      let what := s!"backstop {name} {repr field}"
      t s!"{what}: the build ships with no error ({(ds.filter (·.severity == .error)).map (·.code)})"
        (!ds.any (·.severity == .error))
      t s!"{what}: the page sets '{shown}' ({entries})" (entries.any (hasStr · shown))
      t s!"{what}: the html reads '{shown}'" (hasStr html shown)
      let named := ds.filter (·.code == "W0429")
      t s!"{what}: one warning names the note of 'k' ({named.map (·.message)})"
        (named.size == 1 && named.all fun d => d.subject == some "bibfield:unread:k:note" &&
          hasStr d.message "'note' field of 'k'" && d.trigger.isNone)
  let skip := "\\hspace{1em}x\\vspace{2pt}"
  for (name, pre, list) in lists do
    let (doc, ds) := bibBuild (bibProbeDoc pre list "k") #[("r", bibOf skip), ("r.bib", bibOf skip)]
    let (entries, html) := bibShipped fonts doc
    let what := s!"backstop {name} {repr skip}"
    t s!"{what}: the build ships with no error ({(ds.filter (·.severity == .error)).map (·.code)})"
      (!ds.any (·.severity == .error))
    t s!"{what}: the page sets 'x' ({entries})" (entries.any (hasStr · "x"))
    t s!"{what}: the html reads 'x'" (hasStr html "x")
    t s!"{what}: the skip is named as the body's is, and nothing backstops the field \
      ({ds.filter (fun d => d.code == "W0329" || d.code == "W0429") |>.map (·.code)})"
      ((ds.filter (·.code == "W0329")).size == 1 && !ds.any (·.code == "W0429"))
  let fields := bibFuzzFields 300
  let png ← IO.FS.readBinFile bibFieldPng
  let box ← IO.FS.readBinFile bibFieldBox
  let face := svgDocument "<circle cx=\"10\" cy=\"10\" r=\"8\"/>"
  for (name, pre, list) in lists do
    let mut failed : Array String := #[]
    for field in fields do
      let (doc, ds) := bibBuild (bibProbeDoc ("\\usepackage{graphicx}\n\\usepackage{tikz}\n" ++ pre)
        list "k") #[("r", bibOf field), ("r.bib", bibOf field)]
      let (entries, _) := bibShipped fonts doc
      let (store, fulfilled) := bibFieldStore doc png box face
      let marks := (Ir.footnotesOf doc.body).map (·.1)
      unless !ds.any (·.severity == .error) && (entries.filter (hasStr · "Ann Alpha")).size == 1 &&
          (ds.filter (·.code == "W0429")).all (·.subject == some "bibfield:unread:k:note") &&
          fulfilled.isEmpty && (HtmlDoc.emitClosed { imgs := store } doc #[face]).1.isOk &&
          marks.all (·.isSome) && marks.toList.eraseDups.length == marks.size do
        failed := failed.push field
    t s!"backstop fuzz {name}: every one of {fields.size} builds ships its entry \
      ({failed.size} did not: {failed.toList.take 3})" failed.isEmpty

/-- The fuzz's field texts ship through the driver: PDF and page written, exit 0, no error. -/
def bibFuzzShipChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath binary
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let box ← IO.FS.realPath bibFieldBox
  let png ← IO.FS.readBinFile bibFieldPng
  let faces ← IO.FS.realPath testFonts
  let fields := bibFuzzFields 300
  let bib := String.join (fields.toList.zipIdx.map fun (field, i) =>
    s!"@misc\{k{i}, author = \{Ann Alpha}, title = \{Tee {i}}, note = \{{field}}, year = 2001}\n")
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    IO.FS.createDirAll (dir / "bin")
    writeScript (dir / "bin" / "lualatex") (fakeRenderer box)
    IO.FS.writeBinFile (dir / "img.png") png
    IO.FS.writeFile (dir / "r.bib") bib
    let lists : List (String × String × String) :=
      [("bibtex", "", "\\bibliographystyle{plain}\\bibliography{r}"),
       ("biblatex", "\\usepackage[style=numeric]{biblatex}\n\\addbibresource{r.bib}",
        "\\printbibliography")]
    for (name, pre, list) in lists do
      -- the suite's own faces, a formula's among them
      IO.FS.writeFile (dir / "fuzz.tex") (bibProbeDoc
        (s!"\\fonts\{ dir = \"{faces}\", body = \"Open Sans\" }\n\\usepackage\{graphicx}\n" ++
          "\\usepackage{tikz}\n" ++ pre) list "*")
      for ext in ["pdf", "html"] do
        let (exit, written, codes) ← bibShipRun binary font dir "fuzz.tex" s!"fuzz.{ext}"
        let errors := (codes.filter (·.2 == "error")).map (·.1)
        t s!"fuzz ship {name}, {ext}: {fields.size} fields ship through the driver \
          ({exit}, {errors.toList.eraseDups})"
          (exit == 0 && written && errors.isEmpty && !codes.any (·.1 == "E0606"))

/-- alpha's label reads the key before the organization, line for line against lualatex with bibtex. -/
def bibAlphaKeyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib ← IO.FS.readFile s!"{bibProbeDir}/alphakey.bib"
  let want := refLines (← IO.FS.readFile s!"{bibProbeDir}/alphakey-alpha.ref.txt")
  let (doc, ds) := bibBuild (bibProbeDoc "\\usepackage{url}"
    "\\bibliographystyle{alpha}\\bibliography{alphakey}" "p1,p2,p3,m1,m2,m3,b2,x1,x2")
    #[("alphakey", bib)]
  let (entries, html) := bibShipped fonts doc
  t s!"alpha keys: no error ({(ds.filter (·.severity == .error)).map (·.code)})"
    (!ds.any (·.severity == .error))
  t s!"alpha keys: the list holds bibtex's {want.size} entries ({entries.size})"
    (entries.size == want.size)
  for (w, k) in want.zipIdx do
    let w := bibPlain w
    let got := (entries[k]?).getD ""
    t s!"alpha keys: entry {k + 1} is '{w}' ('{got}')" (got == w)
    t s!"alpha keys: the html reads entry {k + 1}" (hasStr html w)

/-- An entry no name list labels is cited by its label title, against lualatex with biber. -/
def biblatexLabelTitleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  biblatexCiteProbe ref fonts "ltitle" ["authoryear", "numeric"]
  let bib ← IO.FS.readFile s!"{bibProbeDir}/ltitle.bib"
  let body ← IO.FS.readFile s!"{bibProbeDir}/ltitle.body.tex"
  let (doc, _) := bibBuild ("\\documentclass{article}\n" ++
    "\\usepackage[style=authoryear]{biblatex}\n\\addbibresource{ltitle.bib}\n\\begin{document}\n" ++
    body ++ "\\printbibliography\n\\end{document}\n") #[("ltitle", bib)]
  let html := (HtmlDoc.emit {} doc).1
  t "label title: the citation emphasizes the title, its \\texttt as the body sets it"
    (hasStr html "<em>Manual: The <code>foo</code> Package</em> 2015</a>")
  t "label title: the citation's \\emph and formula inside the title, as the body sets them"
    (hasStr html "<em>Über <em>Alles</em> and <math")

/-- A label and a citation's names set as their TeX sets, never flattened to a command's name. -/
def bibLabelTexChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let bib ← IO.FS.readFile s!"{bibProbeDir}/labeltex.bib"
  let quiet (ds : Array Diag) : Bool := !ds.any fun d => d.code.startsWith "W" || d.code.startsWith "E"
  let want := refLines (← IO.FS.readFile s!"{bibProbeDir}/labeltex-alpha.ref.txt")
  let (doc, ds) := bibBuild (bibProbeDoc "" "\\bibliographystyle{alpha}\\bibliography{labeltex}"
    "lt1,lt3,lt4") #[("labeltex", bib)]
  let (entries, html) := bibShipped fonts doc
  t s!"label tex alpha: no warning or error ({ds.map (·.code)})" (quiet ds)
  t s!"label tex alpha: the list holds bibtex's {want.size} entries ({entries})"
    (entries == want.map bibPlain)
  for w in want do
    t s!"label tex alpha: the html reads '{w}'" (hasStr html (bibPlain w))
  let body ← IO.FS.readFile s!"{bibProbeDir}/labeltex-nat.body.tex"
  let (cites, want) := refParts (← IO.FS.readFile s!"{bibProbeDir}/labeltex-plainnat.ref.txt")
  let (doc, ds) := bibBuild (bibtexPage body "\\bibliographystyle{plainnat}\\bibliography{labeltex}"
    "\\usepackage{natbib}") #[("labeltex", bib)]
  let (entries, html) := bibShipped fonts doc
  let page := (bodyLines (layoutOf fonts doc)).map (bibPlain ∘ lineInk)
  t s!"label tex plainnat: no warning or error ({ds.map (·.code)})" (quiet ds)
  for c in cites do
    t s!"label tex plainnat: the page sets '{c}' ({page})" (page.contains c)
    t s!"label tex plainnat: the html reads '{c}'" (hasStr html c)
  t s!"label tex plainnat: the list holds bibtex's entries ({entries})" (entries == want)
  t "label tex plainnat: the citation sets the name's \\textbf as the body sets it"
    (hasStr (HtmlDoc.emit {} doc).1 "<strong>Brandt</strong>")
  biblatexCiteProbe ref fonts "labeltex" ["authoryear", "numeric"]
  let body ← IO.FS.readFile s!"{bibProbeDir}/labeltex.body.tex"
  let (doc, _) := bibBuild ("\\documentclass{article}\n" ++
    "\\usepackage[style=authoryear]{biblatex}\n\\addbibresource{labeltex.bib}\n\\begin{document}\n" ++
    body ++ "\\printbibliography\n\\end{document}\n") #[("labeltex", bib)]
  let raw := (HtmlDoc.emit {} doc).1
  t "label tex authoryear: the citation sets the name's and the shorthand's \\textbf"
    (hasStr raw "<strong>Brandt</strong>" && hasStr raw "<strong>AbC</strong>")

def bibModelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  bibAsWrittenChecks ref
  bibNameChecks ref
  bibDateChecks ref
  bibLetterChecks ref
  bibViewChecks ref
  bibInheritChecks ref
  bibtexOracleChecks ref oneFace
  biblatexOracleChecks ref oneFace
  biblatexUniqueChecks ref oneFace
  biblatexXnameChecks ref oneFace
  biblatexFieldCoverageChecks ref oneFace
  biblatexSortChecks ref oneFace
  biblatexLabelDateChecks ref oneFace
  biblatexPostnoteChecks ref oneFace
  biblatexUnicodeNameChecks ref oneFace
  bibUnicodeNameChecks ref oneFace
  bibUnreadDateChecks ref oneFace
  bibSetChecks ref
  bibRelatedChecks ref
  bibPreambleChecks ref oneFace
  bibSourcesChecks ref
  bibLanguageChecks ref
  bibFieldReadingChecks ref oneFace
  bibNamedChecks ref oneFace
  bibFieldCiteChecks ref oneFace
  bibStringStoreChecks ref oneFace
  bibLabelColumnChecks ref oneFace
  biblatexLocaleSortChecks ref oneFace
  bibRefChecks ref oneFace
  bibFieldCompatChecks ref
  biblatexCiteCommandChecks ref oneFace
  bibElsewhereChecks ref oneFace
  biblatexPunctChecks ref oneFace
  bibReservedChecks ref oneFace
  bibFieldBackstopChecks ref oneFace
  bibFieldContentChecks ref oneFace
  bibAlphaKeyChecks ref oneFace
  biblatexLabelTitleChecks ref oneFace
  bibLabelTexChecks ref oneFace
  biblatexXdataChecks ref oneFace
  bibFieldDoorChecks ref
  bibFieldRefChecks ref oneFace
  bibCommentChecks ref oneFace
  biblatexSuperciteChecks ref oneFace
  bibLabelAlignChecks ref oneFace
