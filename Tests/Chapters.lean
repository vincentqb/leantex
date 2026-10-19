module

public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.Chapters

private instance : ToString Dim.Length := ⟨reprStr⟩

/-- The pages a source ships: each line's baseline, size and text. -/
private def pagesOf (fonts : Font.FontSet) (src : String) :
    Array (Array (Dim.Length × Dim.Length × String)) :=
  (censusOfSrc fonts src).map (·.lines.map fun l => (l.y, l.size, l.text))

/-- The first line on `page` whose text is `text`. -/
private def lineAt (pages : Array (Array (Dim.Length × Dim.Length × String))) (page : Nat) (text : String) :
    Option (Dim.Length × Dim.Length) :=
  (pages[page]?.getD #[]).findSome? fun (y, size, t) => if t == text then some (y, size) else none

/-- report.cls's and book.cls's `\chapter` as lualatex sets it, its head's lines where lualatex
stands them and what it numbers within it, where an article has no `\chapter`. -/
def chapterChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := "\\chapter{Introduction}\nSome text in the first chapter.\\footnote{A first note.}\n" ++
    "\\section{Background}\nMore text in a section.\n\\begin{equation}x = 1\\end{equation}\n" ++
    "\\chapter*{Unnumbered}\nText of an unnumbered chapter.\n" ++
    "\\chapter{Second}\n\\section{Another}\nFinal words.\\footnote{A second note.}\n" ++
    "\\begin{equation}y = 2\\end{equation}\n\\appendix\n\\chapter{Proofs}\n\\section{Lemmas}\nLast words."
  let src := "\\documentclass{report}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let (_, ds) := elabStr src
  let said := (ds.filter (·.severity != .note)).toList.map (·.code)
  t s!"chapters: a report's chapters warn nothing ({said})" (said == [])
  let pages := pagesOf fonts src
  let texts := pages.map (·.map (·.2.2))
  t s!"chapters: each chapter opens a page of its own ({texts.map (·[0]?)})"
    (texts.size == 4 && texts[0]?.bind (·[0]?) == some "Chapter 1" &&
      texts[1]?.bind (·[0]?) == some "Unnumbered" && texts[2]?.bind (·[0]?) == some "Chapter 2" &&
      texts[3]?.bind (·[0]?) == some "Appendix A")
  let huge := Ir.scaleStepIn Ir.sizeScale (Dim.pt 10) "huge"
  let hugeU := Ir.scaleStepIn Ir.sizeScale (Dim.pt 10) "Huge"
  match lineAt pages 0 "Chapter 1", lineAt pages 0 "Introduction",
      lineAt pages 0 "Some text in the first chapter.1", lineAt pages 1 "Unnumbered" with
  | some (label, labelSize), some (title, titleSize), some (text, _), some (bare, bareSize) =>
    t s!"chapters: the word and number at \\huge, the title at \\Huge ({labelSize}, {titleSize})"
      (labelSize == huge && titleSize == hugeU && bareSize == hugeU)
    t s!"chapters: the title 50pt below the word, the text 52pt below the title ({title - label}, {text - title})"
      (title - label == Dim.pt 50 && text - title == Dim.pt 52)
    t s!"chapters: an unnumbered title stands 5pt below where a numbered chapter's word does ({bare - label})"
      (bare - label == Dim.pt 5)
    let top := (Layout.Geom.ofPage (elabStr src).1.page).bodyTop
    t s!"chapters: the word stands 85pt below the text's top, an unnumbered title 90pt ({label - top})"
      (label - top == Dim.pt 85 && bare - top == Dim.pt 90)
  | _, _, _, _ => t s!"chapters: the first chapter's lines ship ({texts})" false
  let all := texts.flatten
  t s!"chapters: sections number within their chapter, an appendix's by its letter ({all})"
    (all.contains "1.1Background" && all.contains "2.1Another" && all.contains "A.1Lemmas")
  t "chapters: equations number within their chapter"
    (all.any (hasStr · "(1.1)") && all.any (hasStr · "(2.1)") && !all.any (hasStr · "(2)"))
  t "chapters: footnotes restart in each chapter"
    (all.contains "1A first note." && all.contains "1A second note.")
  let html := Html.document "en" #[] (docNodesOf (elabStr src).1)
  t "chapters: the web page's chapter heading carries its word and number on a line of its own"
    (hasStr html "<h1 class=\"body-heading chapter\"" &&
      hasStr html "<span class=\"chapter-label\">Chapter 1</span> Introduction" &&
      hasStr html "<span class=\"chapter-label\">Appendix A</span> Proofs")
  let book (opts : String) : String :=
    "\\documentclass" ++ opts ++ "{book}\n\\begin{document}\n\\chapter{Alpha}\n\\section{Bravo}\nWords.\n" ++
      "\\chapter{Charlie}\nWords.\n\\end{document}"
  t "chapters: a book's chapters number as a report's"
    ((pagesOf fonts (book "")).flatten.map (·.2.2) |>.contains "1.1Bravo")
  let right (opts : String) : Nat :=
    ((elabStr (book opts)).2.filter fun d =>
      d.subject == some "chapters:openright" && d.severity != .note).size
  t "chapters: a book's right-hand openings, which one-sided pages lack, are named once"
    (right "" == 1 && right "[openany]" == 0 && right "[oneside]" == 0 &&
      right "[openany,openright]" == 0 && right "[openright,openany]" == 0 &&
      ((elabStr src).2.filter (·.subject == some "chapters:openright")).isEmpty)
  t "chapters: an explicit openright is named once, by the chapters' openings alone"
    (["[openright]", "[twoside,openright]"].all fun o =>
      ((elabStr (book o)).2.filter fun d => d.severity != .note &&
        (d.subject == some "chapters:openright" || hasStr d.message "openright")).size == 1)
  let article := "\\documentclass{article}\n\\begin{document}\n\\chapter{Alpha}\nWords.\n\\end{document}"
  t "chapters: an article has no \\chapter"
    ((elabStr article).2.any fun d => d.code == "W0301" && hasStr d.message "chapter")

/-- A report's chapter as references and assistive technology read it: cleveref names it a chapter,
a label in its title lands on its head, and its word and number stand in its heading's structure. -/
def chapterReadingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := "\\documentclass{report}\n\\usepackage{cleveref}\n\\begin{document}\n" ++
    "\\chapter{Alpha}\\label{ch:a}\n\\section{Bravo}\\label{sec:b}\n" ++
    "See \\cref{ch:a}, \\cref{sec:b}, \\Cref{ch:a} and \\cref{ch:z}.\n" ++
    "\\appendix\n\\chapter{Zulu}\\label{ch:z}\nWords.\n\\end{document}"
  let (doc, _) := elabStr src
  let text := String.intercalate " " ((pagesOf fonts src).toList.flatMap fun p => p.toList.map (·.2.2))
  -- The census reads a no-break space as the gap it sets, no glyph.
  t s!"chapter references: cleveref names a chapter as lualatex does ({text})"
    (hasStr text "See chapter1, section1.1, Chapter1 and chapterA.")
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fonts doc geom
  let site := (Layout.anchorIndex out.pages)[Ir.labelAnchor "ch:a"]?
  t "chapter references: a label in a chapter's title lands on its head's first line"
    (match site with
     | some (_, .line l) => lineText l == "Chapter 1"
     | _ => false)
  match readArtifact (driverPdf fonts geom doc out) with
  | .error e => t s!"chapter structure: the tagged file reads back: {e}" false
  | .ok pages =>
    let label := ((pages[0]?.map (·.runs)).getD #[] |>.filter (hasStr ·.text "Chapter"))[0]?
    t s!"chapter structure: the word and number stand in the heading's structure, no artifact \
({label.map (·.marks.map ArtMark.render)})"
      (label.any fun r => !r.isArtifact && r.marks.any (· matches .content "H1" _))

/-- A chapter's head as the document declares it: its word, its number's form and its counter, and
book's divisions numbering only the main matter's chapters. -/
def chapterDeclarationChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let report (pre body : String) : String :=
    "\\documentclass{report}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let lines (src : String) := (pagesOf fonts src).toList.flatMap fun p => p.toList.map (·.2.2)
  let renamed := report "\\renewcommand{\\chaptername}{Lecture}\n\\renewcommand{\\appendixname}{Annex}\n"
    "\\chapter{Alpha}\nWords.\n\\appendix\n\\chapter{Bravo}\nWords."
  t s!"chapter declarations: the head reads the declared chapter and appendix names ({lines renamed})"
    ((lines renamed).contains "Lecture 1" && (lines renamed).contains "Annex A")
  let roman := report "\\renewcommand{\\thechapter}{\\Roman{chapter}}\n"
    ("\\setcounter{chapter}{3}\n\\chapter{Alpha}\n\\section{Bravo}\nWords.\n" ++
      "\\begin{equation}x = 1\\end{equation}")
  let said := ((elabStr roman).2.filter (·.severity != .note)).toList.map (·.code)
  t s!"chapter declarations: a declared number form and counter number the head, its sections and \
equations ({lines roman}, {said})"
    (said == [] && (lines roman).contains "Chapter IV" && (lines roman).contains "IV.1Bravo" &&
      (lines roman).any (hasStr · "(IV.1)"))
  let book := "\\documentclass{book}\n\\begin{document}\n\\frontmatter\n\\chapter{Preface}\nWords.\n" ++
    "\\mainmatter\n\\chapter{Alpha}\n\\section{Bravo}\nWords.\n\\backmatter\n" ++
    "\\chapter{Afterword}\nWords.\n\\end{document}"
  let (bdoc, bds) := elabStr book
  let heads := bdoc.body.filterMap fun b => match b with
    | .section .h1 _ num title => some (num, Ir.plainText title)
    | _ => none
  t s!"chapter declarations: a book numbers its main matter's chapters alone ({heads})"
    (heads == #[(none, "Preface"), (some "Chapter 1", "Alpha"), (none, "Afterword")] &&
      (lines book).contains "1.1Bravo")
  t "chapter declarations: the divisions' page numbering is set, never named"
    (!bds.any fun d => d.subject == some "matter:pages" || d.code == "W0301")
  let bgeom := Layout.Geom.ofPage bdoc.page
  let numbers := artFolios (driverPdf fonts bgeom bdoc (layoutOf fonts bdoc bgeom))
  -- lualatex: book's front matter numbers its pages i, ii, …, the main matter from 1 again.
  t s!"chapter declarations: the front matter's pages number in roman numerals, the main matter's from 1 ({numbers})"
    (numbers == #[some "i", some "1", some "2"])
  let listing := report "\\usepackage{listings}\n"
    "\\chapter{Alpha}\n\\begin{lstlisting}[caption={A probe}]\nx = 1\n\\end{lstlisting}"
  t "chapter declarations: a listing numbered through the document is named"
    ((elabStr listing).2.any fun d => d.subject == some "chapters:floats")
  let figure := report "" "\\chapter{Alpha}\nWords.\n\\begin{figure}\n\\caption{A probe}\n\\end{figure}"
  t "chapter declarations: a figure numbered within its chapter is not named"
    (!(elabStr figure).2.any fun d => d.subject == some "chapters:floats")

/-- The page's and the counters' numbering as lualatex sets it on invented probes: `\pagenumbering`,
`\the<counter>` in running text, a declared `\theequation`, KOMA-Script's and memoir's chapters,
listings' line range and a Markdown fragment's headings. -/
def numberingStateChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let foliosOf (src : String) : Array (Option String) :=
    let (doc, _) := elabStr src
    let geom := Layout.Geom.ofPage doc.page
    artFolios (driverPdf fonts geom doc (layoutOf fonts doc geom))
  let numbered := "\\documentclass{article}\n\\begin{document}\n\\pagenumbering{roman}\nFront.\n" ++
    "\\newpage\nMore front.\n\\newpage\n\\pagenumbering{arabic}\nBody.\n\\newpage\nMore.\n" ++
    "\\pagenumbering{gobble}\n\\newpage\nLast.\n\\end{document}"
  -- lualatex: i, ii, then 1, then 2, and gobble's page 1 prints no number.
  t s!"page numbering: each style counts from 1 on the page it stands on ({foliosOf numbered})"
    (foliosOf numbered == #[some "i", some "ii", some "1", none, none])
  let lines (src : String) := (pagesOf fonts src).toList.flatMap fun p => p.toList.map (·.2.2)
  let counters := "\\documentclass{report}\n\\begin{document}\n\\chapter{Alpha}\n\\section{Bravo}\n" ++
    "Section \\thesection{} of chapter \\thechapter{} on page \\thepage.\n" ++
    "\\begin{equation}x = 1\\end{equation}\nAfter equation \\theequation.\n" ++
    "\\newpage\nNow page \\thepage.\n\\end{document}"
  let shown := String.join ((fittedOf fonts (elabStr counters).1).out.pages.toList.flatMap fun p =>
    p.lines.toList.map fun l => letters (lineText l))
  t s!"counters: \\the<counter> in running text prints its value, \\thepage its page ({shown})"
    (hasStr shown "Section1.1ofchapter1onpage1." && hasStr shown "Afterequation1.1." &&
      hasStr shown "Nowpage2.")
  let eq := "\\documentclass{report}\n\\renewcommand\\theequation{\\arabic{chapter}-\\arabic{equation}}\n" ++
    "\\begin{document}\n\\chapter{Alpha}\n\\begin{equation}x = 1\\end{equation}\n\\end{document}"
  t s!"counters: a declared \\theequation numbers the equations ({lines eq})"
    ((lines eq).any (hasStr · "(1-1)"))
  let koma := "\\documentclass{scrreprt}\n\\begin{document}\n\\chapter{Introduction}\n" ++
    "Some text in the first chapter.\n\\addchap{Unnumbered}\nText.\n\\end{document}"
  let kpages := pagesOf fonts koma
  let line (p : Nat) (text : String) := ((kpages[p]?.getD #[]).find? (hasStr ·.2.2 text)).map (·.1)
  let ktop := (Layout.Geom.ofPage (elabStr koma).1.page).bodyTop
  match line 0 "Introduction", line 0 "Some text in the first chapter.", line 1 "Unnumbered" with
  | some head, some body, some bare =>
    -- lualatex at 11pt: the head's baseline 67.28pt below the text's top, the text 37.07pt, one
    -- \baselineskip past 1.725 of them, below it; each within a quarter point here.
    let near (a b : Dim.Length) : Bool := (a - b).abs ≤ Dim.pt 1 / 4
    t s!"KOMA-Script chapters: the number and title on one line, the text 1.725\\baselineskip and one \
line below ({head - ktop}, {body - head}, {bare - ktop})"
      (head - ktop == bare - ktop && near (head - ktop) (Dim.pt 6728 / 100) &&
        near (body - head) (Dim.pt 3707 / 100))
  | _, _, _ => t s!"KOMA-Script chapters: the head sets its number before its title ({kpages.map (·.map (·.2.2))})" false
  let listing := "\\documentclass{article}\n\\usepackage{listings}\n\\begin{document}\n" ++
    "\\begin{lstlisting}[firstline=2,lastline=3]\nline one\nline two\nline three\nline four\n" ++
    "\\end{lstlisting}\n\\end{document}"
  t s!"listings: firstline and lastline set the source's lines between them ({lines listing})"
    ((lines listing).contains "linetwo" && (lines listing).contains "linethree" &&
      !(lines listing).contains "lineone" && !(lines listing).contains "linefour")
  let memoir := "\\documentclass{memoir}\n\\begin{document}\n\\chapter{Alpha}\nWords.\n\\end{document}"
  t s!"memoir chapters: the head reads as report's ({lines memoir})"
    ((lines memoir).contains "Chapter 1" && (lines memoir).contains "Alpha")
  let doc (cls body : String) (pre : String := "") : String :=
    s!"\\documentclass{cls}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"
  -- lualatex: memoir numbers chapters and sections, a subsection unnumbered and unlisted.
  let memoirDeep := doc "{memoir}" "\\tableofcontents\n\\chapter{Alpha}\n\\section{Bravo}\n\\subsection{Charlie}\nWords."
  t s!"memoir numbers down to the section ({lines memoirDeep})"
    ((lines memoirDeep).contains "1.1Bravo" && (lines memoirDeep).contains "Charlie" &&
      !(lines memoirDeep).any (hasStr · "1.1.1"))
  -- lualatex: \addchap and \addsec set their titles unnumbered, \addsec listed by its short title.
  let added := doc "{scrreprt}" ("\\tableofcontents\n\\chapter{Alpha}\nWords.\n\\addchap{Extra}\nText.\n" ++
    "\\addsec[Short]{Long title}\nMore.\n\\addchap*{Starred}\nLast.")
  let addedDs := (elabStr added).2
  t s!"KOMA-Script: \\addchap and \\addsec head unnumbered, \\addsec listed, the starred form read ({lines added})"
    (!addedDs.any (·.severity == .error) && (lines added).contains "Starred" &&
      !(lines added).any (hasStr · "Chapter") && (lines added).contains "Extra" &&
      (lines added).any (hasStr · "Short") && !(lines added).any (hasStr · "1Extra"))
  let heading := doc "{article}" "\\tableofcontents\n\\section{Head on \\thepage}\nText."
  let fitted (src : String) : List String := (fittedOf fonts (elabStr src).1).out.pages.toList.flatMap
    fun p => p.lines.toList.map fun l => letters (lineText l)
  t s!"\\thepage in a heading: its contents entry keeps its page ({fitted heading})"
    ((fitted heading).contains "1Headon11" && (fitted heading).contains "1Headon1")
  t "a title's anchor reads no page reference's folio, before the layout or after"
    (Ir.slug #[.text "Head on ", .ref "k" .page "??" none] == Ir.slug #[.text "Head on ", .ref "k" .page "1" none])
  let midPar := doc "{article}" "Words before and \\pagenumbering{roman} words after."
  t s!"\\pagenumbering mid-paragraph leaves the paragraph whole and numbers its page ({lines midPar}, {foliosOf midPar})"
    ((lines midPar).contains "Words before and words after." && foliosOf midPar == #[some "i"])
  let pre := doc "{article}" "Words." "\\pagenumbering{gobble}\n"
  t s!"\\pagenumbering in the preamble numbers the first page ({foliosOf pre})" (foliosOf pre == #[none])
  let within := doc "{article}" "\\section{A}\n\\begin{equation}x\\end{equation}"
    "\\usepackage{amsmath}\n\\renewcommand\\theequation{\\arabic{equation}}\n\\numberwithin{equation}{section}\n"
  t s!"\\numberwithin after a declared \\theequation defines it again ({lines within})"
    ((lines within).any (hasStr · "(1.1)"))
  for cls in ["{scrbook}", "{memoir}"] do
    let fm := doc cls "\\frontmatter\n\\chapter{Preface}\nWords.\n\\mainmatter\n\\chapter{Alpha}\nWords."
    t s!"{cls}'s front matter numbers its pages in roman numerals ({foliosOf fm})"
      ((foliosOf fm)[0]? == some (some "i") && (foliosOf fm).contains (some "1"))
  let deck := "\\documentclass{beamer}\n\\begin{document}\n\\pagenumbering{roman}\n\\begin{frame}A\\end{frame}\n\\end{document}"
  t "a deck's \\pagenumbering is named, its frames numbered as beamer numbers them"
    ((elabStr deck).2.any fun d => d.code == "W0104" && hasStr d.message "pagenumbering")
  -- lualatex: report numbers figures and tables within each chapter, Figure 1.1 and Table 2.1.
  let floats := doc "{report}" ("\\chapter{Alpha}\n\\begin{figure}x\\caption{One}\\label{f}\\end{figure}\n" ++
    "\\begin{figure}y\\caption{Two}\\end{figure}\n\\chapter{Bravo}\n" ++
    "\\begin{figure}z\\caption{Three}\\label{g}\\end{figure}\n" ++
    "\\begin{table}w\\caption{Four}\\end{table}\nSee \\ref{f} and \\ref{g}.")
  t s!"floats in a class with chapters number within each chapter ({fitted floats})"
    ((fitted floats).any (hasStr · "Figure1.1:One") && (fitted floats).any (hasStr · "Figure1.2:Two") &&
      (fitted floats).any (hasStr · "Figure2.1:Three") && (fitted floats).any (hasStr · "Table2.1:Four") &&
      (fitted floats).any (hasStr · "See1.1and2.1.") &&
      !(elabStr floats).2.any (·.subject == some "chapters:floats"))
  -- lualatex: a figure before the first chapter is Figure 1, algorithm.sty's algorithms run on.
  let early := doc "{report}" ("\\begin{figure}x\\caption{Early}\\end{figure}\n\\chapter{Alpha}\n" ++
    "\\begin{figure}y\\caption{Late}\\end{figure}\n\\begin{algorithm}\\caption{Algo}\\end{algorithm}\n" ++
    "\\chapter{Bravo}\n\\begin{algorithm}\\caption{Algb}\\end{algorithm}") "\\usepackage{algorithm}\n"
  t s!"a float before the first chapter has no chapter, and algorithms number through ({fitted early})"
    ((fitted early).any (hasStr · "Figure1:Early") && (fitted early).any (hasStr · "Figure1.1:Late") &&
      (fitted early).any (hasStr · "Algorithm1:Algo") && (fitted early).any (hasStr · "Algorithm2:Algb"))
  -- lualatex: memoir's floats before the first chapter are 0.1 and its equations 1; KOMA-Script's
  -- floats 1 and its equations 0.1.
  let zero (cls : String) : String := doc cls ("\\begin{figure}x\\caption{Early}\\end{figure}\n" ++
    "\\begin{table}x\\caption{Tab}\\end{table}\n\\begin{equation}a = b\\end{equation}\n" ++
    "\\chapter{Alpha}\n\\begin{figure}y\\caption{Late}\\end{figure}")
  t s!"memoir numbers floats before the first chapter within chapter 0 ({fitted (zero "{memoir}")})"
    ((fitted (zero "{memoir}")).any (hasStr · "Figure0.1:Early") &&
      (fitted (zero "{memoir}")).any (hasStr · "Table0.1:Tab") &&
      (fitted (zero "{memoir}")).any (hasStr · "(1)") &&
      (fitted (zero "{memoir}")).any (hasStr · "Figure1.1:Late"))
  t s!"KOMA-Script numbers equations before the first chapter within chapter 0 ({fitted (zero "{scrbook}")})"
    ((fitted (zero "{scrbook}")).any (hasStr · "Figure1:Early") &&
      (fitted (zero "{scrbook}")).any (hasStr · "(0.1)") &&
      (fitted (zero "{scrbook}")).any (hasStr · "Figure1.1:Late"))
  -- lualatex: \addchap restarts the figures, equations and footnotes, the chapter's number standing;
  -- \addchap* and \chapter* restart nothing.
  let restart (cmd : String) : String := doc "{scrbook}" ("\\chapter{Alpha}\n" ++
    "\\begin{figure}x\\caption{One}\\end{figure}\n\\begin{equation}a = b\\end{equation}\n" ++
    "Text\\footnote{first} more\\footnote{second}.\n" ++ cmd ++ "{Extra}\n" ++
    "\\begin{figure}y\\caption{Two}\\end{figure}\n\\begin{equation}c = d\\end{equation}\n" ++
    "Text\\footnote{third}.")
  let added := fitted (restart "\\addchap")
  t s!"KOMA-Script's \\addchap restarts a chapter's counters ({added})"
    (added.any (hasStr · "Figure1.1:Two") && (added.filter (hasStr · "(1.1)")).length == 2 &&
      added.any (hasStr · "1third"))
  t s!"\\addchap* and \\chapter* restart nothing ({fitted (restart "\\addchap*")})"
    (["\\addchap*", "\\chapter*"].all fun c =>
      (fitted (restart c)).any (hasStr · "Figure1.2:Two") && (fitted (restart c)).any (hasStr · "(1.2)") &&
        (fitted (restart c)).any (hasStr · "3third"))
  -- lualatex: memoir's and scrbook's front matter number floats and equations alone; an unstarred
  -- chapter KOMA-Script leaves unnumbered restarts them, before any numbered chapter too, and an
  -- added section restarts its subsections.
  let front (cls : String) : List String := fitted (doc cls ("\\frontmatter\n\\chapter{FA}\n" ++
    "\\begin{figure}x\\caption{FAone}\\end{figure}\n\\begin{figure}x\\caption{FAtwo}\\end{figure}\n" ++
    "\\begin{equation}a = b\\end{equation}\n\\chapter{FB}\n\\begin{figure}x\\caption{FBone}\\end{figure}\n" ++
    "\\mainmatter\n\\chapter{Main}\n\\begin{figure}x\\caption{Mone}\\end{figure}"))
  t s!"the front matter numbers floats and equations alone, KOMA-Script restarting them ({front "{scrbook}"})"
    ((front "{scrbook}").any (hasStr · "Figure1:FAone") && (front "{scrbook}").any (hasStr · "Figure2:FAtwo") &&
      (front "{scrbook}").any (hasStr · "(1)") && (front "{scrbook}").any (hasStr · "Figure1:FBone") &&
      (front "{scrbook}").any (hasStr · "Figure1.1:Mone") &&
      (front "{memoir}").any (hasStr · "Figure1:FAone") && (front "{memoir}").any (hasStr · "Figure1.1:Mone"))
  let early := fitted (doc "{scrreprt}" ("\\begin{figure}x\\caption{Ea}\\end{figure}\n" ++
    "\\addchap{Intro}\n\\begin{figure}x\\caption{Eb}\\end{figure}"))
  t s!"KOMA-Script's \\addchap before any numbered chapter restarts the floats ({early})"
    (early.any (hasStr · "Figure1:Ea") && early.any (hasStr · "Figure1:Eb"))
  let sec := fitted (doc "{scrartcl}" ("\\section{Alpha}\n\\subsection{One}\n\\subsection{Two}\n" ++
    "\\addsec{Bravo}\n\\subsection{Three}"))
  t s!"KOMA-Script's \\addsec restarts its subsections ({sec})"
    (sec.any (hasStr · "1.2Two") && sec.any (hasStr · "1.1Three"))
  t "a chapters option with another value leaves the article's sections as they number"
    ((fitted (doc "[chapters=false]{article}" "\\section{Alpha}\n\\subsection{Bravo}")).any
      (hasStr · "1.1Bravo"))
  let declared := doc "{report}" "\\chapter{Alpha}\n\\begin{figure}x\\caption{One}\\end{figure}"
    "\\renewcommand{\\thefigure}{\\arabic{figure}}\n"
  t "a declared \\thefigure under chapters is named, not read"
    ((elabStr declared).2.any (·.subject == some "chapters:thefigure"))
  let grouped := doc "{article}" "Text {\\pagenumbering{roman}} more."
  t "\\pagenumbering in a group is named under its own spelling"
    ((elabStr grouped).2.any fun d => d.code == "W0104" && hasStr d.message "'\\pagenumbering' in a group" &&
      !hasStr d.message "pagenumbering roman")
  let minted := doc "{article}" ("\\begin{minted}[firstline=2,lastline=3]{text}\nline one\nline two\n" ++
    "line three\nline four\n\\end{minted}") "\\usepackage{minted}\n"
  t s!"minted: firstline and lastline set the source's lines between them ({lines minted})"
    ((lines minted).contains "linetwo" && (lines minted).contains "linethree" &&
      !(lines minted).contains "lineone" && !(lines minted).contains "linefour")
end Tests.Chapters
