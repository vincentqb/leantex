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
  t "chapter declarations: the divisions' page numbering is named once"
    ((bds.filter fun d => d.subject == some "matter:pages" && d.severity != .note).size == 1 &&
      !bds.any (·.code == "W0301"))
  let bgeom := Layout.Geom.ofPage bdoc.page
  let digits (r : ArtRun) : Option String :=
    let tx := r.text.trimAscii.toString
    if !tx.isEmpty && tx.all Char.isDigit then some tx else none
  -- A page's number is its last run of digits alone, below its text.
  let numbers : Array (Option String) :=
    match readArtifact (driverPdf fonts bgeom bdoc (layoutOf fonts bdoc bgeom)) with
    | .ok pages => pages.map fun (p : ArtPage) => (p.runs.filterMap digits).back?
    | .error _ => #[]
  t s!"chapter declarations: the pages number on in arabic numerals through the divisions ({numbers})"
    (numbers == #[some "1", some "2", some "3"])
  let listing := report "\\usepackage{listings}\n"
    "\\chapter{Alpha}\n\\begin{lstlisting}[caption={A probe}]\nx = 1\n\\end{lstlisting}"
  t "chapter declarations: a listing numbered through the document is named"
    ((elabStr listing).2.any fun d => d.subject == some "chapters:floats")
  let figure := report "" "\\chapter{Alpha}\nWords.\n\\begin{figure}\n\\caption{A probe}\n\\end{figure}"
  t s!"chapter declarations: the float numbered through the document is named at its caption"
    ((elabStr figure).2.any fun d => d.subject == some "chapters:floats" &&
      d.span.any (·.pos.line == 6))

end Tests.Chapters
