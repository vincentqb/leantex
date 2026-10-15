module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.MetaEscape

/-! Metadata values reach each artifact through its own escaper: read back from the PDF's Info and
XMP, the typed HTML head and the markdown twin, never escaping their field. -/

/-- Values that would leave their field in some artifact's syntax. -/
def hostileValues : List String :=
  ["say \"hi\", author = \"Injected", "a\\b) /Author (Injected", "(unbalanced", "\\",
   "</title><script>alert(1)</script>", "x\" onload=\"y", "]]><rdf:li>Injected</rdf:li>",
   "one\r\ntwo\rthree", "bell\x07 nul\x00 tab\t", "café ⟨𝒳⟩ — 😀", "\"\"", "&amp; &lt;"]

/-- UTF-16BE code units as characters, a surrogate pair as one. -/
def utf16 : List Nat → String → String
  | hi :: lo :: hi2 :: lo2 :: rest, acc =>
    let u := hi * 256 + lo
    if 0xD800 ≤ u && u < 0xDC00 then
      utf16 rest (acc.push (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (hi2 * 256 + lo2 - 0xDC00))))
    else utf16 (hi2 :: lo2 :: rest) (acc.push (Char.ofNat u))
  | hi :: lo :: _, acc => acc.push (Char.ofNat (hi * 256 + lo))
  | _, acc => acc
termination_by l => l.length

/-- A text string's characters (§7.9.2.2): UTF-16BE after its byte-order mark, else bytes
PDFDocEncoding reads as themselves (printable ASCII, tab, line feed, return); none for any other
byte, which a conforming reader reads otherwise. -/
def textOf (b : ByteArray) : Option String :=
  match b.data.toList.map UInt8.toNat with
  | 0xFE :: 0xFF :: rest => some (utf16 rest "")
  | bs =>
    if bs.all fun n => (0x20 ≤ n && n < 0x7F) || n == 9 || n == 10 || n == 13 then
      some (String.ofList (bs.map Char.ofNat))
    else none

/-- The trailer's Info dictionary of a written PDF. -/
def infoOf (pdf : ByteArray) : Option (Array (String × PdfRead.Obj)) := do
  let tr ← (PdfRead.trailer pdf).toOption
  let doc ← (PdfRead.Doc.ofBytes pdf).toOption
  match ← (doc.deref (← tr.get? "Info")).toOption with
  | .dict es => some es
  | _ => none

/-- One Info entry's text. -/
def infoText (pdf : ByteArray) (key : String) : Option String := do
  let es ← infoOf pdf
  let (_, o) ← es.find? (·.1 == key)
  textOf (← PdfContentLex.strBytes? o)

/-- One catalog entry's text. -/
def catalogText (pdf : ByteArray) (key : String) : Option String := do
  let tr ← (PdfRead.trailer pdf).toOption
  let doc ← (PdfRead.Doc.ofBytes pdf).toOption
  let root ← (doc.deref (← tr.get? "Root")).toOption
  textOf (← PdfContentLex.strBytes? (← root.get? key))

/-- The XMP packet's `x:xmpmeta` element, decoded from the catalog's metadata stream. -/
def xmpOf (pdf : ByteArray) : Option Xml.Node := do
  let tr ← (PdfRead.trailer pdf).toOption
  let doc ← (PdfRead.Doc.ofBytes pdf).toOption
  let root ← (doc.deref (← tr.get? "Root")).toOption
  let (dict, raw) ← (doc.stream (← root.get? "Metadata")).toOption.join
  let data ← (PdfRead.decodeStream dict raw).toOption
  let text ← String.fromUTF8? data
  let start := "<x:xmpmeta"
  let stop := "</x:xmpmeta>"
  let body ← (text.splitOn start)[1]?
  let inner ← (body.splitOn stop)[0]?
  (Xml.parse (start ++ inner ++ stop).toUTF8).toOption

mutual

/-- A node's character data onto `acc`, in document order. -/
def nodeText (acc : String) : Xml.Node → String
  | .text s => acc ++ s
  | .elem _ _ kids => listText acc kids.toList

def listText (acc : String) : List Xml.Node → String
  | [] => acc
  | n :: rest => listText (nodeText acc n) rest

end

mutual

/-- The first element of this name, at any depth. -/
def findElem (name : String) : Xml.Node → Option Xml.Node
  | n@(.elem m _ kids) => if m == name then some n else findInList name kids.toList
  | .text _ => none

def findInList (name : String) : List Xml.Node → Option Xml.Node
  | [] => none
  | n :: rest => (findElem name n).orElse fun _ => findInList name rest

end

/-- The text of the `rdf:li` under an XMP property, as XMP nests a property's value. -/
def xmpField (pdf : ByteArray) (outer : String) : Option String := do
  let li ← findElem "rdf:li" (← findElem outer (← xmpOf pdf))
  nodeText "" li

/-- The text of the first element of this name in the XMP packet. -/
def xmpText (pdf : ByteArray) (name : String) : Option String := do
  nodeText "" (← findElem name (← xmpOf pdf))

mutual

/-- Every `/URI` string inside an object, in order. -/
def urisOf (acc : Array String) : PdfRead.Obj → Array String
  | .dict es => urisEntries acc es.toList
  | .arr xs => urisList acc xs.toList
  | _ => acc

def urisList (acc : Array String) : List PdfRead.Obj → Array String
  | [] => acc
  | o :: rest => urisList (urisOf acc o) rest

def urisEntries (acc : Array String) : List (String × PdfRead.Obj) → Array String
  | [] => acc
  | (k, o) :: rest =>
    let acc := if k == "URI" then
        match (PdfContentLex.strBytes? o).bind textOf with
        | some u => acc.push u
        | none => acc
      else urisOf acc o
    urisEntries acc rest

end

/-- The URI each link annotation's action names, in object order. -/
def linkUris (pdf : ByteArray) : Array String :=
  match PdfRead.objects pdf with
  | .ok es => es.val.foldl (fun acc e => urisOf acc e.val) #[]
  | .error _ => #[]

/-- The head's `<title>` text and each named meta element's content. -/
def headFacts (head : Array Html.Node) : Option String × Array (String × String) :=
  head.foldl (fun (t, ms) n => match n with
    | .elem "title" _ #[.text s] => (some s, ms)
    | .elem "meta" attrs _ =>
      match attrs.find? (·.1 == "name"), attrs.find? (·.1 == "content") with
      | some (_, k), some (_, v) => (t, ms.push (k, v))
      | _, _ => (t, ms)
    | _ => (t, ms)) (none, #[])

/-- A document's PDF, laid out as the driver lays it out. -/
def pdfOf (geom : Layout.Geom) (fonts : Font.FontSet) (doc : Ir.Doc) : ByteArray :=
  Pdf.write geom fonts (layoutOf fonts doc geom).pages doc.info

/-- Each artifact reads back the one metadata record, hostile values included, and the surfaces
copy author TeX into it as text with no key escaping its value. -/
def metaEscapeChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  t "decl: a quoted value reads back as one entry holding exactly the value"
    (hostileValues.all fun v =>
      Decl.parseBlock "t" ("title = " ++ Decl.quote v ++ ", author = " ++ Decl.quote "A") {}
        "pdfmeta" == (#[⟨"title", .str v⟩, ⟨"author", .str "A"⟩], #[]))
  let base := (elabStr (dvDoc "" "Words.")).1
  let xmlAdmitted (v : String) : String := String.ofList (v.toList.filter (Xml.xmlChar ·.toNat))
  let withMeta (v : String) : Ir.Doc :=
    let info : Ir.Meta := {
      title := some v, author := some v, subject := some v, keywords := some v
      url := some ("https://example.org/" ++ v) }
    { base with info }
  let tags := ["<title", "</title", "<script", "</script", "<meta ", "<link ", "<style", "</style"]
  let tagCounts (doc : Ir.Doc) : List Nat :=
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let page := Html.document "en" head body
    tags.map fun tag => (page.splitOn tag).length
  let benign := tagCounts (withMeta "plain words")
  for v in hostileValues do
    let doc := withMeta v
    let pdf := pdfOf geom fonts doc
    let keys := ((infoOf pdf).getD #[]).map (·.1)
    t s!"pdf: the Info title, author, subject and keywords read back exactly ({v.quote})"
      (["Title", "Author", "Subject", "Keywords"].all (infoText pdf · == some v))
    t s!"pdf: the Info dictionary holds no key the value spelled ({v.quote})"
      (keys == #["Title", "Author", "Subject", "Keywords", "Producer"])
    t s!"xmp: the packet parses and its fields read back as the characters XML admits ({v.quote})"
      (xmpField pdf "dc:title" == some (xmlAdmitted v) &&
        xmpField pdf "dc:creator" == some (xmlAdmitted v) &&
        xmpField pdf "dc:description" == some (xmlAdmitted v) &&
        xmpText pdf "pdf:Keywords" == some (xmlAdmitted v) &&
        xmpText pdf "dc:identifier" == some (xmlAdmitted ("https://example.org/" ++ v)))
    let (title, metas) := headFacts (HtmlDoc.emitTree {} doc).1
    t s!"html: the head's title and named metas carry the value ({v.quote})"
      (title == some v && metas.contains ("author", v) && metas.contains ("description", v) &&
        metas.contains ("keywords", v))
    t s!"html: the rendered page holds the tags a plain value's does ({v.quote})"
      (tagCounts doc == benign)
    let md := MarkdownDoc.emit doc
    t s!"md: the twin's title is its first line, alone ({v.quote})"
      (match md.splitOn "\n" with
       | first :: "" :: _ => first.startsWith "# "
       | _ => false)
  let surface (pre : String) : Ir.Doc × Array Diag := elabStr (dvDoc pre "Words.")
  let injected := (surface "\\usepackage{hyperref}\n\\hypersetup{pdfauthor={A\", subject = \"B}}\n").1
  let injectedPdf := pdfOf geom fonts injected
  t "hyperref: a quote in a value sets no other key in the PDF or the HTML head"
    ((infoText injectedPdf "Author").isSome && infoText injectedPdf "Subject" == none &&
      !((headFacts (HtmlDoc.emitTree {} injected).1).2.any (·.1 == "description")))
  for pre in ["\\usepackage[pdftitle={R\\&D at 50\\%off}]{hyperref}\n",
      "\\usepackage{hyperref}\n\\hypersetup{pdftitle={R\\&D at 50\\%off}}\n"] do
    let doc := (surface pre).1
    let pdf := pdfOf geom fonts doc
    t s!"hyperref: a value's TeX is set as text in every artifact, as hyperref's PDF strings ({pre.quote})"
      (infoText pdf "Title" == some "R&D at 50%off" && xmpField pdf "dc:title" == some "R&D at 50%off" &&
        (headFacts (HtmlDoc.emitTree {} doc).1).1 == some "R&D at 50%off" &&
        (MarkdownDoc.emit doc).startsWith "# R\\&D at 50%off\n")
  let declared := (elabStr ("\\DocumentMetadata{lang={en\", title = \"Injected}}\n" ++
    dvDoc "" "Words.")).1
  let metaPdf := pdfOf geom fonts declared
  t "DocumentMetadata: a quote in the language sets no other key, and the tag ships as declared"
    (infoText metaPdf "Title" == none &&
      catalogText metaPdf "Lang" == some "en\", title = \"Injected")
  let read (pre : String) : Option String := infoText (pdfOf geom fonts (surface pre).1) "Title"
  t "hyperref: a value reads as its text: the PDF argument, a box's content, a tie a space, and no footnote, label or thanks"
    (read "\\hypersetup{pdftitle={A\\mbox{Widget}B \\texorpdfstring{TEX}{PDF} C\\footnote{Note.}D\\label{x}E\\thanks{F}~G}}\n"
      == some "AWidgetB PDF CDE G")
  t "hyperref: an author list's separator reads as a semicolon, and quotes as the page sets them"
    (infoText (pdfOf geom fonts (surface "\\hypersetup{pdfauthor={O'Brien \\and Smith}}\n").1)
      "Author" == some "O’Brien; Smith")
  let (reserved, reservedDiags) := surface "\\hypersetup{pdftitle={my_file name}, pdfkeywords={x^2, A & B, \\#1}}\n"
  let reservedPdf := pdfOf geom fonts reserved
  t "hyperref: a reserved character in a value is its text, and the document still ships"
    (infoText reservedPdf "Title" == some "my_file name" &&
      infoText reservedPdf "Keywords" == some "x^2, A & B, #1" &&
      reservedDiags.all fun d => d.code != "E0311")
  let leak := dvDoc "\\hypersetup{pdftitle={A study\\footnote{Aside.}}, pdfsubject={x\\label{sec:one}}}\n"
    "\\section{Alpha}\\label{sec:one}Words\\footnote{Body note.} and \\ref{sec:one}."
  let leakText := pageTextOf fonts leak
  t "hyperref: elaborating a value leaves the document's counters and labels as they were"
    (hasStr leakText "and 1." && hasStr leakText "1Body note.")
  t "title: a tie in the title the metadata falls back to reads as a space"
    (infoText (pdfOf geom fonts (elabStr (dvDoc "\\title{Chapter~One}\n" "Words.")).1) "Title" ==
      some "Chapter One")
  let hostileUrl := "https://example.org/a)b(c"
  let linkDoc := (elabStr (dvDoc "" ("\\href{" ++ hostileUrl ++ "}{link}"))).1
  t "pdf: a link's URI reads back as written"
    (linkUris (pdfOf geom fonts linkDoc) == #[hostileUrl])
  for (what, pre) in [("math family", "\\usepackage{unicode-math}\n\\setmathfont{Foo\", body = \"Evil}\n"),
      ("font path", "\\usepackage{fontspec}\n\\setmainfont[Path=./x\", mono = \"Evil]{Foo}\n")] do
    let css := ((HtmlDoc.emitTree {} (surface pre).1).1.filterMap fun n => match n with
      | .style s => some s
      | _ => none).toList
    t s!"fontspec: a quote in a {what} sets no other slot"
      (css.all fun s => !hasStr s "\"Evil\"")
  t "hyperref: the reading holds at every depth, an author list's edges standing bare"
    (read "\\hypersetup{pdftitle={A{\\footnote{N.}\\mbox{B}}\\texorpdfstring{T} {P}{\\texorpdfstring{x}{y}}}}\n" ==
        some "ABPy" &&
      infoText (pdfOf geom fonts (surface "\\hypersetup{pdfauthor={\\and Ann \\and Bo\\and}}\n").1)
        "Author" == some "Ann; Bo")
  let titled := elabStr (dvDoc ("\\title{The Real Title}\n\\author{Someone}\n\\usepackage{hyperref}\n" ++
    "\\makeatletter\\AtBeginDocument{\\hypersetup{pdftitle={\\@title}, pdfauthor={\\@author}, " ++
    "pdfsubject={}}}\\makeatother\n") "Words.")
  let titledPdf := pdfOf geom fonts titled.1
  t "hyperref: the title and author LaTeX keeps are the document's, and an empty value leaves its field to them"
    (infoText titledPdf "Title" == some "The Real Title" && infoText titledPdf "Author" == some "Someone" &&
      infoText titledPdf "Subject" == none && titled.2.all (·.code != "W0301"))
  let (french, frenchDiags) := elabStr (dvDoc "\\usepackage[french]{babel}\n\\usepackage{hyperref}\n\\hypersetup{pdftitle={Le \\foreignlanguage{english}{workshop} {\\ul{deux}} \\raisebox{1pt}{R}}}\n" "Mots.")
  t "hyperref: a value is the body's TeX, rewritten as the body is"
    (infoText (pdfOf geom fonts french) "Title" == some "Le workshop deux R" &&
      frenchDiags.all fun d => d.code != "W0301" && d.code != "W0104")
  let spaced := (surface "\\hypersetup{pdftitle={A\\ }, pdfsubject={B}}\n").1
  t "hyperref: a value ending in a control space keeps its key's neighbour"
    (infoText (pdfOf geom fonts spaced) "Subject" == some "B")
  let refDiags := (elabStr (dvDoc "\\usepackage{hyperref}\n\\hypersetup{pdftitle={See \\ref{sec:a}}}\n"
    "\\section{Alpha}\\label{sec:a}Words.")).2
  t "hyperref: a reference in a value, which metadata reads before the page numbers it, is named"
    (refDiags.any fun d => d.code == "W0349" && hasStr d.message "pdftitle")
  t "hyperref: the carrier's mark holds a character no control word holds"
    (Compat.metaTextMark.any (!Lex.nameChar ·))
  let colourSrc := dvDoc ("\\usepackage{xcolor}\n\\definecolor{ink, accent = HTML(FF0000), x}{HTML}{112233}\n" ++
    "\\colorlet{brand}{blue, fg = red}\n\\linespread{1.0, fontsize = 20pt}\n")
    "Alpha \\textcolor{accent}{words} and more words."
  t "xcolor: a colour's name or value, or a line spread, sets no other key on the page"
    (!bytesContain (pdfText (pdfOf geom fonts (elabStr colourSrc).1)) "1 0 0 rg" &&
      lineSizeOf (censusOfSrc fonts colourSrc) 0 "Alpha" == some (Dim.pt 10))
  let hyphened := elabStr (dvDoc "\\usepackage{xcolor}\n\\definecolor{light-grey}{gray}{0.95}\n" "Words.")
  t "xcolor: a colour name no palette key spells is named and the document ships"
    (hyphened.2.any (·.code == "W0102") && hyphened.2.all (·.severity != .error))
  let linkDiags := (surface ("\\usepackage{hyperref}\n" ++
    "\\hypersetup{colorlinks, linkcolor={blue, font = \\bfseries}}\n")).2
  t "hyperref: a link colour no palette entry reads is named, not spliced"
    (linkDiags.any fun d => d.code == "W0102" && hasStr d.message "linkcolor")
  let fontDoc := (surface "\\usepackage{fontspec}\n\\setmainfont{Foo\", mono = \"Evil}\n").1
  let css := ((HtmlDoc.emitTree {} fontDoc).1.filterMap fun n => match n with
    | .style s => some s
    | _ => none).toList
  t "fontspec: a quote in a family name sets no other slot, and the stylesheet quotes it whole"
    (css.all (fun s => !hasStr s "--font-mono: \"Evil\"") &&
      css.any fun s => hasStr s "--font-body: \"Foo\\\", mono = \\\"Evil\", Georgia, serif;")

/-- A macro body's argument holding a parameter is a template: the macro ships what its expansion
written out ships and raises what that text raises, at the use, nothing where it is defined. -/
def templateArgChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let said (ds : Array Diag) : List (String × String) :=
    (ds.filter (·.severity != .note)).toList.map fun d => (d.code, d.message)
  let ships (src : String) : Array UInt8 × String × String :=
    let doc := (elabStr src).1
    let (head, tree, _) := HtmlDoc.emitTree {} doc
    ((pdfOf geom fonts doc).data, Html.document "en" head #[], shownTextList "" tree.toList)
  let lines := String.intercalate " " (List.replicate 40 "Words set at the leading the spread asks for.")
  let deckSrc (pre : String) : String :=
    "\\documentclass{beamer}\n" ++ pre ++
      "\\begin{document}\n\\begin{frame}{Alpha}\nWords.\n\\end{frame}\n\\end{document}"
  let colour := "\\usepackage{xcolor}\n"
  let babel := "\\usepackage[french,english]{babel}\n"
  let pairs : List (String × String × String) := [
    ("a definition through two macros",
      dvDoc (colour ++ "\\makeatletter\n\\def\\probe@define#1#2#3{\\definecolor{#3}{#1}{#2}}\n" ++
        "\\newcommand\\probe@use[1]{\\probe@define{HTML}{8B0000}{#1}}\n\\probe@use{probered}\n" ++
        "\\makeatother\n") "Alpha \\textcolor{probered}{words}.",
      dvDoc (colour ++ "\\definecolor{probered}{HTML}{8B0000}\n") "Alpha \\textcolor{probered}{words}."),
    ("a colour let",
      dvDoc (colour ++ "\\newcommand\\mklet[2]{\\colorlet{#1}{#2}}\n\\mklet{probelet}{blue!50!black}\n")
        "Alpha \\textcolor{probelet}{words}.",
      dvDoc (colour ++ "\\colorlet{probelet}{blue!50!black}\n") "Alpha \\textcolor{probelet}{words}."),
    ("a spot colour",
      dvDoc (colour ++ "\\newcommand\\mkspot[2]{\\definespotcolor{#1}{#2}{0,0.8,1,0.4}}\n" ++
        "\\mkspot{probespot}{Probe Ink}\n") "Alpha \\textcolor{probespot}{words}.",
      dvDoc (colour ++ "\\definespotcolor{probespot}{Probe Ink}{0,0.8,1,0.4}\n")
        "Alpha \\textcolor{probespot}{words}."),
    ("a line spread",
      dvDoc "\\newcommand\\spread[1]{\\linespread{#1}}\n\\spread{1.6}\n" lines,
      dvDoc "\\linespread{1.6}\n" lines),
    ("a metadata value",
      dvDoc "\\usepackage{hyperref}\n\\newcommand\\settitle[1]{\\hypersetup{pdftitle={#1}}}\n\\settitle{Probe Title}\n"
        "Words.",
      dvDoc "\\usepackage{hyperref}\n\\hypersetup{pdftitle={Probe Title}}\n" "Words."),
    ("a link colour",
      dvDoc (colour ++ "\\usepackage{hyperref}\n\\newcommand\\links[1]{\\hypersetup{colorlinks, linkcolor=#1}}\n" ++
        "\\links{teal}\n") "\\section{Alpha}\\label{s:a}Words and \\ref{s:a}.",
      dvDoc (colour ++ "\\usepackage{hyperref}\n\\hypersetup{colorlinks, linkcolor=teal}\n")
        "\\section{Alpha}\\label{s:a}Words and \\ref{s:a}."),
    ("a family name and its path",
      dvDoc "\\usepackage{fontspec}\n\\newcommand\\setbody[2]{\\setmainfont[Path=#1]{#2}}\n\\setbody{./faces/}{Probe Serif}\n"
        "Words.",
      dvDoc "\\usepackage{fontspec}\n\\setmainfont[Path=./faces/]{Probe Serif}\n" "Words."),
    ("a math family",
      dvDoc "\\usepackage{unicode-math}\n\\newcommand\\mathf[1]{\\setmathfont{#1}}\n\\mathf{Probe Math}\n"
        "Alpha $x+y$.",
      dvDoc "\\usepackage{unicode-math}\n\\setmathfont{Probe Math}\n" "Alpha $x+y$."),
    ("a language for a span",
      dvDoc (babel ++ "\\newcommand\\inlang[2]{\\foreignlanguage{#1}{#2}}\n") "Alpha \\inlang{french}{mot} words.",
      dvDoc babel "Alpha \\foreignlanguage{french}{mot} words."),
    ("a language switch",
      dvDoc (babel ++ "\\newcommand\\sel[1]{\\selectlanguage{#1}}\n") "Alpha.\n\n\\sel{french} Mot.",
      dvDoc babel "Alpha.\n\n\\selectlanguage{french} Mot."),
    ("a font series",
      dvDoc "\\newcommand\\ser[2]{{\\fontseries{#1}\\selectfont #2}}\n" "Alpha \\ser{b}{bold words}.",
      dvDoc "" "Alpha {\\fontseries{b}\\selectfont bold words}."),
    ("a length",
      dvDoc "\\newcommand\\ind[1]{\\setlength{\\parindent}{#1}}\n\\ind{3em}\n" "Alpha words.\n\nBeta words.",
      dvDoc "\\setlength{\\parindent}{3em}\n" "Alpha words.\n\nBeta words."),
    ("a length added to",
      dvDoc "\\newcommand\\addind[1]{\\addtolength{\\parindent}{#1}}\n\\addind{1em}\n" "Alpha words.\n\nBeta words.",
      dvDoc "\\addtolength{\\parindent}{1em}\n" "Alpha words.\n\nBeta words."),
    ("a name its expansion spells with a space",
      dvDoc (colour ++ "\\newcommand\\mk[2]{\\definecolor{#1}{HTML}{#2}}\n\\mk{bad name}{8B0000}\n") "Words.",
      dvDoc (colour ++ "\\definecolor{bad name}{HTML}{8B0000}\n") "Words."),
    ("a value its expansion spells with a quote",
      dvDoc (colour ++ "\\newcommand\\mk[2]{\\definecolor{#1}{HTML}{#2}}\n\\mk{probeq}{8B0000\", x = \"y}\n")
        "Words.",
      dvDoc (colour ++ "\\definecolor{probeq}{HTML}{8B0000\", x = \"y}\n") "Words."),
    ("a link colour its expansion spells with another key",
      dvDoc ("\\usepackage{hyperref}\n\\newcommand\\lk[1]{\\hypersetup{colorlinks, linkcolor=#1}}\n" ++
        "\\lk{{blue, font = \\bfseries}}\n") "Words.",
      dvDoc "\\usepackage{hyperref}\n\\hypersetup{colorlinks, linkcolor={blue, font = \\bfseries}}\n" "Words."),
    ("two uses with two values",
      dvDoc (colour ++ "\\newcommand\\mk[2]{\\definecolor{#1}{HTML}{#2}}\n\\mk{probeone}{8B0000}\n" ++
        "\\mk{probetwo}{00008B}\n") "Alpha \\textcolor{probeone}{one} \\textcolor{probetwo}{two}.",
      dvDoc (colour ++ "\\definecolor{probeone}{HTML}{8B0000}\n\\definecolor{probetwo}{HTML}{00008B}\n")
        "Alpha \\textcolor{probeone}{one} \\textcolor{probetwo}{two}."),
    ("a parameter of a nested definition",
      dvDoc (colour ++ "\\newcommand\\mkouter[1]{\\newcommand\\mkinner[1]{\\definecolor{##1}{HTML}{#1}}}\n" ++
        "\\mkouter{8B0000}\n\\mkinner{probenest}\n") "Alpha \\textcolor{probenest}{words}.",
      dvDoc (colour ++ "\\definecolor{probenest}{HTML}{8B0000}\n") "Alpha \\textcolor{probenest}{words}."),
    ("a page style",
      dvDoc "\\newcommand\\ps[1]{\\pagestyle{#1}}\n\\ps{empty}\n" "Words.",
      dvDoc "\\pagestyle{empty}\n" "Words."),
    ("a language environment",
      dvDoc (babel ++ "\\newcommand\\ola[2]{\\begin{otherlanguage}{#1}#2\\end{otherlanguage}}\n")
        "Alpha \\ola{french}{mot} words.",
      dvDoc babel "Alpha \\begin{otherlanguage}{french}mot\\end{otherlanguage} words."),
    ("a beamer template",
      deckSrc "\\newcommand\\se[1]{\\setbeamertemplate{navigation symbols}{#1}}\n\\se{}\n",
      deckSrc "\\setbeamertemplate{navigation symbols}{}\n"),
    ("a beamer template no use reaches",
      deckSrc "\\newcommand\\se[1]{\\setbeamertemplate{navigation symbols}{#1}}\n",
      deckSrc "")]
  for (what, tpl, written) in pairs do
    t s!"template: {what} raises what its text written out raises, nothing where it is defined"
      (said (elabStr tpl).2 == said (elabStr written).2)
    t s!"template: {what} ships the page and the web page's head its text written out ships"
      (ships tpl == ships written)
  let repro := (pairs.headD ("", "", "")).2.1
  let spanLang := (elabStr (dvDoc (babel ++ "\\newcommand\\inlang[2]{\\foreignlanguage{#1}{#2}}\n")
    "Alpha \\inlang{french}{mot} words.")).1
  t "template: a language for a span marks the span on the web page"
    (hasStr (HtmlDoc.emit {} spanLang).1 "<span lang=\"fr\">mot</span>")
  t "template: the colour a definition through two macros sets is painted"
    (bytesContain (pdfText (pdfOf geom fonts (elabStr repro).1)) "0.5451 0 0 rg")
  let twoUses := (elabStr (dvDoc (colour ++ "\\newcommand\\mk[2]{\\definecolor{#1}{HTML}{#2}}\n" ++
    "\\mk{probeone}{8B0000}\n\\mk{probetwo}{00008B}\n")
    "Alpha \\textcolor{probeone}{one} \\textcolor{probetwo}{two}.")).1
  let twoText := pdfText (pdfOf geom fonts twoUses)
  t "template: two uses with two values paint each its own colour"
    (bytesContain twoText "0.5451 0 0 rg" && bytesContain twoText "0 0 0.5451 rg")
  let spaced := (elabStr (dvDoc (colour ++ "\\newcommand\\mk[2]{\\definecolor{#1}{HTML}{#2}}\n" ++
    "\\mk{bad name}{8B0000}\n") "Words.")).2.filter (·.code == "W0102")
  t "template: a name its expansion spells with a space is named once, at the use"
    (spaced.size == 1 && spaced.all fun d => d.sites == 1 && d.span.map (·.pos.line) == some 4)
  let envCases : List (String × String × String × List String × Option String) := [
    ("a colour definition",
      colour ++ "\\newenvironment{probeenv}[1]{\\definecolor{probeenvc}{HTML}{#1}}{}\n",
      "\\begin{probeenv}{8B0000}\nAlpha words.\n\\end{probeenv}", ["8B0000", "probeenvc", "HTML"],
      some "definecolor"),
    ("a language switch", babel ++ "\\newenvironment{inlang}[1]{\\selectlanguage{#1}}{}\n",
      "Alpha.\n\\begin{inlang}{french}\nMot.\n\\end{inlang}", ["french"], some "selectlanguage"),
    ("a span's language", babel ++ "\\newenvironment{fl}[2]{\\foreignlanguage{#1}{#2}}{}\n",
      "\\begin{fl}{french}{mot}\nAlpha.\n\\end{fl}", ["french"], some "foreignlanguage"),
    ("a length", "\\newenvironment{ind}[1]{\\setlength{\\parindent}{#1}}{}\n",
      "\\begin{ind}{3em}\nAlpha words.\n\nBeta words.\n\\end{ind}", ["3em"], some "setlength"),
    ("a metadata value", "\\usepackage{hyperref}\n\\newenvironment{probemeta}[1]{\\hypersetup{pdftitle={#1}}}{}\n",
      "\\begin{probemeta}{Probe Title}\nWords.\n\\end{probemeta}", ["Probe", "pdftitle"],
      some "hypersetup"),
    ("a colour macro its code calls",
      colour ++ "\\newcommand\\mk[2]{\\definecolor{#1}{HTML}{#2}}\n" ++
        "\\newenvironment{red}{\\mk{probered}{8B0000}\\color{probered}}{}\n",
      "\\begin{red}\nAlpha words.\n\\end{red}", ["8B0000", "probered", "HTML"], none),
    ("a language macro its begin and end code call",
      babel ++ "\\newcommand\\sel[1]{\\selectlanguage{#1}}\n\\newenvironment{fr}{\\sel{french}}{\\sel{english}}\n",
      "Alpha.\n\\begin{fr}\nMot.\n\\end{fr}", ["french", "english"], none)]
  for (what, pre, body, words, cmd) in envCases do
    let src := dvDoc pre body
    let (ds, _, _, shown) := sourceArtifacts fonts src
    let page := pageTextOf fonts src
    t s!"template: {what} in an environment's code prints no argument on the page"
      (!page.isEmpty && words.all fun w => !hasStr page w)
    t s!"template: {what} in an environment's code prints no argument on the web page"
      (!shown.isEmpty && words.all fun w => !hasStr shown w)
    if let some c := cmd then
      t s!"template: {what} in an environment's code is named once, where it stands"
        ((ds.filter (·.subject == some ("envcode:" ++ c))).size == 1)
  t "template: a span's language in an environment's code keeps the span's text"
    (hasStr (pageTextOf fonts (dvDoc (babel ++ "\\newenvironment{fl}[2]{\\foreignlanguage{#1}{#2}}{}\n")
      "\\begin{fl}{french}{mot}\nAlpha.\n\\end{fl}")) "mot")

end Tests.MetaEscape
