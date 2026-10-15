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

/-- A text string's characters (§7.9.2.2): UTF-16BE after its byte-order mark, else bytes. -/
def textOf (b : ByteArray) : String :=
  match b.data.toList.map UInt8.toNat with
  | 0xFE :: 0xFF :: rest => utf16 rest ""
  | bs => String.ofList (bs.map Char.ofNat)

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
  textOf <$> PdfContentLex.strBytes? o

/-- One catalog entry's text. -/
def catalogText (pdf : ByteArray) (key : String) : Option String := do
  let tr ← (PdfRead.trailer pdf).toOption
  let doc ← (PdfRead.Doc.ofBytes pdf).toOption
  let root ← (doc.deref (← tr.get? "Root")).toOption
  textOf <$> PdfContentLex.strBytes? (← root.get? key)

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
        xmpField pdf "dc:description" == some (xmlAdmitted v))
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
  let fontDoc := (surface "\\usepackage{fontspec}\n\\setmainfont{Foo\", mono = \"Evil}\n").1
  let css := ((HtmlDoc.emitTree {} fontDoc).1.filterMap fun n => match n with
    | .style s => some s
    | _ => none).toList
  t "fontspec: a quote in a family name sets no other slot, and the stylesheet quotes it whole"
    (css.all (fun s => !hasStr s "--font-mono: \"Evil\"") &&
      css.any fun s => hasStr s "--font-body: \"Foo\\\", mono = \\\"Evil\", Georgia, serif;")

end Tests.MetaEscape
