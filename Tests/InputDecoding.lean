module

public import Lean.Data.Json.Parser
public import Lean.Data.Json
public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

namespace InputDecoding

/-- The probes, invented: testdata/probes/u96. -/
def probes : System.FilePath := "testdata/probes/u96"

def probe (name : String) : IO ByteArray := IO.FS.readBinFile (probes / name)

/-- A tex file read the way the driver first reads its document. -/
def readTexFile (file : String) (bytes : ByteArray) : Encoding.FileText :=
  (Encoding.readDocument file bytes).1

def codes (ds : Array Diag) (c : DiagCode) : Nat := (ds.filter (·.kind == c)).size

def count (text : String) (c : Char) : Nat := (text.toList.filter (· == c)).length

def isLegacy : Encoding.Reading → Bool
  | .legacy _ => true
  | _ => false

/-- The porcelain records a run of the built binary prints, as JSON. -/
def records (stdout : String) : Array Lean.Json :=
  ((stdout.splitOn "\n").filterMap fun line => (Lean.Json.parse line).toOption).toArray

def recordCodes (rs : Array Lean.Json) (code : String) : Array Lean.Json :=
  rs.filter (·.getObjValAs? String "code" == .ok code)

def recordMessage (r : Lean.Json) : String := (r.getObjValAs? String "message").toOption.getD ""

/-- A document around a body whose bytes need not be UTF-8. -/
def doc (preamble : String) (body : ByteArray) : ByteArray :=
  s!"\\documentclass\{article}\n{preamble}\\begin\{document}\n".toUTF8 ++ body ++
    "\n\\end{document}\n".toUTF8

/-- The same bytes with every LF a CR: a file with classic Mac line ends. -/
def crOnly (bs : ByteArray) : ByteArray := ⟨bs.data.map fun b => if b == 0x0A then 0x0D else b⟩

/-- The same bytes with every LF a CR LF. -/
def crlf (bs : ByteArray) : ByteArray :=
  ⟨bs.data.foldl (fun acc b => if b == 0x0A then acc.push 0x0D |>.push 0x0A else acc.push b) #[]⟩

def elemCount (tag : String) (nodes : Array Html.Node) : Nat :=
  (elemNodesList (· == tag) #[] nodes.toList).size

end InputDecoding

open InputDecoding in
/-- **Bytes never refuse a document, and every file reads as its bytes and
its declaration say.** The invariants the input door owes, each failing on
the reader it replaced: a leading byte-order mark is not text on either
surface (it was E0313 in tex, and a markdown heading read as a paragraph),
and a UTF-16 mark reads UTF-16; one byte that is not UTF-8 ships as one
U+FFFD and one warning naming its offset (it was fatal E0002), U+0000
among the bytes that warning lists; a file `\usepackage[latin1]{inputenc}`
declares reads byte by byte in that encoding, as pdfLaTeX prints it — a
French or German text whose accented letter precedes a byte UTF-8 takes as
a continuation once read as a CJK or NKo scalar — unless its bytes say
UTF-8; the declaration governs every file the document reads, the one that
makes it and those read before it ran (an `\input` preamble's own title was
U+FFFD); a CR alone ends a line on both surfaces (a classic Mac file's
comment swallowed the rest of the document); the declaration's one note
says how each file read, and its help never deletes a declaration a file
still needs; a switch of encoding mid-file is named, its argument never
ink; a file read twice is named once; and a `.bib` or `.sty` in Latin-1
reads instead of escaping as an uncaught exception. Page claims read the
laid-out lines and the typed HTML tree; the wiring is held by the built
binary. -/
def inputDecodingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fontData ← findFont | failures ref "input decoding: missing fixture font"
  let .ok font := Font.parse fontData | failures ref "input decoding: invalid fixture font"
  let fonts := oneFaceOf font
  -- A leading byte-order mark: the text, the page and the diagnostics are
  -- those of the file without it, on both surfaces.
  let bomRead := Encoding.readTex none "u96-bom.tex" (← probe "u96-bom.tex")
  let plainRead := Encoding.readTex none "u96-nobom.tex" (← probe "u96-nobom.tex")
  t "input decoding: a byte-order mark is not text in tex"
    (bomRead.text == plainRead.text && bomRead.diags.isEmpty)
  t "input decoding: a byte-order mark ships the page of the file without it"
    (pageTextOf fonts bomRead.text == pageTextOf fonts plainRead.text &&
      hasStr (pageTextOf fonts bomRead.text) "BOM only." &&
      (elabStr bomRead.text).2.all (·.kind != .E0313))
  let mdRead := Encoding.readMarkdown "u96-bom.md" (← probe "u96-bom.md")
  let (_, mdTree, _) := HtmlDoc.emitTree {} (elabMd mdRead.text).1
  t "input decoding: a markdown heading after a byte-order mark is a heading"
    (mdRead.diags.isEmpty && mdRead.text.startsWith "# Title" &&
      (elemNodesList (· == "h1") #[] mdTree.toList).any fun n => match n with
        | .elem _ _ kids => nodeTextList "" kids.toList == "Title"
        | _ => false)
  -- One byte that is not UTF-8: one U+FFFD on the page, one warning that
  -- names its offset, line and column, and every offset for a tool.
  let bad := Encoding.readTex none "u96-badbyte.tex" (← probe "u96-badbyte.tex")
  t "input decoding: one bad byte reads as one U+FFFD" (count bad.text '\uFFFD' == 1)
  t "input decoding: one bad byte is one warning naming its offset and place"
    (bad.diags.size == 1 && codes bad.diags .W0002 == 1 && bad.diags.all fun d =>
      d.message == "byte 0xFF at offset 49 is not text in UTF-8" &&
      d.span == some ⟨"u96-badbyte.tex", { line := 3, col := 9 }⟩ &&
      d.recovery == some (.replacedBy "U+FFFD") && d.offsets == #[49])
  t "input decoding: the replacement reaches the page"
    (pageTextOf fonts bad.text == "One bad \uFFFD byte.")
  let five := Encoding.readTex none "five.tex"
    ("x".toUTF8 ++ bytes [0xFF, 0x61, 0xFE, 0x62, 0xFF, 0x63, 0xFE, 0x64, 0xFF])
  t "input decoding: a warning lists three offsets and gives a tool all of them"
    (five.diags.any fun d => d.kind == .W0002 && d.offsets == #[1, 3, 5, 7, 9] &&
      d.message == "5 byte sequences are not text in UTF-8, at offsets 1 (0xFF), 3 (0xFE), \
5 (0xFF) and 2 more")
  let cut := Encoding.readTex none "cut.tex" ("a".toUTF8 ++ bytes [0xE2, 0x82] ++ "b".toUTF8)
  t "input decoding: a truncated sequence is one U+FFFD naming its bytes"
    (cut.text == "a\uFFFDb" && cut.diags.any fun d =>
      d.message == "the bytes 0xE2 0x82 at offset 1 are not text in UTF-8")
  -- The help follows what the bytes show.
  let stray := Encoding.readTex none "stray.tex"
    ("Café crème".toUTF8 ++ bytes [0x92] ++ "s".toUTF8)
  t "input decoding: a stray byte in a UTF-8 file is advised as a correction"
    (stray.diags.any fun d => d.kind == .W0002 &&
      d.help == some "correct the bytes at those offsets: the rest of the file is UTF-8")
  let latinish := Encoding.readTex none "plain.tex" ("Caf".toUTF8 ++ bytes [0xE9])
  t "input decoding: an 8-bit file is advised to declare or convert"
    (latinish.diags.any fun d => d.kind == .W0002 && d.help.any (hasStr · "inputenc"))
  -- As many UTF-8 sequences as stray bytes: a Latin-1 declaration would read
  -- the sequence as two characters, so the help corrects the stray byte.
  let tie := Encoding.readTex none "tie.tex"
    ("Caf".toUTF8 ++ bytes [0xC3, 0xA9] ++ " cr".toUTF8 ++ bytes [0xE8] ++ "me.".toUTF8)
  t "input decoding: a file as much UTF-8 as not is advised as a correction, never a declaration"
    (tie.diags.any fun d => d.kind == .W0002 &&
      d.help == some "correct the bytes at those offsets: the rest of the file is UTF-8")
  -- A document that declares UTF-8 is never told to load inputenc again: a
  -- second load is ignored, so the help names the load it has.
  let utf8Declared : Encoding.Declared := ⟨"utf8", .utf8, "usepackage", ⟨"u.tex", {}⟩⟩
  let underUtf8 := Encoding.readTex (some utf8Declared) "u.tex" ("Caf".toUTF8 ++ bytes [0xE9])
  t "input decoding: a file declared UTF-8 is advised to name its encoding in its own load"
    (underUtf8.diags.any fun d => d.kind == .W0002 && d.help == some
      "'\\usepackage[utf8]{inputenc}' reads UTF-8: save the file as UTF-8, or name its \
encoding in that load, as \\usepackage[latin1]{inputenc} reads Latin-1")
  -- Latin-1 under its declaration: pdfLaTeX's text, and nothing named.
  let latin := readTexFile "u96-latin1.tex" (← probe "u96-latin1.tex")
  t "input decoding: a declared Latin-1 file prints as pdfLaTeX prints it"
    (pageTextOf fonts latin.text == "Café crème." && latin.diags.isEmpty &&
      isLegacy latin.reading)
  -- Two texts whose accented letters precede bytes UTF-8 takes as
  -- continuations: they read byte by byte as declared, the page is the
  -- page of the same text saved as UTF-8, and nothing warns — the declared
  -- reading is pdfLaTeX's — while the sequences are kept for the note.
  for (name, preamble, utf8) in [
      ("u96-french.tex", "\\usepackage[T1]{fontenc}\n\\usepackage[latin1]{inputenc}\n",
        "«\u00A0l'été\u00A0» et ÉTÉ\u00A0: fin."),
      ("u96-german.tex", "\\usepackage[T1]{fontenc}\n\\usepackage[cp1252]{inputenc}\n",
        "»Spaß« und „Gruß“.")] do
    let read := readTexFile name (← probe name)
    let same := readTexFile "same.tex" (doc preamble utf8.toUTF8)
    t s!"input decoding: {name} reads as the text it holds, and prints its page"
      (read.text == same.text && isLegacy read.reading &&
        pageTextOf fonts read.text == pageTextOf fonts same.text &&
        !(pageTextOf fonts read.text).isEmpty)
    t s!"input decoding: {name} reads as declared with no warning, its two UTF-8 runs kept"
      (read.diags.isEmpty && read.minority.size == 2)
  let french := readTexFile "u96-french.tex" (← probe "u96-french.tex")
  t "input decoding: the runs kept are the bytes UTF-8 would have taken"
    (french.minority == #[(102, 3), (111, 2)])
  -- A UTF-8 file declaring latin1 reads as UTF-8: valid, or with a stray
  -- byte its well-formed sequences outnumber, read as declared and named.
  let stale := readTexFile "stale.tex"
    (doc "\\usepackage[latin1]{inputenc}\n" "Café crème.".toUTF8)
  t "input decoding: a file that is valid UTF-8 reads as UTF-8 whatever it declares"
    (pageTextOf fonts stale.text == "Café crème." && stale.diags.isEmpty &&
      stale.reading == .utf8)
  t "input decoding: an overruled declaration ships the page of the document without it"
    (pageTextOf fonts stale.text ==
      pageTextOf fonts (readTexFile "plain.tex" (doc "" "Café crème.".toUTF8)).text)
  let mixed := readTexFile "u96-mixed.tex" (← probe "u96-mixed.tex")
  t "input decoding: a UTF-8 file's stray byte reads as declared, the rest as UTF-8"
    (pageTextOf fonts mixed.text == "Café crème’s." && mixed.reading == .utf8 &&
      codes mixed.diags .W0002 == 0)
  t "input decoding: the stray byte a UTF-8 file read as declared is named, a guess"
    (mixed.diags.size == 1 && mixed.diags.all fun d => d.kind == .W0004 &&
      d.message == "byte 0x92 at offset 83 is read as Windows-1252 (Latin-1), as declared, \
in a file otherwise UTF-8" && d.offsets == #[83])
  -- A tie is no evidence: it goes to the declaration.
  let tie := readTexFile "tie.tex"
    (doc "\\usepackage[latin1]{inputenc}\n" ("x".toUTF8 ++ bytes [0xC3, 0xA9, 0x20, 0xE9]))
  t "input decoding: as many sequences as stray bytes read as declared"
    (isLegacy tie.reading && hasStr tie.text "xÃ© é\n")
  -- An ASCII file reads alike under every declaration: nothing named.
  let ascii := doc "\\usepackage[latin1]{inputenc}\n" "x".toUTF8
  let asciiRead := readTexFile "ascii.tex" ascii
  t "input decoding: an ASCII file reads the same under any declaration"
    (asciiRead.text == (String.fromUTF8? ascii).getD "" && asciiRead.diags.isEmpty &&
      asciiRead.reading == .ascii)
  -- Each encoding's distinguishing bytes, Mac OS Roman's two rows from its
  -- owner's table, and a byte one leaves undefined.
  for (option, byte, expected) in [("latin9", (0xA4 : UInt8), '\u20AC'),
      ("cp1252", 0x80, '\u20AC'), ("ansinew", 0x93, '\u201C'), ("latin1", 0x92, '\u2019'),
      ("applemac", 0x8E, '\u00E9'), ("applemac", 0xDB, '\u20AC'), ("applemac", 0xC6, '\u2206'),
      ("applemac", 0xF0, '\uF8FF'), ("latin9", 0xBD, '\u0153')] do
    let r := readTexFile "enc.tex" (s!"\\usepackage[{option}]\{inputenc}\n".toUTF8 ++ bytes [byte])
    t s!"input decoding: {option} reads byte {byte} as U+{expected.toNat}"
      (r.text.endsWith (String.singleton expected) && isLegacy r.reading && r.diags.isEmpty)
  let hole := readTexFile "hole.tex" ("\\usepackage[cp1252]{inputenc}\n".toUTF8 ++ bytes [0x81])
  t "input decoding: a byte Windows-1252 leaves undefined is U+FFFD, named"
    (hole.text.endsWith "\uFFFD" && hole.diags.any fun d => d.kind == .W0002 &&
      d.message == "byte 0x81 at offset 30 is not text in Windows-1252 (Latin-1)")
  let unread := readTexFile "latin2.tex"
    ("\\usepackage[latin2]{inputenc}\n".toUTF8 ++ bytes [0xB1])
  t "input decoding: an encoding the engine does not read is UTF-8 with its loss named"
    (unread.text.endsWith "\uFFFD" && unread.reading == .replaced &&
      unread.diags.any fun d => d.kind == .W0002 &&
        d.help.any (hasStr · "'\\usepackage[latin2]{inputenc}'"))
  let marked := readTexFile "marked.tex"
    (Utf8.bom ++ "\\usepackage[latin1]{inputenc}\n".toUTF8 ++ bytes [0xE9])
  t "input decoding: a file its byte-order mark calls UTF-8 reads its stray bytes as declared"
    (marked.text.endsWith "é" && marked.reading == .utf8 && marked.diags.any fun d =>
      d.kind == .W0004 && hasStr d.message "in a file its byte-order mark calls UTF-8")
  -- UTF-16 by its byte-order mark, whatever the file declares.
  let u16 := Encoding.readTex none "u96-utf16.tex" (← probe "u96-utf16.tex")
  t "input decoding: a UTF-16 byte-order mark reads UTF-16"
    (u16.reading == .utf16 false && u16.diags.isEmpty &&
      pageTextOf fonts u16.text == "UTF-16 Café.")
  let be := ByteArray.mk #[0xFE, 0xFF, 0x00, 0x41, 0xD8, 0x3D, 0xDE, 0x00, 0xDC, 0x00, 0x00,
    0x00, 0x00, 0x42]
  let beRead := Encoding.readMarkdown "be.md" be
  t "input decoding: UTF-16BE pairs surrogates, and names a lone one and U+0000 in one warning"
    (beRead.text == String.ofList ['A', Char.ofNat 0x1F600, '\uFFFD', '\uFFFD', 'B'] &&
      beRead.reading == .utf16 true && beRead.diags.size == 1 &&
      beRead.diags.all (fun d => d.kind == .W0002 && d.offsets == #[8, 10] &&
        d.message == "2 byte sequences are not text in UTF-16BE, at offsets 8 (0xDC 0x00) and \
10 (0x00 0x00)"))
  let odd := Encoding.readMarkdown "u96-odd16.md" (← probe "u96-odd16.md")
  t "input decoding: a trailing odd byte of UTF-16 is the one byte it is"
    (odd.text == "Hi\uFFFD" && odd.diags.all fun d =>
      d.message == "byte 0x41 at offset 6 is not text in UTF-16LE" && d.offsets == #[6])
  let bare := Encoding.readTex none "bare.tex"
    ("Hi there".toList.foldl (fun b c => b ++ bytes [c.toNat.toUInt8, 0]) ByteArray.empty)
  t "input decoding: UTF-16 with no mark is named as such"
    (bare.diags.any fun d =>
      d.help == some "the file looks like UTF-16 with no byte-order mark: save it as UTF-8")
  -- U+0000 is not text on either surface, and is among the bytes the one
  -- warning per file lists.
  let nul := Encoding.readMarkdown "u96-nul.md" (← probe "u96-nul.md")
  t "input decoding: U+0000 in markdown is U+FFFD, named once as what it is"
    (!nul.text.contains '\x00' && count nul.text '\uFFFD' == 1 && codes nul.diags .W0002 == 1 &&
      nul.diags.all (·.message == "U+0000 at offset 8 is not text") &&
      treeShownOccurs (HtmlDoc.emitTree {} (elabMd nul.text).1).2.1 "A\uFFFDB" == 1)
  let texNul := Encoding.readTex none "nul.tex" ("A".toUTF8 ++ bytes [0] ++ "B".toUTF8)
  t "input decoding: U+0000 in tex is U+FFFD, named once"
    (texNul.text == "A\uFFFDB" && codes texNul.diags .W0002 == 1)
  let nulBad := Encoding.readMarkdown "u96-nulbad.md" (← probe "u96-nulbad.md")
  t "input decoding: U+0000 and a bad byte in one file are one warning"
    (nulBad.diags.size == 1 && nulBad.diags.all fun d => d.kind == .W0002 &&
      d.offsets == #[10, 17] && d.subject == some "input-bytes:u96-nulbad.md" &&
      d.message == "2 byte sequences are not text in UTF-8, at offsets 10 (0x00) and 17 (0xFF)")
  -- A line ends at LF, CR LF and a CR alone, on both surfaces: the page of
  -- a file with classic Mac or Windows line ends is the page of the same
  -- file with LF, and a comment ends at its line.
  let lfTex := doc "" "Caf\u00e9 one. % a comment\n\nSecond paragraph.".toUTF8
  let lfPage := pageLines fonts (Encoding.readTex none "lf.tex" lfTex).text
  for (label, bs) in [("CR", crOnly lfTex), ("CR LF", crlf lfTex)] do
    let read := Encoding.readTex none "ends.tex" bs
    t s!"input decoding: {label} line ends set the page LF sets"
      (!read.text.contains '\r' && pageLines fonts read.text == lfPage &&
        lfPage.any fun p => p.any (·.2 == "Café one.") && p.any (·.2 == "Second paragraph."))
  -- `settle` against its reading spelled out character by character, where
  -- a CR, an LF and a U+0000 meet each other and longer characters.
  let spelled (t : String) : String := Id.run do
    let mut out := ""
    let mut cr := false
    for c in t.toList do
      if c == '\n' then
        unless cr do out := out.push '\n'
        cr := false
      else if c == '\r' then
        out := out.push '\n'
        cr := true
      else
        out := out.push (if c == '\x00' then '\uFFFD' else c)
        cr := false
    return out
  for sample in ["a\r\nb\rc\x00d\r\r\n", "é\r€\n\r\x00\r", "\r", "\n\r\n\r", "x\x00\x00é\r\n"] do
    t s!"input decoding: settle reads {repr sample} as its characters say"
      (Encoding.settle sample == spelled sample)
  let crTex := readTexFile "u96-cr.tex" (← probe "u96-cr.tex")
  t "input decoding: a classic Mac file's comment ends at its line"
    (crTex.diags.isEmpty && hasStr (pageTextOf fonts crTex.text) "Café au lait." &&
      hasStr (pageTextOf fonts crTex.text) "Another paragraph." &&
      (elabStr crTex.text).2.all (·.severity != .error))
  let crMd := Encoding.readMarkdown "u96-cr.md" (← probe "u96-cr.md")
  let lfMd := Encoding.readMarkdown "lf.md" "# Heading\n\nFirst paragraph.\n\nSecond paragraph.\n".toUTF8
  let page (text : String) : String × Array Html.Node :=
    let (head, tree, _) := HtmlDoc.emitTree {} (elabMd text).1
    (Html.document "en" head tree, tree)
  let (crHtml, crTree) := page crMd.text
  t "input decoding: a markdown file with CR line ends is its heading and two paragraphs"
    (crHtml == (page lfMd.text).1 && elemCount "h1" crTree == 1 && elemCount "p" crTree == 2)
  -- The preamble scan: package lists, the first load, comments, the body,
  -- a comment that a CR ends, and the command that loads the package.
  for (src, expected) in [
      ("\\usepackage[T1]{fontenc}\\usepackage[latin1]{inputenc}", some "latin1"),
      ("\\usepackage[utf8,latin9]{inputenc}", some "latin9"),
      ("\\usepackage{fontenc,inputenc}", none),
      ("% \\usepackage[latin1]{inputenc}\n", none),
      ("% a comment\r\\usepackage[latin1]{inputenc}\r", some "latin1"),
      ("\\% \\usepackage[latin1]{inputenc}\n", some "latin1"),
      ("\\RequirePackage[applemac]{inputenc}", some "applemac"),
      ("\\usepackage{inputenc}\\usepackage[latin1]{inputenc}", none),
      ("\\usepackage[%\n  latin1]{%\ninputenc}", some "latin1"),
      ("\\begin{document}\\usepackage[latin1]{inputenc}\\end{document}", none)] do
    t s!"input decoding: the declaration scan reads {src}"
      (((Encoding.declaredIn "scan.tex" src.toUTF8).map (·.option)) == expected)
  t "input decoding: the scan keeps the command that loads the package"
    ((Encoding.declaredIn "scan.tex" "\\RequirePackage[latin1]{inputenc}".toUTF8).map (·.loader)
      == some "RequirePackage")
  -- The tables: one entry per byte, never a control character, and the
  -- encodings' published differences from ISO 8859-1.
  let tables := [EncodingData.windows1252, EncodingData.iso885915, EncodingData.macRoman]
  t "input decoding: each table covers the upper half"
    (tables.all (·.size == 128))
  t "input decoding: no table entry is a control character"
    (tables.all (·.all fun c => c.all fun c => c.toNat ≥ 0xA0))
  let latin9Moves := (List.range 96).filter fun k =>
    EncodingData.iso885915[32 + k]? != some (some (Char.ofNat (0xA0 + k)))
  t "input decoding: ISO 8859-15 moves exactly its eight positions from ISO 8859-1"
    (latin9Moves.map (0xA0 + ·) == [0xA4, 0xA6, 0xA8, 0xB4, 0xB8, 0xBC, 0xBD, 0xBE])
  t "input decoding: Windows-1252 is ISO 8859-1 from 0xA0"
    ((List.range 96).all fun k =>
      EncodingData.windows1252[32 + k]? == some (some (Char.ofNat (0xA0 + k))))
  -- The repair in a formula is an atom of its own: the formula still sets.
  let fs ← mathSetOf fonts
  let fs := { fs with fallback := #[('\uFFFD', 0)] }
  let mathSrc := (Encoding.readTex none "u96-math.tex" (← probe "u96-math.tex")).text
  let (ink, mathDs) := inkedScalars fs mathSrc
  t "input decoding: a replaced byte in a formula leaves the formula set"
    (ink.contains '\uFFFD' && ink.contains (Char.ofNat 0x1D465) && ink.contains (Char.ofNat 0x1D466) &&
      (elabStr mathSrc).2.all (·.kind != .W0012) && mathDs.all (·.kind != .E0405))
  -- Pending: U+FFFD needs a face that draws it. Where none does, the glyph
  -- is the coverage loss E0405, which refuses the PDF until glyph losses
  -- ship a placeholder; this check fails when that changes, and the pending
  -- notes in Encoding's module doc and the README go with it.
  match Font.parse (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")) with
  | .error _ => failures ref "input decoding: SourceSerifPro-Regular.otf unparsable"
  | .ok serif =>
    let (serifInk, serifDs) := inkedScalars (oneFaceOf serif) bad.text
    t "input decoding: an undrawable repair is the coverage loss, pending a placeholder"
      ((serif.gid '\uFFFD').isNone && !serifInk.contains '\uFFFD' &&
        DiagCode.E0405.loss == .dropped && serifDs.any (·.kind == .E0405))
  -- The declaration's note, from the front door over a document's bytes:
  -- one note, at the declaration, naming each file and how it read, and a
  -- help that deletes the declaration only where no file needs it.
  let noteOf (name : String) (bytes : ByteArray) : IO (Array Diag) := do
    return (← Input.readDocument name bytes).ledger.notes
  let latinNotes ← noteOf "u96-latin1.tex" (← probe "u96-latin1.tex")
  t "input decoding: a declaration's note names the file it read and how"
    (latinNotes.size == 1 && latinNotes.all fun d => d.kind == .N0025 &&
      d.span == some ⟨"u96-latin1.tex", { line := 2, col := 1 }⟩ &&
      d.message == "'\\usepackage[latin1]{inputenc}': 'u96-latin1.tex' reads as Windows-1252 \
(Latin-1)" &&
      d.help == some "save 'u96-latin1.tex' as UTF-8 (`iconv -f WINDOWS-1252 -t UTF-8`), then \
delete the declaration")
  let frenchNotes ← noteOf "u96-french.tex" (← probe "u96-french.tex")
  t "input decoding: the note names the runs a declared reading also reads as UTF-8"
    (frenchNotes.all fun d => d.message == "'\\usepackage[latin1]{inputenc}': 'u96-french.tex' \
reads as Windows-1252 (Latin-1), though its bytes at offsets 102 and 111 are well-formed UTF-8 \
too" && d.help.any (·.startsWith "check the text at those offsets, save 'u96-french.tex'"))
  let staleNotes ← noteOf "stale.tex" (doc "\\usepackage[latin1]{inputenc}\n" "Café.".toUTF8)
  t "input decoding: a declaration no file needs is advised for deletion"
    (staleNotes.size == 1 && staleNotes.all fun d =>
      d.message == "'\\usepackage[latin1]{inputenc}': 'stale.tex' is UTF-8, so the declaration \
is not applied to it" &&
      d.help == some "delete the declaration: every file it governs reads alike without it")
  -- Two files a deleted declaration would damage: a UTF-8 file whose stray
  -- byte reads as declared (deleting it makes the byte U+FFFD), and a UTF-8
  -- file under an encoding with no table, which `iconv` from that encoding
  -- would garble.
  let mixedNotes ← noteOf "u96-mixed.tex" (← probe "u96-mixed.tex")
  t "input decoding: a declaration a stray byte reads by is kept until the byte is spelled"
    (mixedNotes.size == 1 && mixedNotes.all fun d =>
      d.message == "'\\usepackage[latin1]{inputenc}': 'u96-mixed.tex' is UTF-8 but for the \
bytes read as Windows-1252 (Latin-1)" &&
      d.help == some "spell in UTF-8 the bytes 'u96-mixed.tex' reads as Windows-1252 (Latin-1), \
then delete the declaration")
  let mixedPlain := Encoding.readTex none "u96-mixed.tex" (← probe "u96-mixed.tex")
  t "input decoding: deleting that declaration would change the page"
    (pageTextOf fonts mixedPlain.text != pageTextOf fonts mixed.text)
  let latin2Notes ← noteOf "u96-latin2.tex" (← probe "u96-latin2.tex")
  t "input decoding: a UTF-8 file under an encoding with no table is not sent through iconv"
    (latin2Notes.size == 1 && latin2Notes.all fun d =>
      d.message == "'\\usepackage[latin2]{inputenc}' names an encoding this engine does not \
read: 'u96-latin2.tex' is UTF-8" &&
      d.help == some "delete the declaration: every file it governs reads alike without it")
  let latin2Bytes ← noteOf "l2.tex"
    (doc "\\usepackage[latin2]{inputenc}\n" ("Zaz".toUTF8 ++ bytes [0xBF, 0xF3, 0xB3]))
  t "input decoding: a file in an encoding with no table is sent through iconv from it"
    (latin2Bytes.all fun d =>
      d.message == "'\\usepackage[latin2]{inputenc}' names an encoding this engine does not \
read: 'l2.tex' is read as UTF-8, its other bytes replaced" &&
      d.help == some "save 'l2.tex' as UTF-8 (`iconv -f latin2 -t UTF-8`), then delete the \
declaration")
  t "input decoding: a declaration over ASCII says it changes nothing"
    ((← noteOf "ascii.tex" ascii).any fun d =>
      hasStr d.message "changes nothing: 'ascii.tex' is ASCII")
  t "input decoding: a UTF-8 declaration leaves its note to the package"
    ((← noteOf "u.tex" (doc "\\usepackage[utf8]{inputenc}\n" "Café.".toUTF8)).isEmpty)
  -- A declaration one file needs and another overrules: the help saves the
  -- one that needs it, and the note names both.
  let d : Encoding.Declared :=
    ⟨"latin1", .legacy .windows1252, "usepackage", ⟨"main.tex", { line := 2 }⟩⟩
  let both : Encoding.Ledger := {
    declared := some d
    reads := #[⟨"main.tex", some d, .legacy .windows1252, #[]⟩,
      ⟨"refs.bib", some d, .utf8, #[]⟩, ⟨"notes.tex", some d, .ascii, #[]⟩] }
  t "input decoding: a note names each file the declaration changed, and saves the one it read"
    (both.notes.size == 1 && both.notes.all fun n =>
      n.message == "'\\usepackage[latin1]{inputenc}': 'main.tex' reads as Windows-1252 \
(Latin-1); 'refs.bib' is UTF-8, so the declaration is not applied to it" &&
      n.help == some "save 'main.tex' as UTF-8 (`iconv -f WINDOWS-1252 -t UTF-8`), then delete \
the declaration")
  -- One accounting at the declaration: the package's translation note
  -- does not stand beside the reading's.
  let elabDs := (elabStr ((String.fromUTF8? ascii).getD "")).2
  t "input decoding: a non-UTF-8 declaration draws no translation note of its own"
    (elabDs.all fun d => !(d.kind == .N0100 && d.span.any (·.pos.line == 2)))
  -- A switch of encoding mid-file: the file reads in one encoding, the
  -- switch is named and its argument is not ink; a switch to the encoding
  -- in force ships the page of the document without it.
  let switchText := (Encoding.readTex none "u96-switch.tex" (← probe "u96-switch.tex")).text
  let (switchDoc, switchDs) := elabStr switchText
  t "input decoding: a switch of encoding is named and its argument is not ink"
    (!hasStr (pageTextOf fonts switchText) "latin1" && !hasStr (pageTextOf fonts switchText) "utf8" &&
      switchDs.any (fun d => d.kind == .W0104 && d.subject == some "inputencoding:latin1") &&
      switchDs.all (·.kind != .W0301) && !switchDoc.body.isEmpty)
  let same := doc "\\usepackage[utf8]{inputenc}\n" "One. \\inputencoding{utf8}Two.".toUTF8
  let without := doc "\\usepackage[utf8]{inputenc}\n" "One. Two.".toUTF8
  let sameText := (Encoding.readTex none "same.tex" same).text
  t "input decoding: a switch to the encoding in force ships the page of the document without it"
    (pageLines fonts sameText == pageLines fonts (Encoding.readTex none "w.tex" without).text &&
      (elabStr sameText).2.all (·.kind != .W0104))
  -- Two encodings the engine has no table for are one only when spelled
  -- alike: a switch from one to the other is named, never discarded.
  let untabled := doc "\\usepackage[latin2]{inputenc}\n" "One. \\inputencoding{cp1250}Two.".toUTF8
  let untabledDs := (elabStr (Encoding.readTex none "u.tex" untabled).text).2
  t "input decoding: a switch between two encodings with no table is named"
    (untabledDs.any fun d => d.kind == .W0104 && d.subject == some "inputencoding:cp1250")
  -- The built binary: the same readings, end to end, and the other files a
  -- document names.
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"input decoding: CLI builds: {build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode != 0 then return
  let face ← IO.FS.realPath (testFonts ++ "/OpenSans-Regular.ttf")
  IO.FS.withTempDir fun dir => do
    let run (name : String) : IO (UInt32 × Array Lean.Json × String) := do
      let out := dir / (name ++ ".html")
      let r ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := #[(probes / name).toString, "-o", out.toString, "--porcelain", "-v"]
        env := #[("LEANTEX_FONT", some face.toString)] }
      let html := (← (IO.FS.readFile out).toBaseIO).toOption.getD ""
      return (r.exitCode, records r.stdout, html ++ r.stderr)
    for (name, shown, replaced, guessed) in [("u96-bom.tex", "BOM only.", 0, 0),
        ("u96-bom.md", "<h1", 0, 0), ("u96-latin1.tex", "Café crème.", 0, 0),
        ("u96-badbyte.tex", "One bad \uFFFD byte.", 1, 0), ("u96-bib.tex", "Éloïse", 0, 0),
        ("u96-sty.tex", "Crème brûlée.", 0, 0), ("u96-chapters.tex", "Café crème.", 0, 0),
        ("u96-macro.tex", "Café.", 0, 0), ("u96-mixed.tex", "Café crème’s.", 0, 1),
        ("u96-german.tex", "Spaß", 0, 0), ("u96-french.tex", "fin.", 0, 0),
        ("u96-utf16.tex", "UTF-16 Café.", 0, 0), ("u96-math.tex", "sets.", 1, 0),
        ("u96-own.tex", "Crêpe au café", 0, 0), ("u96-own.tex", "Thé vert.", 0, 0),
        ("u96-ownsty.tex", "Tarte à la crème tonight.", 0, 0),
        ("u96-early.tex", "Bientôt.", 0, 0), ("u96-cr.tex", "Another paragraph.", 0, 0),
        ("u96-cr.md", "<h1", 0, 0), ("u96-twice.tex", "Na\uFFFDve text.", 1, 0),
        ("u96-latin2.tex", "Café crème.", 0, 0), ("u96-switch.tex", "Done.", 1, 0),
        ("u96-nulbad.md", "A\uFFFDB", 1, 0), ("u96-odd16.md", "Hi\uFFFD", 1, 0)] do
      let (code, rs, html) ← run name
      t s!"input decoding: {name} ships and shows {shown}"
        (code == 0 && hasStr html shown && (recordCodes rs "E0313").isEmpty &&
          (recordCodes rs "E0312").isEmpty)
      t s!"input decoding: {name} names exactly the bytes it replaced and the bytes it guessed"
        ((recordCodes rs "W0002").size == replaced && (recordCodes rs "W0004").size == guessed)
    let (_, badRs, _) ← run "u96-badbyte.tex"
    t "input decoding: the porcelain record carries every offset"
      (badRs.any fun r => r.getObjValAs? String "code" == .ok "W0002" &&
        (r.getObjVal? "offsets").toOption == some (Lean.Json.arr #[49]))
    -- The pending repair glyph, end to end: a face without U+FFFD names the
    -- loss at the byte the warning names.
    let serifFace ← IO.FS.realPath (testFonts ++ "/SourceSerifPro-Regular.otf")
    let serifRun ← IO.Process.output {
      cmd := ".lake/build/bin/leantex"
      args := #[(probes / "u96-badbyte.tex").toString, "-o", (dir / "serif.pdf").toString,
        "--porcelain"]
      env := #[("LEANTEX_FONT", some serifFace.toString)] }
    let at3x9 (code : String) := (recordCodes (records serifRun.stdout) code).any fun r =>
      r.getObjValAs? Nat "line" == .ok 3 && r.getObjValAs? Nat "col" == .ok 9
    t "input decoding: an undrawable repair is named at its byte, pending a placeholder"
      (serifRun.exitCode == 1 && at3x9 "W0002" && at3x9 "E0405")
    -- The declaration in force is the one execution makes: a load in a
    -- branch never taken declares nothing, whatever the preamble spells.
    let (code, rs, html) ← run "u96-iffalse.tex"
    t "input decoding: a declaration in a skipped branch is not applied"
      (code == 0 && hasStr html "Caf\uFFFD." && (recordCodes rs "W0002").size == 1 &&
        (recordCodes rs "N0025").isEmpty)
    -- One note per declaration, naming every file read under it that it
    -- changed — the included ones, the one that makes it, those read before
    -- it ran, and the bibliography too, an ASCII file reading alike either
    -- way — in the spelling the document wrote, and nothing else at its
    -- span.
    for (name, file, line, files, spelled) in [
        ("u96-chapters.tex", "u96-preamble.tex", 1, ["u96-chapters.tex", "u96-chapter.tex"],
          "\\usepackage"),
        ("u96-bib.tex", "u96-bib.tex", 2, ["u96-latin1.bib"], "\\usepackage"),
        ("u96-sty.tex", "u96-sty.tex", 2, ["u96latin1.sty"], "\\usepackage"),
        ("u96-own.tex", "u96-own-pre.tex", 2, ["u96-own.tex", "u96-own-pre.tex"], "\\usepackage"),
        ("u96-ownsty.tex", "u96ownsty.sty", 2, ["u96ownsty.sty"], "\\RequirePackage"),
        ("u96-early.tex", "u96-early-decl.tex", 1, ["u96-early-defs.tex"], "\\usepackage")] do
      let (_, rs, _) ← run name
      let notes := recordCodes rs "N0025"
      t s!"input decoding: {name} has one declaration note naming every file it read"
        (notes.size == 1 && notes.all fun r =>
          files.all (hasStr (recordMessage r) ·) &&
            (recordMessage r).startsWith s!"'{spelled}[latin1]\{inputenc}'")
      let atDecl := rs.filter fun r =>
        r.getObjValAs? Nat "line" == .ok line && r.getObjValAs? Nat "col" == .ok 1 &&
          (r.getObjValAs? String "file").toOption.any (·.endsWith file)
      t s!"input decoding: {name}'s declaration carries one accounting"
        (atDecl.size == 1 && (recordCodes atDecl "N0025").size == 1)
    -- A file read twice is decoded once, and its bytes named once.
    let (_, twiceRs, _) ← run "u96-twice.tex"
    t "input decoding: a file read twice names its bytes once"
      ((recordCodes twiceRs "W0002").size == 1)
