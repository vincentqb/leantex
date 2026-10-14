module

public import Tests.Support
public import scripts.Privacy

public section

open LeanTex.Core

/-- The privacy matcher over invented terms: list reading, folding, word boundaries, phrases, the
TeX, escape and binary readings, paths and line placement. -/
def privacyMatcherChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit := check ref s!"privacy matcher: {name}" ok
  let list := "# invented terms only\n\n  Zorblax  \ncase:KRYX\nQuintel   Varn\n" ++
    "Haps\u00E9\r\nGr\u00F8tvik\ncase:\n\u0301\n#Plumbix\n"
  let terms := Privacy.parseTerms list
  let m := Privacy.Matcher.ofTerms terms
  let hit (s : String) : Bool := !(m.textLines s).isEmpty
  t "the list keeps its five terms, one of them cased"
    (terms.size == 5 && (terms.filter (·.cased)).size == 1)
  t "a comment line is no term" (!hit "Plumbix" && !hit "#Plumbix")
  t "a plain term ignores case" (hit "ZORBLAX" && hit "a zorblax b" && hit "ZoRbLaX")
  t "a plain term ignores the text's diacritics"
    (hit "Z\u00F6rblax" && hit "Zo\u0308rblax" && hit "Z\u00D6RBLAX")
  t "a term's own diacritics fold"
    (hit "hapse" && hit "HAPS\u00C9" && hit "Hapse\u0301" && hit "Haps\u00E8")
  t "a letter no decomposition reaches is not a diacritic"
    (hit "gr\u00F8tvik" && hit "GR\u00D8TVIK" && !hit "Grotvik")
  t "a match touches no letter or digit of its own word"
    (!hit "Zorblaxes" && !hit "prezorblax" && !hit "Zorblax2" && !hit "2Zorblax" &&
      !hit "\u00E9zorblax" && !hit "zorblax\u00E9" && !hit "\u03C9zorblax" &&
      !hit "ZORBLAXES")
  t "a case change opens and closes a word, as an identifier spells one"
    (hit "preZorblax" && hit "ZorblaxEs" && hit "HTMLZorblax" && hit "fooZorblaxBar" &&
      hit "\u00E9Zorblax" && hit "aKRYX" && hit "KRYXUnit" && !hit "KRYXS" && !hit "4KRYX")
  t "punctuation, symbols and underscores bound a match"
    (hit "Zorblax." && hit "(Zorblax)" && hit "x_Zorblax_y" && hit "\\Zorblax@x" &&
      hit "Zorblax\u2019s" && hit "\u00ABZorblax\u00BB" && hit "Zorblax\u2014" &&
      hit "a/Zorblax/b")
  t "a cased term keeps case"
    (hit "KRYX" && hit "the KRYX unit" && !hit "Kryx" && !hit "kryx" && !hit "KRYXS")
  t "a phrase matches across white space, separators and case, or run together"
    (hit "Quintel Varn" && hit "quintel  varn" && hit "Quintel\nVarn" &&
      hit "Quintel\t\tVarn" && hit "Quintel\u00A0Varn" && hit "QuintelVarn" &&
      hit "quintelvarn" && hit "Quintel-Varn" && hit "quintel_varn" && hit "quintel.varn" &&
      hit "quintel/varn" && hit "% Quintel\n% Varn" && hit "-- Quintel\n  -- Varn" &&
      hit "\"Quintel \" ++ \"Varn\"" && hit "QUINTEL_VARN")
  t "a phrase still keeps its words whole and near"
    (!hit "Quintel Varnish" && !hit "xquintel varn" && !hit "Quintel .......... Varn" &&
      !hit "Quintel x Varn")
  t "a term's own separators and case split it into the same words"
    ((Privacy.parseTerms "fooBarBaz\nG-3XY9\nQRVFern\nqrv_fern").map (·.words.size) == #[3, 2, 2, 2])
  let words := Privacy.Matcher.ofTerms (Privacy.parseTerms "fooBarBaz\nG-3XY9\n")
  let whit (s : String) : Bool := !(words.textLines s).isEmpty
  t "a split term matches each spelling of its words"
    (whit "foo bar baz" && whit "foo-bar-baz" && whit "FooBarBaz" && whit "foobarbaz" &&
      whit "g3xy9" && whit "G_3XY9" && !whit "G-3XY9x" && !whit "foo bar bazooka")
  t "a hit is placed on its 1-based line, each line once"
    (m.textLines "a\nZorblax b Zorblax\nc\nKRYX" == #[2, 4] &&
      m.textLines "\n\n\nzorblax\n" == #[4] && m.textLines "x Quintel\nVarn" == #[1] &&
      m.textLines "" == #[])
  t "TeX accents, letter commands, groups, ties and hyphens are read through"
    (hit "Z\\\"orblax" && hit "Zorbl\\'{a}x" && hit "Zorbl{\\'a}x" && hit "Zor\\-blax" &&
      hit "{Z}orblax" && hit "Zorbla\\c{x}" && hit "H\\'{a}ps\\'e" && hit "Quintel~Varn" &&
      hit "Qu\\'{\\i}ntel Varn" && hit "Gr\\o tvik" && !hit "Zorbl\\'{e}x")
  t "a command whose name runs on into the word is no accent"
    (!hit "\\vzorblax" && !hit "\\czorblax")
  t "an accent symbol reads past blanks before its letter"
    (hit "Z\\\" orblax" && hit "Z\\'  orblax" && hit "Haps\\' e" && hit "Haps\\'\t{e}" &&
      !hit "Zor\\- blax" && !hit "Zor\\/ blax")
  t "Lean escapes and character references are decoded"
    (hit "Zo\\u0308rblax" && hit "Zo\\u{308}rblax" && hit "Z\\x6Frblax" &&
      hit "Zorbl&#97;x" && hit "Zorbl&#x61;x" && hit "Z\\\\\\\"orblax" &&
      hit "Quintel\\nVarn")
  t "named references of Latin-1 and percent-encoding are decoded"
    (hit "Haps&eacute;" && hit "HAPS&Eacute;" && hit "Gr&oslash;tvik" &&
      hit "Haps%C3%A9" && hit "Haps%E9" && hit "Zorbl%61x" && hit "Quintel%20Varn" &&
      !hit "Haps&bogus;" && !hit "Zorbl%6x")
  t "an invisible format character splits no word"
    (hit "Zor\u00ADblax" && hit "Zor\u200Bblax" && hit "\uFEFFZorblax")
  let blob (bs : List UInt8) := m.blobHits ⟨bs.toArray⟩
  let utf16be (s : String) : List UInt8 := s.toList.flatMap fun c => [0, c.toNat.toUInt8]
  let utf16le (s : String) : List UInt8 := s.toList.flatMap fun c => [c.toNat.toUInt8, 0]
  t "binary content is read as lenient UTF-8"
    ((blob ([0, 1, 0xFF] ++ "Zorblax".toUTF8.toList)).binary &&
      !(blob ([0, 1, 0xFF] ++ "Zorblaxes".toUTF8.toList)).binary)
  t "binary content is read with its zero bytes removed, as Latin-1"
    ((blob (utf16be "x Z\u00F6rblax y")).binary &&
      (blob (utf16le "x Z\u00F6rblax y")).binary &&
      (blob (0 :: utf16le "x Z\u00F6rblax y")).binary &&
      !(blob (utf16be "Zorblaxes")).binary)
  let bytes (parts : List (List UInt8)) : ByteArray := ⟨parts.foldl (· ++ ·.toArray) #[]⟩
  let u (s : String) : List UInt8 := s.toUTF8.toList
  let cp := Privacy.Matcher.ofTerms (Privacy.parseTerms "Ko\u0161ar\nHaps\u00E9\n")
  let legacy := bytes [u "x\n", u "Haps", [0xE9], u " y\nKo", [0x9A], u "ar\n"]
  t "a non-UTF-8 line is read as lenient UTF-8 and as Windows-1252"
    (Privacy.segmentReadings legacy ==
        #["x\nHaps\uFFFD y\nKo\uFFFDar\n", "x\nHaps\u00E9 y\nKo\u0161ar\n"] &&
      Privacy.segmentReadings "a\u00E9\n".toUTF8 == #["a\u00E9\n"] &&
      Privacy.segmentReadings (bytes [u "ok \u00E9\n", [0xE9], [0], u "z"]) ==
        #["ok \u00E9\n\uFFFD\x00z", "ok \u00E9\n\u00E9\x00z"])
  t "a legacy-encoded text blob reports its lines in both readings"
    ((cp.blobHits legacy).lines == #[2, 3] && !(cp.blobHits legacy).binary &&
      (m.blobHits (bytes [u "a\n", [0xE9], u " Zorblax\n"])).lines == #[2])
  t "Windows-1252 spells letters where Latin-1 has controls"
    (Privacy.cp1252 ⟨#[0x9A, 0x8A, 0x9E, 0xE9, 0x41]⟩ == #['\u0161', '\u0160', '\u017E', '\u00E9', 'A'] &&
      Privacy.cp1252 ⟨#[0x81, 0x8D]⟩ == #['\u0081', '\u008D'])
  t "a text blob reports its lines, never binary"
    ((blob "x\nZorblax\n".toUTF8.toList).lines == #[2] &&
      !(blob "x\nZorblax\n".toUTF8.toList).binary && !(blob "nothing".toUTF8.toList).any)
  t "a path reads like any text"
    (m.pathHit "docs/zorblax-notes.md" && m.pathHit "Zorblax/x.lean" &&
      m.pathHit "docs/quintel-varn.md" && m.pathHit "src/QuintelVarn.lean" &&
      !m.pathHit "docs/zorblaxes.md")
  -- A raw deflate body is the zlib stream less its two header bytes and four-byte check.
  let zlib (s : String) : List UInt8 := (LeanTex.Core.Flate.deflate s.toUTF8).toList
  let raw (s : String) : List UInt8 :=
    let z := LeanTex.Core.Flate.deflate s.toUTF8
    (z.extract 2 (z.size - 4)).toList
  let be (n : Nat) : List UInt8 := [(n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8,
    (n / 256 % 256).toUInt8, (n % 256).toUInt8]
  let le2 (n : Nat) : List UInt8 := [(n % 256).toUInt8, (n / 256 % 256).toUInt8]
  let pdf (content : List UInt8) (info : String) : ByteArray :=
    bytes [u "%PDF-1.7\n%\u00E2\n1 0 obj\n<< /Filter /FlateDecode >>\nstream\r\n", content,
      u "\nendstream\nendobj\n2 0 obj\n", u info, u "\nendobj\n%%EOF\n"]
  let pdfHit (b : ByteArray) : Bool := (m.blobHits b).binary
  t "a PDF's inflated streams are read"
    (pdfHit (pdf (zlib "BT /F1 9 Tf (Zorblax) Tj ET") "<< >>") &&
      pdfHit (pdf (zlib "<x:xmpmeta><dc:creator>Zorblax</dc:creator></x:xmpmeta>") "<< >>") &&
      !pdfHit (pdf (zlib "BT (Zorblaxes) Tj ET") "<< >>") &&
      !pdfHit (pdf (u "BT (no zlib here) Tj ET") "<< >>"))
  t "a PDF's strings are decoded: kerned arrays run together, escapes and hex read"
    (pdfHit (pdf (zlib "[(Zor) -20 (bl) 15 (ax)] TJ") "<< >>") &&
      !pdfHit (pdf (zlib "[(Zor) -20 (bl)] TJ (ax) Tj") "<< >>") &&
      pdfHit (pdf (zlib "x") "<< /Author (Z\\157rbl\\141x) >>") &&
      pdfHit (pdf (zlib "x") "<< /Author (Zor\\\nblax) >>") &&
      pdfHit (pdf (zlib "x") "<< /Title <FEFF005A006F00720062006C00610078> >>") &&
      pdfHit (pdf (zlib "x") "<< /Title <5A6F72626C 6178> >>") &&
      (cp.blobHits (pdf (zlib "x") "<< /Author (Haps\\351) >>")).binary &&
      !pdfHit (pdf (zlib "x") "<< /Title (Zorbl\\(ax\\)) >>"))
  let pngChunk (ty : String) (data : List UInt8) : List UInt8 :=
    be data.length ++ u ty ++ data ++ [0, 0, 0, 0]
  let png (chunks : List (List UInt8)) : ByteArray :=
    bytes ([[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A],
      pngChunk "IHDR" [0, 0, 0, 1, 0, 0, 0, 1, 8, 0, 0, 0, 0]] ++ chunks ++ [pngChunk "IEND" []])
  t "a PNG's compressed text is inflated"
    ((m.blobHits (png [pngChunk "zTXt" (u "Comment" ++ [0, 0] ++ zlib "by Zorblax")])).binary &&
      (m.blobHits (png [pngChunk "iTXt"
        (u "Author" ++ [0, 1, 0] ++ u "en" ++ [0] ++ [0] ++ zlib "Zorblax")])).binary &&
      !(m.blobHits (png [pngChunk "zTXt" (u "Comment" ++ [0, 0] ++ zlib "by nobody")])).binary)
  let gz (flags : UInt8) (header : List UInt8) (s : String) : ByteArray :=
    bytes [[0x1F, 0x8B, 8, flags, 0, 0, 0, 0, 0, 3], header, raw s, [0, 0, 0, 0, 0, 0, 0, 0]]
  t "a gzip member is inflated past the header fields its flags declare"
    ((m.blobHits (gz 0 [] "notes by Zorblax")).binary &&
      (m.blobHits (gz 8 (u "notes.txt" ++ [0]) "notes by Zorblax")).binary &&
      (m.blobHits (gz 4 (le2 3 ++ [1, 2, 3]) "notes by Zorblax")).binary &&
      !(m.blobHits (gz 8 (u "notes.txt" ++ [0]) "notes by nobody")).binary)
  let member (method : Nat) (name : String) (data : List UInt8) : List UInt8 :=
    [0x50, 0x4B, 0x03, 0x04, 20, 0, 0, 0] ++ le2 method ++ [0, 0, 0, 0, 0, 0, 0, 0] ++
      le2 data.length ++ [0, 0] ++ le2 data.length ++ [0, 0] ++ le2 name.length ++ le2 0 ++
      u name ++ data
  t "zip members are read, stored or deflated, and nested containers too"
    ((m.blobHits (bytes [member 8 "word/document.xml" (raw "<w:t>Zorblax</w:t>")])).binary &&
      (m.blobHits (bytes [member 0 "a.txt" (u "x"), member 0 "b.txt" (u "Zorblax")])).binary &&
      (m.blobHits (bytes [member 0 "inner.gz"
        (gz 0 [] "Zorblax").toList])).binary &&
      !(m.blobHits (bytes [member 8 "word/document.xml" (raw "<w:t>nobody</w:t>")])).binary)
  let empty := Privacy.Matcher.ofTerms #[]
  t "an empty list finds nothing"
    (empty.textLines "Zorblax KRYX" == #[] && !(empty.blobHits ⟨#[0, 90]⟩).any &&
      (Privacy.parseTerms "# only a comment\n\n").isEmpty &&
      empty.redact "Zorblax" == "Zorblax")
  t "the fold reads the canonical decomposition, fully expanded"
    (Nfc.decompose '\u00E9' == #['e', '\u0301'] && Nfc.decompose 'a' == #['a'] &&
      Nfc.decompose '\u01D6' == #['u', '\u0308', '\u0304'] &&
      Nfc.combiningClass '\u0301' == 230 && Nfc.combiningClass 'a' == 0)

/-- The privacy gate over invented git answers: diff headers, per-commit log records, the
citation's places, printed findings and their masking. -/
def privacyGateChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit := check ref s!"privacy gate: {name}" ok
  let m := Privacy.Matcher.ofTerms (Privacy.parseTerms "Zorblax\nQuintel Varn\n")
  let dots := "\u2026"
  t "a quoted path is read back: C escapes, octal bytes as UTF-8"
    (Privacy.unquotePath "\"b/we\\\"ird.txt\"" == "b/we\"ird.txt" &&
      Privacy.unquotePath "\"b/caf\\303\\251.txt\"" == "b/caf\u00E9.txt" &&
      Privacy.unquotePath "\"b/tab\\there.txt\"" == "b/tab\there.txt" &&
      Privacy.unquotePath "b/plain.txt" == "b/plain.txt")
  let diff := "diff --git a/x.md b/x.md\n--- a/x.md\n+++ b/x.md\n@@ -1,0 +2,2 @@\n+one\n+two\n" ++
    "diff --git \"a/we\\\"ird.md\" \"b/we\\\"ird.md\"\nnew file mode 100644\n--- /dev/null\n" ++
    "+++ \"b/we\\\"ird.md\"\n@@ -0,0 +1 @@\n+three\n" ++
    "diff --git a/a b.md b/a b.md\n--- /dev/null\n+++ b/a b.md\t\n@@ -0,0 +1 @@\n+four\n" ++
    "diff --git a/gone.md b/gone.md\n--- a/gone.md\n+++ /dev/null\n@@ -1 +0,0 @@\n-five\n"
  t "added lines keep their file through plain, quoted and spaced headers"
    (Privacy.addedLines diff == #[("x.md", 2, "one"), ("x.md", 3, "two"),
      ("we\"ird.md", 1, "three"), ("a b.md", 1, "four")])
  t "a header without the pinned b/ prefix names no file; its lines are lost"
    (Privacy.addedLines "diff --git x x\n--- x\n+++ x\n@@ -0,0 +1 @@\n+Zorblax\n" == #[])
  t "added lines join into runs by file and consecutive line"
    (Privacy.addedRuns #[("a", 3, "x"), ("a", 4, "y"), ("a", 7, "z"), ("b", 8, "w")] ==
      #[("a", 3, "x\ny"), ("a", 7, "z"), ("b", 8, "w")])
  let shaA := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  let shaB := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
  let leadA := s!"  commit {(shaA.take 12).toString}: "
  let leadB := s!"  commit {(shaB.take 12).toString}: "
  let log := s!"\x00{shaA}\n\ndiff --git a/n.md b/n.md\n--- a/n.md\n+++ b/n.md\n" ++
    "@@ -1,0 +2 @@\n+a Zorblax note\n" ++
    s!"\x00{shaB}\n\ndiff --git a/n.md b/n.md\n--- a/n.md\n+++ b/n.md\n@@ -2 +1,0 @@\n" ++
    "-a Zorblax note\n"
  let patches := Privacy.logPatches log
  t "a patch log splits into its commits, each with its patch"
    (patches.map (·.1) == #[shaA, shaB] &&
      (patches.map fun (_, p) => (Privacy.addedLines p).size) == #[1, 0])
  let records := Privacy.logRecords
    s!"\x00{shaA}\x00\ndocs/zorblax.md\x00ok.md\x00\x00{shaB}\x00\nlater.md\x00"
  t "a -z record log pairs each record with its commit"
    (records == #[(shaA, "docs/zorblax.md"), (shaA, "ok.md"), (shaB, "later.md")])
  t "a numstat row git counted no lines in is a binary path"
    (Privacy.binaryRow "-\t-\tfig\tA.bin" == some "fig\tA.bin" &&
      Privacy.binaryRow "3\t0\tx.md" == none)
  let blobs : Array ((String × String) × ByteArray) :=
    #[((shaB, "fig.bin"), ⟨#[0, 1] ++ "Zorblax".toUTF8.data⟩), ((shaB, "clean.bin"), ⟨#[0, 1, 2]⟩)]
  let found := m.commitFindings patches records blobs
  t "a term one commit adds and a later one removes is found in the first"
    (found.contains s!"{leadA}n.md:2" &&
      !found.any fun f => f.startsWith leadB && (f.splitOn "n.md").length > 1)
  t "a commit's added path and binary content are found, masked"
    (found.contains s!"{leadA}docs/{dots} (a path it adds)" &&
      found.contains s!"{leadB}fig.bin (its binary content)" && found.size == 3)
  let msgs := m.messageFindings s!"{shaA}\nA subject\n\nWhy Zorblax.\n\x00{shaB}\nClean\n"
  t "a message is read line by line, its commit named"
    (msgs == #[s!"{leadA}its message, line 3"])
  let staged := m.addedFindings
    "diff --git a/q.md b/q.md\n--- a/q.md\n+++ b/q.md\n@@ -4,0 +5,2 @@\n+Quintel\n+Varn\n" ""
  t "a phrase wrapped over two added lines is one finding, on the first"
    (staged == #["  q.md:5"])
  t "a path's components that hold a term are masked, and only those"
    (m.maskPath "testdata/zorblax/notes.md" == s!"testdata/{dots}/notes.md" &&
      m.maskPath "a/quintel/varn.txt" == s!"a/{dots}/{dots}" &&
      m.maskPath "a/b/c.txt" == "a/b/c.txt" &&
      m.maskPath "x/Quintel Varn.md" == s!"x/{dots}")
  t "a printed line keeps its other words and masks the ones that hit"
    (m.redact "pre-commit: /srv/Zorblax: a path\nclean" == s!"pre-commit: {dots} a path\nclean" &&
      m.redact "a Quintel  Varn b" == s!"a {dots} {dots} {dots} b")
  let latin := Privacy.Matcher.ofTerms (Privacy.parseTerms "Haps\u00E9\n")
  let legacyLine : ByteArray := ⟨"diff --git a/l.txt b/l.txt\n--- a/l.txt\n+++ b/l.txt\n".toUTF8.data ++
    "@@ -0,0 +1,2 @@\n+ok\n+by Haps".toUTF8.data ++ #[0xE9] ++ "\n".toUTF8.data⟩
  t "a non-UTF-8 added line is read as Windows-1252 too, found once"
    (latin.diffFindings legacyLine "" == #["  l.txt:2"] &&
      latin.diffFindings "diff --git a/u.txt b/u.txt\n--- a/u.txt\n+++ b/u.txt\n@@ -0,0 +1 @@\n+Haps\u00E9\n".toUTF8 ""
        == #["  u.txt:1"])
  let legacyLog : ByteArray := ⟨s!"\x00{shaA}\n\ndiff --git a/l.txt b/l.txt\n--- a/l.txt\n+++ b/l.txt\n".toUTF8.data ++
    "@@ -0,0 +1 @@\n+Haps".toUTF8.data ++ #[0xE9] ++ "\n".toUTF8.data⟩
  t "a commit's added line that is not UTF-8 is found in it, once"
    (latin.commitFindings (Privacy.logPatchesOf legacyLog) #[] #[] == #[s!"{leadA}l.txt:1"])
  let legacyMsg : ByteArray := ⟨s!"{shaA}\nA subject\n\nby Haps".toUTF8.data ++ #[0xE9] ++
    s!"\n\x00{shaB}\nClean\n".toUTF8.data⟩
  t "a message that is not UTF-8 is read as Windows-1252 too"
    (latin.messageFindingsOf legacyMsg == #[s!"{leadA}its message, line 3"])
  t "only a name saying its text is compressed is read as a blob"
    (Privacy.opaqueName "fig/a.PDF" && Privacy.opaqueName "notes.docx" &&
      Privacy.opaqueName "x.tar.gz" && !Privacy.opaqueName "notes.md" &&
      !Privacy.opaqueName "pdf" && Privacy.blobRow "-\t-\tfig.bin" == some "fig.bin" &&
      Privacy.blobRow "4\t0\tdoc.pdf" == some "doc.pdf" && Privacy.blobRow "4\t0\tdoc.md" == none &&
      Privacy.blobRow "4\t0" == none)
  t "findings are read once each, in the order first seen"
    (Privacy.uniq #["b", "a", "b", "c", "a"] == #["b", "a", "c"] && Privacy.uniq #[] == #[])
  let readme := "# Tool\n\n## Install\n\nZorblax\n\n## Cite\n\n```bibtex\n@software{x,\n" ++
    "  author = {Zorblax},\n  title  = {Zorblax},\n  note   = {Zorblax},\n" ++
    "  url    = {https://example.org/zorblax},\n" ++
    "  url    = {https://example.org/zorblax} % Zorblax\n}\n```\n\n" ++
    "```bibtex\n  author = {Zorblax},\n```\n\n```sh\nZorblax\n```\n\n## Licence\n\nZorblax\n"
  let cff := "cff-version: 1.2.0\nmessage: Cite Zorblax.\ntitle: Zorblax\n" ++
    "abstract: A Zorblax tool.\nauthors:\n  - family-names: Zorblax\n    given-names: Zorblax\n" ++
    "    email: zorblax@example.org\n" ++
    "repository-code: https://example.org/zorblax\nurl: https://example.org/zorblax\n" ++
    "references:\n  - authors:\n      - family-names: Zorblax\npreferred-citation:\n" ++
    "  title: Zorblax\n  authors:\n    - family-names: Zorblax\n      given-names: Zorblax\n" ++
    "  notes: Zorblax\n  url: https://example.org/zorblax # Zorblax\n" ++
    "  repository-code: https://example.org/zorblax\n"
  let lns (lead f : String) (ns : List Nat) : List String := ns.map fun n => s!"{lead}{f}:{n}"
  let tree (p text : String) : Array String := m.blobFindings p text.toUTF8 ""
  let cited := tree "CITATION.cff" cff ++ tree "README.md" readme
  t "a term passes on the citation's name and URL lines alone, its other lines refused"
    (cited == (lns "  " "CITATION.cff" [2, 3, 4, 8, 13, 15, 19, 20] ++
      lns "  " "README.md" [5, 12, 13, 15, 20, 24, 29]).toArray)
  t "the citation's text read at any other path is found, docs/guide.md included"
    (tree "docs/guide.md" readme ==
        (lns "  " "docs/guide.md" [5, 11, 12, 13, 14, 15, 20, 24, 29]).toArray &&
      tree "docs/CITATION.cff" cff ==
        (lns "  " "docs/CITATION.cff" [2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 17, 18, 19, 20,
          21]).toArray)
  let block (body : String) : String := "## Cite\n\n```bibtex\n" ++ body ++ "\n```\n"
  t "an author line passes only whole, in the block opening the Cite section"
    (tree "README.md" (block "  author = {Zorblax},") == #[] &&
      tree "README.md" (block "  author = {Quintel Varn},") == #[] &&
      tree "README.md" (block "  author = {Zorblax} and more,") == #["  README.md:4"] &&
      tree "README.md" (block "  author = {Zorblax\n  },") == #["  README.md:4"] &&
      tree "README.md" (block "  author = {Quintel},\nVarn") == #["  README.md:4"])
  t "a block under another heading, after text, unclosed, unlabelled or fenced excuses nothing"
    (tree "README.md" "## Install\n\n```bibtex\n  author = {Zorblax},\n```\n" ==
        #["  README.md:4"] &&
      tree "README.md" "## Cite\n\nText.\n\n```bibtex\n  author = {Zorblax},\n```\n" ==
        #["  README.md:6"] &&
      tree "README.md" "## Cite\n\n```bibtex\n  author = {Zorblax},\n" == #["  README.md:4"] &&
      tree "README.md" "## Cite\n\n```\n  author = {Zorblax},\n```\n" == #["  README.md:4"] &&
      tree "README.md" "```sh\n## Cite\n\n```bibtex\n  author = {Zorblax},\n```\n" ==
        #["  README.md:5"] &&
      tree "README.md" "~~~\n## Cite\n\n```bibtex\n  author = {Zorblax},\n```\n~~~\n" ==
        #["  README.md:5"])
  t "a CR, a tab in YAML's indentation or an earlier line opening HTML excuses nothing"
    (tree "README.md" (block "  author = {x\r```\rZorblax},") == #["  README.md:4"] &&
      tree "CITATION.cff" "authors:\n  - family-names: x\rZorblax: y\n" == #["  CITATION.cff:2"] &&
      tree "CITATION.cff" "authors:\n\t- family-names: Zorblax\n" == #["  CITATION.cff:2"] &&
      tree "README.md" "<details>\n## Cite\n```bibtex\n  author = {Zorblax},\n```\n</details>\n" ==
        #["  README.md:4"] &&
      tree "README.md" "<!--\n## Cite\n\n```bibtex\n  author = {Zorblax},\n```\n-->\n" ==
        #["  README.md:5"])
  t "the block ends where CommonMark closes it"
    (tree "README.md" (block "  author = {Zorblax},\n````\n  author = {Zorblax},") ==
        #["  README.md:6"] &&
      tree "README.md" ("## Cite\n\n```bibtex\n  author = {Zorblax},\n   ```\n" ++
          "  author = {Zorblax},\n") ==
        #["  README.md:6"])
  let plus (text : String) : String :=
    String.join ((text.splitOn "\n").dropLast.map fun l => "+" ++ l ++ "\n")
  let readmeDiff := "diff --git a/README.md b/README.md\n--- a/README.md\n+++ b/README.md\n" ++
    "@@ -0,0 +9,9 @@\n" ++ plus ("```bibtex\n@software{x,\n  author = {Zorblax},\n" ++
      "  title  = {Zorblax},\n  note   = {Zorblax},\n  url    = {https://example.org/zorblax},\n" ++
      "  url    = {https://example.org/zorblax} % Zorblax\n}\n```\n") ++
    "@@ -0,0 +29 @@\n+Zorblax\n"
  let citeDiff := readmeDiff ++
    "diff --git a/CITATION.cff b/CITATION.cff\nnew file mode 100644\n--- /dev/null\n" ++
    "+++ b/CITATION.cff\n@@ -0,0 +1,21 @@\n" ++ plus cff ++
    "diff --git a/docs/guide.md b/docs/guide.md\n--- a/docs/guide.md\n+++ b/docs/guide.md\n" ++
    "@@ -0,0 +3 @@\n+  author = {Zorblax},\n"
  let refused := lns "  " "CITATION.cff" [2, 3, 4, 8, 13, 15, 19, 20]
  let hook := m.diffFindings citeDiff.toUTF8 "" #[("README.md", readme), ("CITATION.cff", cff)]
  t "the hook's scan excuses an added line only by its citation place's staged text"
    (hook == (lns "  " "README.md" [12, 13, 15, 29] ++ refused ++ ["  docs/guide.md:3"]).toArray &&
      m.diffFindings citeDiff.toUTF8 "" == (lns "  " "README.md" [11, 12, 13, 14, 15, 29] ++
        lns "  " "CITATION.cff" [2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 17, 18, 19, 20, 21] ++
        ["  docs/guide.md:3"]).toArray &&
      m.diffFindings citeDiff.toUTF8 ""
          #[("README.md", readme.replace "## Cite" "## Notes"), ("CITATION.cff", cff)] ==
        (lns "  " "README.md" [11, 12, 13, 14, 15, 29] ++ refused ++ ["  docs/guide.md:3"]).toArray)
  let citePatches := #[(shaA, citeDiff), (shaB, readmeDiff)]
  let commits := m.commitFindings citePatches #[] #[]
    #[((shaA, "README.md"), readme), ((shaA, "CITATION.cff"), cff)]
  t "the commit scan excuses a line only by its own commit's text of the citation place"
    (commits == (lns leadA "README.md" [12, 13, 15, 29] ++
        lns leadA "CITATION.cff" [2, 3, 4, 8, 13, 15, 19, 20] ++ lns leadA "docs/guide.md" [3] ++
        lns leadB "README.md" [11, 12, 13, 14, 15, 29]).toArray &&
      Privacy.citedIn citePatches ==
        #[(shaA, "README.md"), (shaA, "CITATION.cff"), (shaB, "README.md")])
  let citeMsgs := m.messageFindings (shaA ++ "\nAdd the citation\n\n" ++ readme) ++
    m.messageFindings (shaA ++ "\n" ++ cff)
  t "a commit message is read whole, the citation's name lines in it included"
    (citeMsgs.contains s!"{leadA}its message, line 13" &&
      citeMsgs.contains s!"{leadA}its message, line 6")
  let printed := found ++ msgs ++ staged ++ cited ++ hook ++ commits ++ citeMsgs ++
    #[m.maskPath "testdata/zorblax/notes.md", m.redact "x Zorblax y"]
  t "no finding and no masked text names a term"
    (printed.all fun f => !m.hits f)
