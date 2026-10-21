module

public import Tests.Support
public import LeanTex.Cli.LeanFactsFile

public section

open LeanTex.Core LeanTex.Cli

/-! A Lean page's documentation cites into the bibliography its module docstring declares: doc-gen4's
bracketed keys as doc-gen4 resolves them, and Pandoc's syntax for the keys the bibliography holds,
never asked of Lean; an inclusion's documentation cites into its document's. -/

namespace Tests.LeanCite

/-- Invented entries, keys `ash2001`, `birch2002` and `roe2020`, placeholder names. -/
def leanBib : String :=
  "@book{ash2001, author = {Ash, Ada}, title = {Alpha Notes}, publisher = {Example Press}, \
year = {2001}}\n@book{birch2002, author = {Birch, Bo and Cole, Cy}, title = {Beta Notes}, \
publisher = {Example Press}, year = {2002}}\n@misc{roe2020, author = {Roe, Sam}, \
title = {Placeholder Text}, year = {2020}}\n"

/-- A Lean page whose module doc is `doc`, under `directive`, read citing into `leanBib`. -/
def page (doc : String) (directive : String := "") : Ir.Doc × Array Diag :=
  leanCiteBuild "F.lean" (directive ++ "/-! " ++ doc ++ " -/\n\ndef x := 1\n") #[("refs.bib", leanBib)]

/-- The reference lists of a body: each one's style and keys. -/
def listsOf (d : Ir.Doc) : Array (Option String × Array String) := Ir.foldBlocks (fun out b =>
  match b with
  | .bibliography _ style items => out.push (style, items.map (·.key))
  | _ => out) (fun out _ => out) #[] d.body

/-- The titles of a body's headings, in order. -/
def headingsOf (d : Ir.Doc) : Array String := Ir.foldBlocks (fun out b =>
  match b with
  | .section _ _ _ h => out.push (Ir.plainText h)
  | _ => out) (fun out _ => out) #[] d.body

/-- The files a body's reference lists name. -/
def listFilesOf (d : Ir.Doc) : Array String := Ir.foldBlocks (fun out b =>
  match b with
  | .bibliography src _ _ => out.push src
  | _ => out) (fun out _ => out) #[] d.body

/-- A document built as the driver builds it from its file: read through the front door,
elaborated, and its bibliography read beside it. -/
def driverBuild (path : String) : IO (Ir.Doc × Array Diag) := do
  let read ← Input.readDocument path (← IO.FS.readBinFile path)
  let prepared := Elab.prepareExecuted path read.executed
  let (doc, diags, spans) := Elab.runPrepared path prepared read.diags (fun _ _ => {})
  let (doc, bibDiags, _) ← Input.resolveBibliography path doc (Bib.FieldDoor.of path prepared).read
    spans.labels spans.bib read.ledger
  return (doc, diags ++ bibDiags)

/-- A world holding files by path, `/work` its working directory, where each of `links` is a path
standing for the real file or folder it names. -/
def linkedWorld (files : List (String × ByteArray)) (links : List (String × String)) :
    (q : World.Ask) → World.Reply q
  | .stat path => match links.lookup path with
    | some real => .ok { kind := .file, size := 0, mtimeSec := 0, mtimeNsec := 0, real }
    | none => factsWorld files (.stat path)
  | .readFile path => factsWorld files (.readFile ((links.lookup path).getD path))
  | q => factsWorld files q

def leanCiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- doc-gen4's rule: a bracket whose text is a key it registers, scanning from `[` to the next `]`.
  for (doc, keys) in [("Cites [ash2001].", ["ash2001"]), ("Collapsed [ash2001][] too.", ["ash2001"]),
      ("A key it lacks [nobody1990] stays.", []), ("Code `[ash2001]` stays.", []),
      ("A link [ash2001](https://example.org) stays a link.", []),
      ("Inside brackets [[ash2001]] it registers nothing.", []),
      ("Once registered [ash2001], inside brackets [[ash2001]] it cites.", ["ash2001", "ash2001"]),
      ("An image ![ash2001] is no citation.", []),
      ("A locator [ash2001](Theorem 2) is no link, so the key cites.", ["ash2001"]),
      ("A label it lacks [Ash (2001)][nobody1990] stays.", [])] do
    let (d, _) := page doc
    t s!"lean cite: {repr doc} cites {repr keys}" (keysOf d == keys)
  -- Pandoc's spelling, for a group holding a key the bibliography holds.
  for (doc, keys) in [("[@roe2020, p. 3] and @birch2002 cite.", ["roe2020", "birch2002"]),
      ("@List.map stays text.", []), ("[@nobody1990] stays.", []),
      ("[@roe2020; @nobody1990] is one group, its unknown key named.", ["roe2020", "nobody1990"]),
      ("@roe2020 [ash2001] are two citations, the bracket no locator.", ["roe2020", "ash2001"])] do
    let (d, _) := page doc
    t s!"lean cite: {repr doc} cites {repr keys}" (keysOf d == keys)
  let (d, ds) := page "A group [@roe2020; @nobody1990] cites."
  t s!"lean cite: a group's key the bibliography lacks shows as '?', named once, spelled as written \
({repr (inkText d.body)})"
    (hasStr (inkText d.body) "A group [Roe20, ?] cites." &&
      (ds.filter (·.kind == .W0351)).map (·.subject) == #[some "nobody1990"] &&
      ds.any fun d => d.kind == .W0351 && (d.help.any (hasStr · "@nobody1990")))
  let (d, ds) := page "Unknown [nobody1990] and @List.map and [@nobody1990] stay."
  t "lean cite: a key the bibliography lacks stays text, named nowhere"
    (hasStr (Ir.blocksText d.body) "[nobody1990]" && hasStr (Ir.blocksText d.body) "@List.map" &&
      !ds.any (·.kind == .W0351) && (listsOf d).isEmpty)
  -- doc-gen4's custom text: the author's words link to the entry, which the list holds.
  let (d, _) := page "We follow [Ash (2001)][ash2001]."
  let html := docHtmlOf d
  t s!"lean cite: custom text is the citation's ink, linked to its entry, which the list holds \
({repr (inkText d.body)})"
    (hasStr (inkText d.body) "We follow Ash (2001)." &&
      hasStr html "href=\"#ref-ash2001\"" && hasStr html ">Ash (2001)</a>" &&
      listsOf d == #[(some "alpha", #["ash2001"])])
  let (d, _) := page "The key as its own text [ash2001][ash2001] shows the label."
  t s!"lean cite: custom text that is the key itself shows the label, as doc-gen4 shows its tag \
({repr (inkText d.body)})"
    (keysOf d == ["ash2001"] && hasStr (inkText d.body) "own text [Ash01] shows")
  let (d, _) := page "Custom text [see [x](https://example.org)][ash2001] holding a link."
  t s!"lean cite: custom text holding a link is no reference, the link kept and the key cited \
({repr (inkText d.body)})"
    (keysOf d == ["ash2001"] && hasStr (docHtmlOf d) "href=\"https://example.org\"" &&
      hasStr (inkText d.body) "[see x][Ash01] holding")
  let (d, _) := page "Cites [birch2002]; then [see [birch2002] too][ash2001]."
  t s!"lean cite: custom text holding a citation is no reference, each key cited \
({repr (inkText d.body)})"
    (keysOf d == ["birch2002", "birch2002", "ash2001"] &&
      hasStr (inkText d.body) "[see [BC02] too][Ash01]")
  let (d, _) := page "Cites [ash2001]; its source is [the [ash2001] book](https://example.org)."
  t s!"lean cite: a citation inside link text makes that text literal, as an inner link does \
({repr (inkText d.body)})"
    (keysOf d == ["ash2001", "ash2001"] && !hasStr (docHtmlOf d) "href=\"https://example.org\"" &&
      hasStr (inkText d.body) "[the [Ash01] book](https://example.org)")
  -- A quote right after an inline element reads as Pandoc's smart quotes read it: after emphasis it
  -- closes; after a citation, code or a link a single one opens where a later one pairs with it, and
  -- a double one opens before a word.
  let (d, _) := page "'Quoted' first, \"as in [ash2001]\" and [ash2001]'s view, *x*'s and `x`'s."
  let html := docHtmlOf d
  t "lean cite: a quote after an inline element closes, a possessive's apostrophe too"
    (hasStr html "</a>]” and" && hasStr html "</a>]’s view" && hasStr html "<em>x</em>’s" &&
      hasStr html "<code>x</code>’s." && hasStr html "‘Quoted’ first")
  let (d, _) := page ("Then `c`'quoted' and [l](https://example.org)'quoted', `c`\"quoted\", " ++
    "*x*\"y\" and [ash2001]'quoted'.")
  let html := docHtmlOf d
  t "lean cite: a quote after code, a link or a citation opens where Pandoc's opens"
    (hasStr html "<code>c</code>‘quoted’ and" && hasStr html "</a>‘quoted’," &&
      hasStr html "<code>c</code>“quoted”" && hasStr html "<em>x</em>”y”" &&
      hasStr html "</a>]‘quoted’.")
  -- One list, in alpha's labels as doc-gen4 tags its references, only where something is cited.
  let (d, _) := page "Cites [birch2002] and [ash2001], and [ash2001] again."
  t s!"lean cite: the page ends with one list in alpha's order ({repr (listsOf d)})"
    (listsOf d == #[(some "alpha", #["ash2001", "birch2002"])] &&
      (match d.body.toList.reverse with
        | .bibliography .. :: .section _ _ _ h :: _ => Ir.plainText h == "References"
        | _ => false))
  t "lean cite: a citation sets alpha's label, as doc-gen4 shows its tag"
    (hasStr (Ir.blocksText d.body) "Cites [BC02] and [Ash01], and [Ash01] again.")
  let html := docHtmlOf d
  t "lean cite: the web page links each citation to its entry"
    (hasStr html "href=\"#ref-ash2001\"" && hasStr html "<li id=\"ref-ash2001\"")
  let (d, _) := page "Cites nothing."
  t "lean cite: a page citing nothing sets no list" (listsOf d).isEmpty
  let (d, _) := page "# Notes\n\nCites [ash2001].\n\n## References\n\n* [ash2001]\n"
  t s!"lean cite: the list stands under the documentation's own References heading \
({repr (headingsOf d)})"
    (headingsOf d == #["Notes", "References"] && listsOf d == #[(some "alpha", #["ash2001"])] &&
      (match d.body.toList.reverse with
        | .verbatim .. :: .bibliography .. :: _ => true
        | _ => false))
  let (d, _) := page ("# Notes\n\nCites [ash2001].\n\n## References\n\n* [ash2001]\n\n" ++
    "## Tags\n\nplaceholder\n")
  let listAt := d.body.findIdx? (· matches .bibliography ..)
  let tagsAt := d.body.findIdx? fun b => match b with
    | .section _ _ _ h => Ir.plainText h == "Tags"
    | _ => false
  t s!"lean cite: the list closes the References section, before the next heading of its rank \
({repr listAt}, {repr tagsAt})"
    (headingsOf d == #["Notes", "References", "Tags"] &&
      (match listAt, tagsAt with
        | some l, some g => l < g
        | _, _ => false))
  let (d, _) := page "Cites [ash2001]." "-- leantex: biblio-style = plain\n"
  t s!"lean cite: a directive's biblio-style sets the page's list ({repr (inkText d.body)})"
    (listsOf d == #[(some "plain", #["ash2001"])] && hasStr (inkText d.body) "Cites [1].")
  -- No bibliography, a Python docstring, and an inclusion that sets its documentation as code.
  let (d, _) := elabCode "F.lean" "/-! Cites [ash2001] and [@roe2020]. -/\n\ndef x := 1\n"
  t "lean cite: a page with no bibliography reads no citation"
    ((citesOf d).isEmpty && hasStr (Ir.blocksText d.body) "[ash2001]")
  let refs : Code.Refs := { path := "refs.bib", keys := (Bib.keysOf leanBib).foldl (·.insert ·) {} }
  let (raws, _) := Surface.readCode .python "m.py" "\"\"\"Cites [ash2001] and [@roe2020].\"\"\"\n"
    none {} (some refs)
  let (d, _) := Elab.runRaws "m.py" raws #[]
  t "lean cite: a Python docstring cites as a Lean page's documentation does" !(citesOf d).isEmpty
  let (_, ds) := Surface.readCode .python "m.py" "# leantex: bibliography = refs.bib\nprint(1)\n"
    none {} (some refs)
  t "lean cite: a Python directive's bibliography is refused, its help the module docstring's line"
    (ds.any fun d => d.subject == some "code:bibliography" &&
      d.help.any (hasStr · "Bibliography: [refs.bib](refs.bib)"))
  -- A statement standing without its code sets its documentation, which cites as the page's.
  let heldFacts := "{\"leantex-lean-export\":3,\"lean\":\"4.34.1\",\"errors\":0}\n" ++
    "{\"name\":\"holds\",\"module\":\"F\",\"kind\":\"theorem\",\"range\":[6,0,7,31]," ++
    "\"head\":[6,0],\"signature\":[7,14,7,20],\"proof\":[7,21,7,31],\"proved\":true," ++
    "\"prop\":true,\"doc\":null,\"type\":[[\"const\",\"True\"]]}\n" ++
    "{\"const\":\"True\",\"binders\":\"\"}\n{\"leantex-lean-export-end\":1}\n"
  let (held, heldDs) := leanCiteBuild "F.lean"
    ("-- leantex: show = math\n/-! # Held\n\nBibliography: [refs.bib](refs.bib) -/\n\n" ++
      "/-- Holds, as [ash2001] shows. -/\ntheorem holds : True := trivial\n")
    #[("refs.bib", leanBib)] (LeanFacts.decode heldFacts).toOption
  t s!"lean cite: a statement's documentation set above it cites into the page's bibliography, its list set ({repr (inkText held.body)})"
    (keysOf held == ["ash2001"] && (listsOf held).any (·.2.contains "ash2001") &&
      !heldDs.any (·.kind == .W0449) && hasStr (inkText held.body) "Holds, as")
  let (_, ds) := elabCode "F.lean" "-- leantex: show = docs\n/-! Notes. -/\ndef x := 1\n"
  t "lean cite: a page has no docs view, which it names"
    (ds.any (·.subject == some "code:show:docs"))
  let inclusion (options : String) (refs : Option Code.Refs := none) : Array Parse.Raw × Array Diag :=
    Code.includeLean "F.lean" "/-! Cites [ash2001]. -/\ndef x := 1\n"
      (Code.showingOfEntries .lean (Decl.splitEntries options) (alone := true)) none {}
      ⟨"d.tex", {}⟩ "`\\inputlean`" refs
  t "lean cite: an inclusion's bibliography with no docs view is named, its documentation code"
    ((inclusion "bibliography = refs.bib").2.any (·.subject == some "code:bibliography"))
  t "lean cite: an inclusion's biblio-style is named, its citations set in the document's"
    ((inclusion "show = docs, biblio-style = plain" (some refs)).2.any
      (·.subject == some "code:biblio-style"))
  t "lean cite: a docs view beside another view is named, the docs view set"
    ((inclusion "show = {docs, math}" (some refs)).2.any fun d =>
      d.subject == some "code:show" && hasStr (d.detail.getD "") "`docs` with another view")
  t "lean cite: a phrase under the docs view, which sets no statement, is named"
    ((inclusion "show = docs, phrase.x = \"an x\"" (some refs)).2.any
      (·.subject == some "code:phrase:x"))
  let (raws, ds) := inclusion "show = docs" (some refs)
  let (d, _) := Elab.runRaws "d.tex" raws #[]
  t s!"lean cite: a docs view sets the documentation as prose, its brackets cited, the code a \
listing ({repr (ds.map (·.message))})"
    (keysOf d == ["ash2001"] && (listsOf d).isEmpty && ds.isEmpty &&
      d.body.any (· matches .verbatim ..))
  -- The twins of a page and of a document including its documentation read back to their text.
  for n in ["lean-cite", "lean-cite-include"] do
    let (d, _) ← goldenDoc n
    let (back, ds) := mdBibBuild (MarkdownDoc.emit d) (← corpusBibs d)
    t s!"lean cite: {n}'s twin, rebuilt with its bibliography, sets its ink"
      (!(listsOf d).isEmpty && inkFlat back.body == inkFlat d.body && !ds.any (·.kind == .W0351))
  -- The declaration: one line of a module docstring linking each `.bib` file, which sets nothing.
  for (line, want) in [("Bibliography: [refs.bib](refs.bib)", some #["refs.bib"]),
      ("bibliography: [a](../a.bib), [b](<b c/d.bib>)", some #["../a.bib", "b c/d.bib"]),
      ("Bibliography: [a](a.bib), [b](sub/b.bib)", some #["a.bib", "sub/b.bib"]),
      ("Bibliography: [notes](notes.md)", none), ("Bibliography:", none),
      ("Bibliography: see [refs.bib](refs.bib)", none), ("The bibliography: [a](a.bib)", none),
      ("Bibliography: [r](https://example.org/r.bib)", none),
      ("Bibliography: [r](my%20refs.bib)", some #["my refs.bib"]),
      ("Bibliography: [r](<my%20refs.bib>)", some #["my refs.bib"]), ("Bibliography: [r](r%FF.bib)", none)] do
    t s!"lean cite: {repr line} declares {repr want}" (Code.bibLine? line == want)
  let declaring := "/-! Cites [ash2001].\n\nBibliography: [refs.bib](refs.bib)\n\n```\n\
Bibliography: [fenced.bib](fenced.bib)\n```\n-/\n\n/-- Bibliography: [decl.bib](decl.bib) -/\n\
def x := 1\n"
  t s!"lean cite: a module docstring's line declares, not one in a fence or a declaration's docstring, \
as a Python module docstring's does \
({repr (Code.declaredBibs .lean declaring)})"
    (Code.declaredBibs .lean declaring == #[⟨"refs.bib", 3⟩] &&
      Code.declaredBibs .python "\"\"\"Bibliography: [r.bib](r.bib)\"\"\"\n" == #[⟨"r.bib", 1⟩])
  let fences := "/-! Cites.\n\n````\n```\nBibliography: [a.bib](a.bib)\n````\n\n~~~\n\
Bibliography: [b.bib](b.bib)\n```\n~~~\nBibliography: [c.bib](c.bib) -/\ndef x := 1\n"
  t s!"lean cite: a fence closes only on its own mark at its length or longer \
({repr (Code.declaredBibs .lean fences)})"
    (Code.declaredBibs .lean fences == #[⟨"c.bib", 12⟩])
  let (d, _) := page "Cites [ash2001].\n\nBibliography: [refs.bib](refs.bib)"
  let html := docHtmlOf d
  let twin := MarkdownDoc.emit d
  t "lean cite: the declaration sets no ink on the web page or in the twin"
    (([html, twin].all fun shown => !hasStr shown "Bibliography:" && !hasStr shown "(refs.bib)") &&
      hasStr html "Cites [" && listsOf d == #[(some "alpha", #["ash2001"])])
  let (d, _) := page "Cites [ash2001] mid-paragraph,\nBibliography: [refs.bib](refs.bib)\nand on."
  t "lean cite: a declaration inside a paragraph leaves the paragraph whole"
    (hasStr (MarkdownDoc.emit d) "mid-paragraph, and on.")
  for bad in ["Bibliography: refs.bib", "Bibliography: [r](refs.bibtex)",
      "Bibliography: [r](refs.bib) more text", "Bibliography: [r](https://example.org/r.bib)"] do
    let (d, ds) := page s!"Cites [ash2001].\n\n{bad}"
    t s!"lean cite: {repr bad} declares nothing, named at its line and set as written"
      ((ds.filter (·.subject == some "code:bibliography-line")).map
          (·.span.map fun sp => (sp.pos.line, sp.pos.col)) == #[some (3, 1)] &&
        hasStr (MarkdownDoc.emit d) "Bibliography:")
  let (d, ds) := page "Notes.\n-/\n\n/-- A value.\n\nBibliography: [refs.bib](refs.bib) -/\ndef y := 2\n/-! More."
  t "lean cite: a declaration docstring's bibliography line declares nothing, named and set as written"
    ((ds.filter (·.subject == some "code:bibliography-line")).map (·.span.map (·.pos.line)) ==
      #[some 6] && hasStr (MarkdownDoc.emit d) "Bibliography:")
  let (_, ds) := elabCode "F.lean" "-- leantex: bibliography = refs.bib\n/-! Notes. -/\ndef x := 1\n"
  t "lean cite: a directive's bibliography is refused, its help the docstring's line"
    (ds.any fun d => d.subject == some "code:bibliography" &&
      d.help.any (hasStr · "Bibliography: [refs.bib](refs.bib)"))
  -- Where the bibliography is read: the files the module docstring declares, beside the Lean file.
  let bibBytes := leanBib.toUTF8
  let lakefile := ("/work/lakefile.toml", "name = \"t\"".toUTF8)
  let standard := ("/work/docs/references.bib", bibBytes)
  let declared := (LeanFactsFile.bibFor "Sub/F.lean" #[("refs.bib", 3), ("../docs/references.bib", 4)]).run
    (factsWorld [lakefile, ("/work/Sub/refs.bib", bibBytes), standard])
  t s!"lean cite: declared bibliographies are read beside the Lean file, each named from it \
({repr (declared.1.map (·.name))})"
    (declared.1.map (·.name) == #["refs.bib", "../docs/references.bib"] &&
      declared.1.map (·.path) == #["/work/Sub/refs.bib", "/work/docs/references.bib"] &&
      declared.2.isEmpty)
  let absent := (LeanFactsFile.bibFor "Sub/F.lean" #[("refs.bib", 3)]).run (factsWorld [lakefile])
  t "lean cite: a declared bibliography that is not there is named at its line"
    (absent.1.isEmpty && absent.2.map (·.kind) == #[.W0503] &&
      absent.2.map (·.span.map (·.pos.line)) == #[some 3])
  let none0 := (LeanFactsFile.bibFor "Sub/F.lean" #[]).run (factsWorld [lakefile, standard])
  t "lean cite: a file declaring no bibliography reads none, its project's docs/references.bib unread"
    (none0.1.isEmpty && none0.2.isEmpty)
  let docGen := (LeanFactsFile.projectBib "Sub/F.lean" Ir.CodeLang.lean.row.project).run
    (factsWorld [lakefile, ("/work/Sub/F.lean", "".toUTF8), standard])
  t s!"lean cite: the bibliography doc-gen4 reads is its project's docs/references.bib, named from the \
file ({repr (docGen.map (·.name))})"
    (docGen.map (·.name) == some "../docs/references.bib" &&
      ((LeanFactsFile.projectBib "Sub/F.lean" Ir.CodeLang.lean.row.project).run
        (factsWorld [lakefile])).isNone)
  let linked := (LeanFactsFile.bibFor "other/F.lean" #[("../docs/references.bib", 1)]).run
    (linkedWorld [("/work/proj/lakefile.toml", "".toUTF8), ("/work/proj/Sub/F.lean", "".toUTF8),
      ("/work/proj/docs/references.bib", bibBytes)] [("/work/other/F.lean", "/work/proj/Sub/F.lean")])
  t s!"lean cite: a linked page's declaration is read beside its real file, named from the page as \
given ({repr (linked.1.map (·.name))})"
    (linked.1.map (·.name) == #["../proj/docs/references.bib"] && linked.2.isEmpty)
  let latin1 : ByteArray := "@misc{caf".toUTF8 ++ ⟨#[0xE9]⟩ ++
    ", title = {T}}\n@misc{ash2001, title = {T}}\n".toUTF8
  let latin := (LeanFactsFile.bibFor "Sub/F.lean" #[("../docs/references.bib", 1)]).run
    (factsWorld [lakefile, ("/work/docs/references.bib", latin1)])
  let keysRead (f : LeanFactsFile.BibFile) := Bib.keysOf (Encoding.readMarkdown f.path f.bytes).text
  t s!"lean cite: a bibliography that is no UTF-8 still gives its keys, read as its list reads them \
({repr (latin.1.map keysRead)})"
    (latin.1.any fun f => (keysRead f).contains "ash2001" && !(keysRead f).contains "café")
  let linkedFolder := (LeanFactsFile.bibFor "projlink/Sub/F.lean" #[("../docs/references.bib", 1)]).run
    (linkedWorld [("/work/src/proj/lakefile.toml", "".toUTF8), ("/work/src/proj/Sub/F.lean", "".toUTF8),
      ("/work/src/proj/docs/references.bib", bibBytes)]
      [("/work/projlink/Sub/F.lean", "/work/src/proj/Sub/F.lean"),
        ("/work/projlink/Sub", "/work/src/proj/Sub")])
  t s!"lean cite: a page in a linked folder is named from where that folder really stands \
({repr (linkedFolder.1.map (·.name))})"
    (linkedFolder.1.map (·.name) == #["../docs/references.bib"] && linkedFolder.2.isEmpty)
  let besideDoc := (LeanFactsFile.bibFor "proj/Sub/F.lean" #[("../docs/references.bib", 1)]
    (base := some ".")).run
    (factsWorld [("/work/proj/lakefile.toml", "".toUTF8), ("/work/proj/Sub/F.lean", "".toUTF8),
      ("/work/proj/docs/references.bib", bibBytes)])
  t s!"lean cite: an inclusion's bibliography is named from its document's folder \
({repr (besideDoc.1.map (·.name))})"
    (besideDoc.1.map (·.name) == #["proj/docs/references.bib"])
  -- The driver: a page reads the bibliography it declares, and an inclusion's joins its document's.
  IO.FS.withTempDir fun tmp => do
    let proj := tmp / "proj"
    IO.FS.createDirAll (proj / "docs")
    IO.FS.createDirAll (proj / "Sub")
    IO.FS.writeFile (proj / "lakefile.toml") "name = \"t\"\n"
    IO.FS.writeFile (proj / "docs/references.bib") leanBib
    IO.FS.writeFile (proj / "Sub/F.lean")
      "/-! Cites [ash2001] and [roe2020].\n\nBibliography: [references.bib](../docs/references.bib) -/\n\
\ndef x := 1\n"
    let (d, ds) ← driverBuild (proj / "Sub/F.lean").toString
    t s!"lean cite: through the driver a page cites into the bibliography its docstring declares \
({repr (listFilesOf d)}, {repr (ds.map (·.message))})"
      (listFilesOf d == #["../docs/references.bib"] &&
        listsOf d == #[(some "alpha", #["ash2001", "roe2020"])] &&
        !ds.any (·.severity == .error) && !hasStr (inkText d.body) "?")
    let read ← Input.readDocument (proj / "Sub/F.lean").toString
      (← IO.FS.readBinFile (proj / "Sub/F.lean"))
    t "lean cite: the bibliography a page reads is among the files its build reads"
      (read.reads.any (·.endsWith "/proj/docs/references.bib"))
    IO.FS.writeFile (tmp / "own.bib")
      "@misc{roe2020, author = {Roe, Sam}, title = {The Document's Own Text}, year = {2020}}\n"
    IO.FS.writeFile (tmp / "doc.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{proj/Sub/F.lean}\n\\bibliographystyle{plain}\n\\bibliography{own}\n\
\\end{document}\n")
    let (d, ds) ← driverBuild (tmp / "doc.tex").toString
    t s!"lean cite: an inclusion's bibliography joins its document's list, in the document's style \
({repr (listFilesOf d)}, {repr (listsOf d)}, {repr (ds.map (·.message))})"
      (listFilesOf d == #["own,proj/docs/references.bib"] &&
        listsOf d == #[(some "plain", #["ash2001", "roe2020"])] &&
        !ds.any (·.severity == .error) && hasStr (inkText d.body) "Cites [1] and [2].")
    t "lean cite: a key both hold is set from the document's own file"
      (hasStr (inkText d.body) "own text" && !hasStr (inkText d.body) "Placeholder text")
    IO.FS.writeFile (tmp / "same.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{proj/Sub/F.lean}\n\\bibliography{proj/docs/references}\n\\end{document}\n")
    let (d, _) ← driverBuild (tmp / "same.tex").toString
    t s!"lean cite: an inclusion's file the document already names joins nothing \
({repr (listFilesOf d)})"
      (listFilesOf d == #["proj/docs/references"])
    IO.FS.writeFile (tmp / "note.md") "---\nbibliography: own.bib\n---\n\n# A note\n\n\
The text cites nothing itself.\n\n::: {.lean file=\"proj/Sub/F.lean\" show=\"docs\"}\n:::\n"
    let (d, ds) ← driverBuild (tmp / "note.md").toString
    t s!"lean cite: a markdown document's Lean division cites into its list, though its own text \
cites nothing ({repr (listFilesOf d)}, {repr (listsOf d)}, {repr (ds.map (·.message))})"
      (listFilesOf d == #["own.bib,proj/docs/references.bib"] &&
        listsOf d == #[(some "plainnat", #["ash2001", "roe2020"])] && !ds.any (·.kind == .W0351))
    IO.FS.writeFile (tmp / "bare.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{proj/Sub/F.lean}\n\\end{document}\n")
    let (d, ds) ← driverBuild (tmp / "bare.tex").toString
    t s!"lean cite: a document with no list leaves the inclusion's citations '?', named \
({repr (inkText d.body)})"
      ((listsOf d).isEmpty && hasStr (inkText d.body) "Cites [?] and [?]." &&
        ds.any (·.kind == .W0351))
    IO.FS.writeFile (proj / "Sub/Gone.lean")
      "/-! Cites [ash2001].\n\nBibliography: [gone.bib](gone.bib) -/\n\ndef x := 1\n"
    IO.FS.writeFile (tmp / "missing.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{proj/Sub/Gone.lean}\n\\end{document}\n")
    let (_, ds) ← driverBuild (tmp / "missing.tex").toString
    t s!"lean cite: an inclusion's declared bibliography that is not there is named at its line \
({repr (ds.map (·.message))})"
      (ds.any fun d => d.kind == .W0503 && d.span.any (fun sp => sp.file.endsWith "Gone.lean" &&
        sp.pos.line == 3) && !hasStr d.message "reference list" && !hasStr (d.help.getD "") "/./")
    IO.FS.writeFile (tmp / "twice.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{proj/Sub/Gone.lean}\n\\inputlean[show = docs]{proj/Sub/Gone.lean}\n\
\\end{document}\n")
    let (_, ds) ← driverBuild (tmp / "twice.tex").toString
    t s!"lean cite: a Lean file included twice names its bibliography once \
({repr ((ds.filter (·.kind == .W0503)).map (·.message))})"
      ((ds.filter (·.kind == .W0503)).size == 1)
    IO.FS.writeFile (tmp / "option.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs, bibliography = own.bib]{proj/Sub/F.lean}\n\\bibliography{own}\n\
\\end{document}\n")
    let (d, ds) ← driverBuild (tmp / "option.tex").toString
    t s!"lean cite: an inclusion's bibliography option is refused, the Lean file's own declaration read \
({repr (listFilesOf d)})"
      (ds.any (fun d => d.subject == some "code:bibliography" && d.kind == .W0110) &&
        listFilesOf d == #["own,proj/docs/references.bib"])
    -- A file citing what doc-gen4 would resolve with no declaration is named once, nothing resolved.
    IO.FS.writeFile (proj / "Sub/H.lean")
      "/-! Cites [ash2001] and [roe2020]. -/\n\n/-- Again [ash2001]. -/\ndef x := 1\n"
    let (d, ds) ← driverBuild (proj / "Sub/H.lean").toString
    let named := ds.filter (·.kind == .W0503)
    t s!"lean cite: a page citing its project's docs/references.bib undeclared is named once, its \
citations as written ({repr (named.map (·.message))}, {repr (inkText d.body)})"
      (named.size == 1 && named.all (fun d => d.detail == some "ash2001, roe2020" &&
          d.help.any (hasStr · "`Bibliography: [references.bib](../docs/references.bib)`")) &&
        (listsOf d).isEmpty && hasStr (inkText d.body) "Cites [ash2001] and [roe2020].")
    IO.FS.writeFile (proj / "Sub/Late.lean")
      "-- see [ash2001x] and @ash2001\n\ndef y := 2\n\n/-- Cites [ash2001]. -/\ndef x := 1\n"
    let (_, ds) ← driverBuild (proj / "Sub/Late.lean").toString
    t s!"lean cite: an undeclared citation is named where the documentation cites, not where code \
or a comment spells the key ({repr ((ds.filter (·.kind == .W0503)).map (·.span))})"
      ((ds.filter (·.kind == .W0503)).map (·.span.map (·.pos.line)) == #[some 5])
    IO.FS.writeFile (proj / "Sub/Quiet.lean") "/-! Cites nothing. -/\n\ndef x := 1\n"
    let (_, ds) ← driverBuild (proj / "Sub/Quiet.lean").toString
    t "lean cite: a page citing nothing, declaring nothing, is named nowhere"
      (!ds.any (·.kind == .W0503))
    IO.FS.writeFile (tmp / "undeclared.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{proj/Sub/H.lean}\n\\bibliography{own}\n\\end{document}\n")
    let (d, ds) ← driverBuild (tmp / "undeclared.tex").toString
    t s!"lean cite: an undeclared inclusion is named once and joins no file ({repr (listFilesOf d)})"
      ((ds.filter (·.kind == .W0503)).size == 1 && listFilesOf d == #["own"])
    IO.FS.writeFile (tmp / "bl.tex") ("\\documentclass{article}\n\\usepackage{biblatex}\n\
\\addbibresource{own.bib}\n\\begin{document}\n\\inputlean[show = docs]{proj/Sub/F.lean}\n\
\\printbibliography\n\\end{document}\n")
    let (d, ds) ← driverBuild (tmp / "bl.tex").toString
    t s!"lean cite: a biblatex document's list joins an inclusion's bibliography after its own \
({repr (listFilesOf d)}, {repr (listsOf d)}, {repr (ds.map (·.message))})"
      ((listsOf d).any (fun (_, ks) => ks.contains "ash2001" && ks.contains "roe2020") &&
        !ds.any (·.kind == .W0351) && hasStr (inkText d.body).toLower "own text")
    IO.FS.writeFile (proj / "Sub/G.lean") "/-! Cites nothing. -/\n\ndef y := 2\n"
    IO.FS.writeFile (tmp / "star.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{proj/Sub/G.lean}\n\\nocite{*}\n\\bibliography{own}\n\\end{document}\n")
    let (d, _) ← driverBuild (tmp / "star.tex").toString
    t s!"lean cite: an inclusion citing nothing joins no file, so \\nocite\{*} lists the document's own \
({repr (listFilesOf d)}, {repr (listsOf d)})"
      (listFilesOf d == #["own"] && listsOf d == #[(none, #["roe2020"])])
    let comma := tmp / "pro,j"
    IO.FS.createDirAll (comma / "docs")
    IO.FS.writeFile (comma / "lakefile.toml") "name = \"t\"\n"
    IO.FS.writeFile (comma / "docs/references.bib") leanBib
    IO.FS.writeFile (comma / "F.lean")
      "/-! Cites [ash2001].\n\nBibliography: [references.bib](docs/references.bib) -/\n\ndef x := 1\n"
    IO.FS.writeFile (tmp / "comma.tex") ("\\documentclass{article}\n\\begin{document}\n\
\\inputlean[show = docs]{pro,j/F.lean}\n\\bibliography{own}\n\\end{document}\n")
    let (d, ds) ← driverBuild (tmp / "comma.tex").toString
    t s!"lean cite: a bibliography whose name holds a comma, which a list cannot name, is named \
({repr (ds.map (·.message))})"
      (ds.any (fun d => d.kind == .W0110 && d.subject == some "code:bibliography-comma") &&
        listFilesOf d == #["own"] && hasStr (inkText d.body) "Cites [ash2001].")

/-- The footnotes a body sets, each with whether it holds a citation. -/
def footnotesOf (d : Ir.Doc) : Array Bool :=
  Ir.foldBlocks (fun out _ => out) (fun out x => match x with
    | .footnote _ body => out.push (body.any fun y => y matches .cite .. || y matches .cited ..)
    | _ => out) #[] d.body

/-- A citation sets its label in brackets and a reference list, never a footnote: in markdown, in a
Lean file's documentation and under biblatex's bracketed commands, the twin writing no note; only
biblatex's foot-commands in a TeX document set it in a footnote, as LaTeX does. -/
def citeFootnoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (md, _) := mdBibBuild (worksMeta ++ "Text [@a], @a says, [-@b; see @roe2020, p. 2].\n")
    #[("works.bib", worksBib)]
  t s!"cite notes: a markdown document's citations set no footnote ({footnotesOf md})"
    ((footnotesOf md).isEmpty && !(citesOf md).isEmpty && !hasStr (MarkdownDoc.emit md) "[^")
  let (lean, _) := leanCiteBuild "F.lean" "/-! Cites [a] and [@b, p. 3]. -/\n\ndef x := 1\n"
    #[("works.bib", worksBib)]
  t s!"cite notes: a Lean file's documentation sets no footnote ({footnotesOf lean})"
    ((footnotesOf lean).isEmpty && !(citesOf lean).isEmpty && !hasStr (MarkdownDoc.emit lean) "[^")
  let tex (opts call : String) : Ir.Doc := (bibResolve s!"\\documentclass\{article}\n\
\\usepackage[{opts}]\{biblatex}\n\\addbibresource\{refs.bib}\n\\begin\{document}\n\
Text {call} end.\n\n\\printbibliography\n\\end\{document}\n"
    #[("refs", natbibBib), ("refs.bib", natbibBib)]).1
  for opts in ["style=numeric", "style=authoryear"] do
    for call in ["\\parencite{alpha2019}", "\\autocite{alpha2019}", "\\textcite{alpha2019}",
        "\\cite{alpha2019}", "\\parencites{alpha2019}{delta2021}"] do
      let d := tex opts call
      t s!"cite notes: biblatex {opts} {call} sets no footnote ({footnotesOf d})"
        ((footnotesOf d).isEmpty && !(citesOf d).isEmpty)
    for call in ["\\footcite{alpha2019}", "\\smartcite{alpha2019}",
        "\\footcites{alpha2019}{delta2021}"] do
      let d := tex opts call
      t s!"cite notes: biblatex {opts} {call} sets its citation in a footnote, as LaTeX does \
({footnotesOf d})" (footnotesOf d == #[true])

/-- leantex's own documentation: each module citing a key of `docs/references.bib` declares that file
in its module docstring and builds through its declaration as the driver builds it, every key it
cites in its reference list, and every entry is cited somewhere. -/
def selfDocChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := Bib.parse (← IO.FS.readFile "docs/references.bib")
  let keys := bib.entries.map (·.key)
  t "self docs: the project bibliography parses" (bib.errors.isEmpty && !keys.isEmpty)
  let project ← IO.FS.realPath "docs/references.bib"
  let files := ((← System.FilePath.walkDir "LeanTex") ++ (← System.FilePath.walkDir "scripts")).filter
    (·.toString.endsWith ".lean")
  let keySet := keys.foldl (·.insert ·) ({} : Std.HashSet String)
  let mut cited : Array String := #[]
  for f in files do
    let src ← IO.FS.readFile f
    let ks := (Code.undeclaredCites .lean f.toString src keySet).1
    let declared := Code.declaredBibs .lean src
    unless ks.isEmpty && declared.isEmpty do
      let mut own := !declared.isEmpty
      for b in declared do
        let at_ := (f.parent.getD ".") / b.dest
        own := own && (← at_.pathExists) && (← IO.FS.realPath at_) == project
      t s!"self docs: {f} declares docs/references.bib in its module docstring \
({repr (declared.map (·.dest))})" own
      let (d, ds) ← driverBuild f.toString
      let listed := (listsOf d).flatMap (·.2)
      t s!"self docs: {f} lists every key it cites (missing {ks.filter (!listed.contains ·)})"
        (ks.all listed.contains && !ds.any fun d => [DiagCode.W0351, .W0503, .W0449].contains d.kind)
      cited := cited ++ ks
  t s!"self docs: every project reference is cited (uncited {keys.filter (!cited.contains ·)})"
    (keys.all cited.contains)

end Tests.LeanCite
