module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-! A reference list read at its edges: a quote after what its level set, a key two entries claim,
alpha.bst's labels over invented names, a list whose file is not there, where a citation with no
entry stands, and a Lean page's bibliography that is not UTF-8. -/

namespace Tests.BibEdges

/-- An article's body around `body`, its bibliography `refs` under `style`. -/
def citingDoc (body : String) (style : String := "plain") (files : String := "refs") : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\bibliographystyle{" ++ style ++
    "}\n\\bibliography{" ++ files ++ "}\n\\end{document}\n"

/-- TeX's quotes read against what their level set before them, in the body and in a field. -/
def quoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let body (src : String) : String :=
    Ir.blocksText (elabStr ("\\documentclass{article}\n\\begin{document}\n" ++ src ++
      "\n\\end{document}\n")).1.body
  for (src, want) in [("As \\cite{k}'s view", "’s view"), ("an \\emph{x}'s case", "’s case"),
      ("{GPU}'s case", "GPU’s case"), ("$x$'s case", "’s case"),
      ("\\texttt{x}'s case", "’s case"), ("a~'q' b", "\u00a0‘q’"), ("say 'hi' now", "‘hi’"),
      ("say \"hi\" now", "“hi”")] do
    t s!"tex quotes: '{src}' reads its quote against what stands before it ({repr (body src)})"
      (hasStr (body src) want)
  t s!"tex quotes: literal text keeps its quote ({repr (body "\\texttt{'s}")})"
    (hasStr (body "\\texttt{'s}") "'s")
  let bib := "@book{q, author = {Ash, Ada}, title = {The {GPU}'s Role, $x$'s Value and \
\"{Best}\" Case}, publisher = {Example Press}, year = {2001}}\n"
  let (d, _) := bibBuild (citingDoc "\\nocite{q}") #[("refs", bib)]
  let ink := inkText d.body
  t s!"bib quotes: a field's quote after a group or a formula reads against it ({repr ink})"
    (hasStr ink "GPU’s" && hasStr ink "’s Value" && hasStr ink "“Best”" && !hasStr ink "‘")
  t s!"bib quotes: the plain reading's quote after a formula closes \
({repr (Bib.fieldInlines "$x$'s")})"
    ((Bib.fieldInlines "$x$'s").back? == some (.text "’s"))

/-- A key two entries of one list claim: the first stands, each later one named at its place. -/
def duplicateChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let entry (key title : String) : String :=
    s!"@book\{{key}, author = \{Ash, Ada}, title = \{{title}}, publisher = \{Example Press}, \
year = \{2001}}\n"
  let a := entry "dup" "First Notes"
  let b := entry "other" "Other Notes" ++ entry "dup" "Second Notes" ++ entry "dup" "Third Notes"
  let (d, ds) := bibBuild (citingDoc "See \\cite{dup} and \\cite{other}." (files := "a,b"))
    #[("a", a), ("b", b)]
  let ink := inkText d.body
  t s!"bib duplicate: the first entry of a key stands ({repr ink})"
    (hasStr ink "First Notes" && !hasStr ink "Second Notes" && !hasStr ink "Third Notes")
  let named := ds.filter fun d => d.kind == .W0450 && d.sites > 0
  t s!"bib duplicate: each later entry is named once, at its own file, the first one's place in \
its words ({repr (named.map fun x => (x.message, x.sites, x.span))})"
    (named.size == 1 && named.all fun x => x.sites == 2 &&
      x.span.any (·.file == "b.bib") && x.detail == some "the first at a.bib:1" &&
      x.severity == .warning)
  let (_, ds) := bibBuild (citingDoc "See \\cite{dup}." (files := "a")) #[("a", a)]
  t "bib duplicate: a key one entry holds names nothing" (!ds.any (·.kind == .W0450))
  let (_, ds) := bibBuild (citingDoc "See \\cite{dup}." (files := "a,c")) #[("a", a), ("c", a)]
  t "bib duplicate: a second entry the same as the first loses nothing and names nothing"
    (!ds.any (·.kind == .W0450))
  let (_, ds) := bibBuild (citingDoc "See \\cite{other}." (files := "a,b")) #[("a", a), ("b", b)]
  t "bib duplicate: a key the list does not set names nothing" (!ds.any (·.kind == .W0450))

/-- Invented entries over the name forms alpha.bst labels: von parts, braces, initials, a key, an
organization, an empty author, missing and odd years. -/
def alphaBib : String :=
  "@book{a1, author = {von Ashford, Ludo}, title = {T1}, publisher = {P}, year = {1928}}
@book{a2, author = {{von Ashford}, Ludo}, title = {T2}, publisher = {P}, year = {1928}}
@book{a3, author = {Ludo {von Ashford}}, title = {T3}, publisher = {P}, year = {1928}}
@book{a4, author = {von der Ashford, Ludo}, title = {T4}, publisher = {P}, year = {1928}}
@book{a5, author = {Ludo Von Ashford}, title = {T5}, publisher = {P}, year = {1928}}
@book{a6, author = {von Ashford, Jr., Ludo}, title = {T6}, publisher = {P}, year = {1928}}
@book{a7, author = {Ludo von ashford}, title = {T7}, publisher = {P}, year = {1928}}
@book{a8, author = {von Ashford}, title = {T8}, publisher = {P}, year = {1928}}
@book{a9, author = {Ludo von Ashford and others}, title = {T9}, publisher = {P}, year = {1928}}
@book{b1, author = {Ludo {\\relax von} Ashford}, title = {U1}, publisher = {P}, year = {1928}}
@book{b2, author = {Ludo {\\em von} Ashford}, title = {U2}, publisher = {P}, year = {1928}}
@book{b3, author = {Ludo d'Ashford}, title = {U3}, publisher = {P}, year = {1928}}
@book{b4, author = {Ludo de Ashford-Birch}, title = {U4}, publisher = {P}, year = {1928}}
@book{b5, author = {L. {von} Ashford}, title = {U5}, publisher = {P}, year = {1928}}
@book{b6, author = {Ludo von}, title = {U6}, publisher = {P}, year = {1928}}
@book{b7, author = {von}, title = {U7}, publisher = {P}, year = {1928}}
@book{b8, author = {Ludo vonAshford}, title = {U8}, publisher = {P}, year = {1928}}
@book{b9, author = {{\\v{C}}apek, Karel}, title = {U9}, publisher = {P}, year = {1928}}
@book{c1, author = {Ludo von Ashford and Bea von Birch and Cy von Cole}, title = {V1}, publisher = {P}, year = {1928}}
@book{c2, editor = {Ludo von Ashford}, author = {}, title = {V2}, publisher = {P}, year = {1928}}
@book{c3, author = {Ludo von Ashford}, title = {V3}, publisher = {P}}
@book{c4, author = {Ludo von Ashford}, title = {V4}, publisher = {P}, year = {c. 1928}}
@book{c5, author = {Ludo von Ashford}, title = {V5}, publisher = {P}, year = {{1928}}}
@book{c6, author = {Ludo von Ashford}, title = {V6}, publisher = {P}, year = {28}}
@book{c7, author = {Ludo von Ashford}, key = {Kay}, title = {V7}, publisher = {P}, year = {1928}}
@book{c8, key = {von Kay}, title = {V8}, publisher = {P}, year = {1928}}
@book{c9, organization = {von Org}, title = {V9}, publisher = {P}, year = {1928}}
@manual{d1, organization = {The von Org}, title = {W1}, year = {1928}}
@proceedings{d2, editor = {Ludo von Ashford}, title = {W2}, year = {1928}}
@proceedings{d3, organization = {The Org}, title = {W3}, year = {1928}}
"

/-- bibtex 0.99e's `alpha.bst` over `alphaBib`, its list in its order with each label as lualatex
prints it; its et al. mark prints raised there. -/
def alphaBst : List (String × String) :=
  [("b5", "Ash28a"), ("a5", "Ash28b"), ("c9", "c928"), ("b9", "Čap28"), ("b3", "d’A28"),
   ("b4", "dAB28"), ("d3", "Org28"), ("c3", "vA"), ("a8", "vA28a"), ("a1", "vA28b"),
   ("a7", "va28c"), ("c2", "vA28d"), ("c5", "vA28e"), ("c7", "vA28f"), ("d2", "vA28g"),
   ("c4", "vA28h"), ("a9", "vA+28i"), ("a6", "vA28j"), ("c6", "vA28"), ("c1", "vAvBvC28"),
   ("a4", "vdA28"), ("b7", "von28a"), ("b6", "von28b"), ("a2", "von28c"), ("a3", "von28d"),
   ("c8", "von28e"), ("d1", "von28f"), ("b8", "von28g"), ("b1", "vonA28a"), ("b2", "vonA28b")]

/-- alpha's labels and order as alpha.bst sets them. -/
def alphaChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (d, _) := bibBuild (citingDoc "\\nocite{*}" (style := "alpha")) #[("refs", alphaBib)]
  let items := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map fun it => (it.key, it.marker.getD "")
    | _ => out) (fun out _ => out) #[] d.body
  let off := (items.toList.zip alphaBst).filter fun (a, b) => a != b
  t s!"alpha: every label and the list's order are alpha.bst's ({repr off})"
    (items.toList == alphaBst)

/-- A list whose one file is not there ships with its loss named once. -/
def missingChecks (ref : IO.Ref (List String)) (binary : System.FilePath :=
    ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let src := citingDoc "A claim \\cite{a} and \\cite{b}." (files := "absent")
  let doc := (elabStr src).1
  let (out, ds, _) ← Input.resolveBibliography "doc.tex" doc Bib.plainReading #[]
  t s!"bib missing: one warning names the file and every citation's mark \
({repr (ds.map fun d => (d.code, d.severity))})"
    (ds.map (·.kind) == #[.W0503] && ds.all (·.severity == .warning) &&
      ds.all (·.carries == [.W0351]))
  t "bib missing: both citations show their mark" ((citesOf out).size == 2)
  let binary ← IO.FS.realPath binary
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    IO.FS.createDirAll (dir / "bin")
    IO.FS.writeFile (dir / "doc.tex") src
    let run ← IO.Process.output {
      cmd := binary.toString, cwd := some dir
      args := #["doc.tex", "-o", "doc.html", "--porcelain"]
      env := #[("PATH", some (dir / "bin").toString),
        ("XDG_CACHE_HOME", some (dir / "cache").toString), ("LEANTEX_FONT", some font.toString)] }
    let codes := ((run.stdout.splitOn "\n").filter (!·.isEmpty)).filterMap fun line =>
      ((Lean.Json.parse line).toOption.bind fun j => (j.getObjValAs? String "code").toOption)
    t s!"bib missing CLI: the page ships (exit {run.exitCode}, {codes})"
      (run.exitCode == 0 && (← (dir / "doc.html").pathExists))
    t s!"bib missing CLI: the file's loss is named once, no citation apart ({codes})"
      (codes.count "W0503" == 1 && codes.count "W0351" == 0)

/-- A TeX host including markdown, read as the driver reads it, its reference list resolved with
the elaboration's citation sites. -/
def includedBib (host : String) (files : List (String × String × String))
    (bibs : Array (String × String)) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex "h.tex" host
  let (executed, readDs) := (Elab.executeInputs (mdFileReader files) "h.tex" raws).run #[]
  let prepared := Elab.prepareExecuted "h.tex" executed
  let (doc, eds, spans) := Elab.runPrepared "h.tex" prepared (ds ++ readDs) (fun _ _ => {})
  let sources := (Ir.bibRefs doc).filterMap fun r => bibs.find? (·.1 == r)
  let (doc, bds) := Bib.resolve "h.tex" prepared sources doc spans.cites
  (doc, Bib.accountFront eds bds #[] #[])

/-- A citation with no entry is named at its first site, in the words of the surface it was written in. -/
def siteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := "@book{a, author = {Ash, Ada}, title = {Alpha Notes}, publisher = {Example Press}, \
year = {2001}}\n"
  let (_, ds) := bibBuild (citingDoc "See \\cite{a} and\n\\cite{ghost}.") #[("refs", bib)]
  let missing := ds.filter (·.kind == .W0351)
  t s!"cite site: a TeX citation with no entry is named at its command \
({repr (missing.map fun d => (d.span, d.help))})"
    (missing.size == 1 && missing.all fun d =>
      d.span.any (fun s => s.file == "t.tex" && s.pos.line == 4) &&
        (d.help.any (hasStr · "\\cite")))
  let host := "\\documentclass{article}\n\\usepackage[numbers]{natbib}\n\
\\usepackage[citations]{markdown}\n\\begin{document}\nSee \\citep{a}.\n\n\\markdownInput{p.md}\n\n\
\\bibliographystyle{unsrtnat}\n\\bibliography{refs}\n\\end{document}\n"
  let (_, ds) := includedBib host [("p.md", "p.md", "The notes cite [@a] and\n[@ghost].\n")]
    #[("refs", bib)]
  let missing := ds.filter (·.kind == .W0351)
  t s!"cite site: an included markdown citation is named in the markdown file, spelled as written \
({repr (missing.map fun d => (d.span, d.help))})"
    (missing.size == 1 && missing.all fun d =>
      d.span.any (fun s => s.file == "p.md" && s.pos.line == 2) &&
        d.help.any (hasStr · "@ghost") && !d.help.any (hasStr · "\\cite"))

/-- A Lean page's bibliography that is not UTF-8: its keys are the ones its reference list reads,
so a key holding a byte that is not text stays as written, the file's loss named once. -/
def encodingKeyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let latin1 : ByteArray := "@book{caf".toUTF8 ++ ⟨#[0xE9]⟩ ++ "2001, author = {Ash, Ada}, \
title = {Caf".toUTF8 ++ ⟨#[0xE9]⟩ ++ " Notes}, publisher = {Example Press}, year = {2001}}\n\
@book{ash2001, author = {Ash, Ada}, title = {Alpha Notes}, publisher = {Example Press}, \
year = {2001}}\n".toUTF8
  IO.FS.withTempDir fun dir => do
    IO.FS.writeBinFile (dir / "refs.bib") latin1
    let page := (dir / "F.lean").toString
    let text := "-- leantex: bibliography = refs.bib\n/-! See [café2001] and [ash2001]. -/\n\n\
def x := 1\n"
    let read ← Input.readDocument page text.toUTF8
    let prepared := Elab.prepareExecuted page read.executed
    let (doc, ds, spans) := Elab.runPrepared page prepared read.diags (fun _ _ => {})
    let (doc, bds, ledger) ← Input.resolveBibliography page doc (Bib.FieldDoor.of page prepared).read
      spans.labels spans.bib read.ledger spans.cites
    let all := Bib.accountFront ds bds ledger.notes (Bib.refJudge spans doc)
    let bytes := all.filter fun d => d.kind == .W0002 && d.severity == .warning
    t s!"bib encoding: the page cites the key its list holds, the other as written \
({keysOf doc}, {repr (inkText doc.body)})"
      (keysOf doc == ["ash2001"] && hasStr (inkText doc.body) "[café2001]" &&
        !all.any (·.kind == .W0351))
    t s!"bib encoding: the file's bytes are named once, in no TeX package's words \
({repr (bytes.map (·.help))})"
      (bytes.size == 1 && bytes.all fun d => !d.help.any (hasStr · "inputenc"))

end Tests.BibEdges
