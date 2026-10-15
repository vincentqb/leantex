module

public import Tests.Support

public section

open LeanTex.Core

/-! Markdown's citations: Pandoc's syntax, read as its manual and its reader read it, lowered as
its LaTeX writer lowers it under natbib, resolved through the one bibliography path, and spelled
back by the markdown twin. -/

namespace Tests.MarkdownCite

/-- The citation nodes of an elaborated body in order, resolved or not: their forms and keys. -/
def citesOf (doc : Ir.Doc) : Array (Ir.CiteForm × Array String) :=
  Ir.foldBlocks (fun out _ => out) (fun out x => match x with
    | .cite f ks => out.push (f, ks)
    | .cited f ks _ => out.push (f, ks)
    | _ => out) #[] doc.body

/-- A markdown document elaborated and its bibliography resolved as a build resolves them, from
`.bib` texts by the names the document gives them. -/
def mdBibBuild (src : String) (bibs : Array (String × String)) (file : String := "t.md") :
    Ir.Doc × Array Diag :=
  let (raws, readDs) := Surface.read .markdown file src
  let prepared := Elab.prepareExecuted file (Elab.executeInputs nullReader file raws)
  let (doc, ds, spans) := Elab.runPrepared file prepared readDs (fun _ _ => {})
  let sources := (Ir.bibRefs doc).filterMap fun r => bibs.find? (·.1 == r)
  let (doc, bds) := Bib.resolve file prepared sources doc
  let doc := Bib.resolveListRefs spans.labels doc
  (Ir.eraseLocations doc, Bib.accountFront ds bds #[] (Bib.refJudge spans doc))

/-- Invented entries, keys `a`, `b` and `roe2020`, placeholder names. -/
def worksBib : String :=
  "@book{a, author = {Ash, Ada}, title = {Alpha Notes}, publisher = {Example Press}, year = {2001}}\n\
@book{b, author = {Birch, Bo}, title = {Beta Notes}, publisher = {Example Press}, year = {2002}}\n\
@misc{roe2020, author = {Roe, Sam}, title = {Placeholder Text}, year = {2020}}\n"

/-- Markdown citations beside what Pandoc 3.12.1's LaTeX writer sets for them under `--natbib`
(`citationsToNatbib`), its smart non-breaking space after `p.` written as a space. -/
def pandocNatbib : List (String × String) :=
  [("[@a]", "\\citep{a}"), ("[@a, p. 33]", "\\citep[p. 33]{a}"), ("[see @a]", "\\citep[see][]{a}"),
   ("[see @a, p. 33]", "\\citep[see][p. 33]{a}"), ("[@a; @b]", "\\citep{a, b}"),
   ("[see @a; @b, p. 2]", "\\citep[see][p. 2]{a, b}"),
   ("[see @a, pp. 1-3; @b]", "\\citetext{\\citealp[see][pp. 1-3]{a}; \\citealp{b}}"),
   ("[@a, p. 1; @b]", "\\citetext{\\citealp[p. 1]{a}; \\citealp{b}}"),
   ("[@a; see @b]", "\\citetext{\\citealp{a}; \\citealp[see][]{b}}"),
   ("@a says", "\\citet{a} says"), ("@a [p. 4] says", "\\citet[p. 4]{a} says"),
   ("@a [p. 4; @b] says", "\\citeauthor{a} \\citetext{\\citeyear[p. 4]{a}; \\citealp{b}} says"),
   ("@a [@b] says", "\\citeauthor{a} \\citetext{\\citeyear{a}; \\citealp{b}} says"),
   ("[-@a]", "\\citeyearpar{a}"), ("[-@a, p. 3]", "\\citeyearpar[p. 3]{a}"),
   ("[see -@a]", "\\citeyearpar[see][]{a}"), ("[@a; -@b]", "\\citetext{\\citealp{a}; \\citeyear{b}}"),
   ("-@a says", "\\citeyearpar{a} says"),
   ("[@smith{ii, A, D-Z}, with a suffix]", "\\citep[ii, A, D-Z, with a suffix]{smith}"),
   ("[@smith{}, 99 years later]", "\\citep[, 99 years later]{smith}"),
   ("[*see* @a]", "\\citep[\\emph{see}][]{a}"), ("[@a, and *passim*]", "\\citep[and \\emph{passim}]{a}"),
   ("[@a,p. 33]", "\\citep[p. 33]{a}"), ("[@a: p. 33]", "\\citep[p. 33]{a}"),
   ("[@a\n, p. 33]", "\\citep[p. 33]{a}")]

/-- Keys as Pandoc's `citeKey` reads them, with what stands after the key. -/
def keyCases : List (String × String × String) :=
  [("@Foo_bar.baz. ends", "Foo_bar.baz", ". ends"), ("@Foo_bar--baz ends", "Foo_bar", "baz ends"),
   ("@{Foo_bar.baz.} ends", "Foo_bar.baz.", " ends"), ("@a_b ends", "a_b", " ends"),
   ("@a__b ends", "a__b", " ends"), ("@2020doe ends", "2020doe", " ends"),
   ("@a: ends", "a", ": ends"), ("@a/b ends", "a/b", " ends"),
   ("@http://x.org/a ends", "http://x.org/a", " ends"), ("@a's ends", "a", "s ends"),
   ("@é ends", "é", " ends"), ("(@a) ends", "a", ") ends"), ("a-@b ends", "b", " ends"),
   ("a+@b ends", "b", " ends")]

/-- Text with an `@` that Pandoc reads as no citation, and what the page keeps of it. -/
def notCites : List (String × String) :=
  [("mail x@example.org here", "x@example.org"), ("code `@a` here", "@a"),
   ("escaped \\@a here", "@a"), ("bracketed [x@y.org] here", "[x@y.org]"),
   ("joined [see@a] here", "[see@a]"), ("after a dot a.@b here", "a.@b"),
   ("closing *x*@a here", "@a"), ("no key @-a here", "@-a"), ("no key @:a here", "@:a"),
   ("a wildcard @* here", "@*")]

/-- The citation forms a tex document writes that the twin spells, and how. -/
def texTwinCases : List (String × String) :=
  [("\\citep{a}", "[@a]"), ("\\citep[see][p. 3]{a,b}", "[see @a; @b, p. 3]"),
   ("\\citet{a}", "@a"), ("\\citet[p. 4]{a}", "@a [p. 4]"), ("\\citeyearpar{a}", "[-@a]")]

def mdCiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Each citation elaborates to the IR Pandoc's natbib output does, through the one natbib arm.
  for (md, latex) in pandocNatbib do
    let m := citesOf (elabMd (md ++ "\n")).1
    let l := citesOf (elabStr (dvDoc "\\usepackage{natbib}\n" latex)).1
    t s!"cite: {repr md} elaborates as Pandoc's natbib writer sets it, {latex}" (!m.isEmpty && m == l)
  -- Pandoc's evident-intent reading, not its writer's wart: a suffix's space before its comma.
  t "cite: a suffix spaced before its comma sets without the comma"
    (citesOf (elabMd "[@a , p. 33]\n").1 == citesOf (elabStr (dvDoc "" "\\citep[p. 33]{a}")).1)
  t "cite: a suffix keeps a balanced bracket, which natbib's optional argument cannot hold"
    ((citesOf (elabMd "[@a, p. 3 [note]]\n").1).map (·.1.post) == #["p. 3 [note]"])
  for (md, key, after) in keyCases do
    let (d, _) := elabMd (md ++ "\n")
    let keys := (citesOf d).toList.flatMap fun (_, ks) => ks.toList
    t s!"cite: {repr md} cites {repr key}, then {repr after} as text"
      (keys == [key] && hasStr (Ir.blocksText d.body) after)
  for (md, shown) in notCites do
    let (d, _) := elabMd (md ++ "\n")
    t s!"cite: {repr md} holds no citation and keeps {repr shown}"
      ((citesOf d).isEmpty && hasStr (Ir.blocksText d.body) shown)
  -- A bracket that is no citation list keeps its brackets around what it holds.
  for (md, kept) in [("[@a; text] end", "; text]"), ("[*see @a*] end", "]"), ("[@a][x] end", "][x]")] do
    let (d, _) := elabMd (md ++ "\n")
    t s!"cite: {repr md} is an author-in-text citation inside its kept brackets"
      ((citesOf d).map (·.1.cmd) == #[.textual] && hasStr (Ir.blocksText d.body) kept)
  let (d, _) := elabMd "[@a](https://example.org) end\n"
  t "cite: a citation bracket followed by a destination is a link around an in-text citation"
    (d.body.any fun b => match b with
      | .para xs => xs.any fun x => match x with
        | .link u body => u == "https://example.org" && body.any (· matches .cite ..)
        | _ => false
      | _ => false)
  -- Every note the IR's plain notes cannot carry is named, once per citation.
  let (_, ds) := elabMd "[*see* @a] and [@a, `code`]\n"
  t "cite: a formatted prefix or suffix is named, once per citation"
    ((ds.filter (·.subject == some "md:cite-note")).size == 2)
  -- The twin spells each citation in Pandoc's syntax, and reads back to the same IR.
  for (md, spelled) in mdCiteTwinCases do
    let (d, _) := elabMd (md ++ "\n")
    let twin := MarkdownDoc.emit d
    let (back, _) := elabMd twin
    t s!"twin: {repr md} spells {repr spelled} ({repr twin})" (hasStr twin spelled)
    t s!"twin: {repr md} reads back to its IR" (back.body == d.body)
  for (tex, spelled) in texTwinCases do
    let (d, _) := elabStr (dvDoc "\\usepackage{natbib}\n" tex)
    let twin := MarkdownDoc.emit d
    t s!"twin: tex's {tex} spells {repr spelled} ({repr twin})" (hasStr twin spelled)
    t s!"twin: tex's {tex} reads back to its citation" (citesOf (elabMd twin).1 == citesOf d)
  for tex in ["\\citet{a,b}", "\\Citep{a}", "\\citeauthor{a}", "\\citep*{a}"] do
    let (d, _) := elabStr (dvDoc "\\usepackage{natbib}\n" tex)
    let twin := MarkdownDoc.emit d
    t s!"twin: tex's {tex}, which Pandoc's syntax cannot spell, writes its marks and no citation \
({repr twin})" (!hasStr twin "@" && (citesOf (elabMd twin).1).isEmpty)
  let (d, _) := elabMd "Write x\\@a and \\@b and [x@y.org].\n"
  let twin := MarkdownDoc.emit d
  t s!"twin: an at sign that would open a citation is escaped, an e-mail's is not ({repr twin})"
    (hasStr twin "\\@b" && hasStr twin "x@a" && (citesOf (elabMd twin).1).isEmpty)
  -- One bibliography path: the same numbering, list, styles and undefined-key loss as tex.
  let bibs := #[("works.bib", worksBib)]
  let src := "---\nbibliography: works.bib\nnatbiboptions: numbers\nbiblio-style: unsrtnat\n---\n\n\
Text [@b] and @a and [@ghost].\n"
  let (md, mdDs) := mdBibBuild src bibs
  let (tex, texDs) := bibBuild (dvDoc "\\usepackage[numbers]{natbib}\n"
    "Text \\citep{b} and \\citet{a} and \\citep{ghost}.\n\n\\bibliographystyle{unsrtnat}\n\\bibliography{works.bib}")
    bibs
  let listOf (d : Ir.Doc) : Array (String × Option String) := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map fun it => (it.key, it.marker)
    | _ => out) (fun out _ => out) #[] d.body
  t s!"bib: markdown and tex citations share one numbering and one list ({repr (listOf md)})"
    (listOf md == listOf tex && listOf md == #[("b", some "1"), ("a", some "2")])
  let inkOf (d : Ir.Doc) : String := Ir.blocksText (d.body.filter (· matches .para ..))
  t s!"bib: the citations set as tex's do ({inkOf md})" (inkOf md == inkOf tex)
  let undefinedOf (ds : Array Diag) := ds.filter (·.kind == .W0351)
  t "bib: the undefined key is one W0351 in both, its help in each surface's spelling"
    ((undefinedOf mdDs).size == 1 && (undefinedOf texDs).size == 1 &&
      (undefinedOf mdDs).all (·.help.any (hasStr · "@ghost")) &&
      (undefinedOf texDs).all (·.help.any (hasStr · "\\cite")))
  -- HTML citations link to their entries as tex's do: the same targets and anchors.
  let mdHtml := docHtmlOf md
  let texHtml := docHtmlOf tex
  for k in ["a", "b"] do
    t s!"html: the markdown citation of {k} links to its entry, as tex's does"
      (hasStr mdHtml s!"href=\"#ref-{k}\"" && hasStr mdHtml s!"<li id=\"ref-{k}\"" &&
        hasStr texHtml s!"href=\"#ref-{k}\"" && hasStr texHtml s!"<li id=\"ref-{k}\"")
  -- Both backends from the one IR value: the page and the web page set the same citation ink.
  match ← serifFacesSet with
  | none => t "cite: the serif faces load" false
  | some fonts =>
    let pageText := String.join ((bodyLines (layoutOf fonts md)).toList.map (lineText ·))
    for ink in ["[1]", "Ash [2]", "[?]"] do
      t s!"backends: the page and the web page both set {repr ink}"
        (hasStr pageText ink && hasStr (Ir.blocksText md.body) ink)
  let (noBib, noBibDs) := elabMd "Text [@a].\n"
  t "bib: with no bibliography declared, the help names the metadata key"
    ((citesOf noBib).size == 1 && noBibDs.any fun d =>
      d.kind == .W0351 && d.help.any (hasStr · "bibliography: refs.bib"))
  -- A markdown file included in tex cites into the including document's bibliography.
  let (inc, _) ← elabFixture "md-cite-include" (← fixtureText "testdata/corpus/md-cite-include.tex")
  let lists := Ir.foldBlocks (fun n b => if b matches .bibliography .. then n + 1 else n)
    (fun n _ => n) 0 inc.body
  t s!"include: one reference list numbers the article's and its markdown file's citations \
({repr (listOf inc)})"
    (lists == 1 && listOf inc == #[("roe2020", some "1"), ("poe2022", some "2"),
      ("doe2024", some "3"), ("vale2016", some "4")])
  t "include: the markdown file's citations resolve with the article's"
    (hasStr (Ir.blocksText inc.body) "cite [2] and Doe and Hale [3, p. 42]")

def mdMetadataChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bibs := #[("works.bib", worksBib), ("other.bib", worksBib)]
  let listOf (d : Ir.Doc) : Array String := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map (·.key)
    | _ => out) (fun out _ => out) #[] d.body
  let styleOf (d : Ir.Doc) : Option String := Ir.bibStyleName d
  -- A metadata block is read only at the first line, opening on `---` with no blank line after.
  let metaSrc := "---\nbibliography: works.bib\n---\n\nText [@a].\n"
  let (d, ds) := mdBibBuild metaSrc bibs
  t s!"metadata: a block at the first line declares the bibliography ({repr (listOf d)})"
    (listOf d == #["a"] && styleOf d == some "plainnat" && ds.all (·.kind != .W0307))
  t "metadata: its text never reaches the page"
    (!hasStr (Ir.blocksText d.body) "works.bib" && !hasStr (Ir.blocksText d.body) "bibliography")
  for (why, src) in [("after a blank first line", "\n---\nbibliography: works.bib\n---\n\nText.\n"),
      ("with a blank line after its opening", "---\n\nbibliography: works.bib\n---\n\nText.\n"),
      ("holding no mapping", "---\nJust a line of prose\n---\n\nText.\n"),
      ("never closed", "---\nbibliography: works.bib\n\nText.\n")] do
    let (d, _) := elabMd src
    t s!"metadata: a block {why} stays markdown" (hasStr (Ir.blocksText d.body) "Text" &&
      (listOf d).isEmpty && (hasStr (Ir.blocksText d.body) "bibliography" ||
        hasStr (Ir.blocksText d.body) "Just a line"))
  -- YAML's spellings of a path and of a list of paths.
  for (form, src) in [("a quoted path", "bibliography: 'works.bib'"),
      ("a double-quoted path", "bibliography: \"works.bib\""),
      ("a flow list", "bibliography: [works.bib, other.bib]"),
      ("a block list", "bibliography:\n  - works.bib\n  - other.bib"),
      ("a block list at the key's indent", "bibliography:\n- works.bib\n- other.bib"),
      ("a commented path", "bibliography: works.bib # the entries")] do
    let (d, ds) := mdBibBuild ("---\n" ++ src ++ "\n---\n\nText [@a].\n") bibs
    t s!"metadata: {form} names the bibliography" (listOf d == #["a"] && ds.all (·.kind != .W0307))
  -- What a key declares, and every key not read named once.
  let (d, _) := mdBibBuild ("---\nbibliography: works.bib\nnatbiboptions: numbers\n" ++
    "biblio-style: unsrtnat\nnocite: '@b'\n---\n\nText [@a].\n") bibs
  t s!"metadata: natbib's options, the style and nocite reach the list ({repr (listOf d)})"
    (listOf d == #["a", "b"] && styleOf d == some "unsrtnat" &&
      hasStr (Ir.blocksText d.body) "Text [1]")
  let (d, _) := mdBibBuild "---\nbibliography: works.bib\nnocite: |\n  @*\n---\n\nText.\n" bibs
  t s!"metadata: nocite's wildcard lists every entry ({repr (listOf d)})" ((listOf d).size == 3)
  let (_, ds) := elabMd ("---\ntitle: An invented note\nauthor:\n  - Placeholder Person\n" ++
    "draft_: true\ncsl: chicago.csl\nlink-citations: false\nkeywords: [one, two]\n" ++
    "title: A second title\n---\n\nText.\n")
  let subjects := ds.filterMap (·.subject)
  t s!"metadata: each key not read is named once, an underscore key ignored ({repr subjects})"
    (subjects.filter (·.startsWith "md:meta:") ==
      #["md:meta:author", "md:meta:csl", "md:meta:keywords", "md:meta:title"])
  t "metadata: a CSL style's help names the BibTeX style key"
    (ds.any fun d => d.subject == some "md:meta:csl" && d.help.any (hasStr · "biblio-style"))
  t "metadata: link-citations false is named as the link it does not drop"
    (ds.any (·.subject == some "md:link-citations"))
  let (_, ds) := mdBibBuild "---\nbibliography: works.json\n---\n\nText [@a].\n" bibs
  t "metadata: a bibliography in another format is named, not read"
    (ds.any (·.subject == some "md:meta:bibliography:works.json"))
  -- Where the list stands: a `{#refs}` division, else the end under its declared title.
  let (d, _) := mdBibBuild ("---\nbibliography: works.bib\nreference-section-title: Works cited\n" ++
    "---\n\nText [@a].\n") bibs
  t "metadata: the list sets at the end under its declared title"
    (match d.body.toList.reverse with
      | .bibliography _ _ _ :: .section _ _ _ title :: _ => Ir.plainText title == "Works cited"
      | _ => false)
  let (d, _) := mdBibBuild ("---\nbibliography: works.bib\nreference-section-title: Works cited\n" ++
    "---\n\nText [@a].\n\n::: {#refs}\n## Sources\n:::\n\nAfter the list.\n") bibs
  t "metadata: a {#refs} division places the list after its own blocks, the title unset"
    (match d.body.toList with
      | [.para _, .section _ _ _ h, .bibliography _ _ _, .para after] =>
        Ir.plainText h == "Sources" && Ir.plainText after == "After the list."
      | _ => false)
  let (_, ds) := elabMd "Text.\n\n::: {#refs}\n:::\n"
  t "metadata: a {#refs} division with no bibliography is named" (ds.any (·.subject == some "md:refs"))
  -- An included file's metadata: its nocite joins the document's, its bibliography is the document's.
  let (raws, ds) := Md.readIncluded "part.md" "---\nbibliography: works.bib\nnocite: '@b'\n---\n\nText.\n"
  t "metadata: an included file's bibliography is named, its nocite read"
    (ds.any (·.subject == some "md:meta:bibliography") &&
      raws.any (· matches .ctrl "nocite" _) && !raws.any (· matches .ctrl "markdown bibliography" _))

end Tests.MarkdownCite
