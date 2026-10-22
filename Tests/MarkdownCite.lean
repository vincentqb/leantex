module

public import Tests.Support
public import LeanTex.Cli.World

public section

open LeanTex.Core LeanTex.Cli

/-! Markdown's citations: Pandoc's syntax, read as its manual and its reader read it, lowered as
its LaTeX writer lowers it under natbib, resolved through the one bibliography path, and spelled
back by the markdown twin. -/

namespace Tests.MarkdownCite

/-- A markdown body read under `worksMeta`, which declares the bibliography citations need. -/
def elabCited (body : String) : Ir.Doc × Array Diag := elabMd (worksMeta ++ body ++ "\n")

/-- A page's text as a browser shows it: the rendered HTML without its tags. -/
def webText (doc : Ir.Doc) : String := Id.run do
  let mut out := ""
  let mut inTag := false
  for c in (docHtmlOf doc).toList do
    if c == '<' then inTag := true
    else if c == '>' then inTag := false
    else if !inTag then out := out.push c
  return out

/-- Markdown citations beside what Pandoc 3.12.1's LaTeX writer sets for them under `--natbib`
(`citationsToNatbib`), its smart non-breaking space after `p.` written as a space. -/
def pandocNatbib : List (String × String) :=
  [("[@a]", "\\citep{a}"), ("[@a, p. 33]", "\\citep[p.~33]{a}"), ("[see @a]", "\\citep[see][]{a}"),
   ("[see @a, p. 33]", "\\citep[see][p.~33]{a}"), ("[@a; @b]", "\\citep{a, b}"),
   ("[see @a; @b, p. 2]", "\\citep[see][p.~2]{a, b}"),
   ("[see @a, pp. 1-3; @b]", "\\citetext{\\citealp[see][pp.~1-3]{a}; \\citealp{b}}"),
   ("[@a, p. 1; @b]", "\\citetext{\\citealp[p.~1]{a}; \\citealp{b}}"),
   ("[@a; see @b]", "\\citetext{\\citealp{a}; \\citealp[see][]{b}}"),
   ("@a says", "\\citet{a} says"), ("@a [p. 4] says", "\\citet[p.~4]{a} says"),
   ("@a [p. 4; @b] says", "\\citeauthor{a} \\citetext{\\citeyear[p.~4]{a}; \\citealp{b}} says"),
   ("@a [@b] says", "\\citeauthor{a} \\citetext{\\citeyear{a}; \\citealp{b}} says"),
   ("[-@a]", "\\citeyearpar{a}"), ("[-@a, p. 3]", "\\citeyearpar[p.~3]{a}"),
   ("[see -@a]", "\\citeyearpar[see][]{a}"), ("[@a; -@b]", "\\citetext{\\citealp{a}; \\citeyear{b}}"),
   ("-@a says", "\\citeyearpar{a} says"),
   ("[@smith{ii, A, D-Z}, with a suffix]", "\\citep[ii, A, D-Z, with a suffix]{smith}"),
   ("[@smith{}, 99 years later]", "\\citep[, 99 years later]{smith}"),
   ("[*see* @a]", "\\citep[\\emph{see}][]{a}"), ("[@a, and *passim*]", "\\citep[and \\emph{passim}]{a}"),
   ("[@a,p. 33]", "\\citep[p.~33]{a}"), ("[@a: p. 33]", "\\citep[p.~33]{a}"),
   ("x @a-@b ends", "x \\citet{a}\\citeyearpar{b} ends"), ("[@a.]", "\\citep{a}"),
   ("[@a. p. 3]", "\\citep[p.~3]{a}"), ("[@a! p. 3]", "\\citep[p.~3]{a}"), ("x...@a ends", "x...\\citet{a} ends"),
   ("x --@a ends", "x --\\citet{a} ends"), ("[--@a]", "\\citep[--][]{a}")]

/-- Keys as Pandoc's `citeKey` reads them, with what stands after the key. -/
def keyCases : List (String × String × String) :=
  [("@Foo_bar.baz. ends", "Foo_bar.baz", ". ends"), ("@Foo_bar--baz ends", "Foo_bar", "baz ends"),
   ("@{Foo_bar.baz.} ends", "Foo_bar.baz.", " ends"), ("@a_b ends", "a_b", " ends"),
   ("@a__b ends", "a__b", " ends"), ("@2020doe ends", "2020doe", " ends"),
   ("@a: ends", "a", ": ends"), ("@a/b ends", "a/b", " ends"),
   ("@http://x.org/a ends", "http://x.org/a", " ends"), ("@a's ends", "a", "s ends"),
   ("@é ends", "é", " ends"), ("x (@a) ends", "a", ") ends"), ("a-@b ends", "b", " ends"),
   ("a+@b ends", "b", " ends"), ("x_@a ends", "a", " ends"), ("x*@a ends", "a", " ends"),
   ("(*@a*) ends", "a", ") ends"), ("@{a{b}c} ends", "a{b}c", " ends")]

/-- Text with an `@` that reads as no citation, and what the page keeps of it: Pandoc's readings,
after a word, a closing emphasis or a backslash. -/
def notCites : List (String × String) :=
  [("mail x@example.org here", "x@example.org"), ("code `@a` here", "@a"),
   ("escaped \\@a here", "@a"), ("bracketed [x@y.org] here", "[x@y.org]"),
   ("joined [see@a] here", "[see@a]"), ("after a dot a.@b here", "a.@b"),
   ("closing *x*@a here", "@a"), ("closing _x_@a here", "@a"), ("closing **x**@a here", "@a"),
   ("no key @-a here", "@-a"), ("no key @:a here", "@:a"),
   ("an open brace @{a here", "@{a"), ("a spaced brace @{a b} here", "@{a b}")]

/-- The citation forms a tex document writes that the twin spells, and how. -/
def texTwinCases : List (String × String) :=
  [("\\citep{a}", "[@a]"), ("\\citep[see][p. 3]{a,b}", "[see @a; @b, p.&#32;3]"),
   ("\\citet{a}", "@a"), ("\\citet[p. 4]{a}", "@a [p.&#32;4]"), ("\\citeyearpar{a}", "[-@a]"),
   ("\\citet{a} \\citep{b}", "@a&#32;[@b]"), ("x -\\citet{a}", "x -<!-- -->@a"),
   ("\\citet{a}\\citep{b}", "@a<!-- -->[@b]"), ("\\citep{a}\\citep{b}", "[@a]<!-- -->[@b]"),
   ("word\\citet{a}", "word<!-- -->@a"), ("x-\\citet{a}", "x-@a")]

/-- TeX bodies whose twin cannot spell every citation where it stands, so it sets them as their
marks. -/
def inkTwinCases : List String :=
  ["\\citet*{a} and \\citep{b}; \\citep{a}(x) and \\citep{roe2020}.",
   "\\citeauthor{roe2020} and \\citep{b} and \\citep{a}."]

/-- A tex body with natbib loaded and `works.bib` its bibliography. -/
def worksTex (body : String) : String :=
  dvDoc "\\usepackage{natbib}\n" (body ++ "\n\n\\bibliographystyle{plainnat}\n\\bibliography{works}")

def mdCiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Each citation elaborates to the IR Pandoc's natbib output does, through the one natbib arm.
  for (md, latex) in pandocNatbib do
    let m := citesOf (elabCited md).1
    let l := citesOf (elabStr (dvDoc "\\usepackage{natbib}\n" latex)).1
    t s!"cite: {repr md} elaborates as Pandoc's natbib writer sets it, {latex}" (!m.isEmpty && m == l)
  -- Pandoc's evident-intent reading, not its writer's wart: a suffix's space or line ending before
  -- its comma.
  for md in ["[@a , p. 33]", "[@a\n, p. 33]"] do
    t s!"cite: {repr md}, its comma after white space, sets without the comma"
      (citesOf (elabCited md).1 == citesOf (elabStr (dvDoc "" "\\citep[p.~33]{a}")).1)
  t "cite: a suffix keeps a balanced bracket, which natbib's optional argument cannot hold"
    ((citesOf (elabCited "[@a, p. 3 [note]]").1).map (·.1.post) == #["p.\u00a03 [note]"])
  for (md, key, after) in keyCases do
    let (d, _) := elabCited md
    t s!"cite: {repr md} cites {repr key}, then {repr after} as text"
      (keysOf d == [key] && hasStr (Ir.blocksText d.body) after)
  t "cite: a key's end opens another citation, as Pandoc reads '@a@b'" (keysOf (elabCited "@a@b x").1 == ["a", "b"])
  for (md, shown) in notCites do
    let (d, _) := elabCited md
    t s!"cite: {repr md} holds no citation and keeps {repr shown}"
      ((citesOf d).isEmpty && hasStr (Ir.blocksText d.body) shown)
  -- A bracket that is no citation list keeps its brackets around what it holds.
  for (md, kept) in [("[@a; text] end", "; text]"), ("[*see @a*] end", "]"), ("[@a][x] end", "][x]")] do
    let (d, _) := elabCited md
    t s!"cite: {repr md} is an author-in-text citation inside its kept brackets"
      ((citesOf d).map (·.1.cmd) == #[.textual] && hasStr (Ir.blocksText d.body) kept)
  let (d, _) := elabCited "[@a](https://example.org) end"
  t "cite: a citation bracket followed by a destination is a link around an in-text citation"
    (d.body.any fun b => match b with
      | .para xs => xs.any fun x => match x with
        | .link u body => u == "https://example.org" && body.any (· matches .cite ..)
        | _ => false
      | _ => false)
  let (d, _) := elabCited "Wow![@a] end"
  t "cite: an image opener no image follows sets its '!' before the citation it holds"
    ((citesOf d).map (·.1.cmd) == #[.paren] && hasStr (Ir.blocksText d.body) "Wow!")
  let (d, _) := elabCited "[@a, see [here](https://example.org/a;b)] end"
  t "cite: a link in a note, its destination's ';' included, stays in its citation"
    (keysOf d == ["a"] && Ir.anyInline (· matches .link "https://example.org/a;b" _)
      (d.body.flatMap fun b => match b with | .para xs => xs | _ => #[]))
  -- A bracketed citation sets its notes as content; an author-in-text one's suffix stays text.
  let (d, ds) := elabCited "[*see* @a] and [@a, `code`] and @a [*p.* 3]"
  t "cite: a formatted note sets as content, and only an author-in-text suffix is named"
    ((ds.filter (·.subject == some "md:cite-note")).size == 1 &&
      Ir.anyInline (· matches .styled .emph _)
        (d.body.flatMap fun b => match b with | .para xs => xs | _ => #[]))
  for md in ["[see @a and @b] end", "[@a, see @b] end", "[see [@a] and @b] end", "[@a [@b]] end",
      "[see @a [p. 3; @b]] end", "[x @a [@b]] end"] do
    let (_, ds) := elabCited md
    t s!"cite: {repr md}, a citation inside another's note, is named once"
      ((ds.filter (·.subject == some "md:cite-nested")).size == 1)
  let (_, ds) := elabCited "[see @a [p. 3]] end"
  t "cite: a citation's own locator in its suffix names no nested citation"
    (!ds.any (·.subject == some "md:cite-nested"))
  let (d, ds) := elabCited "[see @{c,d}; @a] end"
  t "cite: a key natbib cannot carry sets as its text, the group's other works cited"
    (keysOf d == ["a"] && hasStr (Ir.blocksText d.body) "@{c,d}" &&
      ds.any (·.subject == some "md:cite-key"))
  let (d, ds) := elabCited "An image ![see @a here](img.svg) end."
  t s!"cite: a citation in an image's text alternative cites, naming nothing ({repr (ds.map (·.code))})"
    (!ds.any (·.kind == .W0392) &&
      (match (Ir.foldBlocks (fun out _ => out) (fun out x => match x with
        | .image _ _ alt => out ++ alt.cites.map (·.2)
        | _ => out) #[] d.body) with
       | #[ks] => ks == #["a"]
       | _ => false))
  -- An included file reads citations where the TeX document's markdown package says to.
  let part := "Thanks to @octocat and [@a].\n"
  for (pre, opts, cites) in [("\\usepackage{markdown}", "", false),
      ("\\usepackage{markdown}", "[citations]", true)] do
    let (d, ds) := includedDoc "h.tex" (dvDoc (pre ++ "\n") s!"\\markdownInput{opts}\{p.md}")
      [("p.md", "p.md", part)]
    t s!"include: under {pre} and \\markdownInput{opts}, the file reads citations: {cites}"
      (!(citesOf d).isEmpty == cites &&
        (cites || (hasStr (Ir.blocksText d.body) "@octocat" && !ds.any (·.kind == .W0351))))
  -- Citations are read only where a bibliography takes them: a document and its own declaration.
  let (d, ds) := elabMd "Thanks to @octocat and [@a].\n"
  t "cite: a document declaring no bibliography keeps its '@' text, as Pandoc sets it uncited"
    ((citesOf d).isEmpty && hasStr (Ir.blocksText d.body) "@octocat and [@a]" &&
      !ds.any (·.kind == .W0351))
  let (d, ds) := elabCode "m.py" "def f():\n    \"\"\"Decorate it with @property, or call @staticmethod.\"\"\"\n"
  t "cite: a Python docstring's '@' stays text"
    ((citesOf d).isEmpty && hasStr (Ir.blocksText d.body) "@property" && !ds.any (·.kind == .W0351))
  let (d, ds) := elabCode "M.lean" "/-- Uses @List.map on each element. -/\ndef f := 1\n"
  t "cite: a Lean docstring's '@' stays text"
    ((citesOf d).isEmpty && hasStr (Ir.blocksText d.body) "@List.map" && !ds.any (·.kind == .W0351))
  -- The twin spells each citation in Pandoc's syntax, and reads back to the same IR.
  for (md, spelled) in mdCiteTwinCases do
    let (d, _) := elabCited md
    let twin := MarkdownDoc.emit d
    let (back, _) := elabMd twin
    t s!"twin: {repr md} spells {repr spelled} ({repr twin})" (hasStr twin spelled)
    t s!"twin: {repr md} reads back to its IR" (back.body == d.body)
  for (tex, spelled) in texTwinCases do
    let (d, _) := elabStr (worksTex tex)
    let twin := MarkdownDoc.emit d
    t s!"twin: tex's {tex} spells {repr spelled} ({repr twin})" (hasStr twin spelled)
    t s!"twin: tex's {tex} reads back to its citations" (citesOf (elabMd twin).1 == citesOf d)
  for tex in ["\\citet{a,b}", "\\Citep{a}", "\\citeauthor{a}", "\\citep*{a}"] do
    let (d, _) := elabStr (worksTex tex)
    let twin := MarkdownDoc.emit d
    t s!"twin: tex's {tex}, which Pandoc's syntax cannot spell, sets as its marks and declares no \
bibliography ({repr twin})" ((citesOf (elabMd twin).1).isEmpty && !hasStr twin "bibliography:")
  -- A numbered list counts in citation order, so a twin that cannot keep every citation in place
  -- sets them all as their marks, linked to the entries it writes.
  let numbered (body : String) : String := dvDoc "\\usepackage[numbers]{natbib}\n"
    (body ++ "\n\n\\bibliographystyle{unsrtnat}\n\\bibliography{works.bib}")
  for tex in inkTwinCases do
    let (d, _) := bibBuild (numbered tex) #[("works.bib", worksBib)]
    let twin := MarkdownDoc.emit d
    let (back, _) := mdBibBuild twin #[("works.bib", worksBib)]
    t s!"twin: {repr tex}'s twin sets as its marks and reads back to its text ({repr twin})"
      (!hasStr twin "bibliography:" && hasStr twin "<a name=\"ref-a\"></a>" &&
        inkText back.body == inkText d.body)
  let (d, _) := bibBuild (numbered "Body\\footnote{See \\citet{a}.} and \\citep{b}.")
    #[("works.bib", worksBib)]
  let twin := MarkdownDoc.emit d
  let (back, _) := mdBibBuild twin #[("works.bib", worksBib)]
  t s!"twin: a citation in a footnote is spelled, the note read back where its mark stands, so \
the list keeps its numbers ({repr twin})"
    (hasStr twin "bibliography:" && hasStr twin "[^1]: See @{a}." &&
      inkText back.body == inkText d.body)
  let (d, _) := bibBuild (numbered "\\citep{a} and \\citep{b}.\n\n\\bibliography{works.bib}")
    #[("works.bib", worksBib)]
  t "twin: a document with two lists sets its citations as their marks"
    (!hasStr (MarkdownDoc.emit d) "bibliography:")
  let (d, _) := bibBuild (numbered "\\citep{b} and \\citet{a}.") #[("works.bib", worksBib)]
  let twin := MarkdownDoc.emit d
  t s!"twin: a declared list's entries stay readable in its division, the bibliography declared \
last ({repr twin})"
    (hasStr twin "::: {#refs}\n<!--\n[1] Bo Birch" && hasStr twin "\n---\nbibliography: works.bib" &&
      twin.endsWith "---\n")
  let (d, _) := mdBibBuild (worksMeta ++ "# A placeholder note\n\nText [@a].\n") #[("works.bib", worksBib)]
  t "twin: a cited document's twin still opens on its title, as llms.txt reads one"
    ((MarkdownDoc.emit d).startsWith "# A placeholder note")
  let (d, _) := elabCited "| Works |\n| --- |\n| [@a, x \\| y] |"
  let twin := MarkdownDoc.emit d
  t s!"twin: a citation's note in a table cell keeps its pipe escaped once ({repr twin})"
    (hasStr twin "[@a, x \\| y]" && (elabMd twin).1.body == d.body)
  let relative := World.ToolPath.relative
  t "twin: the bibliography is named from where the twin is written"
    (relative "out" "sub/refs.bib" == some "../sub/refs.bib" &&
      relative "sub" "sub/refs.bib" == some "refs.bib" &&
      relative "." "refs.bib" == some "refs.bib" && relative "/a" "refs.bib" == none)
  let (d, _) := elabCited "Write x\\@a and \\@b and [x@y.org], citing [@a]."
  let twin := MarkdownDoc.emit d
  t s!"twin: an at sign that would open a citation is escaped, an e-mail's is not ({repr twin})"
    (hasStr twin "\\@b" && hasStr twin "x@a" && citesOf (elabMd twin).1 == citesOf d)
  let (d, _) := elabMd "Thanks to @octocat.\n"
  t "twin: a document with no bibliography writes its '@' as it stands"
    (hasStr (MarkdownDoc.emit d) "to @octocat." && !hasStr (MarkdownDoc.emit d) "---")
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
  let (linked, _) := mdBibBuild (worksMeta ++ "See [the notes [@a]](https://example.org/x).\n") bibs
  let linkedHtml := docHtmlOf linked
  t "html: a citation inside a link's text sets as its text, no anchor nested in the link"
    (hasStr linkedHtml "href=\"https://example.org/x\"" && !hasStr linkedHtml "href=\"#ref-a\"")
  -- Both backends from the one IR value: the page and the web page set the same citation ink.
  match ← serifFacesSet with
  | none => t "cite: the serif faces load" false
  | some fonts =>
    let pageText := String.join ((bodyLines (layoutOf fonts md)).toList.map (lineText ·))
    for ink in ["[1]", "Ash [2]", "[?]"] do
      t s!"backends: the page and the web page both set {repr ink}"
        (hasStr pageText ink && hasStr (webText md) ink)
  -- The twin of a cited document declares its bibliography and reads back to the same text.
  let (back, _) := mdBibBuild (MarkdownDoc.emit md) bibs
  t "twin: a cited document's twin, rebuilt with its bibliography, sets the same text"
    (Ir.blocksText back.body == Ir.blocksText md.body && listOf back == listOf md)
  for n in ["md-cite", "bibliography", "md-cite-include"] do
    let (d, _) ← goldenDoc n
    let (back, _) := mdBibBuild (MarkdownDoc.emit d) (← corpusBibs d)
    t s!"twin: {n}'s twin, rebuilt with its bibliography, sets its text"
      (!(listOf d).isEmpty && Ir.blocksText back.body == Ir.blocksText d.body)
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
  let lists (d : Ir.Doc) : Nat := Ir.foldBlocks (fun n b => if b matches .bibliography .. then n + 1
    else n) (fun n _ => n) 0 d.body
  let styleOf (d : Ir.Doc) : Option String := Ir.bibStyleName d
  let subjectsOf (ds : Array Diag) : Array String := ds.filterMap (·.subject)
  -- A metadata block is read only at the first line, as Pandoc's CommonMark reader reads one.
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
  let (d, _) := mdBibBuild "Text [@a].\n\n---\nbibliography: works.bib\n---\n" bibs
  t "metadata: a block closing the document after a blank line declares the bibliography, as \
Pandoc reads one" (listOf d == #["a"] && !hasStr (Ir.blocksText d.body) "bibliography")
  let (_, ds) := mdBibBuild "---\nbibliography: works.bib\nlink-citations: maybe\n---\n\nText [@a].\n"
    bibs
  t "metadata: a link-citations value neither true nor false is named"
    (ds.any (·.subject == some "md:meta:link-citations"))
  -- YAML's spellings of a key, a path and a list of paths.
  for (form, src) in [("a quoted path", "bibliography: 'works.bib'"),
      ("a double-quoted path", "bibliography: \"works.bib\""),
      ("a double-quoted key", "\"bibliography\": works.bib"),
      ("a single-quoted key", "'bibliography' : works.bib"),
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
  let (_, ds) := elabMd ("---\nbibliography: works.bib\ntitle: An invented note\n" ++
    "author:\n  - Placeholder Person\ndraft_: true\ncsl: chicago.csl\nlink-citations: false\n" ++
    "keywords: [one, two]\ntitle: A second title\n---\n\nText.\n")
  t s!"metadata: each key not read is named once, a repeated one at its first spelling, an \
underscore key ignored ({repr (subjectsOf ds)})"
    ((subjectsOf ds).filter (·.startsWith "md:meta") ==
      #["md:meta-twice:title", "md:meta:csl", "md:meta:keywords"])
  t "metadata: a CSL style's help names the BibTeX style key"
    (ds.any fun d => d.subject == some "md:meta:csl" && d.help.any (hasStr · "biblio-style"))
  t "metadata: link-citations false is named as the link it does not drop"
    (ds.any (·.subject == some "md:link-citations"))
  let (d, ds) := elabMd "---\nnocite: '@a'\nbiblio-style: unsrtnat\n---\n\nText.\n"
  t "metadata: a citation key with no bibliography to act on is named"
    ((subjectsOf ds).contains "md:meta:nocite" && (subjectsOf ds).contains "md:meta:biblio-style" &&
      lists d == 0)
  let (_, ds) := mdBibBuild "---\nbibliography: works.json\n---\n\nText [@a].\n" bibs
  t "metadata: a bibliography in another format is named, not read"
    (ds.any (·.subject == some "md:meta:bibliography:works.json"))
  let (d, _) := mdBibBuild "---\nbibliography: works.bib\n---\n\nText cites nothing.\n" bibs
  t "metadata: a document citing nothing sets no list, as Pandoc's citation processing sets none"
    (lists d == 0)
  -- Where the list stands: the first `{#refs}` division, else the end under its declared title.
  let (d, _) := mdBibBuild ("---\nbibliography: works.bib\nreference-section-title: '*Works* cited'\n" ++
    "---\n\nText [@a].\n") bibs
  t "metadata: the list sets at the end under its declared title, read as markdown"
    (match d.body.toList.reverse with
      | .bibliography _ _ _ :: .section _ _ _ title :: _ =>
        Ir.plainText title == "Works cited" && title.any (· matches .styled .emph _)
      | _ => false)
  let (d, _) := mdBibBuild ("---\nbibliography: works.bib\nreference-section-title: Works cited\n" ++
    "---\n\nText [@a].\n\n::: {#refs}\n## Sources\n:::\n\nAfter the list.\n") bibs
  t "metadata: a {#refs} division places the list after its own blocks, the title unset"
    (match d.body.toList with
      | [.para _, .section _ _ _ h, .bibliography _ _ _, .para after] =>
        Ir.plainText h == "Sources" && Ir.plainText after == "After the list."
      | _ => false)
  let (d, ds) := mdBibBuild (worksMeta ++ "Text [@a].\n\n::: {#refs .wide}\n:::\n\n::: {#refs}\n:::\n\n\
After.\n") bibs
  t "metadata: a {#refs} division with other attributes places the list, the attributes named"
    (lists d == 1 && ds.any (·.subject == some "md:refs-attrs"))
  t "metadata: a second {#refs} division holds no list and is named"
    (ds.any (·.subject == some "md:refs-second") &&
      (match d.body.toList.reverse with
        | .para after :: .bibliography _ _ _ :: _ => Ir.plainText after == "After."
        | _ => false))
  let (_, ds) := elabMd "Text.\n\n::: {#refs}\n:::\n"
  t "metadata: a {#refs} division with no bibliography is named" (ds.any (·.subject == some "md:refs"))
  -- An included file's metadata: its nocite joins the document's, its bibliography is the document's.
  let (raws, ds) := Md.readIncluded "part.md" "---\nbibliography: works.bib\nnocite: '@b'\n---\n\nText.\n"
    true
  t "metadata: an included file's bibliography is named, its nocite read"
    (ds.any (·.subject == some "md:meta:bibliography") &&
      raws.any (· matches .ctrl "nocite" _) && !raws.any (· matches .ctrl "markdown bibliography" _))

end Tests.MarkdownCite
