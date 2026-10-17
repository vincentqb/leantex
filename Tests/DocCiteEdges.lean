module

public import Tests.LeanCite

public section

open LeanTex.Core LeanTex.Cli

/-! Link reference definitions as CommonMark reads them, in a document and in a Lean docstring,
where they stand ahead of the definitions doc-gen4 appends for the keys it cites; its labels
matched as links match them; and a bracket before braces in a docstring. -/

namespace Tests.DocCiteEdges

mutual

/-- The text a page's node carries, after `acc`. -/
def nodeText (acc : String) (n : Html.Node) : String :=
  match n with
  | .text s => acc ++ s
  | .elem _ _ kids => nodesText acc kids.toList
  | .style _ | .script _ _ => acc

def nodesText (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => nodesText (nodeText acc n) rest

end

mutual

/-- Each element of a page's node with an attribute named `key`: the attribute's value and the
element's text, in order. -/
def nodeAttrs (key : String) (out : Array (String × String)) (n : Html.Node) :
    Array (String × String) :=
  match n with
  | .elem _ attrs kids =>
    let out := match attrs.find? (·.1 == key) with
      | some (_, v) => out.push (v, nodesText "" kids.toList)
      | none => out
    nodesAttrs key out kids.toList
  | _ => out

def nodesAttrs (key : String) (out : Array (String × String)) :
    List Html.Node → Array (String × String)
  | [] => out
  | n :: rest => nodesAttrs key (nodeAttrs key out n) rest

end

/-- The links a document's page sets, in order: each one's target and text. -/
def linksOf (d : Ir.Doc) : Array (String × String) := nodesAttrs "href" #[] (docNodesOf d).toList

/-- The text alternatives a document's page sets on its images, in order. -/
def altsOf (d : Ir.Doc) : Array String :=
  (nodesAttrs "aria-label" #[] (docNodesOf d).toList ++ nodesAttrs "alt" #[] (docNodesOf d).toList).map (·.1)

/-- A markdown document's links. -/
def mdLinks (src : String) : Array (String × String) := linksOf (elabMd src).1

/-- A markdown document's text. -/
def mdText (src : String) : String := Ir.blocksText (elabMd src).1.body

/-- Invented entries whose keys differ only in case, and one other. -/
def caseBib : String :=
  "@book{Ash2001, author = {Ash, Ada}, title = {Upper Notes}, publisher = {Example Press}, \
year = {2001}}\n@book{ash2001, author = {Ash, Abe}, title = {Lower Notes}, publisher = {Example Press}, \
year = {2001}}\n@book{birch2002, author = {Birch, Bo}, title = {Beta Notes}, publisher = {Example Press}, \
year = {2002}}\n"

/-- A Lean page whose module doc is `doc`, reading citations into `caseBib`. -/
def casePage (doc : String) : Ir.Doc × Array Diag :=
  leanCiteBuild "F.lean" ("/-! " ++ doc ++ " -/\n\ndef x := 1\n") #[("refs.bib", caseBib)]

/-- A document's link reference definitions set nothing and give their labels' links their
destinations, before or after the link, case-insensitively. -/
def documentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t s!"md refs: a definition after its link gives it its destination \
({mdLinks "See [foo].\n\n[foo]: /url \"title\"\n"})"
    (mdLinks "See [foo].\n\n[foo]: /url \"title\"\n" == #[("/url", "foo")] &&
      !hasStr (mdText "See [foo].\n\n[foo]: /url \"title\"\n") "/url")
  t "md refs: a definition before its links, matched case-insensitively, in each form"
    (mdLinks "[Foo   Bar]: <my url>\n\n[foo bar], [text][FOO BAR] and [foo bar][].\n" ==
      #[("my url", "foo bar"), ("my url", "text"), ("my url", "foo bar")])
  t "md refs: a label no definition holds stays text"
    (mdLinks "See [bar].\n\n[foo]: /url\n" == #[] && hasStr (mdText "See [bar].\n\n[foo]: /url\n") "[bar]")
  t "md refs: the first definition of a label stands"
    (mdLinks "[foo]\n\n[foo]: /first\n[FOO]: /second\n" == #[("/first", "foo")])
  t "md refs: a definition in a block quote defines for the document"
    (mdLinks "[foo]\n\n> [foo]: /url\n" == #[("/url", "foo")])
  t s!"md refs: under definitions alone a setext underline is the paragraph's text \
({repr (mdText "[foo]: /url\n===\n[foo]\n")})"
    (mdLinks "[foo]: /url\n===\n[foo]\n" == #[("/url", "foo")] &&
      hasStr (mdText "[foo]: /url\n===\n[foo]\n") "===")
  t "md refs: definitions open a setext heading's lines, the rest its text"
    (mdLinks "[foo]: /url\nbar\n===\n[foo]\n" == #[("/url", "foo")] &&
      (elabMd "[foo]: /url\nbar\n===\n[foo]\n").1.body.any (· matches .section ..))
  t s!"md refs: a reference image is an image under its definition's source \
({altsOf (elabMd "![a chart][pic]\n\n[pic]: chart.svg\n").1})"
    ((altsOf (elabMd "![a chart][pic]\n\n[pic]: chart.svg\n").1).contains "a chart" &&
      !hasStr (mdText "![a chart][pic]\n\n[pic]: chart.svg\n") "[pic]")
  t "md refs: a full reference whose label no definition holds is no shortcut either"
    (mdLinks "[foo][bar][baz]\n\n[baz]: /url\n" == #[("/url", "bar")])
  t "md refs: a title past which the line goes on leaves the definition its destination"
    (mdLinks "[foo]: /url\n\"title\" ok\n\n[foo]\n" == #[("/url", "foo")] &&
      hasStr (mdText "[foo]: /url\n\"title\" ok\n\n[foo]\n") "title")

/-- A docstring's own link reference definitions stand ahead of the ones doc-gen4 appends for the
keys it cites: its labels link to them, a key's label among them. -/
def docstringChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (d, _) := Tests.LeanCite.page "See [Docs].\n\n[Docs]: https://example.org/docs"
  t s!"lean refs: a docstring's definition sets nothing and links its label \
({linksOf d}, {repr (Ir.blocksText d.body)})"
    (linksOf d == #[("https://example.org/docs", "Docs")] &&
      !hasStr (Ir.blocksText d.body) "example.org")
  for doc in ["See [ash2001].\n\n[ash2001]: https://example.org/a",
      "See [ash2001].\n\n[ASH2001]: https://example.org/a"] do
    let (d, _) := Tests.LeanCite.page doc
    t s!"lean refs: a docstring's definition of a key's label links it there, no citation \
({repr doc}: {keysOf d}, {linksOf d})"
      (keysOf d == [] && linksOf d == #[("https://example.org/a", "ash2001")])
  let (d, _) := Tests.LeanCite.page "See [the notes][docs] and [ash2001].\n\n[docs]: https://example.org/d"
  t s!"lean refs: a full reference to a docstring's definition is a link beside a citation \
({keysOf d}, {linksOf d})"
    (keysOf d == ["ash2001"] && (linksOf d).contains ("https://example.org/d", "the notes"))

/-- doc-gen4 cites a bracket before braces as any other, and a label matching a key it cites
case-insensitively links to that key's entry under the label's own text. -/
def caseChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (d, _) := Tests.LeanCite.page "See [ash2001]{x} here."
  t s!"lean cite: a bracket before braces cites, the braces text \
({keysOf d}, {repr (inkText d.body)})"
    (keysOf d == ["ash2001"] && hasStr (inkText d.body) "{x} here")
  let (d, _) := Tests.LeanCite.page "Cites [ash2001] and [ASH2001]."
  t s!"lean cite: a label alike but in case links to the key's entry under its own text \
({keysOf d}, {linksOf d})"
    ((keysOf d).all (· == "ash2001") && (linksOf d).contains ("#ref-ash2001", "ASH2001") &&
      !hasStr (inkText d.body) "[ASH2001]")
  let (d, _) := Tests.LeanCite.page "Only [ASH2001] here."
  t s!"lean cite: with no bracket spelling the key, a label alike in case cites nothing \
({keysOf d})"
    (keysOf d == [] && hasStr (inkText d.body) "[ASH2001]")
  let (d, _) := casePage "Cites [Ash2001] and [ash2001]."
  t s!"lean cite: two keys alike but in case each cite as written ({keysOf d})"
    (keysOf d == ["Ash2001", "ash2001"])
  let (d, _) := casePage "Cites [Ash2001], [ash2001] and [ASH2001]."
  t s!"lean cite: a label alike in case to two keys links to the first the text cites \
({linksOf d})"
    ((linksOf d).contains ("#ref-Ash2001", "ASH2001"))

/-- A docstring's math span is md4c's: a formula whose source no link, citation or emphasis reads,
between dollars no letter or digit flanks on their outer sides. -/
def mathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (d, ds) := Tests.LeanCite.page "Math $f[ash2001]$ and $$g[birch2002]$$ and [roe2020]."
  let html := docHtmlOf d
  t s!"lean math: a bracket inside a formula cites nothing, the formula set as one \
({keysOf d}, {repr (ds.map (·.code))})"
    (keysOf d == ["roe2020"] && hasStr html "<math" && !ds.any (·.kind == .W0392))
  for (doc, keys) in [("Price x$[ash2001]$ cites.", ["ash2001"]),
      ("Cost $[ash2001]$x cites.", ["ash2001"]), ("A \\$[ash2001] cites.", ["ash2001"]),
      ("Runs $$$[ash2001]$$$ cite.", ["ash2001"]), ("Mixed $$a$ [ash2001]$ cites.", ["ash2001"])] do
    let (d, _) := Tests.LeanCite.page doc
    t s!"lean math: {repr doc} sets no formula there ({keysOf d})" (keysOf d == keys)
  let (d, _) := Tests.LeanCite.page "See $[a](https://example.org)$ here."
  t s!"lean math: an inline link inside a formula is the formula's text ({linksOf d})"
    (!(linksOf d).any (·.1 == "https://example.org"))
  let (d, _) := Tests.LeanCite.page "See [a $b](https://example.org) c$ here."
  t s!"lean math: a link read first keeps a dollar inside it ({linksOf d})"
    ((linksOf d).contains ("https://example.org", "a $b") && !hasStr (docHtmlOf d) "<math")
  let (d, _) := Tests.LeanCite.page "See *a $b* c$ here."
  t s!"lean math: emphasis closing first takes the dollar it passes ({repr (docHtmlOf d)})"
    (hasStr (docHtmlOf d) "<em>a $b</em>" && !hasStr (docHtmlOf d) "<math")
  let (d, ds) := Tests.LeanCite.page "Odd $\\unknownmacro{x}$ here."
  t s!"lean math: a formula holding a control the math model does not read sets as its source, \
named ({repr (ds.map (·.code))})"
    (hasStr (Ir.blocksText d.body) "$\\unknownmacro{x}$" &&
      ds.any fun x => x.kind == .W0392 && x.subject == some "md:docstring-math")
  t "md math: a markdown document's dollars stay text"
    (hasStr (mdText "Price $x$ here.\n") "$x$" && !hasStr (docHtmlOf (elabMd "Price $x$ here.\n").1) "<math")

end Tests.DocCiteEdges
