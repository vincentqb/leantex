module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-! A markdown image's citations in its text alternative, and footnotes as Pandoc and GFM spell
them. -/

namespace Tests.MdNoteEdges

mutual

/-- Each value a page's node gives an attribute named `key`, in order. -/
def nodeAttrValues (key : String) (out : Array String) (n : Html.Node) : Array String :=
  match n with
  | .elem _ attrs kids =>
    let out := match attrs.find? (·.1 == key) with
      | some (_, v) => out.push v
      | none => out
    nodesAttrValues key out kids.toList
  | _ => out

def nodesAttrValues (key : String) (out : Array String) : List Html.Node → Array String
  | [] => out
  | n :: rest => nodesAttrValues key (nodeAttrValues key out n) rest

end

/-- The names a document's page gives its images, as assistive technology reads them. -/
def imageNames (d : Ir.Doc) : Array String :=
  nodesAttrValues "aria-label" #[] (docNodesOf d).toList ++ nodesAttrValues "alt" #[] (docNodesOf d).toList

/-- A citation in an image's text alternative cites its work where the image stands, the
alternative reads its style's text, and the twin spells it back. -/
def altChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := worksMeta ++ "![A chart from @a and [@b, p. 3]](chart.svg)\n\nText cites [@roe2020].\n"
  let (d, ds) := mdBibBuild src #[("works.bib", worksBib)]
  t s!"md alt: a citation in an image's alternative reads as its style sets it ({imageNames d})"
    ((imageNames d).contains "A chart from Ash [2001] and [Birch, 2002, p. 3]")
  let listed := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map (·.key)
    | _ => out) (fun out _ => out) #[] d.body
  t s!"md alt: an alternative's citations list their works, naming nothing ({listed}, \
{repr (ds.map (·.code))})"
    (["a", "b", "roe2020"].all listed.contains && !ds.any (·.kind == .W0392) &&
      !ds.any (·.kind == .W0351))
  let twin := MarkdownDoc.emit d
  t s!"md alt: the twin spells an alternative's citations back ({repr twin})"
    (hasStr twin "![A chart from @a and [@b, p. 3]](chart.svg)")
  let numbered := "---\nbibliography: works.bib\nbiblio-style: unsrtnat\n---\n\nText cites [@roe2020].\n\n\
![See @a](chart.svg)\n"
  let (d, _) := mdBibBuild numbered #[("works.bib", worksBib)]
  let order := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map (·.key)
    | _ => out) (fun out _ => out) #[] d.body
  t s!"md alt: an alternative's citation numbers where its image stands ({order})"
    (order == #["roe2020", "a"])
  let (d, _) := elabMd (worksMeta ++ "![See @ghost here](chart.svg)\n")
  t s!"md alt: with no list read, an alternative's citation shows its mark ({imageNames d})"
    ((imageNames d).contains "See ? here")
  let host := "\\documentclass{article}\n\\usepackage[citations]{markdown}\n\\begin{document}\n\
\\markdownInput{p.md}\n\\bibliographystyle{plainnat}\n\\bibliography{works}\n\\end{document}\n"
  let (raws, ds0) := Surface.read .tex "h.tex" host
  let (executed, readDs) := (Elab.executeInputs
    (mdFileReader [("p.md", "p.md", "![A chart from @a](chart.svg)\n")]) "h.tex" raws).run #[]
  let prepared := Elab.prepareExecuted "h.tex" executed
  let (doc, _, spans) := Elab.runPrepared "h.tex" prepared (ds0 ++ readDs) (fun _ _ => {})
  let (doc, _) := Bib.resolve "h.tex" prepared #[("works", worksBib)] doc spans.cites
  t s!"md alt: an included file's alternative cites as a document's ({imageNames doc})"
    ((imageNames doc).any fun n => hasStr n "A chart from Ash [" && !hasStr n "@" && !hasStr n "\\")
  let (d, _) := elabStr "\\documentclass{article}\n\\begin{document}\n\
\\includegraphics[alt={See \\cite{a} here}]{chart.svg}\n\\end{document}\n"
  t s!"tex alt: a TeX image's alternative reads as it did, its source as written ({imageNames d})"
    ((imageNames d).contains "See \\cite {a} here")

/-- A markdown document's twin, its footnotes' definitions after its body. -/
def twinOf (src : String) : String := MarkdownDoc.emit (elabMd src).1

/-- Footnotes as Pandoc's manual spells them: a reference `[^label]` the text defines takes the
definition's paragraphs, a definition at the top level after a blank line or another definition,
its label matched exactly. -/
def noteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t s!"md notes: a reference takes its definition's text ({repr (twinOf "Text[^a] here.\n\n[^a]: A note.\n")})"
    (hasStr (twinOf "Text[^a] here.\n\n[^a]: A note.\n") "Text[^1] here." &&
      hasStr (twinOf "Text[^a] here.\n\n[^a]: A note.\n") "[^1]: A note.")
  let two := "One[^x] two[^y].\n\n[^x]: First.\n[^y]: Second\n    wrapped.\n\n    Another paragraph.\n"
  t s!"md notes: definitions one after another, a paragraph indented in one ({repr (twinOf two)})"
    (hasStr (twinOf two) "[^1]: First." &&
      hasStr (twinOf two) "[^2]: Second wrapped.\\\n    Another paragraph.")
  t "md notes: labels match exactly, and a reference no definition holds stays text"
    (hasStr (twinOf "A[^K] b[^k].\n\n[^K]: Upper.\n") "A[^1] b\\[^k\\].")
  let (d, _) := elabMd "Text[^a] here.\n[^a]: Not a note.\n"
  t s!"md notes: a definition right after a paragraph's line is that paragraph's text \
({repr (Ir.blocksText d.body)})"
    (hasStr (Ir.blocksText d.body) "[^a]: Not a note.")
  let (d, _) := elabMd "- item[^a]\n\n  [^a]: Inside a list.\n"
  t s!"md notes: a definition inside a list item is the item's text ({repr (Ir.blocksText d.body)})"
    (hasStr (Ir.blocksText d.body) "[^a]: Inside a list.")
  let (_, ds) := elabMd "Text[^a].\n\n[^a]: Once.\n\n[^a]: Twice.\n\n[^b]: Never named.\n\n[^c]: ```\n"
  t s!"md notes: a second definition and one nothing names are named ({repr (ds.map (·.subject))})"
    (ds.any (·.subject == some "md:note-again") && ds.any (·.subject == some "md:note-unused"))
  let (_, ds) := elabMd "Text[^a].\n\n[^a]: A paragraph.\n\n    - and a list\n"
  t s!"md notes: a block other than a paragraph in a note is named ({repr (ds.map (·.subject))})"
    (ds.any (·.subject == some "md:note-block"))

/-- A TeX document's footnote holding a citation: its twin spells the citation in Pandoc's syntax,
which reads back where the note stands, so a numbered list keeps its order. -/
def noteTwinChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := "\\documentclass{article}\n\\usepackage{natbib}\n\\begin{document}\n\
A claim.\\footnote{See \\citet{b} and \\citep{roe2020}.} More text \\citep{a}.\n\
\\bibliographystyle{unsrtnat}\n\\bibliography{works}\n\\end{document}\n"
  let (d, _) := bibBuild src #[("works", worksBib)]
  let twin := MarkdownDoc.emit d
  t s!"tex note twin: a note's citations are spelled ({repr twin})"
    (hasStr twin "[^1]: See @b and [@roe2020]." && hasStr twin "More text [@a].")
  let (back, _) := mdBibBuild twin #[("works.bib", worksBib)]
  let order (x : Ir.Doc) : Array String := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map (·.key)
    | _ => out) (fun out _ => out) #[] x.body
  t s!"tex note twin: read back, the list numbers as the document's ({order d}, {order back})"
    (order d == #["b", "roe2020", "a"] && order back == order d && MarkdownDoc.emit back == twin)

end Tests.MdNoteEdges
