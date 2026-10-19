module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-! A markdown image's citations in its text alternative, and footnotes as Pandoc's manual spells
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
    ((imageNames d).contains "A chart from Ash [2001] and [Birch, 2002, p.\u00a03]")
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
  for (body, name) in [("![*see [@a]* here](chart.svg)", "see [Ash, 2001] here"),
      ("![see [link @a](https://example.org)](chart.svg)", "see link Ash [2001]")] do
    let (d, _) := mdBibBuild (worksMeta ++ body ++ "\n") #[("works.bib", worksBib)]
    t s!"md alt: a citation inside emphasis or a link in an alternative cites ({imageNames d})"
      ((imageNames d).contains name && !(imageNames d).any (hasStr · "\\"))
  let (one, _) := mdBibBuild (worksMeta ++ "One ![see [@a]](chart.svg) end.\n") #[("works.bib", worksBib)]
  let (two, _) := mdBibBuild (worksMeta ++ "Two ![](chart.svg) and ![see [@a]](chart.svg) end.\n")
    #[("works.bib", worksBib)]
  t s!"md alt: an image with no alternative takes none from the next ({imageNames two})"
    (((imageNames two).filter (hasStr · "see")).size == ((imageNames one).filter (hasStr · "see")).size)
  let (d, ds) := mdBibBuild (worksMeta ++ "Only ![see [@a]](chart.svg) here.\n") #[("works.bib", worksBib)]
  let listed := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map (·.key)
    | _ => out) (fun out _ => out) #[] d.body
  t s!"md alt: a document citing only in an alternative lists the work ({listed})"
    (listed == #["a"] && !ds.any (·.kind == .W0351))
  let (d, _) := leanCiteBuild "F.lean"
    "/-! A chart ![see [@roe2020]](chart.svg) here. -/\n\ndef x := 1\n" #[("refs.bib", worksBib)]
  t s!"lean alt: a docstring's image cites in its alternative ({imageNames d})"
    ((imageNames d).any fun n => hasStr n "see " && !hasStr n "\\" && !hasStr n "@")
  let (d, _) := mdBibBuild (worksMeta ++ "Nested ![outer ![inner [@b]](chart.svg) text](chart.svg) end.\n")
    #[("works.bib", worksBib)]
  t s!"md alt: a nested image's alternative stands in the one holding it, its work cited ({imageNames d})"
    ((imageNames d).contains "outer inner [Birch, 2002] text")
  let (d, _) := leanCiteBuild "F.lean"
    "/-! A chart ![see [the notes][roe2020]](chart.svg) here. -/\n\ndef x := 1\n" #[("refs.bib", worksBib)]
  t s!"lean alt: a docstring alternative's link to an entry keeps its words, no mark ({imageNames d})"
    ((imageNames d).contains "see the notes")
  let mixed := worksMeta ++ "![see [@a; -@b, p. 2]](chart.svg)\n\nText cites [@roe2020].\n"
  let (d, _) := mdBibBuild mixed #[("works.bib", worksBib)]
  let twin := MarkdownDoc.emit d
  t s!"md alt: the twin spells an alternative's mixed group and keeps the body's ({repr twin})"
    (hasStr twin "[@a; -@b, p. 2]" && hasStr twin "Text cites [@roe2020].")

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
  for src in ["- item[^a]\n\n  [^a]: Inside a list.\n", "> quote[^a]\n>\n> [^a]: Inside a list.\n",
      "- outer\n\n  > quote[^a]\n  >\n  > [^a]: Inside a list.\n"] do
    let (d, ds) := elabMd src
    t s!"md notes: a definition inside a list item or a block quote defines its note, as Pandoc's \
({repr src}: {repr (pageText d)})"
      (hasStr (pageText d) "Inside a list." && !hasStr (pageText d) "[^a]" &&
        (Ir.footnotesOf d.body).size == 1 && !ds.any (·.subject == some "md:note-unused"))
  let (_, ds) := elabMd "Text[^a].\n\n[^a]: Once.\n\n[^a]: Twice.\n\n[^b]: Never named.\n\n[^c]: ```\n"
  t s!"md notes: a second definition and one nothing names are named ({repr (ds.map (·.subject))})"
    (ds.any (·.subject == some "md:note-again") && ds.any (·.subject == some "md:note-unused"))
  let (_, ds) := elabMd "Text[^a].\n\n[^a]: A paragraph.\n\n    - and a list\n"
  t s!"md notes: a block other than a paragraph in a note is named ({repr (ds.map (·.subject))})"
    (ds.any (·.subject == some "md:note-block"))
  let lazy := "Text[^1] here.\n\n[^1]: A long note that\nwraps without indent.\n\nAfter.\n"
  let (_, ds) := elabMd lazy
  t s!"md notes: a note's paragraph takes a line left unindented, as Pandoc's ({repr (twinOf lazy)})"
    (hasStr (twinOf lazy) "[^1]: A long note that wraps without indent." && !ds.any (·.kind == .E0390))
  let dup := "Text[^a].\n\n[^a]: Once.\n\n[^a]: Twice.\n"
  t s!"md notes: a label's last definition stands, as Pandoc's ({repr (twinOf dup)})"
    (hasStr (twinOf dup) "[^1]: Twice." && !hasStr (twinOf dup) "Once")
  let blocks := "Text[^a].\n\n[^a]: Para.\n\n    ```\n    code line\n    ```\n\n    - item one\n"
  t s!"md notes: a note's other blocks set as its lines ({repr (twinOf blocks)})"
    (hasStr (twinOf blocks) "`code line`" && hasStr (twinOf blocks) "item one")
  let seams := worksMeta ++ "Cites [@a][^n], links [x][^n] and ![^n](x.png).\n\n[x]: https://example.org\n\n\
[^n]: The note.\n"
  let (d, _) := elabMd seams
  t s!"md notes: a note after a citation, a reference or a bang is a note ({repr (twinOf seams)}, \
{keysOf d})"
    (keysOf d == ["a"] && hasStr (twinOf seams) "[x](https://example.org)[^2]" &&
      hasStr (twinOf seams) "and ![^3](x.png)" && hasStr (twinOf seams) "[^3]: The note.")
  let inside := worksMeta ++ "Cite [see[^n] @a, p. 3] and ![a chart[^n]](chart.svg).\n\n[^n]: The note.\n"
  let (_, ds) := elabMd inside
  t s!"md notes: a note named in an alternative is named, one in a citation's note set after it, \
neither unused ({repr (ds.map (·.subject))})"
    ((ds.filter (·.subject == some "md:note-in-text")).size == 1 &&
      ds.any (·.subject == some "cite:note-footnote") && !ds.any (·.subject == some "md:note-unused"))
  let listed := "Intro[^m] text.\n\n- item one[^n]\n- item two\n\n[^n]: First note.\n[^m]: Second note.\n"
  t s!"md notes: definitions after a list are read ({repr (twinOf listed)})"
    (hasStr (twinOf listed) "[^1]: Second note." && hasStr (twinOf listed) "[^2]: First note.")
  for (src, note) in [("Text[^a].\n\n[^a]:\nUnindented content.\n\nBody.\n", "[^1]: Unindented content."),
      ("Text[^a] end.\n\n[^a]:\n\nBody.\n", "[^1]: Body.")] do
    t s!"md notes: a definition's empty line takes the next line, as Pandoc's ({repr (twinOf src)})"
      (hasStr (twinOf src) note)
  let (d, _) := elabMd "Text[^a] end.\n\n[^a]:\n"
  t s!"md notes: an empty definition is an empty note ({repr (Ir.blocksText d.body)})"
    (!hasStr (Ir.blocksText d.body) "[^a]" && (Ir.footnotesOf d.body).size == 1)
  let nested := "Text[^a].\n\n[^a]: Outer[^b] text.\n\n[^b]: Inner.\n"
  let (_, ds) := elabMd nested
  t s!"md notes: a reference inside a definition is its text and leaves its note unused, as \
Pandoc's ({repr (twinOf nested)})"
    (hasStr (twinOf nested) "Outer\\[^b\\] text." && ds.any (·.subject == some "md:note-unused"))
  let (_, ds) := elabMd "Text[^a].\n\n[^a]: Once.\n\n    - a list\n\n[^a]: Twice.\n\n[^c]: Never.\n\n    - a list\n"
  t s!"md notes: a block is named only in a definition that stands and is named \
({repr (ds.map (·.subject))})"
    (!ds.any (·.subject == some "md:note-block"))
  let (d, ds) := includedDoc "h.tex" (dvDoc "\\usepackage{markdown}\n" "\\markdownInput{p.md}")
    [("p.md", "p.md", "Text[^a].\n\n[^a]: A note.\n")]
  t s!"md notes: an included file reads no footnote, as the markdown package's default \
({repr (Ir.blocksText d.body)})"
    (hasStr (Ir.blocksText d.body) "[^a]: A note." &&
      !ds.any fun x => (x.subject.getD "").startsWith "md:note")

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
  let marks := "\\documentclass{article}\n\\begin{document}\nOne\\footnote{Note one.} \
two\\footnote{Note two.}\\setcounter{footnote}{0} again\\footnote{Note three.} \
and\\footnote[7]{Note seven.} also\\footnote[7]{Another seven.}.\n\\end{document}\n"
  let twin := MarkdownDoc.emit (elabStr marks).1
  let back := MarkdownDoc.emit (elabMd twin).1
  t s!"tex note twin: notes whose marks repeat keep their own text read back ({repr twin})"
    (["Note one.", "Note two.", "Note three.", "Note seven.", "Another seven."].all (hasStr back ·))
  let nest := "\\documentclass{article}\n\\begin{document}\nOne\\footnote{Outer\\footnote{Inner.} \
text.}. Two\\footnote{Plain.}.\n\\end{document}\n"
  let twin := MarkdownDoc.emit (elabStr nest).1
  t s!"tex note twin: a nested note's text stands in its note, the twin its round trip's fixed point \
({repr twin})"
    (hasStr twin "[^1]: Outer (Inner.) text." && hasStr twin "[^2]: Plain." &&
      MarkdownDoc.emit (elabMd twin).1 == twin)

/-- Pandoc's inline note `^[…]` reads its content as the text's own, citations included, and its
twin reads back. -/
def inlineNoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := worksMeta ++ "Text^[An inline note citing @a and *more*.] here^[Two [x] y.] end.\n"
  let (d, ds) := mdBibBuild src #[("works.bib", worksBib)]
  t s!"md inline note: its content is a note, its citation cited ({repr (pageText d)})"
    (hasStr (pageText d) "An inline note citing Ash [2001] and more." && hasStr (pageText d) "Two [x] y." &&
      !hasStr (pageText d) "^[" && (Ir.footnotesOf d.body).size == 2 && keysOf d == ["a"] &&
      !ds.any (·.kind == .W0392))
  let twin := MarkdownDoc.emit d
  let (back, _) := mdBibBuild twin #[("works.bib", worksBib)]
  t s!"md inline note: the twin reads back ({repr twin})"
    (MarkdownDoc.emit back == twin && pageText back == pageText d)
  t s!"md inline note: an abbreviation before one joins, as Pandoc's smart punctuation does \
({repr (pageText (elabMd "See cf. ^[A note.] here.\n").1)})"
    (hasStr (pageText (elabMd "See cf. ^[A note.] here.\n").1) "cf.\u00a0")
  let (d, ds) := elabMd "An image ![a ^[note] chart](chart.svg) here.\n"
  t s!"md inline note: one in an alternative sets nothing, named ({repr (ds.map (·.subject))})"
    ((Ir.footnotesOf d.body).size == 0 && ds.any (·.subject == some "md:note-in-text"))
  let (d, _) := elabMd "Unbalanced ^[open here.\n"
  t s!"md inline note: a bracket that never closes is text ({repr (pageText d)})"
    (hasStr (pageText d) "^[open here." && (Ir.footnotesOf d.body).size == 0)
  let (d, _) := includedDoc "h.tex" (dvDoc "\\usepackage{markdown}\n" "\\markdownInput{p.md}")
    [("p.md", "p.md", "Text^[A note.] here.\n")]
  t s!"md inline note: an included file reads none, as the markdown package's default \
({repr (pageText d)})"
    (hasStr (pageText d) "^[A note.]")

/-- A footnote in a citation's note, in either surface, sets after the citation, named once. -/
def citeNoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := worksMeta ++ "Five [@a, see^[x]] and [see [^n] @b] end.\n\n[^n]: The note.\n"
  let (d, ds) := mdBibBuild src #[("works.bib", worksBib)]
  t s!"md cite note: a note in a citation's note sets after the citation ({repr (pageText d)})"
    (hasStr (pageText d) "The note." && !hasStr (pageText d) "^[" && !hasStr (pageText d) "[^n]" &&
      (Ir.footnotesOf d.body).size == 2 && keysOf d == ["a", "b"] &&
      hasStr (pageText d) "[see Birch, 2002]" && ds.any (·.subject == some "cite:note-footnote"))
  let tex := "\\documentclass{article}\n\\usepackage{natbib}\n\\begin{document}\n\
Text \\citep[see\\footnote{An inner note.}][p.~3]{a} end.\n\\bibliographystyle{plainnat}\n\
\\bibliography{works}\n\\end{document}\n"
  let (d, ds) := bibBuild tex #[("works", worksBib)]
  t s!"tex cite note: a footnote in a citation's note sets after the citation, its text once \
({repr (pageText d)})"
    (hasStr (pageText d) "[see Ash, 2001, p.\u00a03]" && (Ir.footnotesOf d.body).size == 1 &&
      ((pageText d).splitOn "An inner note.").length == 2 &&
      ds.any (·.subject == some "cite:note-footnote"))

/-- A note anywhere in a citation's note, nested in emphasis or holding a citation or a note's
reference, sets after the citation once, its text and the note's spaces as written. -/
def citeNoteEdgeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := worksMeta ++ "One [@a, *em^[in em]*] and [see^[x] @a, p. 3] two.\n\n\
Three [see ^[cf. @b] @a] and [see ^[one] and ^[two] @b] end.\n\n\
Four [@a, p. ^[r] 4] and a caret link ^[x](https://example.org) end.\n"
  let (d, ds) := mdBibBuild src #[("works.bib", worksBib)]
  t s!"md cite note: notes in emphasis, holding a citation, or two, set after the citation \
({repr (pageText d)}, {repr (ds.map (·.subject))})"
    (hasStr (pageText d) "[see Ash, 2001]" && hasStr (pageText d) "[see and Birch, 2002]" &&
      hasStr (pageText d) "cf. Birch [2002]" && (Ir.footnotesOf d.body).size == 6 &&
      hasStr (pageText d) "p.\u00a04]" && hasStr (pageText d) "caret link ^x end" &&
      !hasStr (pageText d) "^[" && !hasStr (pageText d) "@" &&
      ((ds.filter (·.subject == some "md:cite-note")).size == 1) && !ds.any (·.subject == some "md:cite-nested"))
  let tex := "\\documentclass{article}\n\\usepackage{natbib}\n\\begin{document}\n\
A\\footnote{five} \\citep[\\emph{see\\footnote{x6}}][]{a} and \\citep[see \\footnote{x3} also][]{b} \
B\\footnote{seven}.\n\\bibliographystyle{plainnat}\n\\bibliography{works}\n\\end{document}\n"
  let (d, _) := bibBuild tex #[("works", worksBib)]
  t s!"tex cite note: a footnote in emphasis in a note sets after the citation, the note's spaces \
once ({repr (pageText d)})"
    (hasStr (pageText d) "[see Ash, 2001]" && hasStr (pageText d) "[see also Birch, 2002]" &&
      !hasStr (pageText d) "seex6" && (Ir.footnotesOf d.body).size == 4)
  for src in [worksMeta ++ "Ref^[see [^r]] nine and ^[outer ^[inner] tail].\n\n[^r]: The ref.\n",
      "Empty ^[] seven.\n\nSp ^[   ] eight and A[^d].\n\n[^d]: Top.\n\n    [^e]: Nested.\n\nThen B[^e].\n"] do
    let (d, ds) := mdBibBuild src #[("works.bib", worksBib)]
    let twin := MarkdownDoc.emit d
    t s!"md inline note: a reference in one, one in another, an empty one and a definition in a note \
read as Pandoc's, the twin a fixed point ({repr twin})"
      (MarkdownDoc.emit (elabMd twin).1 == twin && !hasStr (pageText d) "[^" &&
        !ds.any (·.subject == some "md:note-unused") &&
        (hasStr (pageText d) "The ref." || hasStr (pageText d) "Nested."))

/-- A TeX figure's caption citing fills its image's alternative with the caption's citations as the
reference list sets them. -/
def captionAltChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := "\\documentclass{article}\n\\usepackage{natbib}\n\\begin{document}\n\\begin{figure}\n\
\\includegraphics{chart.svg}\n\\caption{A chart from \\citet{a} and \\citep[p.~3]{b}.}\n\\end{figure}\n\
Text.\n\\bibliographystyle{plainnat}\n\\bibliography{works}\n\\end{document}\n"
  let (d, _) := bibBuild src #[("works", worksBib)]
  t s!"tex alt: a caption's citations read in its image's alternative as the list sets them \
({imageNames d})"
    ((imageNames d).contains "A chart from Ash [2001] and [Birch, 2002, p.\u00a03].")
  let (d, _) := elabStr "\\documentclass{article}\n\\begin{document}\n\\begin{figure}\n\
\\includegraphics{chart.svg}\n\\caption{A plain chart.}\n\\end{figure}\n\\end{document}\n"
  t s!"tex alt: a caption citing nothing fills the alternative with its words ({imageNames d})"
    ((imageNames d).contains "A plain chart.")
  let pic := "\\documentclass{article}\n\\usepackage{natbib}\n\\usepackage{tikz}\n\\begin{document}\n\
\\begin{figure}\n\\begin{tikzpicture}\\draw (0,0) -- (1,1);\\end{tikzpicture}\n\
\\caption{A drawing after \\citep{a}.}\n\\end{figure}\n\\bibliographystyle{plainnat}\n\
\\bibliography{works}\n\\end{document}\n"
  let (d, _) := bibBuild pic #[("works", worksBib)]
  t s!"tex alt: a picture's caption alternative sets its citation as the list does ({imageNames d})"
    ((imageNames d).contains "A drawing after [Ash, 2001].")

end Tests.MdNoteEdges
