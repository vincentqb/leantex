module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-! Markdown citations read at Pandoc's edges, and a TeX note's edge spaces through the twin. -/

namespace Tests.MdCiteEdges

/-- The text of a markdown document's body read under `worksMeta`. -/
def mdText (body : String) : String := Ir.blocksText (elabMd (worksMeta ++ body ++ "\n")).1.body

/-- A key's characters are Haskell's `isAlphaNum`: any script's letters and numbers. -/
def keyDigitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (d, _) := elabMd (worksMeta ++ "A @k٣x, @k²y, @kⅫz, @k３w and @٣k end.\n")
  t s!"md keys: a key holds any script's digits and numbers, first or within \
({keysOf d})"
    (keysOf d == ["k٣x", "k²y", "kⅫz", "k３w", "٣k"])
  let (d, _) := elabMd (worksMeta ++ "A @k\u0301e end.\n")
  t s!"md keys: a combining mark ends a key, as Pandoc's grammar reads it ({keysOf d})"
    (keysOf d == ["k"])

/-- `*`, Pandoc's key for every entry, prints and lists nothing in the text, named, as its citation
processing reads it; the metadata's `nocite` lists every entry. -/
def everyEntryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let listedOf (d : Ir.Doc) : Array String := Ir.foldBlocks (fun out b => match b with
    | .bibliography _ _ items => out ++ items.map (·.key)
    | _ => out) (fun out _ => out) #[] d.body
  for (src, what) in [("All works [@*] listed.", "a group"), ("All works @* listed.", "in the text"),
      ("All works [@*] and [@b] listed.", "beside a work")] do
    let (d, ds) := mdBibBuild (worksMeta ++ src ++ "\n") #[("works.bib", worksBib)]
    t s!"md every entry: '@*' {what} lists nothing of its own ({listedOf d})"
      (listedOf d == (if hasStr src "@b" then #["b"] else #[]))
    t s!"md every entry: '@*' {what} prints nothing, named \
({repr (inkText d.body)}, {repr (ds.map (·.subject))})"
      (hasStr (inkText d.body) "All works " && !hasStr (inkText d.body) "@" &&
        ds.any (·.subject == some "md:cite-every") && !ds.any (·.kind == .W0351))
  let (d, _) := mdBibBuild ("---\nbibliography: works.bib\nnocite: '@*'\n---\n\nText.\n")
    #[("works.bib", worksBib)]
  t s!"md every entry: the metadata's nocite of '@*' lists every entry ({listedOf d})"
    ((listedOf d).size == 3)
  let (d, _) := elabMd (worksMeta ++ "See @*x here.\n")
  t s!"md every entry: '@*x' is the key '*x', as Pandoc reads it ({keysOf d})"
    (keysOf d == ["*x"])

/-- A citation group before braces or a bracket reads as Pandoc reads it. -/
def bracketTailChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let groups (src : String) : Nat :=
    (citesOf (elabMd (worksMeta ++ src ++ "\n")).1).toList.countP fun (f, _) => f.cmd == .paren
  t "md group: braces holding no attribute list follow a citation as text"
    (groups "First [@a]{x} then" == 1 && hasStr (mdText "First [@a]{x} then") "{x} then")
  t "md group: braces holding an attribute list make the bracket no citation group"
    (groups "First [@a]{.c} then" == 0 && groups "First [@a]{} then" == 0 &&
      groups "First [@a]{k=\"v w\" #i -} then" == 0)
  t "md group: a bracket around an in-text citation before a group reads as Pandoc's, one group"
    (groups "Both [@a][@b] here" == 1 &&
      keysOf (elabMd (worksMeta ++ "Both [@a][@b] here\n")).1 == ["a", "b"])
  for (src, n) in [("X [q][@a][@b] y", 2), ("X [@a][@b][@roe2020] y", 2), ("X [@a][@b]{.c} y", 1)] do
    t s!"md group: a label an undefined reference leaves reads on its own, as Pandoc's ({repr src})"
      (groups src == n && (citesOf (elabMd (worksMeta ++ src ++ "\n")).1).toList.countP
        (fun (f, _) => f.cmd == .textual) == (if hasStr src "[q]" then 0 else 1))
  t "md group: a bracket before a reference label is no citation group"
    (groups "No [@a][x] group" == 0 && groups "No [@a][] group" == 0)

/-- An in-text citation's locator follows it after spaces and one line ending, its two trailing
spaces no line break. -/
def breakTailChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let post (src : String) : List String :=
    (citesOf (elabMd (worksMeta ++ src ++ "\n")).1).toList.map (·.1.post)
  t s!"md tail: two spaces ending the line still lead to the locator ({post "As @a  \n[p. 3] says."})"
    (post "As @a  \n[p. 3] says." == ["p.\u00a03"] &&
      !hasStr (mdText "As @a  \n[p. 3] says.") "[p")
  t s!"md tail: a backslash line break ends the citation ({post "As @a\\\n[p. 3] says."})"
    (post "As @a\\\n[p. 3] says." == [""])

/-- The heading a markdown document's metadata sets over its list stands only over a list that
lists an entry. -/
def listTitleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let titled := "---\nbibliography: works.bib\nreference-section-title: Works cited\n---\n\n"
  let heads (body : String) : Array String :=
    Ir.foldBlocks (fun out b => match b with
      | .section _ _ _ h => out.push (Ir.plainText h)
      | _ => out) (fun out _ => out) #[]
      (mdBibBuild (titled ++ body ++ "\n") #[("works.bib", worksBib)]).1.body
  t s!"md list title: a list of no entry sets no heading ({heads "Cites [@ghost]."})"
    (heads "Cites [@ghost]." == #[])
  t s!"md list title: a list of an entry sets its heading ({heads "Cites [@a]."})"
    (heads "Cites [@a]." == #["Works cited"])
  t s!"md list title: the author's own heading over a division stays \
({heads "Cites [@ghost].\n\n# Own heading\n\n::: {#refs}\n:::"})"
    (heads "Cites [@ghost].\n\n# Own heading\n\n::: {#refs}\n:::" == #["Own heading"])

/-- Pandoc's smart punctuation joins an abbreviation to the word after it, where the document is
markdown and no citation follows. -/
def abbrevChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let text := inkText (mdBibBuild (worksMeta ++
    "See p. 3, Dr. Ash, e.g. this, (pp. 4) and p. [@a], Fig. 2 and [@b, p. 5].\n")
    #[("works.bib", worksBib)]).1.body
  t s!"md abbreviation: a space after an abbreviation is non-breaking ({repr text})"
    (hasStr text "p.\u00a03" && hasStr text "Dr.\u00a0Ash" && hasStr text "e.g.\u00a0this" &&
      hasStr text "(pp.\u00a04)")
  t s!"md abbreviation: before a citation, after a capital the list lacks, the space stays \
({repr text})"
    (hasStr text "and p. " && !hasStr text "and p.\u00a0" && hasStr text "Fig. 2")
  t s!"md abbreviation: a citation's locator joins too \
({(citesOf (elabMd (worksMeta ++ "See [@b, p. 5].\n")).1).toList.map (·.1.post)})"
    ((citesOf (elabMd (worksMeta ++ "See [@b, p. 5].\n")).1).toList.map (·.1.post) == ["p.\u00a05"])
  t "md abbreviation: a referenced space stays the space it names"
    (hasStr (mdText "See p.&#32;3.") "p. 3")
  let host := "\\documentclass{article}\n\\usepackage{markdown}\n\\begin{document}\n\
\\markdownInput{p.md}\n\\end{document}\n"
  t "md abbreviation: an included file and TeX keep the space"
    (hasStr (Ir.blocksText (includedDoc "h.tex" host [("p.md", "p.md", "See p. 3.\n")]).1.body) "p. 3" &&
      hasStr (Ir.blocksText (elabStr "\\documentclass{article}\n\\begin{document}\nSee p. 3.\n\
\\end{document}\n").1.body) "p. 3")
  let lean := Ir.blocksText (elabCode "M.lean" "/-! See p. 3. -/\ndef x := 1\n").1.body
  t s!"md abbreviation: a Lean docstring keeps the space, as doc-gen4 sets it ({repr lean})"
    (hasStr lean "p. 3")

/-- A TeX citation's notes set without their edge spaces, so the twin carries them exactly, and a
plain space after an abbreviation reads back as written. -/
def twinChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := "\\documentclass{article}\n\\usepackage{natbib}\n\\begin{document}\n\
A \\citep[ p.~3 ]{a} and \\citep[see ][ chap. 2 ]{roe2020}, e.g. here.\n\
\\bibliographystyle{plainnat}\n\\bibliography{works}\n\\end{document}\n"
  let (d, _) := bibBuild src #[("works", worksBib)]
  let notes := (citesOf d).toList.map fun (f, _) => (f.pre, f.post)
  t s!"tex notes: a note keeps its edge spaces, as natbib sets them ({notes})"
    (notes == [("", " p.\u00a03 "), ("see ", " chap. 2 ")])
  let twin := MarkdownDoc.emit d
  let (back, _) := mdBibBuild twin #[("works.bib", worksBib)]
  t s!"tex twin: the twin spells a note without its edge spaces, reading back to it and the plain \
spaces written ({repr twin})"
    (MarkdownDoc.emit back == twin && hasStr twin "[@a, p. 3]" && hasStr twin "chap.&#32;2]" &&
      hasStr twin "e.g.&#32;here")
  for alt in ["![Plain p.&#32;4](chart.svg)", "![A chart, cf. 2](chart.svg)", "L p.&nbsp; 3"] do
    let once := MarkdownDoc.emit (elabMd (alt ++ "\n")).1
    t s!"md twin: an alternative's spaces after an abbreviation read back as written ({repr once})"
      (MarkdownDoc.emit (elabMd once).1 == once)
  let (d, _) := bibBuild "\\documentclass{article}\n\\usepackage{natbib}\n\\begin{document}\n\
A \\citep[ ]{a} and \\citep[ ][ ]{b}.\n\\bibliographystyle{plainnat}\n\\bibliography{works}\n\
\\end{document}\n" #[("works", worksBib)]
  let twin := MarkdownDoc.emit d
  let (back, _) := mdBibBuild twin #[("works.bib", worksBib)]
  t s!"tex twin: a note of spaces alone spells no note, the twin its round trip's fixed point \
({repr twin})"
    (hasStr twin "A [@a] and [@b]." && MarkdownDoc.emit back == twin)

end Tests.MdCiteEdges
