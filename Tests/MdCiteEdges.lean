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

/-- `*`, Pandoc's key for every entry, lists every entry and prints nothing. -/
def everyEntryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (src, what) in [("All works [@*] listed.", "a group"), ("All works @* listed.", "in the text")] do
    let (d, ds) := mdBibBuild (worksMeta ++ src ++ "\n") #[("works.bib", worksBib)]
    let listed := Ir.foldBlocks (fun out b => match b with
      | .bibliography _ _ items => out ++ items.map (·.key)
      | _ => out) (fun out _ => out) #[] d.body
    t s!"md every entry: '@*' {what} lists every entry ({listed})"
      (listed.size == 3 && ["a", "b", "roe2020"].all listed.contains)
    t s!"md every entry: '@*' {what} prints nothing and names nothing \
({repr (inkText d.body)}, {repr (ds.map (·.code))})"
      (hasStr (inkText d.body) "All works listed." && !ds.any (·.kind == .W0351))
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
  t "md group: a citation group before another reads as two"
    (groups "Both [@a][@b] here" == 2)
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
  t s!"tex notes: a note's edge spaces are off ({notes})"
    (notes == [("", "p.\u00a03"), ("see", "chap. 2")])
  let twin := MarkdownDoc.emit d
  let (back, _) := mdBibBuild twin #[("works.bib", worksBib)]
  t s!"tex twin: the twin reads back to the notes and the plain spaces written ({repr twin})"
    (MarkdownDoc.emit back == twin && hasStr twin "chap.&#32;2" && hasStr twin "e.g.&#32;here")

end Tests.MdCiteEdges
