import Tests.Markdown

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- File reads belong to a macro's use, under that use's argument bindings.
An unused definition must not read, a filename argument selects only its
own answer, and an inline answer must not inherit another answer's block
shape. Both surfaces ship their content through the existing elaborator. -/
def inputUseChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some bytes ← findFont | failures ref "input use: missing fixture font"
  let .ok font := Font.parse bytes | failures ref "input use: invalid fixture font"
  let fonts := oneFaceOf font
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    let pre := "\\usepackage{markdown}\n"
    IO.FS.writeFile (dir / "fragment.tex") "Includedword"
    IO.FS.writeFile (dir / "fragment.md") "Includedword\n"
    IO.FS.writeFile (dir / "other.tex") "Otherword"
    IO.FS.writeFile (dir / "other.md") "Otherword\n"
    IO.FS.writeFile (dir / "block.tex") "\\section{Blockheading}\nBlockword"
    IO.FS.writeFile (dir / "block.md") "# Blockheading\n\nBlockword\n"
    for (command, ext) in [("input", "tex"), ("include", "tex"), ("markdownInput", "md")] do
      let path := "fragment." ++ ext
      let decl (body : String) := "\\newcommand{\\inc}[1]{" ++ body ++ "}\n"
      let (unused, unusedDs) ← elabInputSrc file
        (dvDoc (pre ++ "\\newcommand{\\unused}{\\" ++ command ++ "{absent}}\n")
          "Visibleword.")
      let (_, unusedHtml, _) := HtmlDoc.emitTree {} unused
      t s!"{command}: an unused macro does not read its file"
        (unusedDs.all (·.kind != .E0502) && treeShownOccurs unusedHtml "Visibleword" == 1)
      for (label, definition, use) in [
          ("literal", "\\newcommand{\\inc}{\\" ++ command ++ "{" ++ path ++ "}}\n",
            "\\inc"),
          ("parameter", decl ("\\" ++ command ++ "{#1}"), "\\inc{" ++ path ++ "}")] do
        let (doc, ds) ← elabInputSrc file
          (dvDoc (pre ++ definition) ("Beforeword.\n\n" ++ use ++ "\n\nAfterword."))
        let (_, html, _) := HtmlDoc.emitTree {} doc
        let shown := censusText (censusOf #[] (layoutOf fonts doc))
        t s!"{command}: {label} macro ships included PDF text at its use"
          (hasStr shown "Includedword" && ds.all (·.severity != .error))
        t s!"{command}: {label} macro ships included HTML text at its use"
          (treeShownOccurs html "Includedword" == 1 &&
           treeShownOccurs html path == 0 && ds.all (·.kind != .W0301))
      let wrapper := pre ++ decl ("\\" ++ command ++ "{#1}")
      let (twice, twiceDs) ← elabInputSrc file
        (dvDoc wrapper ("\\inc{" ++ path ++ "} \\inc{other." ++ ext ++ "}"))
      let (_, twiceHtml, _) := HtmlDoc.emitTree {} twice
      t s!"{command}: each filename binding selects exactly its own answer"
        (treeShownOccurs twiceHtml "Includedword" == 1 &&
         treeShownOccurs twiceHtml "Otherword" == 1 &&
         twiceDs.all (·.severity != .error))
      let (mixed, mixedDs) ← elabInputSrc file
        (dvDoc wrapper ("Leadword \\inc{" ++ path ++ "} Tailword\n\n\\inc{block." ++ ext ++ "}"))
      let out := layoutOf fonts mixed
      let (direct, directDs) ← elabInputSrc file
        (dvDoc wrapper ("Leadword \\" ++ command ++ "{" ++ path ++ "} Tailword\n\n\\" ++
          command ++ "{block." ++ ext ++ "}"))
      -- Markdown's native paragraph carries an explicit paragraph end.
      -- A macro must preserve that boundary, just as a TeX fragment with
      -- no paragraph end must remain inline.
      t s!"{command}: each answer keeps the paragraph shape of its direct use"
        ((bodyLines out).map lineText ==
           (bodyLines (layoutOf fonts direct)).map lineText &&
         hasStr (censusText (censusOf #[] out)) "Blockheading" &&
         mixedDs.all (·.severity != .error) && directDs.all (·.severity != .error))
      if command != "markdownInput" then
        t s!"{command}: a block answer does not split the other inline use"
          ((bodyLines out).any fun line =>
            ["Leadword", "Includedword", "Tailword"].all (hasStr (lineText line)))
    let literal := "\\input{never} 100% $x$ # [braces]"
    IO.FS.writeFile (dir / "literal.md") ("```text\n" ++ literal ++ "\n```\n")
    let (doc, ds) ← elabInputSrc file
      (dvDoc (pre ++ "\\newcommand{\\inc}[1]{\\markdownInput{#1}}\n")
        "\\inc{literal.md}")
    let (_, html, _) := HtmlDoc.emitTree {} doc
    t "markdown input use: the answer stays native AST without a source reparse"
      (hasStr (nodeTextList "" html.toList) literal &&
       ds.all fun d => d.kind != .E0502 && d.kind != .W0301)

end Tests
