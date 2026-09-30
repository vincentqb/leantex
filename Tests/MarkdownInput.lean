import Tests.Markdown
import Tests.Artifact

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- Filename quoting is resolved before either surface chooses an extension.
LuaLaTeX removes paired quotes even inside a name, trims surrounding spaces
on names with an extension, and retains a trailing space before an inferred
extension. Spaces within a name are preserved. The selected
file must reach the actual PDF and HTML between its neighbours; a missing
file must name the normalized path at the including source's position. -/
def quotedInputFilenameChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some bytes ← findFont | failures ref "quoted input: missing fixture font"
  let .ok font := Font.parse bytes | failures ref "quoted input: invalid fixture font"
  let fonts := oneFaceOf font
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    let pre := "\\usepackage{markdown}\n"
    let fixtures := [("file name.md", "Quotedword"), ("bare name", "Bareonly"),
      ("choice name", "Barechoice"), ("choice name.tex", "Texchoice"),
      ("typed name.md", "Explicitextension"), ("typed name.md.tex", "Extendedextension"),
      ("texed name.tex", "Texextension"), ("texed name.tex.tex", "Doubledtex"),
      ("spaced name .tex", "Spacedextension"), ("spaced name.tex", "Unspacedextension")]
    for (name, text) in fixtures do
      IO.FS.writeFile (dir / name) (text ++ ".\n")
    for command in ["input", "markdownInput"] do
      for (label, name, expected) in [
          ("quoted", "\"file name.md\"", "Quotedword"),
          ("unquoted spaces", "file name.md", "Quotedword"),
          ("embedded quotes", "file \"name\".md", "Quotedword"),
          ("outer spaces", "  \"file name.md\"  ", "Quotedword"),
          ("inner spaces", "\" file name.md \"", "Quotedword"),
          ("bare fallback", "\"bare name\"", "Bareonly"),
          ("default extension", "\"choice name\"", "Texchoice"),
          ("space before extension", "\" spaced name \"", "Spacedextension"),
          ("explicit extension", "\"typed name.md\"",
            if command == "input" then "Extendedextension" else "Explicitextension"),
          ("tex extension", "\"texed name.tex\"", "Texextension"),
          ("nested", "\"file name.md\"", "Quotedword")] do
        let call := s!"\\{command}\{{name}}"
        IO.FS.writeFile (dir / "nested file.tex") call
        let call := if label == "nested" then "\\input{\"nested file.tex\"}" else call
        let (doc, ds) ← elabInputSrc file (dvDoc pre
          ("Beforefragment.\n\n" ++ call ++ "\n\nAfterfragment."))
        let out := layoutOf fonts doc
        let pdfText ← match readArtifact (driverPdf fonts (Layout.Geom.ofPage doc.page) doc out) with
          | .error err => do
            failures ref s!"quoted input {command}/{label}: PDF readback: {err}"
            pure ""
          | .ok pages => pure (pages.foldl (fun text page =>
              page.runs.foldl (fun text run => text ++ run.text) text) "")
        let (_, htmlTree, _) := HtmlDoc.emitTree {} doc
        let (html, _) := HtmlDoc.emit {} doc
        for marker in ["Beforefragment", expected, "Afterfragment"] do
          t s!"quoted input {command}/{label}: PDF ships {marker} once"
            ((pdfText.splitOn marker).length == 2)
          t s!"quoted input {command}/{label}: HTML ships {marker} once"
            (treeShownOccurs htmlTree marker == 1 && hasStr html marker)
        for (artifact, text) in [("PDF", pdfText), ("HTML", html)] do
          t s!"quoted input {command}/{label}: {artifact} preserves include order"
            ((text.splitOn "Beforefragment").drop 1 |>.any fun tail =>
              (tail.splitOn expected).drop 1 |>.any fun tail => hasStr tail "Afterfragment")
          t s!"quoted input {command}/{label}: {artifact} selects only the intended file"
            (fixtures.all fun (_, marker) => marker == expected || !hasStr text marker)
        t s!"quoted input {command}/{label}: no missing file or parse error"
          (ds.all (·.severity != .error))
      for nested in [false, true] do
        let call := s!"\\{command}\{  \"absent name.md\"  }"
        let nestedFile := (dir / "missing caller.tex").toString
        IO.FS.writeFile nestedFile ("\n\n" ++ call)
        let (_, ds) ← elabInputSrc file (dvDoc pre
          (if nested then "\\input{\"missing caller.tex\"}" else call))
        let missing := ds.filter (·.kind == .E0502)
        let preferred := if command == "input" then "absent name.md.tex" else "absent name.md"
        t s!"quoted input {command}/{nested}: missing file names normalized path and caller"
          (missing.size == 1 && missing.any fun d =>
            hasStr d.message s!"'\\{command}' file '{preferred}'" &&
              d.span.any fun sp =>
                sp.file == (if nested then nestedFile else file) &&
                sp.pos == ⟨if nested then 3 else 4, 1⟩)
    IO.FS.writeFile (dir / "strict fragment.md") "paragraph\n\n<div>unsupported</div>\n"
    let (_, ds) ← elabInputSrc file
      (dvDoc pre "\\markdownInput{ \"strict fragment.md\" }")
    t "quoted input: included diagnostic retains resolved filename and source line"
      (ds.any fun d => d.kind == .E0390 &&
        d.span.any fun sp =>
          sp.file == (dir / "strict fragment.md").toString && sp.pos.line == 3)

/-- Included files use their surface's filename contract and one read-error
contract. LuaLaTeX's `\input` tries a `.tex` suffix, whereas `\markdownInput`
honours an explicit extension. Malformed bytes and unreadable paths must
return diagnostics rather than escape as IO exceptions. -/
def inputFileChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    IO.FS.writeFile (dir / "bare") "Bareonly"
    IO.FS.writeFile (dir / "choice") "Barechoice"
    IO.FS.writeFile (dir / "choice.tex") "Texchoice"
    IO.FS.writeFile (dir / "typed.md") "Explicitextension"
    IO.FS.writeFile (dir / "typed.md.tex") "Extendedextension"
    IO.FS.writeFile (dir / "texed.tex") "Texextension"
    IO.FS.writeFile (dir / "texed.tex.tex") "Doubledtex"
    IO.FS.writeBinFile (dir / "invalid.tex") ⟨#[0xC3, 0x28]⟩
    IO.FS.createDir (dir / "directory.tex")
    for command in ["input", "markdownInput"] do
      for (name, expected) in [("bare", "Bareonly"), ("choice", "Texchoice"),
          ("typed.md", if command == "input" then "Extendedextension"
            else "Explicitextension"), ("texed.tex", "Texextension")] do
        let (doc, ds) ← elabInputSrc file
          (dvDoc "\\usepackage{markdown}\n" s!"\\{command}\{{name}}")
        let (_, html, _) := HtmlDoc.emitTree {} doc
        t s!"{command}: filename {name} selects {expected}"
          (treeShownOccurs html expected == 1 && ds.all (·.severity != .error))
      for (name, kind) in [("invalid.tex", DiagCode.E0002),
          ("directory.tex", DiagCode.E0001)] do
        let result ← (elabInputSrc file
          (dvDoc "\\usepackage{markdown}\n" s!"\\{command}\{{name}}")).toBaseIO
        t s!"{command}: {name} returns {kind.code} instead of throwing"
          (match result with
          | .error _ => false
          | .ok (_, ds) => ds.any fun d => d.kind == kind &&
              (d.span.any (·.file == (dir / name).toString) ||
                hasStr d.message (dir / name).toString))

/-- An included fragment ships between its neighbours in PDF layout and the
typed HTML tree. Literal Markdown never becomes TeX input, and losses keep
the source file and line that can be corrected. Failed on the tree before
the file reader understood `\markdownInput`, including the empty-file and
missing-file cases that a nonempty happy-path probe cannot distinguish. -/
def markdownInputChecks (ref : IO.Ref (List String)) : IO Unit := do
  quotedInputFilenameChecks ref
  inputFileChecks ref
  let t := check ref
  let some bytes ← findFont | failures ref "markdown input: missing fixture font"
  let .ok font := Font.parse bytes | failures ref "markdown input: invalid fixture font"
  let fonts := oneFaceOf font
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    let literal := "\\input{never} 100% $x$ # [braces]"
    let fragment := "# Includedheading\n\nA **strongword** and *emphasisword*.\n\n\
- Firstitem\n- Seconditem\n\n```text\n" ++ literal ++ "\n```\n"
    IO.FS.writeFile (dir / "fragment.md") fragment
    IO.FS.writeFile (dir / "empty.md") ""
    IO.FS.writeFile (dir / "nested.tex") "\\markdownInput{fragment.md}\n"
    let pre := "\\usepackage{markdown}\n"
    for (label, call) in [
        ("direct", "\\markdownInput{fragment.md}"),
        ("empty options", "\\markdownInput[]{fragment.md}"),
        ("spaced argument", "\\markdownInput \n {fragment.md}"),
        ("nested TeX", "\\input{nested}")] do
      for deck in [false, true] do
        let body := "Beforefragment.\n\n" ++ call ++ "\n\nAfterfragment."
        let src := if deck then dvDeck pre ("\\begin{frame}{Hostframe}\n" ++ body ++
          "\n\\end{frame}") else dvDoc pre body
        let (doc, ds) ← elabInputSrc file src
        let out := layoutOf fonts doc
        let shown := censusText (censusOf #[] out)
        let (_, html, _) := HtmlDoc.emitTree {} doc
        let htmlText := nodeTextList "" html.toList
        for text in ["Beforefragment", "Includedheading", "strongword", "emphasisword",
            "Firstitem", "Seconditem", "Afterfragment"] do
          t s!"markdown input {label}/{deck}: PDF ships {text}" (hasStr shown text)
          t s!"markdown input {label}/{deck}: HTML ships {text}" (hasStr htmlText text)
        t s!"markdown input {label}/{deck}: HTML preserves literal code"
          (hasStr htmlText literal)
        -- Verbatim spaces are positioned, glyphless runs: the text census
        -- alone cannot witness them. Compare every run's text, offset and
        -- width with the same literal written as a native typed listing.
        let codeRuns (o : Layout.Out) : Option (Array (Nat × String × Dim.Sp × Dim.Sp)) :=
          ((bodyLines o).find? fun l => hasStr (lineText l) "\\input{never}").map fun l =>
            (lineRuns l).map fun (f, text, x, w) => (f, text, x - l.x, w)
        let native := layoutOf fonts (elabStr
          (src.replace call ("\\begin{lstlisting}[language=text]\n" ++ literal ++
            "\n\\end{lstlisting}"))).1
        t s!"markdown input {label}/{deck}: PDF preserves literal code and spacing"
          ((codeRuns out).isSome && codeRuns out == codeRuns native)
        t s!"markdown input {label}/{deck}: content stays between its neighbours"
          (shown.splitOn "Beforefragment" |>.drop 1 |>.any fun s =>
            (s.splitOn "Includedheading").drop 1 |>.any fun s =>
              hasStr s "Afterfragment")
        t s!"markdown input {label}/{deck}: no unknown calls or errors"
          (ds.all fun d => d.severity != .error &&
            !["W0103", "W0301", "W0302", "W0110"].contains d.code)
        t s!"markdown input {label}/{deck}: literal code cannot request another file"
          (ds.all (·.kind != .E0502))
    let (emptyDoc, emptyDs) ← elabInputSrc file
      (dvDoc pre "Beforeempty.\n\n\\markdownInput{empty.md}\n\nAfterempty.")
    let (_, emptyHtml, _) := HtmlDoc.emitTree {} emptyDoc
    t "markdown input: empty file ships no filename or wrapper text"
      (treeShownOccurs emptyHtml "Beforeempty" == 1 &&
       treeShownOccurs emptyHtml "Afterempty" == 1 &&
       treeShownOccurs emptyHtml "empty.md" == 0 &&
       emptyDs.all (·.kind != .W0301))
    let (_, missingDs) ← elabInputSrc file
      (dvDoc pre "\\markdownInput{absent.md}")
    t "markdown input: missing file names the command and including file"
      (missingDs.any fun d => d.kind == .E0502 &&
        hasStr d.message "\\markdownInput" &&
        d.span.any fun sp => sp.file == file && sp.pos == ⟨4, 1⟩)
    IO.FS.writeFile (dir / "strict.md") "paragraph\n\n<div>unsupported</div>\n"
    let (_, strictDs) ← elabInputSrc file (dvDoc pre "\\markdownInput{strict.md}")
    t "markdown input: dialect errors retain the fragment's own position"
      (strictDs.any fun d => d.kind == .E0390 &&
        d.span.any fun sp => sp.file == (dir / "strict.md").toString && sp.pos.line == 3)
    let (optionDoc, optionDs) ← elabInputSrc file
      (dvDoc pre "\\markdownInput[smartEllipses=true]{fragment.md}")
    let (_, optionHtml, _) := HtmlDoc.emitTree {} optionDoc
    t "markdown input: unsupported options are named while content still ships"
      (optionDs.any (·.kind == .W0110) &&
       treeShownOccurs optionHtml "Includedheading" == 1 &&
       treeShownOccurs optionHtml "smartEllipses" == 0)
    let (_, packageDs) ← elabInputSrc file
      (dvDoc "\\usepackage[smartEllipses]{markdown}\n" "\\markdownInput{fragment.md}")
    t "markdown input: package options do not silently configure another dialect"
      (packageDs.any (·.kind == .W0110))

end Tests
