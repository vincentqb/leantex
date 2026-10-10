module

public import Tests.Markdown
public import Tests.Artifact
public import Tests.DriverAssets

public section

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
                sp.pos == { line := if nested then 3 else 4, col := 1 })
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
      for (name, kind) in [("invalid.tex", DiagCode.W0002),
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
        d.span.any fun sp => sp.file == file && sp.pos == { line := 4, col := 1 })
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

/-- The lines a written PDF sets, each its runs' text at one baseline, in
page order: what the file itself states, read back. -/
def pdfLineTexts (pdf : ByteArray) : Array String :=
  match readArtifact pdf with
  | .error _ => #[]
  | .ok pages => pages.flatMap fun page => Id.run do
    let mut lines : Array (Dim.Sp × String) := #[]
    for run in page.runs do
      match lines.findIdx? (·.1 == run.y) with
      | some k => lines := lines.modify k fun (y, s) => (y, s ++ run.text)
      | none => lines := lines.push (run.y, run.text)
    return lines.map (·.2)

/-- **Markdown included in tex reads its HTML as the markdown read alone
does.** `\markdownInput` reads through the same `Md.read`, so a note's
carried break and its refused tags reach the host's two artifacts exactly as
they reach the note's own: the same lines in the PDF the host writes and in
the note's, the same typed HTML, and each refusal at the note's own line. -/
def markdownInputHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some bytes ← findFont | failures ref "markdown input HTML: missing fixture font"
  let .ok font := Font.parse bytes | failures ref "markdown input HTML: invalid fixture font"
  let fonts := oneFaceOf font
  IO.FS.withTempDir fun dir => do
    let note := "Alder<br>Birch\n\nH<sub>2</sub>O\n"
    IO.FS.writeFile (dir / "note.md") note
    let (host, hostDs) ← elabInputSrc (dir / "host.tex").toString
      (dvDoc "\\usepackage{markdown}\n" "\\markdownInput{note.md}")
    let (alone, aloneDs) := elabMd note
    let pdf (doc : Ir.Doc) : Array String :=
      pdfLineTexts (driverPdf fonts (Layout.Geom.ofPage doc.page) doc (layoutOf fonts doc))
    let html := docTreeOf
    t "markdown input: the PDF sets the note's break as the note alone does"
      (pdf host == pdf alone && (pdf host).extract 0 3 == #["Alder", "Birch", "H2O"])
    t "markdown input: the typed HTML carries the note's break as the note alone does"
      (hasStr (html host) "<p>Alder<br>Birch</p><p>H2O</p>"
        && hasStr (html alone) "<p>Alder<br>Birch</p><p>H2O</p>")
    let refusals (ds : Array Diag) : Array (Nat × Nat) :=
      (ds.filter fun d => d.kind == .E0390 && d.subject == some "md:raw-html").map fun d =>
        ((d.span.map (·.pos.line)).getD 0, (d.span.map (·.pos.col)).getD 0)
    t "markdown input: each refusal names the note's own line and column"
      (refusals hostDs == #[(3, 2), (3, 8)] && refusals hostDs == refusals aloneDs
        && (hostDs.filter (·.kind == .E0390)).all fun d =>
          d.span.any (·.file == (dir / "note.md").toString))

/-- **A disclosure's lost collapse is named for each artifact that loses it,
and for no other.** The HTML page and the markdown twin can each spell the
collapse — a `<details>` element, and the tag the twin's own reader reads —
and neither does: the page holds no `<details>` and the twin writes none.
Paper has no collapse to lose, and the PDF sets the disclosure exactly as
its bold-summary twin sets, every summary and body word in order. So the
loss is kept for exactly the HTML and the twin, in a markdown document and
in markdown a tex host includes, and the driver reports for each artifact
it writes, the twin included: an `-o x.md` build once named nothing, while
its twin had lost the collapse too. -/
def disclosurePrintChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet
    | t "the disclosure print faces load" false
      return
  let body := "\n<summary>Amber</summary>\n\nCedar\n\n</details>\n"
  let namedRight (ds : Array Diag) : Bool :=
    collapseNamed #[.pdf] ds == 0 && collapseNamed #[.html] ds == 1
      && collapseNamed #[.md] ds == 1 && collapseNamed #[.pdf, .html] ds == 1
      && collapseNamed #[.pdf, .md] ds == 1 && collapseNamed #[.html, .md] ds == 2
  for opener in ["<details>", "<details open>"] do
    let (doc, ds) := elabMd (opener ++ body)
    t s!"{opener}: the page sets the disclosure as its bold-summary twin sets"
      (shippedLinesOf fonts doc == shippedLinesOf fonts (elabMd "**Amber**\n\nCedar\n").1)
    t s!"{opener}: neither the HTML page nor the markdown twin carries the collapse"
      ((elemNodesList (· == "details") #[] (docNodesOf doc).toList).isEmpty
        && !hasStr (MarkdownDoc.emit doc).toLower "<details")
    t s!"{opener}: the lost collapse is named once for the HTML and once for the twin"
      (namedRight ds)
  t "the driver reports for each artifact it writes, the markdown twin included"
    (DriverAssets.diagnosticOutputs #[.pdf] == #[.pdf]
      && DriverAssets.diagnosticOutputs #[.html] == #[.html]
      && DriverAssets.diagnosticOutputs #[.md] == #[.md]
      && DriverAssets.diagnosticOutputs #[.pdf, .html, .md] == #[.pdf, .html, .md])
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "note.md") ("<details>" ++ body)
    let (_, ds) ← elabInputSrc (dir / "host.tex").toString
      (dvDoc "\\usepackage{markdown}\n" "\\markdownInput{note.md}")
    t "a tex host names its note's lost collapse once for the HTML and once for the twin"
      (namedRight ds)

end Tests
