module

public import Tests.Markdown
public import Tests.Artifact
public import Tests.DriverAssets
import LeanTex.Core.TexText

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- Filename quoting resolves as LuaLaTeX resolves it before either surface chooses an extension,
and the file ships between its neighbours. -/
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
            d.message == (if command == "input" then Diag.tex .inputMissing [preferred]
              else Diag.say .E0502 .file preferred) &&
              d.detail == some s!"named by \\{command}" &&
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

/-- Included files follow their surface's filename contract, and unreadable bytes or paths return
diagnostics. -/
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

/-- A Markdown fragment's headings in a class with chapters as the markdown package sets them: the
chapter for `#`, each deeper one a level down, numbered as the class numbers them (lualatex); in a
class without, the fragment reads as the file alone (doors D1), where lualatex numbers sections. -/
def markdownHeadingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    IO.FS.writeFile (dir / "frag.md") "# Toplevel\n\nText.\n\n## Nested\n\nMore.\n"
    let heads (cls : String) : IO (Array (Option String × String)) := do
      let (doc, _) ← elabInputSrc file ("\\documentclass{" ++ cls ++ "}\n\\usepackage{markdown}\n" ++
        "\\begin{document}\n\\markdownInput{frag.md}\n\\end{document}")
      return doc.body.filterMap fun b => match b with
        | .section _ _ num title => some (num, Ir.plainText title)
        | _ => none
    let report ← heads "report"
    let article ← heads "article"
    t s!"markdown headings: a report's # is a numbered chapter, its ## a section ({report})"
      (report == #[(some "Chapter 1", "Toplevel"), (some "1.1", "Nested")])
    t s!"markdown headings: an article's fragment reads as the file alone ({article})"
      (article == #[(none, "Toplevel"), (none, "Nested")])

/-- An included markdown fragment ships between its neighbours in both artifacts, its losses at its
own file and line. -/
def markdownInputChecks (ref : IO.Ref (List String)) : IO Unit := do
  markdownHeadingChecks ref
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
        -- Verbatim spaces are glyphless runs, so every run's text, offset and width is compared.
        let codeRuns (o : Layout.Out) : Option (Array (Nat × String × Dim.Length × Dim.Length)) :=
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
        hasStr (saidText d) "\\markdownInput" &&
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

/-- The lines a written PDF sets, each its runs' text at one baseline, in page order. -/
def pdfLineTexts (pdf : ByteArray) : Array String :=
  match readArtifact pdf with
  | .error _ => #[]
  | .ok pages => pages.flatMap fun page => Id.run do
    let mut lines : Array (Dim.Length × String) := #[]
    for run in page.runs do
      match lines.findIdx? (·.1 == run.y) with
      | some k => lines := lines.modify k fun (y, s) => (y, s ++ run.text)
      | none => lines := lines.push (run.y, run.text)
    return lines.map (·.2)

/-- Markdown included in tex reads its HTML as the markdown read alone does. -/
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
    -- The article host indents the note's paragraphs, as the markdown package's LaTeX does.
    t "markdown input: the typed HTML carries the note's break as the note alone does"
      (hasStr (html host) "<p class=u-indent>Alder<br>Birch</p><p class=u-indent>H2O</p>"
        && hasStr (html alone) "<p>Alder<br>Birch</p><p>H2O</p>")
    let refusals (ds : Array Diag) : Array (Nat × Nat) :=
      (ds.filter fun d => d.kind == .E0390 && d.subject == some "md:raw-html").map fun d =>
        ((d.span.map (·.pos.line)).getD 0, (d.span.map (·.pos.col)).getD 0)
    t "markdown input: each refusal names the note's own line and column"
      (refusals hostDs == #[(3, 2), (3, 8)] && refusals hostDs == refusals aloneDs
        && (hostDs.filter (·.kind == .E0390)).all fun d =>
          d.span.any (·.file == (dir / "note.md").toString))

/-- A disclosure is one construct both artifacts read, and paper sets it expanded. -/
def disclosurePrintChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet
    | t "the disclosure print faces load" false
      return
  let body := "\n<summary>Amber</summary>\n\nCedar\n\n</details>\n"
  let element (opener : String) : String :=
    opener ++ "<summary>Amber</summary><p>Cedar</p></details>"
  for (opener, tag) in [("<details>", "<details>"), ("<details open>", "<details open=>")] do
    let (doc, ds) := elabMd (opener ++ body)
    t s!"{opener}: the page sets the disclosure as its bold-summary spelling sets"
      (shippedLinesOf fonts doc == shippedLinesOf fonts (elabMd "**Amber**\n\nCedar\n").1)
    t s!"{opener}: past a heading and before a paragraph, the page sets it as that spelling sets"
      (shippedLinesOf fonts (elabMd ("# Head\n\n" ++ opener ++ body ++ "\nDelta after.\n")).1 ==
        shippedLinesOf fonts (elabMd "# Head\n\n**Amber**\n\nCedar\n\nDelta after.\n").1)
    t s!"{opener}: the HTML page ships the element, open exactly where the tag is"
      (hasStr (docTreeOf doc) (element tag)
        && (elemNodesList (· == "details") #[] (docNodesOf doc).toList).size == 1)
    let twin := MarkdownDoc.emit doc
    t s!"{opener}: the twin writes the element back, read to the same document"
      (hasStr twin (opener ++ "\n<summary>Amber</summary>\n") && (elabMd twin).1.body == doc.body
        && (elabMd twin).2.isEmpty)
    t s!"{opener}: no artifact loses anything, and nothing is named" ds.isEmpty
    for (marker, label) in [("-", "bullet"), ("1.", "ordered")] do
      let pad := String.ofList (List.replicate (marker.length + 1) ' ')
      let item := s!"{marker} {opener}\n{pad}<summary>Amber</summary>\n\n{pad}Cedar\n{pad}</details>\n" ++
        s!"{marker} Birch\n"
      let flat := s!"{marker} **Amber**\n\n{pad}Cedar\n{marker} Birch\n"
      t s!"{opener}: a disclosure opening a {label} item takes its marker beside the summary"
        (shippedLinesOf fonts (elabMd item).1 == shippedLinesOf fonts (elabMd flat).1)
  let css := HtmlDoc.baseCss {} (elabMd ("<details>" ++ body)).1
  let print := ((css.splitOn "@media print {").drop 1).headD ""
  t "the print sheet shows a closed disclosure's body and no toggle marker"
    (hasStr ((print.splitOn "\n}\n").headD "") "details::details-content { content-visibility: visible; }"
      && hasStr ((print.splitOn "\n}\n").headD "") "summary { list-style: none; }")
  t "the driver reports for each artifact, the markdown twin included"
    (DriverAssets.diagnosticOutputs #[.pdf] == #[.pdf]
      && DriverAssets.diagnosticOutputs #[.html] == #[.html]
      && DriverAssets.diagnosticOutputs #[.md] == #[.md]
      && DriverAssets.diagnosticOutputs #[.pdf, .html, .md] == #[.pdf, .html, .md])
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "note.md") ("<details>" ++ body)
    let (host, ds) ← elabInputSrc (dir / "host.tex").toString
      (dvDoc "\\usepackage{markdown}\n" "\\markdownInput{note.md}")
    t "a tex host ships its note's disclosure as the element, no loss"
      (hasStr (docTreeOf host) (element "<details>") && ds.all (·.severity == .note))

end Tests
