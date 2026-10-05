import Tests.Support

open LeanTex.Core

private def templateDeck (pre body : String) : String :=
  "\\documentclass{beamer}\\theme{default}\\title{Example title}" ++ pre ++
    "\\begin{document}" ++ body ++ "\\end{document}"

private def templateHtml (doc : Ir.Doc) : Array Html.Node :=
  let (_, tree, _) := HtmlDoc.emitTree {} doc
  tree

private def templateHtmlFacts (doc : Ir.Doc) :=
  let tree := (templateHtml doc).toList
  (elemAttrsList (fun _ => true) #[] tree, nodeTextList "" tree)

/-- Beamer's marker templates and numbered footer carry content. Their
native translations must preserve that content in both shipped outputs,
including the distinction between an overlay and a numbered frame. -/
def beamerTemplateChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  for datum in ["title", "subtitle", "author", "institute", "date"] do
    for (decl, short) in
        [(s!"\\{datum} [Brief]\{Extended}", "Brief"),
         (s!"\\{datum}[Old]\{Old full}\\{datum}\{Extended}", "Extended"),
         (s!"\\{datum}[]\{Extended}", "")] do
      for inBody in [false, true] do
        let content := s!"\\begin\{frame}\{Metadata}\\insertshort{datum}|\\insert{datum}\\end\{frame}"
        let pre := if inBody then "" else decl
        let body := (if inBody then decl else "") ++ content
        let (actual, ds) := elabStr (templateDeck pre body)
        let expected := (elabStr (templateDeck pre
          ((if inBody then decl else "") ++
            s!"\\begin\{frame}\{Metadata}{short}|Extended\\end\{frame}"))).1
        t s!"metadata inserts {datum}: declared short form and fallback reach both outputs"
          (!ds.any (fun d => d.severity == .error || d.code == "W0301") &&
            reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts expected).pages &&
            templateHtmlFacts actual == templateHtmlFacts expected)
  let items := "\\begin{frame}{Items}\\begin{itemize}\\item First" ++
    "\\begin{itemize}\\item Second\\begin{itemize}\\item Third" ++
    "\\end{itemize}\\end{itemize}\\end{itemize}\\end{frame}"
  for (element, native, marker) in
      [("itemize item", "itemize", "A"),
       ("itemize subitem", "itemize2", "B"),
       ("itemize subsubitem", "itemize3", "C")] do
    let (actual, ds) := elabStr (templateDeck
      s!"\\setbeamertemplate\{{element}}\{{marker}}" items)
    let expected := (elabStr (templateDeck
      s!"\\style\{{native}}\{marker=\{{marker}}}" items)).1
    t s!"marker template {element}: no content loss"
      (!ds.any (fun d => d.severity == .error || d.code == "W0301"))
    t s!"marker template {element}: native PDF and HTML content"
      (reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts expected).pages &&
        templateHtmlFacts actual == templateHtmlFacts expected)
    for decl in [s!"\\setbeamertemplate\{{element}}\{{marker}}",
        s!"\\style\{{native}}\{marker=\{{marker}}}"] do
      let (hooked, hookDs) := elabStr (templateDeck
        ("\\AtBeginDocument{" ++ decl ++ "\\framefoot{Hook note}}") items)
      let hookNative := (elabStr (templateDeck
        s!"\\style\{{native}}\{marker=\{{marker}}}"
        ("\\framefoot{Hook note}" ++ items))).1
      t s!"marker hook {element}: both style arguments stay together; the following note stays in the body"
        (!hookDs.any (fun d => d.severity == .error || d.code == "W0301") &&
          reprStr (layoutOf fonts hooked).pages == reprStr (layoutOf fonts hookNative).pages &&
          templateHtmlFacts hooked == templateHtmlFacts hookNative)
  let (raised, raiseDs) := elabStr (templateDeck
    "\\setbeamertemplate{itemize item}{\\raisebox{0.18ex}[1ex][0pt]{\\scriptsize A}}"
    items)
  let raisedNative := (elabStr (templateDeck
    "\\style{itemize}{marker={\\scriptsize A}}" items)).1
  t "raised marker: unmodelled geometry is named and never becomes ink"
    (raiseDs.any (fun d => d.code == "W0104" && d.subject == some "ctrl:raisebox") &&
      !raiseDs.any (fun d => d.severity == .error || d.code == "W0301") &&
      reprStr (layoutOf fonts raised).pages == reprStr (layoutOf fonts raisedNative).pages &&
      templateHtmlFacts raised == templateHtmlFacts raisedNative)
  let footer (counter : String) :=
    "\\setbeamertemplate{footline}{" ++
      "\\begin{beamercolorbox}[wd=\\paperwidth,ht=2.6ex,dp=1.2ex,leftskip=0.8cm,rightskip=0.8cm]{footline}" ++
      "\\usebeamerfont{footline}\\insertshorttitle\\hfill" ++ counter ++
      "\\end{beamercolorbox}}"
  let frames := "\\begin{frame}{First}One\\pause Two\\end{frame}" ++
    "\\begin{frame}{Second}Three\\end{frame}"
  for (counter, expected) in
      [("\\insertframenumber", #[("Example title", "1"), ("Example title", "2")]),
       ("\\insertframenumber\\,/\\,\\inserttotalframenumber",
        #[("Example title", "1 / 2"), ("Example title", "2 / 2")])] do
    let (doc, ds) := elabStr (templateDeck
      ("\\setbeamerfont{footline}{size=\\scriptsize}" ++ footer counter) frames)
    t s!"numbered template {counter}: body preserved without errors"
      (!ds.any (fun d => d.severity == .error || d.code == "W0301"))
    t s!"numbered template {counter}: Layout.Out counts frames, not overlays"
      (dedupConsecutive (pdfFoots (layoutOf fonts doc)) == expected)
    t s!"numbered template {counter}: HTML uses the same footer and frame count"
      (slideFootsList #[] (templateHtml doc).toList == expected)
  let fontDecl := "\\setbeamerfont{footline}{size=\\scriptsize,series=\\bfseries}"
  let numbered := footer "\\insertframenumber\\,/\\,\\inserttotalframenumber"
  let nativeFont := (elabStr (templateDeck
    "\\chrome{footer={right=\\framefraction}}"
    ("\\framefoot{\\bfseries\\fontsize{8pt}{9.5pt}\\selectfont Example title}" ++ frames))).1
  let defaultFont := (elabStr (templateDeck
    "\\chrome{footer={right=\\framefraction}}"
    ("\\framefoot{Example title}" ++ frames))).1
  for pre in [fontDecl ++ numbered, numbered ++ fontDecl,
      "\\AtEndPreamble{" ++ numbered ++ fontDecl ++ "}"] do
    let (doc, ds) := elabStr (templateDeck pre frames)
    t "numbered template: final font declaration reaches the footer note"
      (!ds.any (fun d => d.severity == .error ||
          (d.code == "W0104" && d.subject == some "beamer:setbeamerfont:footline")) &&
        reprStr (layoutOf fonts doc).pages == reprStr (layoutOf fonts nativeFont).pages &&
        templateHtmlFacts doc == templateHtmlFacts nativeFont)
  t "numbered template: honoured font changes both artifacts"
    (reprStr (layoutOf fonts nativeFont).pages != reprStr (layoutOf fonts defaultFont).pages &&
      templateHtmlFacts nativeFont != templateHtmlFacts defaultFont)
  let (refused, ds) := elabStr (templateDeck
    "\\setbeamertemplate{footline}{Payload\\setbeamertemplate{frame footer}{Nested}}"
    frames)
  let plain := (elabStr (templateDeck "" frames)).1
  t "unknown template: one refusal owns the entire body"
    ((ds.filter (·.code == "E0111")).size == 1 &&
      reprStr (layoutOf fonts refused).pages == reprStr (layoutOf fonts plain).pages &&
      templateHtmlFacts refused == templateHtmlFacts plain)
