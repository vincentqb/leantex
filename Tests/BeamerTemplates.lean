module

public import Tests.Support

public section

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
  let mathFonts ← mathSetOf fonts
  let mathModes := [("dollar", "$", "$"), ("parentheses", "\\(", "\\)"),
      ("brackets", "\\[", "\\]"), ("ensuremath", "\\ensuremath{", "}")] ++
    (Elab.displayMathEnvs.map (·.1) ++ Elab.alignEnvs.map (·.1)).map
      (fun n => (n, s!"\\begin\{{n}}", s!"\\end\{{n}}"))
  for (mode, first, last) in mathModes do
    let wrap := fun s => "\\documentclass{article}\\begin{document}" ++
      first ++ s ++ last ++ "\\end{document}"
    let (actual, ds) := elabStr (wrap "a + \\raisebox{1pt}{\\sum_k R_k} + z^2")
    let expected := (elabStr (wrap "a + {\\sum_k R_k} + z^2")).1
    let html := (templateHtml actual).toList
    t s!"math mode {mode}: the math parser owns containment"
      (ds.any (·.code == "W0389") &&
        !ds.any (fun d => d.code == "W0012" ||
          (d.code == "W0104" && d.subject == some "ctrl:raisebox")))
    t s!"math mode {mode}: containment preserves shipped mathematical ink"
      (reprStr (layoutOf mathFonts actual).pages == reprStr (layoutOf mathFonts expected).pages &&
        nodeTextList "" html == nodeTextList "" (templateHtml expected).toList)
    t s!"math mode {mode}: the HTML math node retains its authored source"
      ((elemAttrsList (· == "math") #[] html).any (fun (_, attrs) =>
        attrs.any (fun (key, value) =>
          key == "data-tex" && hasStr value "\\raisebox {1pt}")))
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
    ("\\framefoot{\\fontsize{8pt}{9.5pt}\\selectfont\\bfseries Example title}" ++ frames))).1
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
  -- beamerbasefont.sty stores one local definition per font axis.
  -- Nonstarred calls replace supplied axes only; starred calls clear all.
  -- The reference probe reads \f@size/\f@shape/\f@series after selection.
  let sized := "\\fontsize{8pt}{9.5pt}\\selectfont"
  for (label, changes, fontCommands) in
      [("merge axes", "\\setbeamerfont{footline}{shape=\\itshape}",
          sized ++ "\\itshape\\bfseries"),
       ("star resets", "\\setbeamerfont*{footline}{shape=\\itshape}", "\\itshape"),
       ("star clears", "\\setbeamerfont*{footline}{}", ""),
       ("empty axis clears", "\\setbeamerfont{footline}{series={}}", sized),
       ("size replaces", "\\setbeamerfont{footline}{size=\\Large}",
          "\\fontsize{14.4pt}{18pt}\\selectfont\\bfseries"),
       ("size aliases replace", "\\setbeamerfont{footline}{size*={11pt}{13pt}}",
          "\\fontsize{11pt}{13pt}\\selectfont\\bfseries"),
       ("size alias returns", "\\setbeamerfont{footline}{size*={11pt}{13pt}}" ++
          "\\setbeamerfont{footline}{size=\\scriptsize}", sized ++ "\\bfseries"),
       ("braced values", "\\setbeamerfont*{footline}{size={\\scriptsize},series={\\bfseries}}",
          sized ++ "\\bfseries")] do
    let (actual, ds) := elabStr (templateDeck (fontDecl ++ changes ++ numbered) frames)
    let expected := (elabStr (templateDeck "\\chrome{footer={right=\\framefraction}}"
      ("\\framefoot{" ++ fontCommands ++
        (if fontCommands.isEmpty then "" else " ") ++ "Example title}" ++ frames))).1
    t s!"footer font {label}: selected fields reach both outputs"
      (!ds.any (fun d => d.severity == .error || d.code == "W0301") &&
        reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts expected).pages &&
        templateHtmlFacts actual == templateHtmlFacts expected)
  let italicUpdate := "\\setbeamerfont{footline}{shape=\\itshape}"
  let italicFont := (elabStr (templateDeck "\\chrome{footer={right=\\framefraction}}"
    ("\\framefoot{" ++ sized ++ "\\itshape\\bfseries Example title}" ++ frames))).1
  for (first, last) in [("{", "}")] ++
      Compat.groupPrimitives.map (fun (first, last) => ("\\" ++ first ++ " ", "\\" ++ last ++ " ")) do
    let inner := "\\setbeamerfont*{footline}{size=\\Large,series=\\mdseries}"
    let (actual, ds) := elabStr (templateDeck
      (fontDecl ++ first ++ inner ++ last ++ italicUpdate ++ numbered) frames)
    t s!"footer font scope {first}: a later update sees the restored fields"
      (!ds.any (fun d => d.severity == .error) &&
        reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts italicFont).pages &&
        templateHtmlFacts actual == templateHtmlFacts italicFont)
  for (first, last) in Compat.groupPrimitives do
    let (_, plainDs) := elabStr ("\\documentclass{article}\\" ++ first ++
      " \\v@final\\" ++ last ++ " \\begin{document}Text\\end{document}")
    t s!"font scope {first}: unrelated preambles retain their primitive diagnostics"
      ([first, last].all fun n => plainDs.any fun d =>
        d.code == "W0301" && d.subject == some ("ctrl:" ++ n))
    let (_, openDs) := elabStr (templateDeck ("\\" ++ first ++ " ") frames)
    t s!"font scope {first}: an unmatched opener retains its diagnostic"
      (openDs.any fun d => d.code == "W0301" && d.subject == some ("ctrl:" ++ first))
  for hook in ["AtEndPreamble", "AtBeginDocument"] do
    let actual := (elabStr (templateDeck
      (fontDecl ++ "\\" ++ hook ++ "{" ++ italicUpdate ++ "}" ++ numbered) frames)).1
    t s!"footer font hook {hook}: updates merge with the captured font"
      (reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts italicFont).pages &&
        templateHtmlFacts actual == templateHtmlFacts italicFont)
  let titleBar := "\\palette{frametitlebg=#eeeeee,frametitlefg=#111111}"
  let titleFont := "\\setbeamerfont*{frametitle}{size=\\Large,series=\\bfseries}"
  for (label, changes, commands) in
      [("merge", "\\setbeamerfont{frametitle}{shape=\\itshape}", "\\Large\\itshape\\bfseries"),
       ("replace size", "\\setbeamerfont{frametitle}{size=\\small}", "\\small\\bfseries"),
       ("reset", "\\setbeamerfont*{frametitle}{shape=\\itshape}", "\\itshape"),
       ("clear", "\\setbeamerfont*{frametitle}{}", ""),
       ("empty key", "\\setbeamerfont{frametitle}{series={}}", "\\Large"),
       ("selection order", "\\setbeamerfont{frametitle}{series=\\mdseries,shape=\\bfseries}",
          "\\Large\\bfseries\\mdseries"),
       ("scope", "{\\setbeamerfont*{frametitle}{size=\\small}}" ++
          "\\setbeamerfont{frametitle}{shape=\\itshape}", "\\Large\\itshape\\bfseries")] do
    let (actual, ds) := elabStr (templateDeck (titleBar ++ titleFont ++ changes) frames)
    let expected := (elabStr (templateDeck
      (titleBar ++ "\\style{frametitle}{font={" ++ commands ++ "}}") frames)).1
    t s!"mapped font {label}: shared capture preserves both output styles"
      (!ds.any (fun d => d.severity == .error || d.code == "W0301") &&
        reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts expected).pages &&
        (HtmlDoc.emit {} actual).1 == (HtmlDoc.emit {} expected).1)
  let emptyFooter := "\\setbeamertemplate{footline}{}"
  let blank := (elabStr (templateDeck "\\runningfoot{\\hfill}"
    ("\\framefoot{}" ++ frames))).1
  for pre in [emptyFooter, fontDecl ++ numbered ++ emptyFooter,
      fontDecl ++ numbered ++ "\\AtEndPreamble{" ++ emptyFooter ++ "}",
      fontDecl ++ numbered ++ "\\AtBeginDocument{" ++ emptyFooter ++ "}"] do
    let (actual, ds) := elabStr (templateDeck pre frames)
    t "empty footer: clears the whole captured band"
      (!ds.any (fun d => d.severity == .error) &&
        reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts blank).pages &&
        templateHtmlFacts actual == templateHtmlFacts blank)
  let restored := (elabStr (templateDeck
    (fontDecl ++ numbered ++ "{" ++ emptyFooter ++ "}") frames)).1
  t "footer scope: a local empty template does not clear the outer template"
    (reprStr (layoutOf fonts restored).pages == reprStr (layoutOf fonts nativeFont).pages &&
      templateHtmlFacts restored == templateHtmlFacts nativeFont)
  let (_, nonemptyDs) := elabStr (templateDeck
    "{\\setbeamerfont*{frametitle}{size=\\small}Payload}" frames)
  t "font scope: consuming a local declaration never hides nondeclaration content"
    (nonemptyDs.any (·.code == "E0313"))
  let replaced := (elabStr (templateDeck (emptyFooter ++ fontDecl ++ numbered) frames)).1
  t "footer replacement: a later numbered template replaces an empty template"
    (reprStr (layoutOf fonts replaced).pages == reprStr (layoutOf fonts nativeFont).pages &&
      templateHtmlFacts replaced == templateHtmlFacts nativeFont)
  let (refused, ds) := elabStr (templateDeck
    "\\setbeamertemplate{footline}{Payload\\setbeamertemplate{frame footer}{Nested}}"
    frames)
  let plain := (elabStr (templateDeck "" frames)).1
  t "unknown template: one refusal owns the entire body"
    ((ds.filter (·.code == "E0111")).size == 1 &&
      reprStr (layoutOf fonts refused).pages == reprStr (layoutOf fonts plain).pages &&
      templateHtmlFacts refused == templateHtmlFacts plain)
