module

public import Tests.Support
public import Tests.StandoutPalette

public section

open LeanTex.Core

private def hookDeck (pre body : String) : String :=
  "\\documentclass{beamer}\n\\theme{default}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

private def hookBlocks (skip : String := "") : String :=
  "\\begin{frame}[t]{Spacing}\n" ++
    "\\begin{block}{First title}" ++ skip ++ " FirstBody\\end{block}\n" ++
    "\\begin{block}{Second title}" ++ skip ++ " SecondBody\\end{block}\n" ++
    "\\begin{alertblock}{Alert title}AlertBody\\end{alertblock}\n\\end{frame}"

private def hookHtml (doc : Ir.Doc) : Array Html.Node :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  body

/-- Tags and attributes of the typed tree, in order, together with its text.
In particular an empty spacing block must have the native block's own
spacing attributes; merely retaining the title and body text is not enough. -/
private def hookHtmlFacts (doc : Ir.Doc) :
    Array (String × Array (String × String)) × String :=
  let tree := hookHtml doc
  (elemAttrsList (fun _ => true) #[] tree.toList, nodeTextList "" tree.toList)

private def standoutFooterBody : String :=
  "\\ifbeamertemplateempty{frame footer}{}{" ++
    "\\setbeamercolor{footline}{use={standout,background canvas}," ++
      "fg=standout.fg,bg=background canvas.bg}" ++
    "\\setbeamertemplate{footline}[plain]" ++
    "\\ifbeamer@noframenumbering\\setbeamertemplate{page number in head/foot}{}\\fi}"

private def standoutFooterHook (body : String := standoutFooterBody)
    (success : String := "")
    (failure : String := "\\PackageError{probe}{PatchFailure}{PatchHelp}") : String :=
  "\\makeatletter\\apptocmd{\\KV@beamerframe@standout}{" ++ body ++ "}{" ++
    success ++ "}{" ++ failure ++ "}\\makeatother"

/-- A preamble block-begin hook appends its supported skips immediately
after each ordinary block title, exactly as an explicit skip at that point
does. Unsupported bodies are consumed whole and named, never recovered as
page content. The footer and error-control cases hold already-working
compatibility alongside the live spacing regression. -/
def beamerHookChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  Tests.StandoutPalette.standoutPaletteChecks ref fonts
  let t := check ref
  let hook (after : String) :=
    "\\addtobeamertemplate{block begin}{}{" ++ after ++ "}"
  let plain := (elabStr (hookDeck "" (hookBlocks))).1
  let plainPages := reprStr (layoutOf fonts plain).pages
  let plainHtml := hookHtmlFacts plain
  for skips in ["\\smallskip", "\\medskip", "\\bigskip",
      " \\smallskip\n\\medskip "] do
    let (actual, ds) := elabStr (hookDeck (hook skips) (hookBlocks))
    let (expected, expectedDs) := elabStr (hookDeck "" (hookBlocks skips))
    t s!"beamer hook {skips}: explicit spacing probe has no losses"
      (!expectedDs.any (fun d => d.severity == .error || d.code == "W0301"))
    t s!"beamer hook {skips}: Layout.Out equals explicit body spacing"
      (reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts expected).pages)
    t s!"beamer hook {skips}: typed HTML equals explicit body spacing"
      (hookHtmlFacts actual == hookHtmlFacts expected)
    t s!"beamer hook {skips}: both artifacts differ from no hook"
      (reprStr (layoutOf fonts actual).pages != plainPages && hookHtmlFacts actual != plainHtml)
    t s!"beamer hook {skips}: translation is accounted without a loss"
      (ds.any (fun d => d.code == "N0100" && hasStr d.message "addtobeamertemplate") &&
       !ds.any (fun d => d.severity == .error || d.code == "W0104" || d.code == "W0387"))
  let actual := (elabStr (hookDeck (hook "\\smallskip") (hookBlocks))).1
  let firstY (doc : Ir.Doc) (text : String) :=
    (bodyLines (layoutOf fonts doc)).findSome? fun line =>
      if lineText line == text then some line.y else none
  -- latex.ltx: \smallskipamount = 3pt plus 1pt minus 1pt. A top-aligned
  -- frame has no vertical justification, so the added natural gap is 3pt.
  t "beamer hook: first body baseline moves by the natural smallskip"
    (match firstY actual "FirstBody", firstY plain "FirstBody" with
     | some a, some b => a - b == 3 * 65536
     | _, _ => false)
  t "beamer hook: first title baseline stays put"
    ((firstY actual "First title").isSome &&
      firstY actual "First title" == firstY plain "First title")
  let twice := (elabStr (hookDeck (hook "\\smallskip" ++ hook "\\medskip") (hookBlocks))).1
  let twiceNative := (elabStr (hookDeck "" (hookBlocks "\\smallskip\\medskip"))).1
  t "beamer hook: successive additions compose in both artifacts"
    (reprStr (layoutOf fonts twice).pages == reprStr (layoutOf fonts twiceNative).pages &&
      hookHtmlFacts twice == hookHtmlFacts twiceNative)
  -- A preamble macro can be defined before the hook is declared. The
  -- template is read when the block is used, after the preamble finishes.
  let macroSource := "\\newcommand{\\panel}{\\begin{block}{Macro title}MacroBody\\end{block}}\n"
  let macroNative := "\\newcommand{\\panel}{\\begin{block}{Macro title}\\smallskip MacroBody\\end{block}}\n"
  let macroFrame := "\\begin{frame}[t]{Macro}\\panel\\end{frame}"
  let fromMacro := (elabStr (hookDeck (macroSource ++ hook "\\smallskip") macroFrame)).1
  let nativeMacro := (elabStr (hookDeck macroNative macroFrame)).1
  t "beamer hook: a block defined before the hook receives the gap at use"
    (reprStr (layoutOf fonts fromMacro).pages == reprStr (layoutOf fonts nativeMacro).pages &&
      hookHtmlFacts fromMacro == hookHtmlFacts nativeMacro)
  let (deferred, deferredDs) := elabStr
    (hookDeck ("\\AtEndPreamble{" ++ hook "\\smallskip" ++ "}") (hookBlocks))
  t "beamer hook: an end-preamble addition reaches both artifacts"
    (!deferredDs.any (fun d => d.severity == .error || d.code == "W0104") &&
      reprStr (layoutOf fonts deferred).pages == reprStr (layoutOf fonts actual).pages &&
      hookHtmlFacts deferred == hookHtmlFacts actual)
  let (empty, emptyDs) := elabStr (hookDeck (hook "") (hookBlocks))
  t "beamer hook: an empty addition is an accounted identity"
    (reprStr (layoutOf fonts empty).pages == plainPages && hookHtmlFacts empty == plainHtml &&
      emptyDs.any (fun d => d.code == "N0100" && hasStr d.message "addtobeamertemplate") &&
      !emptyDs.any (·.code == "W0104"))
  for (element, before, after) in
      [("block begin", "", "HookPayload"),
       ("block begin", "HookPrefix", "\\smallskip"),
       ("footline", "", "HookPayload"),
       ("block begin", "", "\\smallskip\\setbeamertemplate{frame footer}{HookPayload}")] do
    let source := "\\addtobeamertemplate{" ++ element ++ "}{" ++ before ++ "}{" ++ after ++ "}"
    let (refused, ds) := elabStr (hookDeck source (hookBlocks))
    t s!"beamer hook refusal {element}/{before}/{after}: one dropped-body diagnostic"
      ((ds.filter (·.code == "E0111")).size == 1 &&
        !ds.any (fun d => d.code == "E0304" || d.code == "W0301"))
    t s!"beamer hook refusal {element}/{before}/{after}: neither artifact gains body spill"
      (reprStr (layoutOf fonts refused).pages == plainPages && hookHtmlFacts refused == plainHtml)
  for source in ["\\addtobeamertemplate{block end}{}{\\smallskip}",
      "\\addtobeamertemplate{block begin}{\\smallskip}{}"] do
    let (refused, ds) := elabStr (hookDeck source (hookBlocks))
    t s!"beamer hook unsupported site {source}: configuration refusal without changing the page"
      (ds.any (·.code == "W0104") && !ds.any (·.severity == .error) &&
        reprStr (layoutOf fonts refused).pages == plainPages && hookHtmlFacts refused == plainHtml)
  -- A bare preamble group already has E0313, independently of its hook.
  -- Refusing a scoped hook must not change that baseline or set a global gap.
  let (groupPlain, groupPlainDs) := elabStr (hookDeck "{}" (hookBlocks))
  let (groupHook, groupDs) := elabStr (hookDeck ("{" ++ hook "\\smallskip" ++ "}") (hookBlocks))
  t "beamer hook: a grouped preamble addition changes neither artifact nor existing errors"
    (groupDs.any (·.code == "W0104") &&
      (groupDs.filter (·.severity == .error)).map (·.code) ==
        (groupPlainDs.filter (·.severity == .error)).map (·.code) &&
      reprStr (layoutOf fonts groupHook).pages == reprStr (layoutOf fonts groupPlain).pages &&
      hookHtmlFacts groupHook == hookHtmlFacts groupPlain)
  let (bodyHook, localDs) := elabStr (hookDeck "" (hook "\\smallskip" ++ hookBlocks))
  t "beamer hook: a body declaration is refused without applying a global approximation"
    (localDs.any (·.code == "W0104") && !localDs.any (·.severity == .error) &&
      reprStr (layoutOf fonts bodyHook).pages == plainPages && hookHtmlFacts bodyHook == plainHtml)
  let footerWrapper (command : String) :=
    "\\newenvironment{notedframe}[1]{" ++ command ++ "{\\scriptsize #1}}{" ++ command ++ "{}}\n"
  let footerBody :=
    "\\begin{notedframe}{FooterNote}\\begin{frame}{Footer}FooterBody\\end{frame}" ++
      "\\end{notedframe}\\begin{frame}{Cleared}ClearBody\\end{frame}"
  let (footer, footerDs) := elabStr
    (hookDeck (footerWrapper "\\setbeamertemplate{frame footer}") footerBody)
  let nativeFooter := (elabStr (hookDeck (footerWrapper "\\framefoot") footerBody)).1
  t "beamer footer: nested frame-footer setters already match native artifacts"
    (!footerDs.any (·.severity == .error) &&
      reprStr (layoutOf fonts footer).pages == reprStr (layoutOf fonts nativeFooter).pages &&
      hookHtmlFacts footer == hookHtmlFacts nativeFooter &&
      treeOccurs (hookHtml footer) "FooterNote" == 1)
  let (dropped, droppedDs) := elabStr (hookDeck
    "\\setbeamertemplate{footline}{FooterPayload\\setbeamertemplate{frame footer}{NestedPayload}}"
    (hookBlocks))
  t "beamer footer: an unsupported outer template owns the whole refusal"
    ((droppedDs.filter (·.code == "E0111")).size == 1 &&
      reprStr (layoutOf fonts dropped).pages == plainPages && hookHtmlFacts dropped == plainHtml)
  let (logged, logDs) := elabStr (hookDeck
    "\\AtBeginDocument{\\PackageError{probe}{LogPayload}{HelpPayload}}" (hookBlocks))
  t "beamer error control: PackageError already consumes all groups through a deferred hook"
    (logDs.any (fun d => d.code == "W0387" && d.subject == some "ctrl:PackageError") &&
      !logDs.any (fun d => d.code == "W0301" || d.severity == .error) &&
      reprStr (layoutOf fonts logged).pages == plainPages && hookHtmlFacts logged == plainHtml)
  let footerPre := "\\chrome{footer={left=\\sectiontitle,right=\\framefraction}}"
  let frames :=
    "\\framefoot{\\scriptsize StandoutNote}" ++
    "\\begin{frame}[standout]{Focus}StandoutBody\\end{frame}" ++
    "\\framefoot{}\\begin{frame}[standout]{Empty}EmptyBody\\end{frame}" ++
    "\\framefoot{NormalNote}\\begin{frame}{Normal}NormalBody\\end{frame}" ++
    "\\framefoot{}\\begin{frame}{Clear}ClearBody\\end{frame}"
  let build (pre : String) := elabStr (hookDeck (footerPre ++ pre) frames)
  let (without, _) := build ""
  let (restored, restoreDs) := build (standoutFooterHook)
  let out := layoutOf fonts restored
  let html := hookHtml restored
  let expected := #[("StandoutNote", ""), ("NormalNote", "3 / 4"), ("", "4 / 4")]
  t "standout footer hook: Layout.Out restores only the explicit note, without a number"
    (pdfFoots out == expected &&
      (out.pages[0]?.map fun p => p.lines.any (fun l => lineText l == "StandoutNote")) == some true)
  t "standout footer hook: typed HTML restores the same note and ordinary numbered bands"
    (slideFootsList #[] html.toList == expected && treeOccurs html "StandoutNote" == 1)
  let look := (Ir.Design.ofDoc restored).standout
  t "standout footer hook: the restored band uses the standout foreground and canvas"
    ((out.pages[0]?.bind (·.footLook)) == some { fg := look.fg, bar := some look.bg } &&
      (elemStylesList #[] html.toList).any (fun (text, style) =>
        text == "StandoutNote" && hasStr style s!"color: {look.fg.css}" &&
          hasStr style s!"background: {look.bg.css}"))
  t "standout footer hook: no restoration or number is invented for an empty note"
    ((out.pages[1]?.bind (·.foot)).isNone)
  t "standout footer hook: a successful patch does not execute its failure callback"
    (!restoreDs.any (fun d =>
      d.severity == .error || d.code == "W0301" || d.code == "W0104" || d.code == "W0387") &&
      restoreDs.any (fun d => d.code == "N0100" && hasStr d.message "apptocmd") &&
      treeOccurs html "PatchFailure" == 0 && treeOccurs html "PatchHelp" == 0)
  let withoutOut := layoutOf fonts without
  t "standout footer hook: unpatched standout remains plain and later ordinary pages are unchanged"
    (pdfFoots withoutOut == expected.extract 1 expected.size &&
      reprStr (out.pages.extract 2 out.pages.size) ==
        reprStr (withoutOut.pages.extract 2 withoutOut.pages.size))
  let (native, nativeDs) := build "\\chrome{standout-note=true}"
  t "standout footer hook: the native setting and the bounded patch ship the same artifacts"
    (!nativeDs.any (·.severity == .error) &&
      reprStr (layoutOf fonts native).pages == reprStr out.pages &&
      hookHtmlFacts native == hookHtmlFacts restored)
  let dormant :=
    "\\iftrue\\PackageError{probe}{DormantError}{}\\fi" ++
    "\\AtBeginDocument{DormantBody}\\IfPackageLoadedTF{etoolbox}{DormantYes}{DormantNo}" ++
    "\\begin{overprint}\\onslide<+->DormantOverlay\\end{overprint}"
  let (dormantDoc, dormantDs) := build (standoutFooterHook standoutFooterBody "" dormant)
  t "standout footer hook: an unselected callback is opaque to every preamble pass"
    (reprStr (layoutOf fonts dormantDoc).pages == reprStr out.pages &&
      hookHtmlFacts dormantDoc == hookHtmlFacts restored &&
      !dormantDs.any (fun d => d.severity == .error || d.code == "W0387" ||
        d.code == "W0105" || hasStr d.message "overprint" ||
        hasStr d.message "IfPackageLoadedTF" || hasStr d.message "AtBeginDocument"))
  -- A dormant delimited definition must not change a live macro's call
  -- syntax: the semicolon following its braced argument remains page text.
  let probePre := "\\newcommand{\\probe}[1]{#1}"
  let probeFrame := "\\begin{frame}{Delimiter}\\probe{A};\\end{frame}"
  let probePlain := (elabStr (hookDeck (probePre ++ standoutFooterHook) probeFrame)).1
  let (probeDormant, probeDs) := elabStr (hookDeck
    (probePre ++ standoutFooterHook standoutFooterBody "" "\\def\\probe#1;{#1}") probeFrame)
  t "standout footer hook: dormant delimiter syntax cannot consume shipped punctuation"
    (!probeDs.any (·.severity == .error) &&
      (bodyLines (layoutOf fonts probePlain)).any (fun l => lineText l == "A;") &&
      reprStr (layoutOf fonts probeDormant).pages == reprStr (layoutOf fonts probePlain).pages)
  t "standout footer hook: dormant delimiter syntax cannot consume HTML punctuation"
    (hasStr (hookHtmlFacts probePlain).2 "A;" &&
      hookHtmlFacts probeDormant == hookHtmlFacts probePlain)
  -- TeX takes one character for an unbraced argument, even when the lexer
  -- coalesces several into a word. Every prepass must own the same four.
  let tokenHook := "\\makeatletter\\apptocmd{\\KV@beamerframe@standout}{" ++
    standoutFooterBody ++ "}"
  for tail in ["X{\\AtBeginDocument{Leaked}}", "&{\\AtBeginDocument{Leaked}}",
      "XY", " X Y ", "{X}{\\AtBeginDocument{Leaked}}"] do
    let (refused, ds) := build (tokenHook ++ tail ++ "\\makeatother")
    t s!"standout footer hook token callbacks {tail}: one refusal owns all four arguments"
      ((ds.filter (·.severity == .error)).map (·.code) == #["E0111"] &&
        !ds.any (fun d => d.code == "W0301" || d.code == "W0387" ||
          hasStr d.message "AtBeginDocument"))
    t s!"standout footer hook token callbacks {tail}: neither artifact gains callback ink"
      (reprStr (layoutOf fonts refused).pages == reprStr withoutOut.pages &&
        hookHtmlFacts refused == hookHtmlFacts without)
  let (tokenFailure, tokenFailureDs) := build (tokenHook ++ "{}X\\makeatother")
  t "standout footer hook: a single character failure argument stays dormant after success"
    (!tokenFailureDs.any (·.severity == .error) &&
      reprStr (layoutOf fonts tokenFailure).pages == reprStr out.pages &&
      hookHtmlFacts tokenFailure == hookHtmlFacts restored)
  let tailFrame (text : String) := "\\begin{frame}{Tail}" ++ text ++ "\\end{frame}"
  let tailPlain := (elabStr (hookDeck "" (tailFrame "Tail"))).1
  for call in ["\\apptocmd ABCDTail", "\\apptocmd AB{}{}Tail",
      tokenHook ++ "XYTail\\makeatother"] do
    let (tailDoc, ds) := elabStr (hookDeck "" (tailFrame call))
    t s!"standout footer hook character arguments {call}: refusal preserves the word after argument four"
      ((ds.filter (·.severity == .error)).map (·.code) == #["E0111"] &&
        reprStr (layoutOf fonts tailDoc).pages == reprStr (layoutOf fonts tailPlain).pages &&
        hookHtmlFacts tailDoc == hookHtmlFacts tailPlain)
  for (body, success) in
      [(standoutFooterBody ++ "UnexpectedInk", ""),
       (standoutFooterBody.replace "bg=background canvas.bg" "bg=standout.fg", ""),
       (standoutFooterBody.replace "bg=background canvas.bg" "bg=background canvas.bg,UnknownKey", ""),
       ("\\iftrue" ++ standoutFooterBody ++ "\\fi", ""),
       (standoutFooterBody, "\\AtBeginDocument{SuccessBody}"),
       ("\\AtBeginDocument{PatchBody}", "")] do
    let (refused, ds) := build (standoutFooterHook body success dormant)
    t s!"standout footer hook refusal {body}/{success}: one whole-command refusal, no execution"
      ((ds.filter (·.code == "E0111")).size == 1 &&
        !ds.any (fun d => d.code == "W0301" || d.code == "W0387") &&
        reprStr (layoutOf fonts refused).pages == reprStr withoutOut.pages &&
        hookHtmlFacts refused == hookHtmlFacts without)
  let unbraced := (standoutFooterHook).replace "{\\KV@beamerframe@standout}"
    "\\KV@beamerframe@standout\n"
  let spacedBody := standoutFooterBody.replace "fg=standout.fg,bg=background canvas.bg"
    "fg = standout.fg, bg = background canvas.bg"
  for source in [unbraced, standoutFooterHook spacedBody " \n ",
      standoutFooterHook ++ "\\theme{default}"] do
    let (doc, ds) := build source
    t "standout footer hook: token target, key whitespace and later theme preserve the behavior"
      (!ds.any (fun d => d.severity == .error || d.code == "W0301" || d.code == "W0387") &&
        reprStr (layoutOf fonts doc).pages == reprStr out.pages &&
        hookHtmlFacts doc == hookHtmlFacts restored)
  let (disabled, disabledDs) := build
    (standoutFooterHook ++ "\\chrome{standout-note=false}\\theme{default}")
  t "standout footer hook: an explicit native false survives a later theme"
    (!disabledDs.any (·.severity == .error) &&
      reprStr (layoutOf fonts disabled).pages == reprStr withoutOut.pages &&
      hookHtmlFacts disabled == hookHtmlFacts without)
  let (wrongTarget, wrongTargetDs) := build
    ((standoutFooterHook).replace "KV@beamerframe@standout" "unrelatedHook")
  t "standout footer hook: the same body on an unknown target is refused without executing callbacks"
    ((wrongTargetDs.filter (·.code == "E0111")).size == 1 &&
      !wrongTargetDs.any (fun d => d.code == "W0301" || d.code == "W0387") &&
      reprStr (layoutOf fonts wrongTarget).pages == reprStr withoutOut.pages &&
      hookHtmlFacts wrongTarget == hookHtmlFacts without)
  for (pre, body) in [("{" ++ standoutFooterHook ++ "}", frames),
      ("", standoutFooterHook ++ frames)] do
    let (scopedDoc, ds) := elabStr (hookDeck (footerPre ++ pre) body)
    t "standout footer hook: a scoped or body patch cannot set global footer policy"
      ((ds.filter (·.code == "E0111")).size == 1 &&
        !ds.any (fun d => d.code == "W0301" || d.code == "W0387") &&
        reprStr (layoutOf fonts scopedDoc).pages == reprStr withoutOut.pages &&
        hookHtmlFacts scopedDoc == hookHtmlFacts without)
  let titleBody := "\\framefoot{TitleNote}\\maketitle" ++ frames
  let titlePre := footerPre ++ "\\title{TitleProbe}"
  let titlePlain := (elabStr (hookDeck titlePre titleBody)).1
  let titleRestored := (elabStr (hookDeck (titlePre ++ standoutFooterHook) titleBody)).1
  t "standout footer hook: title pages stay plain even with an explicit note in force"
    (reprStr ((layoutOf fonts titlePlain).pages[0]?) ==
        reprStr ((layoutOf fonts titleRestored).pages[0]?) &&
      treeOccurs (hookHtml titleRestored) "TitleNote" == 0)
  let epochBody :=
    "\\palette{standoutfg=#F9F7F1,standoutbg=#18364A}\\framefoot{EpochNote}" ++
    "\\begin{frame}[standout]{Epoch}EpochBody\\end{frame}"
  let epoch := (elabStr (hookDeck (standoutFooterHook) epochBody)).1
  t "standout footer hook: paint resolves from the frame's palette epoch"
    (((layoutOf fonts epoch).pages[0]?.bind (·.footLook)) ==
        some { fg := { r := 249, g := 247, b := 241 }, bar := some { r := 24, g := 54, b := 74 } } &&
      (elemStylesList #[] (hookHtml epoch).toList).any (fun (text, style) =>
        text == "EpochNote" && hasStr style "color: #f9f7f1" &&
          hasStr style "background: #18364a"))
