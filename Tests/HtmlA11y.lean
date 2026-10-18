module

public import Tests.Backends

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! What assistive technology is handed, over every golden fixture's typed tree, judged by
`HtmlDoc.a11yFacts`, the judge the `htmla11y` tier reads. -/

/-- The stylesheet mode a document's page is emitted under: its own `\output{ css = … }`, read as
the driver reads it. -/
def a11yCssOf (doc : Ir.Doc) : HtmlDoc.CssMode :=
  match cssFor doc.output.css with
  | .own => .own
  | .bulma => .bulma
  | .none => .none

/-- One corpus fixture's page as its typed tree, built in-process as the driver builds it; a
boundary picture is its placeholder. -/
def a11yCorpusPage (n : String) :
    IO (Ir.Doc × Image.Store × Array Html.Node × Array Html.Node × Array Diag) := do
  let (doc, _) ← goldenDoc n
  -- A drawn figure's text shapes against the shipped face, as the driver shapes it.
  let fs ← match ← findFont with
    | some data => pure ((Font.parse data).toOption.map oneFaceOf)
    | none => pure none
  let store ← corpusStore doc fs
  -- A drawn figure's own title answers the alternative the document leaves undeclared.
  let doc := corpusTitled doc store
  let (head, body, diags) := HtmlDoc.emitTree { css := a11yCssOf doc, imgs := store } doc
  return (doc, store, head, body, diags)

/-- The judge's reading of one page: the stylesheet mode and the page model decide the scroll
containers. -/
def a11yFactsOf (doc : Ir.Doc) (body : Array Html.Node) : HtmlDoc.A11yFacts :=
  HtmlDoc.a11yFacts (a11yCssOf doc == .own) (doc.docClass.record.model == .frame) body

/-- The style sheets a page's head carries. -/
def headCss (head : Array Html.Node) : String :=
  String.join (head.toList.filterMap fun
    | .style c => some c
    | .elem .. | .text _ | .script .. => none)

/-- The tab stops a page leaves in reach inside pending steps it hides: those inside its overlay
steps where its stylesheet fades them from nothing yet keeps them in reach while pending. -/
def pendingTabStops (head : Array Html.Node) (f : HtmlDoc.A11yFacts) : Nat :=
  let css := headCss head
  if stepsFadeFromNothing css && !pendingStepsOutOfReach css then f.stepTabStops else 0

/-- A page's accessibility deficits, one count per check (`contrast`, `h1`, `hidden-focus`, `img`,
`landmarks`, `link`, `pending-focus`, `scope-marks`, `scroll`, `svg`), sorted by check name. -/
def a11yDeficits (doc : Ir.Doc) (head body : Array Html.Node) :
    List (String × Nat) :=
  let f := a11yFactsOf doc body
  [("contrast", (HtmlDoc.schemeFailures (a11yCssOf doc == .own) doc).length),
   ("h1", if f.h1s == 1 then 0 else 1),
   ("hidden-focus", f.hiddenTabStops),
   ("img", f.imgsUnnamed),
   ("landmarks", f.landmarksAlike),
   ("link", f.linksUnnamed),
   ("pending-focus", pendingTabStops head f),
   ("scope-marks", f.laidUnmarked),
   ("scroll", f.scrollsUnreachable),
   ("svg", f.svgsUnnamed)]

/-- Every golden fixture's deficits, built in-process from committed inputs
only: no browser, no network, no tool. -/
def a11yCorpus : IO (Array (String × List (String × Nat))) := do
  let mut out := #[]
  for n in goldenNames do
    let (doc, _, head, body, _) ← a11yCorpusPage n
    out := out.push (n, a11yDeficits doc head body)
  return out

/-- The `aria-label` of every `<svg>` a body carries. -/
def svgLabels (body : Array Html.Node) : Array (Option String) :=
  (elemAttrsList (· == "svg") #[] body.toList).map (HtmlDoc.attrOf? ·.2 "aria-label")

/-- The `alt` of every `<img>` a body carries. -/
def imgAlts (body : Array Html.Node) : Array (Option String) :=
  (elemAttrsList (· == "img") #[] body.toList).map (HtmlDoc.attrOf? ·.2 "alt")

/-- The format a file's first bytes declare among those a browser decodes in an `<img>` (PNG, JPEG,
GIF, WebP, and an SVG the resource boundary admits); `none` otherwise. -/
def sniffBrowserImage (b : ByteArray) : Option String :=
  let at' (i : Nat) (xs : List UInt8) : Bool :=
    xs.length + i ≤ b.size && (List.range xs.length).all fun k => b[i + k]! == xs[k]!
  if at' 0 [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A] then some "png"
  else if at' 0 [0xFF, 0xD8, 0xFF] then some "jpeg"
  else if at' 0 [0x47, 0x49, 0x46, 0x38] then some "gif"
  else if at' 0 [0x52, 0x49, 0x46, 0x46] && at' 8 [0x57, 0x45, 0x42, 0x50] then some "webp"
  -- An SVG the resource boundary admits is a browser image too.
  else if (Svg.judge b).toBool then some "svg"
  else none

/-- Every deck stage of a body — a `section` carrying the `slide` or
`section-page` class — as its `tabindex` and `aria-label`. -/
def stageMarks (body : Array Html.Node) : Array (Option String × Option String) :=
  ((elemAttrsList (· == "section") #[] body.toList).filter fun (_, attrs) =>
      (HtmlDoc.classTokens attrs).any (fun c => c == "slide" || c == "section-page")).map
    fun (_, attrs) => (HtmlDoc.attrOf? attrs "tabindex", HtmlDoc.attrOf? attrs "aria-label")

private def browserImageChecks (ref : IO.Ref (List String)) (name : String)
    (store : Image.Store) (body : Array Html.Node) (diags : Array Diag) : IO Nat := do
  let t := check ref
  let mut undecodableSeen := 0
  let uses := (elemAttrsList (fun _ => true) #[] body.toList).filterMap fun (tag, attrs) =>
    (HtmlDoc.attrOf? attrs (if tag == "img" then "src" else "data-image-src")).map fun src =>
      (src, (HtmlDoc.attrOf? attrs "data-image-index").bind String.toNat?)
  let marked := uses.filterMap (·.2)
  for k in Array.range store.entries.size do
    let en := store.entries[k]!
    if en.info.isNone || en.src.startsWith Ir.picSrcPrefix then continue
    let href := HtmlDoc.imageRequestHref store en.toRequest
    let sameSource := uses.filter (·.1 == href)
    if sameSource.isEmpty then continue
    let bytes ← IO.FS.readBinFile s!"testdata/corpus/{HtmlDoc.resolvedSrc en}"
    if (sniffBrowserImage bytes).isNone then
      for (_, index) in sameSource do
        t s!"html a11y {name}: '{href}' carries its emitted request index"
          (index.any fun i => (store.entries[i]?).any fun entry =>
            entry.info.isSome &&
            HtmlDoc.imageRequestHref store entry.toRequest == href)
      unless sameSource.any (·.2 == some k) do continue
      undecodableSeen := undecodableSeen + 1
      t s!"html a11y {name}: '{href}' no browser decodes, and a diagnostic names it"
        (diags.any fun d => d.subject == some s!"img:{k}:{href}")
  for d in diags do
    if d.code == "W0605" then
      let named := (Array.range store.entries.size).filter fun k =>
        d.subject == some s!"img:{k}:{HtmlDoc.resolvedSrc store.entries[k]!}"
      t s!"html a11y {name}: a browser-face loss names exactly one emitted request"
        (named.size == 1 && named.all marked.contains)
      for k in named do
        let href := HtmlDoc.resolvedSrc store.entries[k]!
        let bytes ← IO.FS.readBinFile s!"testdata/corpus/{href}"
        let decodes := (sniffBrowserImage bytes).isSome
        t s!"html a11y {name}: '{href}' is named undecodable only when it is" (!decodes)
  return undecodableSeen

/-- The HTML accessibility contract over the shipped corpus, with probes breaking each half once: no
unnamed svg, unreachable scroll container, tab stop under `aria-hidden`, or unnamed summary. -/
def htmlA11yChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Every inline `<svg>` is named and every declared scroll container reachable.
  let mut svgsSeen := 0
  let mut scrollsSeen := 0
  let mut summariesSeen := 0
  let mut undecodableSeen := 0
  let mut laidSeen := 0
  for n in goldenNames do
    let (doc, store, _, body, diags) ← a11yCorpusPage n
    let f := a11yFactsOf doc body
    laidSeen := laidSeen + f.laidParas
    t s!"html a11y {n}: every laid-out paragraph's hidden marks spell its scopes \
({f.laidUnmarked} of {f.laidParas} not)" (f.laidUnmarked == 0)
    svgsSeen := svgsSeen + f.svgs
    scrollsSeen := scrollsSeen + f.scrolls
    t s!"html a11y {n}: every svg is named ({f.svgsUnnamed} of {f.svgs} unnamed)"
      (f.svgsUnnamed == 0)
    t s!"html a11y {n}: every scroll container is reachable \
({f.scrollsUnreachable} of {f.scrolls} not)" (f.scrollsUnreachable == 0)
    -- The corpus holds no linked logo, so the probes below are what fire this.
    t s!"html a11y {n}: no tab stop is hidden from assistive technology \
({f.hiddenTabStops})" (f.hiddenTabStops == 0)
    summariesSeen := summariesSeen + f.summaries
    t s!"html a11y {n}: every disclosure's control is named \
({f.summariesUnnamed} of {f.summaries} not)" (f.summariesUnnamed == 0)
    t s!"html a11y {n}: every link is named ({f.linksUnnamed} of {f.links} not)"
      (f.linksUnnamed == 0)
    t s!"html a11y {n}: no two navigation landmarks are alike ({f.landmarksAlike})"
      (f.landmarksAlike == 0)
    -- No two stages share a name (a floor: the corpus repeats no title).
    let names := (stageMarks body).filterMap (·.2)
    t s!"html a11y {n}: no two stages share a name"
      (names.all fun nm => (names.filter (· == nm)).size == 1)
    -- Every `<img src>` is a format a browser decodes, by its bytes, or a diagnostic names it.
    undecodableSeen := undecodableSeen + (← browserImageChecks ref n store body diags)
  -- A pending step a deck hides is out of reach, its link included; at a covered share it shows,
  -- so in reach.
  let frame := "\\begin{frame}\nFirst words.\n\n\\uncover<2>{Second words " ++
    "\\href{https://example.org}{linked}.}\n\n\\pause\nThird \\href{https://example.org}{words}.\n" ++
    "\\end{frame}"
  for (label, pre, hides) in [("no share declared", "", true), ("beamer's invisible",
      "\\setbeamercovered{invisible}\n", true), ("beamer's transparent",
      "\\setbeamercovered{transparent}\n", false)] do
    let doc := (elabStr (dvDeck pre frame)).1
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let f := HtmlDoc.a11yFacts true true body
    let css := headCss head
    t s!"html a11y, {label}: the pending steps' links are step tab stops ({f.stepTabStops})"
      (f.stepTabStops == 2)
    let what := if hides then "fades from nothing, out of reach" else "covers at its share, in reach"
    t s!"html a11y, {label}: a pending step {what} until its reveal"
      (stepsFadeFromNothing css == hides && pendingStepsOutOfReach css == hides &&
        pendingTabStops head f == 0)
    t s!"html a11y, {label}: no step keyframe moves content" (stepsStandStill css)
    if hides then
      let reachable := head.map fun n => match n with
        | .style c => Html.Node.style ((c.splitOn "ltx-unhide").foldl (· ++ ·) "")
        | other => other
      t s!"html a11y, {label}: a stylesheet whose reveal opens in reach leaves both links in reach"
        (pendingTabStops reachable f == 2)
  t s!"html a11y: the corpus ships inline pictures ({svgsSeen})" (0 < svgsSeen)
  t s!"html a11y: the corpus ships scroll containers ({scrollsSeen})" (0 < scrollsSeen)
  t s!"html a11y: the corpus ships disclosures ({summariesSeen})" (0 < summariesSeen)
  t s!"html a11y: the corpus ships laid-out paragraphs ({laidSeen})" (0 < laidSeen)
  -- A scope the page shows by indentation alone, or a mark too few, leaves its bounds unspoken.
  let line (kids : Array Html.Node) := Html.elem "span" kids #[("class", "lines-line")]
  let scope (kids : Array Html.Node) := Html.elem "span" kids #[("class", "lines-scope")]
  let laid (kids : Array Html.Node) : Nat :=
    (HtmlDoc.a11yFacts true false #[Html.elem "p" kids #[("class", "lines")]]).laidUnmarked
  let opened := line (HtmlDoc.laidMark '(' 1 ++ #[Html.text "q"] ++ HtmlDoc.laidMark ')' 1)
  t "html a11y: a laid-out paragraph's scope spoken by its marks is marked, one unspoken is not"
    (laid #[line #[Html.text "p"], scope #[opened]] == 0 &&
      laid #[line #[Html.text "p"], scope #[line #[Html.text "q"]]] == 1 &&
      laid #[line #[Html.text "p"], scope #[scope #[opened]]] == 1)
  -- A summary holding no text, or only hidden text, names nothing.
  let judged (kids : Array Html.Node) (attrs : Array (String × String)) : Nat :=
    (HtmlDoc.a11yFacts true false #[Html.elem "details" #[Html.elem "summary" kids attrs]]).summariesUnnamed
  t "html a11y: a summary with no text is unnamed"
    (judged #[] #[] == 1 && judged #[Html.text "  "] #[] == 1
      && judged #[Html.elem "span" #[Html.text "Amber"] #[("hidden", "")]] #[] == 1)
  -- Characters a renderer draws as nothing name nothing either.
  let invisible := [" ", "　", "​", "‍", " ", "﻿", "­",
    "‎", ""]
  t "html a11y: a summary of characters drawn as nothing is unnamed"
    (invisible.all fun s => judged #[Html.text (s ++ s)] #[] == 1)
  t "html a11y: a summary's text or its own name names it"
    (judged #[Html.elem "strong" #[Html.text "Amber"]] #[] == 0
      && judged #[] #[("aria-label", "Amber")] == 0)
  t s!"html a11y: the corpus ships an image no browser decodes ({undecodableSeen})"
    (0 < undecodableSeen)
  let imageBytes ← IO.FS.readBinFile "testdata/corpus/figures/box.pdf"
  let selected : Image.Store := { entries := #[
    { src := "figures/box.pdf", info := (Image.decode imageBytes).toOption },
    { src := "figures/box.pdf", page := .number 2,
      info := (Image.decode imageBytes).toOption }] }
  let selectedDoc := (elabStr (dvDoc ""
    "\\begin{ifbackend}{pdf}\\includegraphics{figures/box.pdf}\\end{ifbackend}\
\\includegraphics[page=2,alt={Selected page}]{figures/box.pdf}")).1
  let (_, selectedBody, selectedDiags) := HtmlDoc.emitTree { imgs := selected } selectedDoc
  let selectedCount ← browserImageChecks ref "selected image requests"
    selected selectedBody selectedDiags
  t "html a11y: hidden requests sharing a filename do not enter the visible census"
    (selectedCount == 1)
  let placeholder := Html.elem "span" #[] #[("data-image-src", "figures/box.pdf"),
    ("data-image-index", "1"), ("role", "img"), ("aria-label", "Selected page")]
  let placeholderCount ← browserImageChecks ref "failed browser face"
    selected #[placeholder] selectedDiags
  t "html a11y: failure placeholders enter the same request census"
    (placeholderCount == 1)
  for tag in ["img", "span"] do
    for index in [none, some "99"] do
      let attrs := #[(if tag == "img" then "src" else "data-image-src", "figures/box.pdf")] ++
        (match index with
          | none => #[]
          | some value => #[("data-image-index", value)])
      let broken ← IO.mkRef ([] : List String)
      let _ ← browserImageChecks broken "broken request marker"
        selected #[Html.elem tag #[] attrs] #[]
      t s!"html a11y: the judge rejects {tag} with request index {repr index}"
        (!(← broken.get).isEmpty)
  -- `width` and `height` are CSS px, so a vector box is declared at 1pt = 4/3 px.
  t "html a11y: 56.693pt × 28.346pt reads 76 × 38 CSS px"
    (HtmlDoc.cssPxOfSp 3715432 == 76 && HtmlDoc.cssPxOfSp 1857684 == 38)
  match Image.decode (← IO.FS.readBinFile "testdata/corpus/figures/box.pdf") with
  | .error e => t s!"html a11y: the PDF-page probe decodes: {e}" false
  | .ok plan =>
    let box := elabStr (dvDoc "" "\\includegraphics[alt=a card]{box.pdf}")
    let boxStore : Image.Store := { entries := #[{ src := "box.pdf", info := some plan }] }
    let (_, pbody, pdiags) := HtmlDoc.emitTree { imgs := boxStore } box.1
    let dims := (elemAttrsList (· == "img") #[] pbody.toList).map fun (_, a) =>
      (HtmlDoc.attrOf? a "width", HtmlDoc.attrOf? a "height")
    t s!"html a11y: a PDF page's <img> declares its CSS-pixel box: {dims}"
      (dims == #[(some "340", some "204")])
    t "html a11y: a PDF page's <img> is named undecodable"
      (pdiags.any fun d => d.subject == some "img:0:box.pdf")
    -- W0605's remedy clears it: the web include gated to HTML and the PDF include to PDF.
    let webOnly := "\\begin{ifbackend}{html}\n\\includegraphics[alt={A card}]{rects.png}\n\
\\end{ifbackend}\n"
    let pdfInclude := "\\includegraphics[alt={A card}]{box.pdf}"
    let fires (body : String) : Bool :=
      let (_, _, ds) := HtmlDoc.emitTree { imgs := boxStore } (elabStr (dvDoc "" body)).1
      ds.any fun d => d.subject == some "img:0:box.pdf"
    t "html a11y: W0605 holds while the PDF include ships to both backends"
      (fires (webOnly ++ pdfInclude))
    t "html a11y: W0605's remedy clears it"
      (!fires (webOnly ++ "\\begin{ifbackend}{pdf}\n" ++ pdfInclude ++ "\n\\end{ifbackend}"))
    let pdoc := (elabStr (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\pattern (0,0) rectangle (2,1);\n\\end{tikzpicture}"))).1
    match (Ir.imageRefs pdoc).find? (·.startsWith Ir.picSrcPrefix) with
    | none => t "html a11y: the boundary probe states a picture request" false
    | some src =>
      let picStore : Image.Store :=
        { entries := #[{ src, href := "assets/pic.svg", info := some plan }] }
      let (_, qbody, qdiags) := HtmlDoc.emitTree { imgs := picStore } pdoc
      let qdims := (elemAttrsList (· == "img") #[] qbody.toList).map fun (_, a) =>
        (HtmlDoc.attrOf? a "src", HtmlDoc.attrOf? a "width", HtmlDoc.attrOf? a "height")
      t s!"html a11y: a boundary picture's SVG face declares its CSS-pixel box: {qdims}"
        (qdims == #[(some "assets/pic.svg", some "340", some "204")])
      t "html a11y: a boundary picture's SVG face is not named undecodable"
        (!qdiags.any fun d => (d.subject.getD "").startsWith "img:")
  -- A refused picture's placeholder is never decorative: the code naming the loss is its name.
  let refused := dvDoc "\\pictures{ tool = none }\n"
    "\\begin{tikzpicture}\n\\pattern (0,0) rectangle (2,1);\n\\end{tikzpicture}"
  let (rdoc, rds) := elabStr refused
  let (_, rbody, _) := HtmlDoc.emitTree {} rdoc
  t "html a11y: the refused picture fires W0362" (rds.any (·.code == "W0362"))
  t s!"html a11y: the refused placeholder is named by its loss: {svgLabels rbody}"
    (svgLabels rbody == #[some "W0362"])
  -- A boundary picture with no face is named by what it is; an authored caption wins.
  let shaded := "\\begin{tikzpicture}\n\\pattern (0,0) rectangle (2,1);\n\\end{tikzpicture}"
  let (tdoc, _) := elabStr (dvDoc "" shaded)
  let (_, tbody, _) := HtmlDoc.emitTree {} tdoc
  t s!"html a11y: a boundary picture with no face is named: {imgAlts tbody}"
    (imgAlts tbody == #[some "Figure"] && (a11yFactsOf tdoc tbody).imgsUnnamed == 0)
  let (_, tgbody, _) := HtmlDoc.emitTree {}
    (elabStr (dvDoc "\\usepackage[ngerman]{babel}\n" shaded)).1
  t s!"html a11y: …in German too: {imgAlts tgbody}" (imgAlts tgbody == #[some "Abbildung"])
  let (_, tcbody, _) := HtmlDoc.emitTree {} (elabStr (dvDoc ""
    ("\\begin{figure}\n" ++ shaded ++ "\n\\caption{A shaded card}\n\\end{figure}"))).1
  t s!"html a11y: …and its caption names it where it has one: {imgAlts tcbody}"
    (imgAlts tcbody == #[some "A shaded card"])
  -- role="img" makes an SVG's children presentational, so its labels reach the name only.
  let labelled := dvDoc "" ("\\begin{tikzpicture}\n\\node at (0,0) {left};\n" ++
    "\\node at (2,0) {right};\n\\end{tikzpicture}")
  let (_, lbody, _) := HtmlDoc.emitTree {} (elabStr labelled).1
  t s!"html a11y: a picture is named by its labels: {svgLabels lbody}"
    (svgLabels lbody == #[some "left, right"])
  -- A picture with no words is named by what it is, in the page's language.
  let bare := "\\begin{tikzpicture}\n\\draw (0,0) -- (2,0);\n\\end{tikzpicture}"
  let (_, bbody, _) := HtmlDoc.emitTree {} (elabStr (dvDoc "" bare)).1
  t s!"html a11y: a wordless picture is named by the locale's figure word: {svgLabels bbody}"
    (svgLabels bbody == #[some "Figure"])
  let (_, gbody, _) := HtmlDoc.emitTree {}
    (elabStr (dvDoc "\\usepackage[ngerman]{babel}\n" bare)).1
  t s!"html a11y: …in German too: {svgLabels gbody}"
    (svgLabels gbody == #[some "Abbildung"])
  -- A deck stage is a named, focusable region; the pinned script is the one script node.
  let deckSrc := dvDeck "" ("\\begin{frame}{A Titled Stage}\nBody.\n\\end{frame}\n" ++
    "\\begin{frame}\nOnly words here.\n\\end{frame}\n" ++
    "\\begin{frame}{Stepped}\n\\begin{itemize}\n\\item one\n\\pause\n\\item two\n" ++
    "\\end{itemize}\n\\end{frame}")
  let (_, dbody, _) := HtmlDoc.emitTree {} (elabStr deckSrc).1
  t s!"html a11y: deck stages are focusable and named: {stageMarks dbody}"
    (stageMarks dbody == #[(some "0", some "A Titled Stage"),
      (some "0", some "Only words here."), (some "0", some "Stepped")])
  let scripts := dbody.filterMap fun n => match n with
    | .script _ js => some js
    | _ => none
  t "html a11y: the deck's one script is still the pinned constant"
    (scripts == #[HtmlDoc.deckScript])
  -- An untitled stage is named by the words it shows, never by a hidden speaker note.
  let (_, nbody, _) := HtmlDoc.emitTree {}
    (elabStr (deck169Frame "Visible words.\n\\note{Hidden speaker words.}")).1
  t s!"html a11y: a speaker note stays out of the stage's name: {stageMarks nbody}"
    (stageMarks nbody == #[(some "0", some "Visible words.")])
  -- A themed section page is a stage too.
  let (_, sbody, _) := HtmlDoc.emitTree {} (elabStr (dvDeck "\\theme{moloch}\n"
    "\\section{An Invented Part}\n\\begin{frame}{F}\nx\n\\end{frame}")).1
  t s!"html a11y: a section page is a focusable, named stage: {stageMarks sbody}"
    (stageMarks sbody == #[(some "0", some "An Invented Part"), (some "0", some "F")])
  -- Two stages named alike are one landmark, so a repeated name takes its occurrence number.
  let (_, twbody, _) := HtmlDoc.emitTree {} (elabStr (dvDeck ""
    ("\\begin{frame}{Results}\nfirst\n\\end{frame}\n" ++
     "\\begin{frame}{Results}\nsecond\n\\end{frame}"))).1
  t s!"html a11y: two frames of one title are two stage names: {stageMarks twbody}"
    (stageMarks twbody == #[(some "0", some "Results"), (some "0", some "Results (2)")])
  let (_, numbody, _) := HtmlDoc.emitTree {} (elabStr (dvDeck ""
    ("\\begin{frame}{Results (2)}\nfirst\n\\end{frame}\n" ++
     "\\begin{frame}{Results}\nsecond\n\\end{frame}\n" ++
     "\\begin{frame}{Results}\nthird\n\\end{frame}"))).1
  t s!"html a11y: a stage name passes over a title spelling its numbered form: {stageMarks numbody}"
    (stageMarks numbody == #[(some "0", some "Results (2)"), (some "0", some "Results"),
      (some "0", some "Results (3)")])
  let (_, spbody, _) := HtmlDoc.emitTree {} (elabStr (dvDeck "\\theme{moloch}\n"
    "\\section{Results}\n\\begin{frame}{Results}\nx\n\\end{frame}")).1
  t s!"html a11y: a section page and a frame of one title are two names: {stageMarks spbody}"
    (stageMarks spbody == #[(some "0", some "Results"), (some "0", some "Results (2)")])
  -- Outside the deck a frame is a handout card, not a scroller: no tab stop.
  let (_, abody, _) := HtmlDoc.emitTree {} (elabStr (dvDoc ""
    "\\begin{frame}{A Card}\nx\n\\end{frame}")).1
  t s!"html a11y: a frame outside the deck is no tab stop: {stageMarks abody}"
    (stageMarks abody == #[(none, none)])
  -- A code block scrolls sideways (`overflow-x: auto`), so it is a stop too.
  let (_, cbody, _) := HtmlDoc.emitTree {} (elabStr (dvDoc ""
    "\\begin{verbatim}\ncode\n\\end{verbatim}")).1
  let pres := (elemAttrsList (· == "pre") #[] cbody.toList).map (HtmlDoc.attrOf? ·.2 "tabindex")
  t s!"html a11y: a code block is focusable: {pres}" (pres == #[some "0"])
  -- A poster's corner logo is decorative by role, so its empty alt is no missing alternative.
  let (pdoc2, _) := elabStr ("\\documentclass{poster}\n\\title{T}\n" ++
    "\\logoright{\\includegraphics{rects.png}}\n\\begin{document}\n" ++
    "\\begin{frame}\nx\n\\end{frame}\n\\end{document}")
  let (_, lgbody, _) := HtmlDoc.emitTree {} pdoc2
  let slots := ((elemAttrsList (· == "div") #[] lgbody.toList).filter fun (_, a) =>
      (HtmlDoc.classTokens a).contains "headline-logo").map fun (_, a) =>
    (HtmlDoc.attrOf? a "role", HtmlDoc.attrOf? a "aria-hidden")
  t s!"html a11y: a poster logo slot is declared decorative: {slots}"
    (slots == #[(some "presentation", some "true")])
  t "html a11y: …so the judge counts no unnamed image on it"
    ((a11yFactsOf pdoc2 lgbody).imgsUnnamed == 0)
  -- A linked logo is no decoration: the image's alternative names the link.
  let linkedLogo := "\\href{https://example.org}{\\includegraphics[alt={Example Org}]{rects.png}}"
  let (lpdoc, _) := elabStr ("\\documentclass{poster}\n\\title{T}\n\\logoright{" ++ linkedLogo ++
    "}\n\\begin{document}\n\\begin{frame}\nx\n\\end{frame}\n\\end{document}")
  let (_, lpbody, _) := HtmlDoc.emitTree {} lpdoc
  let lpf := a11yFactsOf lpdoc lpbody
  t s!"html a11y: a linked poster logo hides no tab stop ({lpf.hiddenTabStops})"
    (lpf.hiddenTabStops == 0)
  t s!"html a11y: …and its image's alternative names the link: {imgAlts lpbody}"
    (imgAlts lpbody == #[some "Example Org"])
  let (lddoc, _) := elabStr (deck169 ("\\logo{" ++ linkedLogo ++ "}")
    "\\begin{frame}{Probe}\nx\n\\end{frame}")
  let (_, ldbody, _) := HtmlDoc.emitTree {} lddoc
  let ldf := a11yFactsOf lddoc ldbody
  t s!"html a11y: a linked deck logo hides no tab stop ({ldf.hiddenTabStops})"
    (ldf.hiddenTabStops == 0)
  t s!"html a11y: …and its image's alternative names the link: {imgAlts ldbody}"
    (imgAlts ldbody == #[some "Example Org"])
  -- An unlinked deck logo stays decoration, as the poster's does.
  let (uddoc, _) := elabStr (deck169 "\\logo{\\includegraphics[alt={Example Org}]{rects.png}}"
    "\\begin{frame}{Probe}\nx\n\\end{frame}")
  let (_, udbody, _) := HtmlDoc.emitTree {} uddoc
  let strips := ((elemAttrsList (· == "div") #[] udbody.toList).filter fun (_, a) =>
      (HtmlDoc.classTokens a).contains "slide-logo").map fun (_, a) =>
    (HtmlDoc.attrOf? a "role", HtmlDoc.attrOf? a "aria-hidden")
  t s!"html a11y: an unlinked deck logo strip is declared decorative: {strips} {imgAlts udbody}"
    (strips == #[(some "presentation", some "true")] && imgAlts udbody == #[some ""])

/-- Every level-one heading a body hands assistive technology, outside `aria-hidden` and `hidden`
subtrees, as its attributes and text. -/
def handedH1s (body : Array Html.Node) : Array (Array (String × String) × String) :=
  let w : Html.Walk Unit (Array (Array (String × String) × String)) :=
    { inner := fun _ _ attrs =>
        if HtmlDoc.attrOf? attrs "aria-hidden" == some "true" ||
          (HtmlDoc.attrOf? attrs "hidden").isSome then none else some ()
      enter := fun _ acc tag attrs kids =>
        if tag == "h1" then acc.push (attrs, nodeTextList "" kids.toList) else acc }
  w.list () #[] body.toList

/-- A text with its whitespace runs read as single spaces. -/
def spacedText (s : String) : String :=
  " ".intercalate (((s.split Char.isWhitespace).toList.map (·.toString)).filter (!·.isEmpty))

/-- The text of every title a document's body sets. -/
def typesetTitles (doc : Ir.Doc) : Array String :=
  Ir.foldBlocks (fun acc b => match b with
    | .section .title _ _ xs => acc.push (spacedText (Ir.firstPageText xs))
    | _ => acc) (fun acc _ => acc) #[] (Ir.keepFor "html" doc.body)

/-- The body headings of rank one a document sets apart from its title. -/
def bodyH1Count (doc : Ir.Doc) : Nat :=
  ((Ir.headingLevels (Ir.keepFor "html" doc.body)).filter (· == .h1)).size

/-- The title a page's opening banner names out of sight: a `header` taken out of flow and clipped
to nothing, holding one level-one heading kept on one line. -/
def hiddenBanner? (body : Array Html.Node) : Option String :=
  let decls (attrs : Array (String × String)) := cssDecls ((HtmlDoc.attrOf? attrs "style").getD "")
  match (body[0]? : Option Html.Node) with
  | some (.elem "header" attrs kids) =>
    match kids.toList with
    | [Html.Node.elem "h1" hattrs hkids] =>
      if lastDecl (decls attrs) "position" == some "absolute" &&
          lastDecl (decls attrs) "clip-path" == some "inset(50%)" &&
          lastDecl (decls hattrs) "white-space" == some "nowrap"
      then some (nodeTextList "" hkids.toList) else none
    | _ => none
  | _ => none

/-- A titled page names itself by the title it sets, else its own rank-one heading, else its
declared title out of sight, a titled deck by exactly one h1 above its h2 frame titles; an untitled
page is given none. -/
def pageTitleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut titled := 0
  let mut unset := 0
  for n in goldenNames do
    let (doc, _, _, body, _) ← a11yCorpusPage n
    let h1s := (handedH1s body).map (spacedText ·.2)
    let typeset := typesetTitles doc
    let own := bodyH1Count doc
    let banner := hiddenBanner? body
    match doc.info.title.filter HtmlDoc.nonBlank with
    | some title =>
      titled := titled + 1
      let naming (s : String) : Bool := s == spacedText title || typeset.contains s
      let set := typeset.size + (if doc.headline.isSome then 1 else 0)
      if 0 < set then
        t s!"page title {n}: the title it sets is the page's one h1 naming it ({h1s})"
          (banner.isNone && h1s.size == set + own && (h1s.filter naming).size == set)
      else if 0 < own then
        t s!"page title {n}: a page with a level-one heading of its own is given no other ({h1s})"
          (banner.isNone && h1s.size == own)
      else
        unset := unset + 1
        t s!"page title {n}: a title the page does not set is its one h1, out of sight ({h1s})"
          (banner == some title && h1s == #[spacedText title])
      if doc.docClass.record.model == .frame && own == 0 then
        t s!"page title {n}: a titled deck hands exactly one h1, its title ({h1s})"
          (h1s.size == 1 && h1s.all naming)
    | none =>
      t s!"page title {n}: an untitled page is given no h1 ({h1s})" (banner.isNone && h1s.size == own)
  t s!"page title: the corpus ships titled pages ({titled})" (0 < titled)
  t s!"page title: the corpus ships titles its pages do not set ({unset})" (0 < unset)
  let bodyOf (doc : Ir.Doc) : Array Html.Node := (HtmlDoc.emitTree {} doc).2.1
  let page (src : String) : Array Html.Node := bodyOf (elabStr src).1
  let named (body : Array Html.Node) : Array String := (handedH1s body).map (·.2)
  let frame := "\\begin{frame}{A First Frame}\nx\n\\end{frame}"
  let titleDecl := "\\title{An Invented Deck}\n"
  let unsetDeck := page (dvDeck titleDecl frame)
  let setDeck := page (dvDeck titleDecl ("\\maketitle\n" ++ frame))
  t s!"page title: a titled deck with no title frame hands its title once, out of sight: \
{named unsetDeck}"
    (named unsetDeck == #["An Invented Deck"] && hiddenBanner? unsetDeck == some "An Invented Deck")
  t s!"page title: a deck's title frame carries its title as the one h1: {named setDeck}"
    (named setDeck == #["An Invented Deck"] && (hiddenBanner? setDeck).isNone)
  let tags (ns : Array Html.Node) : List String := (ns.filterMap fun (k : Html.Node) =>
    match k with
    | .elem tag _ _ => some tag
    | _ => none).toList
  for deckBody in [unsetDeck, setDeck] do
    let heads := (elemNodesList (· == "header") #[] (slideStages deckBody).toList).map
      fun h => match h with
        | .elem _ _ kids => tags kids
        | _ => []
    t s!"page title: a frame title stays an h2 beside the deck's title: {heads}"
      (heads == #[["h2"]])
  let unsetArticle := page (dvDoc "\\title{An Invented Study}\n" "\\section{Opening}\nx")
  t "page title: a titled article that sets no title hands it out of sight"
    (named unsetArticle == #["An Invented Study"] &&
      hiddenBanner? unsetArticle == some "An Invented Study")
  let setArticle := page (dvDoc "\\title{An Invented Study}\n" "\\maketitle\n\\section{Opening}\nx")
  t "page title: a titled article's set title is its one h1"
    (named setArticle == #["An Invented Study"] && (hiddenBanner? setArticle).isNone)
  let declared := page (dvDoc "\\pdfmeta{ title = \"An Invented Record\" }\n" "x")
  t "page title: a declared metadata title names the page"
    (named declared == #["An Invented Record"] && hiddenBanner? declared == some "An Invented Record")
  t "page title: an untitled article and an untitled deck are given no h1"
    ((named (page (dvDoc "" "\\section{Opening}\nx"))).isEmpty &&
      (named (page (dvDeck "" frame))).isEmpty)
  t "page title: a blank title declares none"
    ((named (page (dvDoc "\\title{}\n" "x"))).isEmpty &&
      (named (page (dvDoc "\\pdfmeta{ title = \" \" }\n" "x"))).isEmpty)
  let poster := page ("\\documentclass{poster}\n\\title{An Invented Band}\n\\begin{document}\n" ++
    "\\begin{frame}\nx\n\\end{frame}\n\\end{document}")
  t "page title: a poster's headline title is its one h1"
    (named poster == #["An Invented Band"] && (hiddenBanner? poster).isNone)
  let note := (elabMd "# An Invented Note\n\nx\n").1
  t "page title: an untitled markdown page keeps its own level-one heading alone"
    (named (bodyOf note) == #["An Invented Note"])
  let titledNote := bodyOf { note with info := { note.info with title := some "An Invented Study" } }
  t s!"page title: a titled page with a level-one heading of its own is given no second: \
{named titledNote}"
    (named titledNote == #["An Invented Note"] && (hiddenBanner? titledNote).isNone)

/-- The painted request census reads the scalar census's regions: the formulas the math face is
requested for ask exactly the scalars `Layout.docMathScalars` holds. -/
def mathCensusRegionChecks (ref : IO.Ref (List String)) (n : String) (doc : Ir.Doc) :
    IO Bool := do
  let requested := (Ir.mathRequests .face doc).foldl
    (fun acc r => Math.MList.scalarsList true acc r.body) #[]
  let census := Layout.docMathScalars doc
  check ref s!"math census {n}: the painted requests ask the scalar census's scalars"
    (requested.all census.contains && census.all requested.contains)
  let scalars := fun (acc : Array Char) (xs : Array Ir.Inline) =>
    Ir.foldInlines (fun acc x => match x with
      | .formula _ _ body => Math.MList.scalarsList true acc body
      | _ => acc) acc xs
  return !((docPictures doc).foldl (fun acc p => p.labelContents.foldl scalars acc) #[]).isEmpty

/-- No shipped page nests a MathML root or ships an error element, over every golden fixture's typed
tree. -/
def htmlMathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut roots := 0
  let mut carried := 0
  let mut labelled := 0
  for n in goldenNames do
    let (doc, _, _, body, _) ← a11yCorpusPage n
    if ← mathCensusRegionChecks ref n doc then labelled := labelled + 1
    let carriers := elemNodesList (· == "foreignObject") #[] body.toList
    roots := roots + (elemNodesList (· == "math") #[] body.toList).size
    carried := carried + (elemNodesList (· == "math") #[] carriers.toList).size
    t s!"html math {n}: no math element stands inside another"
      (MathMl.unnestedList body.toList)
    t s!"html math {n}: no merror ships \
({(elemNodesList (· == "merror") #[] body.toList).size})"
      (MathMl.tagFreeList (· == "merror") body.toList)
  t s!"html math: the corpus ships MathML ({roots} roots)" (roots > 0)
  t s!"html math: the corpus ships MathML inside a picture ({carried} carriers)" (carried > 0)
  t s!"math census: a fixture's picture labels ask for scalars ({labelled} fixtures)"
    (labelled > 0)
  let (_, _, _, shapes, _) ← a11yCorpusPage "diagram-shapes"
  t "html math: the corpus ships a math alphabet inside a picture"
    ((formulaElems (elemNodesList (· == "foreignObject") #[] shapes.toList)).any fun n =>
      match n with
      | .elem _ attrs _ => HtmlDoc.attrOf? attrs "data-tex" == some "\\mathrm {rd}"
      | _ => false)
  -- The predicates, once each way: a nested root and an error element are seen.
  let nestedRoot := Html.elem "math" #[Html.elem "mrow" #[Html.elem "math" #[]]]
  let framed := Html.elem "math" #[Html.elem "merror" #[Html.elem "mi" #[Html.text "x"]]]
  t "html math: the judge sees a root inside a root"
    (!MathMl.unnested nestedRoot && MathMl.tagFree (· == "merror") nestedRoot)
  t "html math: the judge sees an error element"
    (!MathMl.tagFree (· == "merror") framed && MathMl.unnested framed)
