import Tests.Backends

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! What assistive technology is handed, asserted over the pages the corpus
ships: the typed tree `HtmlDoc.emitTree` produces for every golden fixture,
judged by `HtmlDoc.a11yFacts` — the same judge the `htmla11y` scoreboard
tier reads, so the suite and the tier cannot disagree about what counts. -/

/-- The stylesheet mode a document's page is emitted under: its own
`\output{ css = … }` declaration, read as the driver reads it. -/
def a11yCssOf (doc : Ir.Doc) : HtmlDoc.CssMode :=
  match cssFor doc.output.css with
  | .own => .own
  | .bulma => .bulma
  | .none => .none

/-- One corpus fixture's page as its typed tree, built in-process the way
the driver builds it: the document's own stylesheet mode and its images from
`testdata/corpus` (`corpusStore`). No boundary tool runs here, so a boundary
picture is its placeholder — what a host with no tool ships. -/
def a11yCorpusPage (n : String) :
    IO (Ir.Doc × Image.Store × Array Html.Node × Array Html.Node × Array Diag) := do
  let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
  let (doc, _) ← elabFixture n src
  let store ← corpusStore doc
  let (head, body, diags) := HtmlDoc.emitTree { css := a11yCssOf doc, imgs := store } doc
  return (doc, store, head, body, diags)

/-- The judge's reading of one page: the stylesheet mode and the page model
decide which elements are scroll containers. -/
def a11yFactsOf (doc : Ir.Doc) (body : Array Html.Node) : HtmlDoc.A11yFacts :=
  HtmlDoc.a11yFacts (a11yCssOf doc == .own) (doc.docClass.record.model == .frame) body

/-- A page's accessibility deficits, one count per check — what the
`htmla11y` scoreboard tier ratchets, per fixture, as headroom:

* `contrast` — the stylesheet's pairings the page fails, over both colour
  schemes (`HtmlDoc.schemeFailures`);
* `h1` — 1 unless the page carries exactly one `<h1>`;
* `hidden-focus` — tab stops under `aria-hidden`, a keyboard stop assistive
  technology cannot see;
* `img` — `<img>` with no text alternative and no declared decorative role;
* `scroll` — declared scroll containers a keyboard cannot reach;
* `svg` — `<svg>` with no accessible name.

Sorted by check name, so a tier's rows come out in the order it writes them. -/
def a11yDeficits (doc : Ir.Doc) (imgs : Image.Store) (body : Array Html.Node) :
    List (String × Nat) :=
  let f := a11yFactsOf doc body
  [("contrast", (HtmlDoc.schemeFailures (a11yCssOf doc == .own) imgs doc).length),
   ("h1", if f.h1s == 1 then 0 else 1),
   ("hidden-focus", f.hiddenTabStops),
   ("img", f.imgsUnnamed),
   ("scroll", f.scrollsUnreachable),
   ("svg", f.svgsUnnamed)]

/-- Every golden fixture's deficits, built in-process from committed inputs
only: no browser, no network, no tool. -/
def a11yCorpus : IO (Array (String × List (String × Nat))) := do
  let mut out := #[]
  for n in goldenNames do
    let (doc, store, _, body, _) ← a11yCorpusPage n
    out := out.push (n, a11yDeficits doc store body)
  return out

/-- The `aria-label` of every `<svg>` a body carries. -/
def svgLabels (body : Array Html.Node) : Array (Option String) :=
  (elemAttrsList (· == "svg") #[] body.toList).map (HtmlDoc.attrOf? ·.2 "aria-label")

/-- The `alt` of every `<img>` a body carries. -/
def imgAlts (body : Array Html.Node) : Array (Option String) :=
  (elemAttrsList (· == "img") #[] body.toList).map (HtmlDoc.attrOf? ·.2 "alt")

/-- The format a file's first bytes declare, for the image formats a browser
decodes in an `<img>` (WHATWG MIME Sniffing §6.1, the image signatures):
PNG, JPEG, GIF, WebP. `none` for anything else — a PDF page included. Read
off the bytes, so the judge below does not share the backend's own
classification. -/
def sniffBrowserImage (b : ByteArray) : Option String :=
  let at' (i : Nat) (xs : List UInt8) : Bool :=
    xs.length + i ≤ b.size && (List.range xs.length).all fun k => b[i + k]! == xs[k]!
  if at' 0 [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A] then some "png"
  else if at' 0 [0xFF, 0xD8, 0xFF] then some "jpeg"
  else if at' 0 [0x47, 0x49, 0x46, 0x38] then some "gif"
  else if at' 0 [0x52, 0x49, 0x46, 0x46] && at' 8 [0x57, 0x45, 0x42, 0x50] then some "webp"
  else none

/-- Every `<img src>` a body emits, hidden or not: a browser fetches and
decodes an image under `aria-hidden` all the same. -/
def a11yImgSrcs (body : Array Html.Node) : Array String :=
  (elemAttrsList (· == "img") #[] body.toList).filterMap (HtmlDoc.attrOf? ·.2 "src")

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

/-- The HTML accessibility contract over the shipped corpus and the probes
that break each half once. -/
def htmlA11yChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- W4: every inline <svg> on every shipped page carries an accessible
  -- name. S1: every scroll container the page's own stylesheet declares —
  -- a deck stage, a code block — is reachable from the keyboard.
  -- Non-vacuous only if the corpus ships pictures and scrollers at all.
  let mut svgsSeen := 0
  let mut scrollsSeen := 0
  let mut undecodableSeen := 0
  for n in goldenNames do
    let (doc, store, _, body, diags) ← a11yCorpusPage n
    let f := a11yFactsOf doc body
    svgsSeen := svgsSeen + f.svgs
    scrollsSeen := scrollsSeen + f.scrolls
    t s!"html a11y {n}: every svg is named ({f.svgsUnnamed} of {f.svgs} unnamed)"
      (f.svgsUnnamed == 0)
    t s!"html a11y {n}: every scroll container is reachable \
({f.scrollsUnreachable} of {f.scrolls} not)" (f.scrollsUnreachable == 0)
    -- No tab stop stands under `aria-hidden`: a regression floor over the
    -- shipped pages — the corpus holds no linked logo, so the probes below
    -- are what fire it.
    t s!"html a11y {n}: no tab stop is hidden from assistive technology \
({f.hiddenTabStops})" (f.hiddenTabStops == 0)
    -- No two stages share a name (a floor: the corpus repeats no title).
    let names := (stageMarks body).filterMap (·.2)
    t s!"html a11y {n}: no two stages share a name"
      (names.all fun nm => (names.filter (· == nm)).size == 1)
    -- W3: every <img src> the page emits is a format a browser decodes, or
    -- a diagnostic names the request (subject `img:<index>:<src>`). The format is read
    -- off the file's own bytes, never off the backend's classification;
    -- an image that did not load, or a boundary picture, was named where it
    -- failed, by the fulfilment's own subject-keyed diagnostic.
    undecodableSeen := undecodableSeen + (← browserImageChecks ref n store body diags)
  t s!"html a11y: the corpus ships inline pictures ({svgsSeen})" (0 < svgsSeen)
  t s!"html a11y: the corpus ships scroll containers ({scrollsSeen})" (0 < scrollsSeen)
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
  -- W3's size half: `width`/`height` are CSS px, so a vector page's box is
  -- declared on the CSS ruler (1pt = 4/3 px), not as its point count. The
  -- boundary picture's SVG face (pdftocairo, `width="56.693pt"`) is what a
  -- browser draws 76 × 38; the page used to declare 56 × 28.
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
    -- W0605's remedy, followed, clears it: the web page's include gated to
    -- HTML and the PDF include to PDF. Keeping the PDF include for both
    -- backends, as a reader of "keep the PDF for print" might, does not.
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
      "\\shade (0,0) rectangle (2,1);\n\\end{tikzpicture}"))).1
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
  -- A refused picture's placeholder is never decorative: its name is the
  -- code that names the loss, the text the box itself shows.
  let refused := dvDoc "\\pictures{ tool = none }\n"
    "\\begin{tikzpicture}\n\\shade (0,0) rectangle (2,1);\n\\end{tikzpicture}"
  let (rdoc, rds) := elabStr refused
  let (_, rbody, _) := HtmlDoc.emitTree {} rdoc
  t "html a11y: the refused picture fires W0362" (rds.any (·.code == "W0362"))
  t s!"html a11y: the refused placeholder is named by its loss: {svgLabels rbody}"
    (svgLabels rbody == #[some "W0362"])
  -- A boundary picture with no face in the store — a host with no tool, or
  -- a tool that refused — ships its request key as the `src`, which draws
  -- nothing: never decorative, so it is named by what it is, in the page's
  -- language, and a caption the author wrote still wins.
  let shaded := "\\begin{tikzpicture}\n\\shade (0,0) rectangle (2,1);\n\\end{tikzpicture}"
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
  -- A picture's labels are its name: role="img" makes an SVG's children
  -- presentational (WAI-ARIA 1.2 §5.3), so the words a sighted reader sees
  -- reach assistive technology only through the name.
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
  -- S1: a deck stage is a named, focusable region — named by its title,
  -- or by its own words when it has none — and a stepped frame's stage
  -- keeps both inside its track. The keys the constant script binds are
  -- untouched: the script is still the pinned literal, and it is the one
  -- script node the page carries.
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
  -- An untitled stage is named by the words it shows, never by what it
  -- hides: a speaker note is a hidden aside, not part of the slide.
  let (_, nbody, _) := HtmlDoc.emitTree {}
    (elabStr (deck169Frame "Visible words.\n\\note{Hidden speaker words.}")).1
  t s!"html a11y: a speaker note stays out of the stage's name: {stageMarks nbody}"
    (stageMarks nbody == #[(some "0", some "Visible words.")])
  -- A themed section page is a stage too.
  let (_, sbody, _) := HtmlDoc.emitTree {} (elabStr (dvDeck "\\theme{moloch}\n"
    "\\section{An Invented Part}\n\\begin{frame}{F}\nx\n\\end{frame}")).1
  t s!"html a11y: a section page is a focusable, named stage: {stageMarks sbody}"
    (stageMarks sbody == #[(some "0", some "An Invented Part"), (some "0", some "F")])
  -- Two stages named alike are one landmark to a reader moving by landmark
  -- (axe `landmark-unique`): a repeated name takes its occurrence number,
  -- as the repeated title's anchor does. One construct per probe: two
  -- frames of one title, then a section page and a frame of one title.
  let (_, twbody, _) := HtmlDoc.emitTree {} (elabStr (dvDeck ""
    ("\\begin{frame}{Results}\nfirst\n\\end{frame}\n" ++
     "\\begin{frame}{Results}\nsecond\n\\end{frame}"))).1
  t s!"html a11y: two frames of one title are two stage names: {stageMarks twbody}"
    (stageMarks twbody == #[(some "0", some "Results"), (some "0", some "Results (2)")])
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
  -- A poster's corner logo is decorative furniture by role
  -- (`Ir.logoImageSrcs`), declared so on the page as the deck's logo strip
  -- is: assistive technology skips the slot, so its empty alt is not a
  -- missing alternative.
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
  -- A logo that is a link is no decoration: the keyboard lands on the link,
  -- so its box never leaves the accessibility tree over it, and the image's
  -- own alternative names the link. One construct per probe: the poster's
  -- corner slot, then the deck's logo strip.
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

/-- **No shipped page nests a MathML root or ships an error element.** Over
every golden fixture's typed tree — the pages the corpus ships — no `math`
element stands inside another (`HtmlDoc.mathFacts`, the judge
`MathMl.unnested` names) and no `merror` appears: the driver resolves every
formula a page paints, picture labels included, and a label's carrier is its
formulas' one root. No path ships an `merror` a diagnostic names — an
alphabet the face lacks is named (N0018) and resolves to its source glyphs —
so the count owed is zero, not a count of named ones. Non-vacuous only while
the corpus ships MathML, MathML inside a picture, and an alphabet there. -/
def htmlMathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut roots := 0
  let mut carried := 0
  for n in goldenNames do
    let (_, _, _, body, _) ← a11yCorpusPage n
    let f := HtmlDoc.mathFacts body
    roots := roots + f.roots
    carried := carried + (HtmlDoc.mathFacts
      (elemNodesList (· == "foreignObject") #[] body.toList)).roots
    t s!"html math {n}: no math element stands inside another ({f.nested})"
      (f.nested == 0 && body.all MathMl.unnested)
    t s!"html math {n}: no merror ships ({f.errors})" (f.errors == 0)
  t s!"html math: the corpus ships MathML ({roots} roots)" (roots > 0)
  t s!"html math: the corpus ships MathML inside a picture ({carried} carriers)" (carried > 0)
  let (_, _, _, scm, _) ← a11yCorpusPage "diagram-scm"
  t "html math: the corpus ships a math alphabet inside a picture"
    ((elemNodesList (· == "foreignObject") #[] scm.toList).any fun fo =>
      (elemAttrsOne (fun _ => true) #[] fo).any fun (_, attrs) =>
        HtmlDoc.attrOf? attrs "data-tex" == some "\\mathrm {rd}")
  -- The judge, once each way: a nested root and an error element are seen.
  let nestedRoot := Html.elem "math" #[Html.elem "mrow" #[Html.elem "math" #[]]]
  let framed := Html.elem "math" #[Html.elem "merror" #[Html.elem "mi" #[Html.text "x"]]]
  t "html math: the judge sees a root inside a root"
    ((HtmlDoc.mathFacts #[nestedRoot]).nested == 1 && !MathMl.unnested nestedRoot)
  t "html math: the judge sees an error element"
    ((HtmlDoc.mathFacts #[framed]).errors == 1 && MathMl.unnested framed)
