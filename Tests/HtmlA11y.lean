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
`tests/corpus` (`corpusStore`). No boundary tool runs here, so a boundary
picture is its placeholder — what a host with no tool ships. -/
def a11yCorpusPage (n : String) :
    IO (Ir.Doc × Array Html.Node × Array Html.Node × Array Diag) := do
  let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
  let (doc, _) ← elabFixture n src
  let store ← corpusStore doc
  let (head, body, diags) := HtmlDoc.emitTree { css := a11yCssOf doc, imgs := store } doc
  return (doc, head, body, diags)

/-- The judge's reading of one page: the stylesheet mode and the page model
decide which elements are scroll containers. -/
def a11yFactsOf (doc : Ir.Doc) (body : Array Html.Node) : HtmlDoc.A11yFacts :=
  HtmlDoc.a11yFacts (a11yCssOf doc == .own) (doc.docClass.record.model == .frame) body

mutual

/-- Every element of a tree whose tag `want` accepts, with its attributes,
in document order. -/
def elemAttrsOne (want : String → Bool) (acc : Array (String × Array (String × String))) :
    Html.Node → Array (String × Array (String × String))
  | .elem tag attrs kids =>
    elemAttrsList want (if want tag then acc.push (tag, attrs) else acc) kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def elemAttrsList (want : String → Bool) (acc : Array (String × Array (String × String))) :
    List Html.Node → Array (String × Array (String × String))
  | [] => acc
  | k :: rest => elemAttrsList want (elemAttrsOne want acc k) rest

end

/-- The `aria-label` of every `<svg>` a body carries. -/
def svgLabels (body : Array Html.Node) : Array (Option String) :=
  (elemAttrsList (· == "svg") #[] body.toList).map (HtmlDoc.attrOf? ·.2 "aria-label")

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
    let (doc, _, body, diags) ← a11yCorpusPage n
    let f := a11yFactsOf doc body
    svgsSeen := svgsSeen + f.svgs
    scrollsSeen := scrollsSeen + f.scrolls
    t s!"html a11y {n}: every svg is named ({f.svgsUnnamed} of {f.svgs} unnamed)"
      (f.svgsUnnamed == 0)
    t s!"html a11y {n}: every scroll container is reachable \
({f.scrollsUnreachable} of {f.scrolls} not)" (f.scrollsUnreachable == 0)
    -- W3: every <img src> the page emits is a format a browser decodes, or
    -- a diagnostic names the file (subject `img:<src>`). The format is read
    -- off the file's own bytes, never off the backend's classification;
    -- an image that did not load, or a boundary picture, was named where it
    -- failed, by the fulfilment's own subject-keyed diagnostic.
    let store ← corpusStore doc
    let emitted := a11yImgSrcs body
    for en in store.entries do
      if en.info.isNone || en.src.startsWith Ir.picSrcPrefix then continue
      let href := HtmlDoc.imageHref "assets" store en.src
      unless emitted.contains href do continue
      let bytes ← IO.FS.readBinFile s!"tests/corpus/{HtmlDoc.resolvedSrc en}"
      if (sniffBrowserImage bytes).isNone then
        undecodableSeen := undecodableSeen + 1
        t s!"html a11y {n}: '{href}' no browser decodes, and a diagnostic names it"
          (diags.any fun d => d.subject == some s!"img:{href}")
    for d in diags do
      if let some s := d.subject then
        if s.startsWith "img:" then
          let href := (s.drop 4).toString
          let named := store.entries.find? fun en => HtmlDoc.imageHref "assets" store en.src == href
          let decodes ← match named with
            | some en => do
              let bytes ← IO.FS.readBinFile s!"tests/corpus/{HtmlDoc.resolvedSrc en}"
              pure (sniffBrowserImage bytes).isSome
            | none => pure false
          t s!"html a11y {n}: '{href}' is named undecodable only when it is" (!decodes)
  t s!"html a11y: the corpus ships inline pictures ({svgsSeen})" (0 < svgsSeen)
  t s!"html a11y: the corpus ships scroll containers ({scrollsSeen})" (0 < scrollsSeen)
  t s!"html a11y: the corpus ships an image no browser decodes ({undecodableSeen})"
    (0 < undecodableSeen)
  -- W3's size half: `width`/`height` are CSS px, so a vector page's box is
  -- declared on the CSS ruler (1pt = 4/3 px), not as its point count. The
  -- boundary picture's SVG face (pdftocairo, `width="56.693pt"`) is what a
  -- browser draws 76 × 38; the page used to declare 56 × 28.
  t "html a11y: 56.693pt × 28.346pt reads 76 × 38 CSS px"
    (HtmlDoc.cssPxOfSp 3715432 == 76 && HtmlDoc.cssPxOfSp 1857684 == 38)
  match Image.decode (← IO.FS.readBinFile "tests/corpus/figures/box.pdf") with
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
      (pdiags.any fun d => d.subject == some "img:box.pdf")
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
