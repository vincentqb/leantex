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
  for n in goldenNames do
    let (doc, _, body, _) ← a11yCorpusPage n
    let f := a11yFactsOf doc body
    svgsSeen := svgsSeen + f.svgs
    scrollsSeen := scrollsSeen + f.scrolls
    t s!"html a11y {n}: every svg is named ({f.svgsUnnamed} of {f.svgs} unnamed)"
      (f.svgsUnnamed == 0)
    t s!"html a11y {n}: every scroll container is reachable \
({f.scrollsUnreachable} of {f.scrolls} not)" (f.scrollsUnreachable == 0)
  t s!"html a11y: the corpus ships inline pictures ({svgsSeen})" (0 < svgsSeen)
  t s!"html a11y: the corpus ships scroll containers ({scrollsSeen})" (0 < scrollsSeen)
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
