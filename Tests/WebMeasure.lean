module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.WebMeasure

/-- An invented markdown guide: a title, three sections, prose, a long code line and a table. -/
private def guide : String :=
  "# Field Guide\n\nAn opening line.\n\n## Tallies\n\nCounting swifts at dawn.\n\n" ++
  "```python\ndef tally(day):\n    return sum(e.count for e in day.entries if e.species == \"swift\" and e.verified and e.region == \"north\")\n```\n\n" ++
  "## Routes\n\n| Day | Count |\n|---|---|\n| Monday | 4 |\n\n### Marsh\n\nA marsh line.\n\n## Notes\n\nA closing line.\n"

/-- The elements of a body whose tag is `tag`, with their attributes. -/
private def elems (tag : String) (body : Array Html.Node) : Array (Array (String × String)) :=
  (elemAttrsList (· == tag) #[] body.toList).map (·.2)

private def classOf (attrs : Array (String × String)) : List String :=
  HtmlDoc.classTokens attrs

/-- A flow's page keeps prose at the measure, lets what does not reflow take its natural width past
it on screen alone, and carries its outline in the margin, a named, reachable navigation. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabMd guide
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := HtmlDoc.baseCss {} doc
  t "web measure: the faces the page sets stay decidable from its sheet"
    (HtmlFaces.requests head body #[]).isSome
  let navs := (elems "nav" body).filter fun a => (classOf a).contains HtmlDoc.outlineClass
  t s!"web measure: a flow of three sections carries one outline ({navs.size})" (navs.size == 1)
  t "web measure: the outline is named and a tab stop"
    (navs.all fun a => HtmlDoc.attrOf? a "aria-label" == some "Contents" &&
      HtmlDoc.attrOf? a "tabindex" == some "0")
  let ids := (elemAttrsList (fun _ => true) #[] body.toList).filterMap fun (_, a) => HtmlDoc.attrOf? a "id"
  let navNode := (elemNodesList (· == "nav") #[] body.toList).toList.head?
  let hrefs := match navNode with
    | some n => attrValuesOf (· == "a") "href" n
    | none => #[]
  t s!"web measure: the outline links each section's anchor ({hrefs})"
    (hrefs.size == 3 && hrefs.all fun h => ids.contains (h.drop 1).toString)
  let facts := HtmlDoc.a11yFacts true false body
  t s!"web measure: every scroll box, the outline's included, is reachable ({facts.scrolls}, {facts.scrollsUnreachable})"
    (facts.scrolls == 2 && facts.scrollsUnreachable == 0)
  t "web measure: the outline's facts name it" (facts.navNames.contains "Contents")
  let tables := elems "table" body
  t "web measure: a markdown table's natural columns mark it natural"
    (tables.size == 1 && tables.all fun a => (classOf a).contains "bt-natural")
  t "web measure: a markdown page's measure is book-theme's sixty digits and their insets"
    (hasStr css "--measure: calc(60ch + 7.25rem);" && HtmlDoc.measureMilli doc 500 == 60 * 500 + 7250)
  let blocks := cssBlocksIn css
  let screen (ctx : List String) : Bool := ctx.any (·.startsWith "@media screen")
  let wide := blocks.filter fun (_, _, d) =>
    hasStr d "inline-size: max-content" || hasStr d "var(--wide-room))"
  t s!"web measure: what does not reflow takes its natural width past the text, on screen alone ({wide.size})"
    (wide.size == 2 && wide.all fun (c, sel, _) => screen c && hasStr sel HtmlDoc.naturalBlocks)
  let rooms := blocks.filter fun (_, _, d) => hasStr d "--wide-room:"
  t "web measure: the room is zero but on screen, and every box but the flow's own ends it"
    (rooms.any (fun (c, sel, d) => c.isEmpty && sel == "main" && d == "--wide-room: 0px;") &&
      rooms.any (fun (c, sel, d) => c.isEmpty && sel == s!":where(main) :not({HtmlDoc.roomKeepers})" &&
        d == "--wide-room: 0px;") &&
      rooms.all (fun (c, sel, d) => d == "--wide-room: 0px;" || (screen c && sel == "main")) &&
      hasStr css "@property --wide-room { syntax: \"<length>\"; inherits: true; initial-value: 0px; }")
  t "web measure: the room reads the viewport and the reader's size alone, up to the free column"
    (rooms.any fun (_, _, d) => d == "--wide-room: clamp(0px, (100vw - 2 * 1.25rem - var(--measure)) / 2, 19rem);")
  let ch := HtmlDoc.chMilli none
  let bp := HtmlDoc.outlineBreakMilli doc ch
  let grid := ["@media screen and (min-width: 64.65em)"]
  t s!"web measure: the book layout's grid stands only where the viewport holds its sidebar ({bp})"
    (ch == 640 && bp == 2 * 1250 + 15000 + 1500 + 60 * 640 + 7250 &&
      blocks.any (fun (c, sel, d) => c.isEmpty && sel == "nav.outline" && d.startsWith "display: none;") &&
      blocks.any (fun (c, sel, d) => c == grid && sel == "body" && hasStr d "display: grid;" &&
        hasStr d "[lead-start] 15rem [lead-end] 1.5rem [main-start] min(var(--measure), 100% - 16.5rem) [main-end]" &&
        hasStr d "padding-block-end: 0;") &&
      blocks.any (fun (c, sel, d) => c == grid && sel == "nav.outline" &&
        hasStr d "grid-column: lead;" && hasStr d "position: sticky;" && hasStr d "overflow-y: auto;") &&
      blocks.any fun (c, sel, d) => c == grid && sel == "main" && hasStr d "grid-column: main;" &&
        hasStr d "margin: 0 0 4.350rem;")
  let (art, artDs) := elabStr ("\\documentclass{article}\\page{ web = article }\\begin{document}" ++
    "\\section{A}x\\section{B}y\\end{document}")
  let artCss := HtmlDoc.baseCss {} art
  let artGrid := ["@media screen and (min-width: 72.08em)"]
  t "web measure: a declared article layout takes article-theme's measure and margin column"
    (artDs.isEmpty && hasStr artCss "--measure: calc(72ch + 7.25rem);" &&
      HtmlDoc.outlineBreakMilli art ch == 2 * 1250 + 3000 + 3250 + 72 * 640 + 7250 + 10000 &&
      (cssBlocksIn artCss).any (fun (c, sel, d) => c == artGrid && sel == "nav.outline" &&
        hasStr d "grid-column: margin;") &&
      (cssBlocksIn artCss).any fun (c, sel, d) => c == artGrid && sel == "main" &&
        hasStr d "--wide-room: 0px;")
  let (_, badDs) := elabStr ("\\documentclass{article}\\page{ web = magazine }\\begin{document}" ++
    "x\\end{document}")
  t "web measure: a layout no theme names is named" (badDs.any (·.kind == .E0323))
  let (mdArt, mdArtDs) := elabMd ("---\nweb: article\n---\n\n" ++ guide)
  let mdArtCss := HtmlDoc.baseCss {} mdArt
  t "web measure: a markdown document's metadata declares the article layout as the TeX page's does"
    (mdArtDs.isEmpty && mdArt.page.web == some .article && hasStr mdArtCss "--measure: calc(72ch + 7.25rem);" &&
      (cssBlocksIn mdArtCss).any fun (c, sel, d) => c == artGrid && sel == "nav.outline" &&
        hasStr d "grid-column: margin;")
  let (mdBook, mdBookDs) := elabMd ("---\nweb: book\n---\n\n" ++ guide)
  t "web measure: a markdown document declaring the book layout ships the page declaring none"
    (mdBookDs.isEmpty && mdBook.page.web == some .book &&
      (HtmlDoc.emit {} mdBook).1 == (HtmlDoc.emit {} doc).1)
  let (mdBad, mdBadDs) := elabMd ("---\nweb: magazine\n---\n\n" ++ guide)
  t s!"web measure: a markdown layout no theme names is named as the TeX one is ({mdBadDs.map (·.message)})"
    (mdBad.page.web.isNone && mdBadDs.size == 1 && mdBadDs.all fun d => d.kind == .E0323 &&
      d.message == "invalid value 'magazine' for key web" && (d.span.map (·.pos.line)) == some 2 &&
      (d.help.getD "") == "write 'web: book' or 'web: article'")
  let (_, mdListDs) := elabMd ("---\nweb: [book, article]\n---\n\n" ++ guide)
  t "web measure: a markdown layout that is no single name is named unread"
    (mdListDs.any fun d => d.kind == .W0307 && hasStr d.message "'web'")
  let (_, mdEmptyDs) := elabMd ("---\nweb:\n---\n\n" ++ guide)
  t "web measure: an empty markdown layout is named unread, its help naming the layouts"
    (mdEmptyDs.size == 1 && mdEmptyDs.all fun d => d.kind == .W0307 && hasStr d.message "'web'" &&
      (d.help.getD "") == "write 'web: book' or 'web: article'")
  let (mdEnd, mdEndDs) := elabMd (guide ++ "\n---\nweb: article\n---\n")
  t "web measure: a closing metadata block declares the layout as an opening one does"
    (mdEndDs.isEmpty && mdEnd.page.web == some .article)
  let (raws, rds) := Surface.read .markdown "mid.md" ("---\nweb: article\n---\n\n" ++ guide)
  let k := ((raws.extract 2 raws.size).findIdx? (· matches .par _)).getD 0 + 3
  let mid := (raws.extract 2 k) ++ (raws.extract 0 2) ++ (raws.extract k raws.size)
  let (midDoc, midDs) := Elab.runKept "mid.md" mid rds
  let (headDoc, _) := Elab.runKept "mid.md" raws rds
  t "web measure: the elaborator reads the layout's control wherever it stands at the top level"
    (raws[0]? matches some (Parse.Raw.ctrl _ _) && 3 < k && k < raws.size && midDs.isEmpty &&
      midDoc.page.web == some .article && (HtmlDoc.emit {} midDoc).1 == (HtmlDoc.emit {} headDoc).1)
  t "web measure: TeX names a layout no theme names in the markdown words, its help in its own spelling"
    (badDs.size == 1 && badDs.all fun d => d.kind == .E0323 &&
      d.message == "invalid value 'magazine' for key web" &&
      (d.help.getD "") == "write '\\page{ web = book }' or '\\page{ web = article }'")
  let (inc, incDs) := includedDoc "host.tex" (neutralHost "a")
    [("a", "a.md", "---\nweb: article\n---\n\nAn included line.\n")]
  t "web measure: an included markdown file's layout is named and the page keeps the host's"
    (inc.page.web.isNone && incDs.any fun d => d.kind == .W0307 && hasStr d.message "'web'" &&
      hasStr d.message "including document's layout")
  let (_, dimDs) := elabStr ("\\documentclass{article}\\page{ web = 3pt }\\begin{document}" ++
    "x\\end{document}")
  t "web measure: a value of the wrong type names the layouts"
    (dimDs.any fun d => d.kind == .E0323 && hasStr d.message "'book' or 'article'")
  let (_, deckDs) := elabStr ("\\documentclass{beamer}\\page{ web = book }\\begin{document}" ++
    "\\begin{frame}{One}x\\end{frame}\\end{document}")
  t "web measure: a layout declared on a page no flow sets is named"
    (deckDs.any fun d => d.kind == .W0104 && hasStr d.message "'web'")
  let topTags := body.filterMap fun n => match n with
    | .elem tag attrs _ => some (tag, (classOf attrs).contains HtmlDoc.outlineClass)
    | _ => none
  t s!"web measure: the outline follows the text, so the text comes first in the tab order ({topTags})"
    (topTags.map (·.1) == #["main", "nav"] && topTags.back?.any (·.2))
  let ((one : Ir.Doc), _) := elabMd "# One\n\n## Only\n\nA line.\n"
  let (_, oneBody, _) := HtmlDoc.emitTree {} one
  t "web measure: a page of one section carries no outline"
    ((elems "nav" oneBody).isEmpty && !hasStr (HtmlDoc.baseCss {} one) "nav.outline")
  let (deck, _) := elabStr ("\\documentclass{beamer}\\begin{document}\\section{A}\\begin{frame}{One}x\\end{frame}" ++
    "\\section{B}\\begin{frame}{Two}y\\end{frame}\\end{document}")
  t "web measure: a deck's stages take no flow geometry"
    (!hasStr (HtmlDoc.baseCss {} deck) "--wide-room" && (HtmlDoc.outlineOf deck).isEmpty)
  let (tex, _) := elabStr ("\\documentclass{article}\\page{ textwidth = 300pt }\\begin{document}" ++
    "\\section{A}x\\section{B}y\\begin{tabular}{p{3cm}l}a & b\\end{tabular}\\end{document}")
  let (_, texBody, _) := HtmlDoc.emitTree {} tex
  t "web measure: a declared text width is the measure"
    (hasStr (HtmlDoc.baseCss {} tex) "--measure: 30rem;")
  t "web measure: a table of a declared column width keeps to the measure"
    ((elems "table" texBody).all fun a => !(classOf a).contains "bt-natural")
  let (cv, _) := elabStr ("\\documentclass{resume}\\begin{document}\\section{Work}x\\section{Study}y" ++
    "\\end{document}")
  t "web measure: a page its class binds to one page carries no outline" (HtmlDoc.outlineOf cv).isEmpty
  let (navved, _) := elabStr ("\\documentclass{article}\\begin{document}\\begin{nav}\\href{#a}{A}\\end{nav}" ++
    "\\section{A}x\\section{B}y\\end{document}")
  t "web measure: a page declaring its own navigation carries no outline"
    (HtmlDoc.outlineOf navved).isEmpty
  let (toc, _) := elabStr ("\\documentclass{article}\\begin{document}\\tableofcontents" ++
    "\\section{A}x\\section{B}y\\end{document}")
  t "web measure: a page declaring its own contents carries no outline beside it"
    (HtmlDoc.outlineOf toc).isEmpty
  let bulma := (HtmlDoc.emitTree { css := .bulma } doc).2.1
  t "web measure: a page the engine does not style carries no outline" (elems "nav" bulma).isEmpty

/-- A flow `Layout.paperLossesOnly` passes raises, set, only `Layout.paperLossCodes` beside what its
font assembly raised, and squeezes no frame, so an HTML-only build leaves it unset; each construct
it excludes raises a loss its web page shares. -/
def paperLossChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let mut judged := 0
  let mut faults : Array String := #[]
  let names := goldenNames ++ mdGoldenNames
  for n in names do
    let (doc, _) ← goldenDoc n
    if Layout.paperLossesOnly doc then
      judged := judged + 1
      -- the driver's font assembly names a missing math alphabet before any setting
      let family := oneFace.math.bind (oneFace.fonts[·]?) |>.map (·.family) |>.getD "math face"
      let (doc, raised) := Ir.resolveMathAlphas oneFace.mathAlphabets family doc
      let f := Layout.runFitted (Layout.Geom.ofPage doc.page) oneFace none doc
      for d in f.out.diags do
        unless raised.contains d || (Layout.paperLossCodes.contains d.kind && d.output == some .pdf) do
          faults := faults.push s!"{n}: {d.code}"
      unless f.webSqueeze.isEmpty do faults := faults.push s!"{n}: squeezes"
  t s!"paper losses: an unset flow loses only its paper's losses ({judged} judged, {faults})"
    (judged ≥ 10 && faults.isEmpty)
  let paperOnly (src : String) : Bool × Array Diag :=
    let (doc, _) := elabStr src
    (Layout.paperLossesOnly doc, (layoutOf oneFace doc).diags)
  let article (body : String) : String :=
    "\\documentclass{article}\\begin{document}" ++ body ++ "\\end{document}"
  let wideRow := String.intercalate " & " ((List.range 12).map fun i => s!"column{i}words")
  let (natural, naturalDs) := paperOnly (article ("\\begin{tabular}{" ++ "".pushn 'l' 12 ++ "}" ++ wideRow ++
    "\\end{tabular}"))
  t "paper losses: a natural table past the measure is unset, its overrun the paper's"
    (natural && naturalDs.any fun d => d.kind == .W0338 && d.output == some .pdf)
  let (sized, sizedDs) := paperOnly (article ("\\begin{tabular}{p{5cm}p{5cm}p{5cm}}a & b & c\\end{tabular}"))
  t "paper losses: a table of declared widths is set, its overrun shared"
    (!sized && sizedDs.any fun d => d.kind == .W0338 && d.output.isNone)
  let (tall, tallDs) := paperOnly (article ("x\\footnote{" ++ String.join (List.replicate 600 "tall note words ") ++ "}"))
  t "paper losses: a footnote past the text block is unset, its overrun the paper's"
    (tall && tallDs.any fun d => d.kind == .W0372 && d.output == some .pdf)
  let (allowed, _) := elabStr ("\\documentclass{article}\\allow{W0338}\\begin{document}x\\end{document}")
  t "paper losses: a paper loss accepted by name is set, so its acceptance fires"
    (!Layout.paperLossesOnly allowed)
  let nested := "- a\n  - b\n    - c\n      - d\n        - e\n"
  let (deep, _) := elabMd nested
  t "paper losses: five nested lists are set, W0010 being shared"
    (!Layout.paperLossesOnly deep &&
      (layoutOf oneFace deep).diags.any (·.kind == .W0010))
  let (four, _) := elabMd "- a\n  - b\n    - c\n      - d\n"
  t "paper losses: four nested lists need no setting" (Layout.paperLossesOnly four)
  let (spaced, _) := elabStr ("\\documentclass{article}\\style{section}{ before = 2pt, after = 20pt }" ++
    "\\begin{document}\\section{A}x\\end{document}")
  t "paper losses: a heading's spacing declared both ways is set, W0202 being shared"
    (!Layout.paperLossesOnly spaced &&
      (layoutOf oneFace spaced).diags.any (·.kind == .W0202))
  let (row, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{columns}\\column{0.7\\textwidth}Left words.\\column{0.7\\textwidth}Right words.\\end{columns}" ++
    "\\end{document}")
  t "paper losses: a row of boxes is set, its overrun being shared"
    (!Layout.paperLossesOnly row &&
      (layoutOf oneFace row).diags.any (fun d => d.kind == .W0005 && d.output.isNone))

end Tests.WebMeasure
