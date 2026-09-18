import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The class hook: a semantic distinction the author declares as a named
wrapper survives into the artifact as an addressable annotation. Its absence
was the audited defect — `HtmlDoc.emit ∘ elab` of `\muted{x}` and of `x`
were byte-identical, so no stylesheet could address the author's own role. -/
def classHookChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (mutedDoc, mutedDs) :=
    elabStr (dvDoc "\\define \\muted(word: content) {\\word}\n" "\\muted{quiet} words")
  let (bareDoc, bareDs) := elabStr (dvDoc "" "quiet words")
  t "role sources clean" (mutedDs.isEmpty && bareDs.isEmpty)
  let mutedPage := (HtmlDoc.emit {} mutedDoc).1
  t "an authored role is recoverable from the artifact"
    (mutedPage != (HtmlDoc.emit {} bareDoc).1)
  t "an authored role's class reaches the page"
    ((mutedPage.splitOn "class=\"u-muted\"").length == 2)
  -- Arity reads the definition: a 0-ary command is a spelling, not a role,
  -- and splices transparently.
  let (abbrevDoc, _) :=
    elabStr (dvDoc "\\define \\brand {Example Corp}\n" "\\brand{} words")
  t "a zero-ary command is a spelling, not a role"
    (((HtmlDoc.emit {} abbrevDoc).1.splitOn "u-brand").length == 1)
  -- The census reads through the annotation (role_plaintext): the markdown
  -- twin renders the words, never the wrapper.
  t "the markdown twin reads through a role"
    ((((MarkdownDoc.emit mutedDoc).splitOn "quiet words").length) == 2)
  -- Both halves on one page, judged on the typed tree: a palette role
  -- resolves to its var reference, an authored role to its class — a name
  -- the palette knows adapts, a name it does not becomes addressable, and
  -- neither is silently lost.
  let (bothDoc, bothDs) := elabStr (dvDoc
    ("\\palette{ accent = #205E3B }\n\\define \\entry(word: content) {\\word}\n")
    "\\accent{coloured} and \\entry{classed}")
  t "both halves source clean" bothDs.isEmpty
  let bothTree := HtmlDoc.blockNode {} bothDoc.body[0]!
  let hasSpan (want : String × String) : Html.Node → Bool
    | .elem _ attrs kids => attrs.contains want || kids.any fun k =>
        match k with
        | .elem _ attrs2 kids2 => attrs2.contains want || kids2.any fun k2 =>
            match k2 with
            | .elem _ attrs3 _ => attrs3.contains want
            | _ => false
        | _ => false
    | _ => false
  t "a palette role and an authored role share a page, each addressable"
    (hasSpan ("style", "color: var(--accent, #205e3b)") bothTree &&
     hasSpan ("class", "u-entry") bothTree)
  -- The block half: a command whose expansion is block content keeps its
  -- name on a flow container.
  let (blockRoleDoc, _) := elabStr
    (dvDoc "\\define \\entry(a: content) {\\a\\par}\n" "\\entry{First}\n\\entry{Second}")
  t "a block-level role is an addressable div"
    (((HtmlDoc.emit {} blockRoleDoc).1.splitOn "<div class=\"u-entry\">").length == 3)

/-- `\\style` and its two backends. Its own function: `main` is a single `do`
block and Lean's elaboration budget for one block is spent. -/
def styleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \style: every visual constant a backend applies to an element is a token
  -- the document can name. The font value is a template with a hole.
  let styled := elabStr ("\\documentclass{article}\\palette{ink = #112233}" ++
    "\\tokens{ sep = 3pt }" ++
    "\\style{section}{ font = {\\large\\sffamily\\ink}, before = 2 * sep, after = sep, rule = ink }" ++
    "\\style{itemize}{ indent = 1.2em, gap = sep, marker = {\\ink\\textendash} }" ++
    "\\begin{document}\\section{Head}\\begin{itemize}\\item a\\end{itemize}\\end{document}")
  t "style source clean" (styled.2.all (·.severity == .note))
  let secStyle := styled.1.styles.find? "section"
  t "style section font is a template with a hole"
    ((secStyle.bind (·.font)) == some #[.styled (.size "large") #[.styled .sans
      #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some "ink") #[]]]])
  t "style section spacing reads tokens"
    ((secStyle.bind (·.before)).map (·.width) == some { sp := Dim.pt 6 } &&
     (secStyle.bind (·.after)).map (·.width) == some { sp := Dim.pt 3 })
  t "style section rule names the palette entry"
    ((secStyle.bind (·.rule)).map (·.2) == some (some "ink"))
  let listStyle := styled.1.styles.find? "itemize"
  t "style itemize marker is content"
    ((listStyle.bind (·.marker)) == some #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some "ink") #[.text "–"]])
  -- A declared marker either reaches HTML as declared or the substitution
  -- is named (W0331): the résumé's colour-and-size shape is expressible in
  -- a ::marker rule (CSS Pseudo-Elements 4 §4.1), arbitrary inline content
  -- is not. `markerCss?_text` is the theorem that the expressed content is
  -- exactly the declared characters.
  let dash : Ir.Color := { r := 0x20, g := 0x5E, b := 0x3B }
  t "markerCss? expresses colour and size around text"
    (HtmlDoc.markerCss? #[.colored dash (some "markerink")
        #[.styled (.size "small") #[.text "–"]]] ==
      some { text := "–"
             decls := #["color: var(--markerink, #205e3b);", "font-size: 0.9em;"] })
  t "markerCss? expresses bold plain text"
    (HtmlDoc.markerCss? #[.styled .bold #[.text "»"]] ==
      some { text := "»", decls := #["font-weight: 600;"] })
  t "markerCss? refuses an image marker"
    (HtmlDoc.markerCss? #[.image "rects.png" {} ""] == none)
  t "markerCss? refuses a link marker"
    (HtmlDoc.markerCss? #[.link "https://example.org" #[.text "x"]] == none)
  t "markerCss? refuses a wrapper beside text"
    (HtmlDoc.markerCss? #[.styled .bold #[.text "a"], .text "b"] == none)
  let markerDoc (m : String) : Ir.Doc :=
    (elabStr ("\\documentclass{article}\\palette{ markerink = #205E3B }" ++
      s!"\\style\{itemize}\{ marker = \{{m}} }" ++
      "\\begin{document}\\begin{itemize}\\item a\\end{itemize}\\end{document}")).1
  let (styledMarkerPage, styledMarkerDs) :=
    HtmlDoc.emit {} (markerDoc "\\textcolor{markerink}{\\small\\endash}")
  t "html styled marker reaches ::marker with its colour and size"
    ((styledMarkerPage.splitOn
      "{ content: \"–  \"; color: var(--markerink, #205e3b); font-size: 0.9em; }").length == 2)
  t "html styled marker is clean" (styledMarkerDs.all (·.code != "W0331"))
  let (contentMarkerPage, contentMarkerDs) :=
    HtmlDoc.emit {} (markerDoc "\\includegraphics{rects.png}")
  t "html inexpressible marker is named, not silently defaulted"
    (contentMarkerDs.any fun d => d.code == "W0331" && d.severity == .warning &&
      (d.message.splitOn "itemize").length > 1)
  t "html inexpressible marker emits no ::marker override"
    ((contentMarkerPage.splitOn "rects.png").length == 1)
  -- The content string is escaped: marker text cannot end its own CSS
  -- string (CSS Syntax 3 §4.3.7).
  t "css marker string escapes its delimiters"
    (HtmlDoc.cssString "a\"b\\c" == "a\\\"b\\\\c")
  t "style unknown element" (errCodes ("\\documentclass{article}\\style{footer}{ before = 1pt }" ++
    "\\begin{document}x\\end{document}") == ["E0328"])
  t "style unknown key" (errCodes ("\\documentclass{article}\\style{section}{ colour = 1pt }" ++
    "\\begin{document}x\\end{document}") == ["E0322"])
  t "fillTemplate fills the innermost hole"
    (Ir.fillTemplate #[.styled .bold #[.styled .sans #[]]] #[.text "x"] ==
      #[.styled .bold #[.styled .sans #[.text "x"]]])
  t "fillTemplate leaves plain content alone"
    (Ir.fillTemplate #[.text "–"] #[.text "x"] == #[.text "–"])
  -- The styles reach HTML as CSS on the element, with the template wrapping
  -- the heading and the rule as a class the stylesheet draws.
  let (stylePage, _) := HtmlDoc.emit {} styled.1
  t "html styled heading wraps in the template"
    ((stylePage.splitOn "<h2 class=\"ruled\"><span class=\"size-large\"><span class=\"sans\">").length == 2)
  t "html styled heading spacing" ((stylePage.splitOn "h2 { margin-top: 6pt; margin-bottom: 3pt;").length == 2)
  t "html styled list indent and gap"
    ((stylePage.splitOn "ul { padding-left: 1.2em; }").length == 2 &&
     (stylePage.splitOn "ul > li { margin-top: 3pt; }").length == 2)
  -- Font-relative lengths keep their unit. `1.2em` once became `120%`, which
  -- for padding is a fraction of the container: every styled list left the page.
  t "css em keeps its unit" (HtmlDoc.cssLength { em := 1200 } == "1.2em")
  t "css ex keeps its unit" (HtmlDoc.cssLength { ex := 1500 } == "1.5ex")
  t "css whole em has no fraction" (HtmlDoc.cssLength { em := 2000 } == "2em")
  t "css mixed length sums" (HtmlDoc.cssLength { sp := Dim.pt 3, em := 500 } == "calc(3pt + 0.5em)")
  -- \runninghead[from = 2]: the opening page carries no furniture, and the
  -- gate is the head's own — the undeclared foot keeps its default.
  let (fromDoc, fromDs) := elabStr ("\\documentclass{article}\\runninghead[from = 2]{x}" ++
    "\\begin{document}y\\end{document}")
  t "running from clean" (fromDs.isEmpty && fromDoc.headFrom == 2 && fromDoc.footFrom == 1)

/-- The HTML article layout is a faithful degradation of the PDF page: the
measure, fill rows, link colour, and heading rules all follow the IR. Its own
function, same elaboration-budget reason. -/
def htmlLayoutChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The measure is the page's text width over the base font size, in em so
  -- it scales with the browser font. It used to be a fixed 68ch, an
  -- unrelated design the PDF page never asked for.
  t "html measure derives from the default page"
    (HtmlDoc.measureEm {} == "46.8em")
  let (narrowDoc, narrowDs) := elabStr ("\\documentclass{article}" ++
    "\\page{ hmargin = 0.75in }\\begin{document}x\\end{document}")
  t "html measure follows a declared page" (narrowDs.isEmpty &&
    ((HtmlDoc.emit {} narrowDoc).1.splitOn "--measure: 50.4em;").length == 2)
  -- Exactly two fill groups reserve the right group's max-content width,
  -- then let the left group wrap in what remains. More groups retain the
  -- general flex semantics instead of pretending to be a two-column row.
  let hasClass (name : String) (attrs : Array (String × String)) : Bool :=
    attrs.any fun (key, value) =>
      key == "class" && (value.splitOn " ").contains name
  let (entryDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left label \\hfill 2021\\end{document}")
  let entryTree := HtmlDoc.blockNode {} entryDoc.body[0]!
  let entryPage := (HtmlDoc.emit {} entryDoc).1
  t "html two-group fill row selects the pair contract"
    (match entryTree with
    | .elem "p" attrs kids =>
      hasClass "entry-pair" attrs && kids.size == 2 && kids.all fun child =>
        match child with
        | .elem "span" childAttrs _ => hasClass "group" childAttrs
        | _ => false
    | _ => false)
  t "html pair allocates the right max-content column first"
    ((entryPage.splitOn
      "grid-template-columns: minmax(0, 1fr) max-content;").length == 2)
  t "html pair stacks to one column only at a narrow viewport"
    ((entryPage.splitOn "@media (max-width: 30rem)").length == 2 &&
     (entryPage.splitOn "grid-template-columns: minmax(0, 1fr);").length == 2)
  t "html a stacked last group right-aligns"
    ((entryPage.splitOn ".group:last-child { text-align: right; }").length == 2)
  let (manyDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill middle \\hfill right\\end{document}")
  t "html three-group fill row retains general semantics"
    (match HtmlDoc.blockNode {} manyDoc.body[0]! with
    | .elem "p" attrs kids =>
      hasClass "entry" attrs && !hasClass "entry-pair" attrs && kids.size == 3
    | _ => false)
  let (rowsDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "a \\hfill b\\\\c \\hfill d\\end{document}")
  t "html broken two-group rows select the pair contract"
    (((HtmlDoc.emit {} rowsDoc).1.splitOn
      "<span class=\"entry-row entry-pair\"><span class=\"group\">").length == 3)
  -- The anchor itself carries inheritance, so a host framework cannot remap
  -- links away from the document or enclosing IR colour.
  let (linkDoc, linkDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\href{https://example.org}{invented link}\\end{document}")
  let inheritedLink :=
    "<a href=\"https://example.org\" style=\"color: inherit\">invented link</a>"
  t "html link source is clean" linkDs.isEmpty
  t "html links inherit in every CSS mode"
    ([HtmlDoc.CssMode.own, .bulma, .none].all fun mode =>
      (((HtmlDoc.emit { css := mode } linkDoc).1.splitOn inheritedLink).length == 2))
  let bulmaPage := (HtmlDoc.emit { css := .bulma } linkDoc).1
  t "bulma does not remap links to the accent"
    ((bulmaPage.splitOn "--bulma-link:").length == 1)
  t "html link keeps a visible focus"
    ((entryPage.splitOn "a:focus-visible { outline:").length == 2)
  -- A heading rule sits on the text baseline, where the PDF draws it, not at
  -- the heading's vertical middle.
  let (ruledDoc, _) := elabStr ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink }\\begin{document}\\section{H}\\end{document}")
  t "html heading rule aligns at the baseline"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn
      "h2 { display: flex; align-items: baseline;").length == 2)

/-- The HTML rhythm realization, censused over emitted sheets: every default
vertical gap is one emission — the below element's `margin-top`, computed
from the declared table (`Ir.rhythmGapQuanta`) in the screen context's
quanta — and the one `margin-bottom` in a whole emitted page is the
caption-above float's internal seam, whose neighbour declares no top
margin, so single ownership holds there too. A second margin-bottom would
be a boundary with two emitters: the box-model defect
`HtmlDoc.single_owner_gap_exact` exists to exclude (block flow collapses
the pair, a flex column sums it — the site port shipped 52 px for a
declared 32 px exactly that way). Its own function: `main`'s elaboration
budget is spent. -/
def htmlRhythmChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (plainDoc, plainDs) := elabStr
    "\\documentclass{article}\\begin{document}a\n\nb\n\\end{document}"
  let plainPage := (HtmlDoc.emit {} plainDoc).1
  t "html rhythm fixture elaborates clean" plainDs.isEmpty
  t "html base sheet has one gap owner per boundary"
    ((plainPage.splitOn "margin-bottom").length == 2)
  -- The one longhand margin-bottom is the caption-above float's seam; the
  -- other deliberately bottom-owned boundary is the heading's band below
  -- (PDF semantics; its follower's default top margin is suppressed),
  -- spelled as shorthand and pinned below. The longhand census cannot see
  -- a shorthand (`margin: 0 0 1rem` spells no "margin-bottom"), so the
  -- ownership of each block element is pinned by its whole rule.
  -- Verified load-bearing: putting a bottom margin back on blockquote
  -- fails here.
  t "html heading owns its band below, followers suppressed"
    ((plainPage.splitOn "margin: 0 0 0.725rem;").length == 2 &&
     (plainPage.splitOn ":where(h1, h2, h3, h4) + * { margin-top: 0; }").length == 2)
  t "html block elements own no vertical margins"
    ((plainPage.splitOn "p { margin: 0; }").length == 2 &&
     (plainPage.splitOn "ul, ol { margin: 0; padding-left: 1.35rem; }").length == 2 &&
     (plainPage.splitOn "li { margin: 0; }").length == 2 &&
     (plainPage.splitOn "blockquote { margin: 0; padding: 0 1.35rem; }").length == 2 &&
     (plainPage.splitOn "figure.float { margin: 0 auto; }").length == 2)
  t "html peer gap is one screen quantum, top-owned"
    ((plainPage.splitOn ":where(* + p) { margin-top: 0.725rem; }").length == 2)
  t "html heading gap is two screen quanta"
    ((plainPage.splitOn ":where(* + h2) { margin-top: 1.450rem; }").length == 2)
  t "html float gap keeps its token over the rhythm default"
    ((plainPage.splitOn
      ":where(* + figure.float) { margin-top: var(--floatsep, 1.450rem); }").length == 2)
  t "html float owns the boundary below it"
    ((plainPage.splitOn
      ":where(figure.float + *) { margin-top: var(--floatsep, 1.450rem); }").length == 2)
  let (themedDoc, themedDs) := elabStr ("\\documentclass{beamer}\\usetheme{moloch}" ++
    "\\begin{document}\\section{s}\\begin{frame}{t}x\\end{frame}\\end{document}")
  let themedPage := (HtmlDoc.emit {} themedDoc).1
  t "html themed fixture elaborates clean"
    (themedDs.all fun d => d.severity == .note)
  t "html progress height reads the token the PDF reads"
    ((themedPage.splitOn "height: var(--progressheight, 1pt);").length == 2)
  t "html themed sheet has one gap owner per boundary"
    ((themedPage.splitOn "margin-bottom").length == 2)

/-- Article sections become anchored containers: `<section id="slug">` wraps
the heading and its content, ids stay unique under repeated titles, and an
in-page `\href{#...}` has a real target. Invented titles throughout. -/
def anchorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Opening paragraph.\\section*{Signal Path}First.\\section*{Noise}Second." ++
    "\\section*{Noise}Third.\\end{document}")
  let page := (HtmlDoc.emit {} doc).1
  t "html anchors source is clean" ds.isEmpty
  t "html level-1 sections become containers with slug ids"
    ((page.splitOn "<section id=\"signal-path\">").length == 2 &&
     (page.splitOn "<section id=\"noise\">").length == 2)
  t "html a repeated title takes a numbered anchor"
    ((page.splitOn "<section id=\"noise-2\">").length == 2)
  t "html content before the first section stays outside the containers"
    (match (page.splitOn "Opening paragraph.")[0]? with
     | some before => (before.splitOn "<section").length == 1
     | none => false)
  t "html every container closes" ((page.splitOn "</section>").length == 4)
  -- Identifier fidelity: HTML §3.2.6 forbids only ASCII whitespace in an id
  -- and the WHATWG URL fragment percent-encode set excludes non-ASCII, so a
  -- title's own letters — accented or CJK — survive into its anchor instead
  -- of degrading to hyphens. Invented titles.
  let (intlDoc, intlDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\section*{Café Notes}First.\\section*{概要}Second." ++
    "\\section*{Caf Notes}Third.\\end{document}")
  let (intlPage, intlDiags) := HtmlDoc.emit {} intlDoc
  t "html accented anchors keep their letters" (intlDs.isEmpty &&
    (intlPage.splitOn "<section id=\"café-notes\">").length == 2)
  t "html cjk anchors keep their characters"
    ((intlPage.splitOn "<section id=\"概要\">").length == 2)
  t "html titles that folded together under the ascii rule stay distinct"
    ((intlPage.splitOn "<section id=\"caf-notes\">").length == 2 &&
     intlDiags.isEmpty)
  -- Two distinct titles that still fold to the same slug: the ids stay
  -- unique and W0320 names the collision, because a link written from the
  -- second title's text would silently reach the first section.
  let (clashDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\section*{Signal Path}One.\\section*{Signal, Path}Two.\\end{document}")
  let (clashPage, clashDiags) := HtmlDoc.emit {} clashDoc
  t "html a folded collision of distinct titles warns W0327"
    (clashDiags.any (·.code == "W0327"))
  t "html the colliding sections still take distinct anchors"
    ((clashPage.splitOn "<section id=\"signal-path\">").length == 2 &&
     (clashPage.splitOn "<section id=\"signal-path-2\">").length == 2)
  t "html a repeated identical title numbers quietly"
    (!ds.any (·.code == "W0327") &&
     !(HtmlDoc.emit {} doc).2.any (·.code == "W0327"))
  -- The numbered fallback is itself an id: a title whose own slug is
  -- `noise-2` must not collide with the number handed to a repeated
  -- `Noise`. Uniqueness is per assigned id, not per base.
  let (numDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\section*{Noise}A.\\section*{Noise}B.\\section*{Noise 2}C.\\end{document}")
  let numPage := (HtmlDoc.emit {} numDoc).1
  t "html a numbered fallback never collides with a real title"
    ((numPage.splitOn "<section id=\"noise-2\">").length == 2 &&
     (numPage.splitOn "<section id=\"noise-2-2\">").length == 2)
  let (navDoc, navDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\href{#trailhead}{jump}\\section*{Trailhead}Body.\\end{document}")
  let navPage := (HtmlDoc.emit {} navDoc).1
  t "html an in-page link reaches its section anchor" (navDs.isEmpty &&
    (navPage.splitOn "<a href=\"#trailhead\"").length == 2 &&
    (navPage.splitOn "<section id=\"trailhead\">").length == 2)
  -- Slides keep their own sectioning: one <section> per frame, none per title.
  let (deck, _) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}{One}a\\end{frame}\\end{document}")
  t "html slides sectioning is untouched"
    (((HtmlDoc.emit {} deck).1.splitOn "<section id=").length == 1)
  -- The declared stylesheet: named by the document, linked after the inline
  -- styles in every css mode, and quoted or bare spellings agree.
  let sheetSrc (v : String) := "\\documentclass{article}" ++
    s!"\\output\{ stylesheet = {v} }\\begin\{document}x\\end\{document}"
  let (sheetDoc, sheetDs) := elabStr (sheetSrc "\"site.css\"")
  let (bareDoc, bareDs) := elabStr (sheetSrc "site.css")
  let link := "<link rel=\"stylesheet\" href=\"site.css\">"
  t "output stylesheet parses quoted and bare" (sheetDs.isEmpty && bareDs.isEmpty &&
    sheetDoc.output.stylesheet == some "site.css" &&
    bareDoc.output.stylesheet == some "site.css")
  t "html links the declared stylesheet in every css mode"
    ([HtmlDoc.CssMode.own, .bulma, .none].all fun mode =>
      ((HtmlDoc.emit { css := mode } sheetDoc).1.splitOn link).length == 2)
  t "html declared stylesheet follows the inline styles"
    (match ((HtmlDoc.emit {} sheetDoc).1.splitOn link)[0]? with
     | some before => (before.splitOn "</style>").length == 2
     | none => false)
  t "html no stylesheet, no link"
    (((HtmlDoc.emit {} doc).1.splitOn "<link rel=\"stylesheet\"").length == 1)

/-- The markdown backend: the llms.txt twin comes from the same IR as the
page. Metadata is the preamble, structure maps, decoration degrades to its
text, and a speaker note stays a side channel. Invented content. -/
def markdownChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Alex Doe, PhD\", subject = \"An invented person.\" }" ++
    "\\begin{document}" ++
    "Intro with \\textbf{weight} and \\href{https://example.org}{a link}." ++
    "\\section*{Field Notes}" ++
    "Label \\hfill 2021\\par" ++
    "\\begin{itemize}\\item One thing\\item Another\\end{itemize}" ++
    "\\end{document}")
  let md := (MarkdownDoc.emit doc)
  t "markdown source is clean" ds.isEmpty
  t "markdown metadata renders as the llms.txt preamble"
    (md.startsWith "# Alex Doe, PhD\n\n> An invented person.\n\n")
  t "markdown keeps meaning and degrades decoration"
    ((md.splitOn "Intro with **weight** and [a link](https://example.org).").length == 2)
  t "markdown reserves # for the title"
    ((md.splitOn "\n## Field Notes\n").length == 2 && (md.splitOn "\n# ").length == 1)
  t "markdown fill separates as an em dash"
    ((md.splitOn "Label — 2021").length == 2)
  t "markdown lists are lists"
    ((md.splitOn "- One thing\n- Another\n").length == 2)
  t "markdown ends with exactly one newline"
    (md.endsWith "\n" && !(md.endsWith "\n\n"))
  let (bare, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Just a body: https://example.org text.\\end{document}")
  t "markdown without metadata has no preamble"
    ((MarkdownDoc.emit bare).startsWith "Just a body:")
  let (deck, _) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}{Opening}Visible.\\note{hidden aside}\\end{frame}\\end{document}")
  let deckMd := (MarkdownDoc.emit deck)
  t "markdown frames are sections, notes stay out"
    ((deckMd.splitOn "## Opening").length == 2 &&
     (deckMd.splitOn "hidden aside").length == 1)
  let (esc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "under\\_score and 2*3\\end{document}")
  t "markdown escapes what would read as markup"
    (((MarkdownDoc.emit esc).splitOn "under\\_score and 2\\*3").length == 2)
  -- The declared text alternative (graphicx's alt key, LaTeX News 37)
  -- reaches both backends, and a caption does not overwrite it.
  let (img, imgDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\includegraphics[width=32pt, alt={An invented portrait}]{face.png}" ++
    "\\end{document}")
  t "image alt declares and reaches both backends" (imgDs.isEmpty &&
    (((HtmlDoc.emit {} img).1.splitOn "alt=\"An invented portrait\"").length == 2) &&
    (((MarkdownDoc.emit img).splitOn "![An invented portrait](face.png)").length == 2))
  let (figImg, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{figure}\\includegraphics[alt={Declared wins}]{face.png}" ++
    "\\caption{A caption}\\end{figure}\\end{document}")
  t "figure caption fills only an undeclared alt"
    (((HtmlDoc.emit {} figImg).1.splitOn "alt=\"Declared wins\"").length == 2)

/-- The llms.txt preamble's placement invariant, over all four title
sources: the summary stands immediately after the title line, wherever the
title comes from — the metadata `#` line or the body's own level-0 heading
(`\maketitle`) — and above the body only when nothing carries a title. The
theorems in MarkdownDoc pin the two titled shapes; these pin all four
end-to-end, plus the mid-document remainder ("never precedes"). Own
function: `main`'s elaboration budget. -/
def mdPreambleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- 1: metadata title only — the preamble carries both lines, in order.
  let (metaOnly, ds1) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Meta Title\", subject = \"A meta summary.\" }" ++
    "\\begin{document}Body text.\\end{document}")
  t "metadata-only source is clean" ds1.isEmpty
  t "metadata title: summary follows the title line"
    ((MarkdownDoc.emit metaOnly) == "# Meta Title\n\n> A meta summary.\n\nBody text.\n")
  -- 2: body heading only — the summary follows the body's own title line.
  let bodyOnly : Ir.Doc := {
    info := { subject := some "A body-titled summary." }
    body := #[.section 0 false #[.text "Body Title"], .para #[.text "After."]] }
  t "body title: summary follows the body's title line"
    ((MarkdownDoc.emit bodyOnly) ==
      "# Body Title\n\n> A body-titled summary.\n\nAfter.\n")
  -- 3: both — the body's heading wins; one `#` line, one title, summary after it.
  let (both, ds3) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ subject = \"A shared summary.\" }\\title{Both Sources}" ++
    "\\begin{document}\\maketitle Body text.\\end{document}")
  t "both-sources source is clean" ds3.isEmpty
  let bothMd := (MarkdownDoc.emit both)
  t "both sources: the body's title line leads and the summary follows"
    (bothMd.startsWith "# Both Sources\n\n> A shared summary.\n\n")
  t "both sources: exactly one # line, the title stated once"
    ((bothMd.splitOn "\n# ").length == 1 && (bothMd.splitOn "# Both Sources").length == 2)
  -- 4: neither — nothing carries a title, so the summary opens the twin.
  let neither : Ir.Doc := {
    info := { subject := some "Only a summary." }
    body := #[.para #[.text "x"]] }
  t "no title anywhere: the summary opens the twin"
    ((MarkdownDoc.emit neither) == "> Only a summary.\n\nx\n")
  -- The remainder: a mid-document title (W0321 warns) still pulls the
  -- summary to its own line — after the title, never above the body.
  let mid : Ir.Doc := {
    info := { subject := some "A late summary." }
    body := #[.para #[.text "Lead."], .section 0 false #[.text "Late Title"]] }
  t "a mid-document title carries the summary with it"
    ((MarkdownDoc.emit mid) == "Lead.\n\n# Late Title\n\n> A late summary.\n")
  -- The twin of a small-caps run is its text with the authored casing:
  -- `\scshape` renders uniform small capitals, so the source carries the
  -- reading form and plain text is correct as typed. (W0344 named the loss
  -- back when uniform small caps required writing the casing wrong; it
  -- retired with the workaround.)
  let (sc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "{\\scshape PhD}\\end{document}")
  t "the twin of a mixed-case small-caps run carries the authored casing"
    ((MarkdownDoc.emit sc) == "PhD\n")

/-- One fact, three renderings: a heading's level maps to the same rank in
every backend — `#`-count and `h`-number are both level + 1 (the PDF side
is the census assertion that the title text ships as furniture). Stated
over the two functions the backends actually run. -/
theorem heading_renderings_agree :
    (MarkdownDoc.headingMarker 0 = "#" ∧ HtmlDoc.headingTag 0 = "h1") ∧
    (MarkdownDoc.headingMarker 1 = "##" ∧ HtmlDoc.headingTag 1 = "h2") ∧
    (MarkdownDoc.headingMarker 2 = "###" ∧ HtmlDoc.headingTag 2 = "h3") ∧
    (MarkdownDoc.headingMarker 3 = "####" ∧ HtmlDoc.headingTag 3 = "h4") := by
  decide

/-- `{ifbackend}`: content addressed to a subset of the backends. One IR,
elaborated once; each backend keeps or drops through `Ir.keepFor` at its own
entry. The diagnostics, the `orphanFree` correspondence (the hypothesis of
`Ir.keepFor_covers`, checked here on a real elaboration), and each backend's
kept view are pinned. Invented content. Its own function: `main` is one `do`
block and its elaboration budget is spent. -/
def backendChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Shared opening.\\begin{ifbackend}{html}Only the page carries this." ++
    "\\end{ifbackend}\\begin{ifbackend}{pdf,md}Print and twin carry this." ++
    "\\end{ifbackend}\\end{document}")
  t "ifbackend source is clean" ds.isEmpty
  t "ifbackend carries its target set"
    (match doc.body[1]? with
     | some (Ir.Block.only targets _) => targets == #["html"]
     | _ => false)
  let htmlBody := Ir.keepFor "html" doc.body
  let mdBody := Ir.keepFor "md" doc.body
  t "keepFor keeps the addressed subtree and drops the other"
    (has (Ir.blocksText htmlBody) "Only the page carries this." &&
     !has (Ir.blocksText htmlBody) "Print and twin" &&
     has (Ir.blocksText mdBody) "Print and twin carry this." &&
     !has (Ir.blocksText mdBody) "Only the page")
  -- The theorem's hypothesis holds on the elaborated document, and its
  -- conclusion is observable: every declared leaf survives in some backend.
  t "declared content is orphan-free and every leaf survives somewhere"
    (Ir.orphanFree Ir.backendNames doc.body &&
     (Ir.textLeaves doc.body).all fun leaf =>
        Ir.backendNames.any fun b =>
          (Ir.textLeaves (Ir.keepFor b doc.body)).contains leaf)
  let page := (HtmlDoc.emit {} doc).1
  t "html emits only its own conditional content"
    (has page "Only the page carries this." && !has page "Print and twin")
  t "html marks conditional content with its target set"
    (has page "<div data-backend=\"html\">")
  let md := (MarkdownDoc.emit doc)
  t "markdown emits only its own conditional content"
    (has md "Print and twin carry this." && !has md "Only the page")
  -- Diagnostics: an unknown backend name (W0323), and content no backend
  -- answers (E0334) — flat by typo, or nested by empty intersection.
  t "unknown backend name warns, and an emptied set errors with it"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{ifbackend}{web}x\\end{ifbackend}\\end{document}")
      == ["W0323"] &&
     errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{ifbackend}{web}x\\end{ifbackend}\\end{document}")
      == ["E0334"])
  let nested := "\\documentclass{article}\\begin{document}" ++
    "\\begin{ifbackend}{html}\\begin{ifbackend}{pdf}Orphaned.\\end{ifbackend}" ++
    "\\end{ifbackend}\\end{document}"
  t "nested conditionals intersect to nothing and error"
    (errCodes nested == ["E0334"])
  t "orphanFree mirrors W0321 on the same document"
    (!Ir.orphanFree Ir.backendNames (elabStr nested).1.body)
  t "a missing backends group is an error"
    (errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{ifbackend}text\\end{ifbackend}\\end{document}") == ["E0304"])

/-- The navigation landmark and its two artifact-judged contracts: at most
one unlabeled `<nav>` per page (W0325 — ARIA Authoring Practices, Landmark
Regions: a repeated landmark role needs unique labels, and the engine has
no label mechanism yet) and every in-page link resolving to an anchor the
page emits (W0326 — with '#' and any-ASCII-case '#top' exempt, which the
HTML spec's fragment navigation scrolls to the top of the document). Both
judged over the emitted tree, never the IR: a backend conditional may keep
a nav on one surface only, and only the tree knows what this page carries.
Invented content. -/
def landmarkChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#field-notes}{Notes} \\href{#top}{Top}\\end{nav}" ++
    "\\section*{Field Notes}Body text.\\end{document}")
  let (page, pds) := HtmlDoc.emit {} doc
  t "nav source and page are clean" (ds.isEmpty && pds.isEmpty)
  t "nav emits the landmark element around its links"
    (has page "<nav>" && has page "</nav>" && has page "<a href=\"#field-notes\""
      && has page "<section id=\"field-notes\">")
  t "markdown keeps a nav's content transparent"
    (has (MarkdownDoc.emit doc) "[Notes](#field-notes)")
  let (two, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#a-head}{A}\\end{nav}\\begin{nav}\\href{#a-head}{B}\\end{nav}" ++
    "\\section*{A Head}x\\end{document}")
  t "a second nav landmark warns"
    (((HtmlDoc.emit {} two).2.filter (·.code == "W0325")).size == 1)
  let (kept, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#a-head}{A}\\end{nav}" ++
    "\\begin{ifbackend}{pdf}\\begin{nav}\\href{#a-head}{B}\\end{nav}\\end{ifbackend}" ++
    "\\section*{A Head}x\\end{document}")
  t "a nav another backend owns does not count against this page"
    (((HtmlDoc.emit {} kept).2.filter (·.code == "W0325")).size == 0)
  let (dangle, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\href{#nowhere}{broken} \\href{#nowhere}{again} \\href{#}{up} " ++
    "\\href{#TOP}{Top}\\section*{Somewhere}x\\end{document}")
  let ddiags := ((HtmlDoc.emit {} dangle).2.filter (·.code == "W0326"))
  t "a dangling in-page link is diagnosed once, by name, with the anchors"
    (ddiags.size == 1 &&
     ddiags.all (fun d => (d.message.splitOn "#nowhere").length > 1 &&
       ((d.help.getD "").splitOn "#somewhere").length > 1))
  t "the spec's top fragments resolve without anchors"
    (!ddiags.any fun d =>
      (d.message.splitOn "#TOP").length > 1 || (d.message.splitOn "'#'").length > 1)

/-- The markdown twin's declared name: `\output{ md = "llms.txt" }` rides
the one OutputSpec, so the driver writes the twin as served and the head's
alternate link cannot drift from the file. -/
def mdNameChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\output{ formats = html, md, md = \"llms.txt\" }" ++
    "\\begin{document}x\\end{document}")
  t "md name source clean" ds.isEmpty
  t "the declared twin name is on the output spec" (doc.output.md == some "llms.txt")
  let (page, _) := HtmlDoc.emit { mdHref := some "llms.txt" } doc
  t "the head's alternate link names the served file"
    (((page.splitOn "rel=\"alternate\" type=\"text/markdown\" href=\"llms.txt\"").length) ≥ 2)
  t "an unknown output key is still named"
    (errCodes ("\\documentclass{article}\\output{ pdfx = yes }" ++
      "\\begin{document}x\\end{document}") == ["E0322"])

/-- The pinned placement and the declared reveal: a labeled nav names its
landmark instance (so it never counts toward W0325), a pin becomes
`position: fixed` at the declared corner and offset — read by the HTML
backend alone, the PDF has no viewport — and a declared reveal ships the
scroll-driven CSS (`@supports`, declarative where the platform has it) and
the constant script fallback, judged over the emitted tree. Invented
content. -/
def pinChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let pinnedSrc := "\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#one-head}{One}\\end{nav}" ++
    "\\begin{nav}[label = Return to top, pin = bottom right, " ++
    "offset = 1.5em, reveal = 300px]\\href{#top}{Up}\\end{nav}" ++
    "\\section*{One Head}x\\end{document}"
  let (doc, ds) := elabStr pinnedSrc
  let (page, pds) := HtmlDoc.emit {} doc
  t "pinned nav source and page are clean" (ds.isEmpty && pds.isEmpty)
  t "a labeled nav names its landmark and never counts toward W0325"
    (has page "<nav aria-label=\"Return to top\"" &&
      !pds.any (·.code == "W0325"))
  t "the pin is fixed positioning at the declared corner and offset"
    (has page "position: fixed; bottom: 1.5em; right: 1.5em")
  t "the declared reveal range rides as a custom property, in points"
    (has page "--reveal-range: 225pt")
  t "the reveal ships its declarative form, and only that"
    (has page "@supports (animation-timeline: scroll())" &&
      has page "@keyframes ltx-reveal")
  -- Compatibility is the framework's job, not the engine's: where the
  -- platform lacks scroll-driven animations the control is simply visible,
  -- and no backend emits script to hide that.
  t "no backend emits script for the reveal"
    (!has page "CSS.supports" && !has page "js-reveal" &&
      !has page "addEventListener")
  -- No reveal declared: none of the machinery ships.
  let (plain, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#one-head}{One}\\end{nav}\\section*{One Head}x\\end{document}")
  let (plainPage, _) := HtmlDoc.emit {} plain
  t "no declared reveal, no reveal css"
    (!has plainPage "ltx-reveal" && !has plainPage "CSS.supports")
  -- A reveal another backend owns ships nothing here: judged over the tree.
  let (kept, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{ifbackend}{pdf}\\begin{nav}[label = Up, pin = bottom right, " ++
    "reveal = scroll]\\href{#one-head}{Up}\\end{nav}\\end{ifbackend}" ++
    "\\section*{One Head}x\\end{document}")
  let (keptPage, _) := HtmlDoc.emit {} kept
  t "a reveal another backend owns ships nothing on this page"
    (!has keptPage "ltx-reveal" && !has keptPage "CSS.supports")
  -- The markdown twin keeps a pinned nav transparent, as any nav.
  t "markdown keeps a pinned nav transparent" (has (MarkdownDoc.emit doc) "[Up](#top)")
  -- Declaration mistakes are named, never silent.
  t "offset or reveal without a pin is named as ignored"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{nav}[reveal = scroll]\\href{#a-head}{A}\\end{nav}" ++
      "\\section*{A Head}x\\end{document}") == ["W0110"])
  t "a corner that is not two edge words is E0321"
    (errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{nav}[pin = sideways]\\href{#a-head}{A}\\end{nav}" ++
      "\\section*{A Head}x\\end{document}") == ["E0321"])
  t "an unknown nav key is E0322"
    (errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{nav}[sticky = yes]\\href{#a-head}{A}\\end{nav}" ++
      "\\section*{A Head}x\\end{document}") == ["E0322"])

/-- Interaction states are style keys, not a subsystem: `hover`/`focus`
colour an element's links in that state, `motion` is the transition between
them, and a declared motion cannot ship unguarded (`HtmlDoc.motionCss`;
WCAG 2.2 SC 2.3.3 with sufficient technique C39, the
`prefers-reduced-motion` query of CSS Media Queries 5 §12.1). The PDF path
reads none of the three keys. Invented content. -/
def interactionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\palette{ ink = #1D4ED8 }" ++
    "\\style{nav}{ hover = ink, focus = ink, motion = 150ms }" ++
    "\\begin{document}\\begin{nav}\\href{#one-head}{One}\\end{nav}" ++
    "\\section*{One Head}x\\end{document}")
  t "interaction keys parse" (ds.isEmpty &&
    ((doc.styles.find? "nav").bind (·.hover)).map (·.2) == some (some "ink") &&
    ((doc.styles.find? "nav").bind (·.motion)) == some 150)
  -- css = none ships only the declared rules, so the guard must ride with
  -- the declaration: both halves are checked on the emitted page.
  let (page, pds) := HtmlDoc.emit { css := .none } doc
  t "declared hover and focus land on the nav's links" (pds.isEmpty &&
    has page "nav a:hover { color: var(--ink, #1d4ed8); }" &&
    has page "nav a:focus-visible { outline-color: var(--ink, #1d4ed8); }")
  t "a declared motion ships with its guard even without the base sheet"
    (has page "nav a { transition: color 150ms, outline-color 150ms; }" &&
     has page ("@media (prefers-reduced-motion: reduce) " ++
       "{ nav a { transition: none; } }"))
  t "an unreadable motion duration is an error"
    (errCodes ("\\documentclass{article}\\style{nav}{ motion = fast }" ++
      "\\begin{document}x\\end{document}") == ["E0323"])

/-- The single-emission-site check for `transition:`: nothing but
`HtmlDoc.motionCss` and the base stylesheet's global reduce guard — both in
HtmlDoc.lean — may spell a transition into emitted styles. This is the
architectural half of the by-construction claim `motionCss_guarded`
states; the scan is the same shape as `diagChecks`'. -/
def motionSiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  for f in files do
    let src ← IO.FS.readFile f
    if (src.splitOn "transition:").length > 1 then
      check ref s!"transition is spelled only in HtmlDoc ({f})"
        (f.toString.endsWith "HtmlDoc.lean")

/-- Declared once, derived everywhere: every metadata fact lives in the one
`Ir.Meta` record and each surface derives its own rendering of it — the HTML
head, the llms.txt preamble, and the PDF's Info dictionary and XMP read the
same field, so no surface can drift from another (the report's principle 3).
Invented facts, example.org throughout. -/
def webMetaChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Alex Doe, PhD\", subject = \"An invented person.\"," ++
    " author = \"Alex Doe\", url = \"https://example.org/alex\"," ++
    " image = \"https://example.org/alex/card.png\", favicon = \"favicon.svg\" }" ++
    "\\begin{document}Body text.\\end{document}")
  t "web meta source is clean" ds.isEmpty
  t "web meta declares the record once"
    (doc.info.url == some "https://example.org/alex" &&
     doc.info.image == some "https://example.org/alex/card.png" &&
     doc.info.favicon == some "favicon.svg")
  let page := (HtmlDoc.emit {} doc).1
  let has (s : String) : Bool := (page.splitOn s).length ≥ 2
  t "html head links the canonical url"
    (has "<link rel=\"canonical\" href=\"https://example.org/alex\">")
  t "html head links the favicon" (has "<link rel=\"icon\" href=\"favicon.svg\">")
  t "html og facts derive from the one record"
    (has "<meta property=\"og:title\" content=\"Alex Doe, PhD\">" &&
     has "<meta property=\"og:description\" content=\"An invented person.\">" &&
     has "<meta property=\"og:url\" content=\"https://example.org/alex\">" &&
     has "<meta property=\"og:image\" content=\"https://example.org/alex/card.png\">" &&
     has "<meta property=\"og:type\" content=\"website\">")
  t "html twitter derives only its card kind; the facts fall back to og"
    (has "<meta name=\"twitter:card\" content=\"summary\">" && !has "twitter:title")
  -- The llms.txt twin is discoverable from the page: when the driver
  -- writes one beside the html, the head links it (rel=alternate,
  -- HTML §4.6.6.1; text/markdown, RFC 7763).
  let mdPage := (HtmlDoc.emit { mdHref := some "profile.md" } doc).1
  t "html links its markdown twin as the alternate representation"
    ((mdPage.splitOn ("<link rel=\"alternate\" type=\"text/markdown\" " ++
        "href=\"profile.md\">")).length == 2 &&
     !has "rel=\"alternate\"")
  let md := (MarkdownDoc.emit doc)
  let pdf := Pdf.write geom oneFace (Layout.run geom oneFace none doc).pages doc.info
  t "the one declared title reaches all three surfaces"
    (has "<title>Alex Doe, PhD</title>" &&
     md.startsWith "# Alex Doe, PhD\n" &&
     bytesContain pdf "/Title (Alex Doe, PhD)")
  t "the one declared url reaches the pdf as XMP dc:identifier"
    (bytesContain pdf "<dc:identifier>https://example.org/alex</dc:identifier>")
  -- JSON-LD is the same record again, as a data block. Values pass the
  -- certified JSON escaper, so a hostile title can neither end its own
  -- string nor close the script element.
  let (bare, _) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Quiet Page\" }\\begin{document}x\\end{document}")
  t "html json-ld derives from the one record"
    (has "<script type=\"application/ld+json\">" &&
     has "\"@type\": \"WebPage\"" &&
     has "\"name\": \"Alex Doe, PhD\"" &&
     has "\"url\": \"https://example.org/alex\"" &&
     has "\"author\": {\"@type\": \"Person\", \"name\": \"Alex Doe\"}")
  let hostile := { bare with info := { bare.info with
    url := some "https://example.org/x"
    title := some "a\"</script><b>b" } }
  let hostilePage := (HtmlDoc.emit {} hostile).1
  t "html json-ld escapes a hostile value and survives the payload guard"
    ((hostilePage.splitOn
        "\"name\": \"a\\u0022\\u003c/script>\\u003cb>b\"").length == 2 &&
     (hostilePage.splitOn "/* removed */").length == 1)
  let barePage := (HtmlDoc.emit {} bare).1
  t "html without a declared web identity emits none of the web head"
    ((barePage.splitOn "og:").length == 1 &&
     (barePage.splitOn "rel=\"canonical\"").length == 1 &&
     (barePage.splitOn "twitter:").length == 1 &&
     (barePage.splitOn "ld+json").length == 1)

/-- The content stream a strict viewer accepts. Own function, same
elaboration-budget reason as the others. -/
def pdfStreamChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- The pen is moved by `Tm` when a gap is wide; a `TJ` adjustment is
  -- thousandths of the font size and macOS Preview drops an array holding
  -- one past ±32767 — which is how two headings vanished from a resume.
  -- And an array with no glyphs (a rule-only line) is never written.
  let asciiText (pdf : ByteArray) : String :=
    String.fromUTF8! ⟨pdf.data.map fun b => if b < 128 then b else 46⟩
  let tjNumbers (text : String) : List Int × Nat := Id.run do
    let mut nums : List Int := []
    let mut emptyArrays := 0
    for arr in (text.splitOn "] TJ").dropLast do
      let body := (arr.splitOn "[").getLast?.getD ""
      if !body.any (· == '<') then emptyArrays := emptyArrays + 1
      -- Outside <...> strings, the numbers are adjustments.
      let mut inHex := false
      let mut cur := ""
      for c in body.toList ++ [' '] do
        if c == '<' then inHex := true
        else if c == '>' then inHex := false
        else if !inHex then
          if c.isDigit || c == '-' then cur := cur.push c
          else
            if !cur.isEmpty then
              if let some n := cur.toInt? then nums := n :: nums
              cur := ""
    return (nums, emptyArrays)
  let wide : Layout.Geom := { pageW := Dim.pt 1200, hmargin := Dim.pt 20 }
  let (gapDoc, _) := Elab.run "t" "a\\hfill b\n\n\\underline{x}"
  let gapText := asciiText (Pdf.write wide oneFace (Layout.run wide oneFace none gapDoc).pages)
  let (adjs, empties) := tjNumbers gapText
  t "pdf never writes a TJ adjustment past sixteen bits"
    (adjs.all fun n => n.natAbs ≤ 32767)
  t "pdf writes no glyphless TJ array" (empties == 0)
  -- Three pen placements: the first line, `b` across the fill, the second
  -- line; the underline's rule-only sibling line places nothing.
  t "pdf moves the pen across a wide gap with Tm" ((gapText.splitOn " Tm\n").length == 4)

/-- Faces and sizes have to survive into the content stream, and only the
bytes can say so: a regression once embedded one face where six belonged
while every other test still passed. Its own function: `main`'s do block
has no elaboration budget left. -/
def pdfFaceChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font.Font) : IO Unit := do
  let t := check ref
  let twoFace : Font.FontSet := {
    fonts := #[font, font]
    index := ((List.range 3).flatMap fun slot =>
      let idx := if slot == 1 then 1 else 0
      [((slot, false, false), idx), ((slot, true, false), idx),
       ((slot, false, true), idx), ((slot, true, true), idx)]).toArray
  }
  let (bigDoc, bigDs) := Elab.run "t"
    "plain {\\sffamily other face} and {\\Huge big} and {\\small little}"
  t "size scale source clean" bigDs.isEmpty
  let bigPdf := Pdf.write geom twoFace (Layout.run geom twoFace none bigDoc).pages
  t "pdf references a second face" (bytesContain bigPdf "/F2 ")
  t "pdf sets Huge at 2.488x" (bytesContain bigPdf "24.88 Tf")
  t "pdf sets small at 0.9x" (bytesContain bigPdf "9 Tf")
  t "pdf keeps the body size" (bytesContain bigPdf "10 Tf")
  -- One face only: nothing unused is embedded, so no /F2 exists.
  let plainPdf := Pdf.write geom oneFace (Layout.run geom oneFace none bigDoc).pages
  t "pdf embeds no unused face" (!bytesContain plainPdf "/F2 ")
  -- The descriptor states the parsed metrics (ISO 32000-2 §9.8.1:
  -- CapHeight is the cap height), never a stand-in: the fixture face
  -- declares a cap height under its ascent, so the old CapHeight := ascent
  -- is distinguishable and must stay dead.
  let cap1000 := font.capHeight * 1000 / (font.unitsPerEm : Int)
  let asc1000 := font.ascent * 1000 / (font.unitsPerEm : Int)
  t "pdf descriptor CapHeight is the face's own, not the ascent"
    (cap1000 != asc1000 && bytesContain plainPdf s!"/CapHeight {cap1000}" &&
     !bytesContain plainPdf s!"/CapHeight {asc1000}")
  pdfStreamChecks ref oneFace

def rawPayloadChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Browsers match end tags ASCII-case-insensitively, so the terminator guard
  -- must too; the lowercase spelling is pinned beside the printers' tests,
  -- these pin the case variants in both printers.
  t "html style payload cannot close its own tag in upper case"
    (((Html.render (Html.Node.style "x</STYLE>bad") 0).splitOn "</STYLE").length == 1)
  t "html style payload cannot close its own tag in mixed case inline"
    (((Html.render (Html.elem "p" #[Html.Node.style "x</Style>bad"]) 0).splitOn
      "</Style").length == 1)
  t "html script payload cannot close its own tag in upper case inline"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</SCRIPT>bad"]) 0).splitOn
      "</SCRIPT").length == 1)
  -- The terminator literal omits the closing `>`, which is what catches a
  -- spaced or self-closed end tag; pinned so the case fix cannot regress it.
  t "html script payload with a spaced terminator is removed"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</script >bad"]) 0).splitOn
      "/* removed */").length == 2)

/-- The pre-commit gate's own predicates, exercised through the script's
`--selftest` mode: a gate that does not catch the shape it commemorates
grants false confidence. -/
def precommitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let out ← IO.Process.output
    { cmd := "lean", args := #["--run", "scripts/precommit.lean", "--selftest"] }
  check ref s!"precommit selftest:\n{out.stderr}" (out.exitCode == 0)
  let owed ← IO.Process.output
    { cmd := "lean", args := #["--run", "scripts/owed.lean", "--selftest"] }
  check ref s!"owed selftest:\n{owed.stderr}" (owed.exitCode == 0)

/-- The cross-backend agreement tier, over every golden fixture: a declared
fact both backends render — a footer's slot contents and their sides, a
list item's marker — renders the same from `Layout.Out` and from the typed
HTML tree, or a diagnostic names the divergence (W0007 physical furniture
omitted, W0331 marker substituted, W0332 sequences mixed). This is the
general form of FINDINGS F1 and F5: the next divergence in any fixture
fails here without anyone looking at a page. -/
def agreeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let namingCodes := ["W0007", "W0331", "W0332"]
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, docDs) := Elab.run s!"{n}.tex" src
    let geom := Layout.Geom.ofPage doc.page
    let out := Layout.run geom oneFace (some pats) doc
    let (_, body, htmlDs) := HtmlDoc.emitTree {} doc
    let naming := (docDs ++ out.diags ++ htmlDs).any (namingCodes.contains ·.code)
    let pdf := dedupConsecutive (pdfFoots out)
    let html := slideFootsList #[] body.toList
    check ref s!"agree {n}: footer slots match across backends, or are named"
      (pdf == html || naming)
    for (element, st) in doc.styles.entries do
      if let some m := st.marker then
        match HtmlDoc.markerCss? m with
        | some r =>
          -- The expressible marker shows the declared characters — the
          -- executable face of `markerCss?_text`, judged per fixture.
          check ref s!"agree {n}: the '{element}' marker's HTML text is the declared text"
            (r.text == Ir.plainText m)
        | none =>
          check ref s!"agree {n}: the '{element}' marker's substitution is named"
            (htmlDs.any (·.code == "W0331"))


/- One diagnostic code, one meaning: `DiagCode` in Diag.lean is the single
place a code lives — an unregistered code is unrepresentable, because every
emission site passes a constructor, and a new code is forced through the
`DiagCode.spec` match, where a collision with an existing number is visible
before it ships. The defect class is real twice over: the card slice nearly
renumbered W0315 over the contrast pairing (PLAN 2026-09-17), and the old
string registry's first run found W0314 meaning both a column width and an
unknown theme. What is left to check at runtime: the spec's code strings are
unique (a constructor cannot claim another's number), each carries a
meaning, and no constructor outlives its last emission site. -/

def renderChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- render: porcelain is stable, escaped JSONL
  let d : Diag := Diag.of .E0002 "bad \"quote\"\nline" (some ⟨"a.tex", ⟨3, 7⟩⟩)
    (help := "fix it")
  t "porcelain diag" (Render.porcelainDiag d ==
    "{\"event\":\"diagnostic\",\"severity\":\"error\",\"code\":\"E0002\"," ++
    "\"message\":\"bad \\\"quote\\\"\\nline\",\"file\":\"a.tex\",\"line\":3,\"col\":7," ++
    "\"help\":\"fix it\"}")
  t "porcelain summary" (Render.porcelainSummary "a.tex" false 2 17 ==
    "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":2,\"ms\":17}")

  -- render: human, no color
  t "human diag plain" (Render.human false d ==
    "error[E0002]: bad \"quote\"\nline\n  --> a.tex:3:7\n  help: fix it")

def linkHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- links, running content, and block-producing user commands
  let (linkDoc, linkDs) := elabStr "\\href{https://example.org}{text}"
  t "href source clean" linkDs.isEmpty
  t "href wraps body" (linkDoc.body ==
    #[.para #[.link "https://example.org" #[.text "text"]]])
  let (bareDoc, bareDs) := elabStr "\\href{https://example.org}"
  t "href bare prints its url" (bareDs.isEmpty && bareDoc.body ==
    #[.para #[.link "https://example.org" #[.text "https://example.org"]]])
  let runSrc := "\\documentclass{article}\n" ++
    "\\runninghead{Title \\hfill \\pagenumber}\n" ++
    "\\runningfoot{page \\pagenumber\\ of \\pagecount}\n" ++
    "\\begin{document}x\\end{document}"
  let (runDoc, runDs) := elabStr runSrc
  t "running content clean" runDs.isEmpty
  t "running head parsed" (runDoc.head.isSome && runDoc.foot.isSome)
  t "running head has a page number"
    ((runDoc.head.getD #[]).any fun x => x == .pageNumber)
  let blockMacro := "\\documentclass{article}\n" ++
    "\\define \\entry(a: text) {\\block[before = 3pt]{\\textbf{\\a}}}\n" ++
    "\\begin{document}\\entry{One}\\entry{Two}\\end{document}"
  let (bmDoc, bmDs) := elabStr blockMacro
  t "block-producing macro clean" bmDs.isEmpty
  t "block-producing macro yields blocks" (bmDoc.body.size == 2 &&
    bmDoc.body.all fun b => match b with
      | .role "entry" body => body.all fun inner => match inner with
        | .spaced _ _ => true
        | _ => false
      | _ => false)
  -- An inline-only macro must stay inline, or it would split the paragraph.
  let inlineMacro := "\\documentclass{article}\n" ++
    "\\define \\who(a: text) {\\textbf{\\a}}\n" ++
    "\\begin{document}\\who{Ada} wrote it\\end{document}"
  let (imDoc, _) := elabStr inlineMacro
  t "inline macro does not split the paragraph" (imDoc.body.size == 1)

  -- HTML backend
  let escaped := Html.escapeText "a <script> & \"x\""
  t "html escapes text" (escaped == "a &lt;script&gt; &amp; \"x\"")
  t "html escapes attributes" (Html.escapeAttr "a\"b<c" == "a&quot;b&lt;c")
  t "html void element has no closing tag"
    (Html.render (Html.elem "br" #[]) 0 == "<br>\n")
  t "html phrasing content stays on one line"
    (Html.render (Html.elem "p" #[Html.text "a ", Html.elem "em" #[Html.text "b"],
      Html.text ", c"]) 0 == "<p>a <em>b</em>, c</p>\n")
  t "html style payload cannot close its own tag"
    (((Html.render (Html.Node.style "x</style>bad") 0).splitOn "</style>").length == 2)
  -- The same contract inside a phrasing parent, where rendering goes through
  -- the inline printer instead.
  t "html style payload cannot close its own tag inline"
    (((Html.render (Html.elem "p" #[Html.Node.style "x</style>bad"]) 0).splitOn
      "</style>").length == 2)
  t "html script payload cannot close its own tag inline"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</script>bad"]) 0).splitOn
      "</script>").length == 2)
  rawPayloadChecks ref
  precommitChecks ref

  let (htmlDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ primary = #7C3AED }\n" ++
    "\\pdfmeta{ title = \"T\" }\n" ++
    "\\begin{document}\n" ++
    "\\section{Head}\n" ++
    "A \\textbf{bold} word, \\textcolor{primary}{coloured}, and a " ++
    "\\href{https://example.org}{link}.\n\n" ++
    "\\begin{itemize}\\item One\\end{itemize}\n" ++
    "\\end{document}")
  let (page, pageDiags) := HtmlDoc.emit {} htmlDoc
  t "html emit clean" pageDiags.isEmpty
  t "html has doctype" (page.startsWith "<!DOCTYPE html>")
  t "html sets the title" ((page.splitOn "<title>T</title>").length == 2)
  t "html section becomes h2" ((page.splitOn "<h2>Head</h2>").length == 2)
  t "html bold becomes strong" ((page.splitOn "<strong>bold</strong>").length == 2)
  t "html colour references the token"
    ((page.splitOn "var(--primary, #7c3aed)").length == 2)
  t "html link has href"
    ((page.splitOn
      "<a href=\"https://example.org\" style=\"color: inherit\">link</a>").length == 2)
  t "html single-para item is not wrapped"
    ((page.splitOn "<li>One</li>").length == 2)
  t "html inlines the stylesheet" ((page.splitOn "<style>").length == 2)
  t "html declares the generator" ((page.splitOn "content=\"leantex\"").length == 2)

  -- Running content is paged furniture: HTML says so rather than dropping it.
  let (_, runHtmlDiags) := HtmlDoc.emit {} runDoc
  t "html warns about running content" (runHtmlDiags.any (·.code == "W0007"))

  -- Bulma interop binds our tokens to the framework's own properties.
  let (bulmaPage, _) := HtmlDoc.emit { css := .bulma } htmlDoc
  t "bulma mode binds primary" ((bulmaPage.splitOn "--bulma-primary").length == 2)
  t "bulma mode ships no base sheet" ((bulmaPage.splitOn "--measure").length == 1)
  let (barePage, _) := HtmlDoc.emit { css := .none } htmlDoc
  t "css none emits no style element" ((barePage.splitOn "<style>").length == 1)

  -- A stretched row broken by `\\` becomes a column of rows. A <br> cannot end
  -- a layout row, so the break has to be structural or the second line lands
  -- beside the first -- where the PDF puts it below.
  let (rowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\\\second\\end{document}")
  let (rowPage, _) := HtmlDoc.emit {} rowDoc
  t "broken stretched row becomes rows"
    ((rowPage.splitOn "<span class=\"entry-row").length == 3)
  t "broken stretched row keeps no br" ((rowPage.splitOn "<br>").length == 1)
  -- An unbroken one stays a single row.
  let (oneRowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\end{document}")
  t "unbroken stretched row stays one row"
    (((HtmlDoc.emit {} oneRowDoc).1.splitOn "class=\"entry entry-pair\"").length == 2)

  -- \hfill and control-symbol spaces
  -- \hfill takes no argument but still swallows the following space: a space
  -- after the stretch would be visible at the far margin.
  let (fillDoc, fillDs) := elabStr "a \\hfill b"
  t "hfill source clean" fillDs.isEmpty
  t "hfill becomes an inline fill" (fillDoc.body ==
    #[.para #[.text "a ", .fill, .text "b"]])
  t "thin space escape" ((elabStr "a\\,b").1.body ==
    #[.para #[.text "a b"]])

/-- Images: the decoders' verdicts over synthetic bytes and the shipped
fixtures, the sizing contract on placed pages, the placeholder path, the PDF
embedding, and the HTML emit. Decoder totality over truncations and random
bytes is fuzzed deeper in `scripts/img-fuzz.lean` (an oracle, not a
theorem). -/
def imageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Synthetic PNGs, byte by byte. The decoder reads structure, not CRCs or
  -- pixel data, so the CRC slots are zero and the IDAT payload arbitrary.
  let be32 (n : Nat) : List UInt8 :=
    [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
     UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]
  let chunk (tag : String) (data : List UInt8) : List UInt8 :=
    be32 data.length ++ (tag.toList.map fun c => UInt8.ofNat c.toNat) ++ data ++
      [0, 0, 0, 0]
  let ihdr (w h bd ct interlace : Nat) : List UInt8 :=
    be32 w ++ be32 h ++ [UInt8.ofNat bd, UInt8.ofNat ct, 0, 0, UInt8.ofNat interlace]
  let pngSig : List UInt8 := [137, 80, 78, 71, 13, 10, 26, 10]
  let mkPng (chunks : List UInt8) : ByteArray := bytes (pngSig ++ chunks)
  let plain := mkPng (chunk "IHDR" (ihdr 64 40 8 2 0) ++ chunk "IDAT" [1, 2, 3] ++
    chunk "IEND" [])
  match Image.decodePng plain with
  | .error e => failures ref s!"png decode: {e}"
  | .ok inf =>
    t "png dimensions" (inf.pxW == 64 && inf.pxH == 40)
    t "png default density is one pixel per point"
      (inf.dpiX == 72 && inf.width == Dim.pt 64 && inf.height == Dim.pt 40)
    t "png space and depth" (inf.space == .rgb && inf.bitDepth == 8)
    t "png idat survives" (inf.data == bytes [1, 2, 3])
  -- pHYs at 5906 pixels per metre is 150 dpi to the spec's own rounding.
  let physed := mkPng (chunk "IHDR" (ihdr 64 40 8 2 0) ++
    chunk "pHYs" (be32 5906 ++ be32 5906 ++ [1]) ++ chunk "IDAT" [0] ++ chunk "IEND" [])
  t "png pHYs density read"
    (match Image.decodePng physed with
     | .ok inf => inf.dpiX == 150 && inf.width == Dim.pt 64 * 72 / 150
     | .error _ => false)
  -- Refusals and the decode path, each with its reason: 16-bit alpha and
  -- interlace refuse; 8-bit alpha really decodes — inflate, unfilter,
  -- split — and the alpha plane comes back as an SMask.
  t "png 16-bit alpha refused"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 16 6 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "16-bit").length == 2
     | .ok _ => false)
  -- 2×2 RGBA, row 0 filter None, row 1 filter Sub: known planes out.
  let rgbaRaw := bytes ([0, 10, 20, 30, 255, 40, 50, 60, 128] ++
    [1, 5, 5, 5, 7, 1, 2, 3, 9])
  let rgbaPng := mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++
    chunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ chunk "IEND" [])
  t "png alpha decodes to colour plus smask"
    (match Image.decodePng rgbaPng with
     | .ok inf =>
       inf.space == .rgb && !inf.predictor && !inf.smask.isEmpty &&
       Flate.inflate inf.data 12 ==
         .ok (bytes [10, 20, 30, 40, 50, 60, 5, 5, 5, 6, 7, 8]) &&
       Flate.inflate inf.smask 4 == .ok (bytes [255, 128, 7, 16])
     | .error _ => false)
  -- The inflate under it round-trips its own stored encoder, and reads a
  -- real compressor's stream: rects.png's IDAT is zlib at level 9, and its
  -- unfiltered scanlines are 40 rows of 1+192 bytes.
  t "flate roundtrip on stored blocks"
    (Flate.inflate (Flate.deflateStored rgbaRaw) rgbaRaw.size == .ok rgbaRaw)
  t "png interlace refused"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 2 1) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "interlaced").length == 2
     | .ok _ => false)
  t "png indexed without PLTE refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png indexed with PLTE carries the palette"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "PLTE" [0, 0, 0, 255, 255, 255] ++ chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .ok inf => inf.space == .indexed && inf.palette.size == 6
     | .error _ => false)
  t "png zero size refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 0 8 8 2 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png lying chunk length refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 2 0) ++
      be32 99999 ++ ("IDAT".toList.map fun c => UInt8.ofNat c.toNat) ++ [0]))).isOk
      == false)
  -- A synthetic JPEG: SOI, JFIF APP0 declaring 144 dpi, SOF0 10×20 in three
  -- components, SOS. The scan data never has to exist for the header walk.
  let jfif (unit dx dy : Nat) : List UInt8 :=
    [0xFF, 0xE0, 0, 16, 0x4A, 0x46, 0x49, 0x46, 0, 1, 1, UInt8.ofNat unit,
     UInt8.ofNat (dx / 256), UInt8.ofNat (dx % 256),
     UInt8.ofNat (dy / 256), UInt8.ofNat (dy % 256), 0, 0]
  let sof0 (w h ncomp : Nat) : List UInt8 :=
    [0xFF, 0xC0, 0, UInt8.ofNat (8 + 3 * ncomp), 8,
     UInt8.ofNat (h / 256), UInt8.ofNat (h % 256),
     UInt8.ofNat (w / 256), UInt8.ofNat (w % 256), UInt8.ofNat ncomp] ++
     (List.range ncomp).flatMap fun k => [UInt8.ofNat (k + 1), 0x11, 0]
  let jpg := bytes ([0xFF, 0xD8] ++ jfif 1 144 144 ++ sof0 10 20 3 ++ [0xFF, 0xDA])
  match Image.decodeJpeg jpg with
  | .error e => failures ref s!"jpeg decode: {e}"
  | .ok inf =>
    t "jpeg dimensions" (inf.pxW == 10 && inf.pxH == 20)
    t "jpeg jfif density read" (inf.dpiX == 144 && inf.width == Dim.pt 10 * 72 / 144)
    t "jpeg embeds whole" (inf.data.size == jpg.size)
  t "jpeg cmyk refused"
    (match Image.decodeJpeg (bytes ([0xFF, 0xD8] ++ sof0 4 4 4 ++ [0xFF, 0xDA])) with
     | .error e => (e.splitOn "CMYK").length == 2
     | .ok _ => false)
  t "jpeg aspect-only density keeps the default"
    (match Image.decodeJpeg (bytes ([0xFF, 0xD8] ++ jfif 0 1 1 ++ sof0 4 4 1 ++
      [0xFF, 0xDA])) with
     | .ok inf => inf.dpiX == 72 && inf.space == .gray
     | .error _ => false)
  t "decode rejects foreign bytes" ((Image.decode (bytes [0, 1, 2, 3])).isOk == false)
  t "decode rejects empty" ((Image.decode (bytes [])).isOk == false)

  -- The shipped fixtures: what `lake test` sees on every host.
  let pngData ← IO.FS.readBinFile "tests/corpus/rects.png"
  let jpgData ← IO.FS.readBinFile "tests/corpus/rects.jpg"
  let alphaData ← IO.FS.readBinFile "tests/corpus/rects-alpha.png"
  let pngInfo := Image.decode pngData
  let jpgInfo := Image.decode jpgData
  let alphaInfo := Image.decode alphaData
  t "shipped png decodes 64x40 rgb"
    (match pngInfo with
     | .ok inf => inf.format == .png && inf.pxW == 64 && inf.pxH == 40 &&
        inf.space == .rgb && inf.width == Dim.pt 64
     | .error _ => false)
  t "shipped jpeg decodes 64x40"
    (match jpgInfo with
     | .ok inf => inf.format == .jpeg && inf.pxW == 64 && inf.pxH == 40 &&
        inf.width == Dim.pt 64
     | .error _ => false)
  -- The RGBA fixture went through a real compressor (zlib level 9), so
  -- decoding it exercises the Huffman paths of the inflater; its alpha
  -- fades 255 down to 15 across the rectangle and vanishes outside it.
  t "shipped alpha png decodes with its mask"
    (match alphaInfo with
     | .ok inf =>
       inf.pxW == 48 && inf.pxH == 32 && inf.space == .rgb && !inf.smask.isEmpty &&
       (match Flate.inflate inf.smask (48 * 32) with
        | .ok mask => mask.size == 48 * 32 && mask[0]?.getD 1 == 0 &&
            (mask[4 * 48 + 4]?.getD 0) == 255 && (mask[4 * 48 + 43]?.getD 0) == 21
        | .error _ => false)
     | .error _ => false)
  -- Totality over truncations of both, as for fonts: reaching the count is
  -- the property — a panic would take the run down.
  t "png decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (pngData.extract 0 (pngData.size * k / 64))).isOk).length == 64)
  t "jpeg decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (jpgData.extract 0 (jpgData.size * k / 64))).isOk).length == 64)

  let store : Image.Store := { entries := #[
    { src := "rects.png", info := pngInfo.toOption },
    { src := "rects.jpg", info := jpgInfo.toOption },
    { src := "rects-alpha.png", info := alphaInfo.toOption }] }
  let geom : Layout.Geom := {}
  let imageSegs (out : Layout.Out) : Array (Option Nat × Dim.Sp × Dim.Sp) := Id.run do
    let mut acc : Array (Option Nat × Dim.Sp × Dim.Sp) := #[]
    for p in out.pages do
      for l in p.lines do
        for s in l.segs do
          if let .image idx w h := s then acc := acc.push (idx, w, h)
    return acc
  let layoutOf (src : String) : Layout.Out :=
    let (doc, _) := Elab.run "t" src
    Layout.run geom oneFace none doc store

  -- Intrinsic: no keys, the box is the file's physical size.
  let outIntrinsic := layoutOf "\\includegraphics{rects.png}"
  t "layout intrinsic size"
    (imageSegs outIntrinsic == #[(some 0, Dim.pt 64, Dim.pt 40)])
  -- `width = 0.8\textwidth`: the spelling every deck sizes a figure with.
  let outTw := layoutOf "\\includegraphics[width=0.8\\textwidth]{rects.png}"
  let expectW := geom.textWidth * 800 / 1000
  t "layout width fraction of the measure"
    (imageSegs outTw == #[(some 0, expectW, expectW * Dim.pt 40 / Dim.pt 64)])
  -- Both dimensions declared win exactly.
  let outBoth := layoutOf "\\includegraphics[width=32pt, height=40pt]{rects.png}"
  t "layout declared size wins"
    (imageSegs outBoth == #[(some 0, Dim.pt 32, Dim.pt 40)])
  -- keepaspectratio fits inside the declared box: width binds (the image is
  -- wider than tall), the height follows the intrinsic ratio.
  let outKeep :=
    layoutOf "\\includegraphics[width=32pt, height=32pt, keepaspectratio]{rects.jpg}"
  t "layout keepaspect fits the box"
    (imageSegs outKeep == #[(some 1, Dim.pt 32, Dim.pt 32 * 40 / 64)])
  -- A source the store has no entry for is a placeholder box: the document
  -- still compiles, at the requested size.
  let outMissing := layoutOf "\\includegraphics[width=50pt]{missing.png}"
  t "layout missing image keeps requested width"
    (imageSegs outMissing == #[(none, Dim.pt 50, Dim.pt 50)] &&
     outMissing.pages.size == 1)
  t "layout missing image without a size is an inch square"
    (imageSegs (layoutOf "\\includegraphics{missing.png}") ==
      #[(none, Dim.inch 1, Dim.inch 1)])

  -- The figure environment: a float standing where written, the caption on
  -- its source side (below here) and the alt of the image it captions.
  let (figDoc, figDiags) := Elab.run "t"
    "\\begin{figure}[t]\\centering\\includegraphics{rects.png}\\caption{A mark}\\end{figure}"
  t "figure elaborates with its placement registered as a note"
    (figDiags.all (·.severity == .note) && figDiags.any (·.code == "N0102"))
  t "figure elaborates to a float carrying its caption"
    (match figDoc.body.toList with
     | [.float .figure _ false inner cap] =>
       match inner.toList with
       | [.para xs] =>
         (xs.any fun x => match x with
           | .image "rects.png" _ alt => alt == "A mark"
           | _ => false) &&
         Ir.plainText cap == "A mark"
       | _ => false
     | _ => false)
  t "figure image reaches the page"
    ((imageSegs (Layout.run geom oneFace none figDoc store)).size == 1)
  -- An image in a slide: the frame's page carries it.
  let (slideDoc, _) := Elab.run "t"
    "\\documentclass{slides}\\begin{document}\\begin{frame}{T}\\includegraphics{rects.png}\\end{frame}\\end{document}"
  let slideGeom := Layout.Geom.ofPage slideDoc.page
  t "slide image reaches the frame page"
    ((imageSegs (Layout.run slideGeom oneFace none slideDoc store)).size == 1)
  -- The deck logo: same image node, placed at the lower-right corner of
  -- every page, its right edge on the margin.
  let (logoDoc, logoDiags) := Elab.run "t"
    "\\documentclass{slides}\\logo{\\includegraphics[height=8pt]{rects.png}}\
\\begin{document}\\begin{frame}{A}x\\end{frame}\\begin{frame}{B}y\\end{frame}\\end{document}"
  t "logo declaration elaborates clean" (logoDiags.isEmpty)
  let logoGeom := Layout.Geom.ofPage logoDoc.page
  let logoOut := Layout.run logoGeom oneFace none logoDoc store
  let logoW := Dim.pt 8 * Dim.pt 64 / Dim.pt 40
  t "logo placed on every page at the right margin"
    (logoOut.pages.size == 2 && logoOut.pages.all fun p =>
      p.lines.any fun l =>
        l.x + l.setWidth == logoGeom.pageW - logoGeom.hmargin &&
        l.segs.any fun s => match s with
          | .image _ w h => w == logoW && h == Dim.pt 8
          | _ => false)

  -- The PDF: an XObject per used image, painted by a cm+Do pair; the xref
  -- theorem-test still holds with the new objects in the file.
  let (pdfDoc, _) := Elab.run "t"
    "\\includegraphics{rects.png} and \\includegraphics{rects.jpg} and \
\\includegraphics{rects-alpha.png}"
  let pdfOut := Layout.run geom oneFace none pdfDoc store
  let pdf := Pdf.write geom oneFace pdfOut.pages {} store
  t "pdf embeds the png as flate with the predictor"
    (bytesContain pdf "/Subtype /Image" && bytesContain pdf "/FlateDecode" &&
     bytesContain pdf "/Predictor 15")
  t "pdf embeds the jpeg as dct" (bytesContain pdf "/DCTDecode")
  t "pdf gives the alpha image a soft mask" (bytesContain pdf "/SMask")
  t "pdf paints all three images" (bytesContain pdf "/Im1 Do" &&
    bytesContain pdf "/Im2 Do" && bytesContain pdf "/Im3 Do")
  -- The cm matrix must carry the placed size: a Do behind a degenerate
  -- matrix is a blank box that every structural check would miss.
  t "pdf image matrix carries the placed size"
    (bytesContain pdf "q 64 0 0 40 ")
  t "pdf page resources name the xobjects" (bytesContain pdf "/XObject <<")
  match checkXref pdf with
  | .ok n => t "pdf xref valid with images" (n > 0)
  | .error e => failures ref s!"pdf xref with images: {e}"
  -- The raw IDAT bytes must reach the file unchanged: the stream is the
  -- pass-through, not a re-encoding.
  let containsBytes (hay needle : ByteArray) : Bool := Id.run do
    if needle.size == 0 || hay.size < needle.size then return false
    for i in [0:hay.size - needle.size + 1] do
      let mut ok := true
      for j in [0:needle.size] do
        if hay[i + j]! != needle[j]! then
          ok := false
          break
      if ok then return true
    return false
  t "pdf carries the png stream verbatim"
    (match pngInfo with
     | .ok inf => containsBytes pdf inf.data
     | .error _ => false)
  -- The placeholder: an outlined box, no image object, a valid file.
  let missOut := Layout.run geom oneFace none
    ((Elab.run "t" "\\includegraphics[width=50pt]{missing.png}").1) store
  let missPdf := Pdf.write geom oneFace missOut.pages {} store
  t "pdf placeholder draws an outline, embeds nothing"
    (bytesContain missPdf "re S" && !(bytesContain missPdf "/Subtype /Image"))
  match checkXref missPdf with
  | .ok _ => pure ()
  | .error e => failures ref s!"pdf xref with placeholder: {e}"

  -- The HTML: an <img> through the typed tree, intrinsic pixel size as
  -- attributes so the page never reflows, the caption as alt, the requested
  -- fraction as a percentage.
  let hcfg : HtmlDoc.Config := { imgs := store }
  let (figHtml, _) := HtmlDoc.emit hcfg figDoc
  t "html figure image with alt and intrinsic size"
    ((figHtml.splitOn "<img src=\"rects.png\" alt=\"A mark\" width=\"64\" height=\"40\">").length == 2)
  let (twDoc, _) := Elab.run "t" "\\includegraphics[width=0.8\\textwidth]{rects.png}"
  let (twHtml, _) := HtmlDoc.emit hcfg twDoc
  t "html width fraction becomes a percentage"
    ((twHtml.splitOn "style=\"width: 80%; height: auto\"").length == 2)
  let (missHtml, _) := HtmlDoc.emit hcfg
    ((Elab.run "t" "\\includegraphics{missing.png}").1)
  t "html missing image still emits the img with alt"
    ((missHtml.splitOn "<img src=\"missing.png\"").length == 2)

  -- The surface diagnostics: a length that does not parse, an option the
  -- engine does not model.
  t "includegraphics bad length is E0331"
    (errCodes "\\includegraphics[width=banana]{x.png}" == ["E0331"])
  t "includegraphics em length is E0331"
    (errCodes "\\includegraphics[width=2em]{x.png}" == ["E0331"])
  t "includegraphics unknown option warns W0110"
    (warnCodes "\\includegraphics[angle=45]{x.png}" == ["W0110"])
  t "includegraphics without a file group is E0304"
    (errCodes "\\includegraphics[width=3cm]" == ["E0304"])
  -- totalheight is height plus depth and an image has no depth: one key.
  t "includegraphics totalheight is height"
    (match (elabStr "\\includegraphics[totalheight=8pt]{x.png}").1.body.toList with
     | [.para xs] => xs.any fun x => match x with
        | .image _ spec _ => spec.height == some { sp := Dim.pt 8 }
        | _ => false
     | _ => false)
  -- \logo is a declaration in the body too, and it is stateful there, as
  -- in beamer: a deck scopes a logo to one frame with `\logo{...}` before
  -- it and `\logo{}` after.
  let (bodyLogoDoc, bodyLogoDiags) := Elab.run "t"
    "\\documentclass{slides}\\begin{document}\\logo{\\includegraphics[height=8pt]{rects.png}}\
\\begin{frame}{A}x\\end{frame}\\logo{}\\begin{frame}{B}y\\end{frame}\\end{document}"
  t "logo declared in the body binds" (bodyLogoDiags.isEmpty && bodyLogoDoc.logo.isNone)
  let blOut := Layout.run (Layout.Geom.ofPage bodyLogoDoc.page) oneFace none
    bodyLogoDoc store
  let pageHasImage (p : Layout.PageOut) : Bool :=
    p.lines.any fun l => l.segs.any fun s => match s with
      | .image .. => true
      | _ => false
  t "body logo scopes to its frame's page"
    (blOut.pages.size == 2 && pageHasImage blOut.pages[0]! &&
     !pageHasImage blOut.pages[1]!)
  -- A bare graphicx name gains the extension the file on disk has; the
  -- candidate order tries the name as written first.
  t "source candidates try the written name first"
    ((Image.sourceCandidates "figures/plot").take 2 ==
      ["figures/plot", "figures/plot.png"])
  t "html names the resolved file, not the bare spelling"
    (let store2 : Image.Store := { entries := #[
      { src := "figures/plot", href := "figures/plot.png", info := pngInfo.toOption }] }
     let (h, _) := HtmlDoc.emit { imgs := store2 }
       ((Elab.run "t" "\\includegraphics{figures/plot}").1)
     (h.splitOn "<img src=\"figures/plot.png\"").length == 2)

