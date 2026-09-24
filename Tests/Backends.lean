import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The first elaborated formula in a document's paragraphs, equations,
and centred display blocks (a display alignment sets under `.center`):
enough reach for the one-formula snippets below. -/
def blockFormula (b : Ir.Block) : Option Math.MList :=
  let inls := match b with
    | .para content => content
    | .equation _ content => content
    | _ => #[]
  inls.findSome? fun x => match x with
    | .formula _ _ body => some body
    | _ => none

def firstFormula (d : Ir.Doc) : Option Math.MList :=
  d.body.findSome? fun b => match b with
    | .center bs => bs.findSome? blockFormula
    | b => blockFormula b

/-- Math in HTML is MathML Core from the parsed atoms — one row per
construct, judged on the emitted page. The shapes cite MathML Core (W3C CR
2025-06-24): scripts (§3.4.1 child order base, sub, sup), limits in
display (§3.4.2), fractions and radicals (§3.3.2–3.3.3), stretchy
delimiters (§3.2.4.2), accents (§3.4.2.4) with the U+0305 overline as the
dictionary's stretchy U+203E, alignments as `mtable` with CSS cell
alignment (§3.5.3) and restored `displaystyle` (§2.1.6), spaces as
`mspace` (§3.2.5). The census half: per formula, every scalar the PDF's
coverage census asks (`Math.MList.scalarsList`) appears in the MathML leaf
text and everything in the leaf text is a census scalar or the overline
operator — the executable relation `mathml_glyphs_agree`'s docstring
promises, the U+0305 rule-drawn accent being the one stated exception. -/
def mathmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let page (body : String) : String :=
    (HtmlDoc.emit {} (elabStr (dvDoc "" body)).1).1
  let has (body frag : String) : Bool :=
    ((page body).splitOn frag).length ≥ 2
  -- One row per construct: the MathML shape on the page.
  t "inline math is an inline math element"
    (has "$x$" "<math class=\"math\" data-tex=\"x\"><mi mathvariant=\"normal\">𝑥</mi></math>")
  t "display math is a block math element with the display class"
    (has "\\[ x \\]" "<math display=\"block\" class=\"math math-display\"")
  t "a superscript is msup with an mrow script"
    (has "$x^2$" "<msup><mi mathvariant=\"normal\">𝑥</mi><mrow><mn>2</mn></mrow></msup>")
  t "a stacked pair is msubsup in base, sub, sup order"
    (has "$a_i^2$"
      "<msubsup><mi mathvariant=\"normal\">𝑎</mi><mrow><mi mathvariant=\"normal\">𝑖</mi></mrow><mrow><mn>2</mn></mrow></msubsup>")
  t "a fraction is mfrac with two mrow children"
    (has "$\\frac{1}{2}$" "<mfrac><mrow><mn>1</mn></mrow><mrow><mn>2</mn></mrow></mfrac>")
  t "a square root is msqrt"
    (has "$\\sqrt{x}$" "<msqrt><mi mathvariant=\"normal\">𝑥</mi></msqrt>")
  t "an indexed radical is mroot: base then index"
    (has "$\\sqrt[3]{x}$" "<mroot><mrow><mi mathvariant=\"normal\">𝑥</mi></mrow><mrow><mn>3</mn></mrow></mroot>")
  t "a grown pair is stretchy symmetric mo delimiters"
    (has "$\\left( x \\right)$"
      "<mrow><mo stretchy=\"true\" symmetric=\"true\">(</mo><mi mathvariant=\"normal\">𝑥</mi><mo stretchy=\"true\" symmetric=\"true\">)</mo></mrow>")
  t "display limits are munderover: base, under, over"
    (has "\\[ \\sum_{i}^{n} \\]"
      "<munderover><mo>∑</mo><mrow><mi mathvariant=\"normal\">𝑖</mi></mrow><mrow><mi mathvariant=\"normal\">𝑛</mi></mrow></munderover>")
  t "inline limits ride beside as msubsup"
    (has "$\\sum_{i}^{n}$" "<msubsup><mo>∑</mo>")
  t "an accent is mover accent=true, non-stretching for \\hat"
    (has "$\\hat{x}$"
      "<mover accent=\"true\"><mrow><mi mathvariant=\"normal\">𝑥</mi></mrow><mo stretchy=\"false\">̂</mo></mover>")
  t "\\overline is mover accent=false over the stretchy U+203E operator"
    (has "$\\overline{x}$"
      "<mover accent=\"false\"><mrow><mi mathvariant=\"normal\">𝑥</mi></mrow><mo stretchy=\"true\">‾</mo></mover>")
  t "a display alignment is mtable with displaystyle restored"
    (has "\\begin{align*} a &= b \\\\ c &= d \\end{align*}"
      "<mtable displaystyle=\"true\">")
  t "align columns alternate right and left through mtd CSS"
    (has "\\begin{align*} a &= b \\end{align*}"
      "<mtd style=\"text-align: right; text-align: -webkit-right; padding-right: 0\">")
  t "an array takes text style: no displaystyle on its mtable"
    (has "\\[ \\begin{array}{cc} 1 & 2 \\\\ 3 & 4 \\end{array} \\]"
      "<mtable><mtr>")
  t "a numbered display keeps its number beside the math, never inside"
    (let p := page "\\begin{equation} e = mc^2 \\end{equation}"
     let inMath := (((p.splitOn "<math").getD 1 "").splitOn "</math>").headD ""
     ((p.splitOn "class=\"equation display\"").length ≥ 2) &&
       ((p.splitOn "eqnum").length ≥ 2) &&
       ((inMath.splitOn "eqnum").length == 1))
  t "an explicit space is mspace at its mu width"
    (has "$a\\quad b$" "<mspace width=\"1em\">") -- 18 mu is one em
  t "a thin space is three eighteenths of an em"
    (has "$a\\, b$" "<mspace width=\"0.166em\">")
  t "a negative kern declares the zero floor"
    (has "$a\\! b$" "<mspace width=\"0em\">")
  t "a function name is a multi-character upright mi"
    (has "$\\sin x$" "<mi>sin</mi>")
  t "an unparsed construct stays source text with its data-tex hook"
    (let p := page "$\\overset{?}{=}$"
     ((p.splitOn "<span class=\"math\" data-tex=").length ≥ 2))
  -- The HTML half of the recovery floor: the element's visible text is the
  -- floor (`Ir.floorInk_mem`), the source rides only in data-tex where the
  -- opt-in client renderer finds it. The two backends read the one IR
  -- function, so a reader of either artifact is shown content, not markup.
  t "an unparsed construct's element text is its floor, not its source"
    (let p := page "$\\overset{\\textcolor{indigo}{q}}{=}$"
     let inSpan := (((p.splitOn "<span class=\"math\" data-tex=").getD 1 "").splitOn
       "</span>").headD ""
     let shown := ((inSpan.splitOn ">").getD 1 "")
     shown == "q=" && ((inSpan.splitOn "indigo").length ≥ 2))
  -- The census half, over the same construct list plus the alphabets:
  -- MathML leaf text against the PDF's coverage census, per formula.
  let census := ["$x^2$", "$a_i^2$", "$\\frac{1}{2}$", "$\\sqrt[3]{x}$",
    "$\\left( x \\right)$", "$\\sum_{i=1}^{n} i$", "$\\hat{x}$",
    "$\\overline{x+y}$", "$a \\quad b$", "$\\mathbb{R}^d + \\mathcal{L}$",
    "\\begin{align*} a &= b \\\\ c &= d \\end{align*}"]
  for src in census do
    match firstFormula (elabStr (dvDoc "" src)).1 with
    | none => failures ref s!"census: no formula elaborated for {src}"
    | some body =>
      let leaf := MathMl.listChars #[] body
      let pdf := Math.MList.scalarsList #[] body
      t s!"every PDF census scalar reaches the MathML leaf text: {src}"
        (pdf.all leaf.contains)
      t s!"every MathML leaf scalar is a census scalar or the overline: {src}"
        (leaf.all fun c => pdf.contains c || c == MathMl.overlineChar)

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
  -- The font-axis table (fntguide §2.2) generates both spellings: for every
  -- axis value the one-argument command and the declaration elaborate to
  -- the same styled inline. The two lists once disagreed as hand lists —
  -- \scshape was in, \textsc unknown (W0301).
  for (decl, arg, st) in Elab.fontAxes do
    t s!"font axis \\{arg} and \\{decl} agree"
      ((elabStr s!"\\{arg}\{x}").1.body == #[.para #[.styled st #[.text "x"]]] &&
       (elabStr s!"\{\\{decl} x}").1.body == #[.para #[.styled st #[.text "x"]]] &&
       (elabStr s!"\\{arg}\{x}").2.all (·.severity != .warning))
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
  -- A defined role is styleable: its rhythm and format are declared once,
  -- upstream, and the style addresses the class hook the role already
  -- ships (`u-<name>`) — the door a framework-shaped stylesheet uses too.
  let roleStyled := elabStr ("\\documentclass{article}" ++
    "\\define \\entry(a: content) {\\a\\par}" ++
    "\\style{entry}{ before = 2em }" ++
    "\\begin{document}\\entry{x}\\end{document}")
  t "style admits a defined role" (roleStyled.2.all (·.code != "E0328") &&
    ((roleStyled.1.styles.find? "entry").bind (·.before)).map (·.width) ==
      some { em := 2000 })
  t "style before the define is refused, positionally"
    (errCodes ("\\documentclass{article}\\style{entry}{ before = 2em }" ++
      "\\define \\entry(a: content) {\\a\\par}" ++
      "\\begin{document}\\entry{x}\\end{document}") == ["E0328"])
  let (rolePage, _) := HtmlDoc.emit {} roleStyled.1
  t "html role style lands on the class hook"
    ((rolePage.splitOn ".u-entry { margin-top: 2em; }").length == 2)
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
    ((stylePage.splitOn "</span>\u2003<span class=\"size-large\"><span class=\"sans\">").length == 2 &&
     (stylePage.splitOn "<h2 class=\"ruled\"><span class=\"section-number\">").length == 2)
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
  -- A heading rule sits at half the heading's own x-height, as the PDF
  -- draws it (Layout.paraLineGeom): the flex items align by baseline and
  -- the rule element lifts half its own inherited ex.
  let (ruledDoc, _) := elabStr ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink }\\begin{document}\\section{H}\\end{document}")
  t "html heading rule declares the flex baseline anchor"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn
      "h2 { display: flex; align-items: baseline;").length == 2)
  t "html heading rule lifts half the heading's own ex"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn
      "transform: translateY(-0.5ex)").length == 2)
  -- A baseline rule is the flex baseline itself: the empty `::after` box's
  -- synthesised baseline is its bottom border edge (CSS Flexbox §8.5), so
  -- no translate, and its border weight is the declared thickness — the
  -- HTML projection of the one IR fact the PDF raise projects.
  let (baselineDoc, _) := elabStr ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink, rule-position = baseline, rule-thickness = 2pt }" ++
    "\\begin{document}\\section{H}\\end{document}")
  t "html baseline heading rule drops the translate and takes its thickness"
    (((HtmlDoc.emit {} baselineDoc).1.splitOn
      "h2.ruled::after { transform: none; border-top-width: 2pt; }").length == 2)
  t "html x-height heading rule emits no per-element override"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn "h2.ruled::after").length == 1)
  -- Both backends declare the same underline band source — the font's own
  -- post metrics: CSS Text Decoration 4 §2.4.1 and §2.8.2 bind `from-font`
  -- to the face's declared thickness and position, which are what
  -- `Font.band` reads for the PDF. No unsourced offset survives.
  let fromFontPage := (HtmlDoc.emit {} ruledDoc).1
  t "html u and a underline from the font's own band"
    ((fromFontPage.splitOn "text-decoration-thickness: from-font").length == 3 &&
     (fromFontPage.splitOn "text-underline-position: from-font").length == 3 &&
     (fromFontPage.splitOn "text-underline-offset").length == 1)

mutual

/-- The flow's shape as `tag.class` tokens, in document order: every `<p>`
and every element carrying the `display` class, with `>math` when a
`<math>` child stands directly inside — the typed-tree fact a display
formula's block placement is judged on, never the serialized page. -/
def flowShapeOne (acc : Array String) : Html.Node → Array String
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    if tag == "p" || (cls.splitOn " ").contains "display" then
      acc.push (tag ++ "." ++ cls ++
        (if kids.any (fun k => k matches .elem "math" _ _) then ">math" else ""))
    else flowShapeList acc kids.toList

def flowShapeList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => flowShapeList (flowShapeOne acc k) rest

end

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
    ((plainPage.splitOn "p { margin: 0; hyphens: auto; }").length == 2 &&
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
  -- The display formula's block owns both its boundaries through the two
  -- display tokens the PDF walk reads, over the same rhythm row; the
  -- formula element itself carries no margin, so the boundary has one
  -- emitter. Typed-tree half: paragraph, display, paragraph emits the
  -- `.display` element between two `<p>`s, and the numbered equation
  -- joins the same class.
  t "html display skips are the two tokens over the display row"
    ((plainPage.splitOn
      ":where(* + .display) { margin-top: var(--abovedisplayskip, 1.450rem); }").length == 2 &&
     (plainPage.splitOn
      ":where(.display + *) { margin-top: var(--belowdisplayskip, 1.450rem); }").length == 2 &&
     (plainPage.splitOn ".math-display { margin").length == 1)
  let (dispDoc, dispDs) := elabStr
    "\\documentclass{article}\\begin{document}a\n\n\\[ x = 1 \\]\n\nb\n\n\\begin{equation} y \\end{equation}\n\\end{document}"
  let dispPage := (HtmlDoc.emit {} dispDoc).1
  t "html display fixture elaborates clean" dispDs.isEmpty
  let (_, dispBody, _) := HtmlDoc.emitTree {} dispDoc
  t "html display formula is its own .display block between the paragraphs"
    (flowShapeList #[] dispBody.toList ==
      #["p.", "p.display>math", "p.", "div.equation display>math"])
  t "html display page has no centered wrapper around the formula"
    (!hasStr dispPage "class=\"centered\"")
  let (themedDoc, themedDs) := elabStr ("\\documentclass{beamer}\\usetheme{moloch}" ++
    "\\begin{document}\\section{s}\\begin{frame}{t}x\\end{frame}\\end{document}")
  let themedPage := (HtmlDoc.emit {} themedDoc).1
  t "html themed fixture elaborates clean"
    (themedDs.all fun d => d.severity == .note)
  t "html progress height reads the token the PDF reads"
    ((themedPage.splitOn (".progress { background: var(--progressbg, var(--rule));\n" ++
      "  height: var(--progressheight, 1pt);")).length == 2)
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
    body := #[.section 0 false none #[.text "Body Title"], .para #[.text "After."]] }
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
    body := #[.para #[.text "Lead."], .section 0 false none #[.text "Late Title"]] }
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
  -- A `|` in prose is `\|` in the twin — CommonMark §2.4 escapes any ASCII
  -- punctuation — so a table cell containing one keeps its row instead of
  -- splitting it at the pipe.
  let pipe : Ir.Doc := {
    body := #[.table #[default, default] false false
      #[#[#[.text "a|b"], #[.text "c"]]] #[]] }
  t "a cell containing a pipe keeps its row"
    (((MarkdownDoc.emit pipe).splitOn "| a\\|b | c |").length == 2)

/-- One fact, three renderings, at every level: a heading's `#` count and
its `h` number are both projections of the one shared rank,
`Ir.headingRank`, held beside the outline walk it serves (the PDF side
is the census assertion that the title
text ships as furniture). Stated over the two functions the backends
actually run, quantified over the level — the previous form was a `decide`
over the four constants. -/
theorem heading_renderings_agree (level : Nat) :
    HtmlDoc.headingTag level = "h" ++ toString (Ir.headingRank level) ∧
    (MarkdownDoc.headingMarker level).toList =
      List.replicate (Ir.headingRank level) '#' := by
  refine ⟨rfl, ?_⟩
  simp [MarkdownDoc.headingMarker]

/-- The two backends declare one vertical-distribution table: each is a
projection of `Ir.VAlign.shares`, so the agreement is `rfl` at every
alignment — the previous form was a runtime pin over the four constants
in `deckStructureChecks`, a decide-over-constants wearing a test. -/
theorem vdist_shares_agree (v : Ir.VAlign) :
    HtmlDoc.vdistShares v =
      ((Layout.VDist.of v).above, (Layout.VDist.of v).below) := rfl

/-- `{ifbackend}`: content addressed to a subset of the backends. One IR,
elaborated once; each backend keeps or drops through `Ir.keepFor` at its own
entry. The diagnostics, the `orphanFree` correspondence (the hypothesis of
`Ir.keepFor_covers`, checked here on a real elaboration), and each backend's
kept view are pinned. Invented content. Its own function: `main` is one `do`
block and its elaboration budget is spent. -/
def backendChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has := hasStr
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Shared opening.\\begin{ifbackend}{html}Only the page carries this." ++
    "\\end{ifbackend}\\begin{ifbackend}{pdf,md}Print and twin carry this." ++
    "\\end{ifbackend}\\end{document}")
  t "ifbackend source is clean, apart from the note naming each conditional"
    (ds.all (·.severity == .note) &&
     (ds.filter (·.code == "N0019")).size == 2 && ds.size == 2)
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
  let has := hasStr
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#field-notes}{Notes} \\href{#top}{Top}\\end{nav}" ++
    "\\section*{Field Notes}Body text.\\end{document}")
  let (page, pds) := HtmlDoc.emit {} doc
  t "nav source and page are clean" (ds.isEmpty && pds.isEmpty)
  t "nav emits the landmark element around its links"
    (has page "<nav>" && has page "</nav>" && has page "<a href=\"#field-notes\""
      && has page "<section id=\"field-notes\">")
  t "markdown drops a nav: furniture, never twin content"
    (let md := MarkdownDoc.emit doc
     !has md "[Notes](#field-notes)" && has md "Field Notes" && has md "Body text.")
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
  let has := hasStr
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
  t "the reveal ships with its reduced-motion guard"
    (has page ("@media (prefers-reduced-motion: reduce) " ++
      "{ .reveal-scroll { animation: none; } }"))
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
  -- The markdown twin drops a pinned nav whole, as any nav: furniture.
  t "markdown drops a pinned nav" (!has (MarkdownDoc.emit doc) "[Up](#top)")
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
  let has := hasStr
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
states; the scan is the same shape as `diagChecks`'.

The `animation:` half of the same convention: only HtmlDoc.lean may spell
an animation into emitted styles, and every definition there that does
ends in its own reduced-motion guard (the guard travels with the
declaration — `revealCss`; the deck's typed rules carry theirs by
`guards_by_construction` and spell no `animation:` in source), spells the
guard query itself (the base stylesheet's global block and the guards),
or is named on the allowlist with its reason (`themeCss`'s deck progress
bar ships only under the theme's own stylesheet, whose global reduce
block covers it). Doc comments are stripped first so prose spelling
"animation:" cannot satisfy or trip the census. -/
def motionSiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  for f in files do
    let src ← IO.FS.readFile f
    if (src.splitOn "transition:").length > 1 then
      check ref s!"transition is spelled only in HtmlDoc ({f})"
        (f.toString.endsWith "HtmlDoc.lean")
    if (src.splitOn "animation:").length > 1 then
      check ref s!"animation is spelled only in HtmlDoc ({f})"
        (f.toString.endsWith "HtmlDoc.lean")
  let ownGated := ["themeCss"]
  let src ← IO.FS.readFile "LeanTex/Core/HtmlDoc.lean"
  let stripped := match src.splitOn "/--" with
    | [] => ""
    | first :: rest => first ++ String.join (rest.map fun (seg : String) =>
        String.intercalate "-/" ((seg.splitOn "-/").drop 1))
  let mut name := ""
  let mut body := ""
  let mut blocks : Array (String × String) := #[]
  for line in stripped.splitOn "\n" do
    let starter := ["def ", "private def ", "theorem ", "private theorem ",
      "structure ", "instance ", "mutual", "end "].any (line.startsWith ·)
    if starter then
      blocks := blocks.push (name, body)
      name := if line.startsWith "def " || line.startsWith "private def " then
          (((line.splitOn "def ").getD 1 "").splitOn " ").headD ""
        else ""
      body := line
    else
      body := body ++ "\n" ++ line
  blocks := blocks.push (name, body)
  for (n, b) in blocks do
    if !n.isEmpty && (b.splitOn "animation:").length > 1 then
      let lastToken := (((b.trimAscii.toString.splitOn "\n").getLast?.getD ""
        ).trimAscii.toString.splitOn " ").getLast?.getD ""
      check ref s!"animation-emitting def carries its guard ({n})"
        ((b.splitOn "prefers-reduced-motion").length > 1 ||
         lastToken.endsWith "Guard" || ownGated.contains n)

/-- The paged deck's stylesheet is the slides class's own: snap paging on
screen, the handout card in print, and no other class ships a deck rule —
which is what keeps the site port's webpage output unchanged. Every motion
rule carries its reduced-motion counterpart by theorem
(`HtmlDoc.guards_by_construction`); this pins the emitted page. -/
def deckCssChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (deckDoc, deckDs) := elabStr (deck169 "" "\\begin{frame}{T}\nx\n\\end{frame}")
  let deckPage := (HtmlDoc.emit {} deckDoc).1
  let has := hasStr
  t "deck css fixture elaborates clean" deckDs.isEmpty
  t "the deck pages horizontally by scroll snap on the root, no scrollbar stealing width"
    (has deckPage "html { scroll-snap-type: x mandatory; overflow-y: clip; }" &&
     has deckPage "[data-snap] { scroll-snap-align: start; scroll-snap-stop: always; }")
  t "the deck is a row: main flex, each section one viewport of it"
    (has deckPage ("main { max-width: none; margin: 0; display: flex; " ++
       "align-items: flex-start;") &&
     has deckPage ("section.slide, section.section-page { width: 100vw; " ++
       "flex: 0 0 100vw; height: 100dvh; overflow-y: auto;"))
  t "the deck glide ships with its reduced-motion guard"
    (has deckPage "html { scroll-behavior: smooth; }" &&
     has deckPage "@media (prefers-reduced-motion: reduce) {" &&
     has deckPage "html { scroll-behavior: auto; }")
  t "the deck slide fills the viewport as an opaque column"
    (has deckPage "background: var(--surface); display: flex; flex-direction: column;")
  t "the deck prints as the handout, one card per page"
    (has deckPage "@media print" &&
     has deckPage "break-inside: avoid" &&
     has deckPage "section.slide { break-after: page; }")
  -- No push, no sticky stage, no view-timeline gate in a stepless deck:
  -- the scroll itself is the motion, and the frame sections are the snap
  -- pages on every path (the progress hairline's own scroll() gate is
  -- the theme's, judged in deckProgressChecks).
  t "a stepless deck ships no feature gate: the scroll is the motion"
    (!has deckPage "@supports (animation-timeline: view())" &&
     !has deckPage "@supports not" && !has deckPage "position: sticky" &&
     !has deckPage "ltx-push" && !has deckPage "ltx-uncover" &&
     !has deckPage "class=\"slide-track\"" && !has deckPage "class=\"snap\"" &&
     has deckPage "data-snap>")
  -- The constant keyboard script (`HtmlDoc.deckScript`), the slides
  -- class's own: it queries the same `[data-snap]` selector the door
  -- rule styles, marks `<html data-deck-script>`, and survives the
  -- raw-payload guard verbatim (no `</script` in the constant).
  t "the deck ships the constant keyboard script through the snap door"
    ((deckPage.splitOn "<script").length == 2 &&
     has deckPage "document.documentElement.dataset.deckScript" &&
     has deckPage "document.querySelectorAll(\"[data-snap]\")" &&
     has deckPage "scrollIntoView" && !has deckPage "/* removed */")
  t "the deck keeps the safe area and caps the title band"
    (has deckPage "padding: var(--safearea, 6vmin); position: relative; }" &&
     has deckPage "max-height: var(--titleband, 12.5dvh)")
  -- 11pt over the 90mm stage (Ir.slidesFontSize / Ir.slidesStage169.2),
  -- truncated to the printed milli: deck_type_is_stage_ratio's bounds.
  t "deck type is the PDF's stage ratio, in vh"
    (has deckPage "font-size: 4.311vh; }" &&
     has deckPage "h1 { font-size: 1.728em; }" &&
     has deckPage "section.slide > header h2 { font-size: 1.440em; }")
  let (tokDoc, _) := elabStr (deck169 "\\tokens{ safearea = 20pt }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a declared safearea token overrides the engine default"
    (has (HtmlDoc.emit {} tokDoc).1 "--safearea: 20pt;")
  -- The deck is stage-free by construction: the emitted page carries no
  -- stage millimetre — type rides the stage-height ratio in vh (above)
  -- and the slide fills the viewport (100dvh; a block section fills the
  -- width) — so on a viewport of another ratio the frame reflows rather
  -- than letterboxing. The sharp half: two stages of equal height and
  -- different width (16:9 is 160×90 mm, 14:9 is 140×90) emit identical
  -- screen decks, so the screen rendering never reads the stage width;
  -- the third stage differing keeps the comparison honest (16:10's
  -- 100 mm height moves the vh). Print is the handout — a paged medium
  -- with a stage — so its measure legitimately reads the page and stays
  -- outside this property.
  t "the deck page carries no stage millimetre" (!has deckPage "mm")
  let deckAt (ratio : String) : String :=
    (HtmlDoc.emit {} (elabStr
      (s!"\\documentclass[aspectratio={ratio}]\{slides}\n" ++
        "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}")).1).1
  let screenOf (page : String) : String :=
    (((page.splitOn "@media screen {").getD 1 "").splitOn "@media print").headD ""
  t "equal-height stages emit one screen deck: the width is never read"
    (screenOf (deckAt "169") != "" &&
     screenOf (deckAt "169") == screenOf (deckAt "149") &&
     screenOf (deckAt "169") != screenOf (deckAt "1610"))
  -- The other half of the uncover census: a stepless deck has nothing to
  -- reveal and ships no timeline, uncover rule, track, or spacer — its
  -- frames are their own snap pages.
  t "a stepless deck ships no uncover rule and no track"
    -- (`--frame x`/`animation-timeline: --frame` are the timeline's own
    -- spellings; a `--frametitle…` token var is not a timeline.)
    (!has deckPage "ltx-uncover" && !has deckPage "--frame x" &&
     !has deckPage "animation-timeline: --frame" &&
     !has deckPage "data-snapped" && !has deckPage "scroll-state" &&
     !has deckPage "class=\"slide-track\"" && !has deckPage "class=\"snap\"")
  -- The gate, both directions: no deck rule and no script outside the
  -- slides class.
  for (name, src) in [
      ("article", "\\documentclass{article}\\begin{document}x\\end{document}"),
      ("webpage", "\\documentclass{webpage}\\begin{document}x\\end{document}")] do
    let (doc, _) := elabStr src
    let page := (HtmlDoc.emit {} doc).1
    t s!"{name} ships no deck rule and no deck script"
      (!has page "scroll-snap" && !has page "scroll-behavior" &&
       !has page "scroll-state" && !has page "ltx-uncover" &&
       !has page "slide-track" && !has page "data-snap" &&
       !has page "<script" &&
       has page "section.slide { border:")

  -- Every typed rule survives emission: the declaration multiset of the
  -- emitted stylesheet equals the typed set's — `emitDeckRules` drops and
  -- duplicates nothing on its way through the gate grouping. Each rule
  -- renders on one line, so the parse is line-local: the body between a
  -- line's last `{` and first `}`.
  let rules := HtmlDoc.deckRules "4.311vh" 38 3
  let typed := rules.flatMap fun r => r.decls.map fun d => d.1 ++ ": " ++ d.2
  let emitted := ((HtmlDoc.emitDeckRules rules).splitOn "\n").flatMap fun l =>
    if (l.splitOn "{").length ≥ 2 && (l.splitOn "}").length ≥ 2 then
      let body := ((((l.splitOn "{").getLast?.getD "").splitOn "}").headD "")
      (body.splitOn ";").filterMap fun d =>
        let d := d.trimAscii.toString
        if d.isEmpty then none else some d
    else []
  t "every typed deck declaration survives emission, exactly once"
    (typed.length == emitted.length &&
     typed.all fun d => typed.count d == emitted.count d)

/-- Rubber image sizes in the deck: the stage is the viewport, so every
stage-resolved image dimension ships as its share of the stage
(`HtmlDoc.image_share_agrees`) — `vw`/`dvh` for absolute lengths,
`\textheight` fractions and bare scales; `%` for the `\textwidth`
fraction both backends resolve against the local measure — and the
deck's HTML carries no `pt` image dimension (the "very small image"
defect: a print length on a stage that is the viewport). Flow classes
keep the print reading untouched: paper is paper. -/
def deckImageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let imgs := "\\includegraphics[width=0.5\\textwidth, alt={A synthetic box}]{a.png}\n\n" ++
    "\\includegraphics[height=0.4\\textheight, alt={A synthetic box}]{a.png}\n\n" ++
    "\\includegraphics[width=5cm, alt={A synthetic box}]{a.png}\n\n" ++
    "\\includegraphics[scale=0.5, alt={A synthetic box}]{a.png}\n\n" ++
    "\\begin{tikzpicture}\n\\fill (0,0) rectangle (2,1);\n\\end{tikzpicture}"
  -- 144 px at the default density is 144 pt intrinsic width.
  let info : Image.Plan := { pxW := 144
                             pxH := 72 }
  let store : Image.Store := { entries := #[{ src := "a.png"
                                              info := some info }] }
  let (doc, ds) := elabStr (deck169 ""
    ("\\begin{frame}{Pics}\n" ++ imgs ++ "\n\\end{frame}"))
  t "deck image fixture elaborates clean" ds.isEmpty
  let html := (HtmlDoc.emit { imgs := store } doc).1
  let has (s : String) : Bool := (html.splitOn s).length ≥ 2
  let count (s : String) : Nat := (html.splitOn s).length - 1
  t "a textwidth fraction stays the measure's percentage"
    (has "width: 50%; height: auto")
  t "a textheight fraction is its share of the stage height, in dvh"
    (has "dvh; width: auto")
  t "an absolute length and a bare scale are shares of the stage width"
    (count "vw; height: auto" == 2)
  t "the deck carries no pt image dimension"
    (((html.splitOn "<img").drop 1).all fun s =>
      (((s.splitOn ">").headD "").splitOn "pt").length == 1)
  t "a picture's box is its share of the stage, no pt dimension"
    ((((html.splitOn "<svg").drop 1).all fun s =>
        (((s.splitOn ">").headD "").splitOn "pt").length == 1) &&
     has "vw; height:" && has "dvh\"")
  -- An SVG picture label carries inline content, and math it cannot model
  -- reaches the same floor the prose path does: the label's <tspan> shows
  -- content, never a control sequence (`Ir.floorInk_mem`). This is the
  -- assertion the backend emission owes — the shipped-page census reads
  -- `Layout.Out`, so the SVG label is outside it and would otherwise be
  -- watched by nothing.
  let labelDeck := dvDeck "" ("\\begin{frame}{Labelled}\n" ++
    "\\begin{tikzpicture}\n" ++
    "\\node at (0,0) {$\\overset{\\textcolor{indigo}{q}}{=}$};\n" ++
    "\\end{tikzpicture}\n\\end{frame}")
  let labelHtml := (HtmlDoc.emit {} (elabStr labelDeck).1).1
  t "an SVG label's math shows its floor, never its markup"
    (let spans := (labelHtml.splitOn "<tspan").drop 1
     let shownOf := fun (s : String) =>
       let inner := ((s.splitOn ">").drop 1).headD ""
       (inner.splitOn "<").headD ""
     !spans.isEmpty &&
       spans.all (fun s => !((shownOf s).any (fun c => Ir.markupChars.contains c))) &&
       -- positive too: the label's own content is there, so an empty tspan
       -- or the placeholder cannot pass this
       spans.any (fun s => shownOf s == "q=") &&
       ((labelHtml.splitOn "indigo").length == 1))
  -- The flow reading, untouched: pt for the absolute length and the
  -- scale, % for the fraction, the intrinsic size for the textheight
  -- fraction (no CSS analog on paper).
  let (art, artDs) := elabStr (dvDoc "" imgs)
  t "flow image fixture elaborates clean" artDs.isEmpty
  let artHtml := (HtmlDoc.emit { imgs := store } art).1
  let hasA (s : String) : Bool := (artHtml.splitOn s).length ≥ 2
  t "flow keeps the print reading: pt lengths, no viewport unit"
    (hasA "width: 50%; height: auto" &&
     hasA "pt; height: auto" &&
     hasA "width: 72pt; height: auto" &&
     !hasA "dvh" && !hasA "vw")
  t "a flow picture keeps its pt box"
    (hasA "pt\" height=\"" || hasA "pt\" role=\"img\"")

/-- The paged deck's structure: a frame's declared vertical distribution
reaches the artifact as flex spacers carrying the PDF's own ratios (both
project `Ir.VAlign.shares`; `vdist_shares_agree` states it) and every
slide is fragment-addressable through an id unique by the shared claim
walk. -/
def deckStructureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169 "\\title{T}\\author{A}"
    ("\\maketitle\n" ++
     "\\begin{frame}[t]{Alpha}\na\n\\end{frame}\n" ++
     "\\begin{frame}[b]{Alpha}\nb\n\\end{frame}\n" ++
     "\\begin{frame}{Beta}\nc\n\\end{frame}"))
  t "deck structure fixture elaborates clean" ds.isEmpty
  let (html, eds) := HtmlDoc.emit {} doc
  let count (s : String) : Nat := (html.splitOn s).length - 1
  t "declared distributions land as their ratios"
    -- golden above the title matter, its below share beneath; [t] one
    -- spacer below, [b] one above, the default centring one each side.
    -- The golden pair is the composed share (`Ir.golden_composes_center`):
    -- the frame's own centring unit on each side plus the template's glue.
    (count "flex-grow: 3618" == 1 && count "flex-grow: 2000" == 1 &&
     count "flex-grow: 1\"" == 4)
  t "frame ids are unique, a repeated identical title numbers quietly"
    (count "id=\"alpha\"" == 1 && count "id=\"alpha-2\"" == 1 &&
     count "id=\"beta\"" == 1 && !eds.any (·.code == "W0327"))
  let (linkDoc, _) := elabStr (deck169 ""
    ("\\begin{frame}{A-B}\nx\n\\end{frame}\n" ++
     "\\begin{frame}{A B}\n\\href{#a-b}{go}\n\\end{frame}"))
  let (linkHtml, linkDs) := HtmlDoc.emit {} linkDoc
  t "two different frame titles folding to one slug are named"
    (linkDs.any (·.code == "W0327"))
  t "a deep link to a frame id resolves"
    (!linkDs.any (·.code == "W0326") &&
     (linkHtml.splitOn "id=\"a-b\"").length == 2 &&
     (linkHtml.splitOn "id=\"a-b-2\"").length == 2)

/-- The deck's progress hairline: emitted exactly when the deck draws
progress at all, scaled by the root scroll under `@supports` (Scroll-driven
Animations 1), reading the same two tokens the PDF's section-page bar
reads. The emission census a backend emission owes — asserted on the
emitted page, the HTML face of the `censusTable` obligation. -/
def deckProgressChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169 "\\theme{moloch}"
    "\\section{S}\n\\begin{frame}{T}\nx\n\\end{frame}")
  let html := (HtmlDoc.emit {} doc).1
  let has := hasStr
  t "progress deck elaborates clean" (ds.all fun d => d.severity == .note)
  t "the themed deck ships its progress hairline"
    (has html "class=\"deck-progress\"")
  t "the hairline scales by the root scroll's deck axis under supports"
    (has html "@supports (animation-timeline: scroll())" &&
     has html "animation-timeline: scroll(root x)")
  t "the hairline reads the tokens the PDF's bar reads"
    (has html (".deck-progress { position: fixed; top: 0; left: 0; width: 100%;\n" ++
      "  height: var(--progressheight, 1pt); background: var(--progressfg);"))
  let (bareDoc, _) := elabStr (deck169 "\\theme{default}"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a deck that draws no progress ships no hairline"
    (!has (HtmlDoc.emit {} bareDoc).1 "deck-progress")
  let (artDoc, _) := elabStr "\\documentclass{article}\\begin{document}x\\end{document}"
  t "no other class ships the hairline"
    (!has (HtmlDoc.emit {} artDoc).1 "deck-progress")

/-- The read size ladder reaches both artifacts: the PDF sets a named size
run at the venue's step — judged on the shipped lines' own segments, never
an IR dump — and the HTML stylesheet's `.size-` rules carry the same
ladder, so the two backends cannot disagree on what a venue's `\tiny`
means (`sizeRules`' docstring promise). An undeclared document keeps the
engine's scale in both. -/
def sizeLadderChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let venue := dvDoc
    ("\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xipt}" ++
     "\\renewcommand{\\tiny}{\\@setfontsize\\tiny\\@vipt\\@viipt}\n")
    "x {\\tiny y}"
  let (doc, _) := elabStr venue
  let out := layoutOf oneFace doc
  let sizes := (bodyLines out).flatMap fun l => l.segs.filterMap fun s =>
    match s with
    | .run _ _ _ _ _ size _ _ _ _ => some size
    | _ => none
  t "the venue tiny sets at 0.6 of the body on the shipped page"
    (sizes.contains (doc.page.fontSize * 600 / 1000) &&
     !sizes.contains (doc.page.fontSize * 500 / 1000))
  let html := (HtmlDoc.emit {} doc).1
  t "the html size rule carries the venue step"
    ((html.splitOn ".size-tiny { font-size: 0.600em; }").length == 2)
  let (plain, _) := elabStr (dvDoc "" "x {\\tiny y}")
  t "an undeclared document keeps the engine ladder in the stylesheet"
    ((((HtmlDoc.emit {} plain).1).splitOn
      ".size-tiny { font-size: 0.500em; }").length == 2)
  let psizes := (bodyLines (layoutOf oneFace plain)).flatMap fun l =>
    l.segs.filterMap fun s =>
      match s with
      | .run _ _ _ _ _ size _ _ _ _ => some size
      | _ => none
  t "an undeclared document keeps the engine ladder on the page"
    (psizes.contains (plain.page.fontSize * 500 / 1000))

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
  let has := hasStr page
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
  let pdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace doc geom).pages doc.info)
  t "the one declared title reaches all three surfaces"
    (has "<title>Alex Doe, PhD</title>" &&
     md.startsWith "# Alex Doe, PhD\n" &&
     bytesContain pdf "/Title (Alex Doe, PhD)")
  t "the one declared url reaches the pdf as XMP dc:identifier"
    (bytesContain pdf "<dc:identifier>https://example.org/alex</dc:identifier>")
  -- A text string past ASCII is UTF-16BE with the byte-order mark
  -- (ISO 32000-2 §7.9.2.2): raw UTF-8 in an Info string is read as
  -- PDFDocEncoding, and an 'é' displayed as 'Ã©' in the document panel.
  let accDoc := { doc with info := { doc.info with title := some "Bélair Résumé" } }
  let accPdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace accDoc geom).pages accDoc.info)
  t "an accented Info title is a UTF-16BE hex string with the BOM"
    (bytesContain accPdf
      "/Title <FEFF004200E9006C0061006900720020005200E900730075006D00E9>")
  t "the ascii entries beside it keep the literal spelling"
    (bytesContain accPdf "/Author (Alex Doe)")
  -- Both artifacts declare the document's language everywhere text
  -- appears: <html lang> (WCAG 2.2 SC 3.1.1) and the catalog /Lang
  -- (ISO 32000-2 §14.9.2.2) carry the SAME declared tag, a switched run
  -- is a span with its own lang (SC 3.1.2), and the window titles from
  -- the metadata (/DisplayDocTitle, §12.2).
  let (frDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\usepackage[french]{babel}\n\\begin{document}\n" ++
    "texte \\foreignlanguage{english}{words}\n\\end{document}")
  let frPage := (HtmlDoc.emit {} frDoc).1
  let frPdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace frDoc geom).pages frDoc.info)
  t "both artifacts carry the declared language"
    ((frPage.splitOn "<html lang=\"fr\">").length == 2 &&
     bytesContain frPdf "/Lang (fr)")
  t "a switched run is a span with its own lang"
    ((frPage.splitOn "<span lang=\"en\">words</span>").length == 2)
  t "an undeclared document declares english, and only at the root"
    ((page.splitOn "<html lang=\"en\">").length == 2 &&
     !bytesContain pdf "/Lang")
  t "the reader's window titles from the document's own title"
    (bytesContain pdf "/ViewerPreferences << /DisplayDocTitle true >>")
  t "the stylesheet asks the browser to hyphenate by that declaration"
    ((frPage.splitOn "hyphens: auto").length == 2)
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
  -- numbers off: the claim is about the body's pen movement, and the plain
  -- page number would add its own Tm.
  let (gapDoc0, _) := Elab.run "t" "a\\hfill b\n\n\\underline{x}"
  let gapDoc := { gapDoc0 with page := { gapDoc0.page with numbers := some false } }
  let gapText := asciiText (pdfText (Pdf.write wide oneFace (layoutOf oneFace gapDoc wide).pages))
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
      [((slot, 400, false), idx), ((slot, 700, false), idx),
       ((slot, 400, true), idx), ((slot, 700, true), idx)]).toArray
  }
  let (bigDoc, bigDs) := Elab.run "t"
    "plain {\\sffamily other face} and {\\Huge big} and {\\small little}"
  t "size scale source clean" bigDs.isEmpty
  let bigPdf := pdfText (Pdf.write geom twoFace (layoutOf twoFace bigDoc geom).pages)
  t "pdf references a second face" (bytesContain bigPdf "/F2 ")
  t "pdf sets Huge at 2.488x" (bytesContain bigPdf "24.88 Tf")
  t "pdf sets small at 0.9x" (bytesContain bigPdf "9 Tf")
  t "pdf keeps the body size" (bytesContain bigPdf "10 Tf")
  -- One face only: nothing unused is embedded, so no /F2 exists.
  let plainPdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace bigDoc geom).pages)
  t "pdf embeds no unused face" (!bytesContain plainPdf "/F2 ")
  -- The driver's cached spellings are transparent: pre-deflated content
  -- streams and face files (the cache's shape) write the file the writer
  -- compresses for itself, byte for byte.
  let bigPages := (layoutOf twoFace bigDoc geom).pages
  let cached := (Pdf.pageStreams geom twoFace bigPages).map fun d => (d, some (Flate.deflate d))
  let zFaces := twoFace.fonts.map fun f => some (Flate.deflate f.data)
  t "pdf with cached streams and faces is the pdf without"
    (Pdf.write geom { twoFace with zdata := zFaces } bigPages (streams := cached) ==
      Pdf.write geom twoFace bigPages)
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
  let build ← IO.Process.output
    { cmd := "lake", args := #["build", "precommit", "owed", "-q"] }
  check ref s!"gate scripts build:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    let out ← IO.Process.output
      { cmd := ".lake/build/bin/precommit", args := #["--selftest"] }
    check ref s!"precommit selftest:\n{out.stderr}" (out.exitCode == 0)
    let owed ← IO.Process.output
      { cmd := ".lake/build/bin/owed", args := #["--selftest"] }
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
    let (doc, docDs) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom (some pats)
    let (_, body, htmlDs) := HtmlDoc.emitTree {} doc
    let naming := (docDs ++ out.diags ++ htmlDs).any (namingCodes.contains ·.code)
    let pdf := dedupConsecutive (pdfFoots out)
    -- Both sides collapse a stepped frame's repeated footer: the deck
    -- emits one section per overlay step, as the PDF ships pages.
    let html := dedupConsecutive (slideFootsList #[] body.toList)
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
  t "html section becomes h2, its number a structural span"
    ((page.splitOn "<h2><span class=\"section-number\">1</span>\u2003Head</h2>").length == 2)
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

/-- The page ships the faces it names — the census of the `@font-face`
emission (the same obligation every backend emission carries): one rule per
face of the resolved set, slot variables naming only the synthetic families,
every referenced file among the write requests, and the generic keyword read
from the face's own OS/2 class, never from its name. The set is built from
the shipped corpus faces, so the checks also pin the OS/2 read on real
tables (Open Sans declares class 8; Source Code Pro declares nothing and
takes the slot's kind). -/
def fontShipChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO (Option Font.Font) := do
    try
      match Font.parse (← IO.FS.readBinFile s!"{testFonts}/{name}") with
      | .ok f => pure (some f)
      | .error _ => pure none
    catch _ => pure none
  let some sans ← load "OpenSans-Regular.ttf"
    | t "font ship: OpenSans-Regular loads" false
  let some code ← load "SourceCodePro-Regular.otf"
    | t "font ship: SourceCodePro-Regular loads" false
  let some icons ← load "ExampleIcons-Regular.ttf"
    | t "font ship: ExampleIcons-Regular loads" false
  -- The OS/2 fields, pinned on the real tables the fixtures ship.
  t "font ship: Open Sans declares OS/2 class 8, Source Code Pro none"
    (sans.familyClass == 8 && code.familyClass == 0)
  t "font ship: fsType embedding bits are recorded as declared"
    (sans.fsType == 0 && icons.fsType == 4)
  -- The deck's shape: body and sans from one face, mono its own — the
  -- driver's index for a document that declared body and mono families.
  let fs : Font.FontSet := {
    fonts := #[sans, code]
    index := ((List.range 2).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 0),
       ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray ++
      #[((2, 400, false), 1), ((2, 700, false), 1),
        ((2, 400, true), 1), ((2, 700, true), 1)] }
  let src ← IO.FS.readFile "tests/corpus/deck.tex"
  let (doc, _) ← elabFixture "deck" src
  let cfg : HtmlDoc.Config := { fonts := some fs, fontsDir := "deck.fonts" }
  let (html, _) := HtmlDoc.emit cfg doc
  let faces := HtmlDoc.shipFaces fs
  t "census deck html: one @font-face per resolved face"
    ((html.splitOn "@font-face").length == faces.size + 1)
  t "census deck html: the font-family variables name the synthetic families"
    (((html.splitOn "--font-body: \"ltx-body\"").length == 2) &&
     ((html.splitOn "--font-sans: \"ltx-sans\"").length == 2) &&
     ((html.splitOn "--font-mono: \"ltx-mono\"").length == 2))
  t "font ship: every requested file is referenced from the page"
    ((HtmlDoc.fontAssets fs).all fun a => (html.splitOn a.file).length ≥ 2)
  t "font ship: one write request per face, carrying its bytes"
    ((HtmlDoc.fontAssets fs).size == fs.fonts.size &&
     (HtmlDoc.fontAssets fs).all fun a => !a.data.isEmpty)
  t "font ship: the OS/2 sans class closes the body stack, not the slot's serif"
    ((html.splitOn "--font-body: \"ltx-body\", \"ltx-sans\", \"ltx-mono\", sans-serif;").length == 2)
  t "font ship: an undeclared class takes the slot's kind"
    ((html.splitOn "--font-mono: \"ltx-mono\", \"ltx-body\", \"ltx-sans\", monospace;").length == 2)
  t "font ship: the body weight is the resolved face's, and nothing is faked"
    ((html.splitOn "body { font-weight: 400; font-synthesis: small-caps; }").length == 2)
  -- A face only per-glyph fallback reaches ships under its own family and
  -- every slot stack appends it, so the browser's per-character walk can
  -- reach it — the CSS spelling of `FontSet.fallback`.
  let fsFb : Font.FontSet := { fs with fonts := fs.fonts.push icons }
  let (htmlFb, _) := HtmlDoc.emit { cfg with fonts := some fsFb } doc
  t "font ship: a slotless face ships under its fallback family"
    (((htmlFb.splitOn "font-family: \"ltx-fb2\"").length == 2) &&
     ((htmlFb.splitOn
        "--font-body: \"ltx-body\", \"ltx-sans\", \"ltx-mono\", \"ltx-fb2\", sans-serif;").length == 2))
  -- The math face rides through its token; the `.math` rule reads it.
  let fsMath : Font.FontSet := { fs with math := some 1 }
  let (htmlMath, _) := HtmlDoc.emit { cfg with fonts := some fsMath } doc
  t "font ship: the resolved math face lands in --font-math"
    ((htmlMath.splitOn "--font-math: \"ltx-math\", \"ltx-body\", \"ltx-sans\", \"ltx-mono\", math;").length == 2)
  t "font ship: .math reads the document's math face through its token"
    ((htmlMath.splitOn ".math { font-family: var(--font-math,").length == 2)
  -- Without a set nothing ships: the name-only stacks stay, unchanged.
  t "font ship: a config with no set ships no rules"
    (((HtmlDoc.emit {} doc).1.splitOn "@font-face").length == 1)
  -- The generic keyword rules, on faces that declare each field.
  let mkF (cls : Nat) (fixed : Bool) : Font.Font :=
    { (default : Font.Font) with familyClass := cls, isFixedPitch := fixed }
  t "generic keyword: class 8 is sans-serif"
    (HtmlDoc.genericFor (oneFaceOf (mkF 8 false)) 0 "serif" == "sans-serif")
  t "generic keyword: classes 1-7 are serif"
    (HtmlDoc.genericFor (oneFaceOf (mkF 3 false)) 1 "sans-serif" == "serif")
  t "generic keyword: fixed pitch is monospace whatever the class"
    (HtmlDoc.genericFor (oneFaceOf (mkF 8 true)) 0 "serif" == "monospace")
  t "generic keyword: an undeclared class takes the slot's declared kind"
    (HtmlDoc.genericFor (oneFaceOf (mkF 0 false)) 0 "serif" == "serif")

/-- The backends' note apparatus: the HTML mark is a `doc-noteref` sup
link, the one `doc-endnotes` section carries each body once with its
`doc-backlink` (W3C DPUB-ARIA 1.1), no script and no broken anchor; the
markdown twin sets `[^k]` marks with their definitions after the body. -/
def footnoteBackendChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := dvDoc "" ("A claim\\footnote{the note text} continues.\n\n" ++
    "Second\\footnote[7]{a seventh aside} claim.")
  let (doc, _) := elabStr src
  let (html, hds) := HtmlDoc.emit {} doc
  t "html: each mark is a doc-noteref link"
    ((html.splitOn "role=\"doc-noteref\"").length == 3 &&
     (html.splitOn "href=\"#fn1\"").length == 2 &&
     (html.splitOn "id=\"fnref1\"").length == 2)
  t "html: one doc-endnotes section ships"
    ((html.splitOn "role=\"doc-endnotes\"").length == 2)
  t "html: the note body lands once, in its endnote item"
    ((html.splitOn "id=\"fn1\"").length == 2 &&
     (html.splitOn "the note text").length == 2)
  t "html: each endnote carries its doc-backlink to the mark"
    ((html.splitOn "role=\"doc-backlink\"").length == 3 &&
     (html.splitOn "href=\"#fnref7\"").length == 2)
  t "html: the note anchors resolve both ways (W0326 silent)"
    (hds.all (·.code != "W0326"))
  t "html: the apparatus ships no script"
    ((html.splitOn "<script").length == 1)
  let md := MarkdownDoc.emit doc
  t "md: the marks are [^k] labels"
    ((md.splitOn "[^1]").length ≥ 2 && (md.splitOn "[^7]").length ≥ 2)
  t "md: the definitions land after the body"
    ((md.splitOn "[^1]: the note text").length == 2 &&
     (md.splitOn "[^7]: a seventh aside").length == 2)
  t "md: a noted document keeps one trailing newline"
    (md.endsWith "\n" && !(md.endsWith "\n\n"))
  t "md: an unnoted document is unchanged in shape"
    (let md0 := MarkdownDoc.emit (elabStr (dvDoc "" "plain words")).1
     md0.endsWith "\n" && !(md0.endsWith "\n\n") && !((md0.splitOn "[^").length ≥ 2))

/-- The PDF-figure path (PLAN's asset half of the graphics boundary):
`\includegraphics{x.pdf}` embeds page 1 as a form XObject. The fixture is
the engine's own output (`tests/corpus/figures/box.tex` is its committed
generator), so the reader is exercised against the writer — xref stream,
object stream, embedded font program and all — and the roundtrip below
reads back the file this test writes. -/
def pdfFormChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pdfData ← IO.FS.readBinFile "tests/corpus/figures/box.pdf"
  let inf? := Image.decode pdfData
  t "shipped pdf decodes as a form"
    (match inf? with
     | .ok inf => inf.form.isSome && inf.data.isEmpty
     | .error _ => false)
  -- The intrinsic size is the page box (`form_bbox_exact`'s other half):
  -- the card declared 90 × 54 mm, and the writer's `Sp.toPtString`
  -- rounded each edge once at the thousandth of a point — so the read
  -- box stands within one thousandth-pt unit of the declared size.
  t "pdf intrinsic size is the page box"
    (match inf? with
     | .ok inf =>
       (Dim.mm 90 - inf.width).natAbs ≤ 66 &&
       (Dim.mm 54 - inf.height).natAbs ≤ 66
     | .error _ => false)
  -- The copied graph: the fixture embeds a font, so its resource closure
  -- is non-trivial; `resources_closed` rides in the subtype the decoder
  -- stored, so a dangling hole is unrepresentable here.
  t "pdf resources graph copied with the page"
    (match inf? with
     | .ok inf =>
       (inf.form.map fun f =>
         f.val.objects.size > 0 && !f.val.content.isEmpty).getD false
     | .error _ => false)
  -- Totality over truncations, as fonts: a verdict for every prefix, the
  -- full sweep living in scripts/img-fuzz.lean.
  t "pdf decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (pdfData.extract 0 (pdfData.size * k / 64))).isOk).length == 64)
  t "pdf decode rejects a headerless tail"
    ((Image.decode (pdfData.extract 4 pdfData.size)).isOk == false)
  -- Write → read: place the fixture at a declared size, write the PDF,
  -- and the file carries the form XObject, its xref verifies, and this
  -- engine's own reader follows the produced file back to a form.
  let store : Image.Store := { entries := #[
    { src := "box.pdf", info := inf?.toOption }] }
  let (doc, _) := Elab.run "t"
    "\\includegraphics[width=100pt, alt={An embedded synthetic card}]{box.pdf}"
  let out := layoutOf oneFace doc {} none store
  let pdf := Pdf.write {} oneFace out.pages (imgs := store)
  t "written pdf carries the form XObject" (bytesContain pdf "/Subtype /Form")
  t "written pdf carries the normalizing matrix" (bytesContain pdf "/Matrix")
  t "written pdf xref verifies over the copied graph" ((checkXref pdf).isOk)
  t "written pdf reads back: forms within forms"
    (match PdfRead.readForm pdf with
     | .ok f => !f.val.content.isEmpty
     | .error _ => false)
  -- The placed segment takes the declared width, and the height follows
  -- the box's own ratio, as every image does (`resolveSize`).
  let segs := Id.run do
    let mut acc : Array (Option Nat × Dim.Sp × Dim.Sp) := #[]
    for p in out.pages do
      for l in p.lines do
        for s in l.segs do
          if let .image idx w h := s then acc := acc.push (idx, w, h)
    return acc
  t "pdf figure places at the declared width"
    (match inf?, segs with
     | .ok inf, #[(some 0, w, h)] =>
       w == Dim.pt 100 && h == Dim.pt 100 * inf.height / inf.width
     | _, _ => false)

/-- `algorithm_lines_agree`'s executable side. The theorem holds the line
census — that `algNest`'s forest reads back as the declared array, so no
line reaches one artifact and misses the other — and what remains for an
oracle is the *rendering* of that forest, which no theorem states: one
`<li>` per node, one nested `<ol>` per level, and the emission order the
census fixes. Checked over the shapes that exercise it: the `\eIf` else
standing at its if's own level (the double-nesting defect this pins), a
plain loop, and — built on the IR, since no surface spelling produces
it — a depth that skips a level, where the forest stands a group in for
the level nothing declared. -/
def algorithmBackendChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let emitOf (body : String) : String :=
    (HtmlDoc.emit {} (elabStr (dvDoc "" body)).1).1
  let html := emitOf ("\\begin{algorithm}\n\\caption{An invented check.}\n" ++
    "\\eIf{$a > 0$}{one\\;}{two\\;}\n\\Return{$r$}\\;\n\\end{algorithm}")
  -- one <li> per line: if, one, else, two, end, return
  t "algorithm html: one list item per line"
    (((html.splitOn "<li>").length - 1) == 6)
  -- the outer list plus one nested list per branch body
  t "algorithm html: eIf nests each branch once"
    (((html.splitOn "<ol").length - 1) == 3)
  -- the census in emission order — no line lost, none reordered
  let inOrder (hay : String) (needles : List String) : Bool := Id.run do
    let mut rest := hay
    for n in needles do
      match rest.splitOn n with
      | _ :: t1 :: ts => rest := String.intercalate n (t1 :: ts)
      | _ => return false
    return true
  t "algorithm html: the list-item census keeps line order"
    (inOrder html ["<strong>if</strong>", "<strong>then</strong>", "one;",
      "<strong>else</strong>", "two;", "<strong>end</strong>",
      "<strong>return</strong>"])
  -- the else stands at its if's level: the nested <ol> before it closed
  t "algorithm html: the else closes its then-branch first"
    (inOrder html ["one;", "</ol>", "<strong>else</strong>"])
  let deep := emitOf ("\\begin{algorithm}\n" ++
    "\\For{$i$}{\\While{$c$}{step\\;}}\n\\end{algorithm}")
  t "algorithm html: nested loops nest their lists"
    (((deep.splitOn "<ol").length - 1) == 3 &&
      inOrder deep ["<strong>for</strong>", "<strong>while</strong>",
        "step;", "<strong>end</strong>", "<strong>end</strong>"])
  -- a skipped level, straight on the IR: the forest carries every line and
  -- opens a list for the level no line declared
  let stmt (d : Nat) (txt : String) : Ir.AlgLine :=
    { depth := d, kind := .statement, content := #[.text txt], comment := none }
  let jumpDoc : Ir.Doc :=
    { body := #[.algorithm false true #[stmt 0 "top", stmt 2 "deep"]] }
  let jump := (HtmlDoc.emit {} jumpDoc).1
  t "algorithm html: a skipped level still ships both lines"
    (((jump.splitOn "<li>").length - 1) == 3 && inOrder jump ["top;", "deep;"])
  t "algorithm html: a skipped level opens a list per level"
    (((jump.splitOn "<ol").length - 1) == 3)

mutual

/-- Every `code` element's `class` attribute in the typed tree, in document
order — `none` for a `code` that carries no class. The listing-language
oracle reads the attribute the tree carries, never the printed string. -/
def codeClassesOne (acc : Array (Option String)) : Html.Node → Array (Option String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let acc := if t == "code" then acc.push ((attrs.find? (·.1 == "class")).map (·.2)) else acc
    codeClassesList acc kids.toList

def codeClassesList (acc : Array (Option String)) : List Html.Node → Array (Option String)
  | [] => acc
  | k :: rest => codeClassesList (codeClassesOne acc k) rest

end

/-- `listing_language_agree`'s executable oracle over the two text artifacts:
one declared language reaches the HTML `code` element's `language-…` class
and the markdown fence's info string; a listing without one reaches neither;
a spelling outside the token grammar is named W0110 and reaches neither. The
typed tree is read for the class, the emitted twin for the fence. -/
def listingLanguageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let docOf (body : String) : Ir.Doc × Array Diag := elabStr (dvDoc "" body)
  let classesOf (doc : Ir.Doc) : Array (Option String) :=
    let (head, body, _) := HtmlDoc.emitTree {} doc
    codeClassesList (codeClassesList #[] head.toList) body.toList
  let fencesOf (doc : Ir.Doc) : List String :=
    ((MarkdownDoc.emit doc).splitOn "```").zipIdx.filterMap fun (seg, i) =>
      -- opening fences stand at odd positions between the delimiters; the
      -- info string is the opener's first line
      if i % 2 == 1 then some ((seg.splitOn "\n").headD "") else none
  let (lst, _) := docOf "\\begin{lstlisting}[language=Python]\nx = 1\n\\end{lstlisting}"
  t "html: a listings language reaches the code element's class"
    (classesOf lst == #[some "language-python"])
  t "markdown: a listings language reaches the fence info string"
    (fencesOf lst == ["python"])
  let (mnt, _) := docOf "\\begin{minted}{Python}\nprint(1)\n\\end{minted}"
  t "html: minted's language argument reaches the code element's class"
    (classesOf mnt == #[some "language-python"])
  t "markdown: minted's language argument reaches the fence info string"
    (fencesOf mnt == ["python"])
  let (bare, _) := docOf "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}"
  t "html: a listing without a language carries no class"
    (classesOf bare == #[none])
  t "markdown: a listing without a language opens a bare fence"
    (fencesOf bare == [""])
  let (verb, _) := docOf "\\begin{verbatim}\nx = 1\n\\end{verbatim}"
  t "html: verbatim carries no class"
    (classesOf verb == #[none])
  t "markdown: verbatim opens a bare fence"
    (fencesOf verb == [""])
  -- listings' dialect spelling is outside the token grammar: named, and the
  -- raw text reaches neither artifact
  let (dialect, ds) := docOf "\\begin{lstlisting}[language={[LaTeX]TeX}]\nx\n\\end{lstlisting}"
  t "an invalid language spelling is named W0110"
    (ds.any (·.code == "W0110"))
  t "html: an invalid language spelling reaches no class"
    (classesOf dialect == #[none])
  t "markdown: an invalid language spelling reaches no fence info"
    (fencesOf dialect == [""])
  -- the class survives the caption and line-number apparatus around it
  let (full, _) := docOf ("\\begin{lstlisting}[language=C++, caption={An invented probe}, " ++
    "numbers=left]\nint x;\n\\end{lstlisting}")
  let fullHtml := (HtmlDoc.emit {} full).1
  t "html: a captioned, numbered listing keeps its language class"
    (classesOf full == #[some "language-c++"] &&
      (fullHtml.splitOn "<figure class=\"listing\">").length == 2 &&
      (fullHtml.splitOn "class=\"numbered\"").length == 2)
  t "markdown: a captioned listing's fence carries the info string after the caption"
    (fencesOf full == ["c++"] &&
      ((MarkdownDoc.emit full).splitOn "Listing 1: An invented probe\n\n```c++\n").length == 2)
  -- the attribute goes through the escaper as every attribute does: a
  -- token cannot carry a quote, and the printed class is exactly the token
  t "html: the printed class is the token, escaped by construction"
    ((fullHtml.splitOn "<code class=\"language-c++\">").length == 2)

/-- One cell of an emitted table, as the facts the header contract judges:
the row group it sits in (`thead`/`tbody`, or `""` when the table has
none), its tag, its `scope`, its `class`, and its text. -/
structure CellFact where
  group : String
  tag : String
  scope : String
  cls : String
  text : String
  deriving BEq, Repr

mutual

/-- Every `th`/`td` of a typed tree in document order, each with the row
group above it — the HTML side of `Ir.tableHeaderRows`. -/
def cellFactsOne (group : String) (acc : Array CellFact) : Html.Node → Array CellFact
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let attr (k : String) : String := ((attrs.find? (·.1 == k)).map (·.2)).getD ""
    if tag == "th" || tag == "td" then
      acc.push {
        group := group
        tag := tag
        scope := attr "scope"
        cls := attr "class"
        text := nodeTextOne "" (.elem tag attrs kids) }
    else
      let group := if tag == "thead" || tag == "tbody" then tag else group
      cellFactsList group acc kids.toList

def cellFactsList (group : String) (acc : Array CellFact) : List Html.Node → Array CellFact
  | [] => acc
  | k :: rest => cellFactsList group (cellFactsOne group acc k) rest

end

mutual

/-- Every `tr`'s `class` value in document order (`""` when unclassed): the
rule classes the stylesheet draws, which the header regrouping may not move. -/
def rowClassesOne (acc : Array String) : Html.Node → Array String
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    if tag == "tr" then
      acc.push (((attrs.find? (·.1 == "class")).map (·.2)).getD "")
    else rowClassesList acc kids.toList

def rowClassesList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => rowClassesList (rowClassesOne acc k) rest

end

mutual

/-- The tags of a table's direct children — `colgroup`, `thead`, `tbody`
— so a test can state which row groups a table ships. -/
def tableGroupsOne (acc : Array (Array String)) : Html.Node → Array (Array String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag _ kids =>
    if tag == "table" then
      acc.push (kids.filterMap fun k => match k with
        | .elem t _ _ => some t
        | _ => none)
    else tableGroupsList acc kids.toList

def tableGroupsList (acc : Array (Array String)) : List Html.Node → Array (Array String)
  | [] => acc
  | k :: rest => tableGroupsList (tableGroupsOne acc k) rest

end

/-- One header fact for both artifacts: `Ir.tableHeaderRows` names
booktabs' head — the rows before the first `\midrule` — and the HTML arm
ships exactly those rows as `<thead>`/`<th scope=col>`, the rest as
`<tbody>`/`<td>`. Cell text and order, the rule classes on each row, and
the `bt-cmid` cell class are unchanged by the regrouping: the header is a
semantic fact, not a visual one (the stylesheet neutralises `th`'s UA bold
and centring so the raster cannot move). Invented content. -/
def tableHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let rows3 : Array (Array (Array Ir.Inline)) :=
    #[#[#[.text "a"]], #[#[.text "b"]], #[#[.text "c"]]]
  let hdr := Ir.tableHeaderRows rows3
  t "no rules: zero header rows" (hdr #[] == 0)
  t "toprule alone: zero header rows" (hdr #[(0, .top), (3, .bottom)] == 0)
  t "one row before the midrule: one header row"
    (hdr #[(0, .top), (1, .mid), (3, .bottom)] == 1)
  t "two rows before the midrule: two header rows"
    (hdr #[(0, .top), (2, .mid), (3, .bottom)] == 2)
  t "the first midrule decides, later ones do not"
    (hdr #[(0, .top), (1, .mid), (2, .mid), (3, .bottom)] == 1)
  t "a midrule written before any row (an \\hline frame) heads nothing"
    (hdr #[(0, .mid), (3, .mid)] == 0)
  t "cmidrule, cline, addlinespace and \\\\[len] are not midrules"
    (hdr #[(0, .top), (1, .cmid 1 2 true true), (2, .gap {}),
      (2, .cmid 1 1 false false), (3, .bottom)] == 0)
  t "a midrule index past the rows clamps to the row count"
    (hdr #[(7, .mid)] == 3)
  t "an empty table has zero header rows whatever its rules"
    (Ir.tableHeaderRows #[] #[(0, .mid), (1, .mid)] == 0)
  -- The typed tree: one header row.
  let tree (src : String) : Html.Node :=
    HtmlDoc.blockNode {} (elabStr (dvDoc "" src)).1.body[0]!
  let one := tree ("\\begin{tabular}{lcr}\\toprule Left & Centre & Right \\\\ " ++
    "\\midrule a & b & c \\\\ d & e & f \\\\ \\bottomrule\\end{tabular}")
  let oneCells := cellFactsOne "" #[] one
  t "one header row: three th under thead, six td under tbody"
    (oneCells.map (fun c => (c.group, c.tag)) ==
      #[("thead", "th"), ("thead", "th"), ("thead", "th"),
        ("tbody", "td"), ("tbody", "td"), ("tbody", "td"),
        ("tbody", "td"), ("tbody", "td"), ("tbody", "td")])
  t "every th declares scope=col and no td carries a scope"
    (oneCells.all fun c => (c.tag == "th") == (c.scope == "col") &&
      (c.tag == "td") == (c.scope == ""))
  t "cell text and order survive the regrouping"
    (oneCells.map (·.text) == #["Left", "Centre", "Right", "a", "b", "c", "d", "e", "f"])
  t "the rule classes stand on the same rows as before"
    (rowClassesOne #[] one == #["bt-heavy-above bt-pre", "bt-light-above", "bt-heavy-below"])
  t "the table ships colgroup, thead, tbody in that order"
    (tableGroupsOne #[] one == #[#["colgroup", "thead", "tbody"]])
  -- Two header rows.
  let two := tree ("\\begin{tabular}{ll}\\toprule A & B \\\\ C & D \\\\ " ++
    "\\midrule e & f \\\\ \\bottomrule\\end{tabular}")
  let twoCells := cellFactsOne "" #[] two
  t "two header rows: four th, two td"
    ((twoCells.filter (·.tag == "th")).size == 4 &&
      (twoCells.filter (·.tag == "td")).size == 2 &&
      (twoCells.filter (·.group == "thead")).size == 4)
  -- No midrule: a cmidrule and a gap must not be mistaken for one.
  let cmid := tree ("\\begin{tabular}{lcr}\\toprule left & centre & right \\\\ " ++
    "\\cmidrule(lr){1-2} a & b & c \\\\ \\addlinespace d & e & f \\\\ " ++
    "\\bottomrule\\end{tabular}")
  let cmidCells := cellFactsOne "" #[] cmid
  t "cmidrule and addlinespace head nothing: nine td, no th, no thead"
    (cmidCells.size == 9 && cmidCells.all (fun c => c.tag == "td" && c.group == "tbody"))
  t "the cmid cell class is where it was"
    (cmidCells.map (·.cls) == #["", "", "", "bt-cmid", "bt-cmid", "", "", "", ""])
  t "no header: colgroup and tbody only"
    (tableGroupsOne #[] cmid == #[#["colgroup", "tbody"]])
  -- Bare tabular, no rules at all.
  let bare := tree "\\begin{tabular}{ll}a & b \\\\ c & d\\end{tabular}"
  t "a rule-less table has no th"
    ((cellFactsOne "" #[] bare).all fun c => c.tag == "td" && c.group == "tbody")
  -- Every row a header row: the midrule stands after the last row.
  let allHead := tree "\\begin{tabular}{ll}\\toprule a & b \\\\ \\midrule\\end{tabular}"
  t "a midrule after the last row heads every row: thead and no tbody"
    (tableGroupsOne #[] allHead == #[#["colgroup", "thead"]] &&
      (cellFactsOne "" #[] allHead).all (·.tag == "th"))
  -- The empty table: nothing to group.
  let empty := HtmlDoc.blockNode {} (.table #[default, default] true true #[] #[(0, .mid)])
  t "an empty table ships its colgroup and no row group"
    (tableGroupsOne #[] empty == #[#["colgroup"]])
  -- The fixture's census: the first table heads one row of three, the
  -- second (cmidrule) none; every declared cell ships once.
  let src ← IO.FS.readFile "tests/corpus/tables.tex"
  let (fixture, _) ← elabFixture "tables" src
  let (_, body, _) := HtmlDoc.emitTree {} fixture
  let cells := cellFactsList "" #[] body.toList
  let declared := Ir.foldBlocks (fun n b => match b with
    | .table _ _ _ rows _ => n + rows.foldl (fun m r => m + r.size) 0
    | _ => n) (fun n _ => n) 0 fixture.body
  t "tables fixture: every declared cell ships once"
    (cells.size == declared && declared == 18)
  t "tables fixture: three th, all under thead with scope=col"
    ((cells.filter (·.tag == "th")).size == 3 &&
      (cells.filter (·.tag == "th")).all (fun c => c.group == "thead" && c.scope == "col") &&
      (cells.filter (·.tag == "td")).all (·.group == "tbody"))
  -- The stylesheet's half of "no movement": each cell rule the header
  -- cells left as `td` addresses `th` too, and the UA's bold/centred
  -- `th` defaults are neutralised.
  let css := HtmlDoc.baseCss {} fixture
  t "the table stylesheet addresses th beside td"
    (hasStr css "table.booktabs th" && hasStr css "tr.bt-heavy-above > th" &&
      hasStr css "tr.bt-light-above > th" && hasStr css "th.bt-cmid" &&
      hasStr css "font-weight: inherit")

/-- A five-object PDF whose one font is the standard `Helvetica`, no
program embedded: the file `pdffonts` reports `emb no` for. Built here, in
Lean, so no binary fixture is checked in — and so the census has a file
the writer never produced to judge. -/
def unembeddedProbePdf : ByteArray := Id.run do
  let content := "BT /F1 12 Tf 10 20 Td (Probe) Tj ET"
  let objs : Array String := #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] \
/Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R >>",
    s!"<< /Length {content.utf8ByteSize} >>\nstream\n{content}\nendstream",
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>"]
  let mut out := "%PDF-1.7\n"
  let mut offs : Array Nat := #[]
  for (o, i) in objs.zipIdx do
    offs := offs.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{o}\nendobj\n"
  let xref := out.utf8ByteSize
  let pad10 (n : Nat) : String :=
    let s := toString n
    String.ofList (List.replicate (10 - s.length) '0') ++ s
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for o in offs do
    out := out ++ s!"{pad10 o} 00000 n \n"
  out := out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n"
  return out.toUTF8

/-- A hand-built cross-reference-stream PDF whose catalog, pages and page
ride in one *uncompressed* object stream: the smallest file on which an
object stream's header can be permuted in place (`swap`), with every
offset unchanged — the mutant that distinguishes a reader that checks the
header's numbers from one that trusts the cross-reference. -/
def objStmPdf (swap : Bool) : ByteArray := Id.run do
  let o1 := "<< /Type /Catalog /Pages 2 0 R >>"
  let o2 := "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"
  let o3 := "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 5 0 R >>"
  let off2 := o1.length + 1
  let off3 := off2 + o2.length + 1
  let hdr := if swap then s!"2 0 1 {off2} 3 {off3}" else s!"1 0 2 {off2} 3 {off3}"
  let stm := hdr ++ " " ++ o1 ++ " " ++ o2 ++ " " ++ o3
  let content := "0 0 1 rg 0 0 50 25 re f"
  let mut out := "%PDF-2.0\n"
  let off4 := out.utf8ByteSize
  out := out ++ s!"4 0 obj\n<< /Type /ObjStm /N 3 /First {hdr.length + 1} \
/Length {stm.utf8ByteSize} >>\nstream\n{stm}\nendstream\nendobj\n"
  let off5 := out.utf8ByteSize
  out := out ++ s!"5 0 obj\n<< /Length {content.utf8ByteSize} >>\nstream\n{content}\nendstream\nendobj\n"
  let off6 := out.utf8ByteSize
  let row (kind f2 f3 : Nat) : ByteArray :=
    ⟨#[UInt8.ofNat kind, UInt8.ofNat (f2 / 16777216), UInt8.ofNat (f2 / 65536 % 256),
      UInt8.ofNat (f2 / 256 % 256), UInt8.ofNat (f2 % 256),
      UInt8.ofNat (f3 / 256 % 256), UInt8.ofNat (f3 % 256)]⟩
  let mut rows := ByteArray.empty
  for r in [row 0 0 65535, row 2 4 0, row 2 4 1, row 2 4 2,
      row 1 off4 0, row 1 off5 0, row 1 off6 0] do
    rows := rows ++ r
  let mut bytes := out.toUTF8
  bytes := bytes ++ s!"6 0 obj\n<< /Type /XRef /Size 7 /W [1 4 2] /Root 1 0 R \
/Length {rows.size} >>\nstream\n".toUTF8
  bytes := bytes ++ rows
  bytes := bytes ++ s!"\nendstream\nendobj\nstartxref\n{off6}\n%%EOF\n".toUTF8
  return bytes

/-- The first occurrence of `needle` in `hay`. -/
def findBytes (hay : ByteArray) (needle : String) (from_ : Nat := 0) : Option Nat := Id.run do
  let p := needle.toUTF8
  if hay.size < p.size then return none
  for i in [from_:hay.size - p.size + 1] do
    let mut ok := true
    for k in [0:p.size] do
      if hay[i + k]? != p[k]? then
        ok := false
        break
    if ok then return some i
  return none

/-- `hay` with the bytes at `[i, i + old.length)` — which must spell `old`
— replaced by `new`. -/
def spliceBytes (hay : ByteArray) (i : Nat) (old new : String) : ByteArray :=
  hay.extract 0 i ++ new.toUTF8 ++ hay.extract (i + old.utf8ByteSize) hay.size

/-- One byte of `hay` inverted. -/
def flipByte (hay : ByteArray) (i : Nat) : ByteArray :=
  match hay[i]? with
  | some v => hay.set! i (v ^^^ 0xFF)
  | none => hay

/-- The corpus fixture's images, read from `tests/corpus/` the way the
driver reads them beside the document (boundary pictures stay unfulfilled:
their placeholder boxes are what an unconverted build ships). -/
def corpusStore (doc : Ir.Doc) : IO Image.Store := do
  let mut fetched : Array (String × Image.Fetch) := #[]
  for src in Ir.imageRefs doc do
    let mut f : Image.Fetch := .missing src
    for cand in Image.sourceCandidates src do
      let p := System.FilePath.mk "tests/corpus" / cand
      if ← p.pathExists then
        f := .decoded (if cand == src then "" else cand) (Image.decode (← IO.FS.readBinFile p))
        break
    fetched := fetched.push (src, f)
  return (Image.fulfil fetched).1

/-- What each golden fixture's PDF carries, read back from its bytes by the
census: `(pages, type0Fonts, images, forms, smasks, linkAnnots,
outlineItems, lang, filters)`. A fixture without a row fails the coverage
check, so a new fixture states what its file carries before it enters —
and a writer change that moves a count is visible here, per fixture. The
PDF is built with the suite's one face and the fixture's own images; a
boundary picture is a placeholder box (no converter runs in the suite). -/
def pdfCensusTable :
    List (String × (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Option String × List String)) := [
  ("paragraphs", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("layout", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("declared", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("fonts", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("palette", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("tokens", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("fill", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("links", (1, 1, 0, 0, 0, 3, 0, none, ["FlateDecode"])),
  ("resume", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("talk", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("deck", (8, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("deck1610", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("themed", (8, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("latex-idioms", (1, 1, 0, 0, 0, 0, 0, some "en", ["FlateDecode"])),
  ("wrapper", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("centering", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("columns", (3, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("overlays", (5, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("overlays-blocks", (12, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("overprint", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("notes", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("furniture", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("chrome", (5, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("footer-left", (4, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("footer-mixed", (5, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("footer-collide", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lists", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lists-styled", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lists-deck", (4, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("headroom", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("marker-styled", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("marker-content", (1, 1, 1, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("trio-page", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("trio-deck", (4, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("trio-card", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("valign", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("images", (1, 1, 4, 0, 1, 0, 0, none, ["DCTDecode", "FlateDecode"])),
  ("figures", (1, 3, 0, 2, 0, 0, 0, none, ["FlateDecode"])),
  ("math", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("webpage", (1, 1, 0, 0, 0, 6, 0, none, ["FlateDecode"])),
  ("quotes", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("quote-deck", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("outline", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("outline-gap", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("webnav", (1, 1, 0, 0, 0, 0, 3, none, ["FlateDecode"])),
  ("bibliography", (1, 1, 0, 0, 0, 9, 0, none, ["FlateDecode"])),
  ("resume-data", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("icons", (1, 1, 0, 0, 0, 2, 0, none, ["FlateDecode"])),
  ("diagram", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("diagram-boundary", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("diagram-overflow", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("diagram-refused", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("diagram-scm", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("diagram-tikzset", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("tables", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("tables-ragged", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("subfigures", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("float-center", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("math-companion", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("math-first", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("math-text", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("greek-literal", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("abstract", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("crossref", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("eqnum", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("footnotes", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("redefine", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("titlebars", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("daylight", (4, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("blocks", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("poster", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("poster-headline", (1, 1, 1, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("listings", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("algorithm", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lineno", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lineno-modulo", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"]))]

/-- The read-side census (`PdfCensus`) and the checked reader beneath it
(`PdfRead.objects`): the probe the writer never made judges as
`pdffonts` does; a copied page carrying an unembedded face makes the
written file's census say so (the fact `Check.Shipped.fontsEmbedded` now
reads); six mutants each refuse by a distinct message; every golden
fixture's PDF reads back with every object under its spelled number and a
census row that matches. -/
def pdfCensusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- The probe: one font, no program.
  let probe := unembeddedProbePdf
  t "probe pdf reads as a form" (PdfRead.readForm probe).isOk
  t "probe census: one unembedded font"
    (match pdfCensusOf probe with
     | .ok c => c.fonts == 1 && c.type0Fonts == 0 && !c.fontsEmbedded && c.pages == 1
     | .error _ => false)
  -- The written file: the suite's face embeds; a copied page's face is
  -- judged from the bytes, where the writer's intent would have said yes.
  let (doc, _) := Elab.run "t" "A line of text."
  let out := layoutOf oneFace doc
  let pdf := Pdf.write {} oneFace out.pages
  t "written pdf census: fonts embedded" ((pdfCensusOf pdf).map (·.fontsEmbedded) == .ok true)
  t "written pdf census: one page, one Type0 font"
    ((pdfCensusOf pdf).map (fun c => (c.pages, c.type0Fonts)) == .ok (1, 1))
  let probeStore : Image.Store := { entries := #[
    { src := "probe.pdf", info := (Image.decode probe).toOption }] }
  let (pdoc, _) := Elab.run "t"
    "\\includegraphics[width=50pt, alt={A copied page}]{probe.pdf}"
  let pout := layoutOf oneFace pdoc {} none probeStore
  let ppdf := Pdf.write {} oneFace pout.pages (imgs := probeStore)
  t "copied unembedded page: the census says not embedded"
    ((pdfCensusOf ppdf).map (fun c => (c.fontsEmbedded, c.forms, c.fonts)) == .ok (false, 1, 3))
  t "copied unembedded page: the xref still verifies" (checkXref ppdf).isOk
  -- Mutants: each refuses, each by its own message — the judge breaks once.
  let mutants : IO (Array (String × ByteArray)) := do
    let some sx := findBytes pdf "startxref\n" | return #[]
    let x ← match PdfRead.readXref pdf with
      | .ok x => pure x
      | .error _ => return #[]
    let startStr := toString x.start
    let some dataStart := (findBytes pdf "stream\n" x.start).map (· + 7) | return #[]
    let es ← match PdfRead.objects pdf with
      | .ok es => pure es.val
      | .error _ => return #[]
    -- A stream whose length keeps its digit count one shorter, so every
    -- offset after it stands.
    let some lenE := es.find? fun e =>
        e.stream.isSome && (match e.val.get? "Length" with
          | some (.int n) => n ≥ 11 && n % 10 != 0
          | _ => false) | return #[]
    let some (.int len) := lenE.val.get? "Length" | return #[]
    let some lenAt := findBytes pdf s!"/Length {len} >>" | return #[]
    -- A page's content stream: a bare deflated dictionary.
    let some cE := es.reverse.find? fun e =>
        e.stream.isSome && (e.val.get? "Type").isNone && (e.val.get? "Subtype").isNone &&
          (e.val.get? "Length1").isNone &&
          PdfCensus.filtersOf e.val == #["FlateDecode"] &&
          (match e.loc with | .direct _ => true | _ => false) | return #[]
    let cOff := match cE.loc with | .direct o => o | _ => 0
    let some cData := (findBytes pdf "stream\n" cOff).map (· + 7) | return #[]
    return #[
      ("truncated", pdf.extract 0 (pdf.size - 40)),
      ("startxref off by one", spliceBytes pdf (sx + 10) startStr (toString (x.start + 1))),
      ("xref row byte flipped", flipByte pdf (dataStart + 10)),
      ("/Length one short", spliceBytes pdf lenAt s!"/Length {len} >>" s!"/Length {len - 1} >>"),
      ("content deflate byte corrupted", flipByte pdf (cData + 5)),
      ("object stream ids swapped", objStmPdf true)]
  let ms ← mutants
  t "six mutants built" (ms.size == 6)
  let mut msgs : Array String := #[]
  for (name, m) in ms do
    match checkXref m with
    | .ok n => t s!"mutant {name} refused (accepted {n})" false
    | .error e =>
      t s!"mutant {name} refused" true
      msgs := msgs.push e
  t "the six refusals are six messages"
    ((msgs.qsort (· < ·)).toList.eraseDups.length == 6)
  t "swapped object stream ids are refused naming the object"
    (match checkXref (objStmPdf true) with
     | .error e => hasStr e "object stream 4" && hasStr e "names 1"
     | .ok _ => false)
  t "the unswapped object stream reads" (checkXref (objStmPdf false) == .ok 3)
  t "startxref one byte early is refused too"
    (match findBytes pdf "startxref\n", PdfRead.readXref pdf with
     | some sx, .ok x =>
       !(checkXref (spliceBytes pdf (sx + 10) (toString x.start) (toString (x.start - 1)))).isOk
     | _, _ => false)
  -- Every golden fixture's PDF, read back through the checked reader.
  for n in goldenNames do
    t s!"pdf census covers {n}" (pdfCensusTable.any (·.1 == n))
  for (n, _) in pdfCensusTable do
    t s!"pdf census row {n} names a golden fixture" (goldenNames.contains n)
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc
    let out := layoutOf oneFace doc geom none store
    let pdf := Pdf.write geom oneFace out.pages doc.info store out.outline
    match PdfRead.objects pdf with
    | .error e => t s!"pdf objects {n}: {e}" false
    | .ok es =>
      let c := PdfCensus.ofEntries ((PdfRead.trailer pdf).toOption.getD (.dict #[])) es.val
      t s!"pdf xref covers {n}" (PdfCensus.xrefCovers c es.val)
      let row := (c.pages, c.type0Fonts, c.images, c.forms, c.smasks, c.linkAnnots,
        c.outlineItems, c.lang, c.filters.toList)
      match pdfCensusTable.find? (·.1 == n) with
      | some (_, want) =>
        t s!"pdf census row {n}: {repr row}" (row == want)
      | none => pure ()
  -- The driver, end to end: the gate reads the census of the bytes it is
  -- about to write, and a failing document writes nothing — not the page,
  -- not the `-o` directory. The binary is this tree's own build; the
  -- fixture ships its face from the corpus, so no host font enters.
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    let dir ← IO.FS.createTempDir
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
      (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf"))
    IO.FS.writeBinFile (dir / "probe.pdf") probe
    let pre := "\\documentclass{article}\n\\usepackage{graphicx}\n\
\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }\n"
    let body := "\\begin{document}\nA probe.\n\n\
\\includegraphics[width=50pt, alt={A copied page}]{probe.pdf}\n\\end{document}\n"
    let run (name decl : String) : IO (UInt32 × String × Bool) := do
      IO.FS.writeFile (dir / s!"{name}.tex") (pre ++ decl ++ body)
      let outDir := dir / s!"out-{name}"
      let r ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := #[(dir / s!"{name}.tex").toString, "-o", outDir.toString ++ "/"] }
      return (r.exitCode, r.stdout ++ r.stderr, ← outDir.pathExists)
    let (code, log, dirExists) ← run "control" ""
    t s!"driver control builds the probe document: {log}" (code == 0 && dirExists)
    t "driver control ships the copied unembedded face"
      ((pdfCensusOf (← IO.FS.readBinFile (dir / "out-control" / "control.pdf"))).map
        (·.fontsEmbedded) == .ok false)
    let (code, log, dirExists) ← run "embed" "\\assert{ fonts.all_embedded }\n"
    t s!"driver: fonts.all_embedded fails on the copied face (E0330): {log}"
      (code != 0 && hasStr log "E0330" && hasStr log "fonts.all_embedded")
    t "driver: the failing assertion wrote nothing, not even the -o directory" (!dirExists)
    let (code, _, dirExists) ← run "both"
      "\\output{ formats = pdf, html }\n\\assert{ pages == 99 }\n"
    t "driver: pdf+html with a failing assertion writes nothing" (code != 0 && !dirExists)
    IO.FS.removeDirAll dir

/-- Synthetic pages exercising every content-stream operator the writer
emits: glyph runs that join one `TJ` array, a gap as an adjustment, a face
and colour change, a raised run, a CMYK colour, expansion (`Tz`) turned on
and back off, a kern, a move too large for an adjustment, a rule and
images (loaded, failed, and unnamed), page fills, and every picture path
shape with every paint combination. -/
def contentOpsRed : Ir.Color := { r := 200, g := 30, b := 30 }
def contentOpsGrey : Ir.Color := { r := 240, g := 240, b := 240 }
def contentOpsCyan : Ir.Color := Ir.Color.ofCmyk 1000 0 0 0

def contentOpsRun (idx : Nat) (color : Ir.Color) (w : Dim.Sp) (glyphs : List (Nat × Char))
    (size : Dim.Sp := 0) (raise : Dim.Sp := 0) : Layout.Seg :=
  .run idx color none w glyphs.toArray size false raise none (.leaf 0)

/-- The leaf tags the synthetic pages are marked under: leaf 0 a paragraph,
leaf 1 a heading, leaf 2 a leaf no element holds. -/
def contentOpsTags : Array (Option String) := #[some "P", some "H2", none]

def contentOpsTextPage : Layout.PageOut := {
  lines := #[
    { x := Dim.pt 10, y := Dim.pt 20, size := Dim.pt 12, setWidth := Dim.pt 100, leaf := some 0, segs := #[
        contentOpsRun 0 Ir.Color.black (Dim.pt 30) [(36, 'A'), (37, 'B')],
        .gap (Dim.pt 5) true,
        contentOpsRun 0 Ir.Color.black (Dim.pt 20) [(38, 'C')],
        contentOpsRun 1 contentOpsRed (Dim.pt 20) [(39, 'D')] (Dim.pt 9) (Dim.pt 3),
        contentOpsRun 1 contentOpsRed (Dim.pt 20) [(40, 'E')] (Dim.pt 9) (Dim.pt 3) ] },
    { x := Dim.pt 10, y := Dim.pt 40, size := Dim.pt 12, setWidth := Dim.pt 100, expand := 20,
      leaf := some 1, segs := #[
        contentOpsRun 0 contentOpsCyan (Dim.pt 30) [(70000, 'x'), (4096, 'y')],
        .gap (Dim.pt 5) true,
        contentOpsRun 0 contentOpsCyan (Dim.pt 30) [(1, 'z')] ] },
    { x := Dim.pt 10, y := Dim.pt 60, size := Dim.pt 12, setWidth := Dim.pt 100, leaf := some 2, segs := #[
        contentOpsRun 0 Ir.Color.black (Dim.pt 2) [],
        contentOpsRun 0 Ir.Color.black (Dim.pt 10) [(50, 'a')],
        .gap (Dim.pt 500) true,
        contentOpsRun 0 Ir.Color.black (Dim.pt 10) [(51, 'b')],
        contentOpsRun 0 Ir.Color.black (Dim.pt 10) [(52, 'c')] (Dim.pt 12) (Dim.pt (-3)),
        contentOpsRun 0 Ir.Color.black (Dim.pt 10) [(53, 'd')] (Dim.pt 12) (Dim.pt (-3)) ] },
    { x := Dim.pt 10, y := Dim.pt 80, size := Dim.pt 12, setWidth := Dim.pt 100, segs := #[
        .rule (Dim.pt 40) (Dim.pt 1) (Dim.pt 2) contentOpsRed,
        .image (some 0) (Dim.pt 20) (Dim.pt 15),
        .image (some 1) (Dim.pt 20) (Dim.pt 15),
        .image none (Dim.pt 10) (Dim.pt 5),
        contentOpsRun 0 Ir.Color.black (Dim.pt 10) [(54, 'e')],
        .rule (Dim.pt 10) (Dim.pt 2) 0 Ir.Color.black ] } ],
  fills := #[{ x := 0, y := 0, w := Dim.pt 200, h := Dim.pt 100, color := contentOpsGrey },
             { x := Dim.pt 5, y := Dim.pt 5, w := Dim.pt 50, h := Dim.pt 10, color := contentOpsCyan }] }

/-- Two pictures' paths: the first three stamped with leaf 0, the last two
with leaf 1 (`contentOpsTags` gives both a holder), so the writer groups
them as two figures. -/
def contentOpsPathPage : Layout.PageOut := {
  paths := #[
    { path := .circle (Dim.pt 50) (Dim.pt 50) (Dim.pt 20),
      stroke := some { color := contentOpsRed, dash := .dashed }, leaf := some 0 },
    { path := .rect (Dim.pt 10) (Dim.pt 10) (Dim.pt 30) (Dim.pt 20), stroke := some { dash := .dotted, width := Dim.pt 1 },
      fill := some contentOpsGrey, leaf := some 0 },
    { path := .segs #[.line (Dim.pt 1) (Dim.pt 2) (Dim.pt 3) (Dim.pt 4), .line (Dim.pt 3) (Dim.pt 4) (Dim.pt 5) (Dim.pt 6),
        .cubic (Dim.pt 7) (Dim.pt 8) (Dim.pt 9) (Dim.pt 10) (Dim.pt 11) (Dim.pt 12) (Dim.pt 13) (Dim.pt 14),
        .cubic (Dim.pt 13) (Dim.pt 14) (Dim.pt 1) (Dim.pt 1) (Dim.pt 2) (Dim.pt 2) (Dim.pt 3) (Dim.pt 3)],
      stroke := some {}, leaf := some 0 },
    { path := .tri (Dim.pt 1) (Dim.pt 2) (Dim.pt 3) (Dim.pt 4) (Dim.pt 5) (Dim.pt 6), fill := some contentOpsRed,
      leaf := some 1 },
    { path := .rect (Dim.pt 1) (Dim.pt 1) (Dim.pt 2) (Dim.pt 2), leaf := some 1 } ] }

/-- The streams the writer produced for these pages before the typed
layer existed — captured from `Pdf.pageStreams`, and the spelling the
typed operators must reproduce byte for byte. -/
def contentOpsTextExpected : String :=
  "q 0.941 0.941 0.941 rg 0 0 200 100 re f Q\n" ++
  "q 1 0 0 0 k 5 85 50 10 re f Q\n" ++
  "BT\n1 0 0 1 10 80 Tm\n/F1 12 Tf\n[<00240025>-416<0026>] TJ\n" ++
  "1 0 0 1 65 83 Tm\n/F2 9 Tf\n0.784 0.118 0.118 rg\n[<0027><0028>] TJ\n" ++
  "102.0 Tz\n1 0 0 1 10 60 Tm\n/F1 12 Tf\n1 0 0 0 k\n[<11701000>-407<0001>] TJ\n" ++
  "100.0 Tz\n1 0 0 1 12 40 Tm\n0 0 0 rg\n[<0032>] TJ\n1 0 0 1 522 40 Tm\n[<0033>] TJ\n" ++
  "1 0 0 1 532 37 Tm\n[<0034><0035>] TJ\n1 0 0 1 100 20 Tm\n[<0036>] TJ\nET\n" ++
  "q 20 0 0 15 50 20 cm /Im1 Do Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 70 20 20 15 re S Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 90 20 10 5 re S Q\n" ++
  "q 0.784 0.118 0.118 rg 10 22 40 1 re f Q\n" ++
  "q 0 0 0 rg 110 20 10 2 re f Q"

def contentOpsPathExpected : String :=
  "q 0.784 0.118 0.118 RG 0.4 w [3 3] 0 d 70 50 m 70 61.046 61.046 70 50 70 c " ++
  "38.954 70 30 61.046 30 50 c 30 38.954 38.954 30 50 30 c 61.046 30 70 38.954 70 50 c h S Q\n" ++
  "q 0.941 0.941 0.941 rg 0 0 0 RG 1 w [1 1] 0 d 10 70 30 20 re B Q\n" ++
  "q 0 0 0 RG 0.4 w 1 98 m 3 96 l 5 94 l 7 92 m 9 90 11 88 13 86 c 1 99 2 98 3 97 c S Q\n" ++
  "q 0.784 0.118 0.118 rg 1 98 m 3 96 l 5 94 l h f Q\n" ++
  "q 1 97 2 2 re n Q\n" ++
  "BT\nET"

/-- The same pages under a 3 pt bleed: every coordinate shifts by the
bleed and nothing else changes. -/
def contentOpsBleedExpected : String :=
  "q 0.941 0.941 0.941 rg 3 3 200 100 re f Q\n" ++
  "q 1 0 0 0 k 8 88 50 10 re f Q\n" ++
  "BT\n1 0 0 1 13 83 Tm\n/F1 12 Tf\n[<00240025>-416<0026>] TJ\n" ++
  "1 0 0 1 68 86 Tm\n/F2 9 Tf\n0.784 0.118 0.118 rg\n[<0027><0028>] TJ\n" ++
  "102.0 Tz\n1 0 0 1 13 63 Tm\n/F1 12 Tf\n1 0 0 0 k\n[<11701000>-407<0001>] TJ\n" ++
  "100.0 Tz\n1 0 0 1 15 43 Tm\n0 0 0 rg\n[<0032>] TJ\n1 0 0 1 525 43 Tm\n[<0033>] TJ\n" ++
  "1 0 0 1 535 40 Tm\n[<0034><0035>] TJ\n1 0 0 1 103 23 Tm\n[<0036>] TJ\nET\n" ++
  "q 20 0 0 15 53 23 cm /Im1 Do Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 73 23 20 15 re S Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 93 23 10 5 re S Q\n" ++
  "q 0.784 0.118 0.118 rg 13 25 40 1 re f Q\n" ++
  "q 0 0 0 rg 113 23 10 2 re f Q"

/-- The stream with its marked-content lines removed: what the artifact
acceptance strips from the file, spelled on the string. `Pdf.stripMarks`
is the same operation on the typed line list; the per-page row "stripping
the marked-content lines of the file is stripping the typed lines" in
`artifactMarkChecks` is the bridge between them. -/
def stripMarkLines (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").filter fun l =>
    !(l == "EMC" || l.endsWith " BDC" || l.endsWith " BMC"))

/-- The typed content operators render, with their marked-content lines
removed, byte for byte to the stream the writer wrote before they existed
(`contentOps_text` holds the glyph census, `mark_ink_exact` the ink; this
block holds the spelling). -/
def contentOpsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := { pageW := Dim.pt 200, pageH := Dim.pt 100 }
  let bleed : Layout.Geom := { geom with bleed := Dim.pt 3 }
  let remap : Array Nat := #[0, 1]
  let imgMap : Array (Option Nat) := #[some 0, none]
  let tags := contentOpsTags
  let plain (g : Layout.Geom) (p : Layout.PageOut) : String :=
    Pdf.render (Pdf.contentOpsPlain g remap imgMap tags p)
  let stripped (g : Layout.Geom) (p : Layout.PageOut) : String :=
    stripMarkLines (Pdf.render (Pdf.contentOps g remap imgMap tags p))
  let ink (g : Layout.Geom) (p : Layout.PageOut) : String :=
    Pdf.render (Pdf.inkOps (Pdf.contentOps g remap imgMap tags p))
  t "content ops: text, fills, images and rules render to the recorded stream"
    (plain geom contentOpsTextPage == contentOpsTextExpected)
  t "content ops: every path shape and paint renders to the recorded stream"
    (plain geom contentOpsPathPage == contentOpsPathExpected)
  t "content ops: an empty page is one empty text object"
    (plain geom {} == "BT\nET" && stripped geom {} == "BT\nET")
  t "content ops: the bleed shifts every coordinate and nothing else"
    (plain bleed contentOpsTextPage == contentOpsBleedExpected)
  t "content ops: the marked stream stripped of its marked-content lines is the recorded stream"
    (stripped geom contentOpsTextPage == contentOpsTextExpected
      && stripped geom contentOpsPathPage == contentOpsPathExpected
      && stripped bleed contentOpsTextPage == contentOpsBleedExpected)
  t "content ops: the ink under the wrappers renders to the recorded stream"
    (ink geom contentOpsTextPage == contentOpsTextExpected
      && ink geom contentOpsPathPage == contentOpsPathExpected
      && ink bleed contentOpsTextPage == contentOpsBleedExpected)
  -- The executable twin of `contentOps_text`, on the synthetic pages.
  t "content ops: the glyph census is the page's runs"
    (Pdf.runsOf (Pdf.contentOps geom remap imgMap tags contentOpsTextPage)
      == Pdf.pageRuns contentOpsTextPage)
  -- Two spellings that coincide: the honest bound on injectivity.
  t "content ops: a fill and a fill-only rectangle path spell the same"
    (Pdf.render #[.fill contentOpsRed 1 2 3 4]
      == Pdf.render #[.path (some contentOpsRed) none #[.rect 1 2 3 4]])
  -- `write` and `pageStreams` read the typed layer: the public entry
  -- yields the same bytes for the same pages.
  let some fontData ← findFont | return ()
  let .ok font := Font.parse fontData | return ()
  let twoFace : Font.FontSet := { fonts := #[font, font] }
  let png ← IO.FS.readBinFile "tests/corpus/rects.png"
  let store : Image.Store := { entries := #[
    { src := "a.png", info := (Image.decode png).toOption }, { src := "b.png" }] }
  let streams := Pdf.pageStreams geom twoFace #[contentOpsTextPage, contentOpsPathPage] store
  t "content ops: pageStreams is the typed render, stripped to the recorded stream"
    (streams.map (stripMarkLines <| String.fromUTF8! ·)
      == #[contentOpsTextExpected, contentOpsPathExpected])

/-- The output contract: declared facts held against each artifact's
realization record (one W0701 per unmet fact per artifact), the font
policy's one resolving site, and the byte-reading assertion judged on the
bytes the run emits — failing loud when it emits none of them. -/
def outputContractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let out (decl : String) : Ir.Doc × Array Diag := elabStr (dvDoc s!"\\output\{ {decl} }\n" "x")
  let w0701 (c : Ir.OutputContract) (r : Ir.Realization) : Array Diag :=
    Ir.contractDiags (c.unmet r)
  -- Red 1: the alternatives fact, declared and held against each record.
  let (d1, ds1) := out "formats = pdf, alternatives = required"
  t "contract: 'alternatives = required' is a known key"
    (!ds1.any fun d => d.code == "E0322" || d.code == "E0321")
  t "contract: 'alternatives = required' lands in the contract"
    (d1.output.contract.alternatives == .required)
  t "contract: the PDF realizes no alternative channel → one W0701 naming it"
    (match w0701 d1.output.contract Pdf.profile with
     | #[w] => w.code == "W0701" && w.subject == some "alternatives"
     | _ => false)
  t "contract: the HTML carries alt → no W0701"
    ((w0701 d1.output.contract HtmlDoc.profile).isEmpty)
  -- Red 2: the colour fact.
  let (d2, ds2) := out "formats = pdf, color = srgb"
  t "contract: 'color = srgb' is a known key" (!ds2.any (·.code == "E0322"))
  t "contract: device colour in the PDF → one W0701 naming color"
    (match w0701 d2.output.contract Pdf.profile with
     | #[w] => w.subject == some "color"
     | _ => false)
  t "contract: CSS colour is sRGB by definition → no W0701"
    ((w0701 d2.output.contract HtmlDoc.profile).isEmpty)
  -- Two unmet facts are two warnings, never one.
  let (d12, _) := out "formats = pdf, alternatives = required, color = srgb"
  t "contract: two unmet facts are two W0701s"
    ((w0701 d12.output.contract Pdf.profile).size == 2)
  -- A bad value is E0321 in the existing style; the key is still known.
  t "contract: an unknown alternatives value is E0321"
    ((out "alternatives = maybe").2.any fun d =>
      d.code == "E0321" && hasStr d.message "maybe")
  t "contract: an unknown colour intent is E0321"
    ((out "color = cmyk").2.any (·.code == "E0321"))
  t "contract: an unknown font policy is E0321"
    ((out "fonts = subset").2.any (·.code == "E0321"))
  -- The defaults meet every artifact (the theorems say so; this is the
  -- executable face of the same fact over the elaborated default).
  let (d0, _) := out "formats = pdf, html"
  t "contract: an undeclared contract is met by both records"
    ((d0.output.contract.unmet Pdf.profile).isEmpty &&
     (d0.output.contract.unmet HtmlDoc.profile).isEmpty)
  -- The font policy's one resolving site: declared wins, else the css rule.
  t "font policy: undeclared with no css story ships faces"
    (d0.fontPolicy == .embedded)
  t "font policy: undeclared with css = own ships none"
    ((out "formats = html, css = own").1.fontPolicy == .none)
  t "font policy: 'fonts = embedded' beside css = own opts back in"
    ((out "formats = html, css = own, fonts = embedded").1.fontPolicy == .embedded)
  t "font policy: 'fonts = none' with no css story ships none"
    ((out "formats = html, fonts = none").1.fontPolicy == .none)
  let (dLast, _) := elabStr (dvDoc "\\output{ fonts = none }\n\\output{ fonts = embedded }\n" "x")
  t "font policy: the later declaration wins" (dLast.fontPolicy == .embedded)
  -- `reads`: the closed table, executable.
  t "reads: layout assertions read no artifact"
    ((Ir.AssertKind.pages .eq 1).reads.isEmpty && Ir.AssertKind.textInArea.reads.isEmpty &&
     (Ir.AssertKind.minXHeight 0).reads.isEmpty && Ir.AssertKind.accessibilityAA.reads.isEmpty)
  t "reads: fonts.all_embedded reads the two artifacts that carry faces"
    (Ir.AssertKind.fontsAllEmbedded.reads == #["pdf", "html"])
  -- The driver, end to end, on this tree's own binary and the corpus face.
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds for the contract checks:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    let dir ← IO.FS.createTempDir
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
      (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf"))
    let pre (cls : String) := s!"\\documentclass\{{cls}}\n\
\\fonts\{ dir = \"fonts\", body = \"Source Serif Pro\" }\n"
    let one := "\\begin{document}\nA probe.\n\\end{document}\n"
    let three := "\\begin{document}\nA.\n\\pagebreak\nB.\n\\pagebreak\nC.\n\\end{document}\n"
    let run (name cls decl body : String) : IO (UInt32 × String × System.FilePath) := do
      IO.FS.writeFile (dir / s!"{name}.tex") (pre cls ++ decl ++ body)
      let outDir := dir / s!"out-{name}"
      let r ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := #[(dir / s!"{name}.tex").toString, "-o", outDir.toString ++ "/"] }
      return (r.exitCode, r.stdout ++ r.stderr, outDir)
    let count (log needle : String) : Nat := (log.splitOn needle).length - 1
    -- Red 1 and 2 through the driver: one W0701 per artifact that lacks the fact.
    let (code, log, _) ← run "alt-pdf" "article"
      "\\output{ formats = pdf, alternatives = required }\n" one
    t s!"driver: pdf + alternatives = required builds with one W0701: {log}"
      (code == 0 && count log "warning[W0701]" == 1 && hasStr log "alternatives = required")
    let (code, log, _) ← run "alt-html" "article"
      "\\output{ formats = html, alternatives = required }\n" one
    t "driver: html + alternatives = required builds with no W0701"
      (code == 0 && count log "W0701" == 0)
    let (code, log, _) ← run "alt-both" "article"
      "\\output{ formats = pdf, html, alternatives = required }\n" one
    t "driver: pdf+html + alternatives = required warns once, for the PDF"
      (code == 0 && count log "warning[W0701]" == 1)
    let (code, log, _) ← run "srgb-pdf" "article" "\\output{ formats = pdf, color = srgb }\n" one
    t "driver: pdf + color = srgb builds with one W0701"
      (code == 0 && count log "warning[W0701]" == 1 && hasStr log "color = srgb")
    let (code, log, _) ← run "srgb-html" "article" "\\output{ formats = html, color = srgb }\n" one
    t "driver: html + color = srgb builds with no W0701" (code == 0 && count log "W0701" == 0)
    -- Red 3: css = own ships no face, so the assertion fails; `fonts =
    -- embedded` is the opt-in that ships `.fonts/` and passes it.
    let (code, log, outDir) ← run "own" "article"
      "\\output{ formats = html, css = own }\n\\assert{ fonts.all_embedded }\n" one
    t s!"driver: css = own + fonts.all_embedded is E0330: {log}"
      (code != 0 && hasStr log "E0330" && !(← outDir.pathExists))
    let (code, log, outDir) ← run "optin" "article"
      "\\output{ formats = html, css = own, fonts = embedded }\n\\assert{ fonts.all_embedded }\n" one
    t s!"driver: css = own + fonts = embedded passes the assertion: {log}" (code == 0)
    t "driver: fonts = embedded publishes the face beside the page"
      ((← (outDir / "optin.fonts").isDir) &&
       !(← (outDir / "optin.fonts").readDir).isEmpty)
    let (code, _, outDir) ← run "optout" "article" "\\output{ formats = html, fonts = none }\n" one
    t "driver: fonts = none with no css story ships no faces"
      (code == 0 && !(← (outDir / "optout.fonts").pathExists))
    -- Red 4: layout assertions judge the layout whatever is emitted.
    let (code, log, _) ← run "three" "article" "\\output{ formats = html }\n\\assert{ pages == 3 }\n" three
    t s!"driver: html-only pages == 3 holds on a three-page layout: {log}" (code == 0)
    let (code, log, _) ← run "one" "article" "\\output{ formats = html }\n\\assert{ pages == 3 }\n" one
    t "driver: html-only pages == 3 fails on one page with the layout's actual"
      (code != 0 && hasStr log "E0330" && hasStr log "(actual: 1)")
    let (code, log, _) ← run "resume" "resume" "\\output{ formats = html }\n" one
    t s!"driver: an html-only résumé builds clean under its implied assertions: {log}" (code == 0)
    -- Red 5: the one fail-loud case — a byte-reading assertion with no
    -- artifact to read.
    let (code, log, outDir) ← run "md" "article" "\\output{ formats = md }\n\\assert{ fonts.all_embedded }\n" one
    t s!"driver: md-only fonts.all_embedded fails loud (E0330): {log}"
      (code != 0 && hasStr log "E0330" && hasStr log "no emitted artifact carries this measurement" &&
       !(← outDir.pathExists))
    IO.FS.removeDirAll dir

/-- The allocation contract as one statement, from the two theorems the
object table exists for: the ids are pairwise distinct (`objTable_inj`)
and are exactly `[1, size)` (`objTable_covers` with `objTable_between`). -/
theorem objTable_ids_set_eq (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems : Nat) :
    (Pdf.objTable keep imgs usedImgs np nOut nElems).ids.toList.Nodup ∧
    ∀ id, id ∈ (Pdf.objTable keep imgs usedImgs np nOut nElems).ids ↔
      1 ≤ id ∧ id < (Pdf.objTable keep imgs usedImgs np nOut nElems).size :=
  ⟨Pdf.objTable_inj keep imgs usedImgs np nOut nElems, fun id =>
    ⟨Pdf.objTable_between keep imgs usedImgs np nOut nElems id,
     fun h => Pdf.objTable_covers keep imgs usedImgs np nOut nElems id h.1 h.2⟩⟩

/-- Every object id the writer's cross-reference lists is allocated by one
table (`Pdf.objTable`), read back through the engine's own reader: the
table's ids are exactly the objects the file carries, per corpus fixture,
and the row kind of an id is `kindOf`'s answer, never a default. -/
def objTableChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- One face, one page, nothing else: 1 catalog, 2 pages, four font ids,
  -- the file, the page pair, then Info, XMP, the object stream, the xref.
  -- The structure block sits between the outline and XMP: root, parent
  -- tree, namespace, then one id per element (here the `Document` alone).
  let t0 := Pdf.objTable #[0] {} #[] 1 0 1
  t "table: the font block is four ids then the file"
    (Pdf.ObjTable.type0Id 0 == 3 && Pdf.ObjTable.cidId 0 == 4 && Pdf.ObjTable.fdId 0 == 5 &&
     Pdf.ObjTable.toUniId 0 == 6 && t0.fileId 0 == 7)
  t "table: one face, one page, no outline, one structure element"
    (t0.pageId 0 == 8 && t0.contentId 0 == 9 && t0.infoId == 10 && t0.structTreeRoot == 11 &&
     t0.parentTree == 12 && t0.namespaceId == 13 && t0.structElemId 0 == 14 && t0.xmpId == 15 &&
     t0.objStmId == 16 && t0.xrefId == 17 && t0.size == 18 && t0.nf == 1 && t0.np == 1)
  t "table: the conditional families allocate nothing yet"
    (t0.outputIntent.isNone && t0.icc.isNone)
  -- Two faces, three pages, a two-item outline: the root then its items
  -- sit between Info and the structure block.
  let t1 := Pdf.objTable #[0, 2] {} #[] 3 2 0
  t "table: two faces, three pages, an outline"
    (t1.fileId 1 == 12 && t1.pageId 2 == 17 && t1.contentId 2 == 18 && t1.infoId == 19 &&
     t1.outlineRootId == 20 && t1.outlineItemId 1 == 22 && t1.structTreeRoot == 23 &&
     t1.structBase == 26 && t1.xmpId == 26 && t1.xrefId == 28 && t1.size == 29)
  -- Images: a plain raster is one id; an alpha raster brings its SMask; a
  -- copied page brings its resource graph, one id per object; a placeholder
  -- (no info) brings nothing beyond its own slot.
  let png ← IO.FS.readBinFile "tests/corpus/rects.png"
  let rgbaRaw := bytes ([0, 10, 20, 30, 255, 40, 50, 60, 128] ++ [1, 5, 5, 5, 7, 1, 2, 3, 9])
  let rgbaPng := mkPng (pngChunk "IHDR" (pngIhdr 2 2 8 6 0) ++
    pngChunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ pngChunk "IEND" [])
  let store : Image.Store := { entries := #[
    { src := "plain.png", info := (Image.decode png).toOption },
    { src := "alpha.png", info := (Image.decode rgbaPng).toOption },
    { src := "form.pdf", info := (Image.decode unembeddedProbePdf).toOption },
    { src := "missing.png" }] }
  let formN := match (store.get? 2).bind (·.info) with
    | some inf => match inf.form with
      | some f => f.val.objects.size
      | none => 0
    | none => 0
  t "table: the copied page brings its font dictionary" (formN == 1)
  let ti := Pdf.objTable #[0] store #[0, 1, 2, 3] 2 0 0
  t "table: an XObject per image, then what it brings"
    (ti.imgIds == #[8, 9, 11, 12 + formN] && ti.smaskIds == #[none, some 10, none, none] &&
     ti.formBases == #[none, none, some 12, none] && ti.formSizes == #[0, 0, formN, 0] &&
     ti.ni == 4)
  t "table: the pages follow the last image block"
    (ti.pageId 0 == 13 + formN && ti.contentId 1 == 16 + formN && ti.infoId == 17 + formN &&
     ti.size == 24 + formN)
  -- The executable twin of `objTable_ids_set_eq`, on the shapes above.
  for (name, tb) in [("plain", t0), ("outline", t1), ("images", ti)] do
    t s!"table {name}: the ids are exactly [1, size)"
      (tb.ids.toList == List.range' 1 (tb.size - 1))
  -- The row kind is a function of the table and the object stream's index.
  let cidx : Nat → Option Nat := fun id => if id == 1 then some 0 else if id == 2 then some 1 else none
  t "kindOf: xref, in-stream, direct — and none outside the table"
    (ti.kindOf cidx ti.xrefId == some .xref && ti.kindOf cidx 1 == some (.inStream 0) &&
     ti.kindOf cidx 2 == some (.inStream 1) && ti.kindOf cidx 8 == some .direct &&
     ti.kindOf cidx 0 == none && ti.kindOf cidx ti.size == none)
  -- Every corpus PDF, read back: the objects the file carries are the
  -- table's ids, in order, and the trailer's /Size is the table's.
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc
    let out := layoutOf oneFace doc geom none store
    let tree := Struct.ofDoc (Layout.pdfView doc)
    let tb := Pdf.tableOf oneFace out.pages store out.outline tree
    t s!"table {n}: nodup, covering [1, size)"
      (tb.ids.toList.Nodup && tb.ids.size + 1 == tb.size)
    let pdf := Pdf.write geom oneFace out.pages doc.info store out.outline (tree := tree)
    match PdfRead.objects pdf with
    | .error e => t s!"table {n}: objects: {e}" false
    | .ok es =>
      t s!"table {n}: the file's objects are the table's ids" (es.val.map (·.num) == tb.ids)
      t s!"table {n}: the trailer's /Size is the table's"
        ((((PdfRead.trailer pdf).toOption.bind (·.get? "Size")).bind PdfRead.Obj.int?)
          == some (tb.size : Int))

/-- One page placing the store's first image: the shape whose store
decides the census's image rows. -/
def featurePlacingPages : Array Layout.PageOut :=
  #[{ lines := #[
    { x := Dim.pt 10, y := Dim.pt 40, size := Dim.pt 10, setWidth := Dim.pt 100,
      segs := #[.image (some 0) (Dim.pt 20) (Dim.pt 15)] }] }]

/-- The typed feature census: the registry (`Feature.all` derived and
closed, names one-to-one with rows), `features` on the shapes that decide
each row — a soft-mask image says `smask`, a plain one does not, a copied
page says `formXObject` and `copiedGraph`, a JPEG says `dct` — and, over
every corpus fixture, the four unemitted features stay unreached while
the bookkeeping five — the structure tree among them — are always
reached. -/
def featureCensusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  t "features: the registry counts its constructors"
    (Pdf.Feature.all.length == Pdf.Feature.count && Pdf.Feature.all.Nodup)
  t "features: every row name reads back to its feature"
    (Pdf.Feature.all.all fun f => Pdf.Feature.ofName? f.name == some f)
  t "features: row names are distinct" ((Pdf.Feature.all.map Pdf.Feature.name).Nodup)
  t "features: an unknown row name is nobody's" (Pdf.Feature.ofName? "hologram").isNone
  -- One page placing one image; the store decides the row.
  let png ← IO.FS.readBinFile "tests/corpus/rects.png"
  let jpg ← IO.FS.readBinFile "tests/corpus/rects.jpg"
  let rgbaRaw := bytes ([0, 10, 20, 30, 255, 40, 50, 60, 128] ++ [1, 5, 5, 5, 7, 1, 2, 3, 9])
  let rgbaPng := mkPng (pngChunk "IHDR" (pngIhdr 2 2 8 6 0) ++
    pngChunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ pngChunk "IEND" [])
  let geom : Layout.Geom := {}
  let placing := featurePlacingPages
  let storeOf (src : String) (data : ByteArray) : Image.Store :=
    { entries := #[{ src, info := (Image.decode data).toOption }] }
  let feats (src : String) (data : ByteArray) : Array Pdf.Feature :=
    Pdf.features geom oneFace placing (storeOf src data)
  let alpha := feats "alpha.png" rgbaPng
  t s!"features: an alpha PNG reaches smask and the predictor: {repr alpha}"
    (alpha.contains .smask && alpha.contains .flatePredictor15 && !alpha.contains .dct)
  let plain := feats "plain.png" png
  t s!"features: an opaque PNG reaches the predictor and no smask: {repr plain}"
    (!plain.contains .smask && plain.contains .flatePredictor15 && !plain.contains .dct)
  let jpeg := feats "photo.jpg" jpg
  t s!"features: a JPEG reaches dct alone: {repr jpeg}"
    (jpeg.contains .dct && !jpeg.contains .smask && !jpeg.contains .flatePredictor15)
  let form := feats "page.pdf" unembeddedProbePdf
  t s!"features: a copied page reaches the form and its graph: {repr form}"
    (form.contains .formXObject && form.contains .copiedGraph && !form.contains .dct)
  let missing := Pdf.features geom oneFace placing { entries := #[{ src := "gone.png" }] }
  t s!"features: a placeholder reaches no image feature: {repr missing}"
    (!missing.contains .smask && !missing.contains .formXObject && !missing.contains .dct &&
     !missing.contains .flatePredictor15)
  -- Every placing is under a wrapper (pdf-tag-skeleton): the placeholder's
  -- box a layout artifact, the loaded image of a leafless line a bare one.
  t "features: a placed image reaches marked content, loaded or not"
    (missing.contains .markedContent && plain.contains .markedContent)
  let bare := Pdf.features geom oneFace #[]
  t s!"features: no pages reach the bookkeeping three, the stand-in face, and the structure tree: {repr bare}"
    (bare == #[.xrefStream, .objStm, .cidFontType2, .xmp, .structTree])
  t "features: a bleed reaches the trim box"
    ((Pdf.features { geom with bleed := Dim.pt 3 } oneFace #[]).contains .trimBox &&
     !bare.contains .trimBox)
  t "features: an outline reaches outlines; a URI-only item reaches link-uri too"
    (let o := Pdf.features geom oneFace #[] {} #[{ title := "a", page := some 0 }]
     let u := Pdf.features geom oneFace #[] {} #[{ title := "a", url := some "https://example.org" }]
     o.contains .outlines && !o.contains .linkURI && u.contains .outlines && u.contains .linkURI)
  -- The census over the corpus: the four unemitted features never, the
  -- bookkeeping five always, and the census is in registry order.
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc
    let out := layoutOf oneFace doc geom none store
    let fs := Pdf.features geom oneFace out.pages store out.outline
    t s!"features {n}: never tabs, transparency groups, Brotli or JPX"
      (!fs.contains .tabs && !fs.contains .transparencyGroup && !fs.contains .brotli &&
       !fs.contains .jpx)
    t s!"features {n}: always the cross-reference stream, the object stream, XMP, the structure tree, one CIDFontType2"
      (fs.contains .xrefStream && fs.contains .objStm && fs.contains .xmp &&
       fs.contains .structTree && fs.contains .cidFontType2 && !fs.contains .cidFontType0)
    t s!"features {n}: in registry order, once each"
      (fs.toList == Pdf.Feature.all.filter fs.contains)

/-- The recorded text page under the marking layer: the fills as one bare
`/Artifact` block, the paragraph and heading lines as `/P` and `/H2`
sequences numbered 0 and 1, the line whose leaf no element holds and the
leafless line as bare artifacts, the loaded image of the leafless line a
bare artifact, each placeholder under `/Layout`, the rules as one
`/Layout` block. -/
def artifactTextExpected : String :=
  "/Artifact BMC\nq 0.941 0.941 0.941 rg 0 0 200 100 re f Q\n" ++
  "q 1 0 0 0 k 5 85 50 10 re f Q\nEMC\n" ++
  "BT\n/P << /MCID 0 >> BDC\n1 0 0 1 10 80 Tm\n/F1 12 Tf\n[<00240025>-416<0026>] TJ\n" ++
  "1 0 0 1 65 83 Tm\n/F2 9 Tf\n0.784 0.118 0.118 rg\n[<0027><0028>] TJ\nEMC\n" ++
  "/H2 << /MCID 1 >> BDC\n102.0 Tz\n1 0 0 1 10 60 Tm\n/F1 12 Tf\n1 0 0 0 k\n" ++
  "[<11701000>-407<0001>] TJ\nEMC\n" ++
  "/Artifact BMC\n100.0 Tz\n1 0 0 1 12 40 Tm\n0 0 0 rg\n[<0032>] TJ\n1 0 0 1 522 40 Tm\n" ++
  "[<0033>] TJ\n1 0 0 1 532 37 Tm\n[<0034><0035>] TJ\nEMC\n" ++
  "/Artifact BMC\n1 0 0 1 100 20 Tm\n[<0036>] TJ\nEMC\nET\n" ++
  "/Artifact BMC\nq 20 0 0 15 50 20 cm /Im1 Do Q\nEMC\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0.62 0.62 0.66 RG 0.75 w 70 20 20 15 re S Q\nEMC\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0.62 0.62 0.66 RG 0.75 w 90 20 10 5 re S Q\nEMC\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0.784 0.118 0.118 rg 10 22 40 1 re f Q\n" ++
  "q 0 0 0 rg 110 20 10 2 re f Q\nEMC"

/-- The path page: two pictures, each its paths under one `/P` sequence
(the tag is whatever type holds the leaf — here the synthetic tags'), the
text object empty. -/
def artifactPathExpected : String :=
  "/P << /MCID 0 >> BDC\n" ++
  "q 0.784 0.118 0.118 RG 0.4 w [3 3] 0 d 70 50 m 70 61.046 61.046 70 50 70 c " ++
  "38.954 70 30 61.046 30 50 c 30 38.954 38.954 30 50 30 c 61.046 30 70 38.954 70 50 c h S Q\n" ++
  "q 0.941 0.941 0.941 rg 0 0 0 RG 1 w [1 1] 0 d 10 70 30 20 re B Q\n" ++
  "q 0 0 0 RG 0.4 w 1 98 m 3 96 l 5 94 l 7 92 m 9 90 11 88 13 86 c 1 99 2 98 3 97 c S Q\nEMC\n" ++
  "/H2 << /MCID 1 >> BDC\n" ++
  "q 0.784 0.118 0.118 rg 1 98 m 3 96 l 5 94 l h f Q\n" ++
  "q 1 97 2 2 re n Q\nEMC\n" ++
  "BT\nET"

/-- Two furniture lines around a flow line, the second furniture line
carrying a rule: the furniture groups are pagination artifacts inside the
text object, the flow line — no leaf — a bare artifact, the rule a layout
artifact after `ET`. -/
def artifactFurniturePage : Layout.PageOut := {
  lines := #[
    { x := Dim.pt 10, y := Dim.pt 20, size := Dim.pt 12, setWidth := Dim.pt 100, furniture := true,
      segs := #[contentOpsRun 0 Ir.Color.black (Dim.pt 30) [(36, 'A')]] },
    { x := Dim.pt 10, y := Dim.pt 40, size := Dim.pt 12, setWidth := Dim.pt 100,
      segs := #[contentOpsRun 0 Ir.Color.black (Dim.pt 30) [(37, 'B')]] },
    { x := Dim.pt 10, y := Dim.pt 60, size := Dim.pt 12, setWidth := Dim.pt 100, furniture := true,
      segs := #[contentOpsRun 0 Ir.Color.black (Dim.pt 30) [(38, 'C')],
                .rule (Dim.pt 10) (Dim.pt 1) 0 Ir.Color.black] } ] }

def artifactFurnitureExpected : String :=
  "BT\n/Artifact << /Type /Pagination >> BDC\n1 0 0 1 10 80 Tm\n/F1 12 Tf\n[<0024>] TJ\nEMC\n" ++
  "/Artifact BMC\n1 0 0 1 10 60 Tm\n[<0025>] TJ\nEMC\n" ++
  "/Artifact << /Type /Pagination >> BDC\n1 0 0 1 10 40 Tm\n[<0026>] TJ\nEMC\nET\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0 0 0 rg 40 40 10 1 re f Q\nEMC"

/-- A line whose operators paint: a run with glyphs. Rules and images
gather for painting after `ET`, a kern only moves, so a line of those
alone puts nothing in the text object — unless it resets the expansion
the line before it set (`lineSt`'s `Tz`), which `expectedArtifacts`
tracks. -/
def lineInks (l : Layout.LineOut) : Bool :=
  l.segs.any fun s => match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ => !glyphs.isEmpty
    | .image _ _ _ | .rule _ _ _ _ | .gap _ _ => false

/-- The artifact count a page owes, read from `Layout.PageOut` and the leaf
tags, not from the stream: one block for its fills when it has any, one
for its rules when it has any, one per image segment (the corpus is laid
out here with no store, so every image is a placeholder), one per
furniture line, one per line no element holds whose operators are not
empty — a glyph run, or the expansion reset a rules-only line inherits
from the expanded line before it. -/
def expectedArtifacts (page : Layout.PageOut) (tags : Array (Option String)) : Nat :=
  let rules := page.lines.foldl (init := 0) fun acc l =>
    acc + l.segs.foldl (init := 0) fun acc s =>
      match s with
      | .rule _ _ _ _ => acc + 1
      | .image _ _ _ | .run _ _ _ _ _ _ _ _ _ _ | .gap _ _ => acc
  let images := page.lines.foldl (init := 0) fun acc l =>
    acc + l.segs.foldl (init := 0) fun acc s =>
      match s with
      | .image _ _ _ => acc + 1
      | .rule _ _ _ _ | .run _ _ _ _ _ _ _ _ _ _ | .gap _ _ => acc
  let (unattributed, _) := page.lines.foldl (init := ((0 : Nat), (0 : Int))) fun (acc, tz) l =>
    let nonEmpty := lineInks l || l.expand != tz
    (if Pdf.Origin.of tags l == .unattributed && nonEmpty then acc + 1 else acc, l.expand)
  (if page.fills.isEmpty then 0 else 1) + (if rules == 0 then 0 else 1) + images
    + (page.lines.filter (·.furniture)).size + unattributed

/-- The runs under the pagination wrappers of a text object: what the
furniture artifacts hide from a reader of real content — exactly the
furniture lines' runs, no others. -/
def paginationRuns (ops : Array Pdf.TextOp) : List (Array Nat) :=
  ops.toList.flatMap fun o =>
    match o with
    | .marked (.artifact (some .pagination)) body => Pdf.TextOp.runsList body.toList
    | .marked (.artifact (some .layout)) _ | .marked (.artifact (some .page)) _
    | .marked (.artifact none) _ | .marked (.content _ _ _) _
    | .scale _ | .move _ _ | .font _ _ | .color _ | .show _ => []

def furnitureRuns (page : Layout.PageOut) : List (Array Nat) :=
  page.lines.toList.flatMap fun l =>
    if l.furniture then l.segs.toList.flatMap Pdf.segRuns else []

/-- The lines of a stream that open an artifact sequence. -/
def isArtifactOpen (l : Pdf.Line) : Bool :=
  match l with
  | .open (.artifact _) => true
  | .open (.content _ _ _) => false
  | .op _ | .emc => false

/-- Every painting operator sits inside a wrapper, and the ink is provably
unmoved: the theorems (`mark_ink_exact`, `wrapped_covers`,
`furniture_covers`, `numberMarks_mcids_exact`, `lines_marked_balanced`,
`render_lines_exact`) judged executably on synthetic pages and on every
corpus fixture — the spelling of the wrappers, the string-level strip
equal to the typed strip, the artifact count against the page, the
identifiers `0 … n−1` in stream order, balance, and no flow run under a
pagination wrapper. -/
def artifactMarkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := { pageW := Dim.pt 200, pageH := Dim.pt 100 }
  let remap : Array Nat := #[0, 1]
  let imgMap : Array (Option Nat) := #[some 0, none]
  let tags := contentOpsTags
  let ops (p : Layout.PageOut) := Pdf.contentOps geom remap imgMap tags p
  t "artifacts: the fill block, the rule block and each placeholder wrap as recorded; leaves under their types"
    (Pdf.render (ops contentOpsTextPage) == artifactTextExpected)
  t "artifacts: furniture lines are pagination groups inside the text object, a leafless line a bare one"
    (Pdf.render (ops artifactFurniturePage) == artifactFurnitureExpected)
  t "artifacts: the furniture page strips to its plain twin"
    (stripMarkLines artifactFurnitureExpected
      == Pdf.render (Pdf.contentOpsPlain geom remap imgMap tags artifactFurniturePage))
  t "artifacts: picture paths are grouped per picture under the holder's type"
    (Pdf.render (ops contentOpsPathPage) == artifactPathExpected)
  t "artifacts: the marks of the text page are its two leaves, numbered in stream order"
    (Pdf.pageMarks (ops contentOpsTextPage) == #[(0, 0), (1, 1)]
      && Pdf.pageMarks (ops contentOpsPathPage) == #[(0, 0), (1, 1)])
  -- Well-nesting is a type: a hand-built nest renders balanced, and strips
  -- to its innermost body.
  let nest : Array Pdf.ContentOp :=
    #[.marked (.artifact none) #[.marked (.artifact (some .page)) #[.fill contentOpsRed 1 2 3 4],
        .imageMissing 5 6 7 8], .fill contentOpsRed 9 9 9 9]
  let nestLines := (Pdf.render nest).splitOn "\n"
  t "artifacts: a nested wrapper renders two opening lines and two EMC lines, ink between"
    ((nestLines.filter fun l => l.endsWith " BDC" || l.endsWith " BMC").length == 2
      && (nestLines.filter (· == "EMC")).length == 2
      && stripMarkLines (Pdf.render nest)
          == Pdf.render #[.fill contentOpsRed 1 2 3 4, .imageMissing 5 6 7 8, .fill contentOpsRed 9 9 9 9]
      && Pdf.render (Pdf.inkOps nest) == stripMarkLines (Pdf.render nest))
  t "artifacts: an empty wrapper is one opening line and one EMC line"
    (Pdf.render #[.marked (.artifact none) #[]] == "/Artifact BMC\nEMC")
  -- Numbering descends every body and hands out `0 … n−1` in stream order,
  -- however the construction nested.
  let nested : Array Pdf.ContentOp :=
    #[.marked (.content "P" 9 0) #[.fill contentOpsRed 1 2 3 4,
        .marked (.content "Span" 9 1) #[.fill contentOpsRed 5 6 7 8]],
      .text #[.marked (.artifact none) #[.scale 0], .marked (.content "H1" 9 2) #[.scale 1]],
      .marked (.artifact (some .layout)) #[.marked (.content "Figure" 9 3) #[.imageMissing 1 1 1 1]]]
  t "artifacts: numbering hands out 0 … n−1 in stream order through every body, leaves kept"
    (Pdf.pageMarks (Pdf.numberMarks nested) == #[(0, 0), (1, 1), (2, 2), (3, 3)]
      && Pdf.inkOps (Pdf.numberMarks nested) == Pdf.inkOps nested)
  -- `BDC` takes two operands, `BMC` one: a bare tag before `BDC` is a
  -- syntax error on which poppler drops the rest of the page (found by
  -- `pdftotext`, not by any spelling test — the reason this row exists).
  t "artifacts: every opener is a legal operator — BMC alone, BDC with its dictionary"
    (Pdf.MarkTag.opener (.artifact none) == "/Artifact BMC"
      && [Pdf.ArtifactKind.pagination, .layout, .page].all (fun k =>
        let o := Pdf.MarkTag.opener (.artifact (some k))
        o.startsWith "/Artifact << /Type /" && o.endsWith " >> BDC")
      && Pdf.MarkTag.opener (.content "P" 7 3) == "/P << /MCID 7 >> BDC")
  -- The corpus: every fixture's every page, under the fixture's own
  -- structure tree.
  let mut pages := 0
  let mut wrappers := 0
  let mut marks := 0
  let mut furniture := 0
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom (some pats)
    let tree := Struct.ofDoc (Layout.pdfView doc)
    let tags := Pdf.tagsOf tree
    let all := Pdf.pageOps geom oneFace out.pages {} tree
    for i in [0:out.pages.size] do
      let page := out.pages[i]!
      let ops := all[i]!
      let s := Pdf.render ops
      let ls := Pdf.lines ops
      let pm := Pdf.pageMarks ops
      pages := pages + 1
      wrappers := wrappers + ls.countP Pdf.Line.isOpen
      marks := marks + pm.size
      furniture := furniture + (page.lines.filter (·.furniture)).size
      -- The string-level strip is the typed strip (`render_inkOps_exact`
      -- reaches `joinLines (stripMarks (lines ops))`; this closes the gap
      -- between a line of the file and a `Line`).
      t s!"artifacts {n} p{i}: stripping the marked-content lines of the file is stripping the typed lines"
        (stripMarkLines s == Pdf.render (Pdf.inkOps ops)
          && stripMarkLines s == Pdf.joinLines (Pdf.stripMarks ls))
      t s!"artifacts {n} p{i}: one artifact per fill block, rule block, placeholder, furniture line, and leafless inked line"
        (ls.countP isArtifactOpen == expectedArtifacts page tags)
      t s!"artifacts {n} p{i}: one pagination artifact per furniture line"
        (ls.countP Pdf.Line.isPaginationOpen == (page.lines.filter (·.furniture)).size)
      t s!"artifacts {n} p{i}: the identifiers are 0 … n−1 in stream order"
        (pm.toList.map Prod.fst == List.range pm.size)
      t s!"artifacts {n} p{i}: every mark's tag is the type of the element holding its leaf"
        ((Pdf.contentOpens ls).length == pm.size && ls.all fun l => match l with
          | .open (.content s _ k) => tags[k]?.join == some s
          | .open (.artifact _) | .op _ | .emc => true)
      t s!"artifacts {n} p{i}: BDC and EMC lines pair off"
        (ls.countP Pdf.Line.isOpen == ls.countP Pdf.Line.isEmc
          && ((s.splitOn "\n").filter fun l => l.endsWith " BDC" || l.endsWith " BMC").length
            == ls.countP Pdf.Line.isOpen
          && ((s.splitOn "\n").filter (· == "EMC")).length == ls.countP Pdf.Line.isEmc)
      t s!"artifacts {n} p{i}: the runs under pagination wrappers are the furniture runs, no flow run"
        ((ops.toList.flatMap fun o => match o with
            | .text tops => paginationRuns tops
            | .fill _ _ _ _ _ | .path _ _ _ | .image _ _ _ _ _ | .imageMissing _ _ _ _
            | .marked _ _ => []) == furnitureRuns page)
      t s!"artifacts {n} p{i}: every operation at the top of the stream is wrapped, or the text object with every operator wrapped"
        (ops.all Pdf.ContentOp.wrapped)
  t s!"artifacts: the corpus exercised the layer ({pages} pages, {wrappers} wrappers, \
{marks} marks, {furniture} furniture lines)"
    (pages > 0 && wrappers > 0 && marks > 0 && furniture > 0)

/-- The profile grammar and the contract algebra: a declared conformance
name is a set element implying exactly one assertion, judged on the census
of the built bytes; the meet of two contracts fails no file the two would
each pass; and no claim is written — every corpus PDF is byte-identical
to the writer's output before the grammar existed (the writer takes no
contract; asserted here by the absence of any identification). -/
def pdfContractChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let out (decl : String) : Ir.Doc × Array Diag := elabStr (dvDoc s!"\\output\{ {decl} }\n" "x")
  let profileAsserts (d : Ir.Doc) : Array String := d.asserts.filterMap fun a =>
    match a.kind with
    | .pdfProfile n => some n
    | .pages _ _ | .fontsAllEmbedded | .textInArea | .minXHeight _ | .accessibilityAA => none
  -- Red 1: the key is known, the name lands in the set, one assertion is
  -- implied, and A-4's colour demand folds into the contract.
  let (d1, ds1) := out "formats = pdf, profiles = pdf/a-4"
  t "profiles: 'profiles = pdf/a-4' is a known key" (!ds1.any fun d => d.code == "E0322" || d.code == "E0321")
  t "profiles: the name lands in the set" (d1.output.profiles == #["pdf/a-4"])
  t "profiles: one declared profile implies one pdf.profile assertion"
    (profileAsserts d1 == #["pdf/a-4"])
  t "profiles: the implied assertion reads the PDF alone"
    ((Ir.AssertKind.pdfProfile "pdf/a-4").reads == #["pdf"] &&
     (Ir.AssertKind.pdfProfile "pdf/a-4").source == "pdf.profile = pdf/a-4")
  t "profiles: pdf/a-4 implies color = srgb" (d1.output.contract.color == .srgb)
  -- Red 2: a set, and a refused name naming the registered ones.
  let (d2, _) := out "formats = pdf, profiles = pdf/a-4, pdf/a-4"
  t "profiles: a repeated name is one entry and one assertion"
    (d2.output.profiles == #["pdf/a-4"] && profileAsserts d2 == #["pdf/a-4"])
  let (d2b, _) := out "formats = pdf, profiles = pdf/a-4, pdf/ua-2"
  t "profiles: two names are two entries, two assertions, in declaration order"
    (d2b.output.profiles == #["pdf/a-4", "pdf/ua-2"] && profileAsserts d2b == #["pdf/a-4", "pdf/ua-2"])
  let (dz, dsz) := out "formats = pdf, profiles = pdf/z"
  t "profiles: an unknown name is E0321 listing the registered names"
    (dsz.any fun d => d.code == "E0321" && hasStr d.message "pdf/z" &&
      hasStr (d.help.getD "") "pdf/a-4" && hasStr (d.help.getD "") "pdf/ua-2" &&
      hasStr (d.help.getD "") "pdf/x-6")
  t "profiles: an unknown name never enters the set" (dz.output.profiles.isEmpty && (profileAsserts dz).isEmpty)
  t "profiles: a bare entry after another key is still refused"
    ((out "css = own, pdf/a-4").2.any (·.code == "E0320"))
  -- Red 3: UA-2 folds alternatives = required; declared keys win, in
  -- either order.
  let (d3, _) := out "formats = pdf, profiles = pdf/ua-2"
  t "profiles: pdf/ua-2 implies alternatives = required" (d3.output.contract.alternatives == .required)
  t "profiles: a declared 'color = device' wins over pdf/a-4's srgb"
    ((out "formats = pdf, profiles = pdf/a-4, color = device").1.output.contract.color == .device)
  let (dRev, _) := elabStr (dvDoc "\\output{ color = device }\n\\output{ profiles = pdf/a-4 }\n" "x")
  t "profiles: the declared key wins whatever order the two blocks come in"
    (dRev.output.contract.color == .device)
  t "profiles: a declared 'alternatives = judged' wins over pdf/ua-2's required"
    ((out "formats = pdf, profiles = pdf/ua-2, alternatives = judged").1.output.contract.alternatives == .judged)
  t "profiles: pdf/x-6 folds no backend-neutral demand"
    ((out "formats = pdf, profiles = pdf/x-6").1.output.contract == {})
  -- The algebra, executable: the table, the meet, the order.
  t "contract: the registered names are exactly the table's"
    (PdfContract.Profile.names.all fun n => (PdfContract.Profile.contract? n).isSome)
  t "contract: brotli is not a registered name" ((PdfContract.Profile.contract? "brotli").isNone &&
    !PdfContract.Profile.names.contains "brotli")
  t "contract: the empty set is plain" (PdfContract.Contract.ofProfiles #[] == .ok PdfContract.plain)
  t "contract: plain ≤ every profile; the brotli extension permits more, so it sits below plain"
    (PdfContract.plain.le PdfContract.archive && PdfContract.plain.le PdfContract.accessible &&
     PdfContract.plain.le PdfContract.print && PdfContract.brotli.le PdfContract.plain &&
     !PdfContract.plain.le PdfContract.brotli)
  t "contract: archive is not ≤ plain" (!PdfContract.archive.le PdfContract.plain)
  let both := PdfContract.archive.meet PdfContract.accessible
  t "contract: each member ≤ the meet (meet_covers, executable)"
    (PdfContract.archive.le both && PdfContract.accessible.le both &&
     PdfContract.Contract.ofProfiles #["pdf/a-4", "pdf/ua-2"] == .ok both)
  t "contract: the meet forbids Info, demands tagging, claims both ids"
    (both.infoDict == .absent && both.tagged && both.needsLang && both.ids.contains .pdfa &&
     both.ids.contains .pdfua && both.colour == .intent .rgb)
  let rev := PdfContract.accessible.meet PdfContract.archive
  t "contract: meet is commutative on the demands (meet_comm, executable)"
    (both.infoDict == rev.infoDict && both.colour == rev.colour && both.intent == rev.intent &&
     both.tagged == rev.tagged && both.needsTitle == rev.needsTitle && both.boxes == rev.boxes &&
     both.filters.all rev.filters.contains && rev.filters.all both.filters.contains &&
     both.ids.all rev.ids.contains && rev.ids.all both.ids.contains)
  t "contract: meet is idempotent"
    (PdfContract.archive.meet PdfContract.archive == PdfContract.archive &&
     PdfContract.accessible.meet PdfContract.accessible == PdfContract.accessible)
  t "contract: a-4 + x-6 is refused: two intents of different colour kinds"
    (match PdfContract.Contract.ofProfiles #["pdf/a-4", "pdf/x-6"] with
     | .error v => hasStr v.actual "colour kinds" &&
        (PdfContract.archive.meet PdfContract.print).colour == .conflict
     | .ok _ => false)
  t "contract: an unregistered name is refused by the fold too"
    (match PdfContract.Contract.ofProfiles #["pdf/z"] with
     | .error v => hasStr v.actual "pdf/z"
     | .ok _ => false)
  t "contract: any profile's meet removes the brotli filter"
    (!(PdfContract.brotli.meet PdfContract.archive).filters.contains (.other "BrotliDecode") &&
     PdfContract.brotli.filters.contains (.other "BrotliDecode"))
  t "contract: the filter intersection is the set intersection"
    ((PdfContract.brotli.meet PdfContract.archive).filters.all (fun f =>
        PdfContract.brotli.filters.contains f && PdfContract.archive.filters.contains f) &&
     PdfContract.brotli.filters.all fun f => !PdfContract.archive.filters.contains f ||
        (PdfContract.brotli.meet PdfContract.archive).filters.contains f)
  -- Judged on a written file's census: plain passes, the others fail by
  -- name, and each named fact turns the rule off.
  let (doc, _) := Elab.run "t" "A line of text."
  let lo := layoutOf oneFace doc
  let pdf := Pdf.write {} oneFace lo.pages
  match pdfCensusOf pdf with
  | .error e => t s!"contract: census of the written file: {e}" false
  | .ok c =>
    let rules (k : PdfContract.Contract) (title : Option String := none) : Array String :=
      (PdfContract.violations k c title).map (·.rule)
    t "violations: today's file satisfies plain" ((rules PdfContract.plain).isEmpty)
    t "violations: archive fails on Info and the missing intent, nothing else"
      (rules PdfContract.archive == #["6.1.3-4", "6.2.4.3"])
    -- Every PDF is tagged (pdf-tag-skeleton): the structure and mark rules
    -- hold of the written file; what accessible still lacks is declared.
    t "violations: accessible fails on language and title, the tree and the mark being present"
      (rules PdfContract.accessible == #["8.4.4-1", "8.11.1-1"])
    t "violations: a title turns the title rule off (needsTitle_accounts, executable)"
      (rules PdfContract.accessible (some "T") == #["8.4.4-1"] &&
       !(PdfContract.violations PdfContract.accessible c none).isEmpty)
    t "violations: print fails on the intent and the boxes"
      (rules PdfContract.print == #["6.2.4.3", "trim-xor-art"])
    t "violations: the meet's list is each member's rules"
      (rules both == rules PdfContract.archive ++ rules PdfContract.accessible)
    t "violations: the conflict meet judges too"
      (rules (PdfContract.archive.meet PdfContract.print) == #["6.1.3-4", "6.2.4.3", "trim-xor-art"])
    t "violations: render names the fact then the rule"
      ((PdfContract.violations PdfContract.archive c none).map (·.render) ==
        #["trailer /Info dictionary present (6.1.3-4)",
          "no output intent: device colour has no device-independent meaning (6.2.4.3)"])
  let (docL, _) := elabStr (dvDoc "\\pdfmeta{ language = \"en\" }\n" "A line of text.")
  let loL := layoutOf oneFace docL
  match pdfCensusOf (Pdf.write {} oneFace loL.pages docL.info) with
  | .error e => t s!"contract: census of the language file: {e}" false
  | .ok c =>
    t "violations: a declared language turns the /Lang rule off"
      ((PdfContract.violations PdfContract.accessible c none).map (·.rule) == #["8.11.1-1"])
  -- The corpus: every fixture satisfies plain, every monotone instance
  -- holds, and no file carries an identification — the writer is
  -- untouched by this slice.
  let mut n := 0
  for name in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{name}.tex"
    let (doc, _) ← elabFixture name src
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc
    let lo := layoutOf oneFace doc geom none store
    let pdf := Pdf.write geom oneFace lo.pages doc.info store lo.outline
    t s!"contract {name}: no fixture declares a profile" doc.output.profiles.isEmpty
    t s!"contract {name}: no identification is written" (!bytesContain (pdfText pdf) "pdfaid" &&
      !bytesContain (pdfText pdf) "pdfuaid" && !bytesContain (pdfText pdf) "pdfxid")
    match pdfCensusOf pdf with
    | .error e => t s!"contract {name}: census: {e}" false
    | .ok c =>
      n := n + 1
      let v (k : PdfContract.Contract) := PdfContract.violations k c doc.info.title
      t s!"contract {name}: the file satisfies plain" ((v PdfContract.plain).isEmpty)
      t s!"contract {name}: the meet passes only files each member passes (violations_monotone)"
        (((v both).isEmpty → (v PdfContract.archive).isEmpty && (v PdfContract.accessible).isEmpty) &&
         ((v PdfContract.archive).isEmpty → (v PdfContract.plain).isEmpty))
      t s!"contract {name}: archive fails today on Info" ((v PdfContract.archive).any (·.rule == "6.1.3-4"))
  t s!"contract: the corpus was censused ({n} files)" (n > 0)
  -- The driver, end to end: honest failure with the census facts as
  -- actual, nothing written, exit 2; an unknown name refused; a set with
  -- no PDF to judge fails loud.
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds for the profile checks:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    let dir ← IO.FS.createTempDir
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
      (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf"))
    let pre := "\\documentclass{article}\n\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }\n"
    let one := "\\begin{document}\nA probe.\n\\end{document}\n"
    let run (name decl : String) : IO (UInt32 × String × System.FilePath) := do
      IO.FS.writeFile (dir / s!"{name}.tex") (pre ++ decl ++ one)
      let outDir := dir / s!"out-{name}"
      let r ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := #[(dir / s!"{name}.tex").toString, "-o", outDir.toString ++ "/"] }
      return (r.exitCode, r.stdout ++ r.stderr, outDir)
    let (code, log, outDir) ← run "a4" "\\output{ formats = pdf, profiles = pdf/a-4 }\n"
    t s!"driver: pdf/a-4 on a plain article is E0330 with the census facts as actual: {log}"
      (code == 2 && hasStr log "E0330" && hasStr log "pdf.profile = pdf/a-4" &&
       hasStr log "/Info dictionary present" && hasStr log "no output intent" &&
       !(← outDir.pathExists))
    let (code, log, outDir) ← run "z" "\\output{ formats = pdf, profiles = pdf/z }\n"
    t s!"driver: pdf/z is E0321 naming the registered profiles: {log}"
      (code != 0 && hasStr log "E0321" && hasStr log "pdf/a-4, pdf/ua-2, pdf/x-6" &&
       !(← outDir.pathExists))
    let (code, log, outDir) ← run "ua2" "\\output{ formats = pdf, profiles = pdf/ua-2 }\n"
    t s!"driver: pdf/ua-2 fails honestly on language and title, the tree and the mark present: {log}"
      (code == 2 && hasStr log "pdf.profile = pdf/ua-2" && !hasStr log "no structure tree" &&
       !hasStr log "no MarkInfo" && hasStr log "no /Lang" && hasStr log "no title" &&
       !(← outDir.pathExists))
    let (code, log, outDir) ← run "html" "\\output{ formats = html, profiles = pdf/a-4 }\n"
    t s!"driver: profiles with no PDF emitted fails loud: {log}"
      (code == 2 && hasStr log "no emitted artifact carries this measurement" &&
       !(← outDir.pathExists))
    let (code, log, _) ← run "a4x6" "\\output{ formats = pdf, profiles = pdf/a-4, pdf/x-6 }\n"
    t s!"driver: a-4 + x-6 fails both assertions on the intent conflict: {log}"
      (code == 2 && hasStr log "pdf.profile = pdf/a-4" && hasStr log "pdf.profile = pdf/x-6" &&
       hasStr log "different colour kinds")
    let (code, log, outDir) ← run "none" "\\output{ formats = pdf }\n"
    t s!"driver: no profile, no judgement, the file ships: {log}"
      (code == 0 && (← (outDir / "none.pdf").pathExists))
    IO.FS.removeDirAll dir

/-! ## The structure tree, read back -/

/-- One structure element as the reader sees it: its object number, type,
parent reference, child element numbers in `/K` order, and the
`(page object, mcid)` pairs of its marked-content references. -/
structure ReadElem where
  num : Nat
  s : String
  parent : Option Nat
  kids : Array Nat
  mcids : Array (Nat × Nat)
  ns : Option Nat
  deriving Repr, Inhabited

/-- The reader's view of a file's structure tree: the root's `/K` chain,
walked in preorder. `pageOf` maps a page object number to its index in
the page tree. -/
def readStructTree (es : Array PdfRead.Entry) (root : PdfRead.Obj) : Array ReadElem := Id.run do
  let byNum (n : Nat) : Option PdfRead.Obj := (es.find? (·.num == n)).map (·.val)
  let mut out : Array ReadElem := #[]
  let mut stack : List Nat := match root.get? "K" with
    | some (.arr xs) => xs.toList.filterMap fun o => match o with
      | .ref n _ => some n
      | _ => none
    | some (.ref n _) => [n]
    | _ => []
  -- A tree visits each object once: the object count bounds the walk.
  for _ in [0:es.size + 1] do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      match byNum n with
      | none => pure ()
      | some d =>
        let s := match d.get? "S" with | some (.name s) => s | _ => ""
        let parent := match d.get? "P" with | some (.ref p _) => some p | _ => none
        let ns := match d.get? "NS" with | some (.ref p _) => some p | _ => none
        let kidObjs : List PdfRead.Obj := match d.get? "K" with
          | some (.arr xs) => xs.toList
          | some (.ref n g) => [.ref n g]
          | some (.dict es) => [.dict es]
          | _ => []
        let kids := kidObjs.filterMap fun o => match o with
          | .ref n _ => some n
          | _ => none
        let mcids := kidObjs.filterMap fun o => match o with
          | .dict _ =>
            match o.get? "Pg", (o.get? "MCID").bind PdfRead.Obj.int? with
            | some (.ref pg _), some m => some (pg, m.toNat)
            | _, _ => none
          | _ => none
        out := out.push { num := n, s, parent, kids := kids.toArray, mcids := mcids.toArray, ns }
        stack := kids ++ stack
  return out

/-- The `/MCID n` identifiers a decoded content stream opens, in stream order. -/
def streamMcids (data : ByteArray) : List Nat :=
  ((String.fromUTF8! data).splitOn "\n").filterMap fun l =>
    if l.endsWith " BDC" then
      match (l.splitOn "/MCID ").drop 1 with
      | rest :: _ => (rest.splitOn " ").head?.bind (·.toNat?)
      | [] => none
    else none

/-- **Every PDF is tagged.** The catalog carries `/MarkInfo << /Marked true >>`
and a `/StructTreeRoot`; the tree read back through the engine's reader lists
every marked-content identifier the page streams open, once, with the parent
tree mapping each back to its element; the heading elements are exactly
`Ir.headingLevels`; the typed model agrees with itself (tags, parent tree,
leaf placeholders each held once). Every corpus fixture. -/
def structTreeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- The typed model on a synthetic tree: kinds to types, holders, inline
  -- elements empty, an image its own Figure with /Alt, headings the census.
  let tree : Struct.Tree := { children := #[
    .node (.heading 0) #[.leaf 0 (.text "Title")],
    .node .paragraph #[.leaf 1 (.text "Read "), .node (.link "https://example.org") #[.leaf 2 (.text "this")],
      .leaf 3 (.image "a.png" "An image"), .node .formula #[.leaf 4 (.text "x")]],
    .node (.list false) #[.node .item #[.node .label #[], .node .body #[.node .paragraph #[.leaf 5 (.text "item")]]]],
    .node .aside #[.node .paragraph #[.leaf 6 (.text "speaker")]],
    .node .bibEntry #[.leaf 7 (.text "[1] A")], .node .bibEntry #[.leaf 8 (.text "[2] B")],
    .node .figure #[.node .caption #[.leaf 9 (.text "Cap")], .node .paragraph #[.leaf 10 (.image "b.png" "")]],
    .node .code #[.leaf 11 (.text "code")] ] }
  let sk := Pdf.skeleton tree
  let names := sk.map (·.s)
  t "struct: the skeleton spells the types in preorder, inline elements included, the aside and label absent"
    (names == #["Document", "H1", "P", "Link", "Figure", "Formula", "L", "LI", "LBody", "P",
      "L", "LI", "LBody", "LI", "LBody", "Figure", "Caption", "P", "Figure", "Code"])
  t "struct: the parent of every element but the root is the element before it in its branch"
    (sk[0]!.parent == none && sk[1]!.parent == some 0 && sk[3]!.parent == some 2 &&
     sk[4]!.parent == some 2 && sk[8]!.parent == some 7 && sk[13]!.parent == some 10 &&
     sk[18]!.parent == some 17)
  t "struct: a link's leaf lands in the paragraph, an image is its own Figure with /Alt, an empty alt is none"
    (sk[2]!.kids == #[.leaf 1, .elem 3, .leaf 2, .elem 4, .elem 5, .leaf 4] &&
     sk[4]!.kids == #[.leaf 3] && sk[4]!.alt == some "An image" && sk[18]!.alt == none &&
     sk[5]!.kids == #[])
  t "struct: two reference entries share one L; Code is a 1.7 type, the rest 2.0"
    (sk[10]!.s == "L" && sk[11]!.parent == some 10 && sk[13]!.parent == some 10 &&
     sk[19]!.ns20 == false && sk[2]!.ns20 && sk[0]!.ns20)
  let tags := Pdf.leafTags sk 12
  t "struct: leaf tags are the holders' types; the aside's leaf has none"
    (tags == #[some "H1", some "P", some "P", some "Figure", some "P", some "P", none,
      some "LBody", some "LBody", some "Caption", some "Figure", some "Code"])
  t "struct: the heading census is the tree's" (Pdf.headingsOf sk == [0] && tree.headings == #[0])
  -- fill and the parent tree on two synthetic pages: leaf 1 on page 0 as
  -- mcid 0 and 1, leaf 5 on page 1 as mcid 0.
  let marks : Array (Array (Nat × Nat)) := #[#[(0, 1), (1, 1)], #[(0, 5)]]
  let filled := Pdf.fill sk (Pdf.leafPagesOf 12 marks)
  t "struct: fill puts each mark in the element holding its leaf, in page order"
    (filled[2]!.kids == #[.mcid 0 0, .mcid 0 1, .elem 3, .elem 4, .elem 5] &&
     filled[9]!.kids == #[.mcid 1 0])
  t "struct: the parent tree maps every mark back to the element that lists it"
    (Pdf.parentTreeOf marks (Pdf.leafOwners sk 12) == #[#[some 2, some 2], #[some 9]])
  -- The Struct projection of an elaborated document is a Document over Sect/H/P.
  let (doc, _) := elabStr (dvDoc "" "\\section{Head}\n\nText\\footnote{note body} more.\n\n\\begin{itemize}\\item one\\end{itemize}")
  let esk := Pdf.skeleton (Struct.ofDoc (Layout.pdfView doc))
  t "struct: an elaborated section, footnote and list project to H2, P with FENote, L/LI/LBody/P"
    (esk.map (·.s) == #["Document", "H2", "P", "FENote", "L", "LI", "LBody", "P"])
  -- Every corpus fixture, written and read back.
  let mut elems := 0
  let mut mcids := 0
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc
    let out := layoutOf oneFace doc geom none store
    let tree := Struct.ofDoc (Layout.pdfView doc)
    let pdf := Pdf.write geom oneFace out.pages doc.info store out.outline (tree := tree)
    let text := pdfText pdf
    t s!"struct {n}: the catalog declares marked content and a structure tree root"
      (bytesContain text "/MarkInfo << /Marked true >>" && bytesContain text "/StructTreeRoot"
        && bytesContain text "/S /Document")
    -- The typed model: placeholders held once, tags from the holders.
    let sk := Pdf.skeleton tree
    -- The per-fixture floor beside the proved `skeleton_leafKids_nodup`, and of
    -- `parentTree_covers`'s hypothesis.
    t s!"struct {n}: every leaf placeholder is held by exactly one element" (Pdf.leafKids sk).Nodup
    match PdfRead.objects pdf with
    | .error e => t s!"struct {n}: objects: {e}" false
    | .ok es =>
      let es := es.val
      let trailer := (PdfRead.trailer pdf).toOption.getD (.dict #[])
      let catalog := PdfCensus.catalogOf es trailer
      let census := PdfCensus.ofEntries trailer es
      t s!"struct {n}: the census sees MarkInfo and StructTreeRoot" (census.markInfo && census.structTreeRoot)
      let rootNum := match catalog.get? "StructTreeRoot" with
        | some (.ref r _) => r
        | _ => 0
      let root := PdfCensus.deref es ((catalog.get? "StructTreeRoot").getD .null)
      let pagesObj := PdfCensus.deref es ((catalog.get? "Pages").getD .null)
      let pageNums : Array Nat := match pagesObj.get? "Kids" with
        | some (.arr xs) => xs.filterMap fun o => match o with
          | .ref n _ => some n
          | _ => none
        | _ => #[]
      let pageOf (pg : Nat) : Nat := (pageNums.findIdx? (· == pg)).getD 999
      let tree := readStructTree es root
      elems := elems + tree.size
      t s!"struct {n}: the root's one kid is the Document, in the PDF 2.0 namespace"
        (tree.size > 0 && tree[0]!.s == "Document" && tree[0]!.ns.isSome &&
          (match tree[0]!.ns with
            | some nsNum => match PdfCensus.deref es (.ref nsNum 0) |>.get? "NS" with
              | some (.str raw) => String.fromUTF8! raw == "(http://iso.org/pdf2/ssn)"
              | _ => false
            | none => false))
      t s!"struct {n}: every element names its parent, the root the structure tree root"
        (tree.all fun e => match e.parent with
          | some p => (p == rootNum && e.num == tree[0]!.num)
            || tree.any fun q => q.num == p && q.kids.contains e.num
          | none => false)
      -- The streams' identifiers against the tree's, as multisets.
      let mut streamPairs : Array (Nat × Nat) := #[]
      let mut perPageOk := true
      for (pg, i) in pageNums.zipIdx do
        let pageDict := PdfCensus.deref es (.ref pg 0)
        let ids := match pageDict.get? "Contents" with
          | some (.ref c _) => match es.find? (·.num == c) with
            | some e => match e.decoded with
              | .ok (some data) => streamMcids data
              | _ => []
            | none => []
          | _ => []
        perPageOk := perPageOk && ids == List.range ids.length
          && (pageDict.get? "StructParents").bind PdfRead.Obj.int? == some (i : Int)
        streamPairs := streamPairs ++ (ids.map fun m => (i, m)).toArray
      let treePairs := tree.flatMap fun e => e.mcids.map fun (pg, m) => (pageOf pg, m)
      mcids := mcids + treePairs.size
      let sortPairs (xs : Array (Nat × Nat)) := xs.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
      t s!"struct {n}: the identifiers each page opens are 0 … n−1 and its /StructParents is its index"
        perPageOk
      t s!"struct {n}: the tree lists every identifier the streams open, once, and no other"
        (sortPairs treePairs == sortPairs streamPairs)
      -- The parent tree: entry [page][mcid] is the element listing it.
      let ptObj := PdfCensus.deref es ((root.get? "ParentTree").getD .null)
      let nums : Array PdfRead.Obj := match ptObj.get? "Nums" with
        | some (.arr xs) => xs
        | _ => #[]
      let ptOk := tree.all fun e => e.mcids.all fun (pg, m) =>
        let i := pageOf pg
        match nums[2 * i + 1]? with
        | some (.arr refs) => match refs[m]? with
          | some (.ref en _) => en == e.num
          | _ => false
        | _ => false
      t s!"struct {n}: the parent tree maps every identifier back to the element listing it"
        (ptOk && (root.get? "ParentTreeNextKey").bind PdfRead.Obj.int? == some (pageNums.size : Int))
      -- The heading census: H<n> elements in preorder are the document's levels + 1.
      let hs := tree.filterMap fun e =>
        if e.s.startsWith "H" && e.s.length > 1 then (e.s.drop 1).toString.toNat? else none
      t s!"struct {n}: the heading elements are Ir.headingLevels, each one level up"
        (hs == (Ir.headingLevels (Layout.pdfView doc).body).map (· + 1))
      t s!"struct {n}: every element with a 2.0 type names the namespace"
        (tree.all fun e => e.ns.isSome || e.s == "Code" || e.s == "BlockQuote" || e.s == "Reference")
  t s!"struct: the corpus exercised the tree ({elems} elements, {mcids} marks)"
    (elems > 0 && mcids > 0)

mutual

/-- Every `img` element's `src` attribute in the typed tree, in document
order. The self-contained-page oracle reads the attribute the tree
carries, never the printed string. -/
-- conserves: none — a src census, not text
def imgSrcs (acc : Array String) : Html.Node → Array String
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let acc := if t == "img" then
        match attrs.find? (·.1 == "src") with
        | some (_, s) => acc.push s
        | none => acc
      else acc
    imgSrcsList acc kids.toList

def imgSrcsList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => imgSrcsList (imgSrcs acc k) rest

end

/-- The self-contained page: every `<img src>` a loaded raster entry
produces names a file `publish` writes under `<stem>.assets/`, and nothing
under that directory exists before the assertion gate. A fact of the
artifact, not the IR — file placement is where a page lives — so the
in-memory half reads the typed tree (`imgSrcs`) and the on-disk half runs
this tree's own binary, on a document that ships its face and its raster
from the corpus. -/
def htmlAssetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let png : Image.Plan := { pxW := 64, pxH := 40 }
  let srcsOf (store : Image.Store) (doc : Ir.Doc) : Array String :=
    let (head, body, _) := HtmlDoc.emitTree { imgs := store, assetsDir := "out.assets" } doc
    imgSrcsList (imgSrcsList #[] head.toList) body.toList
  let docOf (body : String) : IO Ir.Doc := do
    let (doc, ds) := elabStr (dvDoc "" body)
    t s!"html assets: fixture elaborates clean: {body}" ds.isEmpty
    return doc
  -- Red 1: a loaded raster links the copy beside the page, and the asset
  -- list names that copy with the store index it came from.
  let doc ← docOf "\\includegraphics[alt={A box}]{rects.png}"
  let one : Image.Store := { entries := #[{ src := "rects.png", info := some png }] }
  t "html assets: a loaded raster's src names its copy under the assets directory"
    (srcsOf one doc == #["out.assets/i0-rects.png"])
  t "html assets: imageAssets names the copy with its store index"
    (HtmlDoc.imageAssets one == #[{ file := "i0-rects.png", srcIndex := 0 }])
  -- Red 2: two sources sharing a basename in different directories take
  -- distinct names — the index prefix, not the basename, carries identity.
  let doc2 ← docOf "\\includegraphics[alt={A}]{a/plot.png} and \\includegraphics[alt={B}]{b/plot.png}"
  let two : Image.Store := { entries := #[{ src := "a/plot.png", info := some png },
                                          { src := "b/plot.png", info := some png }] }
  t "html assets: two rasters sharing a basename take distinct asset names"
    (srcsOf two doc2 == #["out.assets/i0-plot.png", "out.assets/i1-plot.png"])
  t "html assets: imageAssets covers both, in store order"
    ((HtmlDoc.imageAssets two).map (·.srcIndex) == #[0, 1] &&
     (HtmlDoc.imageAssets two).map (·.file) == #["i0-plot.png", "i1-plot.png"])
  -- Red 3: an entry that did not load keeps the source spelling (the
  -- placeholder, already diagnosed) and has no asset row.
  let unloaded : Image.Store := { entries := #[{ src := "rects.png" }] }
  t "html assets: an unloaded entry keeps its source spelling and ships no copy"
    (srcsOf unloaded doc == #["rects.png"] && (HtmlDoc.imageAssets unloaded).isEmpty)
  -- graphicx's extension resolution: the entry's href names the file on
  -- disk, and the copy takes that name, not the bare spelling.
  let bare ← docOf "\\includegraphics[alt={A box}]{rects}"
  let resolved : Image.Store :=
    { entries := #[{ src := "rects", href := "rects.png", info := some png }] }
  t "html assets: a bare graphicx name copies under its resolved file name"
    (srcsOf resolved bare == #["out.assets/i0-rects.png"] &&
     HtmlDoc.imageAssets resolved == #[{ file := "i0-rects.png", srcIndex := 0 }])
  -- A PDF source is a form XObject in the PDF and no browser image either
  -- way: it keeps today's src and ships no copy (named-next for html-oracle).
  let pdfDoc ← docOf "\\includegraphics[alt={A page}]{box.pdf}"
  let pdfPlan := (Image.decode (← IO.FS.readBinFile "tests/corpus/figures/box.pdf")).toOption
  let pdfStore : Image.Store :=
    { entries := #[{ src := "box.pdf", info := pdfPlan }] }
  t "html assets: a PDF source keeps its spelling and ships no copy"
    (srcsOf pdfStore pdfDoc == #["box.pdf"] && (HtmlDoc.imageAssets pdfStore).isEmpty)
  -- A boundary picture publishes as SVG through its own list already; its
  -- entry keeps the href the conversion set.
  let picSrc := Ir.picSrcPrefix ++ "abc"
  let picStore : Image.Store :=
    { entries := #[{ src := picSrc, href := "out.assets/abc.svg"
                     info := some { pxW := 10, pxH := 10 } }] }
  t "html assets: a boundary picture keeps its SVG href and has no raster row"
    (HtmlDoc.imageHref "out.assets" picStore picSrc == "out.assets/abc.svg" &&
     (HtmlDoc.imageAssets picStore).isEmpty)
  -- The name's index is recoverable whatever the basename (the executable
  -- twin of `imageAssetName_inj`).
  t "html assets: equal names mean equal indices"
    (HtmlDoc.imageAssetName 3 "a/x.png" == "i3-x.png" &&
     HtmlDoc.imageAssetName 3 "a/x.png" != HtmlDoc.imageAssetName 13 "x.png" &&
     HtmlDoc.imageAssetName 12 "x.png" != HtmlDoc.imageAssetName 1 "2-x.png")
  -- Red 4 and 5, the driver end to end: the copy lands beside the page
  -- named by `-o`, byte for byte the source; a failing assertion leaves no
  -- `-o` directory and no `.assets/` anywhere — the copies are phase-3
  -- lines, after the gate.
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds for the asset checks:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    let dir ← IO.FS.createTempDir
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
      (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf"))
    let rects ← IO.FS.readBinFile "tests/corpus/rects.png"
    IO.FS.writeBinFile (dir / "rects.png") rects
    let pre := "\\documentclass{article}\n\\usepackage{graphicx}\n\
\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }\n\\output{ formats = html }\n"
    let body := "\\begin{document}\nA box: \\includegraphics[alt={A box}]{rects.png}.\n\\end{document}\n"
    IO.FS.writeFile (dir / "doc.tex") (pre ++ body)
    IO.FS.createDirAll (dir / "out")
    let r ← IO.Process.output {
      cmd := ".lake/build/bin/leantex"
      args := #[(dir / "doc.tex").toString, "-o", (dir / "out" / "x.html").toString] }
    t s!"driver: the page builds under -o out/x.html: {r.stdout}{r.stderr}" (r.exitCode == 0)
    let copy := dir / "out" / "x.assets" / "i0-rects.png"
    let copied ← copy.pathExists
    t "driver: the raster is published beside the page under <stem>.assets" copied
    t "driver: the published raster is the source, byte for byte"
      (copied && (← if copied then IO.FS.readBinFile copy else pure ByteArray.empty) == rects)
    let page ← IO.FS.readFile (dir / "out" / "x.html")
    t "driver: the page links the copy, not the source spelling"
      (hasStr page "src=\"x.assets/i0-rects.png\"" && !hasStr page "src=\"rects.png\"")
    IO.FS.writeFile (dir / "fail.tex") (pre ++ "\\assert{ pages == 99 }\n" ++ body)
    let r2 ← IO.Process.output {
      cmd := ".lake/build/bin/leantex"
      args := #[(dir / "fail.tex").toString, "-o", (dir / "out2").toString ++ "/"] }
    let assetDirs := (← System.FilePath.walkDir dir).filter fun p =>
      p.toString.endsWith ".assets"
    t "driver: a failing assertion publishes no page, no -o directory, and no .assets/ anywhere"
      (r2.exitCode != 0 && !(← (dir / "out2").pathExists) &&
       assetDirs == #[dir / "out" / "x.assets"])
    IO.FS.removeDirAll dir




/-- Anchor claiming: the ids this backend assigns are unique, numbered in
the documented order, and cost their count rather than its cube.

`claimId` probed a growing association array for every candidate id, so
`k` sections sharing one slug scanned `k` entries `k` times. Compiled, 1,800
same-titled sections cost 5.4 s that way and 234 ms keyed. The numbering is
pinned beside the timing because the cheap way to make the probe fast would
be a per-base counter, which assigns different ids the moment another
title's slug has already taken `base-2` — so the ladder is the contract,
not an implementation detail. -/
def anchorCostChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pageOf (body : String) : String × Array Diag :=
    HtmlDoc.emit {} (elabStr ("\\documentclass{article}\\begin{document}" ++
      body ++ "\\end{document}")).1
  let page (body : String) : String := (pageOf body).1
  -- Identical titles take the documented base, base-2, base-3 ladder.
  let shared := page (String.join ((List.range 3).map fun _ => "\\section{Topic}"))
  t "the first of three identical titles claims the bare slug"
    (hasStr shared "id=\"topic\"")
  t "the second takes -2 and the third -3"
    (hasStr shared "id=\"topic-2\"" && hasStr shared "id=\"topic-3\"")
  t "and no fourth id is invented" (!hasStr shared "id=\"topic-4\"")
  t "a repeated identical title takes its number without a warning"
    (((pageOf "\\section{Topic}\\section{Topic}").2.filter (·.code == "W0327")).isEmpty)
  -- A *different* title folding to the same slug is named, not resolved in
  -- silence: an in-page link written from the second title would otherwise
  -- reach the first section with no error anywhere.
  let clash := pageOf "\\section{Data set}\\section{Data-set}"
  t "two different titles sharing a slug both ship an anchor"
    (hasStr clash.1 "id=\"data-set\"" && hasStr clash.1 "id=\"data-set-2\"")
  t "and the collision is named W0327"
    ((clash.2.filter (·.code == "W0327")).size == 1)
  -- Distinct slugs stay distinct at scale, and the ladder is not entered.
  let wide := page (String.join ((List.range 4000).map fun i => s!"\\section\{Topic {i}}"))
  t "the four-thousandth distinct section ships its own anchor, unnumbered"
    (hasStr wide "id=\"topic-3999\"" && !hasStr wide "id=\"topic-3999-2\"")
  -- The cost witness, in the shape that was cubic: every section shares one
  -- slug, so every claim walks the whole ladder and the claim is the
  -- measurement.
  let n := 1800
  let t0 ← IO.monoMsNow
  let big := page (String.join ((List.range n).map fun _ => "\\section{Topic}"))
  -- Consumed before the clock is read again: a pure `let` floats to its
  -- first use, so a timing with nothing between the two reads measures
  -- nothing (the FontDb.families precedent).
  t s!"all {n} same-titled sections ship an anchor"
    (hasStr big s!"id=\"topic-{n}\"" && hasStr big "id=\"topic\"")
  let sharedMs := (← IO.monoMsNow) - t0
  t s!"anchor claiming is not cubic in same-slug sections ({sharedMs} ms for {n})"
    (sharedMs < 1500)
