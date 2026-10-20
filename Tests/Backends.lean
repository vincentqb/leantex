module

public import Tests.Support
public import scripts.Gate
public import LeanTex.Cli.Driver
public import LeanTex.Core.FigureOutline
public import LeanTex.Core.FigureStore
public import Tests.CorpusStore
public import LeanTex.Core.LayoutFigure

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- `n` base units: a coordinate whose value only the comparison reads. -/
private def q (n : Int) : Dim.Length := n * Dim.Length.quantum

/-- Math in HTML is MathML Core built from the parsed atoms, one shape per construct, and its leaf
text matches the PDF's coverage census. -/
def mathmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let page (body : String) : String :=
    (HtmlDoc.emit {} (elabStr (dvDoc "" body)).1).1
  let has (body frag : String) : Bool :=
    ((page body).splitOn frag).length ≥ 2
  let elements (body tag : String) : Array Html.Node :=
    let (_, nodes, _) := HtmlDoc.emitTree {} (elabStr (dvDoc "" body)).1
    elemNodesList (· == tag) #[] nodes.toList
  let mathKids (body : String) : Array Html.Node :=
    match (elements body "math")[0]? with
    | some (Html.Node.elem _ _ kids) => kids
    | _ => #[]
  let token (tag text : String) (n : Html.Node) : Bool :=
    match n with
    | .elem name attrs #[.text s] => name == tag && s == text &&
        (tag != "mi" || attrs.contains ("mathvariant", "normal"))
    | _ => false
  let hasAttrs (body tag : String) (wanted : Array (String × String)) : Bool :=
    (elements body tag).any fun n => match n with
    | .elem _ attrs _ => wanted.all attrs.contains
    | _ => false
  t "inline math is an inline math element"
    (has "$x$" "<math class=\"math\" data-tex=\"x\"><mi mathvariant=\"normal\">𝑥</mi></math>")
  t "display math is a block math element with the display class"
    (has "\\[ x \\]" "<math display=\"block\" class=\"math math-display\"")
  t "a superscript is msup with an mrow script"
    (match mathKids "$x^2$" with
      | #[.elem "msup" _ #[base, .elem "mrow" _ #[sup]]] =>
        token "mi" "𝑥" base && token "mn" "2" sup
      | _ => false)
  t "a stacked pair is msubsup in base, sub, sup order"
    (match mathKids "$a_i^2$" with
      | #[.elem "msubsup" _ #[base, .elem "mrow" _ #[sub], .elem "mrow" _ #[sup]]] =>
        token "mi" "𝑎" base && token "mi" "𝑖" sub && token "mn" "2" sup
      | _ => false)
  t "a fraction is mfrac with two mrow children"
    (match mathKids "$\\frac{1}{2}$" with
      | #[.elem "mfrac" _ #[.elem "mrow" _ #[num], .elem "mrow" _ #[den]]] =>
        token "mn" "1" num && token "mn" "2" den
      | _ => false)
  t "a square root is msqrt"
    (has "$\\sqrt{x}$" "<msqrt><mi mathvariant=\"normal\">𝑥</mi></msqrt>")
  t "an indexed radical is mroot: base then index"
    (match mathKids "$\\sqrt[3]{x}$" with
      | #[.elem "mroot" _ #[.elem "mrow" _ #[base], .elem "mrow" _ #[degree]]] =>
        token "mi" "𝑥" base && token "mn" "3" degree
      | _ => false)
  t "a grown pair is stretchy symmetric mo delimiters"
    (has "$\\left( x \\right)$"
      "<mrow><mo stretchy=\"true\" symmetric=\"true\">(</mo><mi mathvariant=\"normal\">𝑥</mi><mo stretchy=\"true\" symmetric=\"true\">)</mo></mrow>")
  t "display limits are munderover: base, under, over"
    (match mathKids "\\[ \\sum_{i}^{n} \\]" with
      | #[.elem "munderover" _ #[base, .elem "mrow" _ #[sub], .elem "mrow" _ #[sup]]] =>
        token "mo" "∑" base && token "mi" "𝑖" sub && token "mi" "𝑛" sup
      | _ => false)
  let opKids (pre : String) : Array Html.Node :=
    let (_, nodes, _) := HtmlDoc.emitTree {} (elabStr (dvDoc pre "\\[ \\op_{x} \\]")).1
    match (elemNodesList (· == "math") #[] nodes.toList)[0]? with
    | some (Html.Node.elem _ _ kids) => kids
    | _ => #[]
  t "a starred declared operator's scripts are display limits, an unstarred one's beside"
    ((opKids "\\DeclareMathOperator*{\\op}{Err}").any (· matches Html.Node.elem "munder" ..) &&
     (opKids "\\DeclareMathOperator{\\op}{Err}").any (· matches Html.Node.elem "msub" ..))
  t "inline limits ride beside as msubsup"
    (has "$\\sum_{i}^{n}$" "<msubsup><mo stretchy=\"false\">∑</mo>")
  t "an accent is mover accent=true, non-stretching for \\hat"
    (has "$\\hat{x}$"
      "<mover accent=\"true\"><mrow><mi mathvariant=\"normal\">𝑥</mi></mrow><mo stretchy=\"false\">̂</mo></mover>")
  t "\\overline is mover accent=false over the stretchy U+203E operator"
    (has "$\\overline{x}$"
      "<mover accent=\"false\"><mrow><mi mathvariant=\"normal\">𝑥</mi></mrow><mo stretchy=\"true\">‾</mo></mover>")
  t "a display alignment is mtable with displaystyle restored"
    (hasAttrs "\\begin{align*} a &= b \\\\ c &= d \\end{align*}"
      "mtable" #[("displaystyle", "true")])
  t "align columns alternate right and left through mtd CSS"
    (has "\\begin{align*} a &= b \\end{align*}"
      "<mtd style=\"text-align: right; text-align: -webkit-right; padding-right: 0\">")
  t "an array declares text style on its mtable"
    (hasAttrs "\\[ \\begin{array}{cc} 1 & 2 \\\\ 3 & 4 \\end{array} \\]"
      "mtable" #[("displaystyle", "false")])
  t "a numbered display keeps its number beside the math, never inside"
    (let p := page "\\begin{equation} e = mc^2 \\end{equation}"
     let inMath := (((p.splitOn "<math").getD 1 "").splitOn "</math>").headD ""
     ((p.splitOn "class=\"equation display\"").length ≥ 2) &&
       ((p.splitOn "eqnum").length ≥ 2) &&
       ((inMath.splitOn "eqnum").length == 1))
  t "an explicit space is mspace at its mu width"
    (hasAttrs "$a\\quad b$" "mspace" #[("width", "1.000000em")]) -- 18 mu is one em
  t "a thin space is three eighteenths of an em"
    (hasAttrs "$a\\, b$" "mspace" #[("width", "0.166667em")])
  t "a negative kern uses a signed margin with zero MathML width"
    (hasAttrs "$a\\! b$" "mspace"
      #[("width", "0"), ("style", "margin-inline-end: -0.166667em")])
  t "a function name is a multi-character upright mi"
    (has "$\\sin x$" "<mi style=\"white-space: pre\">sin</mi>")
  t "an unparsed construct stays source text with its data-tex hook"
    (let p := page "$\\overset{?}{=}$"
     ((p.splitOn "<span class=\"math\" data-tex=").length ≥ 2))
  t "an unparsed construct's element text is its floor, not its source"
    (let p := page "$\\overset{\\textcolor{indigo}{q}}{=}$"
     let inSpan := (((p.splitOn "<span class=\"math\" data-tex=").getD 1 "").splitOn
       "</span>").headD ""
     let shown := ((inSpan.splitOn ">").getD 1 "")
     shown == "q=" && ((inSpan.splitOn "indigo").length ≥ 2))
  let census := ["$x^2$", "$a_i^2$", "$\\frac{1}{2}$", "$\\sqrt[3]{x}$",
    "$\\left( x \\right)$", "$\\sum_{i=1}^{n} i$", "$\\hat{x}$",
    "$\\overline{x+y}$", "$a \\quad b$", "$\\mathbb{R}^d + \\mathcal{L}$",
    "\\begin{align*} a &= b \\\\ c &= d \\end{align*}"]
  for src in census do
    match firstFormula (elabStr (dvDoc "" src)).1 with
    | none => failures ref s!"census: no formula elaborated for {src}"
    | some body =>
      let leaf := MathMl.listChars #[] body
      let pdf := Math.MList.scalarsList true #[] body
      t s!"every PDF census scalar reaches the MathML leaf text: {src}"
        (pdf.all leaf.contains)
      t s!"every MathML leaf scalar is a census scalar or the overline: {src}"
        (leaf.all fun c => pdf.contains c || c == MathMl.overlineChar)

mutual

/-- The texts of a tree longer than one scalar, each with whether an element keeps its line. -/
private def heldRunsOne (held : Bool) (acc : Array (String × Bool)) :
    Html.Node → Array (String × Bool)
  | .elem _ attrs kids => heldRunsList (held || MathMl.keepsLine attrs) acc kids.toList
  | .text s => if s.length > 1 then acc.push (s, held) else acc
  | .style _ => acc
  | .script _ _ => acc

private def heldRunsList (held : Bool) (acc : Array (String × Bool)) :
    List Html.Node → Array (String × Bool)
  | [] => acc
  | n :: rest => heldRunsList held (heldRunsOne held acc n) rest

end

/-- A formula's text runs keep their lines in the web page, as TeX sets each in one box: however
narrow the column, a reason, a word in a script, a function name or a label's words never wrap,
and a run's own spaces stand as written. -/
def mathLineChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let runs (src : String) : Array (String × Bool) :=
    let (_, nodes, _) := HtmlDoc.emitTree {} (elabStr src).1
    (elemNodesList (· == "math") #[] nodes.toList).foldl (heldRunsOne false) #[]
  let cases : List (String × String × List String) := [
    ("an alignment's reasons column",
      dvDoc "" ("\\begin{align*}\n  a + b &= b + a && \\text{by the placeholder rule of swaps} \\\\\n" ++
        "  &= c && \\text{by an invented lemma}\n\\end{align*}"),
      ["by the placeholder rule of swaps", "by an invented lemma"]),
    ("an inline formula's words", dvDoc "" "Inline: $x = \\text{one long invented phrase}$ ends.",
      ["one long invented phrase"]),
    ("a box and an upright run",
      dvDoc "" "$\\mbox{two words} + \\textrm{three more words}$",
      ["two words", "three more words"]),
    ("function and operator names",
      dvDoc "" "$\\sin x + \\log y + \\operatorname{argmax} z + a \\bmod b$",
      ["sin", "log", "argmax", "mod"]),
    ("a run's own spaces at its edges", dvDoc "" "$x \\text{ if } y$", [" if "]),
    ("a hyphenated run", dvDoc "" "$\\text{well-known}$", ["well-known"]),
    ("words in a script and a fraction",
      dvDoc "" "$x^{\\text{two words}} + \\frac{\\text{an invented}}{2}$",
      ["two words", "an invented"]),
    ("a coloured run", dvDoc "" "$\\textcolor{red}{\\text{a b}}$", ["a b"]),
    ("a cases column",
      dvDoc "" ("\\[ f(x) = \\begin{cases} 1 & \\text{if } x > 0 \\\\ 0 & \\text{otherwise}" ++
        " \\end{cases} \\]"),
      ["if ", "otherwise"]),
    ("a struck run", dvDoc "\\usepackage{cancel}" "$\\cancel{\\text{two words}}$",
      ["two words"]),
    ("a frame's reasons column",
      deck169Frame ("\\begin{align*}\n  a &= b && \\text{by the invented step}\n\\end{align*}"),
      ["by the invented step"]),
    ("a picture label's formula",
      dvDoc "\\usepackage{tikz}" (tikzPicture "\\node {$\\text{two words}$};"),
      ["two words"])]
  for (what, src, want) in cases do
    let got := runs src
    let loose := got.filter (!·.2) |>.map (·.1)
    t s!"{what}: every text run of the formula keeps its line ({loose})" loose.isEmpty
    t s!"{what}: the runs the source writes reach the formula as written ({got.map (·.1)})"
      (want.all fun w => got.any (·.1 == w))

/-- A named wrapper the author declares survives into the artifact as an addressable annotation. -/
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
  let (abbrevDoc, _) :=
    elabStr (dvDoc "\\define \\brand {Example Corp}\n" "\\brand{} words")
  t "a zero-ary command is a spelling, not a role"
    (((HtmlDoc.emit {} abbrevDoc).1.splitOn "u-brand").length == 1)
  t "the markdown twin reads through a role"
    ((((MarkdownDoc.emit mutedDoc).splitOn "quiet words").length) == 2)
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
    (hasSpan ("style", "color: var(--ltx-accent, #205e3b)") bothTree &&
     hasSpan ("class", "u-entry") bothTree)
  let (blockRoleDoc, _) := elabStr
    (dvDoc "\\define \\entry(a: content) {\\a\\par}\n" "\\entry{First}\n\\entry{Second}")
  t "a block-level role is an addressable div"
    (((HtmlDoc.emit {} blockRoleDoc).1.splitOn "<div class=\"u-entry\">").length == 3)

/-- `\style` and its two backends. -/
def styleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (decl, arg, st) in Elab.fontAxes do
    t s!"font axis \\{arg} and \\{decl} agree"
      ((elabStr s!"\\{arg}\{x}").1.body ==
          #[.para #[.styled st #[.italicCorr true, .text "x"], .italicCorr true]] &&
       (elabStr s!"\{\\{decl} x}").1.body == #[.para #[.styled st #[.text "x"]]] &&
       (elabStr s!"\\{arg}\{x}").2.all (·.severity != .warning))
  let styled := elabStr ("\\documentclass{article}\\palette{ink = #112233}" ++
    "\\tokens{ sep = 3pt }" ++
    "\\style{section}{ font = {\\large\\sffamily\\ink}, before = 2 * sep, after = sep, rule = ink }" ++
    "\\style{itemize}{ indent = 1.5em, gap = sep, marker = {\\ink\\textbullet} }" ++
    "\\begin{document}\\section{Head}\\begin{itemize}\\item a\\end{itemize}\\end{document}")
  t "style source clean" (styled.2.all (·.severity == .note))
  let secStyle := styled.1.styles.find? "section"
  t "style section font is a template with a hole"
    ((secStyle.bind (·.font)) == some #[.styled (.size "large") #[.styled .sans
      #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some (.color "ink")) #[]]]])
  t "style section spacing reads tokens"
    ((secStyle.bind (·.before)).map (·.width) == some { fixed := Dim.pt 6 } &&
     (secStyle.bind (·.after)).map (·.width) == some { fixed := Dim.pt 3 })
  t "style section rule names the palette entry"
    ((secStyle.bind (·.rule)).map (·.2) == some (some (.color "ink")))
  let listStyle := styled.1.styles.find? "itemize"
  t "style itemize marker is content"
    ((listStyle.bind (·.marker)) == some #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some (.color "ink")) #[.text "•"]])
  let markInk : Ir.Color := { r := 0x20, g := 0x5E, b := 0x3B }
  t "markerCss? expresses colour and size around text"
    (HtmlDoc.markerCss? #[.colored markInk (some (.color "markerink"))
        #[.styled (.size "small") #[.text "•"]]] ==
      some { text := "•"
             decls := #["color: var(--ltx-c-markerink, #205e3b);", "font-size: 0.9em;"] })
  t "markerCss? expresses bold plain text"
    (HtmlDoc.markerCss? #[.styled .bold #[.text "»"]] ==
      some { text := "»", decls := #["font-weight: 600;"] })
  t "markerCss? refuses an image marker"
    (HtmlDoc.markerCss? #[.image "rects.png" {} .undeclared] == none)
  t "markerCss? refuses a link marker"
    (HtmlDoc.markerCss? #[.link "https://example.org" #[.text "x"]] == none)
  t "markerCss? refuses a wrapper beside text"
    (HtmlDoc.markerCss? #[.styled .bold #[.text "a"], .text "b"] == none)
  let markerDoc (m : String) : Ir.Doc :=
    (elabStr ("\\documentclass{article}\\palette{ markerink = #205E3B }" ++
      s!"\\style\{itemize}\{ marker = \{{m}} }" ++
      "\\begin{document}\\begin{itemize}\\item a\\end{itemize}\\end{document}")).1
  let (styledMarkerPage, styledMarkerDs) :=
    HtmlDoc.emit {} (markerDoc "\\textcolor{markerink}{\\small\\textbullet}")
  t "html styled marker reaches ::marker with its colour and size"
    ((styledMarkerPage.splitOn
      "{ content: \"•  \"; color: var(--ltx-c-markerink, #205e3b); font-size: 0.9em; }").length == 2)
  t "html styled marker is clean" (styledMarkerDs.all (·.code != "W0331"))
  let (nestedMarkerPage, nestedMarkerDs) :=
    HtmlDoc.emit {} (markerDoc "\\textbf{\\textit{»}}")
  t "html nested text-command marker reaches its exact ::marker styles"
    ((nestedMarkerPage.splitOn
      "{ content: \"»  \"; font-weight: 600; font-style: italic; }").length == 2)
  t "html nested text-command marker is clean"
    (nestedMarkerDs.all (·.code != "W0331"))
  let (contentMarkerPage, contentMarkerDs) :=
    HtmlDoc.emit {} (markerDoc "\\includegraphics{rects.png}")
  t "html inexpressible marker is named, not silently defaulted"
    (contentMarkerDs.any fun d => d.code == "W0331" && d.severity == .warning &&
      (d.message.splitOn "itemize").length > 1)
  t "html inexpressible marker emits no ::marker override"
    ((contentMarkerPage.splitOn "rects.png").length == 1)
  t "css marker string escapes its delimiters"
    (HtmlDoc.cssString "a\"b\\c" == "a\\\"b\\\\c")
  t "style unknown element" (errCodes ("\\documentclass{article}\\style{footer}{ before = 1pt }" ++
    "\\begin{document}x\\end{document}") == ["E0328"])
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
  let (stylePage, _) := HtmlDoc.emit {} styled.1
  t "html styled heading wraps in the template"
    ((stylePage.splitOn "</span>\u2003<span class=\"size-large\"><span class=\"sans\">").length == 2 &&
     (stylePage.splitOn "<h2 class=\"ruled\"><span class=\"section-number\">").length == 2)
  -- the sheet spells a TeX length in CSS's points
  t "html styled heading spacing" ((stylePage.splitOn
    s!"h2 \{ margin-top: {(Dim.pt 6).toBpString}pt; margin-bottom: {(Dim.pt 3).toBpString}pt;").length == 2)
  t "html styled list indent and gap"
    ((stylePage.splitOn "\nul { padding-left: 1.5em; }").length == 2 &&
     (stylePage.splitOn s!"ul > li \{ margin-top: {(Dim.pt 3).toBpString}pt; }").length == 2)
  t "css em keeps its unit" (HtmlDoc.cssLength { em := 1500 } == "1.5em")
  t "css ex keeps its unit" (HtmlDoc.cssLength { ex := 1500 } == "1.5ex")
  t "css whole em has no fraction" (HtmlDoc.cssLength { em := 2000 } == "2em")
  t "css mixed length sums" (HtmlDoc.cssLength { fixed := Dim.bp 3, em := 500 } == "calc(3pt + 0.5em)")
  let (fromDoc, fromDs) := elabStr ("\\documentclass{article}\\runninghead[from = 2]{x}" ++
    "\\begin{document}y\\end{document}")
  t "running from clean" (fromDs.isEmpty && fromDoc.headFrom == 2 && fromDoc.footFrom == 1)

/-- The HTML article layout follows the IR: the measure, fill rows, link colour and heading rules. -/
def htmlLayoutChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "html measure derives from the default page"
    (HtmlDoc.measureMilli {} 500 == 46975)
  let (narrowDoc, narrowDs) := elabStr ("\\documentclass{article}" ++
    "\\page{ hmargin = 0.75in }\\begin{document}x\\end{document}")
  t "html measure follows a declared page" (narrowDs.isEmpty &&
    ((HtmlDoc.emit {} narrowDoc).1.splitOn "--measure: 50.589rem;").length == 2)
  let hasClass (name : String) (attrs : Array (String × String)) : Bool :=
    attrs.any fun (key, value) =>
      key == "class" && (value.splitOn " ").contains name
  let (entryDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left label \\hfill 1987\\end{document}")
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
  let (ruledDoc, _) := elabStr ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink }\\begin{document}\\section{H}\\end{document}")
  t "html heading rule declares the flex baseline anchor"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn
      "h2 { display: flex; align-items: baseline;").length == 2)
  t "html heading rule lifts half the heading's own ex"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn
      "transform: translateY(-0.5ex)").length == 2)
  let (baselineDoc, _) := elabStr ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink, rule-position = baseline, rule-thickness = 2pt }" ++
    "\\begin{document}\\section{H}\\end{document}")
  t "html baseline heading rule drops the translate and takes its thickness"
    (((HtmlDoc.emit {} baselineDoc).1.splitOn
      s!"h2.ruled::after \{ transform: none; border-top-width: {(Dim.pt 2).toBpString}pt; }").length == 2)
  t "html x-height heading rule emits no per-element override"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn "h2.ruled::after").length == 1)
  let fromFontPage := (HtmlDoc.emit {} ruledDoc).1
  t "html u and a underline from the font's own band"
    ((fromFontPage.splitOn "text-decoration-thickness: from-font").length == 3 &&
     (fromFontPage.splitOn "text-underline-position: from-font").length == 3 &&
     (fromFontPage.splitOn "text-underline-offset").length == 1)

mutual

/-- The flow's shape as `tag.class` tokens, in document order: every `<p>` and every
`display`-classed element, with `>math` for a direct `<math>` child. -/
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

/-- The subject of one selector part: its rightmost compound, cut at its first pseudo-class,
attribute or id, or `::` for a pseudo-element's compound. -/
private def selSubject (part : String) : String := Id.run do
  let mut cur := ""
  let mut depth := 0
  for c in part.trimAscii.toString.toList do
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if depth == 0 && (c == ' ' || c == '>' || c == '+' || c == '~') then cur := ""
    else cur := cur.push c
  if (cur.splitOn "::").length > 1 then return "::"
  return (cur.takeWhile fun c => c != ':' && c != '[' && c != '#').toString

/-- A compound's element and classes: `table.booktabs` is `table` and `[booktabs]`. -/
private def compoundParts (s : String) : String × List String :=
  match s.splitOn "." with
  | e :: cls => (e, cls.filter (!·.isEmpty))
  | [] => ("", [])

/-- Whether a rule whose subject is compound `c` can match an element whose subject is compound `e`. -/
private def compoundOverlaps (c e : String) : Bool :=
  let (ce, cc) := compoundParts c
  let (ee, ec) := compoundParts e
  c != "::" && ((ce == "*" || (ce.isEmpty && cc.isEmpty)) ||
    (!ce.isEmpty && ce == ee && (cc.isEmpty || ec.isEmpty || cc.any ec.contains)) ||
    (ce.isEmpty && cc.any ec.contains))

/-- Every default vertical gap in the emitted sheets has one emitter, the lower element's
`margin-top`, except the caption-above float's internal seam. -/
def htmlRhythmChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (plainDoc, plainDs) := elabStr
    "\\documentclass{article}\\begin{document}a\n\nb\n\\end{document}"
  let plainPage := (HtmlDoc.emit {} plainDoc).1
  t "html rhythm fixture elaborates clean" plainDs.isEmpty
  t "html base sheet has one gap owner per boundary"
    ((plainPage.splitOn "margin-bottom").length == 2)
  -- A longhand census cannot see a shorthand margin, so each block element's whole rule is pinned.
  t "html heading owns its band below, followers suppressed"
    ((plainPage.splitOn ":where(h1, h2, h3, h4, h5, h6) { margin: 0 0 0.725rem; }").length == 2 &&
     (plainPage.splitOn ":where(:is(h1, h2, h3, h4, h5, h6) + *) { margin-top: 0; }").length == 2)
  t "html block elements' own margins are the emitter's zero-specificity resets"
    ((plainPage.splitOn ":where(p, ul, ol, li, dl, dd, pre, blockquote, hr) { margin: 0; }").length == 2 &&
     (plainPage.splitOn ":where(figure.float) { margin: 0 auto; }").length == 2 &&
     !hasStr plainPage "\nli { margin")
  t "html peer gap is the page's parskip over one screen quantum, top-owned"
    ((plainPage.splitOn ":where(* + p) { margin-top: var(--parskip, 0.725rem); }").length == 2 &&
     !hasStr plainPage "    --parskip:")
  -- A selector reaches what its rightmost compound matches, so both sides are read there.
  let subjects : List String := ([Ir.ListLineage.sizeFile, .beamer, .web].flatMap fun l =>
    let ex := HtmlDoc.exAt none Ir.baseFontSize
    (HtmlDoc.blockGapRules l Ir.baseFontSize ex {}).flatMap fun r => match r with
    | .boundary sel _ => (cssSelectorParts sel).filterMap fun part =>
        let s := selSubject part
        if s == "*" || s.isEmpty then none else some s
    | .reset _ _ => []
    | .parskip _ _ => []
    | .trivIn _ _ _ => []).eraseDups
  let setsMargin (decls : String) : Bool := (decls.splitOn ";").any fun d =>
    match d.splitOn ":" with
    | p :: _ :: _ => ["margin", "margin-top"].contains p.trimAscii.toString
    | _ => false
  let mut shadows : Array String := #[]
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    for (sel, decls) in artCssBlocks (HtmlDoc.baseCss {} doc) do
      if !sel.startsWith ":where(" && setsMargin decls &&
          (cssSelectorParts sel).any (fun part => subjects.any (compoundOverlaps (selSubject part))) then
        shadows := shadows.push s!"{n}: {sel}"
  t "html gap subjects are read off the emitter"
    (["p", "ul", "ol", "li", "h2", "figure.float", ".display", "blockquote"].all subjects.contains)
  unless shadows.isEmpty do IO.eprintln s!"  shadowing rules: {shadows.toList}"
  t "html: no base-sheet rule outranks a gap rule on the element it spaces" shadows.isEmpty
  t "html heading gap is two screen quanta"
    ((plainPage.splitOn ":where(* + h2) { margin-top: 1.450rem; }").length == 2)
  t "html float gap keeps its token over the rhythm default"
    ((plainPage.splitOn
      ":where(* + figure.float) { margin-top: var(--floatsep, 1.450rem); }").length == 2)
  t "html float owns the boundary below it"
    ((plainPage.splitOn
      ":where(figure.float + *) { margin-top: var(--floatsep, 1.450rem); }").length == 2)
  t "html display skips are the two tokens over TeX's long skip"
    ((plainPage.splitOn
      ":where(* + .display) { margin-top: var(--abovedisplayskip, 1.208rem); }").length == 2 &&
     (plainPage.splitOn
      ":where(.display + *) { margin-top: var(--belowdisplayskip, 1.208rem); }").length == 2 &&
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
    ((themedPage.splitOn (".progress { background: var(--ltx-sectionprogressbg);\n" ++
      "  height: var(--progressheight, 1pt);")).length == 2)
  t "html themed sheet has one gap owner per boundary"
    ((themedPage.splitOn "margin-bottom").length == 2)

/-- A list declaring its own spacing carries its class, whose rules space it at each level as the
page does: its declared values over the level's. -/
def htmlListSpacingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let page (pre body : String) : String :=
    (HtmlDoc.emit {} (elabStr (s!"\\documentclass\{article}\\usepackage\{enumitem}{pre}" ++
      s!"\\begin\{document}x\n\n{body}\\end\{document}")).1).1
  let list := "\\begin{itemize}\\item a\\item b\\end{itemize}"
  let item := "li:not(.bibliography *):not(.algorithm *):not([role=doc-endnotes] *):not(.contents *)"
  let space (m : String) := s!"calc({m}rem + var(--parskip, 0rem))"
  let tight := page "\\setlist{nosep}" list
  t "html a list declaring its spacing carries its class" (hasStr tight "<ul class=\"list-set-1\">")
  t "html a declared nosep's items stand no space apart, as on the page"
    (hasStr tight
      s!":where(.list-set-1 > li + {item}, .list-set-1 > dd + dt) \{ margin-top: {space "0.000"}; }" &&
     hasStr tight s!":where(.list-set-1 > {item}, :is(dl, blockquote).list-set-1 > *) \{ --parskip: 0.000rem; }" &&
     hasStr tight s!":where(* + .list-set-1) \{ margin-top: {space "0.000"}; }")
  -- size10.clo's level one: \topsep 8pt, \partopsep 2pt; a declared \itemsep 0pt over \parsep 4pt.
  let own := page "" ("\\begin{itemize}[itemsep=0pt]\\item a\\item b\\end{itemize}\n\n" ++ list)
  t "html a list's own option reaches that list alone"
    (hasStr own "<ul class=\"list-set-1\">" && hasStr own "<ul>" &&
     hasStr own s!":where(.list-set-1 > li + {item}, .list-set-1 > dd + dt) \{ margin-top: {space "0.000"}; }" &&
     hasStr own s!":where(* + .list-set-1) \{ margin-top: {space "1.208"}; }")
  t "html an undeclared list carries no class" (!hasStr (page "" list) "list-set")
  -- 1em at 10pt over the class's \partopsep 2pt, as the page resolves it.
  t "html a list's spacing in em reaches the web page at the page's size"
    (hasStr (page "\\setlist{topsep=1em}" list) s!":where(* + .list-set-1) \{ margin-top: {space "1.450"}; }")
  -- lualatex and the page: 13pt above and below a nested level declaring it, between outer items.
  let between := page "\\setlist[2]{topsep=13pt}"
    "\\begin{itemize}\\item a\n\\begin{itemize}\\item b\\end{itemize}\n\\item c\\end{itemize}"
  let closing (sel : String) := s!":has(> {sel}:last-child, > details[open]:last-child > {sel}:last-child)"
  t "html the item after a nested list declaring spacing stands at that list's closing skip"
    (hasStr between s!"dl):not([class*=\"list-set-\"]) > li{closing ".list-set-1.u-in-paragraph"} + {item}" &&
     hasStr between s!"\{ margin-top: {space "1.570"}; }")
  -- `\endtrivlist`: the nested list's 6pt with the outer \parsep 4pt on it, over the outer 8pt.
  let ends := page "\\setlist{topsep=6pt}"
    "\\begin{itemize}\\item a\n\\begin{itemize}\\item b\\end{itemize}\n\\end{itemize}\n\nc"
  t "html a list closing on a nested list ends on that list's skip and its own parsep"
    (hasStr ends (".list-set-1:not(.u-in-paragraph):has(> li:last-child > " ++
      ".list-set-1.u-in-paragraph:last-child") &&
     hasStr ends "margin-top: calc(max(calc(1.208rem - var(--parskip, 0rem)), 0.966rem) + var(--parskip, 0rem));")
  -- A quotation closing an item on a declared list leaves the larger skip, the list's 9pt, as the page.
  let quoted := page "\\setlist[itemize,2]{topsep=9pt}"
    ("\\begin{itemize}\\item a\n\\begin{quote}b\n\\begin{itemize}\\item c\\end{itemize}\n" ++
      "\\end{quote}\n\\item d\\end{itemize}")
  -- lualatex: the quotation's end re-skips the nested list's 9pt with its \parsep 2pt less the 4pt
  -- outside it, 7pt under the next item.
  t "html the item after a quotation closing on a declared list stands at its re-skip"
    (hasStr quoted ("li:has(> blockquote:not([class*=\"list-set-\"]).u-in-paragraph:last-child > " ++
      ".list-set-1.u-in-paragraph:last-child") && hasStr quoted s!"\{ margin-top: {space "0.845"}; }")
  -- An inline list closing on an opened one: its 8pt under the nested 6pt and its \parsep 4pt.
  let inlineEnds := (HtmlDoc.emit {} (elabStr ("\\documentclass{article}\\begin{document}" ++
    "Alpha\n\\begin{itemize}\\item a\n\n\\begin{itemize}\\item b\\end{itemize}\n\\end{itemize}" ++
    "\n\nc\\end{document}")).1).1
  t "html an undeclared inline list closing on a nested one ends on its re-skip, as the page"
    (hasStr inlineEnds ("dl):not([class*=\"list-set-\"]).u-in-paragraph:has(> li:last-child > ") &&
     hasStr inlineEnds "margin-top: calc(max(calc(1.208rem - var(--parskip, 0rem)), 0.966rem) + var(--parskip, 0rem));")
  -- A description's item reached by the spine as a list's item is.
  let described := page "\\setlist[3]{topsep=10pt}"
    ("\\begin{itemize}\\item a\n\\begin{description}\\item[T] b\n\\begin{itemize}\\item c" ++
      "\\end{itemize}\n\\end{description}\n\\end{itemize}\n\nd")
  t "html a closing spine through a description list reaches its item"
    (hasStr described "> :is(li, dd):last-child > .list-set-1.u-in-paragraph:last-child")
  -- An article's abstract closing on a declared list ends on that list's skip, as the page.
  let abstractEnds := page "\\setlist[2]{topsep=10pt}"
    "\\begin{abstract}a\n\\begin{itemize}\\item b\\end{itemize}\n\\end{abstract}\nc"
  t "html an abstract closing on a declared list ends on its skip"
    (hasStr abstractEnds (":where(.abstract.quoted:has(> .list-set-1.u-in-paragraph:last-child, " ++
      "> details[open]:last-child > .list-set-1.u-in-paragraph:last-child) + *) " ++
      s!"\{ margin-top: {space "1.208"}; }"))

/-- A list's spaces are the class's `\@list⟨n⟩` in HTML too, at each level, in the screen's quanta. -/
def htmlListGapChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let page (cls : String) : String := (HtmlDoc.emit {} (elabStr (s!"\\documentclass{cls}" ++
    "\\begin{document}x\n\n\\begin{itemize}\\item a\\item b\\end{itemize}\\end{document}")).1).1
  let item := "li:not(.bibliography *):not(.algorithm *):not([role=doc-endnotes] *):not(.contents *)"
  let space (m : String) := s!"calc({m}rem + var(--parskip, 0rem))"
  let art := page "{article}"
  -- A list level's elements, each reached through one `<li>` or `<dd>` per enclosing list.
  let elems := ["ul:not(.bibliography)", "ol:not(.algorithm):not(.algorithm *)", "blockquote", "dl",
    ".verbatim-list"]
  let lv (n : Nat) : String :=
    String.join (List.replicate n ":is(li, dd, blockquote, :where(.abstract.quoted)) ")
  let above (n : Nat) := ", ".intercalate (elems.map fun e => s!"{lv n}* + {e}")
  let below (n : Nat) := ", ".intercalate (elems.map fun e => s!"{lv n}{e} + *")
  let items (n : Nat) := s!"{lv n}li + {item}, {lv n}dd + dt"
  let parsep (n : Nat) := s!"{lv n}{item}, {lv n}blockquote > *, {lv n}dl > *"
  let lastList (n : Nat) (sel : String) :=
    let ends := s!":is({", ".intercalate elems}){sel}:last-child"
    let has := s!":has(> {ends}, > details[open]:last-child > {ends})"
    s!"{lv n}li{has} + {item}, {lv n}dd{has} + dt"
  t "html a 10pt list's items stand itemsep over the item's parsep apart"
    (hasStr art s!":where({items 0}) \{ margin-top: {space "0.483"}; }" &&
     hasStr art s!":where({parsep 0}) \{ --parskip: 0.483rem; }")
  -- `\@topsepadd`: `\topsep` plus size10.clo's 2pt `\partopsep` in vertical mode, above and below.
  t "html a 10pt list and quote opening a paragraph stand topsep and partopsep from neighbours"
    (hasStr art s!":where({above 0}) \{ margin-top: {space "1.208"}; }" &&
     hasStr art s!":where({below 0}) \{ margin-top: {space "1.208"}; }")
  t "html a 10pt list and quote inside an open paragraph stand topsep alone"
    (hasStr art s!":where(* + .u-in-paragraph) \{ margin-top: {space "0.966"}; }" &&
     hasStr art s!":where(.u-in-paragraph + *) \{ margin-top: {space "0.966"}; }")
  t "html a nested 10pt list reads its own level"
    (hasStr art s!":where({parsep 1}) \{ --parskip: 0.241rem; }" &&
     hasStr art s!":where({items 1}) \{ margin-top: {space "0.241"}; }" &&
     hasStr art s!":where({above 1}) \{ margin-top: {space "0.725"}; }" &&
     hasStr art s!":where({lv 1}* + .u-in-paragraph) \{ margin-top: {space "0.483"}; }")
  -- `\addvspace` keeps the larger: level two's 4pt + 2pt over level one's 4pt.
  t "html an item after a nested list that opened a paragraph stands the larger space"
    (hasStr art s!":where({lastList 0 ":not(.u-in-paragraph)"}) \{ margin-top: {space "0.725"}; }")
  -- size10.clo:233: level three sets its own 1pt, which a declared value does not reach.
  let declared := page "{article}\\setlength{\\partopsep}{5pt}"
  t "html a declared partopsep reaches the top level and not level three"
    (hasStr declared s!":where({above 0}) \{ margin-top: {space "1.570"}; }" &&
     hasStr declared s!":where({above 2}) \{ margin-top: {space "0.362"}; }")
  let art12 := page "[12pt]{article}"
  t "html a 12pt list reads size12's spacing"
    (hasStr art12 s!":where({parsep 0}) \{ --parskip: 0.503rem; }" &&
     hasStr art12 s!":where({above 0}) \{ margin-top: {space "1.309"}; }" &&
     hasStr art12 s!":where(* + .u-in-paragraph) \{ margin-top: {space "1.006"}; }")
  let deck := page "{beamer}"
  t "html a deck's list reads beamer's spacing, its partopsep zero"
    (hasStr deck s!":where({parsep 0}) \{ --parskip: 0.000rem; }" &&
     hasStr deck s!":where({items 0}) \{ margin-top: {space "0.329"}; }" &&
     hasStr deck s!":where({above 0}) \{ margin-top: {space "0.329"}; }" &&
     !hasStr deck ":where(* + .u-in-paragraph)" && !hasStr deck ":where(.u-in-paragraph + *")
  -- beamerbaselocalstructure.sty: level two's `\itemsep` is zero and level three's `\topsep` 2pt.
  t "html a deck's level-two item after a nested list stands level three's topsep"
    (hasStr deck s!":where({lastList 1 ""}) \{ margin-top: {space "0.219"}; }")
  let web := page "{webpage}"
  t "html a webpage's lists keep the peer gap and its items a leading"
    (!hasStr web "li + li:" && !hasStr web "dl > *) { --parskip:" &&
     hasStr web ":where(* + ul) { margin-top: var(--parskip, 0.725rem); }" &&
     hasStr web ":where(* + .u-trivlist-env) { margin-top: ")
  t "html a reference list's entries stand the page's peer gap apart"
    (hasStr art ":where(.bibliography > li + li) { margin-top: var(--parskip, 0.725rem); }")
  -- A selector list's members: its commas outside parentheses (`:is(li, dd)` holds one).
  let topParts (sel : String) : List String :=
    let (ps, cur, _) := sel.toList.foldl (fun (acc : List String × String × Nat) c =>
      let (ps, cur, d) := acc
      if c == ',' && d == 0 then (cur.trimAscii.toString :: ps, "", d)
      else (ps, cur.push c, if c == '(' then d + 1 else if c == ')' then d - 1 else d))
      ([], "", 0)
    (cur.trimAscii.toString :: ps).reverse
  let lastGap (rules : List HtmlDoc.GapRule) (subject : String) : Option String :=
    rules.foldl (fun acc r => match r with
      | .boundary sel v => if (topParts sel).contains subject then some v else acc
      | .parskip sel v => if (topParts sel).contains subject then some ("parskip " ++ v) else acc
      | .trivIn sel t p =>
        if (topParts sel).contains subject then some s!"trivIn {t} {p}" else acc
      | .reset _ _ => acc) none
  let descPairs : List (String × String) := [0, 1, 2].flatMap fun n =>
    [(s!"{lv n}* + dl", s!"{lv n}* + ul:not(.bibliography)"),
     (s!"{lv n}dl + *", s!"{lv n}ul:not(.bibliography) + *"),
     (s!"{lv n}dd + dt", s!"{lv n}li + {item}"),
     (s!"{lv n}dl > *", s!"{lv n}blockquote > *")]
  for (cls, lineage, size) in [("article", Ir.ListLineage.sizeFile, Dim.pt 10),
      ("beamer", .beamer, Dim.pt 11)] do
    let rules := HtmlDoc.blockGapRules lineage size (HtmlDoc.exAt none size) {}
    t s!"html a {cls} description's boundaries are an itemize's at every level"
      (descPairs.all fun (d, u) => (lastGap rules d).isSome && lastGap rules d == lastGap rules u)

mutual

/-- The first element child's tag of every `<section id>` a tree carries. -/
def sectionHeadsOne (acc : Array String) : Html.Node → Array String
  | .elem tag attrs kids =>
    let acc := if tag == "section" && attrs.any (·.1 == "id") then
        acc.push (match kids.toList.find? (· matches .elem _ _ _) with
          | some (.elem t _ _) => t
          | _ => "")
      else acc
    sectionHeadsList acc kids.toList
  | _ => acc

def sectionHeadsList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => sectionHeadsList (sectionHeadsOne acc k) rest

end

/-- A section's heading opens its space above in HTML too, as the first child of its `<section>`. -/
def htmlSectionGapChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}Alpha.\n\n" ++
    "\\section{Bravo}Charlie.\n\n\\section{Delta}Echo.\\end{document}")
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let page := (HtmlDoc.emit {} doc).1
  t "html section fixture elaborates clean" ds.isEmpty
  t "html every article section opens with its heading"
    (sectionHeadsList #[] body.toList == #["h2", "h2"])
  t "html a section's heading owns the heading gap above its section"
    (hasStr page ":where(* + section[id] > h2:first-child) { margin-top: 1.450rem; }")

/-- Every rule that scrolls a box on screen has a print rule at its selector setting that overflow
`visible`. -/
def printLiftChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let sets (decls prop : String) (vals : List String) : Bool :=
    (decls.splitOn ";").any fun d => match d.splitOn ":" with
      | [p, v] => p.trimAscii.toString == prop && vals.contains v.trimAscii.toString
      | _ => false
  let print (ctx : List String) : Bool := ctx.any (·.startsWith "@media print")
  let mut scrolls := 0
  let mut missing : Array String := #[]
  let mut wraps := true
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let blocks := cssBlocksIn (HtmlDoc.baseCss {} doc)
    for (ctx, sel, decls) in blocks do
      if print ctx || ctx.any (·.startsWith "@media screen") then continue
      for axis in ["overflow", "overflow-x", "overflow-y"] do
        if sets decls axis ["auto", "scroll"] then
          scrolls := scrolls + 1
          unless blocks.any (fun (c, s, d) => print c && s == sel && sets d axis ["visible"]) do
            missing := missing.push s!"{n}: {sel} {axis}"
    wraps := wraps && blocks.any fun (c, s, d) =>
      print c && s == "pre" && sets d "white-space" ["pre-wrap"]
  unless missing.isEmpty do IO.eprintln s!"  unlifted scroll boxes: {missing.toList}"
  t "print lift: the corpus sheets declare scroll boxes at all" (scrolls > 0)
  t "print lift: every box a sheet scrolls on screen grows or wraps on paper" missing.isEmpty
  t "print lift: a code block wraps a long line on paper" wraps

/-- Article sections become anchored containers: `<section id>` wraps each heading and its content,
ids stay unique, and an in-page `\href{#...}` has a target. -/
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
  let (deck, _) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}{One}a\\end{frame}\\end{document}")
  t "html slides sectioning is untouched"
    (((HtmlDoc.emit {} deck).1.splitOn "<section id=").length == 1)
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

/-- The markdown twin comes from the same IR as the page: metadata from the preamble, structure
mapped, decoration degraded to its text, a speaker note kept aside. -/
def markdownChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Alex Doe, Cartographer\", subject = \"An invented person.\" }" ++
    "\\begin{document}" ++
    "Intro with \\textbf{weight} and \\href{https://example.org}{a link}." ++
    "\\section*{Field Notes}" ++
    "Label \\hfill 1987\\par" ++
    "\\begin{itemize}\\item One thing\\item Another\\end{itemize}" ++
    "\\end{document}")
  let md := (MarkdownDoc.emit doc)
  t "markdown source is clean" ds.isEmpty
  t "markdown metadata renders as the llms.txt preamble"
    (md.startsWith "# Alex Doe, Cartographer\n\n> An invented person.\n\n")
  t "markdown keeps meaning and degrades decoration"
    ((md.splitOn "Intro with **weight** and [a link](https://example.org).").length == 2)
  t "markdown reserves # for the title"
    ((md.splitOn "\n## Field Notes\n").length == 2 && (md.splitOn "\n# ").length == 1)
  t "markdown fill separates as an em dash"
    ((md.splitOn "Label — 1987").length == 2)
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

/-- In the llms.txt preamble the summary stands right after the title line, whichever of the four
title sources carries it. -/
def mdPreambleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (metaOnly, ds1) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Meta Title\", subject = \"A meta summary.\" }" ++
    "\\begin{document}Body text.\\end{document}")
  t "metadata-only source is clean" ds1.isEmpty
  t "metadata title: summary follows the title line"
    ((MarkdownDoc.emit metaOnly) == "# Meta Title\n\n> A meta summary.\n\nBody text.\n")
  let bodyOnly : Ir.Doc := {
    info := { subject := some "A body-titled summary." }
    body := #[.section 0 false none #[.text "Body Title"], .para #[.text "After."]] }
  t "body title: summary follows the body's title line"
    ((MarkdownDoc.emit bodyOnly) ==
      "# Body Title\n\n> A body-titled summary.\n\nAfter.\n")
  let (both, ds3) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ subject = \"A shared summary.\" }\\title{Both Sources}" ++
    "\\begin{document}\\maketitle Body text.\\end{document}")
  t "both-sources source is clean" ds3.isEmpty
  let bothMd := (MarkdownDoc.emit both)
  t "both sources: the body's title line leads and the summary follows"
    (bothMd.startsWith "# Both Sources\n\n> A shared summary.\n\n")
  t "both sources: exactly one # line, the title stated once"
    ((bothMd.splitOn "\n# ").length == 1 && (bothMd.splitOn "# Both Sources").length == 2)
  let neither : Ir.Doc := {
    info := { subject := some "Only a summary." }
    body := #[.para #[.text "x"]] }
  t "no title anywhere: the summary opens the twin"
    ((MarkdownDoc.emit neither) == "> Only a summary.\n\nx\n")
  let mid : Ir.Doc := {
    info := { subject := some "A late summary." }
    body := #[.para #[.text "Lead."], .section 0 false none #[.text "Late Title"]] }
  t "a mid-document title carries the summary with it"
    ((MarkdownDoc.emit mid) == "Lead.\n\n# Late Title\n\n> A late summary.\n")
  let (sc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "{\\scshape NaCl}\\end{document}")
  t "the twin of a mixed-case small-caps run carries the authored casing"
    ((MarkdownDoc.emit sc) == "NaCl\n")
  let pipe : Ir.Doc := {
    body := #[.table #[default, default] false false
      #[#[Ir.cellOf #[.text "a|b"], Ir.cellOf #[.text "c"]]] #[] #[]] }
  t "a cell containing a pipe keeps its row"
    (((MarkdownDoc.emit pipe).splitOn "| a\\|b | c |").length == 2)

theorem heading_renderings_agree (level : Ir.HeadingLevel) :
    HtmlDoc.headingTag level = "h" ++ toString (Ir.headingRank level) ∧
    (MarkdownDoc.headingMarker level).toList =
      List.replicate (Ir.headingRank level) '#' := by
  refine ⟨rfl, ?_⟩
  simp [MarkdownDoc.headingMarker]

theorem vdist_shares_agree (keys : Ir.FrameKeys) (v : Ir.VAlign) (breakable : Bool) :
    HtmlDoc.vdistShares keys v breakable =
      ((Layout.VDist.of keys v breakable).above, (Layout.VDist.of keys v breakable).below) := rfl

/-- A line below `k` of a frame's `n` fills stands the same fraction of the leftover on the page and
on the web stage. -/
theorem fill_shares_agree (keys : Ir.FrameKeys) (v : Ir.VAlign) (breakable : Bool)
    (n k : Nat) (hn : 0 < n) :
    (Layout.VDist.of keys v breakable).filAbove k *
        ((HtmlDoc.deckSpacerShares keys breakable v n).1 + Ir.fillUnit * n +
          (HtmlDoc.deckSpacerShares keys breakable v n).2) =
      ((HtmlDoc.deckSpacerShares keys breakable v n).1 + Ir.fillUnit * k) *
        (Layout.VDist.of keys v breakable).filTotal n := by
  have hn' : (n == 0) = false := by simpa using Nat.pos_iff_ne_zero.mp hn
  simp only [Layout.VDist.of, Layout.VDist.filAbove, Layout.VDist.filTotal,
    HtmlDoc.deckSpacerShares, HtmlDoc.vdistShares, Ir.VAlign.shares, hn', Bool.or_false]
  by_cases hj : (Ir.frameGlue keys breakable v).joins = true
  · simp [hj]
  · simp [hj, Nat.mul_comm, Nat.mul_left_comm]

theorem frame_area_agree (chrome : Bool) (v : Ir.VAlign) :
    HtmlDoc.frameOpensBody chrome false v = (Layout.frameAreaFor chrome v == .text) := by
  rw [HtmlDoc.frameOpensBody_projects, Layout.frameAreaFor_projects]

/-- `{ifbackend}` content: one IR elaborated once, each backend keeping or dropping through
`Ir.keepFor`. -/
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

/-- At most one unlabeled `<nav>` per page (W0325), and every in-page link resolves to an anchor the
page emits (W0326). -/
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
  let (many, _) := elabStr ("\\documentclass{article}\\begin{document}\\href{#nowhere}{x}" ++
    String.join ((List.range 30).map fun i => s!"\\section*\{Part {i}}y") ++ "\\end{document}")
  let help := (((HtmlDoc.emit {} many).2.find? (·.code == "W0326")).bind (·.help)).getD ""
  t s!"a dangling link's help names a page's first anchors and counts the rest ({help})"
    (hasStr help " more" && (help.splitOn ", #").length ≤ 12)
  t "the spec's top fragments resolve without anchors"
    (!ddiags.any fun d =>
      (d.message.splitOn "#TOP").length > 1 || (d.message.splitOn "'#'").length > 1)

/-- The markdown twin's declared name rides the one OutputSpec, so the twin and the head's alternate
link agree. -/
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

/-- A labeled nav names its landmark, a pin becomes `position: fixed` at its declared corner in HTML
alone, and a declared reveal ships its scroll-driven CSS and constant script. -/
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
    (has page "--reveal-range: 300pt")
  t "the reveal ships its declarative form, and only that"
    (has page "@supports (animation-timeline: scroll())" &&
      has page "@keyframes ltx-reveal")
  t "the reveal ships with its reduced-motion guard"
    (has page ("@media (prefers-reduced-motion: reduce) " ++
      "{ .reveal-scroll { animation: none; } }"))
  t "no backend emits script for the reveal"
    (!has page "CSS.supports" && !has page "js-reveal" &&
      !has page "addEventListener")
  let (plain, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#one-head}{One}\\end{nav}\\section*{One Head}x\\end{document}")
  let (plainPage, _) := HtmlDoc.emit {} plain
  t "no declared reveal, no reveal css"
    (!has plainPage "ltx-reveal" && !has plainPage "CSS.supports")
  let (kept, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{ifbackend}{pdf}\\begin{nav}[label = Up, pin = bottom right, " ++
    "reveal = scroll]\\href{#one-head}{Up}\\end{nav}\\end{ifbackend}" ++
    "\\section*{One Head}x\\end{document}")
  let (keptPage, _) := HtmlDoc.emit {} kept
  t "a reveal another backend owns ships nothing on this page"
    (!has keptPage "ltx-reveal" && !has keptPage "CSS.supports")
  t "markdown drops a pinned nav" (!has (MarkdownDoc.emit doc) "[Up](#top)")
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

/-- Interaction states are style keys: `hover` and `focus` colour links, `motion` is the transition
between them, and a declared motion never ships unguarded. -/
def interactionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has := hasStr
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\palette{ ink = #1D4ED8 }" ++
    "\\style{nav}{ hover = ink, focus = ink, motion = 150ms }" ++
    "\\begin{document}\\begin{nav}\\href{#one-head}{One}\\end{nav}" ++
    "\\section*{One Head}x\\end{document}")
  t "interaction keys parse" (ds.isEmpty &&
    ((doc.styles.find? "nav").bind (·.hover)).map (·.2) == some (some (.color "ink")) &&
    ((doc.styles.find? "nav").bind (·.motion)) == some 150)
  -- `css = none` ships only the declared rules, so the guard must ride with the declaration.
  let (page, pds) := HtmlDoc.emit { css := .none } doc
  t "declared hover and focus land on the nav's links" (pds.isEmpty &&
    has page "nav a:hover { color: var(--ltx-c-ink, #1d4ed8); }" &&
    has page "nav a:focus-visible { outline-color: var(--ltx-c-ink, #1d4ed8); }")
  t "a declared motion ships with its guard even without the base sheet"
    (has page "nav a { transition: color 150ms, outline-color 150ms; }" &&
     has page ("@media (prefers-reduced-motion: reduce) " ++
       "{ nav a { transition: none; } }"))
  t "an unreadable motion duration is an error"
    (errCodes ("\\documentclass{article}\\style{nav}{ motion = fast }" ++
      "\\begin{document}x\\end{document}") == ["E0323"])

/-- The definitions of a source, docstrings stripped, that spell `animation:` without a
reduced-motion guard, a `…Guard` ending, or an allowlisted own gate. -/
private def unguardedAnimations (src : String) : Array String := Id.run do
  let ownGated := ["themeCss"]
  let stripped := match src.splitOn "/--" with
    | [] => ""
    | first :: rest => first ++ String.join (rest.map fun (seg : String) =>
        String.intercalate "-/" ((seg.splitOn "-/").drop 1))
  let mut name := ""
  let mut body := ""
  let mut blocks : Array (String × String) := #[]
  for line in stripped.splitOn "\n" do
    let head := (declarationHead line).2
    let starter := ["def ", "theorem ", "abbrev ", "opaque ", "axiom ",
      "structure ", "inductive ", "instance ", "mutual", "end "].any (head.startsWith ·)
    if starter then
      blocks := blocks.push (name, body)
      name := if head.startsWith "def " then
          (((head.splitOn "def ").getD 1 "").splitOn " ").headD ""
        else ""
      body := line
    else
      body := body ++ "\n" ++ line
  blocks := blocks.push (name, body)
  let mut faults := #[]
  for (n, b) in blocks do
    if !n.isEmpty && (b.splitOn "animation:").length > 1 then
      let lastToken := (((b.trimAscii.toString.splitOn "\n").getLast?.getD ""
        ).trimAscii.toString.splitOn " ").getLast?.getD ""
      unless (b.splitOn "prefers-reduced-motion").length > 1 ||
          lastToken.endsWith "Guard" || ownGated.contains n do
        faults := faults.push n
  return faults

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
  for declPrefix in ["", "private ", "public ", "@[inline] public ",
      "noncomputable public "] do
    let safe := declPrefix ++ "def safe := \"animation: none;\" ++ reducedMotionGuard\n"
    let unsafe_ := declPrefix ++ "def unguarded := \"animation: pulse 1s;\"\n"
    check ref s!"motion scan accepts guarded {declPrefix}declarations"
      (unguardedAnimations safe == #[])
    check ref s!"motion scan rejects unguarded {declPrefix}declarations"
      (unguardedAnimations (safe ++ unsafe_) == #["unguarded"])
    check ref s!"motion scan attributes guards to their own {declPrefix}declaration"
      (unguardedAnimations (unsafe_ ++ safe) == #["unguarded"])
  for n in unguardedAnimations (← IO.FS.readFile "LeanTex/Core/HtmlDoc.lean") do
    check ref s!"animation-emitting def carries its guard ({n})" false

/-- The paged deck's stylesheet is the slides class's own: snap paging on screen, the handout in
print, and no other class ships a deck rule. -/
def deckCssChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (deckDoc, deckDs) := elabStr (deck169 "" "\\begin{frame}{T}\nx\n\\end{frame}")
  let deckPage := (HtmlDoc.emit {} deckDoc).1
  let has := hasStr
  t "deck css fixture elaborates clean" deckDs.isEmpty
  let (deckHead, deckBody, _) := HtmlDoc.emitTree {} deckDoc
  t "code boxes keep their content height when a deck column overflows"
    ((artCssBlocks (treeCssList "" deckHead.toList)).any fun (sel, decls) =>
      sel == "pre" && has decls "flex-shrink: 0")
  let (linksDoc, linksDs) := elabStr (deck169 "\\theme{moloch}\\title{North}\\author{A}"
    ("\\maketitle\\section{Route}" ++
     "\\begin{frame}{First}A\\pause B\\end{frame}" ++
     "\\begin{frame}{Second}C\\end{frame}" ++
     "\\begin{frame}[standout]D\\end{frame}"))
  let (_, linksBody, _) := HtmlDoc.emitTree {} linksDoc
  let numbered := (elemAttrsList (fun tag => tag == "section" || tag == "div")
    #[] linksBody.toList).filterMap fun (tag, attrs) =>
      (attrs.find? (·.1 == "data-frame-number")).map fun (_, n) => (tag, n)
  t "numbered-link fixture elaborates clean" linksDs.isEmpty
  t "numbered links use the shared frame sequence once per stage, skipping unnumbered pages"
    (numbered == #[("div", "1"), ("section", "2")] &&
      linksDoc.frameNumbers.toList.filterMap id == [1, 2])
  t "the deck pages horizontally by scroll snap on the root, no scrollbar stealing width"
    (has deckPage "html { scroll-snap-type: x mandatory; overflow-y: clip; }" &&
     has deckPage "[data-snap] { scroll-snap-align: start; scroll-snap-stop: always; }")
  t "the deck is a row: main flex, each section one viewport of it"
    (has deckPage "main { display: flex; align-items: flex-start; }" &&
     has deckPage "main { max-width: none; margin: 0; font-size: " &&
     has deckPage ("section.slide, section.section-page { width: 100vw; " ++
       "flex: 0 0 100vw; height: 100dvh; overflow-y: auto;"))
  t "the deck glide ships with its reduced-motion guard"
    (has deckPage "html { scroll-behavior: smooth; }" &&
     has deckPage "@media (prefers-reduced-motion: reduce) {" &&
     has deckPage "html { scroll-behavior: auto; }")
  t "the deck slide fills the viewport as an opaque column on the declared ground"
    (has deckPage ("background: var(--ltx-bg); color: var(--ltx-fg); " ++
      "display: flex; flex-direction: column;"))
  -- Every print block the page carries: the stage's and the colour schemes'.
  let printOf (page : String) : String :=
    String.join (((page.splitOn "@media print {").drop 1).map fun b => (b.splitOn "\n}\n").headD "")
  let stageOf (page : String) : String :=
    (((page.splitOn "@media screen, print {").getD 1 "").splitOn "@media screen {").headD ""
  t "the deck prints its stages, one per sheet, on the PDF's page"
    (has (printOf deckPage) "@page { size: 453.543pt 255.118pt; margin: 0; }" &&
     has (printOf deckPage) ("section.slide, section.section-page { break-after: page; " ++
       "break-before: page; height: auto; min-height: 100dvh; overflow-y: visible; " ++
       "box-decoration-break: clone; print-color-adjust: exact; }") &&
     has (printOf deckPage) ("html { background: var(--ltx-bg); " ++
       "print-color-adjust: exact; }") &&
     has (printOf deckPage) "section.slide { padding-bottom: 0; }" &&
     has (printOf deckPage) ("section.slide::after { content: \"\"; flex: 100000000 0 0; " ++
       "max-height: var(--safearea, 6vmin); }") &&
     !has (printOf deckPage) "break-inside" &&
     has (stageOf deckPage) "section.slide, section.section-page { width: 100vw;" &&
     has (stageOf deckPage) "main { max-width: none; margin: 0; font-size: " &&
     !has (stageOf deckPage) "scroll-snap" &&
     !has (printOf deckPage) "border:" && !has deckPage "section.slide { break-after: page; }")
  t "a stepless deck ships no feature gate: the scroll is the motion"
    (!has deckPage "@supports (animation-timeline: view())" &&
     !has deckPage "@supports not" &&
     !has deckPage ".slide-track > section.slide { position: sticky" &&
     !has deckPage "ltx-push" && !has deckPage "ltx-uncover" &&
     !has deckPage "class=\"slide-track\"" && !has deckPage "class=\"snap\"" &&
     (elemAttrsList (· == "section") #[] deckBody.toList).any fun (_, attrs) =>
       attrs.contains ("data-snap", ""))
  t "the deck ships the constant keyboard script through the snap door"
    ((deckPage.splitOn "<script").length == 2 &&
     has deckPage "document.documentElement.dataset.deckScript" &&
     has deckPage "document.querySelectorAll(\"[data-snap]\")" &&
     has deckPage "scrollIntoView" && !has deckPage "/* removed */")
  t "the deck's keys leave a focused summary to toggle its disclosure"
    ((HtmlDoc.deckScript.splitOn
      "(t.tagName === \"SUMMARY\" && (e.key === \" \" || e.key === \"Enter\"))").length == 2)
  t "the deck keeps the safe area"
    (has deckPage "padding: var(--safearea, 6vmin); position: relative; }")
  for theme in "" :: Theme.builtin.map (·.name) do
    let pre := if theme.isEmpty then "" else s!"\\theme\{{theme}}"
    let (doc, _) := elabStr (deck169 pre
      "\\begin{frame}{First line\\\\Second line}\nBody.\n\\end{frame}")
    let (head, _, _) := HtmlDoc.emitTree {} doc
    let declarations := (artCssBlocks (treeCssList "" head.toList)).toList.flatMap
      fun (sel, decls) =>
        if (sel.splitOn ",").any (fun s => s.trimAscii.toString == "section.slide > header")
        then decls.splitOn ";" |>.map (·.trimAscii.toString)
        else []
    t s!"deck title bands keep their intrinsic height ({theme})"
      (declarations.contains "flex-shrink: 0" &&
       declarations.all fun d =>
         !["height", "max-height", "block-size", "max-block-size", "flex-basis"].contains
           ((d.splitOn ":").headD "").trimAscii.toString)
  -- 11pt over the 90mm stage, truncated to the printed milli.
  t "deck type is the PDF's stage ratio, in vh"
    (has deckPage "font-size: 4.295vh; line-height: 1.200; }" &&
     has deckPage "h1 { font-size: 1.728em; }" &&
     has deckPage "section.slide > header h2 { font-size: 1.440em; }")
  let (tokDoc, _) := elabStr (deck169 "\\tokens{ safearea = 20pt }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a declared safearea token overrides the engine default"
    (has (HtmlDoc.emit {} tokDoc).1 s!"--safearea: {(Dim.pt 20).toBpString}pt;")
  -- Two stages of equal height and different width emit identical screen decks; 16:10 differs.
  t "the deck page carries no stage millimetre"
    (!(deckPage.splitOn "mm").dropLast.any fun piece => piece.back.isDigit || piece.back == '.')
  let deckAt (ratio : String) : String :=
    (HtmlDoc.emit {} (elabStr
      (s!"\\documentclass[aspectratio={ratio}]\{slides}\n" ++
        "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}")).1).1
  let screenOf (page : String) : String :=
    (((page.splitOn "@media screen, print {").getD 1 "").splitOn "@media print").headD ""
  t "equal-height stages emit one screen deck: the width is never read"
    (screenOf (deckAt "169") != "" &&
     screenOf (deckAt "169") == screenOf (deckAt "149") &&
     screenOf (deckAt "169") != screenOf (deckAt "1610"))
  t "a stepless deck ships no uncover rule and no track"
    -- `--frame x` is the timeline's spelling; a `--frametitle…` token var is not a timeline.
    (!has deckPage "ltx-uncover" && !has deckPage "--frame x" &&
     !has deckPage "animation-timeline: --frame" &&
     !has deckPage "scroll-state" &&
     !has deckPage "class=\"slide-track\"" && !has deckPage "class=\"snap\"")
  t "a stepless frame owns its only reveal state on its snap page"
    ((elemAttrsList (· == "section") #[] deckBody.toList).filterMap (fun (_, attrs) =>
      if attrs.contains ("data-snap", "") then
        attrs.find? (·.1 == "data-snapped") else none) == #[("data-snapped", "1")])
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

  -- Each rule renders on one line, so the parse is line-local.
  let rules := HtmlDoc.deckRules
    { body := "4.311vh", root := "3.568vh", leading := "1.200", scale := Ir.sizeScale }
    "453.543pt 255.118pt" 38 3
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

/-- In the deck every stage-resolved image dimension ships as its share of the stage, and flow
classes keep the print reading. -/
def deckImageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let imgs := "\\includegraphics[width=0.5\\textwidth, alt={A synthetic box}]{a.png}\n\n" ++
    "\\includegraphics[height=0.4\\textheight, alt={A synthetic box}]{a.png}\n\n" ++
    "\\includegraphics[width=5cm, alt={A synthetic box}]{a.png}\n\n" ++
    "\\includegraphics[scale=0.5, alt={A synthetic box}]{a.png}\n\n" ++
    "\\begin{tikzpicture}[artifact]\n\\fill (0,0) rectangle (2,1);\n\\end{tikzpicture}"
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
  -- The shipped-page census reads `Layout.Out`, so the SVG label's floor is watched here.
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
       -- Positive too, so an empty tspan or the placeholder cannot pass.
       spans.any (fun s => shownOf s == "q=") &&
       ((labelHtml.splitOn "indigo").length == 1))
  let (art, artDs) := elabStr (dvDoc "" imgs)
  t "flow image fixture elaborates clean" artDs.isEmpty
  let artHtml := (HtmlDoc.emit { imgs := store } art).1
  let hasA (s : String) : Bool := (artHtml.splitOn s).length ≥ 2
  let artBody := ((artHtml.splitOn "<body").drop 1).headD ""
  t "flow keeps the print reading: pt lengths, no viewport unit"
    (hasA "width: 50%; height: auto" &&
     hasA "pt; height: auto" &&
     hasA "width: 72pt; height: auto" &&
     !hasStr artBody "dvh" && !hasStr artBody "vw")
  t "a flow picture keeps its pt box"
    (hasA "pt\" height=\"" || hasA "pt\" role=\"img\"")

/-- A frame's declared vertical distribution reaches the deck as flex spacers carrying the PDF's
ratios, and every slide has a unique fragment id. -/
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
    (count "flex-grow: 3618" == 1 && count "flex-grow: 2000" == 1 &&
     count "flex-grow: 1000\"" == 3 && count "flex-grow: 1500\"" == 1)
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

/-- The deck's progress hairline ships exactly when the deck draws progress, scaled by the root
scroll and reading the PDF bar's two tokens. -/
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
      "  height: var(--progressheight, 1pt); background: var(--ltx-progressfg);"))
  t "the hairline does not print: paper has no scroll, and no blank last sheet"
    (has html "@media print { .deck-progress { display: none; } }")
  let (bareDoc, _) := elabStr (deck169 "\\theme{default}"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a deck that draws no progress ships no hairline"
    (!has (HtmlDoc.emit {} bareDoc).1 "deck-progress")
  let (artDoc, _) := elabStr "\\documentclass{article}\\begin{document}x\\end{document}"
  t "no other class ships the hairline"
    (!has (HtmlDoc.emit {} artDoc).1 "deck-progress")

/-- A venue's size ladder reaches both artifacts: the PDF's named size runs and the HTML's `.size-`
rules. -/
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
    | .run _ _ _ _ _ size _ _ _ _ _ => some size
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
      | .run _ _ _ _ _ size _ _ _ _ _ => some size
      | _ => none
  t "an undeclared document keeps the engine ladder on the page"
    (psizes.contains (plain.page.fontSize * 500 / 1000))

/-- Every metadata fact lives in one `Ir.Meta` record, from which the HTML head, the llms.txt
preamble and the PDF's Info and XMP each derive. -/
def webMetaChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Alex Doe, Cartographer\", subject = \"An invented person.\"," ++
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
    (has "<meta property=\"og:title\" content=\"Alex Doe, Cartographer\">" &&
     has "<meta property=\"og:description\" content=\"An invented person.\">" &&
     has "<meta property=\"og:url\" content=\"https://example.org/alex\">" &&
     has "<meta property=\"og:image\" content=\"https://example.org/alex/card.png\">" &&
     has "<meta property=\"og:type\" content=\"website\">")
  t "html twitter derives only its card kind; the facts fall back to og"
    (has "<meta name=\"twitter:card\" content=\"summary\">" && !has "twitter:title")
  let mdPage := (HtmlDoc.emit { mdHref := some "profile.md" } doc).1
  t "html links its markdown twin as the alternate representation"
    ((mdPage.splitOn ("<link rel=\"alternate\" type=\"text/markdown\" " ++
        "href=\"profile.md\">")).length == 2 &&
     !has "rel=\"alternate\"")
  let md := (MarkdownDoc.emit doc)
  let pdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace doc geom).pages doc.info)
  t "the one declared title reaches all three surfaces"
    (has "<title>Alex Doe, Cartographer</title>" &&
     md.startsWith "# Alex Doe, Cartographer\n" &&
     bytesContain pdf "/Title (Alex Doe, Cartographer)")
  t "the one declared url reaches the pdf as XMP dc:identifier"
    (bytesContain pdf "<dc:identifier>https://example.org/alex</dc:identifier>")
  let accDoc := { doc with info := { doc.info with title := some "Café Crème" } }
  let accPdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace accDoc geom).pages accDoc.info)
  t "an accented Info title is a UTF-16BE hex string with the BOM"
    (bytesContain accPdf
      "/Title <FEFF00430061006600E900200043007200E8006D0065>")
  t "the ascii entries beside it keep the literal spelling"
    (bytesContain accPdf "/Author (Alex Doe)")
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
  let (bare, _) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Quiet Page\" }\\begin{document}x\\end{document}")
  t "html json-ld derives from the one record"
    (has "<script type=\"application/ld+json\">" &&
     has "\"@type\": \"WebPage\"" &&
     has "\"name\": \"Alex Doe, Cartographer\"" &&
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

/-- The content stream a strict viewer accepts. -/
def pdfStreamChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Preview drops a `TJ` array holding an adjustment past ±32767, so a wide gap moves by `Tm`.
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
  -- Numbers off: the plain page number would add its own `Tm`.
  let (gapDoc0, _) := Elab.run "t" "a\\hfill b\n\n\\underline{x}"
  let gapDoc := { gapDoc0 with page := { gapDoc0.page with numbers := some false } }
  let gapText := asciiText (pdfText (Pdf.write wide oneFace (layoutOf oneFace gapDoc wide).pages))
  let (adjs, empties) := tjNumbers gapText
  t "pdf never writes a TJ adjustment past sixteen bits"
    (adjs.all fun n => n.natAbs ≤ 32767)
  t "pdf writes no glyphless TJ array" (empties == 0)
  t "pdf moves the pen across a wide gap with Tm" ((gapText.splitOn " Tm\n").length == 4)

/-- Every face and size survives into the content stream. -/
def pdfFaceChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font) : IO Unit := do
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
  -- the content stream spells TeX's points in PDF's
  let tf (step : String) : String := s!"{(Ir.scaleStepIn Ir.sizeScale (Dim.pt 10) step).toBpString} Tf"
  t "pdf sets Huge at 2.488x" (bytesContain bigPdf (tf "Huge"))
  t "pdf sets small at 0.9x" (bytesContain bigPdf (tf "small"))
  t "pdf keeps the body size" (bytesContain bigPdf (tf "normalsize"))
  let plainPdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace bigDoc geom).pages)
  t "pdf embeds no unused face" (!bytesContain plainPdf "/F2 ")
  let bigPages := (layoutOf twoFace bigDoc geom).pages
  let cached := (Pdf.pageStreams geom twoFace bigPages).map fun d => (d, some (Flate.deflate d))
  let usedBig := Pdf.usedAll twoFace bigPages
  let keepBig := Pdf.keepOf usedBig
  let progs := Pdf.facePrograms twoFace usedBig
  let zFaces := (Array.range twoFace.fonts.size).map fun k =>
    ((keepBig.zip progs).find? (·.1 == k)).map fun (_, p, _) => Flate.deflate p
  t "pdf with cached streams, programs and faces is the pdf without"
    (keepBig == Pdf.keepFaces twoFace bigPages &&
      Pdf.write geom { twoFace with zdata := zFaces } bigPages (streams := cached)
        (programs := progs) ==
      Pdf.write geom twoFace bigPages)
  -- The fixture face's cap height is under its ascent, so CapHeight cannot pass as the ascent.
  let cap1000 := font.capHeight * 1000 / (font.unitsPerEm : Int)
  let asc1000 := font.ascent * 1000 / (font.unitsPerEm : Int)
  t "pdf descriptor CapHeight is the face's own, not the ascent"
    (cap1000 != asc1000 && bytesContain plainPdf s!"/CapHeight {cap1000}" &&
     !bytesContain plainPdf s!"/CapHeight {asc1000}")
  pdfStreamChecks ref oneFace

def rawPayloadChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Browsers match end tags ASCII-case-insensitively, so the terminator guard must too.
  t "html style payload cannot close its own tag in upper case"
    (((Html.render (Html.Node.style "x</STYLE>bad") 0).splitOn "</STYLE").length == 1)
  t "html style payload cannot close its own tag in mixed case inline"
    (((Html.render (Html.elem "p" #[Html.Node.style "x</Style>bad"]) 0).splitOn
      "</Style").length == 1)
  t "html script payload cannot close its own tag in upper case inline"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</SCRIPT>bad"]) 0).splitOn
      "</SCRIPT").length == 1)
  -- The terminator literal omits the closing `>`, which catches a spaced or self-closed end tag.
  t "html script payload with a spaced terminator is removed"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</script >bad"]) 0).splitOn
      "/* removed */").length == 2)
  let lowered (s term : String) : Bool := hasStr s.toLower term
  let edges := ["é</StYlE", "</sty\u0130le", "<</style", "</</style>", "x</styl", "😀</style",
    "</STYLE", "</s\u0000tyle", "", "</style", "</SCRIPT", "x</ScRiPt>", "<</script", "</scrip"]
  t "html raw payload: the byte search finds a terminator where the lowered characters hold one"
    (edges.all fun s => Html.holdsTerm s "</style" == lowered s "</style" &&
      Html.holdsTerm s "</script" == lowered s "</script")
  let alphabet : Array Char := #['<', '/', 's', 'S', 't', 'T', 'y', 'Y', 'l', 'L', 'e', 'E', 'c',
    'C', 'r', 'R', 'i', 'I', 'p', 'P', 'é', '\u0130', '😀', ' ', '>']
  let mut seed : UInt64 := 1709
  let mut misses : Array String := #[]
  let mut positives := 0
  for k in [0:3000] do
    let (len, s1) := rand seed 14
    seed := s1
    let mut text := ""
    for _ in [0:len] do
      let (pick, s2) := rand seed alphabet.size
      seed := s2
      text := text.push (alphabet[pick]?.getD 'x')
    -- Every other text splices a terminator in random case among the random characters.
    if k % 2 == 0 then
      let term := if k % 4 == 0 then "</style" else "</script"
      let mut cased := ""
      for c in term.toList do
        let (up, s3) := rand seed 2
        seed := s3
        cased := cased.push (if up == 1 then c.toUpper else c)
      let (at_, s4) := rand seed (text.length + 1)
      seed := s4
      text := String.ofList (text.toList.take at_) ++ cased ++ String.ofList (text.toList.drop at_)
    if lowered text "</style" || lowered text "</script" then positives := positives + 1
    unless Html.holdsTerm text "</style" == lowered text "</style" &&
        Html.holdsTerm text "</script" == lowered text "</script" do
      misses := misses.push text
  t s!"html raw payload: half the random texts hold a terminator ({positives} of 3000)"
    (positives ≥ 1500)
  t s!"html raw payload: random texts read alike off bytes and characters (differing: \
{misses.toList.take 3})" misses.isEmpty

/-- The pre-commit gate's own predicates, through the script's `--selftest` mode. -/
def precommitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let build ← IO.Process.output
    { cmd := "lake", args := #["build", "precommit", "-q"] }
  check ref s!"gate scripts build:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    let out ← IO.Process.output
      { cmd := ".lake/build/bin/precommit", args := #["--selftest"] }
    check ref s!"precommit selftest:\n{out.stderr}" (out.exitCode == 0)

/-- A fact both backends render from every golden fixture renders the same from `Layout.Out` and the
typed HTML tree, or a diagnostic names the divergence. -/
def agreeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let namingCodes := ["W0007", "W0331", "W0332"]
  for n in goldenNames do
    let (doc, docDs) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom (some pats)
    let (_, body, htmlDs) := HtmlDoc.emitTree {} doc
    let naming := (docDs ++ out.diags ++ htmlDs).any (namingCodes.contains ·.code)
    let pdf := dedupConsecutive (pdfFoots out)
    -- Both sides collapse a stepped frame's repeated footer, one section or page per step.
    let html := dedupConsecutive (slideFootsList #[] body.toList)
    check ref s!"agree {n}: footer slots match across backends, or are named"
      (pdf == html || naming)
    for (element, st) in doc.styles.entries do
      if let some m := st.marker then
        match HtmlDoc.markerCss? m with
        | some r =>
          check ref s!"agree {n}: the '{element}' marker's HTML text is the declared text"
            (r.text == Ir.plainText m)
        | none =>
          check ref s!"agree {n}: the '{element}' marker's substitution is named"
            (htmlDs.any (·.code == "W0331"))

/- One code, one meaning: the spec's code strings are unique, each carries a meaning, and no
constructor outlives its last emission site. -/

def renderChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let d : Diag := Diag.of .E0001 "bad \"quote\"\nline"
    (some ⟨"a.tex", { line := 3, col := 7 }⟩)
    (help := "fix it")
  t "porcelain diag" (Render.porcelainDiag d ==
    "{\"event\":\"diagnostic\",\"severity\":\"error\",\"code\":\"E0001\",\"loss\":\"dropped\"," ++
    "\"message\":\"bad \\\"quote\\\"\\nline\",\"file\":\"a.tex\",\"line\":3,\"col\":7," ++
    "\"help\":\"fix it\"}")
  t "porcelain summary" (Render.porcelainSummary "a.tex" false 2 17 ==
    "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":2,\"ms\":17}")
  t "porcelain summary of a failed run that wrote some artifacts names them"
    (Render.porcelainSummary "a.tex" false 1 17 #["a.html", "a.md"] ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"output\":\"a.html, a.md\",\"errors\":1,\"ms\":17}")
  t "human summary of a failed run that wrote some artifacts names them"
    (Render.humanSummary false "a.tex" 1 17 #["a.html"] == "✖ a.tex — 1 error; wrote a.html (17 ms)")
  t "human summary spells out a control character in a written path"
    (Render.humanSummary false "a.tex" 1 17 #["a\nb.html"] == "✖ a.tex — 1 error; wrote a\\nb.html (17 ms)")
  t "human phase line spells out a tool's control characters"
    (Render.humanPhase "boundary" "x\u001b]0;t\u0007y" 3 == "boundary: x\\x1b]0;t\\x07y (3 ms)")

  t "human diag plain" (Render.human false d ==
    "a.tex:3:7: error: bad \"quote\"\\nline [E0001]\n  note: fix it")

def linkHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
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
  let inlineMacro := "\\documentclass{article}\n" ++
    "\\define \\who(a: text) {\\textbf{\\a}}\n" ++
    "\\begin{document}\\who{Ada} wrote it\\end{document}"
  let (imDoc, _) := elabStr inlineMacro
  t "inline macro does not split the paragraph" (imDoc.body.size == 1)

  let escaped := Html.escapeText "a <script> & \"x\""
  t "html escapes text" (escaped == "a &lt;script&gt; &amp; \"x\"")
  t "html escapes attributes" (Html.escapeAttr "a\"b<c" == "a&quot;b&lt;c")
  t "html escapes every reserved character beside other text"
    (Html.escapeAttr "é\"'<>&x" == "é&quot;&#39;&lt;&gt;&amp;x" &&
      Html.escapeText "é\"'<>&x" == "é\"'&lt;&gt;&amp;x" &&
      Html.escapeText "plain ✓ text" == "plain ✓ text")
  -- RFC 4648 §4's alphabet read by index, the oracle for the page's data URLs
  let reference (bytes : ByteArray) : String := Id.run do
    let alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
    let mut out := ""
    for i in [0:(bytes.size + 2) / 3] do
      let a := (bytes[i * 3]?.getD 0).toNat
      let b := (bytes[i * 3 + 1]?.getD 0).toNat
      let c := (bytes[i * 3 + 2]?.getD 0).toNat
      out := out.push (alphabet.getD (a / 4) '=')
      out := out.push (alphabet.getD ((a % 4) * 16 + b / 16) '=')
      out := out.push (if i * 3 + 1 < bytes.size then alphabet.getD ((b % 16) * 4 + c / 64) '='
        else '=')
      out := out.push (if i * 3 + 2 < bytes.size then alphabet.getD (c % 64) '=' else '=')
    return out
  let samples := (List.range 70).map fun n =>
    ByteArray.mk ((Array.range n).map fun i => (i * 37 + n * 11).toUInt8)
  let long := (List.range 3).map fun r =>
    ByteArray.mk ((Array.range (12288 + r)).map fun i => (i * i * 131 + i / 7 + r).toUInt8)
  t "base64 agrees with the reference encoder"
    ((ByteArray.mk ((Array.range 256).map (·.toUInt8)) :: samples ++ long).all fun b =>
      HtmlResource.base64 b == reference b)
  t "html void element has no closing tag"
    (Html.render (Html.elem "br" #[]) 0 == "<br>\n")
  t "html phrasing content stays on one line"
    (Html.render (Html.elem "p" #[Html.text "a ", Html.elem "em" #[Html.text "b"],
      Html.text ", c"]) 0 == "<p>a <em>b</em>, c</p>\n")
  t "html style payload cannot close its own tag"
    (((Html.render (Html.Node.style "x</style>bad") 0).splitOn "</style>").length == 2)
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
    ((page.splitOn "var(--ltx-c-primary, #7c3aed)").length == 2)
  t "html link has href"
    ((page.splitOn
      "<a href=\"https://example.org\" style=\"color: inherit\">link</a>").length == 2)
  t "html single-para item is not wrapped"
    ((page.splitOn "<li>One</li>").length == 2)
  t "html inlines the stylesheet" ((page.splitOn "<style>").length == 2)
  t "html declares the generator" ((page.splitOn "content=\"leantex\"").length == 2)

  let (_, runHtmlDiags) := HtmlDoc.emit {} runDoc
  t "html warns about running content" (runHtmlDiags.any (·.code == "W0007"))

  let (bulmaPage, _) := HtmlDoc.emit { css := .bulma } htmlDoc
  t "bulma mode binds primary" ((bulmaPage.splitOn "--bulma-primary").length == 2)
  t "bulma mode ships no base sheet" ((bulmaPage.splitOn "--measure").length == 1)
  let (barePage, _) := HtmlDoc.emit { css := .none } htmlDoc
  t "css none emits no style element" ((barePage.splitOn "<style>").length == 1)

  -- A `<br>` cannot end a layout row, so the break is structural.
  let (rowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\\\second\\end{document}")
  let (rowPage, _) := HtmlDoc.emit {} rowDoc
  t "broken stretched row becomes rows"
    ((rowPage.splitOn "<span class=\"entry-row").length == 3)
  t "broken stretched row keeps no br" ((rowPage.splitOn "<br>").length == 1)
  let (oneRowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\end{document}")
  t "unbroken stretched row stays one row"
    (((HtmlDoc.emit {} oneRowDoc).1.splitOn "class=\"entry entry-pair\"").length == 2)

  let (fillDoc, fillDs) := elabStr "a \\hfill b"
  t "hfill source clean" fillDs.isEmpty
  t "hfill becomes an inline fill" (fillDoc.body ==
    #[.para #[.text "a ", .fill, .text "b"]])
  t "thin space escape" ((elabStr "a\\,b").1.body ==
    #[.para #[.text "a b"]])

/-- The faces a page ships are the faces its text selects: a style no text takes ships no face, a
style some text takes ships its face, and a sheet the page loads from elsewhere ships every face. -/
def faceUseChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pick (want : Nat × Bool) (faces : List (Nat × Bool)) : Option (Nat × Bool) :=
    HtmlFaces.select? id want faces
  t "face use: weight 600 takes 700 over 400 (CSS Fonts 4 §5.2)"
    (pick (600, false) [(400, false), (700, false)] == some (700, false))
  t "face use: weight 450 takes 400, below before above 500"
    (pick (450, false) [(400, false), (700, false)] == some (400, false))
  t "face use: weight 300 takes the lightest above when none is below"
    (pick (300, false) [(700, false), (400, false)] == some (400, false))
  t "face use: style outranks weight"
    (pick (700, true) [(700, false), (400, true)] == some (400, true))
  let load := loadTestFont
  let names := #["OpenSans-Regular.ttf", "OpenSans-Bold.ttf", "OpenSans-Italic.ttf",
    "OpenSans-BoldItalic.ttf", "SourceCodePro-Regular.otf"]
  let mut fonts : Array Font := #[]
  for n in names do
    match ← load n with
    | some f => fonts := fonts.push f
    | none => t s!"face use: {n} loads" false
  if fonts.size != names.size then return
  let variants (slot : Nat) : Array ((Nat × Nat × Bool) × Nat) :=
    #[((slot, 400, false), 0), ((slot, 700, false), 1), ((slot, 400, true), 2),
      ((slot, 700, true), 3)]
  let fs : Font.FontSet := { fonts, index := variants 0 ++ variants 1 ++
    #[((2, 400, false), 4), ((2, 700, false), 4), ((2, 400, true), 4), ((2, 700, true), 4)] }
  let shipped (body : String) : IO (Array Nat) := do
    let (doc, _) ← elabFixture "face-use"
      ("\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n")
    let (html, _) := HtmlDoc.emit { fonts := some fs } doc
    return (List.range fonts.size).toArray.filter fun i =>
      (html.splitOn (HtmlDoc.fontResource (fs.get i)).uri).length ≥ 2
  t "face use: upright prose ships the upright face alone"
    ((← shipped "Invented words, set upright.") == #[0])
  t "face use: an emphasis ships the italic face beside it"
    ((← shipped "Invented words with \\emph{one} stressed.") == #[0, 2])
  t "face use: bold emphasis ships the bold italic face, and the bold box's own beside it"
    ((← shipped "Invented \\textbf{\\emph{words}} here.") == #[0, 1, 3])
  t "face use: a heading ships the bold face its weight selects"
    ((← shipped "\\section{Invented}\nWords.") == #[0, 1])
  t "face use: code ships the typewriter face"
    ((← shipped "Invented \\texttt{code}.") == #[0, 4])
  t "face use: a heading holding only code ships the face that sets its line (CSS Fonts 4 §5.4)"
    ((← shipped "\\section*{\\texttt{code}}\nWords.") == #[0, 1, 4])
  let (doc, _) ← elabFixture "face-use"
    "\\documentclass{article}\n\\begin{document}\nInvented words.\n\\end{document}\n"
  let (html, _) := HtmlDoc.emit { fonts := some fs, mathRenderer := some "/* invented */" } doc
  t "face use: a page a math renderer may rewrite ships every face"
    ((List.range fonts.size).all fun i =>
      (html.splitOn (HtmlDoc.fontResource (fs.get i)).uri).length ≥ 2)
  let reads (css : String) : Bool := (HtmlFaces.requests #[.style css] #[] #[]).isSome
  let asks (text : String) (c : Char) : Bool :=
    match HtmlFaces.requests #[] #[.text text] #[] with
    | some reqs => reqs.toList.any (·.2.contains c)
    | none => false
  let asksIn (css : String) (body : Array Html.Node) (c : Char) : Bool :=
    match HtmlFaces.requests #[.style css] body #[] with
    | some reqs => reqs.toList.any (·.2.contains c)
    | none => false
  let sc (text : String) := #[Html.Node.elem "span" #[("class", "sc")] #[.text text]]
  t "face use: text set in capitals asks its letters' Unicode capitals, other text none"
    (asksIn ".sc { font-variant-caps: all-small-caps }" (sc "éß") 'É' &&
      asksIn ".sc { text-transform: uppercase }" (sc "ǆ") 'Ǆ' &&
      asksIn ".sc { font-variant: small-caps }" (sc "ß") 'S' &&
      !asks "éɐ" 'É' && !asks "ɐ" '\u2C6F' &&
      !asksIn ".sc { font-variant-caps: all-small-caps } .sc span { font-variant: normal }"
        #[Html.Node.elem "span" #[("class", "sc")] #[Html.Node.elem "span" #[] #[.text "é"]]] 'É' &&
      !asksIn ".sc { text-transform: lowercase }" (sc "é") 'É')
  t "face use: a space a shaper sets from U+0020 asks the space, never a face of its own"
    (!asks "a\u2003b" '\u2003' && !asks "a\u00a0b" '\u00a0' && asks "a\u2003b" ' ')
  let item := Html.Node.elem "li" #[] #[.text "x"]
  let list (tag : String) (kids : Array Html.Node) := Html.Node.elem tag #[] kids
  t "face use: a list item asks its list style's marker, a nested one its own"
    (asksIn "" #[list "ul" #[item]] '•' && !asksIn "" #[list "ul" #[item]] '▪' &&
      asksIn "" #[list "ul" #[list "li" #[list "ul" #[list "li" #[list "ul" #[item]]]]]] '▪' &&
      asksIn "" #[list "ol" #[item]] '7' && !asksIn "" #[list "ol" #[item]] '•')
  t "face use: a marker's content, or a list style the sheet sets, decides its characters"
    (!asksIn "li::marker { content: \"–\" }" #[list "ul" #[item]] '•' &&
      asksIn "li::marker { content: \"–\" }" #[list "ul" #[item]] '–' &&
      asksIn "ul { list-style: square inside }" #[list "ul" #[item]] '▪' &&
      !asksIn "ul { list-style: none }" #[list "ul" #[item]] '•' &&
      asksIn "ul { list-style-type: symbols(cyclic \"*\") }" #[list "ul" #[item]] '▪')
  t "face use: a disclosure's summary asks both of its markers"
    (asksIn "" #[list "details" #[list "summary" #[.text "x"]]] '▸' &&
      asksIn "" #[list "details" #[list "summary" #[.text "x"]]] '▾')
  t "face use: a sheet's nested rule, registered property but a length or rollback leaves every face"
    (reads "p { font-weight: bold }" && !reads "p { & em { font-weight: bold } }" &&
      !reads "@property --w { syntax: '*'; inherits: true; initial-value: bold }" &&
      reads "@property --w { syntax: \"<length>\"; inherits: true; initial-value: 0px }" &&
      !reads "em { font-style: revert }" &&
      !reads "@page { @top-center { content: \"x\" } }" && reads "@page { margin: 1cm }")
  t "face use: an import the sheet's end ends, in any case, leaves every face"
    (!reads "@import url(x.css);" && !reads "@import url(x.css)" && !reads "@IMPORT 'x.css'")
  t "face use: a quote keyword in content may set any quotation mark"
    ((HtmlFaces.contentChars #[] "open-quote").contains '“' &&
      (HtmlFaces.contentChars #[] "close-quote").contains '»' &&
      (HtmlFaces.contentChars #[] "\"x\"") == "x")
  t "face use: a content string's escapes read as CSS Syntax reads them"
    (HtmlFaces.unescape "\\3c x\\\"y\\\n".toList == "<x\"y" &&
      HtmlFaces.unescape "\\1D44E".toList == "𝑎" && HtmlFaces.unescape "\\".toList == "")
  let literals (call : String) : List String := ((HtmlDoc.deckScript.splitOn call).drop 1).filterMap
    fun rest => ((rest.drop 1).toString.splitOn "\"").head?
  t "face use: the classes the deck script sets are the ones the reading assumes"
    (((literals "classList.toggle(") ++ literals "classList.add(").all
        HtmlDoc.deckScriptClasses.contains &&
      !hasStr HtmlDoc.deckScript "className" && !hasStr HtmlDoc.deckScript "setAttribute(\"class")
  let (doc, _) ← elabFixture "face-use" ("\\documentclass{article}\n" ++
    "\\output{ formats = html, stylesheet = \"page.css\" }\n" ++
    "\\begin{document}\nInvented words.\n\\end{document}\n")
  let (head, body, _) := HtmlDoc.emitTree { fonts := some fs } doc
  t "face use: a sheet the page loads from elsewhere leaves every face shipped"
    ((HtmlDoc.faceUses fs head body).isNone &&
      (HtmlDoc.shipFaces fs #[] (HtmlDoc.faceUses fs head body)).size == (HtmlDoc.allFaces fs).size)

/-- The page ships the faces it names: one `@font-face` rule per face its text selects, every
referenced file written, the generic keyword read from the face's OS/2 class. -/
def fontShipChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load := loadTestFont
  let some sans ← load "OpenSans-Regular.ttf"
    | t "font ship: OpenSans-Regular loads" false
  let some code ← load "SourceCodePro-Regular.otf"
    | t "font ship: SourceCodePro-Regular loads" false
  let some icons ← load "ExampleIcons-Regular.ttf"
    | t "font ship: ExampleIcons-Regular loads" false
  t "font ship: Open Sans declares OS/2 class 8, Source Code Pro none"
    (sans.familyClass == 8 && code.familyClass == 0)
  t "font ship: fsType embedding bits are recorded as declared"
    (sans.fsType == 0 && icons.fsType == 4)
  let fs : Font.FontSet := {
    fonts := #[sans, code]
    index := ((List.range 2).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 0),
       ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray ++
      #[((2, 400, false), 1), ((2, 700, false), 1),
        ((2, 400, true), 1), ((2, 700, true), 1)] }
  let src ← IO.FS.readFile "testdata/corpus/deck.tex"
  let (doc, _) ← elabFixture "deck" src
  let cfg : HtmlDoc.Config := { fonts := some fs }
  let (html, _) := HtmlDoc.emit cfg doc
  let (deckHead, deckBody, _) := HtmlDoc.emitTree cfg doc
  let faces := HtmlDoc.shipFaces fs #[] (HtmlDoc.faceUses fs deckHead deckBody)
  t "census deck html: one @font-face per face its text selects"
    ((html.splitOn "@font-face").length == faces.size + 1)
  t "census deck html: the font-family variables name the synthetic families"
    (((html.splitOn "--font-body: \"ltx-body\"").length == 2) &&
     ((html.splitOn "--font-mono: \"ltx-mono\"").length == 2))
  t "font ship: slots resolving to the same faces share one family, its programs shipped once"
    (((html.splitOn "--font-sans: \"ltx-body\"").length == 2) &&
     !hasStr html "font-family: \"ltx-sans\"" &&
     (html.splitOn (HtmlDoc.fontResource sans).uri).length == 2)
  -- Each slot's stack opens on a family whose @font-face rules are exactly that slot's faces.
  let slotFacesOf (set : Font.FontSet) (slot : Nat) : List Nat :=
    (List.range set.fonts.size).filter fun i => set.index.any fun e => e.1.1 == slot && e.2 == i
  let opening := stackOpening
  let familyFaces (set : Font.FontSet) (fam : String) : List Nat :=
    ((((HtmlDoc.allFaces set).filter (·.family == fam)).toList.map (·.index)).eraseDups).mergeSort
      (· ≤ ·)
  let opensOnOwnFaces (set : Font.FontSet) (page : String) : Bool :=
    [("body", 0), ("sans", 1), ("mono", 2)].all fun (var, slot) =>
      (opening page var).any fun fam => familyFaces set fam == slotFacesOf set slot
  let variants (slot face : Nat) : Array ((Nat × Nat × Bool) × Nat) :=
    #[((slot, 400, false), face), ((slot, 700, false), face), ((slot, 400, true), face),
      ((slot, 700, true), face)]
  let fsMonoBody : Font.FontSet :=
    { fonts := #[sans, code], index := variants 0 0 ++ variants 1 1 ++ variants 2 0 }
  let fsPartial : Font.FontSet :=
    { fonts := #[sans, code], index := variants 0 0 ++ variants 2 1 ++
        #[((1, 400, false), 0), ((1, 700, false), 1), ((1, 400, true), 0), ((1, 700, true), 1)] }
  let fsFamily : Font.FontSet :=
    { fonts := #[sans, code], index := variants 0 0 ++ variants 1 0 ++ variants 2 1 ++
        variants Ir.familySlotBase 0 }
  let pageOf (set : Font.FontSet) : String := (HtmlDoc.emit { cfg with fonts := some set } doc).1
  t "font ship: every slot's stack opens on a family shipping exactly that slot's faces"
    ([fs, fsMonoBody, fsPartial, fsFamily].all fun set => opensOnOwnFaces set (pageOf set))
  t "font ship: a typewriter slot resolving to the body's faces opens on the body's family"
    (opening (pageOf fsMonoBody) "mono" == some "ltx-body")
  t "font ship: slots sharing only some faces keep families of their own"
    (opening (pageOf fsPartial) "sans" == some "ltx-sans" &&
      hasStr (pageOf fsPartial) "font-family: \"ltx-sans\"")
  t "font ship: a declared family resolving to the body's faces ships under the body's family"
    (!((HtmlDoc.allFaces fsFamily).any (·.family == s!"ltx-{Ir.familySlotBase}")) &&
      (HtmlDoc.familiesOf fsFamily 0).contains "ltx-body")
  let (famDoc, _) ← elabFixture "deck-family"
    (src.replace "\\begin{document}" "\\newfontfamily\\probeA{Open Sans}\n\\begin{document}")
  let famPage (set : Font.FontSet) : String := (HtmlDoc.emit { cfg with fonts := some set } famDoc).1
  let declared := toString Ir.familySlotBase
  t "font ship: a declared family's stack opens on a family shipping exactly its slot's faces"
    (opensOnOwnFaces fsFamily (famPage fsFamily) &&
      (opening (famPage fsFamily) declared).any fun fam =>
        familyFaces fsFamily fam == slotFacesOf fsFamily Ir.familySlotBase)
  t "font ship: a declared family resolving to the body's faces opens on the body's family"
    (opening (famPage fsFamily) declared == some "ltx-body")
  t "font ship: a declared family resolving no face opens on the body's family, naming none undefined"
    (opening (famPage fs) declared == some "ltx-body" &&
      !hasStr (famPage fs) s!"\"ltx-{declared}\"")
  t "font ship: a face is embedded exactly when the page's text selects it"
    ((List.range fs.fonts.size).all fun i =>
      ((html.splitOn (HtmlDoc.fontResource (fs.get i)).uri).length ≥ 2) ==
        faces.any (·.index == i))
  t "font ship: one captured resource per face, carrying its bytes"
    ((HtmlDoc.fontResources fs).size == fs.fonts.size &&
     (HtmlDoc.fontResources fs).all fun a => !a.bytes.isEmpty)
  t "font ship: the OS/2 sans class closes the body stack, not the slot's serif"
    ((html.splitOn "--font-body: \"ltx-body\", \"ltx-mono\", sans-serif;").length == 2)
  t "font ship: an undeclared class takes the slot's kind"
    ((html.splitOn "--font-mono: \"ltx-mono\", \"ltx-body\", monospace;").length == 2)
  t "font ship: the body weight is the resolved face's, and nothing is faked"
    ((html.splitOn "body { font-weight: 400; --ltx-body-weight: 400; font-synthesis: small-caps; }").length == 2)
  let fsFb : Font.FontSet := { fs with fonts := fs.fonts.push icons }
  let (htmlFb, _) := HtmlDoc.emit { cfg with fonts := some fsFb } doc
  let iconChar := ((List.range 0x1900).map (fun k => Char.ofNat (0xE000 + k))).find? fun c =>
    (icons.gid c).isSome && (sans.gid c).isNone && (code.gid c).isNone
  let (iconDoc, _) ← elabFixture "deck-icon" (src.replace "\\end{document}"
    (s!"Invented {(iconChar.map String.singleton).getD ""} mark.\n" ++ "\\end{document}"))
  let (htmlIcon, _) := HtmlDoc.emit { cfg with fonts := some fsFb } iconDoc
  t "font ship: a slotless face stands in every stack under its fallback family"
    ((htmlFb.splitOn
        "--font-body: \"ltx-body\", \"ltx-mono\", \"ltx-fb2\", sans-serif;").length == 2)
  t "font ship: a slotless face ships only where text falls back to it"
    (iconChar.isSome && ((htmlFb.splitOn "font-family: \"ltx-fb2\"").length == 1) &&
      ((htmlIcon.splitOn "font-family: \"ltx-fb2\"").length == 2))
  let fsMath : Font.FontSet := { fs with math := some 1 }
  let (htmlMath, _) := HtmlDoc.emit { cfg with fonts := some fsMath } doc
  t "font ship: the resolved math face lands in --font-math"
    ((htmlMath.splitOn "--font-math: \"ltx-math\", \"ltx-body\", \"ltx-mono\", math;").length == 2)
  t "font ship: .math reads the document's math face through its token"
    ((htmlMath.splitOn ".math { font-family: var(--font-math,").length == 2)
  t "font ship: a config with no set ships no rules"
    (((HtmlDoc.emit {} doc).1.splitOn "@font-face").length == 1)
  let mkF (cls : Nat) (fixed : Bool) : Font :=
    { (default : Font) with familyClass := cls, isFixedPitch := fixed }
  t "generic keyword: class 8 is sans-serif"
    (HtmlDoc.genericFor (oneFaceOf (mkF 8 false)) 0 "serif" == "sans-serif")
  t "generic keyword: classes 1-7 are serif"
    (HtmlDoc.genericFor (oneFaceOf (mkF 3 false)) 1 "sans-serif" == "serif")
  t "generic keyword: fixed pitch is monospace whatever the class"
    (HtmlDoc.genericFor (oneFaceOf (mkF 8 true)) 0 "serif" == "monospace")
  t "generic keyword: an undeclared class takes the slot's declared kind"
    (HtmlDoc.genericFor (oneFaceOf (mkF 0 false)) 0 "serif" == "serif")

/-- Footnotes: the HTML mark is a `doc-noteref` link, one `doc-endnotes` section holds each body
once with its backlink, and the markdown twin sets `[^k]` marks with definitions after the body. -/
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
     (html.splitOn "href=\"#fnref2\"").length == 2 &&
     (html.splitOn "value=\"7\"").length == 2)
  t "html: the note anchors resolve both ways (W0326 silent)"
    (hds.all (·.code != "W0326"))
  -- A book restarts its notes at each chapter: each mark takes its own anchor and its note's place,
  -- equal words in two chapters included, and each item shows its mark's number.
  let (book, _) := elabStr ("\\documentclass{book}\\begin{document}\\chapter{One}A\\footnote{Same}" ++
    " B\\footnote{second}.\n\n\\chapter{Two}C\\footnote{Same}.\\end{document}")
  let (bookHtml, bookDs) := HtmlDoc.emit {} book
  let count (s : String) : Nat := (bookHtml.splitOn s).length - 1
  t s!"html: restarted notes keep distinct anchors, each item showing its mark's number"
    ((List.range 3).all (fun i => count s!"id=\"fn{i + 1}\"" == 1 && count s!"id=\"fnref{i + 1}\"" == 1 &&
      count s!"href=\"#fn{i + 1}\"" == 1 && count s!"href=\"#fnref{i + 1}\"" == 1) &&
     count "value=\"1\"" == 2 && bookDs.all (·.code != "W0326") &&
     ((bookHtml.splitOn "<li ").drop 1).zipIdx.all fun (item, i) =>
       hasStr item s!"id=\"fn{i + 1}\"" && hasStr item s!"href=\"#fnref{i + 1}\"")
  -- A speaker note's mark has no endnote, so it links nowhere.
  let (deck, _) := elabStr ("\\documentclass{beamer}\\begin{document}\\begin{frame}A\\footnote[5]{shown}" ++
    "\\note{Speaker\\footnote[5]{shown}}\\end{frame}\\end{document}")
  let (deckHtml, _) := HtmlDoc.emit {} deck
  t "html: a speaker note's mark takes no note's anchor"
    ((deckHtml.splitOn "id=\"fnref1\"").length == 2 && (deckHtml.splitOn "href=\"#fn1\"").length == 2)
  t "html: the apparatus ships no script"
    ((html.splitOn "<script").length == 1)
  let md := MarkdownDoc.emit doc
  t "md: the marks are labels numbered by their place, whatever mark a note shows"
    ((md.splitOn "[^1]").length ≥ 2 && (md.splitOn "[^2]").length ≥ 2 && !hasStr md "[^7]")
  t "md: the definitions land after the body"
    ((md.splitOn "[^1]: the note text").length == 2 &&
     (md.splitOn "[^2]: a seventh aside").length == 2)
  t "md: a noted document keeps one trailing newline"
    (md.endsWith "\n" && !(md.endsWith "\n\n"))
  t "md: an unnoted document is unchanged in shape"
    (let md0 := MarkdownDoc.emit (elabStr (dvDoc "" "plain words")).1
     md0.endsWith "\n" && !(md0.endsWith "\n\n") && !((md0.splitOn "[^").length ≥ 2))

/-- `\includegraphics{x.pdf}` embeds page 1 as a form XObject, read from a fixture the engine itself
wrote. -/
def pdfFormChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pdfData ← IO.FS.readBinFile "testdata/corpus/figures/box.pdf"
  let inf? := Image.decode pdfData
  t "shipped pdf decodes as a form"
    (match inf? with
     | .ok inf => inf.form.isSome && inf.data.isEmpty
     | .error _ => false)
  -- The writer rounds each edge once at a thousandth of a point, hence the tolerance.
  t "pdf intrinsic size is the page box"
    (match inf? with
     | .ok inf =>
       (Dim.mm 90 - inf.width).abs ≤ Dim.Length.ofBpMilli 1 &&
       (Dim.mm 54 - inf.height).abs ≤ Dim.Length.ofBpMilli 1
     | .error _ => false)
  t "pdf resources graph copied with the page"
    (match inf? with
     | .ok inf =>
       (inf.form.map fun f =>
         f.val.objects.size > 0 && !f.val.content.isEmpty).getD false
     | .error _ => false)
  t "pdf decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (pdfData.extract 0 (pdfData.size * k / 64))).isOk).length == 64)
  t "pdf decode rejects a headerless tail"
    ((Image.decode (pdfData.extract 4 pdfData.size)).isOk == false)
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
  let segs := Id.run do
    let mut acc : Array (Option Nat × Dim.Length × Dim.Length) := #[]
    for p in out.pages do
      for l in p.lines do
        for s in l.segs do
          if let .image idx w h _ _ _ := s then acc := acc.push (idx, w, h)
    return acc
  t "pdf figure places at the declared width"
    (match inf?, segs with
     | .ok inf, #[(some 0, w, h)] =>
       w == Dim.pt 100 && h == (Dim.pt 100).mulDiv inf.height inf.width
     | _, _ => false)

/-- `algNest`'s forest renders as one `<li>` per node and one nested `<ol>` per level, in census
order, an else at its if's level. -/
def algorithmBackendChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let emitOf (body : String) : String :=
    (HtmlDoc.emit {} (elabStr (dvDoc "" body)).1).1
  let html := emitOf ("\\begin{algorithm}\n\\caption{An invented check.}\n" ++
    "\\eIf{$a > 0$}{one\\;}{two\\;}\n\\Return{$r$}\\;\n\\end{algorithm}")
  t "algorithm html: one list item per line"
    (((html.splitOn "<li>").length - 1) == 6)
  t "algorithm html: eIf nests each branch once"
    (((html.splitOn "<ol").length - 1) == 3)
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
  t "algorithm html: the else closes its then-branch first"
    (inOrder html ["one;", "</ol>", "<strong>else</strong>"])
  let deep := emitOf ("\\begin{algorithm}\n" ++
    "\\For{$i$}{\\While{$c$}{step\\;}}\n\\end{algorithm}")
  t "algorithm html: nested loops nest their lists"
    (((deep.splitOn "<ol").length - 1) == 3 &&
      inOrder deep ["<strong>for</strong>", "<strong>while</strong>",
        "step;", "<strong>end</strong>", "<strong>end</strong>"])
  let stmt (d : Nat) (txt : String) : Ir.AlgLine :=
    { depth := d, kind := .statement, content := #[.text txt], comment := none }
  let jumpDoc : Ir.Doc :=
    { body := #[.algorithm false true #[stmt 0 "top", stmt 2 "deep"]] }
  let jump := (HtmlDoc.emit {} jumpDoc).1
  t "algorithm html: a skipped level still ships both lines"
    (((jump.splitOn "<li>").length - 1) == 3 && inOrder jump ["top;", "deep;"])
  t "algorithm html: a skipped level opens a list per level"
    (((jump.splitOn "<ol").length - 1) == 3)
  let some bytes ← findFont | failures ref "algorithm comments: missing fixture font"
  let .ok font := Font.parse bytes |
    failures ref "algorithm comments: invalid fixture font"
  let fonts := oneFaceOf font
  for command in ["tcp", "tcc"] do
    for suffix in ["", "*", "*[r]", "*[l]", "*[f]", "*[h]"] do
      for beforeText in ["", "Beforecomment"] do
        let (doc, ds) := elabStr (dvDoc "\\usepackage{algorithm2e}\n"
          ("\\begin{algorithm}\n" ++ beforeText ++ "\\" ++ command ++ suffix ++
            "{Remarkword}\\;\nAftercomment\\;\n\\end{algorithm}"))
        let (_, nodes, _) := HtmlDoc.emitTree {} doc
        let shown := censusText (censusOf #[] (layoutOf fonts doc))
        let label := s!"algorithm {command}{suffix}/{beforeText}"
        t (label ++ ": comment arguments are consumed without errors")
          (ds.all (·.severity != .error))
        t (label ++ ": PDF ships the comment once and keeps its following line")
          ((shown.splitOn "Remarkword").length == 2 && hasStr shown "Aftercomment")
        t (label ++ ": HTML ships the comment once and keeps its following line")
          (treeShownOccurs nodes "Remarkword" == 1 &&
           treeShownOccurs nodes "Aftercomment" == 1)

mutual

/-- Every `code` element's `class` attribute in the typed tree, in document order, `none` where it
carries none. -/
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

/-- One declared language reaches the HTML `code` element's `language-…` class and the markdown
fence's info string; none, or a malformed one (W0110), reaches neither. -/
def listingLanguageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let docOf (body : String) : Ir.Doc × Array Diag := elabStr (dvDoc "" body)
  let classesOf (doc : Ir.Doc) : Array (Option String) :=
    let (head, body, _) := HtmlDoc.emitTree {} doc
    codeClassesList (codeClassesList #[] head.toList) body.toList
  let fencesOf (doc : Ir.Doc) : List String :=
    ((MarkdownDoc.emit doc).splitOn "```").zipIdx.filterMap fun (seg, i) =>
      -- Opening fences stand at odd positions between the delimiters.
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
  let (dialect, ds) := docOf "\\begin{lstlisting}[language={[LaTeX]TeX}]\nx\n\\end{lstlisting}"
  t "an invalid language spelling is named W0110"
    (ds.any (·.code == "W0110"))
  t "html: an invalid language spelling reaches no class"
    (classesOf dialect == #[none])
  t "markdown: an invalid language spelling reaches no fence info"
    (fencesOf dialect == [""])
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
  t "html: the printed class is the token, escaped by construction"
    ((fullHtml.splitOn "<code class=\"language-c++\">").length == 2)

/-- One cell of an emitted table: its row group (`thead`, `tbody` or `""`), tag, `scope`, `class`
and text. -/
structure CellFact where
  group : String
  tag : String
  scope : String
  cls : String
  text : String
  colspan : String
  deriving BEq, Repr

mutual

/-- Every `th`/`td` of a typed tree in document order, each with the row group above it. -/
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
        text := nodeTextOne "" (.elem tag attrs kids)
        colspan := attr "colspan" }
    else
      let group := if tag == "thead" || tag == "tbody" then tag else group
      cellFactsList group acc kids.toList

def cellFactsList (group : String) (acc : Array CellFact) : List Html.Node → Array CellFact
  | [] => acc
  | k :: rest => cellFactsList group (cellFactsOne group acc k) rest

end

mutual

/-- Every `tr`'s `class` value in document order (`""` when unclassed). -/
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

/-- The tags of each table's direct children (`colgroup`, `thead`, `tbody`). -/
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

/-- booktabs' head rows ship as `<thead>`/`<th scope=col>` and the rest as `<tbody>`/`<td>`, with
cell text, order and rule classes unchanged. -/
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
    (Ir.tableHeaderRows (#[] : Array (Array (Array Ir.Block))) #[(0, .mid), (1, .mid)] == 0)
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
  t "the rule classes stand on the same rows after regrouping"
    (rowClassesOne #[] one == #["bt-heavy-above bt-pre", "bt-light-above", "bt-heavy-below"])
  t "the table ships colgroup, thead, tbody in that order"
    (tableGroupsOne #[] one == #[#["colgroup", "thead", "tbody"]])
  let two := tree ("\\begin{tabular}{ll}\\toprule A & B \\\\ C & D \\\\ " ++
    "\\midrule e & f \\\\ \\bottomrule\\end{tabular}")
  let twoCells := cellFactsOne "" #[] two
  t "two header rows: four th, two td"
    ((twoCells.filter (·.tag == "th")).size == 4 &&
      (twoCells.filter (·.tag == "td")).size == 2 &&
      (twoCells.filter (·.group == "thead")).size == 4)
  let cmid := tree ("\\begin{tabular}{lcr}\\toprule left & centre & right \\\\ " ++
    "\\cmidrule(lr){1-2} a & b & c \\\\ \\addlinespace d & e & f \\\\ " ++
    "\\bottomrule\\end{tabular}")
  let cmidCells := cellFactsOne "" #[] cmid
  t "cmidrule and addlinespace head nothing: nine td, no th, no thead"
    (cmidCells.size == 9 && cmidCells.all (fun c => c.tag == "td" && c.group == "tbody"))
  t "the cmid cells carry bt-cmid and every natural cell carries bt-nowrap"
    (cmidCells.map (·.cls) ==
      #["bt-left bt-nowrap", "bt-center bt-nowrap", "bt-right bt-nowrap",
        "bt-left bt-cmid bt-nowrap", "bt-center bt-cmid bt-nowrap",
        "bt-right bt-nowrap", "bt-left bt-nowrap", "bt-center bt-nowrap", "bt-right bt-nowrap"])
  t "no header: colgroup and tbody only"
    (tableGroupsOne #[] cmid == #[#["colgroup", "tbody"]])
  let bare := tree "\\begin{tabular}{ll}a & b \\\\ c & d\\end{tabular}"
  t "a rule-less table has no th"
    ((cellFactsOne "" #[] bare).all fun c => c.tag == "td" && c.group == "tbody")
  let allHead := tree "\\begin{tabular}{ll}\\toprule a & b \\\\ \\midrule\\end{tabular}"
  t "a midrule after the last row heads every row: thead and no tbody"
    (tableGroupsOne #[] allHead == #[#["colgroup", "thead"]] &&
      (cellFactsOne "" #[] allHead).all (·.tag == "th"))
  let spanned := tree ("\\begin{tabular}{lrr}\\toprule & \\multicolumn{2}{c}{Head} \\\\ " ++
    "\\midrule a & 1 & 2 \\\\ \\bottomrule\\end{tabular}")
  let spannedCells := cellFactsOne "" #[] spanned
  t "a spanning head is one th with colspan, its covered cell ships no element"
    (spannedCells.map (fun c => (c.group, c.tag, c.text, c.colspan)) ==
      #[("thead", "th", "", ""), ("thead", "th", "Head", "2"),
        ("tbody", "td", "a", ""), ("tbody", "td", "1", ""), ("tbody", "td", "2", "")])
  t "a spanning head takes its own alignment, not its column's"
    (match spanned with
     | .elem _ _ kids => (kids.toList.findSome? fun k => match k with
         | .elem "thead" _ rs => rs.toList.findSome? fun r => match r with
             | .elem "tr" _ cs => cs[1]?.bind fun c => match c with
                 | .elem _ attrs _ => attrs.find? (·.1 == "class")
                 | _ => none
             | _ => none
         | _ => none) == some ("class", "bt-center bt-nowrap")
     | _ => false)
  let empty := HtmlDoc.blockNode {} (.table #[default, default] true true #[] #[(0, .mid)] #[])
  t "an empty table ships its colgroup and no row group"
    (tableGroupsOne #[] empty == #[#["colgroup"]])
  let src ← IO.FS.readFile "testdata/corpus/tables.tex"
  let (fixture, _) ← elabFixture "tables" src
  let (_, body, _) := HtmlDoc.emitTree {} fixture
  let cells := cellFactsList "" #[] body.toList
  -- A span-covered cell has no element of its own.
  let declared := Ir.foldBlocks (fun n b => match b with
    | .table _ _ _ rows _ spans => n + rows.foldl (fun m r => m + r.size) 0
        - spans.foldl (fun m s => m + (s.n - 1)) 0
    | _ => n) (fun n _ => n) 0 fixture.body
  t "tables fixture: every declared cell ships once"
    (cells.size == declared && declared == 20)
  t "tables fixture: three th, all under thead with scope=col"
    ((cells.filter (·.tag == "th")).size == 3 &&
      (cells.filter (·.tag == "th")).all (fun c => c.group == "thead" && c.scope == "col") &&
      (cells.filter (·.tag == "td")).all (·.group == "tbody"))
  let css := HtmlDoc.baseCss {} fixture
  t "the table stylesheet addresses th beside td"
    (hasStr css "table.booktabs th" && hasStr css "tr.bt-heavy-above > th" &&
      hasStr css "tr.bt-light-above > th" && hasStr css "th.bt-cmid" &&
      hasStr css "font-weight: inherit")

/-- A five-object PDF whose one font is the standard `Helvetica`, no program embedded. -/
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

/-- A cross-reference-stream PDF whose catalog, pages and page ride in one uncompressed object
stream, its header permuted in place under `swap`. -/
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

def flipByte (hay : ByteArray) (i : Nat) : ByteArray :=
  match hay[i]? with
  | some v => hay.set! i (v ^^^ 0xFF)
  | none => hay

/-- One golden fixture elaborated, laid out, written and read back once for the corpus judges; `pdf`
carries no structure tree. -/
structure GoldenArt where
  name : String
  doc : Ir.Doc
  geom : Layout.Geom
  store : Image.Store
  out : Layout.Out
  pdf : ByteArray
  /-- `pdfText pdf`, extracted once. -/
  text : ByteArray
  /-- `PdfRead.objects pdf`, parsed once, its error preserved. -/
  objs : Except String (Array PdfRead.Entry)

def goldenArts (oneFace : Font.FontSet) : IO (Array GoldenArt) := do
  let mut arts : Array GoldenArt := Array.emptyWithCapacity goldenNames.length
  for name in goldenNames do
    let (doc, _) ← goldenDoc name
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc (some oneFace)
    let out := layoutOf oneFace doc geom none store
    let pdf := Pdf.write geom oneFace out.pages doc.info store out.outline
    arts := arts.push
      { name := name, doc := doc, geom := geom, store := store, out := out, pdf := pdf,
        text := pdfText pdf, objs := (PdfRead.objects pdf).map (·.val) }
  return arts

/-- What each golden fixture's PDF carries, read back by the census: `(pages, type0Fonts, images,
forms, smasks, linkAnnots, outlineItems, lang, filters)`. -/
def pdfCensusTable :
    List (String × (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Option String × List String)) := [
  ("affine-lengths", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("paragraphs", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("layout", (1, 1, 0, 0, 0, 0, 2, none, ["FlateDecode"])),
  ("declared", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("fonts", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("palette", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("tokens", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("fill", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("links", (1, 1, 0, 0, 0, 3, 1, none, ["FlateDecode"])),
  ("resume", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("talk", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("deck", (7, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("deck1610", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("themed", (8, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("latex-idioms", (1, 1, 0, 0, 0, 0, 0, some "en", ["FlateDecode"])),
  ("wrapper", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("centering", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("columns", (3, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("boxes", (1, 1, 0, 0, 0, 1, 0, none, ["FlateDecode"])),
  ("overlays", (10, 1, 0, 0, 0, 9, 0, none, ["FlateDecode"])),
  ("overlays-blocks", (12, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("overprint", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("notes", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("furniture", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("chrome", (5, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("footer-left", (4, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("footer-mixed", (5, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("footer-collide", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lists", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lists-styled", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lists-deck", (4, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("headroom", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("marker-styled", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("marker-content", (1, 1, 1, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("trio-page", (1, 1, 0, 0, 0, 0, 2, none, ["FlateDecode"])),
  ("trio-deck", (3, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("trio-card", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("valign", (6, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("images", (1, 1, 4, 0, 1, 0, 1, none, ["DCTDecode", "FlateDecode"])),
  ("figures", (1, 3, 0, 2, 0, 0, 1, none, ["FlateDecode"])),
  ("svg-figures", (2, 1, 1, 9, 0, 0, 1, none, ["FlateDecode"])),
  ("math", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("math-alpha", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("webpage", (1, 1, 0, 0, 0, 6, 0, none, ["FlateDecode"])),
  ("quotes", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("quote-deck", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("outline", (1, 1, 0, 0, 0, 0, 4, none, ["FlateDecode"])),
  ("outline-gap", (1, 1, 0, 0, 0, 0, 2, none, ["FlateDecode"])),
  ("webnav", (1, 1, 0, 0, 0, 0, 3, none, ["FlateDecode"])),
  ("nav-directory", (1, 1, 0, 0, 0, 0, 300, none, ["FlateDecode"])),
  ("bibliography", (1, 1, 0, 0, 0, 9, 0, none, ["FlateDecode"])),
  ("md-cite", (1, 1, 0, 0, 0, 8, 1, none, ["FlateDecode"])),
  ("md-cite-include", (1, 1, 0, 0, 0, 5, 0, none, ["FlateDecode"])),
  ("resume-data", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("icons", (1, 1, 0, 0, 0, 2, 0, none, ["FlateDecode"])),
  ("diagram", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("diagram-boundary", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("diagram-overflow", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("diagram-refused", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("diagram-shapes", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("diagram-tikzset", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("diagram-strokes", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("diagram-tree", (1, 1, 0, 0, 0, 0, 2, none, ["FlateDecode"])),
  ("diagram-scope", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("diagram-cd", (1, 1, 0, 0, 0, 0, 2, none, ["FlateDecode"])),
  ("diagram-longtail", (1, 1, 0, 0, 0, 0, 2, none, ["FlateDecode"])),
  ("tables", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("tables-deck", (3, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("tables-ragged", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("subfigures", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("float-center", (1, 1, 0, 0, 0, 2, 1, none, ["FlateDecode"])),
  ("box-sides", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("math-companion", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("math-first", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("math-text", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("math-cancel", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("greek-literal", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("abstract", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("crossref", (1, 1, 0, 0, 0, 5, 3, none, ["FlateDecode"])),
  ("eqnum", (1, 1, 0, 0, 0, 1, 1, none, ["FlateDecode"])),
  ("footnotes", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("redefine", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("titlebars", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("titleground", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("daylight", (5, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("blocks", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("poster", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("poster-headline", (1, 1, 1, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("listings", (1, 1, 0, 0, 0, 1, 0, none, ["FlateDecode"])),
  ("palette-seeds", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("alert-mark", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("deck-sections", (6, 1, 0, 0, 0, 3, 4, none, ["FlateDecode"])),
  ("deck-hooks", (8, 1, 0, 0, 0, 11, 4, none, ["FlateDecode"])),
  ("contents", (2, 1, 0, 0, 0, 7, 6, none, ["FlateDecode"])),
  ("algorithm", (1, 1, 0, 0, 0, 1, 1, none, ["FlateDecode"])),
  ("lineno", (2, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("lineno-modulo", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("cond-newif", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("cond-ifdefined", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("cond-ifx", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("cond-ifnum", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("cond-loaded", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("md-code", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("code-lean", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("code-lean-prose", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("code-python", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("code-bash", (1, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("lean-cite", (1, 1, 0, 0, 0, 5, 1, none, ["FlateDecode"])),
  ("lean-cite-include", (1, 1, 0, 0, 0, 8, 0, none, ["FlateDecode"])),
  ("md-emphasis", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("md-headings", (1, 1, 0, 0, 0, 0, 4, none, ["FlateDecode"])),
  -- No link annotation: the image a link wraps ships without its link (`silentLosses`).
  ("md-images", (1, 1, 4, 0, 1, 0, 1, none, ["DCTDecode", "FlateDecode"])),
  -- the included markdown's link is the page's one annotation
  ("md-include", (1, 1, 0, 0, 0, 1, 0, none, ["FlateDecode"])),
  ("md-include-deck", (2, 1, 0, 0, 0, 0, 0, none, ["FlateDecode"])),
  ("md-links", (1, 1, 0, 0, 0, 8, 1, none, ["FlateDecode"])),
  ("md-lists", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("md-quotes", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("md-readme", (1, 1, 0, 0, 0, 1, 5, none, ["FlateDecode"])),
  ("md-rules", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"])),
  ("md-table", (1, 1, 0, 0, 0, 0, 1, none, ["FlateDecode"]))]

/-- The read-side census and its checked reader: a probe the writer never made, a copied unembedded
face, six mutants refused by distinct messages, and every golden fixture read back. -/
def pdfCensusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let probe := unembeddedProbePdf
  t "probe pdf reads as a form" (PdfRead.readForm probe).isOk
  t "probe census: one unembedded font"
    (match pdfCensusOf probe with
     | .ok c => c.fonts == 1 && c.type0Fonts == 0 && !c.fontsEmbedded && c.pages == 1
     | .error _ => false)
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
    -- The length keeps its digit count, so every offset after it stands.
    let some lenE := es.find? fun e =>
        e.stream.isSome && (match e.val.get? "Length" with
          | some (.int n) => n ≥ 11 && n % 10 != 0
          | _ => false) | return #[]
    let some (.int len) := lenE.val.get? "Length" | return #[]
    let some lenAt := findBytes pdf s!"/Length {len} >>" | return #[]
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
  for n in goldenNames do
    t s!"pdf census covers {n}" (pdfCensusTable.any (·.1 == n))
  for (n, _) in pdfCensusTable do
    t s!"pdf census row {n} names a golden fixture" (goldenNames.contains n)
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc (some oneFace)
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
  -- The tree's own binary, with the fixture's face from the corpus, so no host font enters.
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    IO.FS.withTempDir fun dir => do
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

def contentOpsRed : Ir.Color := { r := 200, g := 30, b := 30 }
def contentOpsGrey : Ir.Color := { r := 240, g := 240, b := 240 }
def contentOpsCyan : Ir.Color := Ir.Color.ofCmyk 1000 0 0 0

def contentOpsRun (idx : Nat) (color : Ir.Color) (w : Dim.Length) (glyphs : List (Nat × Char))
    (size : Dim.Length := 0) (raise : Dim.Length := 0) : Layout.Seg :=
  .run idx color none w (glyphs.toArray.map fun (g, c) => (g, c, w / glyphs.length)) size {} {}
    raise none (.leaf 0)

/-- The widths the synthetic pages' faces declare, in millionths of the em: each glyph's laid
advance at its run's size. -/
def contentOpsWidths (_ : Unit) : Array (Array Int) :=
  let face := (Array.range 70001).map fun g => match g with
    | 36 | 37 | 70000 | 4096 => 1250000
    | 38 => 1666667
    | 39 | 40 => 2222222
    | 1 => 2500000
    | _ => 833333
  #[face, face]

/-- The leaf tags the synthetic pages are marked under: leaf 0 a paragraph,
leaf 1 a heading, leaf 2 a leaf no element holds. -/
def contentOpsTags : Array (Option String) := #[some "P", some "H2", none]

def contentOpsTextPage : Layout.PageOut := {
  lines := #[
    { x := Dim.bp 10, y := Dim.bp 20, size := Dim.bp 12, setWidth := Dim.bp 100, leaf := some 0, segs := #[
        contentOpsRun 0 Ir.Color.black (Dim.bp 30) [(36, 'A'), (37, 'B')],
        .gap (Dim.bp 5) true,
        contentOpsRun 0 Ir.Color.black (Dim.bp 20) [(38, 'C')],
        contentOpsRun 1 contentOpsRed (Dim.bp 20) [(39, 'D')] (Dim.bp 9) (Dim.bp 3),
        contentOpsRun 1 contentOpsRed (Dim.bp 20) [(40, 'E')] (Dim.bp 9) (Dim.bp 3) ] },
    { x := Dim.bp 10, y := Dim.bp 40, size := Dim.bp 12, setWidth := Dim.bp 100, expand := 20,
      leaf := some 1, segs := #[
        contentOpsRun 0 contentOpsCyan (Dim.bp 30) [(70000, 'x'), (4096, 'y')],
        .gap (Dim.bp 5) true,
        contentOpsRun 0 contentOpsCyan (Dim.bp 30) [(1, 'z')] ] },
    { x := Dim.bp 10, y := Dim.bp 60, size := Dim.bp 12, setWidth := Dim.bp 100, leaf := some 2, segs := #[
        contentOpsRun 0 Ir.Color.black (Dim.bp 2) [],
        contentOpsRun 0 Ir.Color.black (Dim.bp 10) [(50, 'a')],
        .gap (Dim.bp 500) true,
        contentOpsRun 0 Ir.Color.black (Dim.bp 10) [(51, 'b')],
        contentOpsRun 0 Ir.Color.black (Dim.bp 10) [(52, 'c')] (Dim.bp 12) (Dim.bp (-3)),
        contentOpsRun 0 Ir.Color.black (Dim.bp 10) [(53, 'd')] (Dim.bp 12) (Dim.bp (-3)) ] },
    { x := Dim.bp 10, y := Dim.bp 80, size := Dim.bp 12, setWidth := Dim.bp 100, segs := #[
        .rule (Dim.bp 40) (Dim.bp 1) (Dim.bp 2) contentOpsRed false,
        .image (some 0) (Dim.bp 20) (Dim.bp 15) true 0 false,
        .image (some 1) (Dim.bp 20) (Dim.bp 15) true 0 false,
        .image none (Dim.bp 10) (Dim.bp 5) true 0 false,
        contentOpsRun 0 Ir.Color.black (Dim.bp 10) [(54, 'e')],
        .rule (Dim.bp 10) (Dim.bp 2) 0 Ir.Color.black false ] } ],
  fills := #[{ x := 0, y := 0, w := Dim.bp 200, h := Dim.bp 100, color := contentOpsGrey },
             { x := Dim.bp 5, y := Dim.bp 5, w := Dim.bp 50, h := Dim.bp 10, color := contentOpsCyan }] }

/-- A synthetic figure of plain draws, its frame y up. -/
def contentOpsFigure {L : Type} (nodes : Array (Gfx.Node L)) : Gfx.Figure L :=
  { box := ((0, 0), (0, 0)), clipToBox := false, nodes := nodes, outlines := #[], symbols := #[]
    rasters := #[], title := none, losses := #[] }

/-- The placement a synthetic page's pictures stand under: picture y up
from the 100pt page's bottom, so picture and PDF coordinates coincide. -/
def contentOpsPlace : Gfx.Iso := { flipY := true, dx := 0, dy := Dim.bp 100 }

/-- Two pictures' ink under leaf 0 and leaf 1, which the writer groups as two figures. -/
def contentOpsPathPage : Layout.PageOut := {
  inks := #[
    { fig := contentOpsFigure #[
        .draw (.ellipse (Dim.bp 50) (Dim.bp 50) (Dim.bp 20) (Dim.bp 20)) none
          (some (Ir.Pic.strokeOf { color := contentOpsRed, dash := .dashed })),
        .draw (.rect (Dim.bp 10) (Dim.bp 70) (Dim.bp 30) (Dim.bp 20))
          (some (Ir.Pic.solidFill contentOpsGrey))
          (some (Ir.Pic.strokeOf { dash := .dotted, width := Dim.bp 1 })),
        .draw (.path (Ir.Pic.edgeSubpaths #[
            .line (Dim.bp 1) (Dim.bp 98) (Dim.bp 3) (Dim.bp 96),
            .line (Dim.bp 3) (Dim.bp 96) (Dim.bp 5) (Dim.bp 94),
            .cubic (Dim.bp 7) (Dim.bp 92) (Dim.bp 9) (Dim.bp 90) (Dim.bp 11) (Dim.bp 88) (Dim.bp 13)
              (Dim.bp 86),
            .cubic (Dim.bp 13) (Dim.bp 86) (Dim.bp 1) (Dim.bp 99) (Dim.bp 2) (Dim.bp 98) (Dim.bp 3)
              (Dim.bp 97)]))
          none (some (Ir.Pic.strokeOf {}))]
      place := contentOpsPlace, leaf := some 0 },
    { fig := contentOpsFigure #[
        .draw (.path #[{ start := (Dim.bp 1, Dim.bp 98)
                         segs := #[.line (Dim.bp 3, Dim.bp 96), .line (Dim.bp 5, Dim.bp 94)]
                         closed := true }])
          (some (Ir.Pic.solidFill contentOpsRed)) none,
        .draw (.rect (Dim.bp 1) (Dim.bp 97) (Dim.bp 2) (Dim.bp 2)) none none]
      place := contentOpsPlace, leaf := some 1 } ] }

/-- The recorded streams of the synthetic text pages, which the typed operators reproduce byte for
byte, gaps placed by the viewer's arithmetic. -/
def contentOpsTextExpected : String :=
  "q 0.941 0.941 0.941 rg 0 0 200 100 re f Q\n" ++
  "q 1 0 0 0 k 5 85 50 10 re f Q\n" ++
  "BT\n1 0 0 1 10 80 Tm\n/F1 12 Tf\n[<00240025>-417<0026>] TJ\n" ++
  "1 0 0 1 65 83 Tm\n/F2 9 Tf\n0.784 0.118 0.118 rg\n[<0027><0028>] TJ\n" ++
  "102.0 Tz\n1 0 0 1 10 60 Tm\n/F1 12 Tf\n1 0 0 0 k\n[<11701000>-359<0001>] TJ\n" ++
  "100.0 Tz\n1 0 0 1 12 40 Tm\n0 0 0 rg\n[<0032>] TJ\n1 0 0 1 522 40 Tm\n[<0033>] TJ\n" ++
  "1 0 0 1 532 37 Tm\n[<0034><0035>] TJ\n1 0 0 1 100 20 Tm\n[<0036>] TJ\nET\n" ++
  "q 20 0 0 15 50 20 cm /Im1 Do Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 70 20 20 15 re S Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 90 20 10 5 re S Q\n" ++
  "q 0.784 0.118 0.118 rg 10 22 40 1 re f Q\n" ++
  "q 0 0 0 rg 110 20 10 2 re f Q"

def contentOpsPathExpected : String :=
  "q 0.784 0.118 0.118 RG 0.399 w [2.989 2.989] 0 d 70 50 m 70 61.046 61.046 70 50 70 c " ++
  "38.954 70 30 61.046 30 50 c 30 38.954 38.954 30 50 30 c 61.046 30 70 38.954 70 50 c h S Q\n" ++
  "q 0.941 0.941 0.941 rg 0 0 0 RG 1 w [1 0.996] 0 d 10 70 30 20 re B Q\n" ++
  "q 0 0 0 RG 0.399 w 1 98 m 3 96 l 5 94 l 7 92 m 9 90 11 88 13 86 c 1 99 2 98 3 97 c S Q\n" ++
  "q 0.784 0.118 0.118 rg 1 98 m 3 96 l 5 94 l h f Q\n" ++
  "q 1 97 2 2 re n Q\n" ++
  "BT\nET"

/-- The same pages under a 3 pt bleed: every coordinate shifts by the
bleed and nothing else changes. -/
def contentOpsBleedExpected : String :=
  "q 0.941 0.941 0.941 rg 3 3 200 100 re f Q\n" ++
  "q 1 0 0 0 k 8 88 50 10 re f Q\n" ++
  "BT\n1 0 0 1 13 83 Tm\n/F1 12 Tf\n[<00240025>-417<0026>] TJ\n" ++
  "1 0 0 1 68 86 Tm\n/F2 9 Tf\n0.784 0.118 0.118 rg\n[<0027><0028>] TJ\n" ++
  "102.0 Tz\n1 0 0 1 13 63 Tm\n/F1 12 Tf\n1 0 0 0 k\n[<11701000>-359<0001>] TJ\n" ++
  "100.0 Tz\n1 0 0 1 15 43 Tm\n0 0 0 rg\n[<0032>] TJ\n1 0 0 1 525 43 Tm\n[<0033>] TJ\n" ++
  "1 0 0 1 535 40 Tm\n[<0034><0035>] TJ\n1 0 0 1 103 23 Tm\n[<0036>] TJ\nET\n" ++
  "q 20 0 0 15 53 23 cm /Im1 Do Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 73 23 20 15 re S Q\n" ++
  "q 0.62 0.62 0.66 RG 0.75 w 93 23 10 5 re S Q\n" ++
  "q 0.784 0.118 0.118 rg 13 25 40 1 re f Q\n" ++
  "q 0 0 0 rg 113 23 10 2 re f Q"

/-- The stream with its marked-content lines removed, as the artifact acceptance strips the file. -/
def stripMarkLines (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").filter fun l =>
    !(l == "EMC" || l.endsWith " BDC" || l.endsWith " BMC"))

/-- The typed content operators render, marked-content lines removed, byte for byte to the recorded
streams. -/
def contentOpsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := { pageW := Dim.bp 200, pageH := Dim.bp 100 }
  let bleed : Layout.Geom := { geom with bleed := Dim.bp 3 }
  let remap : Array Nat := #[0, 1]
  let imgMap : Array (Option Nat) := #[some 0, none]
  let tags := contentOpsTags
  let plain (g : Layout.Geom) (p : Layout.PageOut) : String :=
    Pdf.render (Pdf.contentOpsPlain g remap (contentOpsWidths ()) imgMap tags Pdf.figureNames #[] p)
  let stripped (g : Layout.Geom) (p : Layout.PageOut) : String :=
    stripMarkLines (Pdf.render (Pdf.contentOps g remap (contentOpsWidths ()) imgMap tags Pdf.figureNames #[] p))
  let ink (g : Layout.Geom) (p : Layout.PageOut) : String :=
    Pdf.render (Pdf.inkOps (Pdf.contentOps g remap (contentOpsWidths ()) imgMap tags Pdf.figureNames #[] p))
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
  t "content ops: the glyph census is the page's runs"
    (Pdf.runsOf (Pdf.contentOps geom remap (contentOpsWidths ()) imgMap tags Pdf.figureNames #[]
        contentOpsTextPage)
      == Pdf.paintRuns contentOpsTextPage &&
      Pdf.paintRuns contentOpsTextPage == Pdf.pageRuns contentOpsTextPage)
  t "content ops: a fill and a fill-only rectangle path spell the same"
    (Pdf.render #[.fill contentOpsRed (q 1) (q 2) (q 3) (q 4)]
      == Pdf.render #[.paint (some { paint := .solid contentOpsRed, evenOdd := false }) none none
        #[.rect (q 1) (q 2) (q 3) (q 4)]])
  let some fontData ← findFont | return ()
  let .ok font := Font.parse fontData | return ()
  let twoFace : Font.FontSet := { fonts := #[font, font] }
  let png ← IO.FS.readBinFile "testdata/corpus/rects.png"
  let store : Image.Store := { entries := #[
    { src := "a.png", info := (Image.decode png).toOption }, { src := "b.png" }] }
  let streams := Pdf.pageStreams geom twoFace #[contentOpsTextPage, contentOpsPathPage] store
  let typed (p : Layout.PageOut) : String :=
    stripMarkLines (Pdf.render (Pdf.contentOps geom remap
      (Pdf.widthTable twoFace.fonts #[0, 1]) imgMap (Pdf.tagsOf ⟨#[]⟩) Pdf.figureNames #[] p))
  t "content ops: pageStreams is the typed render under the faces' own widths"
    (streams.map (stripMarkLines <| String.fromUTF8! ·)
      == #[typed contentOpsTextPage, typed contentOpsPathPage])

/-- Declared output facts are held against each artifact's realization record, one W0701 per unmet
fact per artifact, and a byte-reading assertion with no bytes fails loud. -/
def outputContractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let out (decl : String) : Ir.Doc × Array Diag := elabStr (dvDoc s!"\\output\{ {decl} }\n" "x")
  let w0701 (c : Ir.OutputContract) (r : Ir.Realization) : Array Diag :=
    Ir.contractDiags (c.unmet r)
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
  let (d2, ds2) := out "formats = pdf, color = srgb"
  t "contract: 'color = srgb' is a known key" (!ds2.any (·.code == "E0322"))
  t "contract: device colour in the PDF → one W0701 naming color"
    (match w0701 d2.output.contract Pdf.profile with
     | #[w] => w.subject == some "color"
     | _ => false)
  t "contract: CSS colour is sRGB by definition → no W0701"
    ((w0701 d2.output.contract HtmlDoc.profile).isEmpty)
  let (d12, _) := out "formats = pdf, alternatives = required, color = srgb"
  t "contract: two unmet facts are two W0701s"
    ((w0701 d12.output.contract Pdf.profile).size == 2)
  t "contract: an unknown alternatives value is E0321"
    ((out "alternatives = maybe").2.any fun d =>
      d.code == "E0321" && hasStr d.message "maybe")
  t "contract: an unknown colour intent is E0321"
    ((out "color = cmyk").2.any (·.code == "E0321"))
  t "contract: an unknown font policy is E0321"
    ((out "fonts = subset").2.any (·.code == "E0321"))
  let (d0, _) := out "formats = pdf, html"
  t "contract: an undeclared contract is met by both records"
    ((d0.output.contract.unmet Pdf.profile).isEmpty &&
     (d0.output.contract.unmet HtmlDoc.profile).isEmpty)
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
  t "reads: layout assertions read no artifact"
    ((Ir.AssertKind.pages .eq 1).reads.isEmpty && Ir.AssertKind.textInArea.reads.isEmpty &&
     (Ir.AssertKind.minXHeight 0).reads.isEmpty && Ir.AssertKind.accessibilityAA.reads.isEmpty)
  t "reads: fonts.all_embedded reads the two artifacts that carry faces"
    (Ir.AssertKind.fontsAllEmbedded.reads == #["pdf", "html"])
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds for the contract checks:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    IO.FS.withTempDir fun dir => do
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
      let (code, log, _) ← run "alt-pdf" "article"
        "\\output{ formats = pdf, alternatives = required }\n" one
      t s!"driver: pdf + alternatives = required builds with one W0701: {log}"
        (code == 0 && count log "[W0701]" == 1 && hasStr log "alternatives = required")
      let (code, log, _) ← run "alt-html" "article"
        "\\output{ formats = html, alternatives = required }\n" one
      t "driver: html + alternatives = required builds with no W0701"
        (code == 0 && count log "W0701" == 0)
      let (code, log, _) ← run "alt-both" "article"
        "\\output{ formats = pdf, html, alternatives = required }\n" one
      t "driver: pdf+html + alternatives = required warns once, for the PDF"
        (code == 0 && count log "[W0701]" == 1)
      let (code, log, _) ← run "srgb-pdf" "article" "\\output{ formats = pdf, color = srgb }\n" one
      t "driver: pdf + color = srgb builds with one W0701"
        (code == 0 && count log "[W0701]" == 1 && hasStr log "color = srgb")
      let (code, log, _) ← run "srgb-html" "article" "\\output{ formats = html, color = srgb }\n" one
      t "driver: html + color = srgb builds with no W0701" (code == 0 && count log "W0701" == 0)
      let (code, log, outDir) ← run "own" "article"
        "\\output{ formats = html, css = own }\n\\assert{ fonts.all_embedded }\n" one
      t s!"driver: css = own + fonts.all_embedded is E0330: {log}"
        (code != 0 && hasStr log "E0330" && !(← outDir.pathExists))
      let (code, log, outDir) ← run "optin" "article"
        "\\output{ formats = html, css = own, fonts = embedded }\n\\assert{ fonts.all_embedded }\n" one
      t s!"driver: css = own + fonts = embedded passes the assertion: {log}" (code == 0)
      let optinHtml ← IO.FS.readFile (outDir / "optin.html")
      t "driver: fonts = embedded publishes the font bytes inside the single page"
        (hasStr optinHtml "src: url(\"data:font/" &&
         (← outDir.readDir).map (·.fileName) == #["optin.html"])
      let (code, _, outDir) ← run "optout" "article" "\\output{ formats = html, fonts = none }\n" one
      t "driver: fonts = none with no css story ships no faces"
        (code == 0 && !(← (outDir / "optout.fonts").pathExists))
      let (code, log, _) ← run "three" "article" "\\output{ formats = html }\n\\assert{ pages == 3 }\n" three
      t s!"driver: html-only pages == 3 holds on a three-page layout: {log}" (code == 0)
      let (code, log, _) ← run "one" "article" "\\output{ formats = html }\n\\assert{ pages == 3 }\n" one
      t "driver: html-only pages == 3 fails on one page with the layout's actual"
        (code != 0 && hasStr log "E0330" && hasStr log "(actual: 1)")
      let (code, log, _) ← run "resume" "resume" "\\output{ formats = html }\n" one
      t s!"driver: an html-only résumé builds clean under its implied assertions: {log}" (code == 0)
      let (code, log, outDir) ← run "md" "article" "\\output{ formats = md }\n\\assert{ fonts.all_embedded }\n" one
      t s!"driver: md-only fonts.all_embedded fails loud (E0330): {log}"
        (code != 0 && hasStr log "E0330" && hasStr log "no emitted artifact carries this measurement" &&
         !(← outDir.pathExists))

theorem objTable_ids_set_eq (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems nFigDict nFigForm : Nat) :
    (Pdf.objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids.toList.Nodup ∧
    ∀ id, id ∈ (Pdf.objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids ↔
      1 ≤ id ∧ id < (Pdf.objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size :=
  ⟨Pdf.objTable_inj keep imgs usedImgs np nOut nElems nFigDict nFigForm, fun id =>
    ⟨Pdf.objTable_between keep imgs usedImgs np nOut nElems nFigDict nFigForm id,
     fun h => Pdf.objTable_covers keep imgs usedImgs np nOut nElems nFigDict nFigForm id h.1 h.2⟩⟩

/-- Every object id the writer's cross-reference lists is allocated by one table, read back through
the engine's own reader, per corpus fixture. -/
def objTableChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let t0 := Pdf.objTable #[0] {} #[] 1 0 1 0 0
  t "table: the font block is four ids then the file"
    (Pdf.ObjTable.type0Id 0 == 3 && Pdf.ObjTable.cidId 0 == 4 && Pdf.ObjTable.fdId 0 == 5 &&
     Pdf.ObjTable.toUniId 0 == 6 && t0.fileId 0 == 7)
  t "table: one face, one page, no outline, one structure element"
    (t0.pageId 0 == 8 && t0.contentId 0 == 9 && t0.infoId == 10 && t0.structTreeRoot == 11 &&
     t0.parentTree == 12 && t0.namespaceId == 13 && t0.structElemId 0 == 14 && t0.resId == 15 &&
     t0.xmpId == 16 && t0.objStmId 0 == 17 && t0.nStm == 1 && t0.xrefId == 18 && t0.size == 19 &&
     t0.nf == 1 && t0.np == 1)
  t "table: the conditional families allocate nothing yet"
    (t0.outputIntent.isNone && t0.icc.isNone)
  let t1 := Pdf.objTable #[0, 2] {} #[] 3 2 0 0 0
  t "table: two faces, three pages, an outline"
    (t1.fileId 1 == 12 && t1.pageId 2 == 17 && t1.contentId 2 == 18 && t1.infoId == 19 &&
     t1.outlineRootId == 20 && t1.outlineItemId 1 == 22 && t1.structTreeRoot == 23 &&
     t1.structBase == 26 && t1.resId == 26 && t1.xmpId == 27 && t1.xrefId == 29 && t1.size == 30)
  let t2 := Pdf.objTable #[0] {} #[] 1 0 1 2 3
  t "table: two figure dictionaries then three figure forms"
    (t2.resId == 15 && t2.figDictId 0 == 16 && t2.figDictId 1 == 17 && t2.figFormId 0 == 18 &&
     t2.figFormId 2 == 20 && t2.xmpId == 21 && t2.size == 24)
  let png ← IO.FS.readBinFile "testdata/corpus/rects.png"
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
  let ti := Pdf.objTable #[0] store #[0, 1, 2, 3] 2 0 0 0 0
  t "table: an XObject per image, then what it brings"
    (ti.imgIds == #[8, 9, 11, 12 + formN] && ti.smaskIds == #[none, some 10, none, none] &&
     ti.formBases == #[none, none, some 12, none] && ti.formSizes == #[0, 0, formN, 0] &&
     ti.ni == 4)
  t "table: the pages follow the last image block"
    (ti.pageId 0 == 13 + formN && ti.contentId 1 == 16 + formN && ti.infoId == 17 + formN &&
     ti.size == 25 + formN)
  -- 600 outline items make 613 compressed objects: three object streams.
  let tl := Pdf.objTable #[0] {} #[] 1 600 1 0 0
  t "table: one object stream per capacity of compressed objects"
    (Pdf.compressedCount tl.nf tl.np tl.nOut tl.nElems tl.nFigDict == 613 && tl.nStm == 3 &&
     tl.objStmId 0 == tl.xmpId + 1 && tl.objStmId 2 == tl.xmpId + 3 &&
     tl.xrefId == tl.xmpId + 4 && tl.size == tl.xmpId + 5)
  for (name, tb) in [("plain", t0), ("outline", t1), ("figures", t2), ("images", ti),
      ("streams", tl)] do
    t s!"table {name}: the ids are exactly [1, size)"
      (tb.ids.toList == List.range' 1 (tb.size - 1))
  let cidx : Nat → Option Nat := fun id => if id == 1 then some 0 else if id == 2 then some 1 else none
  t "kindOf: xref, in-stream, direct — and none outside the table"
    (ti.kindOf cidx ti.xrefId == some .xref && ti.kindOf cidx 1 == some (.inStream 0) &&
     ti.kindOf cidx 2 == some (.inStream 1) && ti.kindOf cidx 8 == some .direct &&
     ti.kindOf cidx 0 == none && ti.kindOf cidx ti.size == none)
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc (some oneFace)
    let out := layoutOf oneFace doc geom none store
    let tree := Struct.ofDoc (Layout.pdfView doc)
    let tb := Pdf.tableOf geom oneFace out.pages store out.outline tree
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

/-- One page placing the store's first image. -/
def featurePlacingPages : Array Layout.PageOut :=
  #[{ lines := #[
    { x := Dim.pt 10, y := Dim.pt 40, size := Dim.pt 10, setWidth := Dim.pt 100,
      segs := #[.image (some 0) (Dim.pt 20) (Dim.pt 15) true 0 false] }] }]

/-- The typed feature census: the registry is closed and one-to-one, each row is decided by its
shape, and over the corpus the unemitted features stay unreached and the bookkeeping ones are always
reached. -/
def featureCensusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  t "features: the registry counts its constructors"
    (Pdf.Feature.all.length == Pdf.Feature.count && Pdf.Feature.all.Nodup)
  t "features: every row name reads back to its feature"
    (Pdf.Feature.all.all fun f => Pdf.Feature.ofName? f.name == some f)
  t "features: row names are distinct" ((Pdf.Feature.all.map Pdf.Feature.name).Nodup)
  t "features: an unknown row name is nobody's" (Pdf.Feature.ofName? "hologram").isNone
  let requestsAgree (f : Ir.Features) : Bool :=
    (!(HtmlDoc.kernCssFor f).isEmpty) == Layout.kernEnabled f
  let kernOn : Ir.Features := { kern := true }
  let kernOff : Ir.Features := { kern := false }
  t "features: both backend projections agree in both feature states"
    (requestsAgree kernOn && requestsAgree kernOff)
  t "features: crossing either projection falsifies the agreement check"
    ((!(HtmlDoc.kernCssFor kernOn).isEmpty) != Layout.kernEnabled kernOff &&
      (!(HtmlDoc.kernCssFor kernOff).isEmpty) != Layout.kernEnabled kernOn)
  let png ← IO.FS.readBinFile "testdata/corpus/rects.png"
  let jpg ← IO.FS.readBinFile "testdata/corpus/rects.jpg"
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
  let outlineOf (n : Nat) : Array Layout.OutlineEntry := Array.replicate n { title := "a" }
  let planAt (n : Nat) := Pdf.prepare geom oneFace #[] {} {} (outlineOf n)
  let multiAt (n : Nat) : Bool :=
    (Pdf.features geom oneFace #[] {} (outlineOf n)).contains .objStmMulti
  let full := Pdf.objStmCapacity + 1 - (planAt 1).compressed.length
  t s!"features: {full} entries fill one object stream exactly, one more opens a second"
    ((planAt full).compressed.length == Pdf.objStmCapacity && (planAt full).chunks.length == 1 &&
      (planAt (full + 1)).chunks.length == 2)
  t "features: objstm-multi exactly when a second object stream opens"
    (!bare.contains .objStmMulti && !multiAt full && multiAt (full + 1))
  let translucent : List String := ["svg-figures"]
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc (some oneFace)
    let out := layoutOf oneFace doc geom none store
    let fs := Pdf.features geom oneFace out.pages store out.outline
    t s!"features {n}: never tabs, Brotli or JPX"
      (!fs.contains .tabs && !fs.contains .brotli && !fs.contains .jpx)
    t s!"features {n}: a transparency group exactly where a figure has a translucent group"
      (fs.contains .transparencyGroup == translucent.contains n)
    t s!"features {n}: always the cross-reference stream, the object stream, XMP, the structure tree, one CIDFontType2"
      (fs.contains .xrefStream && fs.contains .objStm && fs.contains .xmp &&
       fs.contains .structTree && fs.contains .cidFontType2 && !fs.contains .cidFontType0)
    t s!"features {n}: in registry order, once each"
      (fs.toList == Pdf.Feature.all.filter fs.contains)

/-- The recorded text page under the marking layer. -/
def artifactTextExpected : String :=
  "/Artifact BMC\nq 0.941 0.941 0.941 rg 0 0 200 100 re f Q\n" ++
  "q 1 0 0 0 k 5 85 50 10 re f Q\nEMC\n" ++
  "BT\n/P << /MCID 0 >> BDC\n1 0 0 1 10 80 Tm\n/F1 12 Tf\n[<00240025>-417<0026>] TJ\n" ++
  "1 0 0 1 65 83 Tm\n/F2 9 Tf\n0.784 0.118 0.118 rg\n[<0027><0028>] TJ\nEMC\n" ++
  "/H2 << /MCID 1 >> BDC\n102.0 Tz\n1 0 0 1 10 60 Tm\n/F1 12 Tf\n1 0 0 0 k\n" ++
  "[<11701000>-359<0001>] TJ\nEMC\n" ++
  "/Artifact BMC\n100.0 Tz\n1 0 0 1 12 40 Tm\n0 0 0 rg\n[<0032>] TJ\n1 0 0 1 522 40 Tm\n" ++
  "[<0033>] TJ\n1 0 0 1 532 37 Tm\n[<0034><0035>] TJ\nEMC\n" ++
  "/Artifact BMC\n1 0 0 1 100 20 Tm\n[<0036>] TJ\nEMC\nET\n" ++
  "/Artifact BMC\nq 20 0 0 15 50 20 cm /Im1 Do Q\nEMC\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0.62 0.62 0.66 RG 0.75 w 70 20 20 15 re S Q\nEMC\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0.62 0.62 0.66 RG 0.75 w 90 20 10 5 re S Q\nEMC\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0.784 0.118 0.118 rg 10 22 40 1 re f Q\n" ++
  "q 0 0 0 rg 110 20 10 2 re f Q\nEMC"

/-- The path page: two pictures, each its paths under one `/P` sequence, the text object empty. -/
def artifactPathExpected : String :=
  "/P << /MCID 0 >> BDC\n" ++
  "q 0.784 0.118 0.118 RG 0.399 w [2.989 2.989] 0 d 70 50 m 70 61.046 61.046 70 50 70 c " ++
  "38.954 70 30 61.046 30 50 c 30 38.954 38.954 30 50 30 c 61.046 30 70 38.954 70 50 c h S Q\n" ++
  "q 0.941 0.941 0.941 rg 0 0 0 RG 1 w [1 0.996] 0 d 10 70 30 20 re B Q\n" ++
  "q 0 0 0 RG 0.399 w 1 98 m 3 96 l 5 94 l 7 92 m 9 90 11 88 13 86 c 1 99 2 98 3 97 c S Q\nEMC\n" ++
  "/H2 << /MCID 1 >> BDC\n" ++
  "q 0.784 0.118 0.118 rg 1 98 m 3 96 l 5 94 l h f Q\n" ++
  "q 1 97 2 2 re n Q\nEMC\n" ++
  "BT\nET"

/-- Two furniture lines around a flow line, the second carrying a rule. -/
def artifactFurniturePage : Layout.PageOut := {
  lines := #[
    { x := Dim.bp 10, y := Dim.bp 20, size := Dim.bp 12, setWidth := Dim.bp 100, furniture := true,
      segs := #[contentOpsRun 0 Ir.Color.black (Dim.bp 30) [(36, 'A')]] },
    { x := Dim.bp 10, y := Dim.bp 40, size := Dim.bp 12, setWidth := Dim.bp 100,
      segs := #[contentOpsRun 0 Ir.Color.black (Dim.bp 30) [(37, 'B')]] },
    { x := Dim.bp 10, y := Dim.bp 60, size := Dim.bp 12, setWidth := Dim.bp 100, furniture := true,
      segs := #[contentOpsRun 0 Ir.Color.black (Dim.bp 30) [(38, 'C')],
                .rule (Dim.bp 10) (Dim.bp 1) 0 Ir.Color.black false] } ] }

def artifactFurnitureExpected : String :=
  "BT\n/Artifact << /Type /Pagination >> BDC\n1 0 0 1 10 80 Tm\n/F1 12 Tf\n[<0024>] TJ\nEMC\n" ++
  "/Artifact BMC\n1 0 0 1 10 60 Tm\n[<0025>] TJ\nEMC\n" ++
  "/Artifact << /Type /Pagination >> BDC\n1 0 0 1 10 40 Tm\n[<0026>] TJ\nEMC\nET\n" ++
  "/Artifact << /Type /Layout >> BDC\nq 0 0 0 rg 40 40 10 1 re f Q\nEMC"

/-- A line whose operators paint: one holding a run with glyphs. -/
def lineInks (l : Layout.LineOut) : Bool :=
  l.segs.any fun s => match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
    | .image _ _ _ _ _ _ | .rule _ _ _ _ _ | .decoration _ _ _ _ _ _
    | .gap _ _ | .decoratedGap _ _ _ | .poly _ _ => false

/-- The artifact count a page owes, read from `Layout.PageOut` and the leaf tags rather than the
stream. -/
def expectedArtifacts (page : Layout.PageOut) (tags : Array (Option String)) : Nat :=
  let rules := page.lines.foldl (init := 0) fun acc l =>
    acc + l.segs.foldl (init := 0) fun acc s =>
      match s with
      -- the layout block over the text holds the rules and the polygons alike
      | .rule _ _ _ _ _ | .poly _ _ => acc + 1
      | .decoration kind _ _ _ _ _ => if kind.isMark then acc else acc + 1
      | .image _ _ _ _ _ _ | .run _ _ _ _ _ _ _ _ _ _ _ | .gap _ _ | .decoratedGap _ _ _ => acc
  -- the marks a line paints under its text stand in a layout block of their own
  let marks := page.lines.foldl (init := 0) fun acc l =>
    acc + l.segs.foldl (init := 0) fun acc s =>
      match s with
      | .decoration kind _ _ _ _ _ => if kind.isMark then acc + 1 else acc
      | .rule _ _ _ _ _ | .poly _ _ | .image _ _ _ _ _ _ | .run _ _ _ _ _ _ _ _ _ _ _ | .gap _ _
      | .decoratedGap _ _ _ => acc
  let images := page.lines.foldl (init := 0) fun acc l =>
    acc + l.segs.foldl (init := 0) fun acc s =>
      match s with
      | .image _ _ _ _ _ _ => acc + 1
      | .rule _ _ _ _ _ | .decoration _ _ _ _ _ _ | .run _ _ _ _ _ _ _ _ _ _ _
      | .gap _ _ | .decoratedGap _ _ _ | .poly _ _ => acc
  let (unattributed, _) := page.lines.foldl (init := ((0 : Nat), (0 : Int))) fun (acc, tz) l =>
    let nonEmpty := lineInks l || l.expand != tz
    (if Pdf.Origin.of tags l == .unattributed && nonEmpty then acc + 1 else acc, l.expand)
  (if page.fills.isEmpty then 0 else 1) + (if marks == 0 then 0 else 1) + (if rules == 0 then 0 else 1)
    + images
    + (page.lines.filter (·.furniture)).size + unattributed

/-- The runs under a text object's pagination wrappers. -/
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

def isArtifactOpen (l : Pdf.Line) : Bool :=
  match l with
  | .open (.artifact _) => true
  | .open (.content _ _ _) => false
  | .op _ | .emc => false

/-- Every painting operator sits inside a wrapper with its ink unmoved, on synthetic pages and every
corpus fixture. -/
def artifactMarkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := { pageW := Dim.bp 200, pageH := Dim.bp 100 }
  let remap : Array Nat := #[0, 1]
  let imgMap : Array (Option Nat) := #[some 0, none]
  let tags := contentOpsTags
  let ops (p : Layout.PageOut) :=
    Pdf.contentOps geom remap (contentOpsWidths ()) imgMap tags Pdf.figureNames #[] p
  t "artifacts: the fill block, the rule block and each placeholder wrap as recorded; leaves under their types"
    (Pdf.render (ops contentOpsTextPage) == artifactTextExpected)
  t "artifacts: furniture lines are pagination groups inside the text object, a leafless line a bare one"
    (Pdf.render (ops artifactFurniturePage) == artifactFurnitureExpected)
  t "artifacts: the furniture page strips to its plain twin"
    (stripMarkLines artifactFurnitureExpected
      == Pdf.render (Pdf.contentOpsPlain geom remap (contentOpsWidths ()) imgMap tags Pdf.figureNames #[]
        artifactFurniturePage))
  t "artifacts: picture paths are grouped per picture under the holder's type"
    (Pdf.render (ops contentOpsPathPage) == artifactPathExpected)
  t "artifacts: the marks of the text page are its two leaves, numbered in stream order"
    (Pdf.pageMarks (ops contentOpsTextPage) == #[(0, 0), (1, 1)]
      && Pdf.pageMarks (ops contentOpsPathPage) == #[(0, 0), (1, 1)])
  let nest : Array Pdf.ContentOp :=
    #[.marked (.artifact none) #[.marked (.artifact (some .page)) #[.fill contentOpsRed (q 1) (q 2) (q 3) (q 4)],
        .imageMissing (q 5) (q 6) (q 7) (q 8)], .fill contentOpsRed (q 9) (q 9) (q 9) (q 9)]
  let nestLines := (Pdf.render nest).splitOn "\n"
  t "artifacts: a nested wrapper renders two opening lines and two EMC lines, ink between"
    ((nestLines.filter fun l => l.endsWith " BDC" || l.endsWith " BMC").length == 2
      && (nestLines.filter (· == "EMC")).length == 2
      && stripMarkLines (Pdf.render nest)
          == Pdf.render #[.fill contentOpsRed (q 1) (q 2) (q 3) (q 4), .imageMissing (q 5) (q 6) (q 7) (q 8), .fill contentOpsRed (q 9) (q 9) (q 9) (q 9)]
      && Pdf.render (Pdf.inkOps nest) == stripMarkLines (Pdf.render nest))
  t "artifacts: an empty wrapper is one opening line and one EMC line"
    (Pdf.render #[.marked (.artifact none) #[]] == "/Artifact BMC\nEMC")
  let nested : Array Pdf.ContentOp :=
    #[.marked (.content "P" 9 0) #[.fill contentOpsRed (q 1) (q 2) (q 3) (q 4),
        .marked (.content "Span" 9 1) #[.fill contentOpsRed (q 5) (q 6) (q 7) (q 8)]],
      .text #[.marked (.artifact none) #[.scale 0], .marked (.content "H1" 9 2) #[.scale 1]],
      .marked (.artifact (some .layout)) #[.marked (.content "Figure" 9 3) #[.imageMissing (q 1) (q 1) (q 1) (q 1)]]]
  t "artifacts: numbering hands out 0 … n−1 in stream order through every body, leaves kept"
    (Pdf.pageMarks (Pdf.numberMarks nested) == #[(0, 0), (1, 1), (2, 2), (3, 3)]
      && Pdf.inkOps (Pdf.numberMarks nested) == Pdf.inkOps nested)
  -- A bare tag before `BDC` is a syntax error on which poppler drops the rest of the page.
  t "artifacts: every opener is a legal operator — BMC alone, BDC with its dictionary"
    (Pdf.MarkTag.opener (.artifact none) == "/Artifact BMC"
      && [Pdf.ArtifactKind.pagination, .layout, .page].all (fun k =>
        let o := Pdf.MarkTag.opener (.artifact (some k))
        o.startsWith "/Artifact << /Type /" && o.endsWith " >> BDC")
      && Pdf.MarkTag.opener (.content "P" 7 3) == "/P << /MCID 7 >> BDC")
  let mut pages := 0
  let mut wrappers := 0
  let mut marks := 0
  let mut furniture := 0
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
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
            | .fill _ _ _ _ _ | .paint _ _ _ _ | .group _ _ _ _ | .shade _ _ | .outline _ _ _
            | .xobject _ _ _ _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .marked _ _ => [])
              == furnitureRuns page)
      t s!"artifacts {n} p{i}: every top-level operation is wrapped, or is the text object with every operator wrapped"
        (ops.all Pdf.ContentOp.wrapped)
  t s!"artifacts: the corpus exercised the layer ({pages} pages, {wrappers} wrappers, \
{marks} marks, {furniture} furniture lines)"
    (pages > 0 && wrappers > 0 && marks > 0 && furniture > 0)

/-- A declared conformance name implies exactly one assertion judged on the built bytes' census, the
meet of two contracts fails no file both pass, and no claim is written. -/
def pdfContractChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (arts : Array GoldenArt) : IO Unit := do
  let t := check ref
  let out (decl : String) : Ir.Doc × Array Diag := elabStr (dvDoc s!"\\output\{ {decl} }\n" "x")
  let profileAsserts (d : Ir.Doc) : Array String := d.asserts.filterMap fun a =>
    match a.kind with
    | .pdfProfile n => some n
    | .pages _ _ | .fontsAllEmbedded | .textInArea | .minXHeight _ | .accessibilityAA => none
  let (d1, ds1) := out "formats = pdf, profiles = pdf/a-4"
  t "profiles: 'profiles = pdf/a-4' is a known key" (!ds1.any fun d => d.code == "E0322" || d.code == "E0321")
  t "profiles: the name lands in the set" (d1.output.profiles == #["pdf/a-4"])
  t "profiles: one declared profile implies one pdf.profile assertion"
    (profileAsserts d1 == #["pdf/a-4"])
  t "profiles: the implied assertion reads the PDF alone"
    ((Ir.AssertKind.pdfProfile "pdf/a-4").reads == #["pdf"] &&
     (Ir.AssertKind.pdfProfile "pdf/a-4").source == "pdf.profile = pdf/a-4")
  t "profiles: pdf/a-4 implies color = srgb" (d1.output.contract.color == .srgb)
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
  let mut n := 0
  for a in arts do
    let name := a.name
    let doc := a.doc
    let pdf := a.pdf
    t s!"contract {name}: no fixture declares a profile" doc.output.profiles.isEmpty
    t s!"contract {name}: no identification is written" (!bytesContain a.text "pdfaid" &&
      !bytesContain a.text "pdfuaid" && !bytesContain a.text "pdfxid")
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
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds for the profile checks:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    IO.FS.withTempDir fun dir => do
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
      t s!"driver: pdf/z is E0321 naming the registered profiles, its PDF shipped unclaimed: {log}"
        (code == 1 && hasStr log "E0321" && hasStr log "pdf/a-4, pdf/ua-2, pdf/x-6" &&
         (← (outDir / "z.pdf").pathExists))
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

/-- The `/MCID n` identifiers a decoded content stream opens, in stream order. -/
def streamMcids (data : ByteArray) : List Nat :=
  ((String.fromUTF8! data).splitOn "\n").filterMap fun l =>
    if l.endsWith " BDC" then
      match (l.splitOn "/MCID ").drop 1 with
      | rest :: _ => (rest.splitOn " ").head?.bind (·.toNat?)
      | [] => none
    else none

/-- Every PDF is tagged: `/MarkInfo` and a `/StructTreeRoot`, a tree listing each marked-content
identifier once with a parent tree mapping it back, and heading elements equal to
`Ir.headingLevels`. -/
def structTreeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (arts : Array GoldenArt) : IO Unit := do
  let t := check ref
  let tree : Struct.Tree := { children := #[
    .node (.heading 0) #[.leaf 0 (.text "Title")],
    .node .paragraph #[.leaf 1 (.text "Read "), .node (.link "https://example.org") #[.leaf 2 (.text "this")],
      .leaf 3 (.image "a.png" (.described "An image")), .node .formula #[.leaf 4 (.text "x")]],
    .node (.list false) #[.node .item #[.node .label #[], .node .body #[.node .paragraph #[.leaf 5 (.text "item")]]]],
    .node .aside #[.node .paragraph #[.leaf 6 (.text "speaker")]],
    .node .bibEntry #[.leaf 7 (.text "[1] A")], .node .bibEntry #[.leaf 8 (.text "[2] B")],
    .node .figure #[.node .caption #[.leaf 9 (.text "Cap")], .node .paragraph #[.leaf 10 (.image "b.png" .undeclared)]],
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
  let marks : Array (Array (Nat × Nat)) := #[#[(0, 1), (1, 1)], #[(0, 5)]]
  let filled := Pdf.fill sk (Pdf.leafPagesOf 12 marks)
  t "struct: fill puts each mark in the element holding its leaf, in page order"
    (filled[2]!.kids == #[.mcid 0 0, .mcid 0 1, .elem 3, .elem 4, .elem 5] &&
     filled[9]!.kids == #[.mcid 1 0])
  t "struct: the parent tree maps every mark back to the element that lists it"
    (Pdf.parentTreeOf marks (Pdf.leafOwners sk 12) == #[#[some 2, some 2], #[some 9]])
  let (doc, _) := elabStr (dvDoc "" "\\section{Head}\n\nText\\footnote{note body} more.\n\n\\begin{itemize}\\item one\\end{itemize}")
  let esk := Pdf.skeleton (Struct.ofDoc (Layout.pdfView doc))
  t "struct: an elaborated section, footnote and list project to H2, P with FENote, L/LI/LBody/P"
    (esk.map (·.s) == #["Document", "H2", "P", "FENote", "L", "LI", "LBody", "P"])
  let (altDoc, _) := elabStr (dvDoc "\\pictures{ tool = none }\n" (
    "\\begin{tikzpicture}[alt={Two squares joined by a bar}]" ++
      "\\fill (0,0) rectangle (1,1);\\end{tikzpicture}\n\n" ++
    "\\begin{tikzpicture}[artifact]\\fill (0,0) rectangle (4,0.1);\\end{tikzpicture}\n\n" ++
    "\\begin{tikzpicture}\\node at (0,0) {North};\\node at (2,0) {South};" ++
      "\\end{tikzpicture}\n\n" ++
    "\\begin{tikzpicture}\\fill (0,0) rectangle (1,1);\\end{tikzpicture}\n\n" ++
    "\\includegraphics[artifact]{rects.png}"))
  let altOut := layoutOf oneFace altDoc
  let altPdf := Pdf.write (Layout.Geom.ofPage altDoc.page) oneFace altOut.pages altDoc.info {}
    altOut.outline (tree := Struct.ofDoc (Layout.pdfView altDoc))
  match PdfRead.objects altPdf with
  | .error e => t s!"struct alt: objects: {e}" false
  | .ok es =>
    let es := es.val
    let trailer := (PdfRead.trailer altPdf).toOption.getD (.dict #[])
    let root := PdfCensus.deref es
      (((PdfCensus.catalogOf es trailer).get? "StructTreeRoot").getD .null)
    t "struct alt: the written Figures carry the /Alt the IR resolves; decoration is no element"
      (((readStructTree es root).filter (·.s == "Figure")).map (·.alt) ==
        #[some "(Two squares joined by a bar)", some "(North, South)", none])
  let mut elems := 0
  let mut mcids := 0
  for a in arts do
    let n := a.name
    let doc := a.doc
    let geom := a.geom
    let store := a.store
    let out := a.out
    let tree := Struct.ofDoc (Layout.pdfView doc)
    let pdf := Pdf.write geom oneFace out.pages doc.info store out.outline (tree := tree)
    let text := pdfText pdf
    t s!"struct {n}: the catalog declares marked content and a structure tree root"
      (bytesContain text "/MarkInfo << /Marked true >>" && bytesContain text "/StructTreeRoot"
        && bytesContain text "/S /Document")
    let sk := Pdf.skeleton tree
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
      let hs := tree.filterMap fun e =>
        if e.s.startsWith "H" && e.s.length > 1 then (e.s.drop 1).toString.toNat? else none
      t s!"struct {n}: the heading elements project Ir.headingLevels exactly"
        (hs == (Ir.headingLevels (Layout.pdfView doc).body).map Ir.headingRank)
      t s!"struct {n}: every element with a 2.0 type names the namespace"
        (tree.all fun e => e.ns.isSome || e.s == "Code" || e.s == "BlockQuote" || e.s == "Reference")
  t s!"struct: the corpus exercised the tree ({elems} elements, {mcids} marks)"
    (elems > 0 && mcids > 0)

mutual

/-- Every `img` element's `src` attribute in the typed tree, in document order. -/
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

/-- Captured raster bytes live in the typed image carrier and the one file the CLI publishes, and
replacing a raster changes its embedded URL. -/
def htmlAssetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let png : Image.Plan := { pxW := 64, pxH := 40 }
  let srcsOf (store : Image.Store) (doc : Ir.Doc) : Array String :=
    let (head, body, _) := HtmlDoc.emitTree { imgs := store } doc
    imgSrcsList (imgSrcsList #[] head.toList) body.toList
  let docOf (body : String) : IO Ir.Doc := do
    let (doc, ds) := elabStr (dvDoc "" body)
    t s!"html assets: fixture elaborates clean: {body}" ds.isEmpty
    return doc
  let rects ← IO.FS.readBinFile "testdata/corpus/rects.png"
  let alpha ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
  let rectsUri ← htmlDataOracle "image/png" rects
  let alphaUri ← htmlDataOracle "image/png" alpha
  let doc ← docOf "\\includegraphics[alt={A box}]{rects.png}"
  let one : Image.Store := { entries := #[{ src := "rects.png", info := some png, source := some rects }] }
  t "html assets: a loaded raster's src embeds its exact capture"
    (srcsOf one doc == #[rectsUri])
  t "html assets: the capture list carries the source bytes"
    ((HtmlDoc.imageResources one).map (·.bytes) == #[rects])
  let doc2 ← docOf "\\includegraphics[alt={A}]{a/plot.png} and \\includegraphics[alt={B}]{b/plot.png}"
  let two : Image.Store := { entries := #[
    { src := "a/plot.png", info := some png, source := some rects },
    { src := "b/plot.png", info := some png, source := some alpha }] }
  t "html assets: rasters sharing a basename retain distinct content URLs"
    (srcsOf two doc2 == #[rectsUri, alphaUri] && rectsUri != alphaUri)
  t "html assets: captured resources cover both in store order"
    ((HtmlDoc.imageResources two).map (·.bytes) == #[rects, alpha])
  let unloaded : Image.Store := { entries := #[{ src := "rects.png" }] }
  t "html assets: an unloaded entry keeps its source spelling and ships no copy"
    (srcsOf unloaded doc == #["rects.png"] && (HtmlDoc.imageAssets unloaded).isEmpty)
  let bare ← docOf "\\includegraphics[alt={A box}]{rects}"
  let resolved : Image.Store :=
    { entries := #[{ src := "rects", href := "rects.png", info := some png, source := some rects }] }
  t "html assets: a bare graphicx name embeds the resolved file's bytes"
    (srcsOf resolved bare == #[rectsUri])
  let pdfDoc ← docOf "\\includegraphics[alt={A page}]{box.pdf}"
  let pdfPlan := (Image.decode (← IO.FS.readBinFile "testdata/corpus/figures/box.pdf")).toOption
  let pdfStore : Image.Store :=
    { entries := #[{ src := "box.pdf", info := pdfPlan }] }
  t "html assets: a PDF source keeps its spelling and ships no copy"
    (srcsOf pdfStore pdfDoc == #["box.pdf"] && (HtmlDoc.imageAssets pdfStore).isEmpty)
  let picSrc := Ir.picSrcPrefix ++ "abc"
  let picStore : Image.Store :=
    { entries := #[{ src := picSrc, webSvg := some "<svg/>".toUTF8
                     info := some { pxW := 10, pxH := 10 } }] }
  t "html assets: a boundary picture embeds its SVG bytes"
    (HtmlDoc.imageHref picStore picSrc == "data:image/svg+xml;base64,PHN2Zy8+" &&
     (HtmlDoc.imageResources picStore).map (·.bytes) == #["<svg/>".toUTF8])
  t "html assets: equal names mean equal indices"
    (HtmlDoc.imageAssetName 3 "a/x.png" == "i3-x.png" &&
     HtmlDoc.imageAssetName 3 "a/x.png" != HtmlDoc.imageAssetName 13 "x.png" &&
     HtmlDoc.imageAssetName 12 "x.png" != HtmlDoc.imageAssetName 1 "2-x.png")
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds for the asset checks:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    IO.FS.withTempDir fun dir => do
      IO.FS.createDirAll (dir / "fonts")
      IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
        (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf"))
      let rects ← IO.FS.readBinFile "testdata/corpus/rects.png"
      IO.FS.writeBinFile (dir / "rects.png") rects
      let pre := "\\documentclass{article}\n\\usepackage{graphicx}\n\
\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }\n\\output{ formats = html }\n"
      let body := "\\begin{document}\nA box: \\includegraphics[alt={A box}]{rects.png}.\n\\end{document}\n"
      IO.FS.writeFile (dir / "doc.tex") (pre ++ body)
      IO.FS.createDirAll (dir / "out")
      let buildPage := IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := #[(dir / "doc.tex").toString, "-o", (dir / "out" / "x.html").toString] }
      let readImage (phase : String) (expected : ByteArray) : IO (String × String) := do
        let page ← IO.FS.readFile (dir / "out" / "x.html")
        let imgs := page.splitOn "<img "
        let tag := ((imgs.getD 1 "").splitOn ">").headD ""
        let attr := ((" " ++ tag).splitOn " src=\"").getD 1 ""
        let url := (attr.splitOn "\"").headD ""
        let expectedUri ← htmlDataOracle "image/png" expected
        t s!"driver: {phase}: the page embeds one raster byte for byte"
          (imgs.length == 2 && url == expectedUri)
        t s!"driver: {phase}: the output contains only the HTML file"
          ((← (dir / "out").readDir).map (·.fileName) == #["x.html"])
        return (page, url)
      let r ← buildPage
      t s!"driver: the page builds under -o out/x.html: {r.stdout}{r.stderr}" (r.exitCode == 0)
      let (_, url) ← readImage "first build" rects
      let alpha ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
      t "driver: the replacement raster has different source bytes" (alpha != rects)
      IO.FS.writeBinFile (dir / "rects.png") alpha
      let changed ← buildPage
      t s!"driver: the same document and output rebuild after replacing the raster: \
{changed.stdout}{changed.stderr}" (changed.exitCode == 0)
      let (changedPage, changedUrl) ← readImage "replaced raster" alpha
      t "driver: replacing bytes at the same source path changes the page's image URL"
        (url != changedUrl)
      let unchanged ← buildPage
      t s!"driver: the same document and output rebuild with unchanged raster bytes: \
{unchanged.stdout}{unchanged.stderr}" (unchanged.exitCode == 0)
      let (unchangedPage, unchangedUrl) ← readImage "unchanged raster" alpha
      t "driver: unchanged raster bytes preserve the page and its image URL"
        (unchangedPage == changedPage && unchangedUrl == changedUrl)
      IO.FS.writeFile (dir / "fail.tex") (pre ++ "\\assert{ pages == 99 }\n" ++ body)
      let r2 ← IO.Process.output {
        cmd := ".lake/build/bin/leantex"
        args := #[(dir / "fail.tex").toString, "-o", (dir / "out2").toString ++ "/"] }
      let assetDirs := (← System.FilePath.walkDir dir).filter fun p =>
        p.toString.endsWith ".assets"
      t "driver: a failing assertion publishes no page, no -o directory, and no .assets/ anywhere"
        (r2.exitCode != 0 && !(← (dir / "out2").pathExists) &&
         assetDirs.isEmpty)
      -- An error whose cause stops no writer ships the page beside it; a missing input does not.
      IO.FS.writeFile (dir / "lossy.tex") (pre ++ "\\begin{document}\n\\begin{itemize}\n" ++
        "Kqzv stray\n\\item one\n\\end{itemize}\n\\end{document}\n")
      IO.FS.writeFile (dir / "unread.tex")
        (pre ++ "\\begin{document}\n\\input{nowhere-invented}\n\\end{document}\n")
      let built (name : String) : IO (IO.Process.Output × Bool) := do
        let r ← IO.Process.output {
          cmd := ".lake/build/bin/leantex"
          args := #[(dir / s!"{name}.tex").toString, "-o", (dir / s!"{name}.html").toString] }
        return (r, ← (dir / s!"{name}.html").pathExists)
      let (lossy, lossyShips) ← built "lossy"
      t s!"driver: an error that stops no writer ships the page and exits 1: {lossy.stderr}"
        (lossy.exitCode == 1 && lossyShips && hasStr lossy.stderr "E0310" &&
          hasStr lossy.stderr "lossy.html")
      IO.FS.writeFile (dir / "asserted.tex") (pre ++ "\\assert{ pages == 3 }\n\\begin{document}\n" ++
        "\\begin{itemize}\nKqzv stray\n\\item one\n\\end{itemize}\n\\end{document}\n")
      let (asserted, _) ← built "asserted"
      t s!"driver: an error beside a failed assertion exits 1, both counted: {asserted.stderr}"
        (asserted.exitCode == 1 && hasStr asserted.stderr "2 errors")
      let (unread, unreadShips) ← built "unread"
      t s!"driver: a missing input still ships nothing: {unread.stderr}"
        (unread.exitCode == 1 && !unreadShips && hasStr unread.stderr "E0502")

/-- Assigned anchor ids are unique and numbered by the documented ladder. -/
def anchorIdChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pageOf (body : String) : String × Array Diag :=
    HtmlDoc.emit {} (elabStr ("\\documentclass{article}\\begin{document}" ++
      body ++ "\\end{document}")).1
  let page (body : String) : String := (pageOf body).1
  let shared := page (String.join ((List.range 3).map fun _ => "\\section{Topic}"))
  t "the first of three identical titles claims the bare slug"
    (hasStr shared "id=\"topic\"")
  t "the second takes -2 and the third -3"
    (hasStr shared "id=\"topic-2\"" && hasStr shared "id=\"topic-3\"")
  t "and no fourth id is invented" (!hasStr shared "id=\"topic-4\"")
  t "a repeated identical title takes its number without a warning"
    (((pageOf "\\section{Topic}\\section{Topic}").2.filter (·.code == "W0327")).isEmpty)
  let clash := pageOf "\\section{Data set}\\section{Data-set}"
  t "two different titles sharing a slug both ship an anchor"
    (hasStr clash.1 "id=\"data-set\"" && hasStr clash.1 "id=\"data-set-2\"")
  t "and the collision is named W0327"
    ((clash.2.filter (·.code == "W0327")).size == 1)
  let treeIds (body : Array Html.Node) : Array String :=
    (elemAttrsList (fun _ => true) #[] body.toList).filterMap fun (_, attrs) =>
      (HtmlDoc.attrOf? attrs "id").filter (·.startsWith "topic")
  let (_, early, earlyDs) := HtmlDoc.emitTree {} (elabStr ("\\documentclass{article}" ++
    "\\begin{document}\\section{Topic 4}" ++ String.join (List.replicate 4 "\\section{Topic}") ++
    "\\end{document}")).1
  t s!"a title taking a numbered form first is passed over by its base's claims: {treeIds early}"
    (treeIds early == #["topic-4", "topic", "topic-2", "topic-3", "topic-5"] &&
     (earlyDs.filter (·.code == "W0327")).size == 1)
  let (_, steps, stepDs) := HtmlDoc.emitTree {} (elabStr (dvDeck ""
    ("\\begin{frame}{Topic}\nx\\only<2>{y}\\only<3>{z}\n\\end{frame}\n" ++
     "\\begin{frame}{Topic}\nw\n\\end{frame}"))).1
  t s!"a stepped frame's step anchors are passed over by the next frame of its title: {treeIds steps}"
    (treeIds steps == #["topic", "topic-1", "topic-2", "topic-3", "topic-4"] &&
     !stepDs.any (·.code == "W0327"))
  let wide := page (String.join ((List.range 4000).map fun i => s!"\\section\{Topic {i}}"))
  t "the four-thousandth distinct section ships its own anchor, unnumbered"
    (hasStr wide "id=\"topic-3999\"" && !hasStr wide "id=\"topic-3999-2\"")
  let n := 1800
  let t0 ← IO.monoMsNow
  let big := page (String.join ((List.range n).map fun _ => "\\section{Topic}"))
  -- Consumed before the clock is read again: a pure `let` floats to its first use.
  t s!"all {n} same-titled sections ship an anchor"
    (hasStr big s!"id=\"topic-{n}\"" && hasStr big "id=\"topic\"")
  let sharedMs := (← IO.monoMsNow) - t0
  t s!"hang guard: {n} same-titled sections claim their anchors within {hangGuardMs 250} ms ({sharedMs} ms)"
    (sharedMs < hangGuardMs 250)
