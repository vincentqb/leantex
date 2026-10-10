module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! A supported HTML spelling is a typed Markdown construct, never markup
passed to the backend. These invented cases hold its visible content to the
shipped tree and layout. The disclosure loses interactivity, so its route
must name that loss even when every word ships. -/

def markdownHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let refused (src : String) : Bool :=
    (dvMd src).any fun d => d.kind == .E0390 && d.subject == some "md:raw-html"
  let disclosure := "<details>\n<summary>Amber &amp; linen</summary>\n\
\nCedar body.\n\n```\n<sample> & literal\n```\n\n- Elm item\n\
\n</details>\n\nFir after.\n"
  let tree := mdTreeOf disclosure
  t "a disclosure's summary ships before its complete body"
    (hasStr tree "<p><strong>Amber & linen</strong></p><p>Cedar body.</p>")
  t "a disclosure preserves its code, list and following block"
    (mdCodeBlocks disclosure == #[some "<sample> & literal"]
      && mdCodeBlocks disclosure == mdCodeBlocks "```\n<sample> & literal\n```\n"
      && hasStr tree "<ul><li>Elm item</li></ul><p>Fir after.</p>")
  t "supported disclosures compile and name their lost collapse for the HTML and the twin"
    (!refused disclosure
      && collapseNamed #[.html] (dvMd disclosure) == 1 && collapseNamed #[.md] (dvMd disclosure) == 1
      && collapseNamed #[.pdf] (dvMd disclosure) == 0)
  t "a disclosure with no blank lines still ships its summary and body"
    (hasStr (mdTreeOf "<details>\n<summary>Grove</summary>\nHazel\n</details>\nIris\n")
      "<p><strong>Grove</strong></p><p>Hazel</p><p>Iris</p>")
  t "adjacent disclosures remain separate and preserve source order"
    (hasStr (mdTreeOf "<details>\n<summary>Juniper</summary>\nKelp\n</details>\n\
<details>\n<summary>Larch</summary>\nMoss\n</details>\n")
      "<p><strong>Juniper</strong></p><p>Kelp</p>\
<p><strong>Larch</strong></p><p>Moss</p>")
  let nested := "<details>\n<summary>Outer</summary>\nBefore\n\
<details>\n<summary>Inner</summary>\nInside\n</details>\nAfter\n</details>\nEnd\n"
  t "nested disclosures preserve all summaries, bodies and following text"
    (!refused nested
      && hasStr (mdTreeOf nested)
        "<p><strong>Outer</strong></p><p>Before</p>\
<p><strong>Inner</strong></p><p>Inside</p><p>After</p><p>End</p>"
      && collapseNamed #[.html] (dvMd nested) == 2 && collapseNamed #[.md] (dvMd nested) == 2)
  for src in [
      "> <details>\n> <summary>Amber</summary>\n>\n> Cedar\n> </details>\n\nFir\n",
      "- <details>\n  <summary>Amber</summary>\n\n  Cedar\n  </details>\n\nFir\n"] do
    t "disclosures keep their surrounding quote or list container"
      (!refused src
        && (hasStr (mdTreeOf src) "</blockquote><p>Fir</p>"
          || hasStr (mdTreeOf src) "</li></ul><p>Fir</p>")
        && hasStr (mdTreeOf src) "<strong>Amber</strong>"
        && hasStr (mdTreeOf src) "Cedar")
  t "supported HTML names are case insensitive"
    (!refused "<DETAILS >\n<SUMMARY >Amber</SUMMARY >\nCedar\n</DETAILS >\n"
      && hasStr (mdTreeOf "<DETAILS >\n<SUMMARY >Amber</SUMMARY >\nCedar\n</DETAILS >\n")
        "<p><strong>Amber</strong></p><p>Cedar</p>")
  t "a summary is HTML text, not another Markdown or TeX parse"
    (hasStr (mdTreeOf "<details>\n<summary>*Oak* \\textbf{literal} &lt;sample&gt;</summary>\n\
Pine\n</details>\n") "<strong>*Oak* \\textbf{literal} <sample></strong>")
  let quoted := "<details>\n<summary>&lt;script&gt;alert(7)&lt;/script&gt; \
\\input{literal} &amp; &#60;img&#62;</summary>\nBody\n</details>\n"
  let (_, safeBody, _) := HtmlDoc.emitTree {} (elabMd quoted).1
  let rendered := Html.render (Html.elem "div" safeBody) 0
  t "decoded summary markup remains visible escaped text in the artifact"
    (!refused quoted
      && hasStr rendered "&lt;script&gt;alert(7)&lt;/script&gt;"
      && hasStr rendered "\\input{literal} &amp; &lt;img&gt;"
      && (elemNodesList (fun tag => tag == "script" || tag == "img") #[] safeBody.toList).isEmpty
      && !hasStr rendered "<script" && !hasStr rendered "<img")
  t "comments have no visible content and do not refuse the document"
    (!refused "<!-- hidden -->\n\nReed\n"
      && hasStr (mdTreeOf "<!-- hidden -->\n\nReed\n") "<p>Reed</p>")
  t "an inline comment preserves adjoining text and Markdown emphasis"
    (!refused "Sage<!-- **hidden** -->*Thyme*\n"
      && hasStr (mdTreeOf "Sage<!-- **hidden** -->*Thyme*\n") "<p>Sage<em>Thyme</em></p>")
  t "comment boundary validation stops at the consumed comment"
    (!refused "Sage<!-- hidden -->--!>Thyme\n"
      && mdTreeOf "Sage<!-- hidden -->--!>Thyme\n" == mdTreeOf "Sage--!>Thyme\n")
  t "a multiline block comment consumes its own lines only"
    (!refused "<!--\n# hidden\n-->\n\nUmber\n"
      && hasStr (mdTreeOf "<!--\n# hidden\n-->\n\nUmber\n") "<p>Umber</p>")
  t "an unclosed block comment ends at the container boundary or end of input"
    (mdTreeOf "<!-- hidden\n# hidden\n" == mdTreeOf ""
      && !refused "<!-- hidden\n# hidden\n"
      && !refused "> <!-- hidden\n\nVisible\n"
      && hasStr (mdTreeOf "> <!-- hidden\n\nVisible\n") "<p>Visible</p>")
  t "an incomplete inline comment follows ordinary literal text semantics"
    (!refused "Amber <!-- incomplete\n"
      && mdTreeOf "Amber <!-- incomplete\n" == mdTreeOf "Amber \\<!-- incomplete\n"
      && hasStr (mdTreeOf "Amber <!-- incomplete\n") "<p>Amber <!– incomplete</p>")
  let fence := "```\n<!-- visible -->\n<details>\n```\n"
  let (_, fenceBody, _) := HtmlDoc.emitTree {} (elabMd fence).1
  t "HTML spellings inside a fence are literal code"
    (!refused fence && match mdPresList #[] fenceBody.toList with
      | #[.elem "pre" attrs #[.elem "code" cas kids]] =>
        attrs == mdCodeBlockPreAttrs && cas.isEmpty
          && kids.all (fun n => match n with | .text _ => true | _ => false)
          && nodeTextList "" kids.toList == "<!-- visible -->\n<details>"
      | _ => false)
  t "an empty named anchor becomes a typed target and its link still resolves"
    (!refused "<a name=\"willow\"></a>\n\n[Willow](#willow)\n"
      && hasStr (mdTreeOf "<a name=\"willow\"></a>\n\n[Willow](#willow)\n")
        "id=willow"
      && hasStr (mdTreeOf "<a name=\"willow\"></a>\n\n[Willow](#willow)\n")
        "href=#willow")
  t "an inline named anchor preserves the text on both sides"
    (!refused "Yarrow<a id='zinnia'></a>Zinnia\n"
      && hasStr (mdTreeOf "Yarrow<a id='zinnia'></a>Zinnia\n")
        "Yarrow<span id=zinnia></span>Zinnia")
  t "target keys keep case and punctuation across HTML spelling variants"
    (!refused "<A NAME = Grove.1:_- ></A >\n\n[Go](#Grove.1:_-)\n"
      && hasStr (mdTreeOf "<A NAME = Grove.1:_- ></A >\n\n[Go](#Grove.1:_-)\n")
        "id=Grove.1:_-"
      && hasStr (mdTreeOf "<A NAME = Grove.1:_- ></A >\n\n[Go](#Grove.1:_-)\n")
        "href=#Grove.1:_-")
  for key in ["fern₈", "fern₉", "café", "東京", "ø-β"] do
    let src := s!"<a name=\"{key}\"></a>\n\n[Go](#{key})\n"
    let (_, body, _) := HtmlDoc.emitTree {} (elabMd src).1
    t "a Unicode target keeps its exact key at both ends of its fragment link"
      (!refused src
        && (elemNodesList (· == "span") #[] body.toList).any
          (fun n => match n with
            | .elem _ attrs _ => attrs.contains ("id", key)
            | _ => false)
        && (elemNodesList (· == "a") #[] body.toList).any
          (fun n => match n with
            | .elem _ attrs _ => attrs.contains ("href", "#" ++ key)
            | _ => false))
  t "distinct Unicode target keys do not collapse to the same native anchor"
    (hasStr (mdTreeOf "<a id=\"fern₈\"></a><a id=\"fern₉\"></a>\n")
      "id=fern₈></span><span id=fern₉>")
  -- `open` on a disclosure is its expanded state, which the disclosure sets
  -- (`htmlTwinChecks`); on any other element, and beside another attribute,
  -- it is refused like every attribute the vocabulary does not read.
  for attrs in ["open", "hidden", "aria-hidden=\"true\"", "role=\"none\"",
      "lang=\"de\"", "style=\"display:none\"", "onclick=\"evil()\""] do
    for src in (if attrs == "open" then [] else
          [s!"<details {attrs}>\n<summary>Amber</summary>\nCedar\n</details>\n"]) ++ [
        s!"<details>\n<summary {attrs}>Amber</summary>\nCedar\n</details>\n",
        s!"<a name=\"willow\" {attrs}></a>\n"] do
      t s!"HTML attributes are never silently discarded: {attrs}" (refused src)
  for src in [
      "<details onclick=\"evil()\">\n<summary>Amber</summary>\nCedar\n</details>\n",
      "<details>\n<summary hidden>Amber</summary>\nCedar\n</details>\n",
      "<details>\n<summary>Amber<script>evil()</script></summary>\nCedar\n</details>\n",
      "<a id=\"willow\" onclick=\"evil()\"></a>\n",
      "<a name=\"willow\">visible</a>\n",
      "<a name=\"willow\" id=\"other\"></a>\n",
      "<a name=\"two words\"></a>\n", "<a name=\"willow&quot;other\"></a>\n",
      "<a id=\"\"></a>\n", "<a id=\"willow\"/>\n",
      "<script>evil()</script>\n", "<img src=\"https://example.org/x\">\n",
      "<div hidden>visible</div>\n",
      "<!-- hidden -->Visible\n", "<!-- hidden\n-->Visible\n",
      "Amber<!-- hidden --!>Willow<!-- tail -->Cedar\n",
      "<!-- hidden --!>Willow<!-- tail -->\n\nCedar\n",
      "<!-- hidden\n--!>Willow<!-- tail -->\n\nCedar\n",
      "<!-- hidden --!>Willow\n",
      "<details-extra>\n<summary>Amber</summary>\nCedar\n</details-extra>\n",
      "<details open=\"false\">\n<summary>Amber</summary>\nCedar\n</details>\n",
      "<details open name=\"g\">\n<summary>Amber</summary>\nCedar\n</details>\n",
      "<details/>\n<summary>Amber</summary>\nCedar\n</details>\n",
      "<details>\n<summary>Amber</summary>Visible\nCedar\n</details>\n",
      "<details>\n<summary>Amber</summary>\nCedar\n</details>Visible\n",
      "<details>\n<summary>Amber &NotEqualTilde;</summary>\nCedar\n</details>\n",
      "<details>\n<summary>Amber &copy</summary>\nCedar\n</details>\n",
      "<details>\n<summary>Amber &#128;</summary>\nCedar\n</details>\n",
      "<details>\nCedar\n</details>\n",
      "<details>\n<summary>Amber</summary>\nCedar\n",
      "</details>\n"] do
    t s!"unsupported HTML remains refused: {src.replace "\n" "⏎"}" (refused src)
  let some fonts ← serifFacesSet
    | t "the Markdown HTML regression faces load" false
      return
  let (doc, _) := elabMd disclosure
  let painted := String.intercalate "\n" ((bodyLines (layoutOf fonts doc)).map lineText).toList
  for word in ["Amber", "linen", "Cedar", "body.", "<sample>", "literal", "Elm", "Fir"] do
    t s!"a disclosure's {word} reaches the shipped layout" (hasStr painted word)

/-- The source text a diagnostic's span starts at, to the end of its line. -/
def mdSpanText (src : String) (d : Diag) : String :=
  match d.span with
  | none => ""
  | some sp =>
    match (src.splitOn "\n").toArray[sp.pos.line - 1]? with
    | none => ""
    | some l => String.ofList (l.toList.drop (sp.pos.col - 1))

/-- **Every raw HTML element is lowered or named, once — evidence for the
loop, not a theorem.** `htmlInlineAt_accounts` states one step of the inline
scan; the scan that resumes past each step, and the block reader around it,
are read here over a generated family instead: tag names from the block, raw
and phrasing vocabularies and an invented one, in four tag shapes and a
comment, at seven sites. Every refusal stands on the `<` of one of the
shape's tags, no site is named by two codes, and inside a paragraph the page
is the page with the refused tags deleted, keeping exactly its bare breaks,
and the refusals count the refused tags. -/
def mdHtmlAccountsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let tree := docTreeOf
  let raw (ds : Array Diag) : Array Diag :=
    ds.filter fun d => d.kind == .E0390 && d.subject == some "md:raw-html"
  let names := ["div", "p", "table", "details", "summary", "h2", "pre", "script", "style",
    "textarea", "b", "em", "code", "kbd", "sub", "sup", "span", "img", "br", "wbr", "input",
    "x-kestrel"]
  let mut bad : Array String := #[]
  for n in names do
    for (shape, tags) in [(s!"<{n}>Kestrel</{n}>", [s!"<{n}>", s!"</{n}>"]),
        (s!"<{n}/>", [s!"<{n}/>"]), (s!"<{n} data-k=\"1\">", [s!"<{n} data-k=\"1\">"]),
        (s!"</{n}>", [s!"</{n}>"])] do
      for (site, place) in mdHtmlSites do
        -- A bare `<br>` is the vocabulary: carried as a break, never refused.
        let carried := tags.filter fun tg => tg == "<br>" || tg == "<br/>"
        let refusedTags := tags.filter (!carried.contains ·)
        -- A §4.6 condition-1 block runs to its own closing tag, so inside a
        -- disclosure body it also consumes the disclosure's `</details>`:
        -- the disclosure is then refused, once, at its own `<`.
        let unclosing := site == "disclosure body" &&
          ["pre", "script", "style", "textarea"].contains n && shape != s!"<{n}>Kestrel</{n}>"
        let src := place shape
        let (doc, ds) := elabMd src
        let refused := raw ds
        let label := s!"{site} {shape}"
        unless refused.all (fun d => (tags ++ (if unclosing then ["<details>"] else [])).any
            ((mdSpanText src d).startsWith ·)) do
          bad := bad.push s!"{label}: a refusal stands off the shape's tags"
        unless siteCollisions ds == #[] do
          bad := bad.push s!"{label}: two codes name one site {siteCollisions ds}"
        if site == "mid-paragraph" then
          let bare := refusedTags.foldl (fun s tg => s.replace tg "") src
          unless tree doc == tree (elabMd bare).1 do
            bad := bad.push s!"{label}: the page is not the page with the refused tags deleted"
          unless refused.size == refusedTags.length do
            bad := bad.push s!"{label}: {refused.size} refusals for {refusedTags.length} tags"
          unless ((tree doc).splitOn "<br>").length == carried.length + 1 do
            bad := bad.push s!"{label}: the page does not carry exactly its bare breaks"
        else if refused.isEmpty && !(!carried.isEmpty && hasStr (tree doc) "<br>") then
          bad := bad.push s!"{label}: nothing refused and nothing carried"
  t s!"every raw HTML element is lowered, or refused once at its own < \
({bad.size} faults; first: {bad.toList.take 3})" bad.isEmpty
  -- A comment ships nothing and names nothing, wherever it is the whole of
  -- its line or sits inside text: both pages and the diagnostics are those
  -- of the document without it. Opening a line that holds text, it is the
  -- start of a larger raw block (§4.6), refused once at its `<`.
  let some fonts ← serifFacesSet
    | t "the raw HTML accounts faces load" false
      return
  let comment := "<!-- Kestrel -->"
  for (site, place) in mdHtmlSites do
    let src := place comment
    let (doc, ds) := elabMd src
    if site == "line start" then
      t "a comment opening a line that holds text is refused once, at its <"
        ((raw ds).size == 1 && (raw ds).all fun d => (mdSpanText src d).startsWith "<!--")
    else
      let (bareDoc, bareDs) := elabMd (src.replace comment "")
      t s!"a comment {site} ships nothing and names nothing"
        (tree doc == tree bareDoc && !hasStr (tree doc) "Kestrel"
          && shippedLinesOf fonts doc == shippedLinesOf fonts bareDoc
          && ds.map (fun d => (d.code, d.subject)) == bareDs.map (fun d => (d.code, d.subject)))

/-- The two artifacts a twin row compares, and what the run named: the
emitted HTML document's bytes, every shipped line's position, size and text,
and each diagnostic's code and subject. -/
def mdArtifactsOf (fonts : Font.FontSet) (src : String) :
    String × Array (Dim.Sp × Dim.Sp × Dim.Sp × String) × Array (String × Option String) :=
  let (doc, ds) := elabMd src
  ((HtmlDoc.emit {} doc).1, shippedLinesOf fonts doc, ds.map fun d => (d.code, d.subject))

/-- The text of the document's own shipped lines, furniture left out. -/
def mdBodyTextOf (fonts : Font.FontSet) (src : String) : Array String :=
  (bodyLines (layoutOf fonts (elabMd src).1)).map lineText

/-- A context a twin row places a spelling in: what opens its first line,
what every later line carries, and what closes its last. -/
def mdInContext (ctx : String × String × String × String) (s : String) : String :=
  let (_, first, rest, close) := ctx
  let ls := (s.splitOn "\n").zipIdx.map fun (l, k) => (if k == 0 then first else rest) ++ l
  String.intercalate "\n" ls ++ close ++ "\n"

/-- The contexts a block spelling is placed in. -/
def mdBlockContexts : List (String × String × String × String) :=
  [("document", "", "", ""), ("list item", "- ", "  ", ""), ("quote", "> ", "> ", "")]

/-- The contexts an inline spelling is placed in. -/
def mdInlineContexts : List (String × String × String × String) :=
  mdBlockContexts ++ [("link text", "[", "", "](https://example.org)"), ("emphasis", "*", "", "*")]

/-- **An HTML spelling the reader accepts ships its markdown twin.** Each
row is spellings the vocabulary reads and the one they all lower to; in
every context the row names, a spelling and its twin give byte-identical
HTML, the same shipped lines (position, size and text) and the same
diagnostics. Never the IR: a row holds the artifacts, where a reader meets
the page. -/
def htmlTwinChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet
    | t "the HTML twin regression faces load" false
      return
  let disclosure (opener : String) : String :=
    opener ++ "\n<summary>Amber</summary>\n\nCedar\n\n</details>"
  let rows : List (List String × String × List (String × String × String × String)) :=
    [(["Alder<br>Birch", "Alder<br/>Birch", "Alder<BR />Birch", "Alder <br>\nBirch"],
      "Alder  \nBirch", mdInlineContexts),
     (["<details open>", "<details open=\"\">", "<DETAILS OPEN=open>"].map disclosure,
      disclosure "<details>", mdBlockContexts)]
  for (spellings, twin, contexts) in rows do
    for spelling in spellings do
      for ctx in contexts do
        let label := s!"{ctx.1}: {spelling.replace "\n" "⏎"}"
        let (ah, al, ad) := mdArtifactsOf fonts (mdInContext ctx spelling)
        let (bh, bl, bd) := mdArtifactsOf fonts (mdInContext ctx twin)
        t s!"an accepted HTML spelling ships its twin's HTML ({label})" (ah == bh)
        t s!"an accepted HTML spelling ships its twin's lines ({label})" (al == bl)
        t s!"an accepted HTML spelling names what its twin names ({label})" (ad == bd)
  for opener in ["<details open>", "<details open=\"\">", "<DETAILS OPEN=open>"] do
    let ds := dvMd (disclosure opener)
    t s!"{opener} names its lost collapse once for each artifact that loses it"
      (collapseNamed #[.html] ds == 1 && collapseNamed #[.md] ds == 1 && collapseNamed #[.pdf] ds == 0)
  -- A break before a bracket reads no length: the bracket is text.
  let (xh, _, xd) := mdArtifactsOf fonts "Alder<br>[x]\n"
  t "a <br> before a bracket ships the bracket as text"
    (hasStr xh "Alder<br>[x]" && mdBodyTextOf fonts "Alder<br>[x]\n" == #["Alder", "[x]"]
      && xd.isEmpty)
  -- An attribute, the closing spelling and a line holding only the tag
  -- are not the vocabulary: each is refused once, at its own `<`.
  for (src, col) in [("Alder<br class=\"k\">Birch\n", 6), ("Alder</br>Birch\n", 6),
      ("<br>\n", 1)] do
    let ds := dvMd src
    t s!"{src.replace "\n" "⏎"} is refused once, at its <"
      (ds.size == 1 && ds.all fun d => d.kind == .E0390 && d.subject == some "md:raw-html"
        && d.span.map (·.pos.col) == some col)
  -- Markdown writes no break inside a heading; this spelling can, and both
  -- artifacts set it: the HTML heading holds the break and the page sets
  -- two heading lines.
  let (hh, _, hd) := mdArtifactsOf fonts "# Alder<br>Birch\n"
  t "a <br> inside a heading ships in the heading's HTML" (hasStr hh "Alder<br>Birch</h1>")
  t "a <br> inside a heading sets two heading lines"
    (mdBodyTextOf fonts "# Alder<br>Birch\n" == #["Alder", "Birch"] && hd.isEmpty)

/-- Where a shipped line's text stands on the page: the left edge of its
first glyph run and the right edge of its last, its segments walked as the
page paints them. -/
def inkSpanOf (l : Layout.LineOut) : Option (Dim.Sp × Dim.Sp) := Id.run do
  let mut px := l.x
  let mut first : Option Dim.Sp := none
  let mut last : Option Dim.Sp := none
  for seg in l.segs do
    match seg with
    | .run _ _ _ w .. =>
      if first.isNone then first := some px
      px := px + w
      last := some px
    | .gap w _ | .decoratedGap w _ _ | .rule w .. | .decoration _ w .. | .image _ w _ =>
      px := px + w
    | .poly .. => pure ()
  return match first, last with
    | some a, some b => some (a, b)
    | _, _ => none

/-- **A break inside a table cell sets as its lines would as rows.** A
`<br>` in a cell is a line of its own, on the page as in a browser: each
line stands on its column's side — left, right or centred, as the delimiter
row says — and the column is as wide as its widest line, never as the
cell's words on one line. Held on the shipped lines, against the same words
spelled as rows, for each side; the page's cell keeps its break. -/
def cellBreakChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet
    | t "the cell break faces load" false
      return
  let spanOf (src word : String) : Option (Dim.Sp × Dim.Sp) :=
    ((bodyLines (layoutOf fonts (elabMd src).1)).find? (fun l => hasStr (lineText l) word)).bind
      inkSpanOf
  for (side, delim) in [("left", "---"), ("right", "---:"), ("centred", ":---:")] do
    let broken := s!"| Alder | Elm |\n| --- | {delim} |\n| Cedar | Fir<br>Gorse bush |\n"
    let rows := s!"| Alder | Elm |\n| --- | {delim} |\n| Cedar | Fir |\n|  | Gorse bush |\n"
    for w in ["Elm", "Fir", "Gorse bush"] do
      t s!"a {side} cell's broken lines stand where its lines as rows stand ({w}: \
{repr (spanOf broken w)}, as rows {repr (spanOf rows w)})"
        ((spanOf broken w).isSome && spanOf broken w == spanOf rows w)
    t s!"a {side} cell's page keeps its break inside the cell"
      (hasStr (HtmlDoc.emit {} (elabMd broken).1).1 "Fir<br>Gorse bush</td>")
  -- A tex natural cell holds no break and sets as it always has: on one
  -- line, from the very items its column was measured from, the
  -- document's hyphenation in force; a braced `\\` is a break, and its
  -- lines stand on the column's side.
  let pats := Hyphen.english.get
  for spec in ["l", "c", "r"] do
    for words in ["anything", "article artifact", "a hyphenation candidate"] do
      let src := s!"\\begin\{tabular}\{{spec}}{words}\\end\{tabular}\n"
      let out := layoutOf fonts (elabStr (dvDoc "" src)).1 (pats := some pats)
      let lines := (bodyLines out).filter fun l => !(lineText l).trimAscii.isEmpty
      t s!"a tex {spec} cell without a break sets on one line, never overfull ({words})"
        ((lines.toList.map lineText).any (hasStr · words) && lines.size == 1 &&
          !(out.diags.any (·.code == "W0005")))
  let braced := "\\begin{tabular}{r}Elm\\\\{Fir\\\\Gorse bush}\\end{tabular}\n"
  let out := layoutOf fonts (elabStr (dvDoc "" braced)).1 (pats := some pats)
  let rights := ["Elm", "Fir", "Gorse bush"].map fun w =>
    ((bodyLines out).find? fun l => hasStr (lineText l) w).bind inkSpanOf |>.map (·.2)
  t s!"a tex r cell's braced break sets its lines flush right ({repr rights})"
    (rights.all (·.isSome) && (rights.eraseDups.length == 1))
  let wide := "| Alder | Elm |\n| --- | --- |\n| Cedar<br>Dove | Fir |\n"
  let wideRows := "| Alder | Elm |\n| --- | --- |\n| Cedar | Fir |\n| Dove |  |\n"
  for w in ["Elm", "Fir"] do
    t s!"a column holding a broken cell is as wide as its widest line ({w}: \
{repr (spanOf wide w)}, as rows {repr (spanOf wideRows w)})"
      ((spanOf wide w).isSome && spanOf wide w == spanOf wideRows w)

/-- Does each word stand in `hay` exactly once, in this order? -/
def mdOnceInOrder (hay : String) (ws : List String) : Bool :=
  let at_ (w : String) : Nat := ((hay.splitOn w).headD "").length
  ws.all (fun w => (hay.splitOn w).length == 2) &&
    ((ws.map at_).zip ((ws.map at_).drop 1)).all fun (a, b) => a < b

/-- **A refused disclosure is accounted once.** A disclosure with no
summary, one its input ends inside, and one its list item cuts off are each
refused at their opening `<`, the document's one diagnostic, and each ships
every word it held, once, in source order — with no disclosure of its own,
so no collapse is named and no empty summary sets. A summary line the reader
cannot read — a tag inside it, an attribute on it, a summary over several
lines — is raw HTML: refused at its own `<` and its lines dropped, as an HTML
block's are, and that refusal is the disclosure's one diagnostic too, every
other word still shipping once, in order. -/
def refusedDisclosureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (label, src, words, dropped, at_) in [
      ("no summary", "<details>\nCedar\n</details>\n", ["Cedar"], [], (1, 1)),
      ("unclosed", "<details>\n<summary>Amber</summary>\nCedar\n", ["Amber", "Cedar"], [], (1, 1)),
      ("cut off by its list item", "- <details>\n  <summary>Amber</summary>\n  Cedar\n\nFir\n",
        ["Amber", "Cedar", "Fir"], [], (1, 3)),
      ("a summary holding a tag",
        "<details>\n<summary>Amber<br>Birch</summary>\n\nCedar\n\n</details>\n",
        ["Cedar"], ["Amber", "Birch"], (2, 1)),
      ("an unclosed summary with an attribute", "<details>\n<summary hidden>Amber</summary>\n\nCedar\n",
        ["Cedar"], ["Amber"], (2, 1)),
      ("a summary over several lines",
        "<details>\n<summary>\nAmber\n</summary>\n\nCedar\n\n</details>\nFir\n",
        ["Cedar", "Fir"], ["Amber"], (2, 1)),
      ("a summary tag spread over two lines",
        "<details>\n<summary\nclass=\"x\">Amber</summary>\n\nCedar\n\n</details>\n",
        ["Cedar"], ["Amber"], (2, 1)),
      ("a summary tag closed on its next line",
        "<details>\n<summary class=\"x\"\n>Amber</summary>\n\nCedar\n\n</details>\n",
        ["Cedar"], ["Amber"], (2, 1)),
      ("an unclosed disclosure whose summary tag spans lines",
        "<details>\n<summary\nclass=\"x\">Amber</summary>\n\nCedar\n",
        ["Cedar"], ["Amber"], (2, 1))] do
    let (doc, ds) := elabMd src
    let shown := docTreeOf doc
    t s!"a refused disclosure ({label}) is its document's one diagnostic, at its <"
      (ds.size == 1 && ds.all fun d => d.kind == .E0390 && d.subject == some "md:raw-html"
        && d.span.map (fun sp => (sp.pos.line, sp.pos.col)) == some at_)
    t s!"a refused disclosure ({label}) names no collapse and no site twice"
      (ds.all (·.subject != some "md:disclosure") && siteCollisions ds == #[])
    t s!"a refused disclosure ({label}) ships every other word once, in source order"
      (mdOnceInOrder shown words && dropped.all (!hasStr shown ·))
    t s!"a refused disclosure ({label}) sets no empty summary" (!hasStr shown "<strong></strong>")

/-- The fixes the raw-HTML help names, each as the rewrite of a refused
construct it asks the author for. The help is exactly these phrases, in
this order, so a fix the help gains owes its rewrite here. -/
def rawHtmlFixes : List (String × (String → String)) :=
  [("write it in markdown (**bold**, *emphasis*, [text](url), ![alt](src))", fun _ => "**Kestrel**"),
   ("quote it as a code span with `...`", fun raw => s!"`{raw}`"),
   ("delete the tags", fun _ => "Kestrel")]

/-- The elements a block opens: what a fix must leave as the bare word left
it, text and phrasing aside. -/
def mdBlockNames : List String :=
  ["p", "h1", "h2", "h3", "h4", "h5", "h6", "ul", "ol", "li", "blockquote", "section",
    "details", "summary", "div", "pre", "table", "hr"]

mutual

/-- The block elements a node opens, in document order, onto `acc`. -/
def mdBlockTagsOne (acc : Array String) : Html.Node → Array String
  | .elem tag _ kids =>
    mdBlockTagsList (if mdBlockNames.contains tag then acc.push tag else acc) kids.toList
  | _ => acc

/-- `mdBlockTagsOne` over siblings, the accumulator threaded. -/
def mdBlockTagsList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | n :: rest => mdBlockTagsList (mdBlockTagsOne acc n) rest

end

/-- The block elements a document's page opens, in order. -/
def mdBlockTags (doc : Ir.Doc) : Array String :=
  mdBlockTagsList #[] (HtmlDoc.emitTree {} doc).2.1.toList

/-- **Every fix the raw-HTML help names keeps the refused text where it
stood.** An inline tag pair at every site the accounts family places one,
and a block on its own: every refusal's help is exactly `rawHtmlFixes`'
phrases, and each fix, applied there, reads with no refusal and opens the
blocks the bare word opens there, the word inside them. A fix that moved
the text out of its block — a blank line around an inline tag's text splits
its paragraph in three — fails here. -/
def mdRawHtmlHelpChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let help := match (rawHtmlFixes.map (·.1)).reverse with
    | [] => ""
    | [one] => one
    | last :: before => ", ".intercalate before.reverse ++ ", or " ++ last
  let cases := (mdHtmlSites.map fun (site, place) => (site, place, "<b>Kestrel</b>")) ++
    [("own block, a block construct", fun s => s!"Alder\n\n{s}\n\nBirch\n", "<div>Kestrel</div>")]
  for (site, place, raw) in cases do
    let refused := (dvMd (place raw)).filter (·.kind == .E0390)
    t s!"the raw-HTML help names exactly its fixes ({site})"
      (!refused.isEmpty && refused.all (·.help == some help))
    let bare := mdBlockTags (elabMd (place "Kestrel")).1
    for (phrase, fix) in rawHtmlFixes do
      let (doc, ds) := elabMd (place (fix raw))
      t s!"'{phrase}' reads with no refusal ({site})" (ds.all (·.kind != .E0390))
      t s!"'{phrase}' keeps the text in its block ({site})"
        (mdBlockTags doc == bare && hasStr (docTreeOf doc) "Kestrel")

/-- **A hard break, and text that spells one, survive markdown → markdown
in every context.** The markdown backend writes a hard break as `<br>`, which
the reader reads back as that break wherever it stands; a backslash or two
trailing spaces end the line instead, which a heading cannot continue and a
container's next line continues only behind the container's prefix. Text is
the other half: the reader reads `<br>`, a comment, an empty target, a
disclosure and a character reference as what they spell, so text holding
one is written escaped — and inside a code span, which reads literally, as
it is. For each source the twin reads back with nothing raised, to the
source's page — rendered, which tells a break from the text `<br>` — and
is its own twin; and a tex document's breaks stay inside the constructs
that held them while its text stays text. A table cell is held to GFM's
spelling, every pipe escaped, and a break inside one reads back as the
break it was. -/
def mdTwinBreakChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (ctx, src) in [("paragraph", "Alder<br>Birch\n"), ("heading", "# Alder<br>Birch\n"),
      ("list item", "- Alder<br>Birch\n"), ("nested list item", "- Cedar\n  - Alder<br>Birch\n"),
      ("quote", "> Alder<br>Birch\n"), ("emphasis", "*Alder<br>Birch*\n"),
      ("link text", "[Alder<br>Birch](https://example.org)\n"),
      ("a break's spellings as text", "Write \\<br> to break, or &lt;br/&gt; with references.\n"),
      ("a heading's text", "# Alder \\<br> Birch\n"),
      ("a comment as text", "Keep \\<!-- Cedar --> in view.\n"),
      ("a target as text", "Mark \\<a name=\"willow\">\\</a> here.\n"),
      ("a run ending on a break", "*Alder<br>*\n"), ("a strong run ending on two breaks", "**Alder<br><br>**\n"),
      ("a run ending on a break, then text", "**Alder<br>** Birch\n"),
      ("a run ending on a break after text", "Birch **Alder<br>**\n"),
      ("a list item's run ending on a break", "- **Alder<br>**\n"),
      ("a quotation's run ending on a break", "> *Alder<br>*\n"),
      ("a table cell's break", "| Alder | Elm |\n| --- | --- |\n| Birch<br>Cedar | Fir |\n"),
      ("a heading's break", "## Gorse<br>Holly\n"),
      ("a target and its link", "<a name=\"willow\"></a>Mark here, and [back](#willow).\n"),
      ("a target by id", "<a id=\"birch\"></a>Mark here, and [back](#birch).\n"),
      ("a disclosure as text", "\\<details>\n\n\\<summary>Amber\\</summary>\n\nCedar\n"),
      ("references as text", "Elm &amp; Fir write &amp;lt; as text.\n"),
      ("code spans", "Code `<br>`, `a & b`, `&lt;`, `a|b`, ``a`b``, `*x*` and `\\`.\n")] do
    let doc := (elabMd src).1
    let twin := MarkdownDoc.emit doc
    let (back, backDs) := elabMd twin
    t s!"a twin reads back with nothing raised ({ctx})" backDs.isEmpty
    t s!"a twin reads back to the source's page ({ctx})" (docHtmlOf back == docHtmlOf doc)
    t s!"a twin is its own twin ({ctx})" (MarkdownDoc.emit back == twin)
  let tex := "\\section{Alder\\\\Birch}\nCedar\\\\Dove\n\\begin{itemize}\\item Elm\\\\Fir\\end{itemize}\n" ++
    "\\begin{quote}Gorse\\\\Holly\\end{quote}\n" ++
    "Iris<br>Juniper, \\texttt{Kelp<br>Larch} and Moss\\&lt;Nettle.\n"
  let twin := MarkdownDoc.emit (elabStr tex).1
  let (back, backDs) := elabMd twin
  let html := docHtmlOf back
  t "a tex document's twin reads back with nothing raised" backDs.isEmpty
  for (a, b) in [("Alder", "Birch"), ("Cedar", "Dove"), ("Elm", "Fir"), ("Gorse", "Holly")] do
    t s!"a tex break between {a} and {b} stays inside its construct" (hasStr html s!"{a}<br>{b}")
  for shown in ["Iris&lt;br&gt;Juniper", "Kelp&lt;br&gt;Larch", "Moss&amp;lt;Nettle"] do
    t s!"a tex document's text reads back as text: {shown}" (hasStr html shown)
  -- A run's closing break in a tex document's twin: kept inside the run
  -- as `<br>` only where its closer still closes after one — never before
  -- a word, through an enclosing run or a wrapper with no delimiter — so
  -- the emphasis reads back, in a paragraph, a heading and a cell alike.
  for src in ["\\emph{\\textbf{Alder\\\\}}Birch", "\\textcolor{red}{\\emph{Alder\\\\}}Birch",
      "\\underline{\\emph{Alder\\\\}}Birch", "\\textsc{\\emph{Alder\\\\}}Birch",
      "\\section{\\emph{Alder\\\\}Birch}", "\\section{Birch\\emph{\\\\Alder}}",
      "\\begin{tabular}{l}{\\emph{Alder\\\\}}Birch\\end{tabular}"] do
    let twin := MarkdownDoc.emit (elabStr (src ++ "\n")).1
    let (back, backDs) := elabMd twin
    let page := docHtmlOf back
    t s!"a tex run's closing break keeps its emphasis in the twin ({src}: {repr twin})"
      (backDs.isEmpty && MarkdownDoc.emit back == twin && hasStr page "Alder" &&
        (hasStr page "<em>" || hasStr page "<strong>") && !hasStr page "*")
  -- A footnote inside code-set text keeps its mark there and its note once,
  -- after the document, never copied into the code.
  let noted := MarkdownDoc.emit (elabStr "\\texttt{alpha\\footnote{Gamma note.}beta}\n").1
  t s!"a note inside code keeps its mark and its text once ({repr noted})"
    (hasStr noted "`alpha`[^1]`beta`" && (noted.splitOn "Gamma note.").length == 2)
  -- A target reads back under the id the source page gives it, so a link
  -- to it lands in the twin's page as in the source's.
  let labelled := (elabStr "\\section{Alder}\\label{sec:alder}\nSee the section.\n").1
  let twin := MarkdownDoc.emit labelled
  let (back, backDs) := elabMd twin
  t s!"a tex label's twin is a target under the page's id ({repr twin})"
    (hasStr twin "<a name=\"sec:alder\"></a>" && backDs.isEmpty &&
      hasStr (docHtmlOf labelled) "id=\"sec:alder\"" && hasStr (docHtmlOf back) "id=\"sec:alder\"")
  -- A pipe-table row splits at every unescaped `|`, a code span's and a
  -- destination's included, and reads `\|` back as `|` (GFM 4.10).
  let table := MarkdownDoc.emit (elabStr ("\\begin{tabular}{ll}\\texttt{a|b} & c|d\\\\" ++
    "x & \\href{https://example.org/a|b}{e}\\end{tabular}\n")).1
  t "a table cell's twin escapes every pipe it holds"
    (hasStr table "| `a\\|b` | c\\|d |" && hasStr table "| x | [e](https://example.org/a\\|b) |")

/-- Hard breaks whose two artifacts disagree today, each with the file that
owes the agreement. A run: HTML sets an empty line between two breaks, and
so does lualatex for `\\` twice — LaTeX's break sets `\null` after itself,
a box the next break's line keeps — while the PDF's line breaker discards
everything between two forced breaks and steps one baseline. A break that
opens its paragraph: HTML sets an empty first line, as CommonMark's
`<p><br />` means, while the PDF's line breaker discards a forced break with
nothing before it; LaTeX refuses that `\\` outright ("There's no line here
to end") and sets nothing. Read in both directions by `breakRunAgreeChecks`:
a row whose artifacts come to agree fails until it goes. -/
def breakRunDebt : List (String × String) :=
  [("markdown <br><br>", "LeanTex/Core/Layout.lean"),
   ("markdown backslash breaks", "LeanTex/Core/Layout.lean"),
   ("tex breaks", "LeanTex/Core/Layout.lean"),
   ("markdown leading <br>", "LeanTex/Core/Layout.lean"),
   ("markdown leading backslash break", "LeanTex/Core/Layout.lean"),
   ("tex leading break", "LeanTex/Core/Elab.lean, which keeps a break LaTeX refuses")]

/-- **Hard breaks set as many lines in both artifacts**, or their
disagreement is a `breakRunDebt` row. For a run, the HTML's line steps
between the two words are its `<br>`s and the PDF's the baseline distance
between them, counted in the distance one break sets. For a break that opens
its paragraph, the HTML sets an empty first line when the paragraph opens
with its `<br>`, and the PDF when its first word stands one break's distance
below where it stands without the break. -/
def breakRunAgreeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet
    | t "the break-run faces load" false
      return
  let yOf (doc : Ir.Doc) (w : String) : Option Int :=
    ((bodyLines (layoutOf fonts doc)).find? (fun l => hasStr (lineText l) w)).map (·.y)
  let gap (doc : Ir.Doc) : Nat :=
    match yOf doc "Alder", yOf doc "Birch" with
    | some a, some b => (b - a).natAbs
    | _, _ => 0
  let runs : List (String × Ir.Doc × Ir.Doc) :=
    [("markdown <br><br>", (elabMd "Alder<br><br>Birch\n").1, (elabMd "Alder<br>Birch\n").1),
     ("markdown backslash breaks", (elabMd "Alder\\\n\\\nBirch\n").1,
      (elabMd "Alder\\\nBirch\n").1),
     ("tex breaks", (elabStr "Alder\\\\\\\\Birch").1, (elabStr "Alder\\\\Birch").1)]
  for (label, two, one) in runs do
    let steps := ((docTreeOf two).splitOn "<br>").length - 1
    t s!"a run of breaks is measured on the page ({label})" (gap one > 0 && steps == 2)
    t s!"a run of breaks sets as many lines in both artifacts, or is recorded ({label})"
      ((gap two == steps * gap one) == !breakRunDebt.any (·.1 == label))
  let step := gap (elabMd "Alder<br>Birch\n").1
  let leads : List (String × Ir.Doc × Ir.Doc) :=
    [("markdown leading <br>", (elabMd "<br>Birch\n").1, (elabMd "Birch\n").1),
     ("markdown leading backslash break", (elabMd "\\\nBirch\n").1, (elabMd "Birch\n").1),
     ("tex leading break", (elabStr "\\\\Birch").1, (elabStr "Birch").1)]
  for (label, lead, bare) in leads do
    let pdfEmpty := match yOf lead "Birch", yOf bare "Birch" with
      | some a, some b => (a - b).natAbs == step
      | _, _ => false
    let htmlEmpty := hasStr (docTreeOf lead) "<p><br>Birch"
    t s!"a leading break is measured on the page ({label})"
      (step != 0 && (yOf lead "Birch").isSome && (yOf bare "Birch").isSome)
    t s!"a leading break sets as many lines in both artifacts, or is recorded ({label})"
      ((pdfEmpty == htmlEmpty) == !breakRunDebt.any (·.1 == label))
