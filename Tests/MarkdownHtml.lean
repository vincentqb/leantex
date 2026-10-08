import Tests.Support

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
  t "supported disclosures compile and name their lost collapse behaviour"
    (!refused disclosure
      && ((dvMd disclosure).filter fun d =>
        d.kind == .W0392 && d.subject == some "md:disclosure").size == 1)
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
      && ((dvMd nested).filter (·.subject == some "md:disclosure")).size == 2)
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
  for attrs in ["open", "hidden", "aria-hidden=\"true\"", "role=\"none\"",
      "lang=\"de\"", "style=\"display:none\"", "onclick=\"evil()\""] do
    for src in [
        s!"<details {attrs}>\n<summary>Amber</summary>\nCedar\n</details>\n",
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
