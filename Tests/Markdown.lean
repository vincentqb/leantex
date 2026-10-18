module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! What the markdown surface means, asserted over the emitted HTML tree. -/

/-- Documents that end a list with a thematic break and carry on, over container, marker, break
spelling, nesting, blank line and following block. -/
def mdBreakFamily : Array (String × Nat × List String) := Id.run do
  let afters : List (List String × List String) :=
    [(["zulu after"], ["zulu"]), (["## yankee heading"], ["yankee"]),
     (["> xray quoted"], ["xray"]), (["- whiskey item"], ["whiskey"]),
     (["1. victor item"], ["victor"]), (["```", "uniform code", "```"], ["uniform"])]
  let mut out : Array (String × Nat × List String) := #[]
  for pre in ["", "> "] do
    for mk in ["- ", "* ", "+ ", "1. ", "1) "] do
      for brk in ["***", "* * *", "- - -", "---", "___", "_ _ _", " * * *", "-  -  -"] do
        for nested in [false, true] do
          for gap in [false, true] do
            for (after, words) in afters do
              let mut lines : Array String := #[pre ++ mk ++ "alpha"]
              let mut want : List String := ["alpha"] ++ words
              if nested then
                lines := lines.push (pre ++ String.ofList (List.replicate mk.length ' ')
                  ++ mk ++ "bravo")
                want := "bravo" :: want
              if gap then lines := lines.push pre.trimAsciiEnd.toString
              lines := lines.push (pre ++ brk)
              let brkLine := lines.size
              for a in after do lines := lines.push (pre ++ a)
              out := out.push (String.intercalate "\n" lines.toList ++ "\n", brkLine, want)
  return out

/-- Every block of the source reaches the page or a diagnostic. -/
def mdAccountsChecks (t : String → Bool → IO Unit) : IO Unit := do
  let fam := mdBreakFamily
  let mut bad : Array String := #[]
  for (src, brkLine, words) in fam do
    let tree := mdTreeOf src
    let lost := words.filter (!hasStr tree ·)
    let named := (dvMd src).any fun d =>
      d.kind == .W0307 && d.subject == some "md:thematic-break"
        && (d.span.map (·.pos.line)) == some brkLine
    unless lost.isEmpty && named do
      bad := bad.push s!"{src.replace "\n" "⏎"} lost {lost} named {named}"
  t s!"every block after a list and a thematic break ships or is named ({bad.size} of {fam.size} documents fail; first: {bad.toList.take 3})" bad.isEmpty
  t "a spaced dash line under a paragraph is a break, not a heading"
    (has1 "Foo\n- - -\n" "<p>Foo</p>" && !has1 "Foo\n- - -\n" "<h")
  t "a spaced equals line under a paragraph is text, not a heading"
    (has1 "Foo\n= =\n" "= =" && !has1 "Foo\n= =\n" "<h")
  t "an unspaced dash line under a paragraph is still a heading"
    (has1 "Foo\n---\n" "<h2>Foo</h2>")
  t "a list, a thematic break and another list are three blocks"
    (has1 "* Foo\n* * *\n* Bar\n" "<ul><li>Foo</li></ul><ul><li>Bar</li></ul>")
where
  has1 (src needle : String) : Bool := hasStr (mdTreeOf src) needle

def mdSurfaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let tree := mdTreeOf
  let has (src needle : String) : Bool := hasStr (tree src) needle
  t "a markdown paragraph ships as a paragraph"
    (has "a paragraph\n\n" "<p>")
  t "emphasis, strong emphasis and a code span reach their elements"
    (has "*e* **s** `c`\n" "<em>" && has "*e* **s** `c`\n" "<strong>"
      && has "*e* **s** `c`\n" "<code>")
  t "a link keeps its destination"
    (has "[t](https://example.org)\n" "https://example.org")
  t "a second ordered item is a sibling, not a lazy continuation"
    ((dvMd "1. one\n2. two\n").all (·.kind != .E0390))
  t "both ordered items ship"
    (has "1. one\n2. two\n" "one" && has "1. one\n2. two\n" "two")
  t "a bullet list and an ordered list after it are siblings"
    (has "- b\n\n1. o\n" "<ul>" && has "- b\n\n1. o\n" "<ol>")
  t "a block after a list still ships"
    (has "- b\n\n> q\n" "<blockquote>")
  t "a heading after a list still ships"
    (has "- b\n\n## h\n" "</ul><section id=h><h2>h</h2></section>")
  t "a dashed underline under a paragraph is a setext heading"
    (has "Foo\n---\n" "<h2>")
  t "an equals underline is a level-one setext heading"
    (has "Foo\n===\n" "<h1 class=body-heading>Foo</h1>")
  t "an indented line under a paragraph is continuation text"
    (has "foo\n    # bar\n" "# bar")
  let refusedWith (src subject : String) : Bool :=
    (dvMd src).any fun d => d.kind == .E0390 && d.subject == some subject
  t "raw HTML is refused, naming its class"
    (refusedWith "<div>x</div>\n" "md:raw-html")
  t "an indented code block is refused, naming its class"
    (refusedWith "    code\n" "md:indented-code")
  t "a lazy continuation is refused, naming its class"
    (refusedWith "> quoted\nlazy\n" "md:lazy-continuation")
  t "every refusal carries a fix-it"
    (((dvMd "<div>x</div>\n").filter (·.kind == .E0390)).all (·.help.isSome))
  let routed (src subject : String) : Bool :=
    (dvMd src).any fun d => d.kind == .W0307 && d.subject == some subject
  t "a thematic break is routed by name"
    (routed "a\n\n***\n\nb\n" "md:thematic-break")
  t "an image's alt text reaches the page"
    (has "![the alt](/u)\n" "the alt")
  t "an image with alt text raises no missing-alternative warning"
    ((dvMd "![the alt](/u)\n").all (·.kind != .N0376))
  t "a per cent sign in markdown text is not a comment"
    (has "50% of it\n" "50%")
  t "a dollar sign in markdown text is not mathematics"
    (has "it costs $5\n" "$5")
  t "a backslash escape leaves the character literal"
    (has "\\*not emph\\*\n" "*not emph*")
  let fence := "```"
  let codeIs (src : String) : Bool := mdCodeBlocks src == #[some "code"]
  t "a fence inside a blockquote closes with its quote"
    (codeIs ("> a\n> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n\nafter\n\n## h\n"))
  t "a block after a quoted fence still ships"
    (has ("> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n\nafter\n\n## h\n")
      "</blockquote><p>after</p><section id=h><h2>h</h2></section>")
  t "a quoted fence does not ship its quote marker as code"
    (!has ("> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n") "<code>> code")
  t "a fence inside a nested list item closes"
    (codeIs ("- a\n  - b\n    " ++ fence ++ "\n    code\n    " ++ fence ++ "\n- c\n\nlast\n"))
  t "a sibling item after a nested fence still ships"
    (has ("- a\n  - b\n    " ++ fence ++ "\n    code\n    " ++ fence ++ "\n- c\n\nlast\n")
      "</li></ul></li><li>c</li></ul><p>last</p>")
  t "a fence in a list item does not ship the item's indent as code"
    (codeIs ("- item\n\n  " ++ fence ++ "\n  code\n  " ++ fence ++ "\n"))
  t "an autolink at the start of a line is not refused"
    ((dvMd "<https://example.org> is the site.\n").all (·.kind != .E0390))
  t "an autolink at the start of a line reaches the page"
    (has "<https://example.org> is the site.\n" "https://example.org")
  t "a less-than before a word is literal text, not a tag"
    ((dvMd "use x <y for comparison and more text\n").all (·.kind != .E0390))
  t "an ill-formed attribute name makes the text literal"
    ((dvMd "<a h*#ref=\"hi\">\n").all (·.kind != .E0390))
  t "a complete tag is still refused"
    (refusedWith "<span>x</span> in a line\n" "md:raw-html")
  t "a comment consumes no visible content and needs no refusal"
    ((dvMd "<!-- c -->\n").all (·.kind != .E0390)
      && mdTreeOf "<!-- c -->\n" == mdTreeOf "")
  t "a comment ended early by `--!>` cannot hide visible content"
    (refusedWith "Amber<!-- hidden --!>Willow<!-- tail -->Cedar\n" "md:raw-html"
      && refusedWith "<!-- hidden\n--!>Willow\n" "md:raw-html")
  t "a block refusal inside a quote names the tag's column"
    ((dvMd "> <div>x</div>\n").any fun d =>
      d.kind == .E0390 && (d.span.map (·.pos.col)) == some 3)
  t "a fenced block's info string reaches the code element's class"
    (has ("" ++ fence ++ "ruby\nx = 1\n" ++ fence ++ "\n") "<code class=language-ruby>")
  t "only the info string's first word is the language"
    (has ("" ++ fence ++ "ruby startline=3\nx\n" ++ fence ++ "\n") "<code class=language-ruby>")
  t "a carried info string is not routed"
    ((dvMd ("" ++ fence ++ "ruby\nx\n" ++ fence ++ "\n")).all
      (fun d => d.subject != some "md:code-info"))
  let degraded (src subject : String) : Bool :=
    (dvMd src).any fun d => d.kind == .W0392 && d.subject == some subject
  t "a dropped link title is named"
    (degraded "[a link](https://example.org \"the title\")\n" "md:link-title")
  t "a dropped image title is named"
    (degraded "![alt](/u.png \"img title\")\n" "md:image-title")
  t "a link with no title raises nothing"
    ((dvMd "[a link](https://example.org)\n").all (·.kind != .W0392))
  t "an alt value carrying a comma reaches the page whole"
    (has "![alt, with=comma](/u.png)\n" "alt, with=comma")
  t "a thematic break, which ships nothing, is pending"
    (routed "a\n\n***\n\nb\n" "md:thematic-break")
  t "a fourth-level heading ships at its declared rank without a loss"
    (has "#### h\n" "<h4>h</h4>"
      && !(dvMd "#### h\n").any (·.subject == some "md:heading-depth"))
  t "a loose list, which ships, is degraded"
    (degraded "- a\n\n- b\n" "md:loose-list")
  t "an ordered list's start number, whose list ships, is degraded"
    (degraded "3. three\n4. four\n" "md:list-start")
  t "no md route claims a shipping construct is absent"
    ((dvMd "#### h\n\n[a](u \"t\")\n").all (·.kind != .W0307))
  t "a starred thematic break is a break, not three nested lists"
    (!has "a\n\n* * *\n\nb\n" "<ul>")
  t "a dashed thematic break is a break, not three nested lists"
    (!has "a\n\n- - -\n\nb\n" "<ul>")
  t "a starred thematic break routes its own construct"
    (routed "a\n\n* * *\n\nb\n" "md:thematic-break")
  t "the blocks either side of a thematic break still ship"
    (has "a\n\n* * *\n\nb\n" "<p>a</p><p>b</p>")
  t "five spaces after a marker is indented code inside the item"
    (refusedWith "-     foo\n" "md:indented-code")
  t "one space after a marker is ordinary item content"
    (has "- foo\n" "<li>foo</li>")
  t "three spaces after a marker is still item content"
    (has "-   foo\n" "<li>foo</li>")
  t "an empty item's content is not a lazy continuation"
    ((dvMd "-   \n  foo\n").all (·.kind != .E0390))
  t "an empty item's content ships as its item"
    (has "-   \n  foo\n" "<ul><li>foo</li></ul>")
  t "a quote marker alone does not open an empty paragraph"
    ((dvMd "> \n> quoted\n").all (·.kind != .E0390))
  t "emphasis around a link pairs across it"
    (has "*a [b*](c) d*\n" "<em>a <a" && has "*a [b*](c) d*\n" ">b*</a> d</em>")
  t "underscore emphasis around a link pairs across it"
    (has "_a [b_](c) d_\n" "<em>a <a" && has "_a [b_](c) d_\n" ">b_</a> d</em>")
  t "emphasis around an image pairs across it"
    (has "*a ![b*](c) d*\n" "<em>a <img" && has "*a ![b*](c) d*\n" " d</em>")
  t "strong emphasis around a link pairs across it"
    (has "**a [b**](c) d**\n" "<strong>a <a" && has "**a [b**](c) d**\n" ">b**</a> d</strong>")
  t "a match removes the delimiters between its pair"
    (has "*foo _bar* baz_\n" "<em>foo _bar</em> baz_")
  t "a strong pair inside emphasis keeps the stray delimiter literal"
    (has "*foo __bar *baz bim__ bam*\n" "<em>foo <strong>bar *baz bim</strong> bam</em>")
  t "a link's delimiter does not pair with one in its enclosing image"
    (has "![*a [b*](c)](d)\n" "alt=*a b*" && !has "![*a [b*](c)](d)\n" "<em>")
  t "a delimiter inside link text does not pair with one outside it"
    (has "*[foo*](/url)\n" "*<a" && has "*[foo*](/url)\n" ">foo*</a>")
  t "an image's opener stays active across a link inside it"
    (has "![[a](b)](c)\n" "<img" && has "![[a](b)](c)\n" "alt=a")
  t "a link's opener goes inactive across a link inside it"
    (has "[[a](b)](c)\n" "[<a" && has "[[a](b)](c)\n" "</a>](c)")
  let codeInfo (src : String) : Bool :=
    (dvMd src).any fun d => d.kind == .W0392 && d.subject == some "md:code-info"
  let noLeak (src : String) : Bool := (dvMd src).all (·.kind != .W0110)
  t "a bracket in an info string does not leak into the code"
    (codeIs (fence ++ "a]b\ncode\n" ++ fence ++ "\n")
      && codeInfo (fence ++ "a]b\ncode\n" ++ fence ++ "\n"))
  t "text after a bracket in an info string does not reach the page"
    (!has (fence ++ "x]leaked text\ncode\n" ++ fence ++ "\n") "leaked")
  t "a comma in an info string switches on no listing option"
    (!has (fence ++ "python,numbers=left\ncode\n" ++ fence ++ "\n") "numbered"
      && codeInfo (fence ++ "python,numbers=left\ncode\n" ++ fence ++ "\n"))
  t "a chunk header's braces do not ship as the code's first line"
    (!has (fence ++ "{r, echo=FALSE}\nx <- 1\n" ++ fence ++ "\n") "[language"
      && mdCodeBlocks (fence ++ "{r, echo=FALSE}\nx <- 1\n" ++ fence ++ "\n") == #[some "x <- 1"])
  t "a lone brace for an info string does not ship as code"
    (!has (fence ++ "{\ncode line\n" ++ fence ++ "\n") "[language")
  t "the info string's first word ends at a tab"
    (has (fence ++ "ruby\tx\ncode\n" ++ fence ++ "\n") "<code class=language-ruby>")
  t "a backslash escape in an info string is resolved"
    (has (fence ++ "foo\\+bar\nfoo\n" ++ fence ++ "\n") "class=language-foo+bar")
  t "an info word outside the language grammar is named, not dropped"
    (codeInfo (fence ++ "f&ouml;&ouml;\nfoo\n" ++ fence ++ "\n"))
  t "no fenced block raises an unmodelled listing option"
    ([fence ++ "a]b\nc\n" ++ fence, fence ++ "{r, echo=FALSE}\nc\n" ++ fence,
      fence ++ "python,numbers=left\nc\n" ++ fence, fence ++ "ruby\tx\nc\n" ++ fence,
      fence ++ "f&ouml;\nc\n" ++ fence, fence ++ "{\nc\n" ++ fence].all (noLeak ·))
  t "a bracket and a comma in an alternative reach the page whole"
    (has "![a\\]b, c=d](u.png)\n" "alt=a]b, c=d>" && noLeak "![a\\]b, c=d](u.png)\n")
  t "a closing brace in an alternative reaches the page whole"
    (has "![a}, b](u.png)\n" "alt=a}, b>" && noLeak "![a}, b](u.png)\n")
  t "balanced double quotes in an alternative reach the page whole"
    (has "![say \"hi\" now](u.png)\n" "alt=say \"hi\" now>")
  t "an alternative with a lone quote, a brace and commas reaches the page whole, unnamed"
    ((dvMd "![a } , \" b , c](u.png)\n").all (fun d => d.subject != some "md:image-alt")
      && has "![a } , \" b , c](u.png)\n" "alt=a } , \" b , c>")
  t "a double quote an option spelling does carry is not named"
    ((dvMd "![a } , \" b](u.png)\n").all (fun d => d.subject != some "md:image-alt")
      && has "![a } , \" b](u.png)\n" "alt=a } , \" b>")
  let puncts := "!#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList
  let altLost := puncts.filter fun c =>
    let src := "![x\\" ++ String.singleton c ++ "y, z=w](u.png)\n"
    !(has src ("alt=x" ++ String.singleton c ++ "y, z=w>") && noLeak src)
  t s!"every ASCII punctuation character but the quote reaches an alternative whole (lost: {altLost})" altLost.isEmpty
  let subjects (src : String) : List String :=
    ((dvMd src).filter (·.kind == .E0390)).toList.filterMap (·.subject) |>.eraseDups
  t "a four-column indent under a quoted paragraph is lazy, not code"
    (subjects "> foo\n    - bar\n" == ["md:lazy-continuation"])
  t "a marker past the item's column is lazy, not indented code"
    (subjects "- a\n - b\n  - c\n   - d\n    - e\n" == ["md:lazy-continuation"])
  t "a lazy line is refused once, not again as a block of its own"
    (subjects "  1.  A paragraph\n    with two lines.\n" == ["md:lazy-continuation"])
  t "a lazy line leaves its container open"
    (((tree "> a\nlazy\n> b\n").splitOn "<blockquote>").length == 2)
  t "an HTML block's lines are not read again as markdown"
    (subjects "<table>\n  <tr>\n    <td>\n           hi\n    </td>\n  </tr>\n</table>\n\nokay.\n"
      == ["md:raw-html"]
      && has "<table>\n  <tr>\n    <td>\n           hi\n    </td>\n  </tr>\n</table>\n\nokay.\n"
        "<p>okay.</p>")
  t "a CDATA block runs to its end marker"
    (subjects "<![CDATA[\nf(a,b)\n{\n    return 1;\n}\n]]>\nokay\n" == ["md:raw-html"]
      && !has "<![CDATA[\nf(a,b)\n{\n    return 1;\n}\n]]>\nokay\n" "return"
      && has "<![CDATA[\nf(a,b)\n{\n    return 1;\n}\n]]>\nokay\n" "<p>okay</p>")
  t "an HTML block is refused once, not once per line"
    (((dvMd "<div>\n<div>\n</div>\n</div>\n").filter (·.kind == .E0390)).size == 1)
  t "a tag that may not interrupt a paragraph stays inside it"
    (!has "para\n<custom-tag>\nmore text\n" "</p><p>more")
  t "the shortest comment is complete and invisible"
    ((dvMd "a <!--> b\n").all (·.kind != .E0390)
      && has "a <!--> b\n" "<p>a b</p>")
  -- cmark nests a bare destination's parentheses at most 32 deep.
  let deep (k : Nat) : String :=
    "[a](" ++ String.ofList (List.replicate k '(') ++ "x"
      ++ String.ofList (List.replicate k ')') ++ ")\n"
  t "a destination nested 32 deep is a link, 33 deep is text"
    (has (deep 32) "<a " && !has (deep 33) "<a ")
  mdAccountsChecks t
