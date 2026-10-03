import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! **What the markdown surface means, asserted over the artifact.**

Markdown has no semantics of its own here: its meaning is the desugaring
into the surface AST the one elaborator reads. So a claim about a markdown
construct is a claim about the typed HTML tree the backend emits, never
about the md AST or an IR dump — the four container-stack defects below all
produced a plausible IR and shipped nothing.

Each row is a regression floor: it names the invariant whose absence let the
defect through, and it failed before the fix. -/
mutual

/-- One node as its tag, attributes and text, flattened — with its closing
tag, so the string states *nesting* and not only presence. Without the
closing tags a row could only ask whether a tag appeared anywhere: the
weakest row here passed on the letter `h` occurring in the tree, while the
heading it was about shipped inside the list item above it. The accumulator
threads so the walk is linear. -/
def mdFlattenOne (acc : String) (n : Html.Node) : String :=
  match n with
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let as := attrs.foldl (fun s a => s ++ " " ++ a.1 ++ "=" ++ a.2) ""
    if Html.voidTags.contains tag then acc ++ "<" ++ tag ++ as ++ ">"
    else mdFlatten (acc ++ "<" ++ tag ++ as ++ ">") kids.toList ++ "</" ++ tag ++ ">"

def mdFlatten (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => mdFlatten (mdFlattenOne acc n) rest

end

/-- The tags and text a markdown source's page carries, in order: enough to
state what shipped and where, which is what every defect below was about. -/
def mdTreeOf (src : String) : String :=
  let (doc, _) := elabMd src
  let (_, body, _) := HtmlDoc.emitTree {} doc
  mdFlatten "" body.toList

mutual

/-- Every `<pre>` of a tree, in document order, the accumulator threaded. -/
def mdPresOne (acc : Array Html.Node) (n : Html.Node) : Array Html.Node :=
  match n with
  | .elem "pre" _ _ => acc.push n
  | .elem _ _ kids => mdPresList acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def mdPresList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => mdPresList (mdPresOne acc n) rest

end

/-- The attributes of an unconfigured fence's `<pre>`: the verbatim size,
leading and tab settings, and a tab stop so a keyboard can reach and scroll it
(`HtmlDoc.a11yFacts`). Named once, so a backend change fails the fence rows
at this line rather than at four literals. The exact attribute check also
rejects leaked language text or an attribute hiding the code. A bare fence
sets at the ambient size — the document base, `1em` — as LaTeX's `verbatim`
does (it selects the mono family and changes no size). -/
def mdCodeBlockPreAttrs : Array (String × String) :=
  #[("style", "font-size: 1em; line-height: 1.2; tab-size: 8;"), ("tabindex", "0")]

/-- The page's code blocks, in order, each as the one text its `<code>`
holds — when the block is exactly a `<pre>` carrying `mdCodeBlockPreAttrs`
whose only child is a `<code>` with no attribute holding one text node, and
`none` for any other shape: a node before or after the `<code>`, an
attribute leaked onto either element, content split or nested. A needle
anchored at `</code></pre>` passed a page whose every `<pre>` opened with
leaked text. -/
def mdCodeBlocks (src : String) : Array (Option String) :=
  let (doc, _) := elabMd src
  let (_, body, _) := HtmlDoc.emitTree {} doc
  (mdPresList #[] body.toList).map fun n =>
    match n with
    | .elem "pre" attrs #[.elem "code" cattrs #[.text s]] =>
      if attrs == mdCodeBlockPreAttrs && cattrs.isEmpty then some s else none
    | _ => none

/-- A generated family of documents that each end a list with a thematic
break and then carry on: container context × list marker × break spelling ×
nesting × a blank line or not × the block that follows. -/
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

/-- **Every block of the source reaches the page or a diagnostic.** A list
followed by a spaced thematic break kept its frame open with no item in it,
and everything after the break landed in the list's own accumulator, which
its close discarded: the rest of the document shipped nowhere, with no
diagnostic at all. So the statement is over a generated family, not one
case: in every document the family builds, every sentinel word ships, and
the break — the one block with no ink in this engine — is named by its
route at its own line. -/
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
  t s!"every block after a list and a thematic break ships or is named \
({bad.size} of {fam.size} documents fail; first: {bad.toList.take 3})" bad.isEmpty
  -- A setext underline is one run of `=` or `-`: with spaces inside it, the
  -- line under a paragraph is a thematic break (or text), never a heading.
  t "a spaced dash line under a paragraph is a break, not a heading"
    (has1 "Foo\n- - -\n" "<p>Foo</p>" && !has1 "Foo\n- - -\n" "<h")
  t "a spaced equals line under a paragraph is text, not a heading"
    (has1 "Foo\n= =\n" "= =" && !has1 "Foo\n= =\n" "<h")
  t "an unspaced dash line under a paragraph is still a heading"
    (has1 "Foo\n---\n" "<h3>Foo</h3>")
  t "a list, a thematic break and another list are three blocks"
    (has1 "* Foo\n* * *\n* Bar\n" "<ul><li>Foo</li></ul><ul><li>Bar</li></ul>")
where
  has1 (src needle : String) : Bool := hasStr (mdTreeOf src) needle

def mdSurfaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let tree := mdTreeOf
  let has (src needle : String) : Bool := hasStr (tree src) needle
  -- The reader reaches both backends through one elaborator: the surface
  -- the document was written in is invisible past the frontend.
  t "a markdown paragraph ships as a paragraph"
    (has "a paragraph\n\n" "<p>")
  t "emphasis, strong emphasis and a code span each reach their element"
    (has "*e* **s** `c`\n" "<em>" && has "*e* **s** `c`\n" "<strong>"
      && has "*e* **s** `c`\n" "<code>")
  t "a link keeps its destination"
    (has "[t](https://example.org)\n" "https://example.org")
  -- Defect: a sibling item whose container failed to match was read as a
  -- lazy continuation, so the second item of every ordered list that did
  -- not start at 1 raised E0390 and lost its text.
  t "a second ordered item is a sibling, not a lazy continuation"
    ((dvMd "1. one\n2. two\n").all (·.kind != .E0390))
  t "both ordered items ship"
    (has "1. one\n2. two\n" "one" && has "1. one\n2. two\n" "two")
  -- Defect: a marker of a different kind opened a list *inside* the open
  -- one, and the outer list then swallowed every following block.
  t "a bullet list and an ordered list after it are siblings"
    (has "- b\n\n1. o\n" "<ul>" && has "- b\n\n1. o\n" "<ol>")
  t "a block after a list still ships"
    (has "- b\n\n> q\n" "<blockquote>")
  t "a heading after a list still ships"
    (has "- b\n\n## h\n" "</ul><h3>h</h3>")
  -- Defect: a `---` line under a paragraph was read as a thematic break,
  -- which dropped the setext heading's title into the paragraph above.
  t "a dashed underline under a paragraph is a setext heading"
    (has "Foo\n---\n" "<h3>")
  t "an equals underline is a level-one setext heading"
    (has "Foo\n===\n" "<h2>")
  -- Defect: an indented line under an open paragraph was tested for block
  -- starts first, so `    # bar` became a heading instead of paragraph text.
  t "an indented line under a paragraph is continuation text"
    (has "foo\n    # bar\n" "# bar")
  -- The three strict classes, each refused with its own subject so the
  -- dialect decision is data. A class that stopped firing would pass a
  -- lint and change the dialect silently.
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
  -- A construct the surface AST cannot express is named, not dropped in
  -- silence: the routed items are a record of what the kernel owes. The
  -- code says whether its content reached the page — `W0307` only where
  -- nothing did.
  let routed (src subject : String) : Bool :=
    (dvMd src).any fun d => d.kind == .W0307 && d.subject == some subject
  t "a thematic break is routed by name"
    (routed "a\n\n***\n\nb\n" "md:thematic-break")
  -- An image's text alternative survives the trip, so the accessibility
  -- judge has nothing to report.
  t "an image's alt text reaches the page"
    (has "![the alt](/u)\n" "the alt")
  t "an image with alt text raises no missing-alternative warning"
    ((dvMd "![the alt](/u)\n").all (·.kind != .N0376))
  -- Text that would be a control sequence in tex is literal in markdown:
  -- the desugaring goes through `word`, never through generated source.
  t "a per cent sign in markdown text is not a comment"
    (has "50% of it\n" "50%")
  t "a dollar sign in markdown text is not mathematics"
    (has "it costs $5\n" "$5")
  t "a backslash escape leaves the character literal"
    (has "\\*not emph\\*\n" "*not emph*")
  -- Defect: a fenced leaf skipped container matching, so a fence inside a
  -- quote or an item never closed. The rest of the document — the closing
  -- fence, the paragraph, the heading — shipped as code, with no
  -- diagnostic, and the content kept its container's prefixes.
  let fence := "```"
  -- The whole code block, both sides of the `<code>`: exactly one `<pre>`
  -- on the page, whose only child is a `<code>` holding exactly `code`.
  let codeIs (src : String) : Bool := mdCodeBlocks src == #[some "code"]
  t "a fence inside a blockquote closes with its quote"
    (codeIs ("> a\n> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n\nafter\n\n## h\n"))
  t "a block after a quoted fence still ships"
    (has ("> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n\nafter\n\n## h\n")
      "</blockquote><p>after</p><h3>h</h3>")
  t "a quoted fence does not ship its quote marker as code"
    (!has ("> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n") "<code>> code")
  t "a fence inside a nested list item closes"
    (codeIs ("- a\n  - b\n    " ++ fence ++ "\n    code\n    " ++ fence ++ "\n- c\n\nlast\n"))
  t "a sibling item after a nested fence still ships"
    (has ("- a\n  - b\n    " ++ fence ++ "\n    code\n    " ++ fence ++ "\n- c\n\nlast\n")
      "</li></ul></li><li>c</li></ul><p>last</p>")
  t "a fence in a list item does not ship the item's indent as code"
    (codeIs ("- item\n\n  " ++ fence ++ "\n  code\n  " ++ fence ++ "\n"))
  -- Defect: the raw-HTML test fired on any `<` followed by a letter, so a
  -- valid autolink at the start of a line and text the spec reads literally
  -- failed the build. Only a complete tag (§6.6) is raw HTML.
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
  t "a comment is still refused"
    (refusedWith "<!-- c -->\n" "md:raw-html")
  -- Defect: a block-level refusal named column one of its line, so inside a
  -- quote it pointed at the `>` and a checker reading the refused text back
  -- from the source read the container prefix instead of the tag.
  t "a block refusal inside a quote names the tag's column"
    ((dvMd "> <div>x</div>\n").any fun d =>
      d.kind == .E0390 && (d.span.map (·.pos.col)) == some 3)
  -- Defect: a fenced block's info string was routed as unexpressible, but
  -- `Ir.ListingSpec.language` carries it and both artifacts project it. Six
  -- ledger rows read as `match` only because the comparison drops `class`.
  t "a fenced block's info string reaches the code element's class"
    (has ("" ++ fence ++ "ruby\nx = 1\n" ++ fence ++ "\n") "<code class=language-ruby>")
  t "only the info string's first word is the language"
    (has ("" ++ fence ++ "ruby startline=3\nx\n" ++ fence ++ "\n") "<code class=language-ruby>")
  t "a carried info string is no longer routed"
    ((dvMd ("" ++ fence ++ "ruby\nx\n" ++ fence ++ "\n")).all
      (fun d => d.subject != some "md:code-info"))
  -- Defect: link and image titles were destructured as `_` and dropped with
  -- no diagnostic at all. `Ir.Inline.link` has no title field, so the loss
  -- is real and takes a name.
  let degraded (src subject : String) : Bool :=
    (dvMd src).any fun d => d.kind == .W0392 && d.subject == some subject
  t "a dropped link title is named"
    (degraded "[a link](https://example.org \"the title\")\n" "md:link-title")
  t "a dropped image title is named"
    (degraded "![alt](/u.png \"img title\")\n" "md:image-title")
  t "a link with no title raises nothing"
    ((dvMd "[a link](https://example.org)\n").all (·.kind != .W0392))
  -- An alt value carrying a comma or an equals sign rides a braced group,
  -- so it survives the option split instead of being routed.
  t "an alt value carrying a comma reaches the page whole"
    (has "![alt, with=comma](/u.png)\n" "alt, with=comma")
  -- The loss class a route takes is decided by what reaches the page, which
  -- is the registry's rule: `pending` (floor absent) only where nothing
  -- ships, `degraded` (floor content) where the construct ships diminished.
  t "a thematic break, which ships nothing, is pending"
    (routed "a\n\n***\n\nb\n" "md:thematic-break")
  t "a heading below the third level, which ships, is degraded"
    (degraded "#### h\n" "md:heading-depth")
  t "a loose list, which ships, is degraded"
    (degraded "- a\n\n- b\n" "md:loose-list")
  t "an ordered list's start number, whose list ships, is degraded"
    (degraded "3. three\n4. four\n" "md:list-start")
  t "no md route still claims a shipping construct is absent"
    ((dvMd "#### h\n\n[a](u \"t\")\n").all (·.kind != .W0307))
  -- Defect: the container loop opened a list item before the thematic-break
  -- test ran, so `* * *` and `- - -` became three nested empty lists.
  t "a starred thematic break is a break, not three nested lists"
    (!has "a\n\n* * *\n\nb\n" "<ul>")
  t "a dashed thematic break is a break, not three nested lists"
    (!has "a\n\n- - -\n\nb\n" "<ul>")
  t "a starred thematic break routes its own construct"
    (routed "a\n\n* * *\n\nb\n" "md:thematic-break")
  t "the blocks either side of a thematic break still ship"
    (has "a\n\n* * *\n\nb\n" "<p>a</p><p>b</p>")
  -- Defect: the spaces after a marker were counted from the second one, so
  -- five of them read as one and `-     foo` set its content as item text
  -- where the strict dialect owes an indented-code refusal.
  t "five spaces after a marker is indented code inside the item"
    (refusedWith "-     foo\n" "md:indented-code")
  t "one space after a marker is ordinary item content"
    (has "- foo\n" "<li>foo</li>")
  t "three spaces after a marker is still item content"
    (has "-   foo\n" "<li>foo</li>")
  -- Defect: an empty remainder after the markers opened an empty paragraph,
  -- and the next unmarked line was then refused as a lazy continuation of
  -- it. The marker line opens nothing.
  t "an empty item's content is not a lazy continuation"
    ((dvMd "-   \n  foo\n").all (·.kind != .E0390))
  t "an empty item's content ships as its item"
    (has "-   \n  foo\n" "<ul><li>foo</li></ul>")
  t "a quote marker alone does not open an empty paragraph"
    ((dvMd "> \n> quoted\n").all (·.kind != .E0390))
  -- Defect: the openers-bottom floor was one per delimiter shape for the
  -- whole paragraph, while the search skipped openers in another bracket
  -- region, so a closer inside a link that found no partner raised the
  -- floor above a valid opener outside it. Each row fails on that reader.
  t "emphasis around a link pairs across it"
    (has "*a [b*](c) d*\n" "<em>a <a" && has "*a [b*](c) d*\n" ">b*</a> d</em>")
  t "underscore emphasis around a link pairs across it"
    (has "_a [b_](c) d_\n" "<em>a <a" && has "_a [b_](c) d_\n" ">b_</a> d</em>")
  t "emphasis around an image pairs across it"
    (has "*a ![b*](c) d*\n" "<em>a <img" && has "*a ![b*](c) d*\n" " d</em>")
  t "strong emphasis around a link pairs across it"
    (has "**a [b**](c) d**\n" "<strong>a <a" && has "**a [b**](c) d**\n" ">b**</a> d</strong>")
  -- Defect: a match left the delimiters between opener and closer on the
  -- stack, so a later closer paired across the match and built crossing
  -- emphasis.
  t "a match removes the delimiters between its pair"
    (has "*foo _bar* baz_\n" "<em>foo _bar</em> baz_")
  t "a strong pair inside emphasis keeps the stray delimiter literal"
    (has "*foo __bar *baz bim__ bam*\n" "<em>foo <strong>bar *baz bim</strong> bam</em>")
  -- Defect: regions were filled pair by pair, so an image's region
  -- overwrote the link inside it and a delimiter in the link paired with
  -- one in the image text around it.
  t "a delimiter inside a link does not pair with one in the image around it"
    (has "![*a [b*](c)](d)\n" "alt=*a b*" && !has "![*a [b*](c)](d)\n" "<em>")
  t "a delimiter inside link text does not pair with one outside it"
    (has "*[foo*](/url)\n" "*<a" && has "*[foo*](/url)\n" ">foo*</a>")
  -- Defect: a closed link deactivated every open bracket, images included,
  -- so an image whose text held a link never formed.
  t "an image's opener stays active across a link inside it"
    (has "![[a](b)](c)\n" "<img" && has "![[a](b)](c)\n" "alt=a")
  t "a link's opener goes inactive across a link inside it"
    (has "[[a](b)](c)\n" "[<a" && has "[[a](b)](c)\n" "</a>](c)")
  -- Defect: the info string was spliced into `{lstlisting}`'s option head
  -- and the alternative into `\includegraphics`'s, both re-read by the
  -- elaborator, so reader text crossed into another grammar: a `]` ended
  -- the head and leaked into the code, a `,` switched on options, a brace
  -- shipped `[language={r,]` as the code's first line.
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
      && has (fence ++ "{r, echo=FALSE}\nx <- 1\n" ++ fence ++ "\n") "<code>x <- 1</code>")
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
  t "an alternative no option spelling carries is named, and still ships"
    ((dvMd "![a } , \" b , c](u.png)\n").any
        (fun d => d.kind == .W0392 && d.subject == some "md:image-alt")
      && has "![a } , \" b , c](u.png)\n" "alt=a } , \u201d b , c>")
  t "a double quote an option spelling does carry is not named"
    ((dvMd "![a } , \" b](u.png)\n").all (fun d => d.subject != some "md:image-alt")
      && has "![a } , \" b](u.png)\n" "alt=a } , \" b>")
  let puncts := "!#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList
  let altLost := puncts.filter fun c =>
    let src := "![x\\" ++ String.singleton c ++ "y, z=w](u.png)\n"
    !(has src ("alt=x" ++ String.singleton c ++ "y, z=w>") && noLeak src)
  t s!"every ASCII punctuation character but the quote reaches an alternative whole \
(lost: {altLost})" altLost.isEmpty
  -- Defect: a strict refusal named the wrong class, or a second class the
  -- case never exercised. Each refusal is a claim the reviewed list is
  -- checked against, so a wrong subject is a wrong verdict.
  let subjects (src : String) : List String :=
    ((dvMd src).filter (·.kind == .E0390)).toList.filterMap (·.subject) |>.eraseDups
  t "a line indented four columns under a quoted paragraph is lazy, not indented code"
    (subjects "> foo\n    - bar\n" == ["md:lazy-continuation"])
  t "a marker indented past the item's column is lazy, not indented code"
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
  -- `<!-->` and `<!--->` are complete comments (0.31.2); searched for from
  -- the fourth character, `<!-->` read as the start of an unclosed one.
  t "the shortest comment is a complete raw-HTML construct"
    (refusedWith "a <!--> b\n" "md:raw-html")
  -- A bare destination nests parentheses at most 32 deep (cmark's limit;
  -- the spec asks for at least three), which is what bounds each scan.
  let deep (k : Nat) : String :=
    "[a](" ++ String.ofList (List.replicate k '(') ++ "x"
      ++ String.ofList (List.replicate k ')') ++ ")\n"
  t "a destination nested 32 deep is a link, 33 deep is text"
    (has (deep 32) "<a " && !has (deep 33) "<a ")
  mdAccountsChecks t
