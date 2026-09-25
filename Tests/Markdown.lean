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
    ((dvMd "![the alt](/u)\n").all (·.kind != .W0376))
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
  t "a fence inside a blockquote closes with its quote"
    (has ("> a\n> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n\nafter\n\n## h\n")
      "<pre><code>code</code></pre>")
  t "a block after a quoted fence still ships"
    (has ("> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n\nafter\n\n## h\n")
      "</blockquote><p>after</p><h3>h</h3>")
  t "a quoted fence does not ship its quote marker as code"
    (!has ("> " ++ fence ++ "\n> code\n> " ++ fence ++ "\n") "<code>> code")
  t "a fence inside a nested list item closes"
    (has ("- a\n  - b\n    " ++ fence ++ "\n    code\n    " ++ fence ++ "\n- c\n\nlast\n")
      "<pre><code>code</code></pre>")
  t "a sibling item after a nested fence still ships"
    (has ("- a\n  - b\n    " ++ fence ++ "\n    code\n    " ++ fence ++ "\n- c\n\nlast\n")
      "</li></ul></li><li>c</li></ul><p>last</p>")
  t "a fence in a list item does not ship the item's indent as code"
    (has ("- item\n\n  " ++ fence ++ "\n  code\n  " ++ fence ++ "\n")
      "<pre><code>code</code></pre>")
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
