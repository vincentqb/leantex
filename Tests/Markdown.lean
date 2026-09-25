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

/-- One node as its tag and text, flattened. The accumulator threads so the
walk is linear. -/
def mdFlattenOne (acc : String) (n : Html.Node) : String :=
  match n with
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let as := attrs.foldl (fun s a => s ++ " " ++ a.1 ++ "=" ++ a.2) ""
    mdFlatten (acc ++ "<" ++ tag ++ as ++ ">") kids.toList

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
    (has "- b\n\n## h\n" "h")
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
  -- silence: the routed items are a record of what the kernel owes.
  let routed (src subject : String) : Bool :=
    (dvMd src).any fun d => d.kind == .W0307 && d.subject == some subject
  t "a thematic break is routed by name"
    (routed "a\n\n***\n\nb\n" "md:thematic-break")
  t "a heading below the third level is routed by name"
    (routed "#### h\n" "md:heading-depth")
  t "a fenced block's info string is routed by name"
    (routed "```ruby\nx\n```\n" "md:code-info")
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
