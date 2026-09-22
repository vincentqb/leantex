import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The kinds of a node array's top level, in order: the shape a
break-once check reads. -/
def structKinds (ns : Array Struct.Node) : Array Struct.Kind :=
  ns.filterMap fun n => match n with
    | .node k _ => some k
    | .leaf _ _ => none

/-- The children of the first node, when the array opens with one. -/
def structKids (ns : Array Struct.Node) : Array Struct.Node :=
  match ns[0]? with
  | some (Struct.Node.node _ kids) => kids
  | _ => #[]

def structTexts (ns : Array Struct.Node) : Array String :=
  (Struct.leaves ns).map fun (_, l) => l.census

/-- The structure tree: one backend-neutral projection of the IR, held to
the IR's own censuses. The theorems (`structTree_text`, `_headings_covers`,
`_images_covers`, `_leaves_id`) close in Struct.lean; the rows here are
their executable witnesses over every golden fixture, and one break-once
check per major arm — the tree a backend will read must classify each IR
constructor the way this file says, and a reclassified arm fails here by
name. -/
def structChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- the theorems, witnessed over the corpus (ir tier: the tree is an IR
  -- projection, and these compare two IR readings, never a page)
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let tree := Struct.ofDoc doc
    t s!"struct {n}: leaf text is blocksText" (tree.text == Ir.blocksText doc.body)
    t s!"struct {n}: headings are headingLevels" (tree.headings == Ir.headingLevels doc.body)
    t s!"struct {n}: images are the fold's census" (tree.images == Struct.irImages doc.body)
    let ids := tree.leaves.map (·.1)
    t s!"struct {n}: leaf ids are the preorder index" (ids == Array.range ids.size)
    -- a fixture that ships text has a tree with leaves to attribute it to
    t s!"struct {n}: text implies leaves"
      ((Ir.blocksText doc.body).isEmpty || !tree.leaves.isEmpty)

  -- block arms, one each
  let para : Ir.Block := .para #[.text "one"]
  let tree1 := Struct.ofBlocks #[para]
  t "para is a paragraph over one text leaf"
    (structKinds tree1 == #[.paragraph] && structTexts tree1 == #[ "one" ])
  let sec := Struct.ofBlocks #[.section 2 false (some "1.1") #[.text "Heading"]]
  t "section is a heading at its level, the number generated"
    (structKinds sec == #[.heading 2] && structTexts sec == #["Heading"])
  let lst := Struct.ofBlocks #[.list true #[#[para], #[para]]]
  t "list is list/item/label/body"
    (structKinds lst == #[.list true]
      && structKinds (structKids lst) == #[.item, .item]
      && structKinds (structKids (structKids lst)) == #[.label, .body])
  t "quote is a quote" (structKinds (Struct.ofBlocks #[.quote #[para]]) == #[.quote])
  t "abstract is a section" (structKinds (Struct.ofBlocks #[.abstract #[para]]) == #[.section])
  let titled := Struct.ofBlocks #[.titled .block #[.text "T"] #[para]]
  t "titled block is a section opening with its title"
    (structKinds titled == #[.section] && structKinds (structKids titled) == #[.title, .paragraph])
  t "an untitled block invents no title node"
    (structKinds (structKids (Struct.ofBlocks #[.titled .block #[] #[para]])) == #[.paragraph])
  let eq := Struct.ofBlocks #[.equation "(1)" #[.formula true "x" (Math.MList.ofList [])]]
  t "equation is a formula whose number is a label leaf after the content"
    (structKinds eq == #[.formula] && structKinds (structKids eq) == #[.formula, .label]
      && structTexts eq == #["x", "(1)"])
  let code := Struct.ofBlocks #[.verbatim none "let x" {}]
  t "verbatim is code over one leaf" (structKinds code == #[.code] && structTexts code == #["let x"])
  let listing := Struct.ofBlocks #[.verbatim none "let x" { caption := some (1, #[.text "Cap"]) }]
  t "a captioned listing is a figure: caption then code"
    (structKinds listing == #[.figure] && structKinds (structKids listing) == #[.caption, .code]
      && structTexts listing == #["Cap", "let x"])
  let alg := Struct.ofBlocks #[.algorithm false true
    #[{ depth := 0, kind := .statement, content := #[.text "a"], comment := some #[.text "c"] }]]
  t "algorithm is code, content then comment"
    (structKinds alg == #[.code] && structTexts alg == #["a", "c"])
  t "speaker note is an aside" (structKinds (Struct.ofBlocks #[.note #[para]]) == #[.aside])
  t "nav is a landmark" (structKinds (Struct.ofBlocks #[.nav {} #[para]]) == #[.nav])
  let frame := Struct.ofBlocks #[.frame #[.text "F"] false .center false #[para]]
  t "frame is a section opening with its title"
    (structKinds frame == #[.section] && structKinds (structKids frame) == #[.title, .paragraph])
  t "logo and framefoot are artifacts"
    (structKinds (Struct.ofBlocks #[.logo #[.text "l"], .framefoot #[.text "f"]])
      == #[.artifact, .artifact])
  let pic := Struct.ofBlocks #[.picture {}]
  t "picture is a figure over a picture leaf"
    (structKinds pic == #[.figure] && (Struct.leaves pic).map (·.2) == #[.picture])
  let tbl := Struct.ofBlocks #[.table #[] true true #[#[#[.text "a"], #[.text "b"]]] #[]]
  t "table is table/row/cell"
    (structKinds tbl == #[.table] && structKinds (structKids tbl) == #[.row]
      && structKinds (structKids (structKids tbl)) == #[.cell, .cell]
      && structTexts tbl == #["a", "b"])
  let fl := Struct.ofBlocks #[.float .figure (some 1) false #[para] #[.text "Cap"]]
  t "float is a figure, its caption first whatever capAbove says"
    (structKinds fl == #[.figure] && structKinds (structKids fl) == #[.caption, .paragraph]
      && structTexts fl == #["Cap", "one"])
  t "a bare float invents no caption"
    (structKinds (structKids (Struct.ofBlocks #[.float .figure none false #[para] #[]]))
      == #[.paragraph])
  let bib := Struct.ofBlocks
    #[.bibliography "refs" none #[{ key := "k", marker := some "1", content := #[.text "Entry"] }]]
  t "bibliography is one entry node per item, one leaf each"
    (structKinds bib == #[.bibEntry] && structTexts bib == #["Entry"])
  -- transparent wrappers splice, decorative and state-only arms vanish
  t "center/ragged/spaced/role/step/only/columns are transparent"
    (structKinds (Struct.ofBlocks
      #[.center #[para], .ragged #[para], .spaced {} #[para], .role "r" #[para],
        .step 1 none #[para], .only #["html"] #[para], .columns #[(none, #[para])]])
      == #[.paragraph, .paragraph, .paragraph, .paragraph, .paragraph, .paragraph, .paragraph])
  t "rule, pagebreak, setPalette, setTokens produce no node"
    ((Struct.ofBlocks #[.rule default none {}, .pagebreak, .setPalette {}, .setTokens {}]).isEmpty)

  -- inline arms
  let inl (x : Ir.Inline) : Array Struct.Node := structKids (Struct.ofBlocks #[.para #[x]])
  t "link is a link node over its body"
    (structKinds (inl (.link "https://example.org" #[.text "b"])) == #[.link "https://example.org"])
  t "a language style is a span" (structKinds (inl (.styled (.lang "fr") #[.text "b"])) == #[.span "fr"])
  t "other styles are transparent"
    ((inl (.styled .bold #[.text "b"])) == #[.leaf 0 (.text "b")])
  t "footnote is a note" (structKinds (inl (.footnote (some 1) #[.text "n"])) == #[.note])
  t "ref is a reference over its resolved text"
    (structKinds (inl (.ref "k" .plain "3" (some "a"))) == #[.reference (some "a")]
      && structTexts (inl (.ref "k" .plain "3" (some "a"))) == #["3"])
  t "math is a formula over its source"
    (structKinds (inl (.math false "x^2")) == #[.formula] && structTexts (inl (.math false "x^2")) == #["x^2"])
  t "image is a leaf carrying source and alternative"
    ((Struct.leaves (inl (.image "a.png" {} "alt"))).map (·.2) == #[.image "a.png" "alt"])
  t "icon is a text leaf worth its alternative"
    ((Struct.leaves (inl (.icon 'x' "arrow"))).map (·.2) == #[.text "arrow"])
  t "linebreak is a leaf worth a space"
    ((Struct.leaves (inl (.linebreak {}))).map (·.2.census) == #[" "])
  t "label, fill, strut, page placeholders produce nothing"
    ((inl (.label "k")).isEmpty && (inl .fill).isEmpty && (inl (.strut {})).isEmpty
      && (inl .pageNumber).isEmpty && (inl .pageCount).isEmpty)

  -- ids: preorder across nesting, and the tree a document elaborates
  let nested := Struct.ofBlocks
    #[.section 1 false none #[.text "H"],
      .list false #[#[.para #[.text "a", .link "u" #[.text "b"]]], #[.para #[.text "c"]]],
      .float .figure none false #[.para #[.image "i.png" {} "pic"]] #[.text "Cap"]]
  t "ids run 0..n-1 in preorder across nesting"
    ((Struct.leaves nested).map (·.1) == #[0, 1, 2, 3, 4, 5]
      && structTexts nested == #["H", "a", "b", "c", "Cap", ""])
  let (doc, _) := elabStr (dvDoc "" "\\section{Intro}\n\nText\\footnote{note} here.\n\n\\begin{itemize}\\item one\\end{itemize}")
  let tree := Struct.ofDoc doc
  t "an elaborated document projects heading, paragraph with a note, and a list"
    (structKinds tree.children == #[.heading 1, .paragraph, .list false]
      && tree.headings == #[1]
      && (structKinds (structKids (tree.children.extract 1 2))).contains .note)
