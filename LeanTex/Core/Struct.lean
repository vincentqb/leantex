module

public import LeanTex.Core.Ir

/-! The document's structure tree: one backend-neutral projection of the IR that a tagged PDF's
structure tree and an HTML page's element tree both read; its leaves carry preorder ids. -/

namespace LeanTex.Core.Struct

open Ir

/-- A structure node's kind: the standard structure types the IR can fill (ISO 32000-2 §14.8.4). -/
public inductive Kind where
  /-- The root, one per document. -/
  | document
  /-- A titled region that is not an outline heading; its title is a `.title` child. -/
  | section
  /-- The title of a `.section` region. -/
  | title
  /-- An outline heading at its `\section` level. -/
  | heading (level : Ir.HeadingLevel)
  | paragraph
  | list (ordered : Bool)
  | item
  /-- A list item's marker: generated ink, so it carries no leaf. -/
  | label
  /-- A list item's content. -/
  | body
  | table
  | row
  | cell
  | caption
  /-- A captioned object or a diagram. -/
  | figure
  | formula
  /-- A code listing or pseudocode. -/
  | code
  | quote
  /-- A footnote's body. -/
  | note
  /-- A speaker note: a side channel, never page content. -/
  | aside
  /-- A navigation landmark. -/
  | nav
  /-- One reference-list entry. -/
  | bibEntry
  | link (url : String)
  /-- A language span, the BCP 47 tag it declares. -/
  | span (lang : String)
  /-- One line of a laid-out paragraph, with how many scopes it opens and how many it closes, which
  a reader of the tagged file gets as parentheses. -/
  | line (opens closes : Nat)
  /-- A cross-reference and the anchor it resolved to. -/
  | reference (target : Option String)
  /-- Generated furniture the census counts: a deck logo, a frame footer. -/
  | artifact
  deriving Repr, BEq, Inhabited

/-- What a leaf stands for: the ink-bearing atoms of the document. -/
public inductive Leaf where
  | text (s : String)
  /-- An image, its source and its text alternative. -/
  | image (src : String) (alt : Alt)
  /-- A diagram, one leaf, with the alternative a reader of either artifact gets. -/
  | picture (alt : Alt)
  /-- A declared line break, worth the space `plainText` reads it as. -/
  | linebreak
  deriving Repr, BEq, Inhabited

/-- A leaf's census text: exactly what `plainTextOne` says of the inline
it came from. -/
public def Leaf.census : Leaf → String
  | .text s => s
  | .image _ _ => ""
  | .picture _ => ""
  | .linebreak => " "

/-- A leaf's alternative census: its source (`none` for a native picture) and alternative. -/
def Leaf.altCensus (out : Array (Option String × Alt)) :
    Leaf → Array (Option String × Alt)
  | .image src alt => out.push (some src, alt)
  | .picture alt => out.push (none, alt)
  | .text _ | .linebreak => out

/-- Whether a structure element holds the leaf: every leaf but a decorative image or picture. -/
@[expose] public def Leaf.held : Leaf → Bool
  | .image _ .decorative | .picture .decorative => false
  | .image _ .undeclared | .image _ (.described _) | .picture .undeclared
  | .picture (.described _) | .text _ | .linebreak => true

/-- What a kind contributes to the outline census: an outline heading its level. -/
def Kind.outlineEmit (out : Array Ir.HeadingLevel) : Kind → Array Ir.HeadingLevel
  | .heading level => out.push level
  | .document | .section | .title | .paragraph | .list _ | .item | .label | .body
  | .table | .row | .cell | .caption | .figure | .formula | .code | .quote | .note
  | .aside | .nav | .bibEntry | .link _ | .span _ | .line _ _ | .reference _ | .artifact => out

/-- Whether the outline census reads a kind's content: every kind's but a speaker note's. -/
@[expose] public def Kind.outlineDescends : Kind → Bool
  | .aside => false
  | .document | .section | .title | .heading _ | .paragraph | .list _ | .item | .label
  | .body | .table | .row | .cell | .caption | .figure | .formula | .code | .quote
  | .note | .nav | .bibEntry | .link _ | .span _ | .line _ _ | .reference _ | .artifact => true

theorem Kind.outlineEmit_acc (out : Array Ir.HeadingLevel) (kind : Kind) :
    kind.outlineEmit out = out ++ kind.outlineEmit #[] := by
  cases kind <;> simp [Kind.outlineEmit]

public inductive Node where
  | leaf (id : Nat) (l : Leaf)
  | node (kind : Kind) (children : Array Node)
  deriving Repr, BEq, Inhabited

/-- The tree: a `.document` root over the body's nodes. -/
public structure Tree where
  children : Array Node
  deriving Repr, BEq, Inhabited

-- A hand-rolled mutual walk: a tree needs the close event `foldBlocks` lacks.

mutual

@[expose] public def inlinesRaw (out : Array Node) : List Inline → Array Node
  | [] => out
  | x :: rest => inlinesRaw (inlineRaw out x) rest

@[expose] public def inlineRaw (out : Array Node) : Inline → Array Node
  | .text s => out.push (.leaf 0 (.text s))
  | .math _ src => out.push (.node .formula #[.leaf 0 (.text (mathFloor src))])
  | .formula _ _ body => out.push (.node .formula #[.leaf 0 (.text (formulaFloor body))])
  | .styled style body =>
    match style with
    | .lang tag => out.push (.node (.span tag) (inlinesRaw #[] body.toList))
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .family _ | .size _ | .fontSize _ _ => inlinesRaw out body.toList
  | .colored _ _ body => inlinesRaw out body.toList
  | .located _ body => inlinesRaw out body.toList
  | .role _ body => inlinesRaw out body.toList
  | .link url body => out.push (.node (.link url) (inlinesRaw #[] body.toList))
  | .label _ => out
  | .ref _ _ text target => out.push (.node (.reference target) #[.leaf 0 (.text text)])
  | .decorated _ body => inlinesRaw out body.toList
  | .fill => out
  | .hspace _ _ => out
  | .rule _ _ _ => out.push (.node .artifact #[])
  | .pageNumber => out
  | .pageCount => out
  | .linebreak _ => out.push (.leaf 0 .linebreak)
  | .strut _ => out
  | .italicCorr _ => out
  | .onSteps _ body => inlinesRaw out body.toList
  | .altSteps _ active otherwise =>
    inlinesRaw (inlinesRaw out active.toList) otherwise.toList
  | .image src _ alt => out.push (.leaf 0 (.image src alt))
  | .icon _ label => out.push (.leaf 0 (.text label))
  | .cite _ keys => out.push (.leaf 0 (.text (citeMarks keys)))
  | .cited _ _ ink => inlinesRaw out ink.toList
  | .footnote _ body => out.push (.node .note (inlinesRaw #[] body.toList))

end

/-- A title region's node, when the title is not empty. -/
public def titleRaw (title : Array Inline) : Array Node :=
  if title.isEmpty then #[] else #[.node .title (inlinesRaw #[] title.toList)]

/-- A caption's node, when there is one to caption with. -/
public def captionRaw (caption : Array Inline) : Array Node :=
  if caption.isEmpty then #[] else #[.node .caption (inlinesRaw #[] caption.toList)]

/-- Table cells, each its own `.cell` over its inline content. -/
def cellsRaw (out : Array Node) : List (Array Inline) → Array Node
  | [] => out
  | cell :: rest => cellsRaw (out.push (.node .cell (inlinesRaw #[] cell.toList))) rest

public def rowsRaw (out : Array Node) : List (Array (Array Inline)) → Array Node
  | [] => out
  | row :: rest => rowsRaw (out.push (.node .row (cellsRaw #[] row.toList))) rest

/-- Reference-list entries, each its own `.bibEntry` over its inline content. -/
public def bibRaw (out : Array Node) : List BibItem → Array Node
  | [] => out
  | item :: rest =>
    bibRaw (out.push (.node .bibEntry (inlinesRaw #[] item.content.toList))) rest

/-- Pseudocode lines: each line's content then its comment, in reading order. -/
public def algRaw (out : Array Node) : List AlgLine → Array Node
  | [] => out
  | l :: rest =>
    algRaw (match l.comment with
      | some c => inlinesRaw (inlinesRaw out l.content.toList) c.toList
      | none => inlinesRaw out l.content.toList) rest

/-- A laid-out paragraph's lines, each a `.line` over its content with the scopes it opens past the
line before, at depth `prev`, and closes before the next. -/
public def laidRaw (prev : Nat) (out : Array Node) : List LaidLine → Array Node
  | [] => out
  | l :: rest =>
    let b := l.bounds prev ((rest.head?.map (·.depth)).getD 0)
    laidRaw l.depth (out.push (.node (.line b.1 b.2) (inlinesRaw #[] l.content.toList))) rest

mutual

@[expose] public def blocksRaw (out : Array Node) : List Block → Array Node
  | [] => out
  | b :: rest => blocksRaw (blockRaw out b) rest

@[expose] public def blockRaw (out : Array Node) : Block → Array Node
  | .para content => out.push (.node .paragraph (inlinesRaw #[] content.toList))
  | .section level _ _ title => out.push (.node (.heading level) (inlinesRaw #[] title.toList))
  | .list ordered _ items => out.push (.node (.list ordered) (itemsRaw #[] items.toList))
  | .center body => blocksRaw out body.toList
  | .lines ls => out.push (.node .paragraph (laidRaw 0 #[] ls.toList))
  | .ragged _ body => blocksRaw out body.toList
  | .spaced _ body => blocksRaw out body.toList
  | .role _ body => blocksRaw out body.toList
  | .link target body => out.push (.node (.link target) (blocksRaw #[] body.toList))
  | .quote _ body => out.push (.node .quote (blocksRaw #[] body.toList))
  | .abstract body => out.push (.node .section (blocksRaw #[] body.toList))
  | .titled _ title body =>
    out.push (.node .section (blocksRaw (titleRaw title) body.toList))
  | .disclosure title _ body =>
    out.push (.node .section (blocksRaw (titleRaw title) body.toList))
  | .equation number content =>
    out.push (.node .formula
      ((inlinesRaw #[] content.toList).push (.node .label (inlinesRaw #[] number.toList))))
  | .verbatim _ content spec =>
    match spec.caption with
    | some (_, cap) =>
      out.push (.node .figure
        #[.node .caption #[.leaf 0 (.text (plainText cap))],
          .node .code #[.leaf 0 (.text content)]])
    | none => out.push (.node .code #[.leaf 0 (.text content)])
  | .algorithm _ _ lines => out.push (.node .code (algRaw #[] lines.toList))
  | .columns cols => colsRaw out cols.toList
  | .onSteps _ body => blocksRaw out body.toList
  | .altSteps _ active otherwise =>
    blocksRaw (blocksRaw out active.toList) otherwise.toList
  | .note body => out.push (.node .aside (blocksRaw #[] body.toList))
  | .only _ body => blocksRaw out body.toList
  | .nav _ body => out.push (.node .nav (blocksRaw #[] body.toList))
  | .logo content => out.push (.node .artifact (inlinesRaw #[] content.toList))
  | .pagebreak => out
  | .frame title _ _ _ body =>
    out.push (.node .section (blocksRaw (titleRaw title) body.toList))
  | .framefoot content => out.push (.node .artifact (inlinesRaw #[] content.toList))
  | .setPalette _ => out
  | .setTokens _ => out
  | .rule _ _ _ => out
  | .picture pic => out.push (.leaf 0 (.picture pic.alternative))
  | .table _ _ _ rows _ _ => out.push (.node .table (rowsRaw #[] rows.toList))
  -- The caption stands first whatever `capAbove` says: census order is `blocksText`'s.
  | .float _ _ _ body caption =>
    out.push (.node .figure (blocksRaw (captionRaw caption) body.toList))
  | .bibliography _ _ items => bibRaw out items.toList

public def itemsRaw (out : Array Node) : List (Array Block) → Array Node
  | [] => out
  | item :: rest =>
    itemsRaw (out.push (.node .item
      #[.node .label #[], .node .body (blocksRaw #[] item.toList)])) rest

public def colsRaw (out : Array Node) : List (BoxWidth × Array Block) → Array Node
  | [] => out
  | (_, body) :: rest => colsRaw (blocksRaw out body.toList) rest

end

mutual

public def numberList (k : Nat) (out : Array Node) : List Node → Array Node × Nat
  | [] => (out, k)
  | n :: rest =>
    let r := numberOne k n
    numberList r.2 (out.push r.1) rest

def numberOne (k : Nat) : Node → Node × Nat
  | .leaf _ l => (.leaf k l, k + 1)
  | .node kind kids =>
    let r := numberList k #[] kids.toList
    (.node kind r.1, r.2)

end

/-- Number a shape's leaves in preorder from `k`. -/
@[expose] public def number (k : Nat) (ns : Array Node) : Array Node := (numberList k #[] ns.toList).1

/-- The structure of a block sequence, leaves numbered from 0. -/
@[expose] public def ofBlocks (bs : Array Block) : Array Node := number 0 (blocksRaw #[] bs.toList)

/-- The document's structure tree: its body under one `.document` root; furniture has no node. -/
@[expose] public def ofDoc (doc : Doc) : Tree := { children := ofBlocks doc.body }

public theorem picture_leaf_projects (out : Array Node) (pic : Pic.Picture) :
    blockRaw out (.picture pic) = out.push (.leaf 0 (.picture pic.alternative)) := by
  simp [blockRaw]

public structure NodeFold (α : Type) where
  leaf : α → Nat → Leaf → α
  enter : α → Kind → α
  descends : Kind → Bool

mutual

public def foldNodeList (f : NodeFold α) (acc : α) : List Node → α
  | [] => acc
  | n :: rest => foldNodeList f (foldNode f acc n) rest

public def foldNode (f : NodeFold α) (acc : α) : Node → α
  | .leaf id l => f.leaf acc id l
  | .node kind kids =>
    match f.descends kind with
    | true => foldNodeList f (f.enter acc kind) kids.toList
    | false => f.enter acc kind

end

/-- A node's fold: entered, then its content read when the fold descends into its kind. -/
private def NodeFold.node (f : NodeFold α) (acc : α) (kind : Kind) (content : α → α) : α :=
  match f.descends kind with
  | true => content (f.enter acc kind)
  | false => f.enter acc kind

/-- An IR census as its walk's functions, one for each position `blockRaw` reads. -/
private structure Census (α : Type) where
  inline : α → Inline → α
  inlines : α → List Inline → α
  block : α → Block → α
  blocks : α → List Block → α
  items : α → List (Array Block) → α
  cols : α → List (BoxWidth × Array Block) → α
  rows : α → List (Array (Array Inline)) → α
  cells : α → List (Array Inline) → α
  bib : α → List BibItem → α
  alg : α → List AlgLine → α
  laid : α → Nat → List LaidLine → α

/-- What `F` reads over a title or caption region's node, absent when the content is empty. -/
private def Census.region (G : Census α) (F : NodeFold α) (kind : Kind) (a : α) (xs : Array Inline) : α :=
  if xs.isEmpty then a else F.node a kind (G.inlines · xs.toList)

/-- `G` is the census `F` reads off `blockRaw`'s tree: one equation per IR constructor and list
position the tree reads. -/
private structure Sim (F : NodeFold α) (G : Census α) : Prop where
  inlinesNil : ∀ a, G.inlines a [] = a
  inlinesCons : ∀ a x xs, G.inlines a (x :: xs) = G.inlines (G.inline a x) xs
  iText : ∀ a s, G.inline a (.text s) = F.leaf a 0 (.text s)
  iMath : ∀ a d src, G.inline a (.math d src) = F.node a .formula (F.leaf · 0 (.text (mathFloor src)))
  iFormula : ∀ a d src body,
    G.inline a (.formula d src body) = F.node a .formula (F.leaf · 0 (.text (formulaFloor body)))
  iLang : ∀ a tag body,
    G.inline a (.styled (.lang tag) body) = F.node a (.span tag) (G.inlines · body.toList)
  iStyled : ∀ a s body, (∀ tag, s ≠ .lang tag) → G.inline a (.styled s body) = G.inlines a body.toList
  iColored : ∀ a c n body, G.inline a (.colored c n body) = G.inlines a body.toList
  iLocated : ∀ a n body, G.inline a (.located n body) = G.inlines a body.toList
  iRole : ∀ a n body, G.inline a (.role n body) = G.inlines a body.toList
  iLink : ∀ a url body, G.inline a (.link url body) = F.node a (.link url) (G.inlines · body.toList)
  iLabel : ∀ a key, G.inline a (.label key) = a
  iRef : ∀ a key form text target,
    G.inline a (.ref key form text target) = F.node a (.reference target) (F.leaf · 0 (.text text))
  iDecorated : ∀ a k body, G.inline a (.decorated k body) = G.inlines a body.toList
  iFill : ∀ a, G.inline a .fill = a
  iHspace : ∀ a g keep, G.inline a (.hspace g keep) = a
  iRule : ∀ a w h r, G.inline a (.rule w h r) = F.node a .artifact id
  iPageNumber : ∀ a, G.inline a .pageNumber = a
  iPageCount : ∀ a, G.inline a .pageCount = a
  iLinebreak : ∀ a e, G.inline a (.linebreak e) = F.leaf a 0 .linebreak
  iStrut : ∀ a h, G.inline a (.strut h) = a
  iItalicCorr : ∀ a m, G.inline a (.italicCorr m) = a
  iOnSteps : ∀ a spec body, G.inline a (.onSteps spec body) = G.inlines a body.toList
  iAltSteps : ∀ a spec x y, G.inline a (.altSteps spec x y) = G.inlines (G.inlines a x.toList) y.toList
  iImage : ∀ a src size alt, G.inline a (.image src size alt) = F.leaf a 0 (.image src alt)
  iIcon : ∀ a sc label, G.inline a (.icon sc label) = F.leaf a 0 (.text label)
  iCite : ∀ a tx keys, G.inline a (.cite tx keys) = F.leaf a 0 (.text (citeMarks keys))
  iCited : ∀ a tx keys ink, G.inline a (.cited tx keys ink) = G.inlines a ink.toList
  iFootnote : ∀ a n body, G.inline a (.footnote n body) = F.node a .note (G.inlines · body.toList)
  cellsNil : ∀ a, G.cells a [] = a
  cellsCons : ∀ a c rest, G.cells a (c :: rest) = G.cells (F.node a .cell (G.inlines · c.toList)) rest
  rowsNil : ∀ a, G.rows a [] = a
  rowsCons : ∀ a r rest, G.rows a (r :: rest) = G.rows (F.node a .row (G.cells · r.toList)) rest
  bibNil : ∀ a, G.bib a [] = a
  bibCons : ∀ a it rest,
    G.bib a (it :: rest) = G.bib (F.node a .bibEntry (G.inlines · it.content.toList)) rest
  algNil : ∀ a, G.alg a [] = a
  algCons : ∀ a l rest, G.alg a (l :: rest) = G.alg (match l.comment with
    | some c => G.inlines (G.inlines a l.content.toList) c.toList
    | none => G.inlines a l.content.toList) rest
  laidNil : ∀ a p, G.laid a p [] = a
  laidCons : ∀ a p l rest, G.laid a p (l :: rest) =
    let b := l.bounds p ((rest.head?.map (·.depth)).getD 0)
    G.laid (F.node a (.line b.1 b.2) (G.inlines · l.content.toList)) l.depth rest
  blocksNil : ∀ a, G.blocks a [] = a
  blocksCons : ∀ a b bs, G.blocks a (b :: bs) = G.blocks (G.block a b) bs
  itemsNil : ∀ a, G.items a [] = a
  itemsCons : ∀ a item rest, G.items a (item :: rest) =
    G.items (F.node a .item fun a => F.node (F.node a .label id) .body (G.blocks · item.toList)) rest
  colsNil : ∀ a, G.cols a [] = a
  colsCons : ∀ a w body rest, G.cols a ((w, body) :: rest) = G.cols (G.blocks a body.toList) rest
  bPara : ∀ a c, G.block a (.para c) = F.node a .paragraph (G.inlines · c.toList)
  bSection : ∀ a level st num title,
    G.block a (.section level st num title) = F.node a (.heading level) (G.inlines · title.toList)
  bList : ∀ a o s items, G.block a (.list o s items) = F.node a (.list o) (G.items · items.toList)
  bCenter : ∀ a body, G.block a (.center body) = G.blocks a body.toList
  bLines : ∀ a ls, G.block a (.lines ls) = F.node a .paragraph (G.laid · 0 ls.toList)
  bRagged : ∀ a fl body, G.block a (.ragged fl body) = G.blocks a body.toList
  bSpaced : ∀ a g body, G.block a (.spaced g body) = G.blocks a body.toList
  bRole : ∀ a n body, G.block a (.role n body) = G.blocks a body.toList
  bLink : ∀ a t body, G.block a (.link t body) = F.node a (.link t) (G.blocks · body.toList)
  bQuote : ∀ a q body, G.block a (.quote q body) = F.node a .quote (G.blocks · body.toList)
  bAbstract : ∀ a body, G.block a (.abstract body) = F.node a .section (G.blocks · body.toList)
  bTitled : ∀ a k title body, G.block a (.titled k title body) =
    F.node a .section fun a => G.blocks (G.region F .title a title) body.toList
  bDisclosure : ∀ a title e body, G.block a (.disclosure title e body) =
    F.node a .section fun a => G.blocks (G.region F .title a title) body.toList
  bEquation : ∀ a num c, G.block a (.equation num c) =
    F.node a .formula fun a => F.node (G.inlines a c.toList) .label (G.inlines · num.toList)
  bVerbatim : ∀ a cov content spec, G.block a (.verbatim cov content spec) = match spec.caption with
    | some (_, cap) => F.node a .figure fun a =>
      F.node (F.node a .caption (F.leaf · 0 (.text (plainText cap)))) .code (F.leaf · 0 (.text content))
    | none => F.node a .code (F.leaf · 0 (.text content))
  bAlgorithm : ∀ a n s lines, G.block a (.algorithm n s lines) = F.node a .code (G.alg · lines.toList)
  bColumns : ∀ a cols, G.block a (.columns cols) = G.cols a cols.toList
  bOnSteps : ∀ a spec body, G.block a (.onSteps spec body) = G.blocks a body.toList
  bAltSteps : ∀ a spec x y, G.block a (.altSteps spec x y) = G.blocks (G.blocks a x.toList) y.toList
  bNote : ∀ a body, G.block a (.note body) = F.node a .aside (G.blocks · body.toList)
  bOnly : ∀ a t body, G.block a (.only t body) = G.blocks a body.toList
  bNav : ∀ a spec body, G.block a (.nav spec body) = F.node a .nav (G.blocks · body.toList)
  bLogo : ∀ a c, G.block a (.logo c) = F.node a .artifact (G.inlines · c.toList)
  bPagebreak : ∀ a, G.block a .pagebreak = a
  bFrame : ∀ a title st v br body, G.block a (.frame title st v br body) =
    F.node a .section fun a => G.blocks (G.region F .title a title) body.toList
  bFramefoot : ∀ a c, G.block a (.framefoot c) = F.node a .artifact (G.inlines · c.toList)
  bSetPalette : ∀ a p, G.block a (.setPalette p) = a
  bSetTokens : ∀ a t, G.block a (.setTokens t) = a
  bRule : ∀ a c n th, G.block a (.rule c n th) = a
  bPicture : ∀ a pic, G.block a (.picture pic) = F.leaf a 0 (.picture pic.alternative)
  bTable : ∀ a cols pl pr rows rules spans,
    G.block a (.table cols pl pr rows rules spans) = F.node a .table (G.rows · rows.toList)
  bFloat : ∀ a k n ca body cap, G.block a (.float k n ca body cap) =
    F.node a .figure fun a => G.blocks (G.region F .caption a cap) body.toList
  bBibliography : ∀ a src st items, G.block a (.bibliography src st items) = G.bib a items.toList

public theorem foldNodeList_nil_exact (f : NodeFold α) (acc : α) : foldNodeList f acc [] = acc := by rfl

public theorem foldNodeList_cons_exact (f : NodeFold α) (acc : α) (n : Node) (rest : List Node) :
    foldNodeList f acc (n :: rest) = foldNodeList f (foldNode f acc n) rest := by rfl

public theorem foldNode_leaf_exact (f : NodeFold α) (acc : α) (id : Nat) (l : Leaf) :
    foldNode f acc (.leaf id l) = f.leaf acc id l := by rfl

public theorem foldNode_node_exact (f : NodeFold α) (acc : α) (kind : Kind) (kids : Array Node) :
    foldNode f acc (.node kind kids)
      = match f.descends kind with
        | true => foldNodeList f (f.enter acc kind) kids.toList
        | false => f.enter acc kind := by rfl

private theorem foldNode_node (f : NodeFold α) (acc : α) (kind : Kind) (kids : Array Node) :
    foldNode f acc (.node kind kids) = f.node acc kind (foldNodeList f · kids.toList) := rfl

theorem foldNodeList_append (f : NodeFold α) (acc : α) (a b : List Node) :
    foldNodeList f acc (a ++ b) = foldNodeList f (foldNodeList f acc a) b := by
  induction a generalizing acc with
  | nil => rfl
  | cons n rest ih =>
    rw [List.cons_append, foldNodeList_cons_exact, foldNodeList_cons_exact, ih]

theorem foldNodeList_snoc (f : NodeFold α) (acc : α) (l : List Node) (n : Node) :
    foldNodeList f acc (l ++ [n]) = foldNode f (foldNodeList f acc l) n := by
  rw [foldNodeList_append]
  rfl

theorem foldNodeList_push (f : NodeFold α) (acc : α) (out : Array Node) (n : Node) :
    foldNodeList f acc (out.push n).toList = foldNode f (foldNodeList f acc out.toList) n := by
  rw [Array.toList_push, foldNodeList_snoc]

/-- A census that only appends, so the whole walk builds onto its accumulator. -/
public structure Appends {β : Type} (f : NodeFold (Array β)) : Prop where
  leaf : ∀ (out : Array β) (id : Nat) (l : Leaf), f.leaf out id l = out ++ f.leaf #[] id l
  enter : ∀ (out : Array β) (kind : Kind), f.enter out kind = out ++ f.enter #[] kind

mutual

public theorem foldNodeList_acc {β : Type} {f : NodeFold (Array β)} (h : Appends f) (out : Array β)
    (ns : List Node) : foldNodeList f out ns = out ++ foldNodeList f #[] ns := by
  match ns with
  | [] => simp [foldNodeList_nil_exact]
  | n :: rest =>
    rw [foldNodeList_cons_exact, foldNodeList_acc h _ rest, foldNode_acc h out n,
      foldNodeList_cons_exact, foldNodeList_acc h (foldNode f #[] n) rest, Array.append_assoc]

public theorem foldNode_acc {β : Type} {f : NodeFold (Array β)} (h : Appends f) (out : Array β)
    (n : Node) : foldNode f out n = out ++ foldNode f #[] n := by
  match n with
  | .leaf id l => rw [foldNode_leaf_exact, foldNode_leaf_exact, h.leaf]
  | .node kind kids =>
    rw [foldNode_node_exact, foldNode_node_exact]
    cases hd : f.descends kind
    · simpa using h.enter out kind
    · simp only []
      rw [foldNodeList_acc h (f.enter out kind) kids.toList, h.enter out kind,
        foldNodeList_acc h (f.enter #[] kind) kids.toList, Array.append_assoc]

end

/-- The tree's text census: every leaf's text, in preorder. -/
def leafTextFold : NodeFold String where
  leaf := fun acc _ l => acc ++ l.census
  enter := fun acc _ => acc
  descends := fun _ => true

public def leafText (ns : Array Node) : String := foldNodeList leafTextFold "" ns.toList

public def Tree.text (t : Tree) : String := leafText t.children

/-- Every leaf with its id, in preorder. -/
@[expose] public def leavesFold : NodeFold (Array (Nat × Leaf)) where
  leaf := fun out id l => out.push (id, l)
  enter := fun out _ => out
  descends := fun _ => true

@[expose] public def leavesList (out : Array (Nat × Leaf)) (ns : List Node) : Array (Nat × Leaf) :=
  foldNodeList leavesFold out ns

@[expose] public def leavesOne (out : Array (Nat × Leaf)) (n : Node) : Array (Nat × Leaf) :=
  foldNode leavesFold out n

@[expose] public def leaves (ns : Array Node) : Array (Nat × Leaf) := leavesList #[] ns.toList

@[expose] public def Tree.leaves (t : Tree) : Array (Nat × Leaf) := Struct.leaves t.children

/-- How many leaves the tree gives an inline sequence. -/
@[expose] public def leafCountInlines (xs : Array Inline) : Nat := (leaves (inlinesRaw #[] xs.toList)).size

/-- How many leaves the tree gives a block sequence. -/
@[expose] public def leafCountBlocks (bs : Array Block) : Nat := (leaves (blocksRaw #[] bs.toList)).size

/-- The outline headings, in preorder; an `.aside` ships none. -/
def headingsFold : NodeFold (Array Ir.HeadingLevel) where
  leaf := fun out _ _ => out
  enter := Kind.outlineEmit
  descends := Kind.outlineDescends

public def headingsList (out : Array Ir.HeadingLevel) (ns : List Node) : Array Ir.HeadingLevel := foldNodeList headingsFold out ns

public def headingsOne (out : Array Ir.HeadingLevel) (n : Node) : Array Ir.HeadingLevel := foldNode headingsFold out n

public def headings (ns : Array Node) : Array Ir.HeadingLevel := headingsList #[] ns.toList

@[expose] public def Tree.headings (t : Tree) : Array Ir.HeadingLevel := Struct.headings t.children

/-- Every non-text leaf's source and text alternative, in preorder. -/
def altsFold : NodeFold (Array (Option String × Alt)) where
  leaf := fun out _ l => l.altCensus out
  enter := fun out _ => out
  descends := fun _ => true

public def alts (ns : Array Node) : Array (Option String × Alt) := foldNodeList altsFold #[] ns.toList

public def Tree.alts (t : Tree) : Array (Option String × Alt) := Struct.alts t.children

public theorem leavesAppends : Appends leavesFold where
  leaf := by intros; simp [leavesFold]
  enter := by intros; simp [leavesFold]

theorem headingsAppends : Appends headingsFold where
  leaf := by intros; simp [headingsFold]
  enter := fun out kind => Kind.outlineEmit_acc out kind

/-- The IR's alternative census through the shared fold, in document order. -/
def altPush (out : Array (Option String × Alt)) (x : Inline) : Array (Option String × Alt) :=
  match x with
  | .image src _ alt => out.push (some src, alt)
  | _ => out

def altPicPush (out : Array (Option String × Alt)) (b : Block) :
    Array (Option String × Alt) :=
  match b with
  | .picture pic => out.push (none, pic.alternative)
  | _ => out

public def irAlts (bs : Array Block) : Array (Option String × Alt) :=
  foldBlocks altPicPush altPush #[] bs

public theorem leavesList_nil_exact (out : Array (Nat × Leaf)) : leavesList out [] = out := by rfl

public theorem leavesList_cons_exact (out : Array (Nat × Leaf)) (n : Node) (rest : List Node) :
    leavesList out (n :: rest) = leavesList (leavesOne out n) rest := by rfl

public theorem leavesOne_leaf_exact (out : Array (Nat × Leaf)) (id : Nat) (l : Leaf) :
    leavesOne out (.leaf id l) = out.push (id, l) := by rfl

public theorem leavesOne_node_exact (out : Array (Nat × Leaf)) (kind : Kind) (kids : Array Node) :
    leavesOne out (.node kind kids) = leavesList out kids.toList := by rfl

public theorem headingsList_nil_exact (out : Array Ir.HeadingLevel) : headingsList out [] = out := by rfl

public theorem headingsList_cons_exact (out : Array Ir.HeadingLevel) (n : Node) (rest : List Node) :
    headingsList out (n :: rest) = headingsList (headingsOne out n) rest := by rfl

public theorem headingsOne_leaf_exact (out : Array Ir.HeadingLevel) (id : Nat) (l : Leaf) :
    headingsOne out (.leaf id l) = out := by rfl

public theorem headingsOne_heading_exact (out : Array Ir.HeadingLevel) (level : Ir.HeadingLevel) (kids : Array Node) :
    headingsOne out (.node (.heading level) kids) = headingsList (out.push level) kids.toList := by
  rfl

public theorem headingsOne_aside_exact (out : Array Ir.HeadingLevel) (kids : Array Node) :
    headingsOne out (.node .aside kids) = out := by rfl

public theorem headingsOne_through_exact (out : Array Ir.HeadingLevel) (kind : Kind) (kids : Array Node)
    (hh : ∀ level, kind ≠ .heading level) (ha : kind ≠ .aside) :
    headingsOne out (.node kind kids) = headingsList out kids.toList := by
  cases kind
  case heading level => exact absurd rfl (hh level)
  case aside => exact absurd rfl ha
  all_goals rfl

public theorem headings_eq_exact (ns : Array Node) : headings ns = headingsList #[] ns.toList := by rfl

public theorem headingsList_acc (out : Array Ir.HeadingLevel) (ns : List Node) :
    headingsList out ns = out ++ headingsList #[] ns := by
  exact foldNodeList_acc headingsAppends out ns

public theorem leavesList_append (out : Array (Nat × Leaf)) (a b : List Node) :
    leavesList out (a ++ b) = leavesList (leavesList out a) b := by
  exact foldNodeList_append leavesFold out a b

public theorem leavesList_snoc (out : Array (Nat × Leaf)) (l : List Node) (n : Node) :
    leavesList out (l ++ [n]) = leavesOne (leavesList out l) n := by
  exact foldNodeList_snoc leavesFold out l n

section Simulation

variable {α : Type} {F : NodeFold α} {G : Census α}

mutual

private theorem inlinesRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (xs : List Inline) :
    foldNodeList F a (inlinesRaw out xs).toList = G.inlines (foldNodeList F a out.toList) xs := by
  match xs with
  | [] => exact (h.inlinesNil _).symm
  | x :: rest =>
    rw [inlinesRaw, inlinesRaw_fold_exact h a _ rest, inlineRaw_fold_exact h a out x, h.inlinesCons]

private theorem inlineRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (x : Inline) :
    foldNodeList F a (inlineRaw out x).toList = G.inline (foldNodeList F a out.toList) x := by
  match x with
  | .text s => simp only [inlineRaw, foldNodeList_push, h.iText]; rfl
  | .math d src => simp only [inlineRaw, foldNodeList_push, h.iMath]; rfl
  | .formula d src body => simp only [inlineRaw, foldNodeList_push, h.iFormula]; rfl
  | .styled style body =>
    match style with
    | .lang tag =>
      simp only [inlineRaw, foldNodeList_push, foldNode_node, h.iLang]
      exact congrArg (F.node _ _) (funext fun a' => inlinesRaw_fold_exact h a' #[] body.toList)
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .family _ | .size _ | .fontSize _ _ =>
      exact (inlinesRaw_fold_exact h a out body.toList).trans (h.iStyled _ _ _ (by intro _ e; cases e)).symm
  | .colored c n body => rw [h.iColored]; exact inlinesRaw_fold_exact h a out body.toList
  | .located n body => rw [h.iLocated]; exact inlinesRaw_fold_exact h a out body.toList
  | .role n body => rw [h.iRole]; exact inlinesRaw_fold_exact h a out body.toList
  | .link url body =>
    simp only [inlineRaw, foldNodeList_push, foldNode_node, h.iLink]
    exact congrArg (F.node _ _) (funext fun a' => inlinesRaw_fold_exact h a' #[] body.toList)
  | .label key => rw [h.iLabel]; rfl
  | .ref key form text target => simp only [inlineRaw, foldNodeList_push, h.iRef]; rfl
  | .decorated k body => rw [h.iDecorated]; exact inlinesRaw_fold_exact h a out body.toList
  | .fill => rw [h.iFill]; rfl
  | .hspace g keep => rw [h.iHspace]; rfl
  | .rule w hh r => simp only [inlineRaw, foldNodeList_push, h.iRule]; rfl
  | .pageNumber => rw [h.iPageNumber]; rfl
  | .pageCount => rw [h.iPageCount]; rfl
  | .linebreak e => simp only [inlineRaw, foldNodeList_push, h.iLinebreak]; rfl
  | .strut hh => rw [h.iStrut]; rfl
  | .italicCorr m => rw [h.iItalicCorr]; rfl
  | .onSteps spec body => rw [h.iOnSteps]; exact inlinesRaw_fold_exact h a out body.toList
  | .altSteps spec x y =>
    rw [h.iAltSteps, ← inlinesRaw_fold_exact h a out x.toList]
    exact inlinesRaw_fold_exact h a (inlinesRaw out x.toList) y.toList
  | .image src size alt => simp only [inlineRaw, foldNodeList_push, h.iImage]; rfl
  | .icon sc label => simp only [inlineRaw, foldNodeList_push, h.iIcon]; rfl
  | .cite tx keys => simp only [inlineRaw, foldNodeList_push, h.iCite]; rfl
  | .cited tx keys ink => rw [h.iCited]; exact inlinesRaw_fold_exact h a out ink.toList
  | .footnote n body =>
    simp only [inlineRaw, foldNodeList_push, foldNode_node, h.iFootnote]
    exact congrArg (F.node _ _) (funext fun a' => inlinesRaw_fold_exact h a' #[] body.toList)

end

private theorem inlinesNode_fold_exact (h : Sim F G) (a : α) (kind : Kind) (xs : Array Inline) :
    foldNode F a (.node kind (inlinesRaw #[] xs.toList)) = F.node a kind (G.inlines · xs.toList) :=
  congrArg (F.node _ _) (funext fun a' => inlinesRaw_fold_exact h a' #[] xs.toList)

private theorem regionRaw_fold_exact (h : Sim F G) (a : α) (kind : Kind) (xs : Array Inline) :
    foldNodeList F a (if xs.isEmpty then #[] else #[.node kind (inlinesRaw #[] xs.toList)]).toList =
      G.region F kind a xs := by
  unfold Census.region
  split
  · rfl
  · exact inlinesNode_fold_exact h a kind xs

private theorem cellsRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (cells : List (Array Inline)) :
    foldNodeList F a (cellsRaw out cells).toList = G.cells (foldNodeList F a out.toList) cells := by
  induction cells generalizing out with
  | nil => exact (h.cellsNil _).symm
  | cons c rest ih => rw [cellsRaw, ih, foldNodeList_push, inlinesNode_fold_exact h, h.cellsCons]

private theorem rowsRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node)
    (rows : List (Array (Array Inline))) :
    foldNodeList F a (rowsRaw out rows).toList = G.rows (foldNodeList F a out.toList) rows := by
  induction rows generalizing out with
  | nil => exact (h.rowsNil _).symm
  | cons r rest ih =>
    rw [rowsRaw, ih, foldNodeList_push, foldNode_node, h.rowsCons]
    exact congrArg (G.rows · rest)
      (congrArg (F.node _ _) (funext fun a' => cellsRaw_fold_exact h a' #[] r.toList))

private theorem bibRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (items : List BibItem) :
    foldNodeList F a (bibRaw out items).toList = G.bib (foldNodeList F a out.toList) items := by
  induction items generalizing out with
  | nil => exact (h.bibNil _).symm
  | cons it rest ih => rw [bibRaw, ih, foldNodeList_push, inlinesNode_fold_exact h, h.bibCons]

private theorem algRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (lines : List AlgLine) :
    foldNodeList F a (algRaw out lines).toList = G.alg (foldNodeList F a out.toList) lines := by
  induction lines generalizing out with
  | nil => exact (h.algNil _).symm
  | cons l rest ih =>
    rw [algRaw, ih, h.algCons]
    cases l.comment <;> simp only [inlinesRaw_fold_exact h]

private theorem laidRaw_fold_exact (h : Sim F G) (a : α) (p : Nat) (out : Array Node)
    (lines : List LaidLine) :
    foldNodeList F a (laidRaw p out lines).toList = G.laid (foldNodeList F a out.toList) p lines := by
  induction lines generalizing p out with
  | nil => exact (h.laidNil _ _).symm
  | cons l rest ih => rw [laidRaw, ih, foldNodeList_push, inlinesNode_fold_exact h, h.laidCons]

mutual

private theorem blocksRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (bs : List Block) :
    foldNodeList F a (blocksRaw out bs).toList = G.blocks (foldNodeList F a out.toList) bs := by
  match bs with
  | [] => exact (h.blocksNil _).symm
  | b :: rest =>
    rw [blocksRaw, blocksRaw_fold_exact h a _ rest, blockRaw_fold_exact h a out b, h.blocksCons]

private theorem blockRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (b : Block) :
    foldNodeList F a (blockRaw out b).toList = G.block (foldNodeList F a out.toList) b := by
  match b with
  | .para c => rw [blockRaw, foldNodeList_push, inlinesNode_fold_exact h, h.bPara]
  | .section level st num title => rw [blockRaw, foldNodeList_push, inlinesNode_fold_exact h, h.bSection]
  | .list o _ items =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bList]
    exact congrArg (F.node _ _) (funext fun a' => itemsRaw_fold_exact h a' #[] items.toList)
  | .center body => rw [h.bCenter]; exact blocksRaw_fold_exact h a out body.toList
  | .lines ls =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bLines]
    exact congrArg (F.node _ _) (funext fun a' => laidRaw_fold_exact h a' 0 #[] ls.toList)
  | .ragged fl body => rw [h.bRagged]; exact blocksRaw_fold_exact h a out body.toList
  | .spaced g body => rw [h.bSpaced]; exact blocksRaw_fold_exact h a out body.toList
  | .role n body => rw [h.bRole]; exact blocksRaw_fold_exact h a out body.toList
  | .link t body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bLink]
    exact congrArg (F.node _ _) (funext fun a' => blocksRaw_fold_exact h a' #[] body.toList)
  | .quote _ body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bQuote]
    exact congrArg (F.node _ _) (funext fun a' => blocksRaw_fold_exact h a' #[] body.toList)
  | .abstract body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bAbstract]
    exact congrArg (F.node _ _) (funext fun a' => blocksRaw_fold_exact h a' #[] body.toList)
  | .titled k title body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bTitled]
    exact congrArg (F.node _ _) (funext fun a' => by
      rw [blocksRaw_fold_exact h a' (titleRaw title) body.toList, titleRaw, regionRaw_fold_exact h])
  | .disclosure title e body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bDisclosure]
    exact congrArg (F.node _ _) (funext fun a' => by
      rw [blocksRaw_fold_exact h a' (titleRaw title) body.toList, titleRaw, regionRaw_fold_exact h])
  | .equation num c =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bEquation]
    exact congrArg (F.node _ _) (funext fun a' => by
      rw [foldNodeList_push, inlinesNode_fold_exact h, inlinesRaw_fold_exact h a' #[] c.toList]; rfl)
  | .verbatim cov content spec =>
    rw [h.bVerbatim]
    simp only [blockRaw]
    split <;> simp only [foldNodeList_push] <;> rfl
  | .algorithm n s lines =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bAlgorithm]
    exact congrArg (F.node _ _) (funext fun a' => algRaw_fold_exact h a' #[] lines.toList)
  | .columns cols => rw [h.bColumns]; exact colsRaw_fold_exact h a out cols.toList
  | .onSteps spec body => rw [h.bOnSteps]; exact blocksRaw_fold_exact h a out body.toList
  | .altSteps spec x y =>
    rw [h.bAltSteps, ← blocksRaw_fold_exact h a out x.toList]
    exact blocksRaw_fold_exact h a (blocksRaw out x.toList) y.toList
  | .note body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bNote]
    exact congrArg (F.node _ _) (funext fun a' => blocksRaw_fold_exact h a' #[] body.toList)
  | .only t body => rw [h.bOnly]; exact blocksRaw_fold_exact h a out body.toList
  | .nav spec body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bNav]
    exact congrArg (F.node _ _) (funext fun a' => blocksRaw_fold_exact h a' #[] body.toList)
  | .logo c => rw [blockRaw, foldNodeList_push, inlinesNode_fold_exact h, h.bLogo]
  | .pagebreak => rw [h.bPagebreak]; rfl
  | .frame title st v br body =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bFrame]
    exact congrArg (F.node _ _) (funext fun a' => by
      rw [blocksRaw_fold_exact h a' (titleRaw title) body.toList, titleRaw, regionRaw_fold_exact h])
  | .framefoot c => rw [blockRaw, foldNodeList_push, inlinesNode_fold_exact h, h.bFramefoot]
  | .setPalette p => rw [h.bSetPalette]; rfl
  | .setTokens t => rw [h.bSetTokens]; rfl
  | .rule c n th => rw [h.bRule]; rfl
  | .picture pic => rw [blockRaw, foldNodeList_push, h.bPicture]; rfl
  | .table cols pl pr rows rules spans =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bTable]
    exact congrArg (F.node _ _) (funext fun a' => rowsRaw_fold_exact h a' #[] rows.toList)
  | .float k n ca body cap =>
    rw [blockRaw, foldNodeList_push, foldNode_node, h.bFloat]
    exact congrArg (F.node _ _) (funext fun a' => by
      rw [blocksRaw_fold_exact h a' (captionRaw cap) body.toList, captionRaw, regionRaw_fold_exact h])
  | .bibliography src st items => rw [h.bBibliography]; exact bibRaw_fold_exact h a out items.toList

private theorem itemsRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node) (items : List (Array Block)) :
    foldNodeList F a (itemsRaw out items).toList = G.items (foldNodeList F a out.toList) items := by
  match items with
  | [] => exact (h.itemsNil _).symm
  | item :: rest =>
    rw [itemsRaw, itemsRaw_fold_exact h a _ rest, foldNodeList_push, foldNode_node, h.itemsCons]
    exact congrArg (G.items · rest) (congrArg (F.node _ _) (funext fun a' =>
      congrArg (F.node _ _) (funext fun a'' => blocksRaw_fold_exact h a'' #[] item.toList)))

private theorem colsRaw_fold_exact (h : Sim F G) (a : α) (out : Array Node)
    (cols : List (BoxWidth × Array Block)) :
    foldNodeList F a (colsRaw out cols).toList = G.cols (foldNodeList F a out.toList) cols := by
  match cols with
  | [] => exact (h.colsNil _).symm
  | (w, body) :: rest => rw [colsRaw, colsRaw_fold_exact h a _ rest, blocksRaw_fold_exact h, h.colsCons]

end

mutual

private theorem numberList_fold_exact (hl : ∀ a i j l, F.leaf a i l = F.leaf a j l) (a : α) (k : Nat)
    (out : Array Node) (ns : List Node) :
    foldNodeList F a (numberList k out ns).1.toList = foldNodeList F (foldNodeList F a out.toList) ns := by
  match ns with
  | [] => rfl
  | n :: rest =>
    rw [numberList, foldNodeList_cons_exact, numberList_fold_exact hl a _ _ rest, foldNodeList_push,
      numberOne_fold_exact hl]

private theorem numberOne_fold_exact (hl : ∀ a i j l, F.leaf a i l = F.leaf a j l) (a : α) (k : Nat)
    (n : Node) :
    foldNode F a (numberOne k n).1 = foldNode F a n := by
  match n with
  | .leaf id l => exact hl a k id l
  | .node kind kids =>
    simp only [numberOne, foldNode_node]
    exact congrArg (F.node _ _) (funext fun a' => numberList_fold_exact hl a' k #[] kids.toList)

end

/-- The census `F` reads off a numbered block sequence, when `F` reads no leaf's id. -/
private theorem ofBlocks_fold_exact (h : Sim F G) (hl : ∀ a i j l, F.leaf a i l = F.leaf a j l) (a : α)
    (bs : Array Block) : foldNodeList F a (ofBlocks bs).toList = G.blocks a bs.toList := by
  unfold ofBlocks number
  rw [numberList_fold_exact hl, blocksRaw_fold_exact h]
  rfl

end Simulation

private def textCensus : Census String where
  inline a x := let t := plainTextOne x; a ++ t
  inlines a xs := let t := plainTextList xs; a ++ t
  block := blockTextOne
  blocks := blockTextList
  items := blockTextItems
  cols := blockTextColumns
  rows := blockTextTableRows
  cells := blockTextTableCells
  bib := blockTextBibItems
  alg := algLineText
  laid a _ ls := laidText a ls

private def headingsCensus : Census (Array Ir.HeadingLevel) where
  inline a _ := a
  inlines a _ := a
  block := headingLevelOne
  blocks := headingLevelList
  items := headingLevelItems
  cols := headingLevelColumns
  rows a _ := a
  cells a _ := a
  bib a _ := a
  alg a _ := a
  laid a _ _ := a

private def altsCensus : Census (Array (Option String × Alt)) where
  inline := foldInline altPush
  inlines := foldInlineList altPush
  block := foldBlock altPicPush altPush
  blocks := foldBlockList altPicPush altPush
  items := foldBlockItems altPicPush altPush
  cols := foldBlockCols altPicPush altPush
  rows := foldTableRows altPush
  cells := foldTableCells altPush
  bib := foldBibItems altPush
  alg := foldAlgLines altPush
  laid a _ ls := foldLaidLines altPush a ls

private theorem textSim : Sim leafTextFold textCensus := by
  constructor <;> intros <;>
    simp [textCensus, Census.region, NodeFold.node, leafTextFold, Leaf.census, plainTextOne,
      plainTextList, plainText, blockTextOne, blockTextList, blockTextItems, blockTextColumns,
      blockTextTableRows, blockTextTableCells, blockTextBibItems, algLineText, laidText,
      ListingSpec.capText, String.append_assoc] <;>
    first | rfl | (split <;> simp_all [plainTextList])

private theorem headingsSim : Sim headingsFold headingsCensus := by
  constructor <;> intros <;>
    simp [headingsCensus, Census.region, NodeFold.node, headingsFold, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne, headingLevelList, headingLevelItems, headingLevelColumns] <;>
    first | rfl | (split <;> simp_all)

private theorem altsSim : Sim altsFold altsCensus := by
  constructor <;> intros <;>
    simp [altsCensus, Census.region, NodeFold.node, altsFold, Leaf.altCensus, foldInline, foldInlineList,
      foldBlock, foldBlockList, foldBlockItems, foldBlockCols, foldTableRows, foldTableCells, foldBibItems,
      foldAlgLines, foldLaidLines, altPush, altPicPush] <;>
    first | rfl | (split <;> simp_all [foldInlineList])

public theorem number_text (k : Nat) : Conserves leafText (number k) := by
  intro ns
  exact numberList_fold_exact (F := leafTextFold) (fun _ _ _ _ => rfl) "" k #[] ns.toList

public theorem structTree_text (bs : Array Block) : leafText (ofBlocks bs) = blocksText bs :=
  ofBlocks_fold_exact textSim (fun _ _ _ _ => rfl) "" bs

public theorem ofDoc_text (doc : Doc) : (ofDoc doc).text = blocksText doc.body := by
  exact structTree_text doc.body

public theorem structTree_headings_covers (bs : Array Block) :
    headings (ofBlocks bs) = headingLevels bs :=
  ofBlocks_fold_exact headingsSim (fun _ _ _ _ => rfl) #[] bs

public theorem structTree_alts_covers (bs : Array Block) : alts (ofBlocks bs) = irAlts bs :=
  ofBlocks_fold_exact altsSim (fun _ _ _ _ => rfl) #[] bs

public theorem leavesList_acc (out : Array (Nat × Leaf)) (ns : List Node) :
    leavesList out ns = out ++ leavesList #[] ns :=
  foldNodeList_acc leavesAppends out ns

theorem numberList_acc (k : Nat) (out : Array Node) (ns : List Node) :
    (numberList k out ns).1 = out ++ (numberList k #[] ns).1
      ∧ (numberList k out ns).2 = (numberList k #[] ns).2 := by
  induction ns generalizing k out with
  | nil => simp [numberList]
  | cons n rest ih =>
    simp only [numberList]
    obtain ⟨h1, h2⟩ := ih (numberOne k n).2 (out.push (numberOne k n).1)
    obtain ⟨h1', h2'⟩ := ih (numberOne k n).2 (#[].push (numberOne k n).1)
    refine ⟨?_, by rw [h2, h2']⟩
    rw [h1, h1']
    simp

theorem range'_join {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  obtain ⟨m, rfl⟩ : ∃ m, b = a + m := ⟨b - a, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, c = a + m + n := ⟨c - (a + m), by omega⟩
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, List.range'_append_1]
  congr 1
  omega

mutual

theorem numberList_id (k : Nat) (ns : List Node) :
    (leavesList #[] (numberList k #[] ns).1.toList).toList.map Prod.fst
        = List.range' k ((numberList k #[] ns).2 - k)
      ∧ k ≤ (numberList k #[] ns).2 := by
  match ns with
  | [] => simp [numberList, leavesList_nil_exact]
  | n :: rest =>
    obtain ⟨hn, hkn⟩ := numberOne_id k n
    obtain ⟨hr, hkr⟩ := numberList_id (numberOne k n).2 rest
    obtain ⟨h1, h2⟩ := numberList_acc (numberOne k n).2 (#[].push (numberOne k n).1) rest
    simp only [numberList]
    rw [h1, h2, Array.toList_append, leavesList_append, leavesList_acc, Array.toList_append,
      List.map_append, hr]
    refine ⟨?_, by omega⟩
    have hone : (leavesList #[] (#[].push (numberOne k n).1).toList).toList.map Prod.fst
        = List.range' k ((numberOne k n).2 - k) := by
      rw [Array.toList_push]
      simpa [leavesList_nil_exact, leavesList_cons_exact] using hn
    rw [hone]
    exact range'_join hkn hkr

theorem numberOne_id (k : Nat) (n : Node) :
    (leavesOne #[] (numberOne k n).1).toList.map Prod.fst
        = List.range' k ((numberOne k n).2 - k)
      ∧ k ≤ (numberOne k n).2 := by
  match n with
  | .leaf id l => simp [numberOne, leavesOne_leaf_exact]
  | .node kind kids =>
    simp only [numberOne, leavesOne_node_exact]
    exact numberList_id k kids.toList

end

public theorem structTree_leaves_id (bs : Array Block) :
    (leaves (ofBlocks bs)).toList.map Prod.fst = List.range (leaves (ofBlocks bs)).size := by
  unfold ofBlocks number
  unfold leaves
  obtain ⟨h, _⟩ := numberList_id 0 (blocksRaw #[] bs.toList).toList
  rw [List.range_eq_range', h]
  congr 1
  have := congrArg List.length h
  simp only [List.length_map, Array.length_toList, List.length_range'] at this
  omega

mutual

theorem inlinesRaw_acc (out : Array Node) (xs : List Inline) :
    inlinesRaw out xs = out ++ inlinesRaw #[] xs := by
  match xs with
  | [] => simp [inlinesRaw]
  | x :: rest =>
    rw [inlinesRaw, inlinesRaw_acc _ rest, inlineRaw_acc out x, inlinesRaw,
      inlinesRaw_acc (inlineRaw #[] x) rest, Array.append_assoc]

theorem inlineRaw_acc (out : Array Node) (x : Inline) :
    inlineRaw out x = out ++ inlineRaw #[] x := by
  match x with
  | .text s => simp [inlineRaw]
  | .math d src => simp [inlineRaw]
  | .formula d src body => simp [inlineRaw]
  | .styled style body =>
    match style with
    | .lang tag => simp [inlineRaw]
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .family _ | .size _ | .fontSize _ _ =>
      simp only [inlineRaw]
      exact inlinesRaw_acc out body.toList
  | .colored c n body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .located n body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .role n body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .link url body => simp [inlineRaw]
  | .label key => simp [inlineRaw]
  | .ref key form text target => simp [inlineRaw]
  | .decorated kind body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .fill => simp [inlineRaw]
  | .hspace g keep => simp [inlineRaw]
  | .rule w h r => simp [inlineRaw]
  | .pageNumber => simp [inlineRaw]
  | .pageCount => simp [inlineRaw]
  | .linebreak extra => simp [inlineRaw]
  | .strut h => simp [inlineRaw]
  | .italicCorr m => simp [inlineRaw]
  | .onSteps spec body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .altSteps spec active otherwise =>
    simp only [inlineRaw]
    rw [inlinesRaw_acc (inlinesRaw out active.toList) otherwise.toList,
      inlinesRaw_acc (inlinesRaw #[] active.toList) otherwise.toList,
      inlinesRaw_acc out active.toList, Array.append_assoc]
  | .image src size alt => simp [inlineRaw]
  | .icon sc label => simp [inlineRaw]
  | .cite tx keys => simp [inlineRaw]
  | .cited tx keys ink =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out ink.toList
  | .footnote num body => simp [inlineRaw]

end

theorem bibRaw_acc (out : Array Node) (items : List BibItem) :
    bibRaw out items = out ++ bibRaw #[] items := by
  induction items generalizing out with
  | nil => simp [bibRaw]
  | cons it rest ih =>
    rw [bibRaw, ih, bibRaw, ih (#[].push _)]
    simp

mutual

theorem blocksRaw_acc (out : Array Node) (bs : List Block) :
    blocksRaw out bs = out ++ blocksRaw #[] bs := by
  match bs with
  | [] => simp [blocksRaw]
  | b :: rest =>
    rw [blocksRaw, blocksRaw_acc _ rest, blockRaw_acc out b, blocksRaw,
      blocksRaw_acc (blockRaw #[] b) rest, Array.append_assoc]

public theorem blockRaw_acc (out : Array Node) (b : Block) :
    blockRaw out b = out ++ blockRaw #[] b := by
  match b with
  | .para content => simp [blockRaw]
  | .section level st num title => simp [blockRaw]
  | .list ordered _ items => simp [blockRaw]
  | .center body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .lines ls => simp [blockRaw]
  | .ragged _ body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .spaced g body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .role nm body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .link target body => simp [blockRaw]
  | .quote _ body => simp [blockRaw]
  | .abstract body => simp [blockRaw]
  | .titled kind title body => simp [blockRaw]
  | .disclosure title _ body => simp [blockRaw]
  | .equation number content => simp [blockRaw]
  | .verbatim c content spec =>
    simp only [blockRaw]
    split <;> simp
  | .algorithm nm sm lines => simp [blockRaw]
  | .columns cols =>
    simp only [blockRaw]; exact colsRaw_acc out cols.toList
  | .onSteps spec body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .altSteps spec active otherwise =>
    simp only [blockRaw]
    rw [blocksRaw_acc (blocksRaw out active.toList) otherwise.toList,
      blocksRaw_acc (blocksRaw #[] active.toList) otherwise.toList,
      blocksRaw_acc out active.toList, Array.append_assoc]
  | .note body => simp [blockRaw]
  | .only targets body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .nav spec body => simp [blockRaw]
  | .logo content => simp [blockRaw]
  | .pagebreak => simp [blockRaw]
  | .frame title st v br body => simp [blockRaw]
  | .framefoot content => simp [blockRaw]
  | .setPalette pal => simp [blockRaw]
  | .setTokens tk => simp [blockRaw]
  | .rule c nm th => simp [blockRaw]
  | .picture p => simp [blockRaw]
  | .table cols pl pr rows rules spans => simp [blockRaw]
  | .float fk num ca body caption => simp [blockRaw]
  | .bibliography src style items =>
    simp only [blockRaw]; exact bibRaw_acc out items.toList

theorem colsRaw_acc (out : Array Node) (cols : List (BoxWidth × Array Block)) :
    colsRaw out cols = out ++ colsRaw #[] cols := by
  match cols with
  | [] => simp [colsRaw]
  | (w, body) :: rest =>
    rw [colsRaw, colsRaw_acc _ rest, blocksRaw_acc out body.toList, colsRaw,
      colsRaw_acc (blocksRaw #[] body.toList) rest, Array.append_assoc]

end

mutual

theorem numberList_leafCount_aux (k : Nat) (ns : List Node) :
    (leavesList #[] (numberList k #[] ns).1.toList).size = (leavesList #[] ns).size := by
  match ns with
  | [] => simp [numberList, leavesList_nil_exact]
  | n :: rest =>
    obtain ⟨h1, _⟩ := numberList_acc (numberOne k n).2 (#[].push (numberOne k n).1) rest
    simp only [numberList]
    rw [h1, Array.toList_append, leavesList_append, leavesList_acc, Array.size_append,
      Array.toList_push, leavesList_cons_exact, leavesList_acc (leavesOne #[] n) rest,
      Array.size_append]
    rw [numberList_leafCount_aux (numberOne k n).2 rest]
    simp only [List.nil_append, leavesList_nil_exact, leavesList_cons_exact]
    rw [numberOne_leafCount k n]

theorem numberOne_leafCount (k : Nat) (n : Node) :
    (leavesOne #[] (numberOne k n).1).size = (leavesOne #[] n).size := by
  match n with
  | .leaf id l => simp [numberOne, leavesOne_leaf_exact]
  | .node kind kids =>
    simp only [numberOne, leavesOne_node_exact]
    exact numberList_leafCount_aux k kids.toList

end

public theorem numberList_leafCount (k : Nat) (ns : List Node) :
    (leavesList #[] (numberList k #[] ns).1.toList).size = (leavesList #[] ns).size := by
  exact numberList_leafCount_aux k ns

theorem numberList_count (k : Nat) (ns : List Node) :
    (numberList k #[] ns).2 = k + (leavesList #[] ns).size := by
  obtain ⟨hid, hle⟩ := numberList_id k ns
  have hlen := congrArg List.length hid
  rw [List.length_map, List.length_range'] at hlen
  rw [← numberList_leafCount k ns]
  have : (leavesList #[] (numberList k #[] ns).1.toList).size
      = (leavesList #[] (numberList k #[] ns).1.toList).toList.length := by simp
  omega

theorem numberList_append (k : Nat) (a b : List Node) :
    (numberList k #[] (a ++ b)).1
        = (numberList k #[] a).1 ++ (numberList (numberList k #[] a).2 #[] b).1
      ∧ (numberList k #[] (a ++ b)).2 = (numberList (numberList k #[] a).2 #[] b).2 := by
  induction a generalizing k with
  | nil => simp [numberList]
  | cons n rest ih =>
    obtain ⟨hr1, hr2⟩ := ih (numberOne k n).2
    obtain ⟨hab1, hab2⟩ := numberList_acc (numberOne k n).2
      (#[].push (numberOne k n).1) (rest ++ b)
    obtain ⟨ha1, ha2⟩ := numberList_acc (numberOne k n).2
      (#[].push (numberOne k n).1) rest
    simp only [List.cons_append, numberList]
    rw [hab1, hab2, ha1, ha2, hr1, hr2, Array.append_assoc]
    exact ⟨rfl, rfl⟩

public theorem pair_leaf_ids (a b : Array Node) (k : Nat) :
    (leaves (number k (a ++ b))).toList.map Prod.fst
      = List.range' k (leaves a).size
        ++ List.range' (k + (leaves a).size) (leaves b).size := by
  have hfst := numberList_count k a.toList
  have hoth := numberList_count (k + (leaves a).size) b.toList
  obtain ⟨hidf, _⟩ := numberList_id k a.toList
  obtain ⟨hido, _⟩ := numberList_id (k + (leaves a).size) b.toList
  obtain ⟨happ, _⟩ := numberList_append k a.toList b.toList
  have hca : (leavesList #[] a.toList).size = (leaves a).size := rfl
  have hcb : (leavesList #[] b.toList).size = (leaves b).size := rfl
  rw [hca] at hfst
  rw [hcb] at hoth
  rw [hfst] at happ hidf
  simp only [leaves, number, Array.toList_append]
  rw [happ, Array.toList_append, leavesList_append, leavesList_acc, Array.toList_append,
    List.map_append, hidf, hido, hoth]
  simp
  omega

public theorem onSteps_id (spec : OverlaySpec) (bodyI : Array Inline) (bodyB : Array Block)
    (out : Array Node) (k : Nat) :
    number k (inlineRaw out (.onSteps spec bodyI)) = number k (inlinesRaw out bodyI.toList)
      ∧ number k (blockRaw out (.onSteps spec bodyB)) = number k (blocksRaw out bodyB.toList) := by
  exact ⟨rfl, rfl⟩

public theorem alt_leaf_projects (spec : OverlaySpec)
    (firstI otherI : Array Inline) (firstB otherB : Array Block) (k : Nat) :
    (leaves (number k (inlineRaw #[] (Inline.altSteps spec firstI otherI)))).toList.map Prod.fst
        = List.range' k (leafCountInlines firstI)
          ++ List.range' (k + leafCountInlines firstI) (leafCountInlines otherI)
      ∧ (leaves (number k (blockRaw #[] (Block.altSteps spec firstB otherB)))).toList.map Prod.fst
        = List.range' k (leafCountBlocks firstB)
          ++ List.range' (k + leafCountBlocks firstB) (leafCountBlocks otherB) := by
  have hi : inlineRaw #[] (Inline.altSteps spec firstI otherI)
      = inlinesRaw #[] firstI.toList ++ inlinesRaw #[] otherI.toList := by
    simp only [inlineRaw]
    exact inlinesRaw_acc (inlinesRaw #[] firstI.toList) otherI.toList
  have hb : blockRaw #[] (Block.altSteps spec firstB otherB)
      = blocksRaw #[] firstB.toList ++ blocksRaw #[] otherB.toList := by
    simp only [blockRaw]
    exact blocksRaw_acc (blocksRaw #[] firstB.toList) otherB.toList
  rw [hi, hb, pair_leaf_ids, pair_leaf_ids]
  exact ⟨rfl, rfl⟩

end LeanTex.Core.Struct
