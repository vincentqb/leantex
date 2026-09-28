import LeanTex.Core.Ir

/-! # The structure tree

The document's semantic structure as one backend-neutral value: what a
tagged PDF's structure tree and an HTML page's element tree both say
about the document, projected once from the IR so the two artifacts cannot
disagree on it. Both backends may read it; neither owns it. The tree
carries structure and text only — no geometry, no style, no ink — and its
leaves are the atoms a page attributes ink to: text runs, images, diagram
boxes. Each leaf bears its preorder index, the id a page line will name
(`LineOut.leaf`, the attribution channel M7-18 adds) and a tagger keys
its marked content by.

Three census facts hold the tree to the IR: its leaf text is exactly
`blocksText` (`structTree_text`), its outline headings are exactly
`headingLevels` (`structTree_headings_covers`), and every image and native
picture alternative is exactly the generic fold's alternative census
(`structTree_alts_covers`) — so the walk here descends everywhere the one
shared fold does, footnote bodies and role wrappers included. `structTree_leaves_id` pins the ids: the k-th leaf
in preorder carries `k`.

Every IR arm is classified here, explicitly. A *transparent* wrapper
(`.center`, `.ragged`, `.spaced`, `.role`, `.columns`, `.step`, `.only`;
inline `.styled` bar `.lang`, `.colored`, `.role`, `.underline`, `.step`)
splices its body and invents no node — layout scope is not document
structure. A *decorative* arm (`.rule`) and a *state-only* arm
(`.setPalette`, `.setTokens`, `.pagebreak`; inline `.label`, `.fill`,
`.strut`, `.italicCorr`, `.pageNumber`, `.pageCount`) produces nothing: no text, no
structure. Generated furniture the census still counts (`.logo`,
`.framefoot`) sits under `.artifact`, so a tagger marks it as such. -/

namespace LeanTex.Core.Struct

open Ir

/-- A structure node's kind: the standard structure types the IR can
honestly fill (ISO 32000-2 §14.8.4; the HTML element each maps to is the
one `HtmlDoc` already emits for the arm). -/
inductive Kind where
  /-- The root, one per document. -/
  | document
  /-- A titled region that is not an outline heading: an abstract, a
  beamer block, a slide. Its title, when it has one, is a `.title` child. -/
  | section
  /-- The title of a `.section` region — a frame's or a block's title,
  which `headingLevels` does not count. -/
  | title
  /-- An outline heading at its `\section` level. -/
  | heading (level : Nat)
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
  /-- A captioned object (`{figure}`, `{table}`, a captioned listing) and
  a diagram: HTML's `<figure>`, PDF's `Figure`. -/
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
  /-- A cross-reference and the anchor it resolved to. -/
  | reference (target : Option String)
  /-- Generated furniture the census counts: a deck logo, a frame footer. -/
  | artifact
  deriving Repr, BEq, Inhabited

/-- What a leaf stands for: the ink-bearing atoms of the document. -/
inductive Leaf where
  | text (s : String)
  /-- An image, its source and its text alternative. -/
  | image (src : String) (alt : Alt)
  /-- A diagram, its one leaf, and the alternative a reader of either
  artifact gets (`Pic.Picture.alternative`): its own element in the PDF, as
  an image's is. -/
  | picture (alt : Alt)
  /-- A declared line break, worth the space `plainText` reads it as. -/
  | linebreak
  deriving Repr, BEq, Inhabited

/-- A leaf's census text: exactly what `plainTextOne` says of the inline
it came from. -/
def Leaf.census : Leaf → String
  | .text s => s
  | .image _ _ => ""
  | .picture _ => ""
  | .linebreak => " "

/-- A leaf's alternative census: every non-text leaf's source (an
image's source, `none` for a native picture) and the alternative the
artifacts project. -/
def Leaf.altCensus (out : Array (Option String × Alt)) :
    Leaf → Array (Option String × Alt)
  | .image src alt => out.push (some src, alt)
  | .picture alt => out.push (none, alt)
  | .text _ | .linebreak => out

/-- Does a structure element hold the leaf? Every leaf but decoration: an
image or picture declared decorative is held by nothing, so its ink is an
artifact (ISO 32000-2 §14.8.2.2) — the one resolving site the PDF's
skeleton and its leaf census both read. -/
def Leaf.held : Leaf → Bool
  | .image _ .decorative | .picture .decorative => false
  | .image _ .undeclared | .image _ (.described _) | .picture .undeclared
  | .picture (.described _) | .text _ | .linebreak => true

-- **The kind classification**: what a census does with a kind, as two
-- functions on `Kind` rather than a match inside a walk. A prover reduces
-- these on a concrete kind, so the walk's descent equation is citable with
-- no hypothesis about which kind it is — and the same two answers are the
-- fields a shared node walk would carry.

/-- What a kind contributes to the outline census on the way in: an outline
heading its level, every other kind nothing. The one resolving site for
"which kinds are the outline". -/
def Kind.outlineEmit (out : Array Nat) : Kind → Array Nat
  | .heading level => out.push level
  | .document | .section | .title | .paragraph | .list _ | .item | .label | .body
  | .table | .row | .cell | .caption | .figure | .formula | .code | .quote | .note
  | .aside | .nav | .bibEntry | .link _ | .span _ | .reference _ | .artifact => out

/-- Does the outline census read a kind's content? A speaker note is a side
channel, so no heading inside one reaches the outline (`.aside`); every other
kind reads through. The one place a census declines a subtree. -/
def Kind.outlineDescends : Kind → Bool
  | .aside => false
  | .document | .section | .title | .heading _ | .paragraph | .list _ | .item | .label
  | .body | .table | .row | .cell | .caption | .figure | .formula | .code | .quote
  | .note | .nav | .bibEntry | .link _ | .span _ | .reference _ | .artifact => true

/-- The outline's contribution builds onto its accumulator: the classifier's
half of the outline census's `Appends` witness. -/
theorem Kind.outlineEmit_acc (out : Array Nat) (kind : Kind) :
    kind.outlineEmit out = out ++ kind.outlineEmit #[] := by
  cases kind <;> simp [Kind.outlineEmit]

inductive Node where
  | leaf (id : Nat) (l : Leaf)
  | node (kind : Kind) (children : Array Node)
  deriving Repr, BEq, Inhabited

/-- The tree: a `.document` root over the body's nodes. -/
structure Tree where
  children : Array Node
  deriving Repr, BEq, Inhabited

-- The projection. A hand-rolled mutual walk rather than a `foldBlocks`
-- leaf: the fold reads a node before its content and has no close event,
-- so an accumulator cannot know where a container ends, and a tree is
-- exactly that nesting. Structural recursion through `List`, an `Array`
-- accumulator threaded through, one explicit arm per constructor. Leaf ids
-- are placeholders here; `number` assigns the preorder index once.

mutual

def inlinesRaw (out : Array Node) : List Inline → Array Node
  | [] => out
  | x :: rest => inlinesRaw (inlineRaw out x) rest

def inlineRaw (out : Array Node) : Inline → Array Node
  | .text s => out.push (.leaf 0 (.text s))
  | .math _ src => out.push (.node .formula #[.leaf 0 (.text (mathFloor src))])
  | .formula _ _ body => out.push (.node .formula #[.leaf 0 (.text (formulaFloor body))])
  | .styled style body =>
    match style with
    | .lang tag => out.push (.node (.span tag) (inlinesRaw #[] body.toList))
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .size _ => inlinesRaw out body.toList
  | .colored _ _ body => inlinesRaw out body.toList
  | .role _ body => inlinesRaw out body.toList
  | .link url body => out.push (.node (.link url) (inlinesRaw #[] body.toList))
  | .label _ => out
  | .ref _ _ text target => out.push (.node (.reference target) #[.leaf 0 (.text text)])
  | .underline body => inlinesRaw out body.toList
  | .fill => out
  | .pageNumber => out
  | .pageCount => out
  | .linebreak _ => out.push (.leaf 0 .linebreak)
  | .strut _ => out
  | .italicCorr _ => out
  | .step _ _ body => inlinesRaw out body.toList
  | .alt _ _ active otherwise =>
    inlinesRaw (inlinesRaw out active.toList) otherwise.toList
  | .image src _ alt => out.push (.leaf 0 (.image src alt))
  | .icon _ label => out.push (.leaf 0 (.text label))
  | .cite _ keys => out.push (.leaf 0 (.text (citeMarks keys)))
  | .footnote _ body => out.push (.node .note (inlinesRaw #[] body.toList))

end

/-- A title region's node, when the title is not empty: an empty title is
beamer's untitled block or a bare frame, and no node is invented for it. -/
def titleRaw (title : Array Inline) : Array Node :=
  if title.isEmpty then #[] else #[.node .title (inlinesRaw #[] title.toList)]

/-- A caption's node, when there is one to caption with. -/
def captionRaw (caption : Array Inline) : Array Node :=
  if caption.isEmpty then #[] else #[.node .caption (inlinesRaw #[] caption.toList)]

/-- Table cells, each its own `.cell` over its inline content. -/
def cellsRaw (out : Array Node) : List (Array Inline) → Array Node
  | [] => out
  | cell :: rest => cellsRaw (out.push (.node .cell (inlinesRaw #[] cell.toList))) rest

def rowsRaw (out : Array Node) : List (Array (Array Inline)) → Array Node
  | [] => out
  | row :: rest => rowsRaw (out.push (.node .row (cellsRaw #[] row.toList))) rest

/-- Reference-list entries: one leaf each, the entry's whole text, as
`textLeaves` reads them — the entries are the style's renderings, not
authored content, and no walk descends them. -/
def bibRaw (out : Array Node) : List BibItem → Array Node
  | [] => out
  | item :: rest =>
    bibRaw (out.push (.node .bibEntry #[.leaf 0 (.text (plainText item.content))])) rest

/-- Pseudocode lines: each line's content then its comment, in reading
order — the order `algLineText` and `foldAlgLines` both read. -/
def algRaw (out : Array Node) : List AlgLine → Array Node
  | [] => out
  | l :: rest =>
    algRaw (match l.comment with
      | some c => inlinesRaw (inlinesRaw out l.content.toList) c.toList
      | none => inlinesRaw out l.content.toList) rest

mutual

def blocksRaw (out : Array Node) : List Block → Array Node
  | [] => out
  | b :: rest => blocksRaw (blockRaw out b) rest

def blockRaw (out : Array Node) : Block → Array Node
  | .para content => out.push (.node .paragraph (inlinesRaw #[] content.toList))
  | .section level _ _ title => out.push (.node (.heading level) (inlinesRaw #[] title.toList))
  | .list ordered items => out.push (.node (.list ordered) (itemsRaw #[] items.toList))
  | .center body => blocksRaw out body.toList
  | .ragged _ body => blocksRaw out body.toList
  | .spaced _ body => blocksRaw out body.toList
  | .role _ body => blocksRaw out body.toList
  | .quote body => out.push (.node .quote (blocksRaw #[] body.toList))
  | .abstract body => out.push (.node .section (blocksRaw #[] body.toList))
  | .titled _ title body =>
    out.push (.node .section (blocksRaw (titleRaw title) body.toList))
  -- the number is census text, set beside the formula in every backend: a
  -- counter's digits, or an author's tag elaborated as inline content
  | .equation number content =>
    out.push (.node .formula
      ((inlinesRaw #[] content.toList).push (.node .label (inlinesRaw #[] number.toList))))
  -- a listing's caption is one leaf, as `textLeaves` and the shared fold
  -- read it (the fold does not descend a `.verbatim`)
  | .verbatim _ content spec =>
    match spec.caption with
    | some (_, cap) =>
      out.push (.node .figure
        #[.node .caption #[.leaf 0 (.text (plainText cap))],
          .node .code #[.leaf 0 (.text content)]])
    | none => out.push (.node .code #[.leaf 0 (.text content)])
  | .algorithm _ _ lines => out.push (.node .code (algRaw #[] lines.toList))
  | .columns cols => colsRaw out cols.toList
  | .step _ _ body => blocksRaw out body.toList
  | .alt _ _ active otherwise =>
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
  -- the caption stands first whatever `capAbove` says: census order is
  -- `blocksText`'s, and a caption's placement is the page's, not the tree's
  | .float _ _ _ body caption =>
    out.push (.node .figure (blocksRaw (captionRaw caption) body.toList))
  | .bibliography _ _ items => bibRaw out items.toList

def itemsRaw (out : Array Node) : List (Array Block) → Array Node
  | [] => out
  | item :: rest =>
    itemsRaw (out.push (.node .item
      #[.node .label #[], .node .body (blocksRaw #[] item.toList)])) rest

def colsRaw (out : Array Node) : List (BoxWidth × Array Block) → Array Node
  | [] => out
  | (_, body) :: rest => colsRaw (blocksRaw out body.toList) rest

end

-- The numbering pass: leaf ids are the preorder index, assigned once over
-- the built shape. Structural recursion through `List`, the counter and
-- the accumulator threaded together.

mutual

def numberList (k : Nat) (out : Array Node) : List Node → Array Node × Nat
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
def number (k : Nat) (ns : Array Node) : Array Node := (numberList k #[] ns.toList).1

/-- The structure of a block sequence, leaves numbered from 0. -/
def ofBlocks (bs : Array Block) : Array Node := number 0 (blocksRaw #[] bs.toList)

/-- The document's structure tree: its body under one `.document` root.
The furniture regions (`Doc.head`, `foot`, `logo`, the headline band) are
page artifacts the furniture pass writes and flags as such; they are not
document structure and have no node here. -/
def ofDoc (doc : Doc) : Tree := { children := ofBlocks doc.body }

/-- **A picture's leaf projects the one IR value** (`_projects`): its own
leaf, carrying `Ir.Pic.Picture.alternative` — the value the HTML's svg
reads too (`HtmlDoc.html_picture_name_projects`) — which the PDF turns into
its `Figure` (`Pdf.altElem`). -/
theorem picture_leaf_projects (out : Array Node) (pic : Pic.Picture) :
    blockRaw out (.picture pic) = out.push (.leaf 0 (.picture pic.alternative)) := by
  simp [blockRaw]

-- **One walk over the tree.** The four censuses below differ in three
-- answers and nothing else, so those three are the walk's fields. Read off
-- the four callers rather than invented:
--
--   * `leaf` takes the id because one caller of four reads it (`leaves`
--     pairs it with the leaf; the text and image censuses ignore it).
--   * `enter` is what a node ships before its content: only the outline
--     ships anything (`Kind.outlineEmit`), the other three thread the
--     accumulator through.
--   * `descends` is whether the content is read at all — the one thing a
--     leaf fold cannot say. `.aside` is a side channel, so the outline
--     declines its subtree. It is a function of the kind alone, which is
--     what lets a proof reduce it without unfolding the walk.
--
-- No close event and no context, unlike `Ir.CtxFold`: none of the four
-- needs to know where a container ends, and all four thread one
-- accumulator left to right. Structural mutual recursion through `List`,
-- the knot the projection walks already tie.

structure NodeFold (α : Type) where
  leaf : α → Nat → Leaf → α
  enter : α → Kind → α
  descends : Kind → Bool

mutual

def foldNodeList (f : NodeFold α) (acc : α) : List Node → α
  | [] => acc
  | n :: rest => foldNodeList f (foldNode f acc n) rest

def foldNode (f : NodeFold α) (acc : α) : Node → α
  | .leaf id l => f.leaf acc id l
  | .node kind kids =>
    match f.descends kind with
    | true => foldNodeList f (f.enter acc kind) kids.toList
    | false => f.enter acc kind

end

-- The walk's own equations, and the two arguments every census over it
-- shares: an appended list folds the halves in turn, and a census that only
-- appends builds onto the accumulator it was given. Stated once over any
-- `NodeFold`; each census's named form below is an instance.

theorem foldNodeList_nil_exact (f : NodeFold α) (acc : α) : foldNodeList f acc [] = acc := rfl

theorem foldNodeList_cons_exact (f : NodeFold α) (acc : α) (n : Node) (rest : List Node) :
    foldNodeList f acc (n :: rest) = foldNodeList f (foldNode f acc n) rest := rfl

theorem foldNode_leaf_exact (f : NodeFold α) (acc : α) (id : Nat) (l : Leaf) :
    foldNode f acc (.leaf id l) = f.leaf acc id l := rfl

theorem foldNode_node_exact (f : NodeFold α) (acc : α) (kind : Kind) (kids : Array Node) :
    foldNode f acc (.node kind kids)
      = match f.descends kind with
        | true => foldNodeList f (f.enter acc kind) kids.toList
        | false => f.enter acc kind := rfl

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

/-- A census that only appends: each of its answers builds onto the
accumulator it was given, so the whole walk does. The hypothesis the
accumulator-extraction argument needs, named rather than repeated per
census. -/
structure Appends {β : Type} (f : NodeFold (Array β)) : Prop where
  leaf : ∀ (out : Array β) (id : Nat) (l : Leaf), f.leaf out id l = out ++ f.leaf #[] id l
  enter : ∀ (out : Array β) (kind : Kind), f.enter out kind = out ++ f.enter #[] kind

mutual

theorem foldNodeList_acc {β : Type} {f : NodeFold (Array β)} (h : Appends f) (out : Array β)
    (ns : List Node) : foldNodeList f out ns = out ++ foldNodeList f #[] ns := by
  match ns with
  | [] => simp [foldNodeList_nil_exact]
  | n :: rest =>
    rw [foldNodeList_cons_exact, foldNodeList_acc h _ rest, foldNode_acc h out n,
      foldNodeList_cons_exact, foldNodeList_acc h (foldNode f #[] n) rest, Array.append_assoc]

theorem foldNode_acc {β : Type} {f : NodeFold (Array β)} (h : Appends f) (out : Array β)
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

def leafTextList (acc : String) (ns : List Node) : String := foldNodeList leafTextFold acc ns

def leafTextOne (acc : String) (n : Node) : String := foldNode leafTextFold acc n

def leafText (ns : Array Node) : String := leafTextList "" ns.toList

def Tree.text (t : Tree) : String := leafText t.children

/-- Every leaf with its id, in preorder. -/
def leavesFold : NodeFold (Array (Nat × Leaf)) where
  leaf := fun out id l => out.push (id, l)
  enter := fun out _ => out
  descends := fun _ => true

def leavesList (out : Array (Nat × Leaf)) (ns : List Node) : Array (Nat × Leaf) :=
  foldNodeList leavesFold out ns

def leavesOne (out : Array (Nat × Leaf)) (n : Node) : Array (Nat × Leaf) :=
  foldNode leavesFold out n

def leaves (ns : Array Node) : Array (Nat × Leaf) := leavesList #[] ns.toList

def Tree.leaves (t : Tree) : Array (Nat × Leaf) := Struct.leaves t.children

/-- How many leaves the tree gives an inline sequence: the projection's own
count, so a consumer that has to step over a group it does not ship steps
by exactly what the tree numbered. -/
def leafCountInlines (xs : Array Inline) : Nat := (leaves (inlinesRaw #[] xs.toList)).size

/-- How many leaves the tree gives a block sequence. -/
def leafCountBlocks (bs : Array Block) : Nat := (leaves (blocksRaw #[] bs.toList)).size

/-- The outline headings, in preorder: every `.heading`'s level. An
`.aside` is a side channel and never ships a heading, as `headingLevels`
reads the speaker note it comes from — the one census that declines a
subtree, and it declines it by the classification, not by a walk of its
own. -/
def headingsFold : NodeFold (Array Nat) where
  leaf := fun out _ _ => out
  enter := Kind.outlineEmit
  descends := Kind.outlineDescends

def headingsList (out : Array Nat) (ns : List Node) : Array Nat := foldNodeList headingsFold out ns

def headingsOne (out : Array Nat) (n : Node) : Array Nat := foldNode headingsFold out n

def headings (ns : Array Node) : Array Nat := headingsList #[] ns.toList

def Tree.headings (t : Tree) : Array Nat := Struct.headings t.children

/-- Every non-text leaf's source and text alternative, in preorder. -/
def altsFold : NodeFold (Array (Option String × Alt)) where
  leaf := fun out _ l => l.altCensus out
  enter := fun out _ => out
  descends := fun _ => true

def altsList (out : Array (Option String × Alt)) (ns : List Node) : Array (Option String × Alt) :=
  foldNodeList altsFold out ns

def altsOne (out : Array (Option String × Alt)) (n : Node) : Array (Option String × Alt) :=
  foldNode altsFold out n

def alts (ns : Array Node) : Array (Option String × Alt) := altsList #[] ns.toList

def Tree.alts (t : Tree) : Array (Option String × Alt) := Struct.alts t.children

theorem leavesAppends : Appends leavesFold where
  leaf := by intros; simp [leavesFold]
  enter := by intros; simp [leavesFold]

theorem headingsAppends : Appends headingsFold where
  leaf := by intros; simp [headingsFold]
  enter := fun out kind => Kind.outlineEmit_acc out kind

/-- The IR's alternative census through the shared fold: every image's
source and alternative and every native picture's resolved alternative, in
document order. -/
def altPush (out : Array (Option String × Alt)) (x : Inline) : Array (Option String × Alt) :=
  match x with
  | .image src _ alt => out.push (some src, alt)
  | _ => out

def altPicPush (out : Array (Option String × Alt)) (b : Block) :
    Array (Option String × Alt) :=
  match b with
  | .picture pic => out.push (none, pic.alternative)
  | _ => out

def irAlts (bs : Array Block) : Array (Option String × Alt) :=
  foldBlocks altPicPush altPush #[] bs

-- **The censuses' interface**: the equations a prover may cite, stated. A
-- definition is not an interface — it becomes one the moment a downstream
-- proof unfolds it, and then the census cannot be refactored without
-- breaking a file that cannot see the change. So each census states the four
-- equations it is built from (nil, cons, leaf, node) and its entry point,
-- and every proof below — here and in `PdfStruct` — cites those rather than
-- the definitions. The outline's node equation reads the kind classification
-- rather than a kind pattern, so it fires on any kind with no hypothesis:
-- the two classifiers reduce, the match follows.

theorem leafTextList_nil_exact (acc : String) : leafTextList acc [] = acc := rfl

theorem leafTextList_cons_exact (acc : String) (n : Node) (rest : List Node) :
    leafTextList acc (n :: rest) = leafTextList (leafTextOne acc n) rest := rfl

theorem leafTextOne_leaf_exact (acc : String) (id : Nat) (l : Leaf) :
    leafTextOne acc (.leaf id l) = acc ++ l.census := rfl

theorem leafTextOne_node_exact (acc : String) (kind : Kind) (kids : Array Node) :
    leafTextOne acc (.node kind kids) = leafTextList acc kids.toList := rfl

theorem leafText_eq_exact (ns : Array Node) : leafText ns = leafTextList "" ns.toList := rfl

theorem leavesList_nil_exact (out : Array (Nat × Leaf)) : leavesList out [] = out := rfl

theorem leavesList_cons_exact (out : Array (Nat × Leaf)) (n : Node) (rest : List Node) :
    leavesList out (n :: rest) = leavesList (leavesOne out n) rest := rfl

theorem leavesOne_leaf_exact (out : Array (Nat × Leaf)) (id : Nat) (l : Leaf) :
    leavesOne out (.leaf id l) = out.push (id, l) := rfl

theorem leavesOne_node_exact (out : Array (Nat × Leaf)) (kind : Kind) (kids : Array Node) :
    leavesOne out (.node kind kids) = leavesList out kids.toList := rfl

theorem leaves_eq_exact (ns : Array Node) : leaves ns = leavesList #[] ns.toList := rfl

theorem headingsList_nil_exact (out : Array Nat) : headingsList out [] = out := rfl

theorem headingsList_cons_exact (out : Array Nat) (n : Node) (rest : List Node) :
    headingsList out (n :: rest) = headingsList (headingsOne out n) rest := rfl

theorem headingsOne_leaf_exact (out : Array Nat) (id : Nat) (l : Leaf) :
    headingsOne out (.leaf id l) = out := rfl

/-- The outline's descent equation, over any kind: the classification says
whether the content is read and what the node ships, so a citation names no
kind and carries no hypothesis. -/
theorem headingsOne_node_exact (out : Array Nat) (kind : Kind) (kids : Array Node) :
    headingsOne out (.node kind kids)
      = match kind.outlineDescends with
        | true => headingsList (kind.outlineEmit out) kids.toList
        | false => kind.outlineEmit out := rfl

theorem headingsOne_heading_exact (out : Array Nat) (level : Nat) (kids : Array Node) :
    headingsOne out (.node (.heading level) kids) = headingsList (out.push level) kids.toList :=
  rfl

theorem headingsOne_aside_exact (out : Array Nat) (kids : Array Node) :
    headingsOne out (.node .aside kids) = out := rfl

theorem headingsOne_through_exact (out : Array Nat) (kind : Kind) (kids : Array Node)
    (hh : ∀ level, kind ≠ .heading level) (ha : kind ≠ .aside) :
    headingsOne out (.node kind kids) = headingsList out kids.toList := by
  cases kind
  case heading level => exact absurd rfl (hh level)
  case aside => exact absurd rfl ha
  all_goals rfl

theorem headings_eq_exact (ns : Array Node) : headings ns = headingsList #[] ns.toList := rfl

theorem altsList_nil_exact (out : Array (Option String × Alt)) : altsList out [] = out := rfl

theorem altsList_cons_exact (out : Array (Option String × Alt)) (n : Node) (rest : List Node) :
    altsList out (n :: rest) = altsList (altsOne out n) rest := rfl

theorem altsOne_leaf_exact (out : Array (Option String × Alt)) (id : Nat) (l : Leaf) :
    altsOne out (.leaf id l) = l.altCensus out := rfl

theorem altsOne_node_exact (out : Array (Option String × Alt)) (kind : Kind) (kids : Array Node) :
    altsOne out (.node kind kids) = altsList out kids.toList := rfl

theorem alts_eq_exact (ns : Array Node) : alts ns = altsList #[] ns.toList := rfl

-- The census lemmas the projection theorems stand on: each census over an
-- appended list folds the halves in turn, so a pushed node is the census
-- of the array then of the node. Each is its census's instance of the one
-- argument stated over `foldNodeList` above.

theorem leafTextList_append (acc : String) (a b : List Node) :
    leafTextList acc (a ++ b) = leafTextList (leafTextList acc a) b :=
  foldNodeList_append leafTextFold acc a b

theorem leafTextList_snoc (acc : String) (l : List Node) (n : Node) :
    leafTextList acc (l ++ [n]) = leafTextOne (leafTextList acc l) n :=
  foldNodeList_snoc leafTextFold acc l n

theorem leafTextList_push (acc : String) (out : Array Node) (n : Node) :
    leafTextList acc (out.push n).toList = leafTextOne (leafTextList acc out.toList) n :=
  foldNodeList_push leafTextFold acc out n

theorem headingsList_append (out : Array Nat) (a b : List Node) :
    headingsList out (a ++ b) = headingsList (headingsList out a) b :=
  foldNodeList_append headingsFold out a b

theorem headingsList_snoc (out : Array Nat) (l : List Node) (n : Node) :
    headingsList out (l ++ [n]) = headingsOne (headingsList out l) n :=
  foldNodeList_snoc headingsFold out l n

theorem headingsList_push (out : Array Nat) (ns : Array Node) (n : Node) :
    headingsList out (ns.push n).toList = headingsOne (headingsList out ns.toList) n :=
  foldNodeList_push headingsFold out ns n

-- The accumulator extraction each projection proof needs of the outline
-- walk, in place of its equations: the generic argument at the census.

/-- The outline census builds onto its accumulator: the census of a list is
the accumulator, then the list's own — the fact a projection proof needs of
the walk, in place of its equations. -/
theorem headingsList_acc (out : Array Nat) (ns : List Node) :
    headingsList out ns = out ++ headingsList #[] ns :=
  foldNodeList_acc headingsAppends out ns

theorem headingsOne_acc (out : Array Nat) (n : Node) :
    headingsOne out n = out ++ headingsOne #[] n :=
  foldNode_acc headingsAppends out n

theorem altsList_append (out : Array (Option String × Alt)) (a b : List Node) :
    altsList out (a ++ b) = altsList (altsList out a) b :=
  foldNodeList_append altsFold out a b

theorem altsList_snoc (out : Array (Option String × Alt)) (l : List Node) (n : Node) :
    altsList out (l ++ [n]) = altsOne (altsList out l) n :=
  foldNodeList_snoc altsFold out l n

theorem altsList_push (out : Array (Option String × Alt)) (ns : Array Node) (n : Node) :
    altsList out (ns.push n).toList = altsOne (altsList out ns.toList) n :=
  foldNodeList_push altsFold out ns n

theorem leavesList_append (out : Array (Nat × Leaf)) (a b : List Node) :
    leavesList out (a ++ b) = leavesList (leavesList out a) b :=
  foldNodeList_append leavesFold out a b

theorem leavesList_snoc (out : Array (Nat × Leaf)) (l : List Node) (n : Node) :
    leavesList out (l ++ [n]) = leavesOne (leavesList out l) n :=
  foldNodeList_snoc leavesFold out l n

theorem leavesList_push (out : Array (Nat × Leaf)) (ns : Array Node) (n : Node) :
    leavesList out (ns.push n).toList = leavesOne (leavesList out ns.toList) n :=
  foldNodeList_push leavesFold out ns n

/-- An empty inline array has no list: the shape the empty-title and
empty-caption splits reduce to. -/
theorem toList_of_isEmpty (xs : Array Inline) (h : xs.isEmpty = true) : xs.toList = [] := by
  rw [Array.isEmpty_iff] at h
  rw [h]

-- **The tree's text is the IR's** (`structTree_text`). The projection drops
-- and invents no character: every leaf's census text in preorder is
-- `blocksText`, the same string the overlay and conditional walks
-- conserve. Stated with the accumulators generalized, one arm per
-- constructor, the inline walk first.

mutual

theorem inlinesRaw_text (acc : String) (out : Array Node) (xs : List Inline) :
    leafTextList acc (inlinesRaw out xs).toList
      = leafTextList acc out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [inlinesRaw, plainTextList]
  | x :: rest =>
    rw [inlinesRaw, inlinesRaw_text acc (inlineRaw out x) rest, inlineRaw_text acc out x,
      plainTextList, String.append_assoc]

theorem inlineRaw_text (acc : String) (out : Array Node) (x : Inline) :
    leafTextList acc (inlineRaw out x).toList
      = leafTextList acc out.toList ++ plainTextOne x := by
  match x with
  | .text s =>
    simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, Leaf.census, plainTextOne]
  | .math d src =>
    simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, leafTextOne_node_exact,
      leafTextList_nil_exact, leafTextList_cons_exact, Leaf.census, plainTextOne]
  | .formula d src body =>
    simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, leafTextOne_node_exact,
      leafTextList_nil_exact, leafTextList_cons_exact, Leaf.census, plainTextOne]
  | .styled style body =>
    match style with
    | .lang tag =>
      simp only [inlineRaw, leafTextList_push, leafTextOne_node_exact, plainTextOne]
      rw [inlinesRaw_text (leafTextList acc out.toList) #[] body.toList]
      rfl
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .size _ =>
      simp only [inlineRaw, plainTextOne]
      exact inlinesRaw_text acc out body.toList
  | .colored c n body =>
    simp only [inlineRaw, plainTextOne]
    exact inlinesRaw_text acc out body.toList
  | .role n body =>
    simp only [inlineRaw, plainTextOne]
    exact inlinesRaw_text acc out body.toList
  | .link url body =>
    simp only [inlineRaw, leafTextList_push, leafTextOne_node_exact, plainTextOne]
    rw [inlinesRaw_text (leafTextList acc out.toList) #[] body.toList]
    rfl
  | .label key => simp [inlineRaw, plainTextOne]
  | .ref key form text target =>
    simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, leafTextOne_node_exact,
      leafTextList_nil_exact, leafTextList_cons_exact, Leaf.census, plainTextOne]
  | .underline body =>
    simp only [inlineRaw, plainTextOne]
    exact inlinesRaw_text acc out body.toList
  | .fill => simp [inlineRaw, plainTextOne]
  | .pageNumber => simp [inlineRaw, plainTextOne]
  | .pageCount => simp [inlineRaw, plainTextOne]
  | .linebreak extra => simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, Leaf.census,
    plainTextOne]
  | .strut h => simp [inlineRaw, plainTextOne]
  | .italicCorr m => simp [inlineRaw, plainTextOne]
  | .step n l body =>
    simp only [inlineRaw, plainTextOne]
    exact inlinesRaw_text acc out body.toList
  | .alt n l active otherwise =>
    simp only [inlineRaw, plainTextOne]
    rw [inlinesRaw_text acc (inlinesRaw out active.toList) otherwise.toList,
      inlinesRaw_text acc out active.toList, String.append_assoc]
  | .image src size alt =>
    simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, Leaf.census, plainTextOne]
  | .icon sc label => simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, Leaf.census,
    plainTextOne]
  | .cite tx keys => simp [inlineRaw, leafTextList_snoc, leafTextOne_leaf_exact, Leaf.census,
    plainTextOne]
  | .footnote num body =>
    simp only [inlineRaw, leafTextList_push, leafTextOne_node_exact, plainTextOne]
    rw [inlinesRaw_text (leafTextList acc out.toList) #[] body.toList]
    rfl

end

/-- Inline content built onto an empty accumulator: its census is exactly
the content's plain text — the shape every node-opening arm reduces to. -/
theorem inlinesRaw_text_nil (acc : String) (xs : Array Inline) :
    leafTextList acc (inlinesRaw #[] xs.toList).toList = acc ++ plainText xs := by
  rw [inlinesRaw_text]
  rfl

theorem titleRaw_text (acc : String) (title : Array Inline) :
    leafTextList acc (titleRaw title).toList = acc ++ plainText title := by
  unfold titleRaw
  split
  · rename_i h
    simp [plainText, toList_of_isEmpty title h, plainTextList, leafTextList_nil_exact]
  · simp only [leafTextList_nil_exact, leafTextList_cons_exact, leafTextOne_node_exact]
    exact inlinesRaw_text_nil acc title

theorem captionRaw_text (acc : String) (caption : Array Inline) :
    leafTextList acc (captionRaw caption).toList = acc ++ plainText caption := by
  unfold captionRaw
  split
  · rename_i h
    simp [plainText, toList_of_isEmpty caption h, plainTextList, leafTextList_nil_exact]
  · simp only [leafTextList_nil_exact, leafTextList_cons_exact, leafTextOne_node_exact]
    exact inlinesRaw_text_nil acc caption

theorem cellsRaw_text (acc : String) (out : Array Node) (cells : List (Array Inline)) :
    leafTextList acc (cellsRaw out cells).toList
      = blockTextTableCells (leafTextList acc out.toList) cells := by
  induction cells generalizing out with
  | nil => rfl
  | cons cell rest ih =>
    rw [cellsRaw, ih, leafTextList_push, blockTextTableCells]
    simp only [leafTextOne_node_exact]
    rw [inlinesRaw_text_nil]

theorem rowsRaw_text (acc : String) (out : Array Node) (rows : List (Array (Array Inline))) :
    leafTextList acc (rowsRaw out rows).toList
      = blockTextTableRows (leafTextList acc out.toList) rows := by
  induction rows generalizing out with
  | nil => rfl
  | cons row rest ih =>
    rw [rowsRaw, ih, leafTextList_push, blockTextTableRows]
    simp only [leafTextOne_node_exact]
    rw [cellsRaw_text]
    rfl

theorem bibRaw_text (acc : String) (out : Array Node) (items : List BibItem) :
    leafTextList acc (bibRaw out items).toList
      = blockTextBibItems (leafTextList acc out.toList) items := by
  induction items generalizing out with
  | nil => rfl
  | cons item rest ih =>
    rw [bibRaw, ih, leafTextList_push, blockTextBibItems]
    simp [leafTextOne_leaf_exact, leafTextOne_node_exact, leafTextList_nil_exact,
      leafTextList_cons_exact, Leaf.census]

theorem algRaw_text (acc : String) (out : Array Node) (lines : List AlgLine) :
    leafTextList acc (algRaw out lines).toList
      = algLineText (leafTextList acc out.toList) lines := by
  induction lines generalizing out with
  | nil => rfl
  | cons l rest ih =>
    rw [algRaw, ih, algLineText]
    cases l.comment with
    | none => simp only [inlinesRaw_text, plainText]
    | some c => simp only [inlinesRaw_text, plainText]

mutual

theorem blocksRaw_text (acc : String) (out : Array Node) (bs : List Block) :
    leafTextList acc (blocksRaw out bs).toList
      = blockTextList (leafTextList acc out.toList) bs := by
  match bs with
  | [] => rfl
  | b :: rest =>
    rw [blocksRaw, blocksRaw_text acc (blockRaw out b) rest, blockRaw_text acc out b,
      blockTextList]

theorem blockRaw_text (acc : String) (out : Array Node) (b : Block) :
    leafTextList acc (blockRaw out b).toList
      = blockTextOne (leafTextList acc out.toList) b := by
  match b with
  | .para content =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    exact inlinesRaw_text_nil _ content
  | .section level st num title =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    exact inlinesRaw_text_nil _ title
  | .list ordered items =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [itemsRaw_text]
    rfl
  | .center body =>
    simp only [blockRaw, blockTextOne]
    exact blocksRaw_text acc out body.toList
  | .ragged _ body =>
    simp only [blockRaw, blockTextOne]
    exact blocksRaw_text acc out body.toList
  | .spaced g body =>
    simp only [blockRaw, blockTextOne]
    exact blocksRaw_text acc out body.toList
  | .role n body =>
    simp only [blockRaw, blockTextOne]
    exact blocksRaw_text acc out body.toList
  | .quote body =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [blocksRaw_text]
    rfl
  | .abstract body =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [blocksRaw_text]
    rfl
  | .titled kind title body =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [blocksRaw_text, titleRaw_text]
  | .equation number content =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [inlinesRaw_text_nil, inlinesRaw_text_nil]
  | .verbatim covered content spec =>
    simp only [blockRaw, blockTextOne]
    split
    · rename_i n cap h
      simp [leafTextList_snoc, leafTextOne_leaf_exact, leafTextOne_node_exact,
        leafTextList_nil_exact, leafTextList_cons_exact, Leaf.census, ListingSpec.capText, h]
    · rename_i h
      simp [leafTextList_snoc, leafTextOne_leaf_exact, leafTextOne_node_exact,
        leafTextList_nil_exact, leafTextList_cons_exact, Leaf.census, ListingSpec.capText, h]
  | .algorithm n sm lines =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [algRaw_text]
    rfl
  | .columns cols =>
    simp only [blockRaw, blockTextOne]
    exact colsRaw_text acc out cols.toList
  | .step n l body =>
    simp only [blockRaw, blockTextOne]
    exact blocksRaw_text acc out body.toList
  | .alt n l active otherwise =>
    simp only [blockRaw, blockTextOne]
    rw [blocksRaw_text acc (blocksRaw out active.toList) otherwise.toList,
      blocksRaw_text acc out active.toList]
  | .note body =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [blocksRaw_text]
    rfl
  | .only targets body =>
    simp only [blockRaw, blockTextOne]
    exact blocksRaw_text acc out body.toList
  | .nav spec body =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [blocksRaw_text]
    rfl
  | .logo content =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    exact inlinesRaw_text_nil _ content
  | .pagebreak => simp [blockRaw, blockTextOne]
  | .frame title st v _ body =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [blocksRaw_text, titleRaw_text]
  | .framefoot content =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    exact inlinesRaw_text_nil _ content
  | .setPalette pal => simp [blockRaw, blockTextOne]
  | .setTokens tk => simp [blockRaw, blockTextOne]
  | .rule c n th => simp [blockRaw, blockTextOne]
  | .picture pic =>
    simp [blockRaw, leafTextList_snoc, leafTextOne_leaf_exact, Leaf.census, blockTextOne]
  | .table cols pl pr rows rules spans =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [rowsRaw_text]
    rfl
  | .float k n ca body caption =>
    simp only [blockRaw, leafTextList_push, leafTextOne_node_exact, blockTextOne]
    rw [blocksRaw_text, captionRaw_text]
  | .bibliography src style items =>
    simp only [blockRaw, blockTextOne]
    exact bibRaw_text acc out items.toList

theorem itemsRaw_text (acc : String) (out : Array Node) (items : List (Array Block)) :
    leafTextList acc (itemsRaw out items).toList
      = blockTextItems (leafTextList acc out.toList) items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [itemsRaw, itemsRaw_text acc _ rest, leafTextList_push, blockTextItems]
    simp only [leafTextOne_node_exact, leafTextList_nil_exact, leafTextList_cons_exact]
    rw [blocksRaw_text]
    rfl

theorem colsRaw_text (acc : String) (out : Array Node) (cols : List (BoxWidth × Array Block)) :
    leafTextList acc (colsRaw out cols).toList
      = blockTextColumns (leafTextList acc out.toList) cols := by
  match cols with
  | [] => rfl
  | (w, body) :: rest =>
    rw [colsRaw, colsRaw_text acc _ rest, blocksRaw_text, blockTextColumns]

end

-- Numbering is markup: the pass rewrites ids and nothing else, so every
-- census over the shape is fixed under it. Structural recursion through
-- `List`, the numbering's own shape.

mutual

theorem numberList_text (acc : String) (k : Nat) (out : Array Node) (ns : List Node) :
    leafTextList acc (numberList k out ns).1.toList
      = leafTextList (leafTextList acc out.toList) ns := by
  match ns with
  | [] => rfl
  | n :: rest =>
    rw [numberList, leafTextList_cons_exact, numberList_text acc _ _ rest, leafTextList_push,
      numberOne_text]

theorem numberOne_text (acc : String) (k : Nat) (n : Node) :
    leafTextOne acc (numberOne k n).1 = leafTextOne acc n := by
  match n with
  | .leaf id l => rfl
  | .node kind kids =>
    simp only [numberOne, leafTextOne_node_exact]
    rw [numberList_text]
    rfl

end

/-- **Numbering conserves the text**: the ids pass is a `Conserves`
instance over the tree's own census. -/
theorem number_text (k : Nat) : Conserves leafText (number k) := fun ns => by
  rw [leafText_eq_exact, leafText_eq_exact, number, numberList_text]
  rfl

/-- **The tree's text is the IR's.** The projection of a block sequence has
exactly `blocksText`'s characters in its leaves, in preorder: nothing
dropped, nothing invented, the ids added on top. The census equality of
the `_text` shape; not a `Conserves` instance itself because the walk is
IR → tree, not IR → IR — `number_text` is the instance the tree-side pass
owes, and `structTree_text` composes it with the raw walk's equality. -/
theorem structTree_text (bs : Array Block) : leafText (ofBlocks bs) = blocksText bs := by
  unfold ofBlocks
  rw [number_text, leafText, blocksRaw_text]
  rfl

/-- The document face: the tree's text is the body's. -/
theorem ofDoc_text (doc : Doc) : (ofDoc doc).text = blocksText doc.body :=
  structTree_text doc.body

-- **The outline is the IR's** (`structTree_headings_covers`): the tree's
-- `.heading` levels in preorder are `headingLevels`. Inline content opens
-- no heading, so the inline walk is fixed; the block walk mirrors
-- `headingLevelOne` arm for arm.

mutual

theorem inlinesRaw_headings (hs : Array Nat) (out : Array Node) (xs : List Inline) :
    headingsList hs (inlinesRaw out xs).toList = headingsList hs out.toList := by
  match xs with
  | [] => rfl
  | x :: rest =>
    rw [inlinesRaw, inlinesRaw_headings hs (inlineRaw out x) rest, inlineRaw_headings]

theorem inlineRaw_headings (hs : Array Nat) (out : Array Node) (x : Inline) :
    headingsList hs (inlineRaw out x).toList = headingsList hs out.toList := by
  match x with
  | .text s => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact]
  | .math d src => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact,
    headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit, headingsList_nil_exact,
    headingsList_cons_exact]
  | .formula d src body => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact,
    headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit, headingsList_nil_exact,
    headingsList_cons_exact]
  | .styled style body =>
    match style with
    | .lang tag =>
      simp only [inlineRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
        Kind.outlineEmit]
      rw [inlinesRaw_headings]
      rfl
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .size _ =>
      simp only [inlineRaw]
      exact inlinesRaw_headings hs out body.toList
  | .colored c n body =>
    simp only [inlineRaw]
    exact inlinesRaw_headings hs out body.toList
  | .role n body =>
    simp only [inlineRaw]
    exact inlinesRaw_headings hs out body.toList
  | .link url body =>
    simp only [inlineRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit]
    rw [inlinesRaw_headings]
    rfl
  | .label key => rfl
  | .ref key form text target => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact,
    headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit, headingsList_nil_exact,
    headingsList_cons_exact]
  | .underline body =>
    simp only [inlineRaw]
    exact inlinesRaw_headings hs out body.toList
  | .fill => rfl
  | .pageNumber => rfl
  | .pageCount => rfl
  | .linebreak extra => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact]
  | .strut h => rfl
  | .italicCorr m => rfl
  | .step n l body =>
    simp only [inlineRaw]
    exact inlinesRaw_headings hs out body.toList
  | .alt n l active otherwise =>
    simp only [inlineRaw]
    rw [inlinesRaw_headings hs (inlinesRaw out active.toList) otherwise.toList,
      inlinesRaw_headings hs out active.toList]
  | .image src size alt => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact]
  | .icon sc label => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact]
  | .cite tx keys => simp [inlineRaw, headingsList_snoc, headingsOne_leaf_exact]
  | .footnote num body =>
    simp only [inlineRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit]
    rw [inlinesRaw_headings]
    rfl

end

theorem inlinesRaw_headings_nil (hs : Array Nat) (xs : Array Inline) :
    headingsList hs (inlinesRaw #[] xs.toList).toList = hs := by
  rw [inlinesRaw_headings]
  rfl

theorem titleRaw_headings (hs : Array Nat) (title : Array Inline) :
    headingsList hs (titleRaw title).toList = hs := by
  unfold titleRaw
  split
  · rfl
  · simp only [headingsList_nil_exact, headingsList_cons_exact, headingsOne_node_exact,
    Kind.outlineDescends, Kind.outlineEmit]
    exact inlinesRaw_headings_nil hs title

theorem captionRaw_headings (hs : Array Nat) (caption : Array Inline) :
    headingsList hs (captionRaw caption).toList = hs := by
  unfold captionRaw
  split
  · rfl
  · simp only [headingsList_nil_exact, headingsList_cons_exact, headingsOne_node_exact,
    Kind.outlineDescends, Kind.outlineEmit]
    exact inlinesRaw_headings_nil hs caption

theorem cellsRaw_headings (hs : Array Nat) (out : Array Node) (cells : List (Array Inline)) :
    headingsList hs (cellsRaw out cells).toList = headingsList hs out.toList := by
  induction cells generalizing out with
  | nil => rfl
  | cons cell rest ih =>
    rw [cellsRaw, ih, headingsList_push]
    simp only [headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit]
    rw [inlinesRaw_headings_nil]

theorem rowsRaw_headings (hs : Array Nat) (out : Array Node) (rows : List (Array (Array Inline))) :
    headingsList hs (rowsRaw out rows).toList = headingsList hs out.toList := by
  induction rows generalizing out with
  | nil => rfl
  | cons row rest ih =>
    rw [rowsRaw, ih, headingsList_push]
    simp only [headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit]
    rw [cellsRaw_headings]
    rfl

theorem bibRaw_headings (hs : Array Nat) (out : Array Node) (items : List BibItem) :
    headingsList hs (bibRaw out items).toList = headingsList hs out.toList := by
  induction items generalizing out with
  | nil => rfl
  | cons item rest ih =>
    rw [bibRaw, ih, headingsList_push]
    simp [headingsOne_leaf_exact, headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit,
      headingsList_nil_exact, headingsList_cons_exact]

theorem algRaw_headings (hs : Array Nat) (out : Array Node) (lines : List AlgLine) :
    headingsList hs (algRaw out lines).toList = headingsList hs out.toList := by
  induction lines generalizing out with
  | nil => rfl
  | cons l rest ih =>
    rw [algRaw, ih]
    cases l.comment with
    | none => simp only [inlinesRaw_headings]
    | some c => simp only [inlinesRaw_headings]

mutual

theorem blocksRaw_headings (hs : Array Nat) (out : Array Node) (bs : List Block) :
    headingsList hs (blocksRaw out bs).toList
      = headingLevelList (headingsList hs out.toList) bs := by
  match bs with
  | [] => rfl
  | b :: rest =>
    rw [blocksRaw, blocksRaw_headings hs (blockRaw out b) rest, blockRaw_headings hs out b,
      headingLevelList]

theorem blockRaw_headings (hs : Array Nat) (out : Array Node) (b : Block) :
    headingsList hs (blockRaw out b).toList
      = headingLevelOne (headingsList hs out.toList) b := by
  match b with
  | .para content =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    exact inlinesRaw_headings_nil _ content
  | .section level st num title =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    exact inlinesRaw_headings_nil _ title
  | .list ordered items =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [itemsRaw_headings]
    rfl
  | .center body =>
    simp only [blockRaw, headingLevelOne]
    exact blocksRaw_headings hs out body.toList
  | .ragged _ body =>
    simp only [blockRaw, headingLevelOne]
    exact blocksRaw_headings hs out body.toList
  | .spaced g body =>
    simp only [blockRaw, headingLevelOne]
    exact blocksRaw_headings hs out body.toList
  | .role n body =>
    simp only [blockRaw, headingLevelOne]
    exact blocksRaw_headings hs out body.toList
  | .quote body =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [blocksRaw_headings]
    rfl
  | .abstract body =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [blocksRaw_headings]
    rfl
  | .titled kind title body =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [blocksRaw_headings, titleRaw_headings]
  | .equation number content =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [inlinesRaw_headings_nil]
    simp [inlinesRaw_headings_nil]
  | .verbatim covered content spec =>
    simp only [blockRaw, headingLevelOne]
    split
    · simp [headingsList_snoc, headingsOne_leaf_exact, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingsList_nil_exact, headingsList_cons_exact]
    · simp [headingsList_snoc, headingsOne_leaf_exact, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingsList_nil_exact, headingsList_cons_exact]
  | .algorithm n sm lines =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [algRaw_headings]
    rfl
  | .columns cols =>
    simp only [blockRaw, headingLevelOne]
    exact colsRaw_headings hs out cols.toList
  | .step n l body =>
    simp only [blockRaw, headingLevelOne]
    exact blocksRaw_headings hs out body.toList
  | .alt n l active otherwise =>
    simp only [blockRaw, headingLevelOne]
    rw [blocksRaw_headings hs (blocksRaw out active.toList) otherwise.toList,
      blocksRaw_headings hs out active.toList]
  | .note body => simp [blockRaw, headingsList_snoc, headingsOne_node_exact, Kind.outlineDescends,
    Kind.outlineEmit, headingLevelOne]
  | .only targets body =>
    simp only [blockRaw, headingLevelOne]
    exact blocksRaw_headings hs out body.toList
  | .nav spec body =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [blocksRaw_headings]
    rfl
  | .logo content =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    exact inlinesRaw_headings_nil _ content
  | .pagebreak => rfl
  | .frame title st v _ body =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [blocksRaw_headings, titleRaw_headings]
  | .framefoot content =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    exact inlinesRaw_headings_nil _ content
  | .setPalette pal => rfl
  | .setTokens tk => rfl
  | .rule c n th => rfl
  | .picture pic => simp [blockRaw, headingsList_snoc, headingsOne_leaf_exact, headingLevelOne]
  | .table cols pl pr rows rules spans =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [rowsRaw_headings]
    rfl
  | .float k n ca body caption =>
    simp only [blockRaw, headingsList_push, headingsOne_node_exact, Kind.outlineDescends,
      Kind.outlineEmit, headingLevelOne]
    rw [blocksRaw_headings, captionRaw_headings]
  | .bibliography src style items =>
    simp only [blockRaw, headingLevelOne]
    exact bibRaw_headings hs out items.toList

theorem itemsRaw_headings (hs : Array Nat) (out : Array Node) (items : List (Array Block)) :
    headingsList hs (itemsRaw out items).toList
      = headingLevelItems (headingsList hs out.toList) items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [itemsRaw, itemsRaw_headings hs _ rest, headingsList_push, headingLevelItems]
    simp only [headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit,
      headingsList_nil_exact, headingsList_cons_exact]
    rw [blocksRaw_headings]
    rfl

theorem colsRaw_headings (hs : Array Nat) (out : Array Node)
    (cols : List (BoxWidth × Array Block)) :
    headingsList hs (colsRaw out cols).toList
      = headingLevelColumns (headingsList hs out.toList) cols := by
  match cols with
  | [] => rfl
  | (w, body) :: rest =>
    rw [colsRaw, colsRaw_headings hs _ rest, blocksRaw_headings, headingLevelColumns]

end

mutual

theorem numberList_headings (hs : Array Nat) (k : Nat) (out : Array Node) (ns : List Node) :
    headingsList hs (numberList k out ns).1.toList
      = headingsList (headingsList hs out.toList) ns := by
  match ns with
  | [] => rfl
  | n :: rest =>
    rw [numberList, headingsList_cons_exact, numberList_headings hs _ _ rest, headingsList_push,
      numberOne_headings]

theorem numberOne_headings (hs : Array Nat) (k : Nat) (n : Node) :
    headingsOne hs (numberOne k n).1 = headingsOne hs n := by
  match n with
  | .leaf id l => rfl
  | .node kind kids =>
    simp only [numberOne, headingsOne_node_exact, Kind.outlineDescends, Kind.outlineEmit]
    split <;> first | rfl | (rw [numberList_headings]; rfl)

end

/-- **The outline is the IR's.** The tree's heading levels in preorder are
exactly `headingLevels`: every `\section` at its level, in order, and no
heading the outline does not know — the fact the outline diagnostics, the
markdown preamble, and a tagger's `H<n>` sequence all read. -/
theorem structTree_headings_covers (bs : Array Block) :
    headings (ofBlocks bs) = headingLevels bs := by
  unfold ofBlocks headingLevels
  rw [headings_eq_exact, number, numberList_headings, blocksRaw_headings]
  rfl

-- **The alternatives are the IR's** (`structTree_alts_covers`): the
-- structure leaves and shared fold carry the same image sources and native
-- picture alternatives, in document order. The projection walk therefore
-- descends everywhere the fold does (footnotes, roles, columns, cells), and
-- no alternative-bearing leaf is attributed nowhere.

mutual

theorem inlinesRaw_alts (is : Array (Option String × Alt)) (out : Array Node) (xs : List Inline) :
    altsList is (inlinesRaw out xs).toList
      = foldInlineList altPush (altsList is out.toList) xs := by
  match xs with
  | [] => rfl
  | x :: rest =>
    rw [inlinesRaw, inlinesRaw_alts is (inlineRaw out x) rest, inlineRaw_alts,
      foldInlineList]

theorem inlineRaw_alts (is : Array (Option String × Alt)) (out : Array Node) (x : Inline) :
    altsList is (inlineRaw out x).toList = foldInline altPush (altsList is out.toList) x := by
  match x with
  | .text s => simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, Leaf.altCensus, foldInline,
    altPush]
  | .math d src =>
    simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, altsOne_node_exact, Leaf.altCensus,
      altsList_nil_exact, altsList_cons_exact, foldInline, altPush]
  | .formula d src body =>
    simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, altsOne_node_exact, Leaf.altCensus,
      altsList_nil_exact, altsList_cons_exact, foldInline, altPush]
  | .styled style body =>
    match style with
    | .lang tag =>
      simp only [inlineRaw, altsList_push, altsOne_node_exact, foldInline, altPush]
      rw [inlinesRaw_alts]
      rfl
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .size _ =>
      simp only [inlineRaw, foldInline, altPush]
      exact inlinesRaw_alts is out body.toList
  | .colored c n body =>
    simp only [inlineRaw, foldInline, altPush]
    exact inlinesRaw_alts is out body.toList
  | .role n body =>
    simp only [inlineRaw, foldInline, altPush]
    exact inlinesRaw_alts is out body.toList
  | .link url body =>
    simp only [inlineRaw, altsList_push, altsOne_node_exact, foldInline, altPush]
    rw [inlinesRaw_alts]
    rfl
  | .label key => simp [inlineRaw, foldInline, altPush]
  | .ref key form text target =>
    simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, altsOne_node_exact, Leaf.altCensus,
      altsList_nil_exact, altsList_cons_exact, foldInline, altPush]
  | .underline body =>
    simp only [inlineRaw, foldInline, altPush]
    exact inlinesRaw_alts is out body.toList
  | .fill => simp [inlineRaw, foldInline, altPush]
  | .pageNumber => simp [inlineRaw, foldInline, altPush]
  | .pageCount => simp [inlineRaw, foldInline, altPush]
  | .linebreak extra => simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, Leaf.altCensus,
    foldInline, altPush]
  | .strut h => simp [inlineRaw, foldInline, altPush]
  | .italicCorr m => simp [inlineRaw, foldInline, altPush]
  | .step n l body =>
    simp only [inlineRaw, foldInline, altPush]
    exact inlinesRaw_alts is out body.toList
  | .alt n l active otherwise =>
    simp only [inlineRaw, foldInline, altPush]
    rw [inlinesRaw_alts is (inlinesRaw out active.toList) otherwise.toList,
      inlinesRaw_alts is out active.toList]
  | .image src size alt => simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, Leaf.altCensus,
    foldInline, altPush]
  | .icon sc label => simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, Leaf.altCensus,
    foldInline, altPush]
  | .cite tx keys => simp [inlineRaw, altsList_snoc, altsOne_leaf_exact, Leaf.altCensus,
    foldInline, altPush]
  | .footnote num body =>
    simp only [inlineRaw, altsList_push, altsOne_node_exact, foldInline, altPush]
    rw [inlinesRaw_alts]
    rfl

end

theorem inlinesRaw_alts_nil (is : Array (Option String × Alt)) (xs : Array Inline) :
    altsList is (inlinesRaw #[] xs.toList).toList = foldInlineList altPush is xs.toList := by
  rw [inlinesRaw_alts]
  rfl

theorem titleRaw_alts (is : Array (Option String × Alt)) (title : Array Inline) :
    altsList is (titleRaw title).toList = foldInlineList altPush is title.toList := by
  unfold titleRaw
  split
  · rename_i h
    rw [toList_of_isEmpty title h]
    rfl
  · simp only [altsList_nil_exact, altsList_cons_exact, altsOne_node_exact]
    exact inlinesRaw_alts_nil is title

theorem captionRaw_alts (is : Array (Option String × Alt)) (caption : Array Inline) :
    altsList is (captionRaw caption).toList = foldInlineList altPush is caption.toList := by
  unfold captionRaw
  split
  · rename_i h
    rw [toList_of_isEmpty caption h]
    rfl
  · simp only [altsList_nil_exact, altsList_cons_exact, altsOne_node_exact]
    exact inlinesRaw_alts_nil is caption

theorem cellsRaw_alts (is : Array (Option String × Alt)) (out : Array Node)
    (cells : List (Array Inline)) :
    altsList is (cellsRaw out cells).toList
      = foldTableCells altPush (altsList is out.toList) cells := by
  induction cells generalizing out with
  | nil => rfl
  | cons cell rest ih =>
    rw [cellsRaw, ih, altsList_push, foldTableCells]
    simp only [altsOne_node_exact]
    rw [inlinesRaw_alts_nil]

theorem rowsRaw_alts (is : Array (Option String × Alt)) (out : Array Node)
    (rows : List (Array (Array Inline))) :
    altsList is (rowsRaw out rows).toList
      = foldTableRows altPush (altsList is out.toList) rows := by
  induction rows generalizing out with
  | nil => rfl
  | cons row rest ih =>
    rw [rowsRaw, ih, altsList_push, foldTableRows]
    simp only [altsOne_node_exact]
    rw [cellsRaw_alts]
    rfl

theorem bibRaw_alts (is : Array (Option String × Alt)) (out : Array Node) (items : List BibItem) :
    altsList is (bibRaw out items).toList = altsList is out.toList := by
  induction items generalizing out with
  | nil => rfl
  | cons item rest ih =>
    rw [bibRaw, ih, altsList_push]
    simp [altsOne_leaf_exact, altsOne_node_exact, Leaf.altCensus, altsList_nil_exact,
      altsList_cons_exact]

theorem algRaw_alts (is : Array (Option String × Alt)) (out : Array Node) (lines : List AlgLine) :
    altsList is (algRaw out lines).toList
      = foldAlgLines altPush (altsList is out.toList) lines := by
  induction lines generalizing out with
  | nil => rfl
  | cons l rest ih =>
    rw [algRaw, ih, foldAlgLines]
    cases l.comment with
    | none => simp only [inlinesRaw_alts]
    | some c => simp only [inlinesRaw_alts]

mutual

theorem blocksRaw_alts (is : Array (Option String × Alt)) (out : Array Node) (bs : List Block) :
    altsList is (blocksRaw out bs).toList
      = foldBlockList altPicPush altPush (altsList is out.toList) bs := by
  match bs with
  | [] => rfl
  | b :: rest =>
    rw [blocksRaw, blocksRaw_alts is (blockRaw out b) rest, blockRaw_alts is out b,
      foldBlockList]

theorem blockRaw_alts (is : Array (Option String × Alt)) (out : Array Node) (b : Block) :
    altsList is (blockRaw out b).toList
      = foldBlock altPicPush altPush (altsList is out.toList) b := by
  match b with
  | .para content =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    exact inlinesRaw_alts_nil _ content
  | .section level st num title =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    exact inlinesRaw_alts_nil _ title
  | .list ordered items =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [itemsRaw_alts]
    rfl
  | .center body =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact blocksRaw_alts is out body.toList
  | .ragged _ body =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact blocksRaw_alts is out body.toList
  | .spaced g body =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact blocksRaw_alts is out body.toList
  | .role n body =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact blocksRaw_alts is out body.toList
  | .quote body =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [blocksRaw_alts]
    rfl
  | .abstract body =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [blocksRaw_alts]
    rfl
  | .titled kind title body =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [blocksRaw_alts, titleRaw_alts]
  | .equation number content =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [inlinesRaw_alts_nil]
    simp [inlinesRaw_alts_nil]
  | .verbatim covered content spec =>
    simp only [blockRaw, foldBlock, altPicPush]
    split
    · simp [altsList_snoc, altsOne_leaf_exact, altsOne_node_exact, Leaf.altCensus,
      altsList_nil_exact, altsList_cons_exact]
    · simp [altsList_snoc, altsOne_leaf_exact, altsOne_node_exact, Leaf.altCensus,
      altsList_nil_exact, altsList_cons_exact]
  | .algorithm n sm lines =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [algRaw_alts]
    rfl
  | .columns cols =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact colsRaw_alts is out cols.toList
  | .step n l body =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact blocksRaw_alts is out body.toList
  | .alt n l active otherwise =>
    simp only [blockRaw, foldBlock, altPicPush]
    rw [blocksRaw_alts is (blocksRaw out active.toList) otherwise.toList,
      blocksRaw_alts is out active.toList]
  | .note body =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [blocksRaw_alts]
    rfl
  | .only targets body =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact blocksRaw_alts is out body.toList
  | .nav spec body =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [blocksRaw_alts]
    rfl
  | .logo content =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    exact inlinesRaw_alts_nil _ content
  | .pagebreak => rfl
  | .frame title st v _ body =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [blocksRaw_alts, titleRaw_alts]
  | .framefoot content =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    exact inlinesRaw_alts_nil _ content
  | .setPalette pal => rfl
  | .setTokens tk => rfl
  | .rule c n th => rfl
  | .picture pic => simp [blockRaw, altsList_snoc, altsOne_leaf_exact, Leaf.altCensus,
    foldBlock, altPicPush]
  | .table cols pl pr rows rules spans =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [rowsRaw_alts]
    rfl
  | .float k n ca body caption =>
    simp only [blockRaw, altsList_push, altsOne_node_exact, foldBlock, altPicPush]
    rw [blocksRaw_alts, captionRaw_alts]
  | .bibliography src style items =>
    simp only [blockRaw, foldBlock, altPicPush]
    exact bibRaw_alts is out items.toList

theorem itemsRaw_alts (is : Array (Option String × Alt)) (out : Array Node)
    (items : List (Array Block)) :
    altsList is (itemsRaw out items).toList
      = foldBlockItems altPicPush altPush (altsList is out.toList) items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [itemsRaw, itemsRaw_alts is _ rest, altsList_push, foldBlockItems]
    simp only [altsOne_node_exact, altsList_nil_exact, altsList_cons_exact]
    rw [blocksRaw_alts]
    rfl

theorem colsRaw_alts (is : Array (Option String × Alt)) (out : Array Node)
    (cols : List (BoxWidth × Array Block)) :
    altsList is (colsRaw out cols).toList
      = foldBlockCols altPicPush altPush (altsList is out.toList) cols := by
  match cols with
  | [] => rfl
  | (w, body) :: rest =>
    rw [colsRaw, colsRaw_alts is _ rest, blocksRaw_alts, foldBlockCols]

end

mutual

theorem numberList_alts (is : Array (Option String × Alt)) (k : Nat) (out : Array Node)
    (ns : List Node) :
    altsList is (numberList k out ns).1.toList
      = altsList (altsList is out.toList) ns := by
  match ns with
  | [] => rfl
  | n :: rest =>
    rw [numberList, altsList_cons_exact, numberList_alts is _ _ rest, altsList_push,
      numberOne_alts]

theorem numberOne_alts (is : Array (Option String × Alt)) (k : Nat) (n : Node) :
    altsOne is (numberOne k n).1 = altsOne is n := by
  match n with
  | .leaf id l => rfl
  | .node kind kids =>
    simp only [numberOne, altsOne_node_exact]
    rw [numberList_alts]
    rfl

end

/-- **The alternatives are the IR's.** Every image and native-picture
leaf of the structure tree, source where one exists and resolved
alternative, is exactly the shared fold's whole-document census. -/
theorem structTree_alts_covers (bs : Array Block) : alts (ofBlocks bs) = irAlts bs := by
  unfold ofBlocks irAlts foldBlocks
  rw [alts_eq_exact, number, numberList_alts, blocksRaw_alts]
  rfl

-- **Ids are the preorder index** (`structTree_leaves_id`): the k-th leaf
-- in preorder carries `k`, so the attribution channel's `Option Nat` and a
-- tagger's `/K` both index one array.

/-- `leaves` builds onto its accumulator: the census of a list is the
accumulator, then the list's own. -/
theorem leavesList_acc (out : Array (Nat × Leaf)) (ns : List Node) :
    leavesList out ns = out ++ leavesList #[] ns :=
  foldNodeList_acc leavesAppends out ns

theorem leavesOne_acc (out : Array (Nat × Leaf)) (n : Node) :
    leavesOne out n = out ++ leavesOne #[] n :=
  foldNode_acc leavesAppends out n

/-- `numberList` builds onto its accumulator and counts independently of it. -/
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

/-- Two adjacent ranges join: the numbering's induction step. -/
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

/-- **Ids are the preorder index.** The leaves of a projected block
sequence, in preorder, carry `0, 1, …, n − 1`: the k-th leaf is the one
whose id is `k`, so `leaves t` is the one array the attribution channel's
`Option Nat` and a tagger's marked-content keys both index. -/
theorem structTree_leaves_id (bs : Array Block) :
    (leaves (ofBlocks bs)).toList.map Prod.fst = List.range (leaves (ofBlocks bs)).size := by
  unfold ofBlocks number
  rw [leaves_eq_exact]
  obtain ⟨h, _⟩ := numberList_id 0 (blocksRaw #[] bs.toList).toList
  rw [List.range_eq_range', h]
  congr 1
  have := congrArg List.length h
  simp only [List.length_map, Array.length_toList, List.length_range'] at this
  omega

-- **A group's ids are the tree's** (`alt_leaf_projects`): where one node
-- holds two alternatives and a page ships only one of them, the id the page
-- references must be the one the tree assigned that alternative. The
-- projection walks build onto their accumulator, so an alternation's node
-- array is its two groups' arrays appended; numbering an append numbers the
-- halves in turn; so the second group's ids begin exactly its sibling's leaf
-- count later. That offset is what a page steps over, and stepping over it is
-- what makes the reference a projection rather than a fresh mint.

mutual

/-- `inlinesRaw` builds onto its accumulator. -/
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
    | .medium | .series _ | .upright | .size _ =>
      simp only [inlineRaw]
      exact inlinesRaw_acc out body.toList
  | .colored c n body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .role n body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .link url body => simp [inlineRaw]
  | .label key => simp [inlineRaw]
  | .ref key form text target => simp [inlineRaw]
  | .underline body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .fill => simp [inlineRaw]
  | .pageNumber => simp [inlineRaw]
  | .pageCount => simp [inlineRaw]
  | .linebreak extra => simp [inlineRaw]
  | .strut h => simp [inlineRaw]
  | .italicCorr m => simp [inlineRaw]
  | .step n l body =>
    simp only [inlineRaw]
    exact inlinesRaw_acc out body.toList
  | .alt n l active otherwise =>
    simp only [inlineRaw]
    rw [inlinesRaw_acc (inlinesRaw out active.toList) otherwise.toList,
      inlinesRaw_acc (inlinesRaw #[] active.toList) otherwise.toList,
      inlinesRaw_acc out active.toList, Array.append_assoc]
  | .image src size alt => simp [inlineRaw]
  | .icon sc label => simp [inlineRaw]
  | .cite tx keys => simp [inlineRaw]
  | .footnote num body => simp [inlineRaw]

end

/-- `bibRaw` builds onto its accumulator: the `.bibliography` arm's half. -/
theorem bibRaw_acc (out : Array Node) (items : List BibItem) :
    bibRaw out items = out ++ bibRaw #[] items := by
  induction items generalizing out with
  | nil => simp [bibRaw]
  | cons it rest ih =>
    rw [bibRaw, ih, bibRaw, ih (#[].push _)]
    simp

mutual

/-- `blocksRaw` builds onto its accumulator. -/
theorem blocksRaw_acc (out : Array Node) (bs : List Block) :
    blocksRaw out bs = out ++ blocksRaw #[] bs := by
  match bs with
  | [] => simp [blocksRaw]
  | b :: rest =>
    rw [blocksRaw, blocksRaw_acc _ rest, blockRaw_acc out b, blocksRaw,
      blocksRaw_acc (blockRaw #[] b) rest, Array.append_assoc]

theorem blockRaw_acc (out : Array Node) (b : Block) :
    blockRaw out b = out ++ blockRaw #[] b := by
  match b with
  | .para content => simp [blockRaw]
  | .section level st num title => simp [blockRaw]
  | .list ordered items => simp [blockRaw]
  | .center body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .ragged _ body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .spaced g body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .role nm body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .quote body => simp [blockRaw]
  | .abstract body => simp [blockRaw]
  | .titled kind title body => simp [blockRaw]
  | .equation number content => simp [blockRaw]
  | .verbatim c content spec =>
    simp only [blockRaw]
    split <;> simp
  | .algorithm nm sm lines => simp [blockRaw]
  | .columns cols =>
    simp only [blockRaw]; exact colsRaw_acc out cols.toList
  | .step nn l body =>
    simp only [blockRaw]; exact blocksRaw_acc out body.toList
  | .alt nn l active otherwise =>
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

/-- Numbering moves no leaf: the numbered shape has exactly the leaves the
shape had. -/
theorem numberList_leafCount (k : Nat) (ns : List Node) :
    (leavesList #[] (numberList k #[] ns).1.toList).size = (leavesList #[] ns).size := by
  match ns with
  | [] => simp [numberList, leavesList_nil_exact]
  | n :: rest =>
    obtain ⟨h1, h2⟩ := numberList_acc (numberOne k n).2 (#[].push (numberOne k n).1) rest
    simp only [numberList]
    rw [h1, Array.toList_append, leavesList_append, leavesList_acc, Array.size_append,
      Array.toList_push, leavesList_cons_exact, leavesList_acc (leavesOne #[] n) rest,
      Array.size_append]
    rw [numberList_leafCount (numberOne k n).2 rest]
    simp only [List.nil_append, leavesList_nil_exact, leavesList_cons_exact]
    rw [numberOne_leafCount k n]

theorem numberOne_leafCount (k : Nat) (n : Node) :
    (leavesOne #[] (numberOne k n).1).size = (leavesOne #[] n).size := by
  match n with
  | .leaf id l => simp [numberOne, leavesOne_leaf_exact]
  | .node kind kids =>
    simp only [numberOne, leavesOne_node_exact]
    exact numberList_leafCount k kids.toList

end

/-- The counter a numbering leaves: the start plus the shape's leaf count. -/
theorem numberList_count (k : Nat) (ns : List Node) :
    (numberList k #[] ns).2 = k + (leavesList #[] ns).size := by
  obtain ⟨hid, hle⟩ := numberList_id k ns
  have hlen := congrArg List.length hid
  rw [List.length_map, List.length_range'] at hlen
  rw [← numberList_leafCount k ns]
  have : (leavesList #[] (numberList k #[] ns).1.toList).size
      = (leavesList #[] (numberList k #[] ns).1.toList).toList.length := by simp
  omega

/-- Numbering an append numbers the halves in turn: the second half starts
where the first left the counter. -/
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

/-- Two shapes numbered as one from `k`: the first takes `k …`, the second
resumes at `k` plus the first's leaf count. -/
theorem pair_leaf_ids (a b : Array Node) (k : Nat) :
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

/-- **`alt_leaf_projects`** (`_projects`): the ids the tree gives an overlay
alternation's two groups, at both levels the IR carries one. The group stored
first — the one step 1 inks (`Ir.altShowsFirst_id`) — is numbered from the
node's own start; the other from that start plus the first group's leaf count.

Layout's alternation arms are this projection: a page that inks the group
stored first steps the counter over the other group *after* setting it, and a
page that inks the other steps over the first group's `leafCountInlines` (or
`leafCountBlocks`) *before* setting it, so in both orders the group lands on
the id the tree already assigned it. That is what keeps one leaf per group
across a frame's step pages — the id is the node's position in the document
tree, not a count the walk accumulates, and nothing has to reconcile two
counters after the fact. -/
theorem alt_leaf_projects (n : Nat) (last : Option Nat)
    (firstI otherI : Array Inline) (firstB otherB : Array Block) (k : Nat) :
    (leaves (number k (inlineRaw #[] (Inline.alt n last firstI otherI)))).toList.map Prod.fst
        = List.range' k (leafCountInlines firstI)
          ++ List.range' (k + leafCountInlines firstI) (leafCountInlines otherI)
      ∧ (leaves (number k (blockRaw #[] (Block.alt n last firstB otherB)))).toList.map Prod.fst
        = List.range' k (leafCountBlocks firstB)
          ++ List.range' (k + leafCountBlocks firstB) (leafCountBlocks otherB) := by
  have hi : inlineRaw #[] (Inline.alt n last firstI otherI)
      = inlinesRaw #[] firstI.toList ++ inlinesRaw #[] otherI.toList := by
    simp only [inlineRaw]
    exact inlinesRaw_acc (inlinesRaw #[] firstI.toList) otherI.toList
  have hb : blockRaw #[] (Block.alt n last firstB otherB)
      = blocksRaw #[] firstB.toList ++ blocksRaw #[] otherB.toList := by
    simp only [blockRaw]
    exact blocksRaw_acc (blocksRaw #[] firstB.toList) otherB.toList
  rw [hi, hb, pair_leaf_ids, pair_leaf_ids]
  exact ⟨rfl, rfl⟩

end LeanTex.Core.Struct
