import LeanTex.Core.Struct
import LeanTex.Core.PdfContent
import LeanTex.Core.PdfRead

/-!
# The PDF structure tree, as a typed model

The structure tree a tagged PDF carries (ISO 32000-2 §14.7) is a
projection of `Struct.Tree`: one `StructElem` per structure node, each
with its PDF 2.0 standard structure type, its parent, and its kids — child
elements and the marked content of the leaves it holds. The projection has
two halves, so the stream and the tree cannot disagree:

1. `skeleton` walks the tree once and emits the elements with `.leaf k`
   placeholders where leaf `k`'s marked content will go. `leafTags` reads,
   off that skeleton, the structure type of the element holding each leaf
   — the tag the content stream spells (`Origin.of`).
2. `fill` replaces each `.leaf k` by the `(page, mcid)` pairs the numbered
   streams carry for `k` (`pageMarks`). The parent tree is the same map
   read in the other direction (`parentTreeOf`).

So the tag on a marked-content sequence *is* the type of the element that
lists it, and the parent tree entry of an identifier *is* the element that
lists it — by construction (`parentTree_covers`), not by a second walk.
Headings: the elements' heading levels are exactly the tree's
(`pdf_headings_covers`), so with `structTree_headings_covers` they are
`Ir.headingLevels` of the document.

A line's marked content lands in the element that *holds* its leaf: the
nearest block-level ancestor — paragraph, heading, title, caption, cell,
code, label, footnote body, list body, bibliography entry, figure, display
formula — never an inline element (link, span, reference, inline formula).
The attribution channel names a line by the first leaf of the block it
sets (`LineOut.leaf`), so a paragraph opening with a link must land in the
paragraph, not the link. Inline elements are emitted, empty, for the
inline slices to fill.
-/

namespace LeanTex.Core.Pdf

open LeanTex.Core

/-- A child of a structure element: another element (by index in the
elements array), a placeholder for leaf `k`'s marked content (the
skeleton's spelling, before `fill`), or one marked-content sequence on a
page (after `fill`). -/
inductive StructKid where
  | elem (idx : Nat)
  | leaf (k : Nat)
  | mcid (page mcid : Nat)
  deriving Repr, BEq, Inhabited

/-- One structure element (§14.7.2): its standard structure type, its
parent (`none` for the root, whose parent is the structure tree root
itself), its kids in reading order, and the attributes later slices fill:
`/Alt` for a figure, `/Lang` and `/ActualText` for spans, `/A` entries.
`heading` is the tree's heading level when the element is an `Hn` — the
census `pdf_headings_covers` reads. -/
structure StructElem where
  s : String
  /-- The type is in the PDF 2.0 standard structure namespace (§14.8.4;
  the element names it through `/NS`). `false` for the types PDF 2.0
  dropped and kept only in the 1.7 namespace — `Code`, `BlockQuote`,
  `Reference` — which an element names by carrying no `/NS`. -/
  ns20 : Bool := true
  parent : Option Nat := none
  kids : Array StructKid := #[]
  heading : Option Nat := none
  alt : Option String := none
  lang : Option String := none
  actualText : Option String := none
  attrs : Array (String × PdfRead.Obj) := #[]
  deriving Repr, BEq, Inhabited

/-- The PDF 2.0 standard structure type of a tree node kind (ISO 32000-2
§14.8.4). A heading at tree level `n` is `H{n+1}`: level 0 is the document
title, the HTML's one `<h1>`, and the two artifacts number headings the
same way. A `.title` is the title of a region, PDF 2.0's block-level
`Title`. Generated furniture the census counts (`.artifact`) is
`NonStruct`, a grouping of no structural significance whose leaves the
page never attributes. A `.nav` ships no ink on the page (its links are
the outline) and stands as a `Sect` so the census sees through it. -/
def structTypeOf : Struct.Kind → String
  | .document => "Document"
  | .section => "Sect"
  | .title => "Title"
  | .heading level => s!"H{level + 1}"
  | .paragraph => "P"
  | .list _ => "L"
  | .item => "LI"
  | .label => "Lbl"
  | .body => "LBody"
  | .table => "Table"
  | .row => "TR"
  | .cell => "TD"
  | .caption => "Caption"
  | .figure => "Figure"
  | .formula => "Formula"
  | .code => "Code"
  | .quote => "BlockQuote"
  | .note => "FENote"
  | .aside => "Aside"
  | .nav => "Sect"
  | .bibEntry => "LBody"
  | .link _ => "Link"
  | .span _ => "Span"
  | .reference _ => "Reference"
  | .artifact => "NonStruct"

/-- Is the kind's type in the PDF 2.0 namespace? PDF 2.0 dropped `Code`,
`BlockQuote` and `Reference` from its standard set (ISO 32000-2 §14.8.4,
Table 366 note on deprecated 1.7 types); those stand in the 1.7 namespace. -/
def inPdf2Namespace : Struct.Kind → Bool
  | .code => false
  | .quote => false
  | .reference _ => false
  | .document | .section | .title | .heading _ | .paragraph | .list _ | .item | .label | .body
  | .table | .row | .cell | .caption | .figure | .formula | .note | .aside | .nav | .bibEntry
  | .link _ | .span _ | .artifact => true

/-- The heading level a kind carries, for the census. -/
def headingLevelOf : Struct.Kind → Option Nat
  | .heading level => some level
  | .document | .section | .title | .paragraph | .list _ | .item | .label | .body | .table
  | .row | .cell | .caption | .figure | .formula | .code | .quote | .note | .aside | .nav
  | .bibEntry | .link _ | .span _ | .reference _ | .artifact => none

/-- Does an element of this kind hold the marked content of the text
leaves under it? Block-level kinds do; inline kinds (link, span,
reference) pass their leaves to the enclosing holder; a formula holds only
when it stands as a block (`inline = false`), an inline formula is part of
its paragraph. -/
def isHolder (kind : Struct.Kind) (inline : Bool) : Bool :=
  match kind with
  | .paragraph | .title | .heading _ | .caption | .cell | .code | .label | .body | .note
  | .bibEntry | .figure | .artifact => true
  | .formula => !inline
  | .document | .section | .list _ | .item | .table | .row | .quote | .aside | .nav
  | .link _ | .span _ | .reference _ => false

/-- The element a node kind projects to, before its kids. -/
def elemOf (kind : Struct.Kind) : StructElem :=
  { s := structTypeOf kind, ns20 := inPdf2Namespace kind, heading := headingLevelOf kind }

/-- Append `e` as the last child of `parent`: its index is the next slot. -/
def pushElem (es : Array StructElem) (parent : Nat) (e : StructElem) : Array StructElem × Nat :=
  let idx := es.size
  let es := es.modify parent fun p => { p with kids := p.kids.push (.elem idx) }
  (es.push { e with parent := some parent }, idx)

/-- Append a marked-content placeholder to the element holding it. -/
def addKid (es : Array StructElem) (holder : Nat) (k : StructKid) : Array StructElem :=
  es.modify holder fun p => { p with kids := p.kids.push k }

/-- A reference-list entry as `LI`/`LBody` under the open `L`, opening one
under `parent` when none is: consecutive entries share a list. -/
def bibEntryElems (es : Array StructElem) (parent : Nat) (openList : Option Nat) :
    Array StructElem × Nat × Nat :=
  let (es, l) := match openList with
    | some l => (es, l)
    | none => pushElem es parent { s := "L" }
  let (es, li) := pushElem es l { s := "LI" }
  let (es, lb) := pushElem es li { s := "LBody" }
  (es, l, lb)

/-- The `Figure` an image or picture leaf's alternative projects to. -/
def figureElem (k : Nat) (alt : Option String) : StructElem :=
  { s := structTypeOf .figure, kids := #[.leaf k], alt := alt }

/-- The one projection of a non-text leaf's alternative into the structure
tree (ISO 32000-2 §14.8.4.8.5 Figure, §14.9.3 alternate descriptions,
§14.8.2.2 artifacts): described, a `Figure` with `/Alt`; undeclared, a
`Figure` without — the honest failure a checker names; decorative, no
element, so no element holds the leaf and the content stream marks its ink
`/Artifact` (`PdfContent.Origin.of`), latex-lab's `artifact`. -/
def altElem (es : Array StructElem) (parent k : Nat) : Ir.Alt → Array StructElem
  | .described t => (pushElem es parent (figureElem k (some t))).1
  | .undeclared => (pushElem es parent (figureElem k none)).1
  | .decorative => es

mutual

/-- The elements of a node list under `parent`, text leaves landing in
`holder`; `inline` says the walk is inside a holder (so a formula is
inline); `openList` is the `L` consecutive reference entries share. -/
def skelList (es : Array StructElem) (parent holder : Nat) (inline : Bool)
    (openList : Option Nat) : List Struct.Node → Array StructElem
  | [] => es
  | n :: rest =>
    let r := skelStep es parent holder inline openList n
    skelList r.1 parent holder inline r.2 rest

/-- One node, with the list the next reference entry may join. A text or
break leaf is a placeholder in its holder; an image or picture leaf
projects its one alternative (`altElem`); a speaker note (`.aside`) is not
page content and emits nothing;
a label (`.label`: a list marker, an equation number) is transparent while
the page attributes at line granularity — its ink rides the line of the
body it decorates, and an empty `Lbl` would demand a `ListNumbering` the
layout has not said (the list slice adds both together); a reference entry
joins the open `L` (or opens one) as `LI`/`LBody`; every other node is one
element over its kids, holding their leaves when its kind holds, and closes
any open list. -/
def skelStep (es : Array StructElem) (parent holder : Nat) (inline : Bool)
    (openList : Option Nat) : Struct.Node → Array StructElem × Option Nat
  | .leaf k l =>
    match l with
    | .text _ => (addKid es holder (.leaf k), none)
    | .linebreak => (addKid es holder (.leaf k), none)
    | .picture alt => (altElem es parent k alt, none)
    | .image _ alt => (altElem es parent k alt, none)
  | .node kind kids =>
    match kind with
    | .aside => (es, none)
    | .label => (skelList es parent holder inline none kids.toList, none)
    | .bibEntry =>
      let (es, l, lb) := bibEntryElems es parent openList
      (skelList es lb lb true none kids.toList, some l)
    | .document | .section | .title | .heading _ | .paragraph | .list _ | .item
    | .body | .table | .row | .cell | .caption | .figure | .formula | .code | .quote | .note
    | .nav | .link _ | .span _ | .reference _ | .artifact =>
      let (es, i) := pushElem es parent (elemOf kind)
      let (h, inl) := if isHolder kind inline then (i, true) else (holder, inline)
      (skelList es i h inl none kids.toList, none)

end

/-- The `Document` root, its parent the structure tree root. -/
def rootElem : StructElem := { s := structTypeOf .document }

/-- The structure elements of a tree, in preorder, the root at index 0,
leaf placeholders in place of marked content. -/
def skeleton (t : Struct.Tree) : Array StructElem :=
  skelList #[rootElem] 0 0 false none t.children.toList

private def assignOwner (i : Nat) (out : Array (Option Nat)) : StructKid → Array (Option Nat)
  | .leaf j => out.setIfInBounds j (some i)
  | .elem _ => out
  | .mcid _ _ => out

/-- The element holding each leaf `k < n`: the one whose kids carry
`.leaf k`. The soundness half — an owner listed does hold the leaf — is
`leafOwners_mem`; that each leaf is held once is the skeleton's
(`skeleton_leafKids_nodup`). -/
def leafOwners (es : Array StructElem) (n : Nat) : Array (Option Nat) :=
  (es.toList.zipIdx).foldl (fun out (e, i) =>
    e.kids.foldl (assignOwner i) out) (Array.replicate n none)

/-- Every owner an answer map records holds the leaf it is recorded for:
the invariant `leafOwners`' fold preserves. -/
private def OwnerSound (es : Array StructElem) (out : Array (Option Nat)) : Prop :=
  ∀ j i, out[j]? = some (some i) → ∃ e, es[i]? = some e ∧ StructKid.leaf j ∈ e.kids

private theorem ownerSound_kids {es : Array StructElem} {e : StructElem} {i : Nat}
    (hi : es[i]? = some e) {out : Array (Option Nat)} (ho : OwnerSound es out) :
    OwnerSound es (e.kids.foldl (assignOwner i) out) := by
  refine Array.foldl_induction (motive := fun _ acc => OwnerSound es acc) ho ?_
  intro idx acc hacc
  have hmem : e.kids[idx.1] ∈ e.kids := e.kids.getElem_mem idx.isLt
  unfold assignOwner
  split
  next j0 hk =>
    intro j' i' hj'
    rw [Array.getElem?_setIfInBounds] at hj'
    split at hj'
    next heq =>
      split at hj'
      · have hii : i = i' := by simpa using hj'
        subst hii
        exact ⟨e, hi, heq ▸ hk ▸ hmem⟩
      · simp at hj'
    next => exact hacc j' i' hj'
  next => exact hacc
  next => exact hacc

/-- Soundness of the owner map (the `_mem` shape: the owner is drawn from
the elements that carry the leaf): `leafOwners` records `some i` at slot
`j` only from the element at index `i` listing `.leaf j`, so the tag
`leafTags` reads off an owner is the type of an element that does hold the
leaf. The fold's inversion, by the invariant `OwnerSound`. That each leaf
is held by *one* element is the separate census
(`skeleton_leafKids_nodup`). -/
theorem leafOwners_mem (es : Array StructElem) (n j i : Nat)
    (h : (leafOwners es n)[j]? = some (some i)) :
    ∃ e, es[i]? = some e ∧ StructKid.leaf j ∈ e.kids := by
  have base : OwnerSound es (Array.replicate n (none : Option Nat)) := by
    intro j' i' hj'
    rcases Nat.lt_or_ge j' n with hlt | hge
    · rw [Array.getElem?_eq_getElem (by simpa using hlt)] at hj'
      simp at hj'
    · rw [Array.getElem?_eq_none (by simpa using hge)] at hj'
      simp at hj'
  have main : OwnerSound es (leafOwners es n) := by
    unfold leafOwners
    refine List.foldlRecOn _ _ base ?_
    intro out ho p hp
    obtain ⟨e, idx⟩ := p
    exact ownerSound_kids (by
      have hg := (List.mk_mem_zipIdx_iff_getElem?).1 hp
      simpa using hg) ho
  exact main j i h

/-- Every leaf placeholder the elements carry, in element order: the
census `skeleton_leafKids_nodup` says holds each leaf once; `leafIdsOf` is
its element case, and `leafKids_addKid_leaf` the reason the census is a
permutation of the ids and not an append of them. -/
def leafKids (es : Array StructElem) : List Nat :=
  es.toList.flatMap fun e => e.kids.toList.filterMap fun k =>
    match k with
    | .leaf j => some j
    | .elem _ => none
    | .mcid _ _ => none

/-- The structure type each leaf's marked content is tagged with: the type
of the element holding it, `none` for a leaf no element holds (a leaf under
a speaker note, or beyond the tree) — the content stream marks such a
line an artifact (`Origin.of`). -/
def leafTags (es : Array StructElem) (n : Nat) : Array (Option String) :=
  (leafOwners es n).map fun o => o.bind fun i => es[i]?.map (·.s)

/-- The `(page, mcid)` pairs painting each leaf `k < n`, page by page in
stream order, from the numbered streams' marks. -/
def leafPagesOf (n : Nat) (marks : Array (Array (Nat × Nat))) : Array (Array (Nat × Nat)) :=
  (marks.toList.zipIdx).foldl (fun out (pm, p) =>
    pm.foldl (fun out (m, k) => out.modify k (·.push (p, m))) out)
    (Array.replicate n #[])

/-- A kid with its leaf placeholder replaced by the leaf's marked content. -/
def fillKid (lp : Array (Array (Nat × Nat))) : StructKid → Array StructKid
  | .leaf k => ((lp[k]?).getD #[]).map fun (p, m) => .mcid p m
  | .elem i => #[.elem i]
  | .mcid p m => #[.mcid p m]

/-- The elements with every placeholder filled. -/
def fill (es : Array StructElem) (lp : Array (Array (Nat × Nat))) : Array StructElem :=
  es.map fun e => { e with kids := e.kids.flatMap (fillKid lp) }

/-- The parent tree (§14.7.5.4), page by page: entry `m` of page `p` is the
element holding the leaf that identifier `m` paints. Reads the marks by
position — `numberMarks_mcids_exact` says position and identifier agree. -/
def parentTreeOf (marks : Array (Array (Nat × Nat))) (owners : Array (Option Nat)) :
    Array (Array (Option Nat)) :=
  marks.map fun pm => pm.map fun (_, k) => (owners[k]?).join

/-! ## Theorems -/

/-- The heading levels of an element array, in order. -/
def headingsOf (es : Array StructElem) : List Nat := es.toList.filterMap (·.heading)

theorem List.filterMap_modify_of {α β : Type} (g : α → Option β) (f : α → α)
    (hf : ∀ a, g (f a) = g a) (l : List α) (i : Nat) :
    (l.modify i f).filterMap g = l.filterMap g := by
  induction l generalizing i with
  | nil => simp
  | cons a rest ih =>
    cases i with
    | zero => simp [List.filterMap_cons, hf]
    | succ i => simp [List.filterMap_cons, ih]

theorem headingsOf_modify (es : Array StructElem) (i : Nat) (f : StructElem → StructElem)
    (hf : ∀ e, (f e).heading = e.heading) : headingsOf (es.modify i f) = headingsOf es := by
  simp only [headingsOf, Array.toList_modify]
  exact List.filterMap_modify_of _ f hf _ i

theorem headingsOf_push (es : Array StructElem) (e : StructElem) :
    headingsOf (es.push e) = headingsOf es ++ e.heading.toList := by
  simp [headingsOf, Array.toList_push, List.filterMap_append, List.filterMap_cons]
  cases e.heading <;> rfl

theorem headingsOf_pushElem (es : Array StructElem) (parent : Nat) (e : StructElem) :
    headingsOf (pushElem es parent e).1 = headingsOf es ++ e.heading.toList := by
  simp only [pushElem, headingsOf_push]
  have h := headingsOf_modify es parent
    (fun p => { p with kids := p.kids.push (.elem es.size) }) (fun _ => rfl)
  rw [h]

theorem headingsOf_addKid (es : Array StructElem) (holder : Nat) (k : StructKid) :
    headingsOf (addKid es holder k) = headingsOf es :=
  headingsOf_modify _ _ _ (fun _ => rfl)

theorem headingsOf_altElem (es : Array StructElem) (parent k : Nat) (a : Ir.Alt) :
    headingsOf (altElem es parent k a) = headingsOf es := by
  cases a <;> simp [altElem, headingsOf_pushElem, figureElem]

/-- **`pdf_alt_projects`** (the `_projects` statement): the element a
non-text leaf gets is a function of its one alternative — a described one
the last element pushed, a `Figure` under `parent` holding the leaf with
`/Alt` its text; an undeclared one the same `Figure` with no `/Alt`; a
decorative one no element at all. -/
theorem pdf_alt_projects (es : Array StructElem) (parent k : Nat) :
    (∀ t, (altElem es parent k (.described t)).back? =
        some { figureElem k (some t) with parent := some parent }) ∧
    (altElem es parent k .undeclared).back? =
        some { figureElem k none with parent := some parent } ∧
    altElem es parent k .decorative = es := by
  refine ⟨fun t => ?_, ?_, rfl⟩ <;> simp [altElem, pushElem]

theorem headingsOf_bibEntryElems (es : Array StructElem) (parent : Nat) (openList : Option Nat) :
    headingsOf (bibEntryElems es parent openList).1 = headingsOf es := by
  unfold bibEntryElems
  cases openList <;> simp [headingsOf_pushElem]

/-- `Struct.headingsList` with an accumulator is the accumulator then the
census from empty: the list form of the census's own `headingsList_acc`. -/
theorem Struct.headingsList_out (l : List Struct.Node) (out : Array Nat) :
    (Struct.headingsList out l).toList = out.toList ++ (Struct.headingsList #[] l).toList := by
  rw [Struct.headingsList_acc]
  simp

theorem Struct.headingsOne_out (n : Struct.Node) (out : Array Nat) :
    (Struct.headingsOne out n).toList = out.toList ++ (Struct.headingsOne #[] n).toList := by
  rw [Struct.headingsOne_acc]
  simp

mutual

theorem skelList_headings : ∀ (l : List Struct.Node) (es : Array StructElem)
    (parent holder : Nat) (inline : Bool) (openList : Option Nat),
    headingsOf (skelList es parent holder inline openList l)
      = headingsOf es ++ (Struct.headingsList #[] l).toList
  | [], es, parent, holder, inline, openList => by
    simp [skelList, Struct.headingsList_nil_exact]
  | n :: rest, es, parent, holder, inline, openList => by
    rw [skelList, skelList_headings rest, skelStep_headings n, Struct.headingsList_cons_exact,
      Struct.headingsList_out rest (Struct.headingsOne #[] _)]
    simp

theorem skelStep_headings : ∀ (n : Struct.Node) (es : Array StructElem) (parent holder : Nat)
    (inline : Bool) (openList : Option Nat),
    headingsOf (skelStep es parent holder inline openList n).1
      = headingsOf es ++ (Struct.headingsOne #[] n).toList
  | .leaf k l, es, parent, holder, inline, openList => by
    cases l <;> simp [skelStep, headingsOf_addKid, headingsOf_altElem,
      Struct.headingsOne_leaf_exact]
  | .node kind kids, es, parent, holder, inline, openList => by
    cases kind
    case aside => simp [skelStep, Struct.headingsOne_aside_exact]
    case label =>
      rw [Struct.headingsOne_through_exact _ _ _ (by simp) (by simp)]
      simp only [skelStep]
      rw [skelList_headings kids.toList]
    case bibEntry =>
      rw [Struct.headingsOne_through_exact _ _ _ (by simp) (by simp)]
      simp only [skelStep]
      rw [skelList_headings kids.toList, headingsOf_bibEntryElems]
    case heading level =>
      rw [Struct.headingsOne_heading_exact]
      simp only [skelStep, skelList_headings, headingsOf_pushElem, elemOf, headingLevelOf,
        List.append_assoc]
      rw [Struct.headingsList_out kids.toList (#[].push _)]
      simp
    all_goals
      rw [Struct.headingsOne_through_exact _ _ _ (by simp) (by simp)]
      simp only [skelStep, skelList_headings, headingsOf_pushElem, elemOf, headingLevelOf,
        List.append_assoc]
      simp

end

/-- **`pdf_headings_covers`** (the `_covers` statement, the PDF projection
corollary of `structTree_headings_covers`): the heading elements of the
structure tree, in preorder, carry exactly the tree's heading levels — so,
over `Struct.ofDoc`, exactly `Ir.headingLevels` of the document's body.
The type spelled is `H{level+1}`. -/
theorem pdf_headings_covers (t : Struct.Tree) :
    headingsOf (skeleton t) = t.headings.toList := by
  unfold skeleton Struct.Tree.headings
  rw [Struct.headings_eq_exact, skelList_headings]
  simp [headingsOf, rootElem]

theorem pdf_headings_covers_doc (doc : Ir.Doc) :
    headingsOf (skeleton (Struct.ofDoc doc)) = (Ir.headingLevels doc.body).toList := by
  rw [pdf_headings_covers, Struct.Tree.headings, Struct.ofDoc, Struct.structTree_headings_covers]

/-- **`structKids_mem`** (the `_mem` statement): every marked-content kid of
a filled element is drawn from `leafPages` — a pair the streams carry for
some leaf the element held. -/
theorem structKids_mem (es : Array StructElem) (lp : Array (Array (Nat × Nat))) :
    ∀ e ∈ fill es lp, ∀ p m, StructKid.mcid p m ∈ e.kids →
      ∃ k : Nat, (p, m) ∈ (lp[k]?).getD #[] ∨ StructKid.mcid p m ∈ (es.toList.flatMap (·.kids.toList)) := by
  intro e he p m hm
  simp only [fill, Array.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  simp only [Array.mem_flatMap] at hm
  obtain ⟨k0, hk0, hk⟩ := hm
  cases k0 with
  | leaf k =>
    refine ⟨k, Or.inl ?_⟩
    simp only [fillKid, Array.mem_map] at hk
    obtain ⟨⟨p', m'⟩, hpm, h⟩ := hk
    cases h
    exact hpm
  | elem i => simp [fillKid] at hk
  | mcid p' m' =>
    refine ⟨0, Or.inr ?_⟩
    simp only [fillKid, Array.mem_singleton] at hk
    rw [← hk] at hk0
    simp only [List.mem_flatMap]
    exact ⟨e0, Array.mem_toList_iff.mpr he0, Array.mem_toList_iff.mpr hk0⟩

/-- The leaf ids one element holds, in kid order: `leafKids`' element case. -/
def leafIdsOf (e : StructElem) : List Nat :=
  e.kids.toList.filterMap fun k =>
    match k with
    | .leaf j => some j
    | .elem _ => none
    | .mcid _ _ => none

theorem leafKids_eq_flatMap (es : Array StructElem) :
    leafKids es = es.toList.flatMap leafIdsOf := rfl

theorem leafKids_push (es : Array StructElem) (e : StructElem) :
    leafKids (es.push e) = leafKids es ++ leafIdsOf e := by
  simp [leafKids_eq_flatMap, Array.toList_push]

theorem List.flatMap_modify_of {α β : Type} (g : α → List β) (f : α → α)
    (hf : ∀ a, g (f a) = g a) (l : List α) (i : Nat) :
    (l.modify i f).flatMap g = l.flatMap g := by
  induction l generalizing i with
  | nil => simp
  | cons a rest ih =>
    cases i with
    | zero => simp [hf]
    | succ i => simp [ih]

/-- A `modify` that appends to one element's own census moves the whole
census by a permutation and not by an append: the element sits in the middle
of the list, so what it gained lands before everything after it. -/
theorem List.flatMap_modify_perm {α β : Type} (g : α → List β) (f : α → α) (extra : List β)
    (hf : ∀ a, g (f a) = g a ++ extra) (l : List α) (i : Nat) (hi : i < l.length) :
    ((l.modify i f).flatMap g).Perm (l.flatMap g ++ extra) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons, List.flatMap_cons, hf, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    | succ i =>
      simp only [List.modify_succ_cons, List.flatMap_cons, List.append_assoc]
      exact List.Perm.append_left _ (ih i (by simpa using hi))

theorem leafIdsOf_push_leaf (e : StructElem) (k : Nat) :
    leafIdsOf { e with kids := e.kids.push (.leaf k) } = leafIdsOf e ++ [k] := by
  simp [leafIdsOf, Array.toList_push]

theorem leafIdsOf_push_elem (e : StructElem) (i : Nat) :
    leafIdsOf { e with kids := e.kids.push (.elem i) } = leafIdsOf e := by
  simp [leafIdsOf, Array.toList_push]

/-- A `modify` whose function leaves an element's leaf ids alone leaves the
whole census alone — the `.elem` kid `pushElem` writes onto a parent. Total
in the index: `Array.modify` out of bounds is the identity, and so is this. -/
theorem leafKids_modify_of (es : Array StructElem) (i : Nat) (f : StructElem → StructElem)
    (hf : ∀ e, leafIdsOf (f e) = leafIdsOf e) :
    leafKids (es.modify i f) = leafKids es := by
  rw [leafKids_eq_flatMap, leafKids_eq_flatMap, Array.toList_modify]
  exact List.flatMap_modify_of leafIdsOf f hf _ i

/-- **A leaf added to an element in the middle is a permutation, not an
append.** `addKid` is `Array.modify`, so the new id lands before every
element after the holder: the census order changes and only the multiset is
preserved — which is all `Nodup` needs. The index bound is a hypothesis
because `Array.modify` out of bounds is the identity, and the leaf would
then vanish in silence. -/
theorem leafKids_addKid_leaf (es : Array StructElem) (holder k : Nat)
    (h : holder < es.size) :
    (leafKids (addKid es holder (.leaf k))).Perm (leafKids es ++ [k]) := by
  rw [leafKids_eq_flatMap, leafKids_eq_flatMap, addKid, Array.toList_modify]
  exact List.flatMap_modify_perm leafIdsOf _ [k]
    (fun e => leafIdsOf_push_leaf e k) _ holder (by simpa using h)

theorem leafKids_pushElem (es : Array StructElem) (parent : Nat) (e : StructElem) :
    leafKids (pushElem es parent e).1 = leafKids es ++ leafIdsOf e := by
  simp only [pushElem, leafKids_push]
  rw [leafKids_modify_of _ _ _ (fun e0 => leafIdsOf_push_elem e0 es.size)]
  simp [leafIdsOf]

/-! ### The leaf census of the skeleton -/

/-- The leaf ids the skeleton walk reaches, in preorder: every leaf an
element holds (`Struct.Leaf.held`) outside a speaker note. The descent is
the engine's own classifier — `skelStep` emits nothing at all for `.aside`,
which is exactly what `Kind.outlineDescends` says — so this is the walk's
census and not a transcription of it. -/
def skelLeafFold : Struct.NodeFold (Array Nat) where
  leaf := fun out id l => if l.held then out.push id else out
  enter := fun out _ => out
  descends := Struct.Kind.outlineDescends

theorem skelLeafAppends : Struct.Appends skelLeafFold where
  leaf := by intro out id l; cases h : l.held <;> simp [skelLeafFold, h]
  enter := by intro out kind; simp [skelLeafFold]

def skelLeafIds (l : List Struct.Node) : Array Nat := Struct.foldNodeList skelLeafFold #[] l

def skelLeafIdsOne (n : Struct.Node) : Array Nat := Struct.foldNode skelLeafFold #[] n

theorem skelLeafIds_nil : skelLeafIds [] = #[] := rfl

theorem skelLeafIds_cons (n : Struct.Node) (l : List Struct.Node) :
    skelLeafIds (n :: l) = skelLeafIdsOne n ++ skelLeafIds l := by
  rw [skelLeafIds, Struct.foldNodeList_cons_exact,
    Struct.foldNodeList_acc skelLeafAppends]
  rfl

theorem skelLeafIdsOne_leaf (k : Nat) (l : Struct.Leaf) :
    skelLeafIdsOne (.leaf k l) = if l.held then #[k] else #[] := by
  cases h : l.held <;> simp [skelLeafIdsOne, Struct.foldNode_leaf_exact, skelLeafFold, h]

theorem skelLeafIdsOne_node (kind : Struct.Kind) (kids : Array Struct.Node) :
    skelLeafIdsOne (.node kind kids)
      = if kind.outlineDescends then skelLeafIds kids.toList else #[] := by
  rw [skelLeafIdsOne, Struct.foldNode_node_exact]
  cases hd : kind.outlineDescends <;> simp [hd, skelLeafFold, skelLeafIds]

/-! ### Sizes: the walk only grows the element array -/

theorem size_le_addKid (es : Array StructElem) (holder : Nat) (k : StructKid) :
    es.size ≤ (addKid es holder k).size := by simp [addKid]

theorem size_le_pushElem (es : Array StructElem) (parent : Nat) (e : StructElem) :
    es.size < (pushElem es parent e).1.size := by simp [pushElem]

theorem size_le_altElem (es : Array StructElem) (parent k : Nat) (a : Ir.Alt) :
    es.size ≤ (altElem es parent k a).size := by
  cases a <;> simp [altElem, pushElem]

theorem bibEntryElems_lb_lt (es : Array StructElem) (parent : Nat) (openList : Option Nat) :
    (bibEntryElems es parent openList).2.2 < (bibEntryElems es parent openList).1.size := by
  unfold bibEntryElems
  cases openList <;> simp [pushElem]

theorem size_le_bibEntryElems (es : Array StructElem) (parent : Nat) (openList : Option Nat) :
    es.size ≤ (bibEntryElems es parent openList).1.size := by
  unfold bibEntryElems
  cases openList <;> simp [pushElem] <;> omega

mutual

theorem size_le_skelList : ∀ (l : List Struct.Node) (es : Array StructElem)
    (parent holder : Nat) (inline : Bool) (openList : Option Nat),
    es.size ≤ (skelList es parent holder inline openList l).size
  | [], es, _, _, _, _ => by simp [skelList]
  | n :: rest, es, parent, holder, inline, openList => by
    rw [skelList]
    exact Nat.le_trans (size_le_skelStep n es parent holder inline openList)
      (size_le_skelList rest _ parent holder inline _)

theorem size_le_skelStep : ∀ (n : Struct.Node) (es : Array StructElem)
    (parent holder : Nat) (inline : Bool) (openList : Option Nat),
    es.size ≤ (skelStep es parent holder inline openList n).1.size
  | .leaf k l, es, parent, holder, inline, openList => by
    cases l <;> simp only [skelStep] <;>
      first
        | exact size_le_addKid es holder _
        | exact size_le_altElem es parent k _
  | .node kind kids, es, parent, holder, inline, openList => by
    cases kind
    case aside => simp [skelStep]
    case label => simpa [skelStep] using size_le_skelList kids.toList es parent holder inline none
    case bibEntry =>
      simp only [skelStep]
      exact Nat.le_trans (size_le_bibEntryElems es parent openList)
        (size_le_skelList kids.toList _ _ _ _ none)
    all_goals
      simp only [skelStep]
      exact Nat.le_trans (Nat.le_of_lt (size_le_pushElem es parent _))
        (size_le_skelList kids.toList _ _ _ _ none)

end

theorem leafIdsOf_of_kids_empty (e : StructElem) (h : e.kids = #[]) : leafIdsOf e = [] := by
  simp [leafIdsOf, h]

theorem leafKids_bibEntryElems (es : Array StructElem) (parent : Nat) (openList : Option Nat) :
    leafKids (bibEntryElems es parent openList).1 = leafKids es := by
  unfold bibEntryElems
  cases openList <;>
    simp [leafKids_pushElem, leafIdsOf_of_kids_empty]

theorem leafKids_pushElem_empty (es : Array StructElem) (parent : Nat) (e : StructElem)
    (h : e.kids = #[]) : leafKids (pushElem es parent e).1 = leafKids es := by
  rw [leafKids_pushElem, leafIdsOf_of_kids_empty e h, List.append_nil]

/-- A non-text leaf's element holds it exactly when the leaf is held
(`Struct.Leaf.held`): a decorative one adds no element and no leaf. -/
theorem leafKids_altElem (es : Array StructElem) (parent k : Nat) (a : Ir.Alt) :
    leafKids (altElem es parent k a) =
      leafKids es ++ (if (Struct.Leaf.picture a).held then [k] else []) := by
  cases a <;> simp [altElem, leafKids_pushElem, figureElem, leafIdsOf, Struct.Leaf.held]

mutual

/-- **The skeleton's leaf census, accumulator-generalised.** The elements a
node list produces hold exactly the leaf ids the walk reaches, on top of
whatever the accumulator already held — as a *permutation*, because `addKid`
writes into the middle of the array. `holder < es.size` is load-bearing:
`Array.modify` out of bounds is the identity, so without it a text leaf
would be dropped in silence rather than held. -/
theorem skelList_leafKids : ∀ (l : List Struct.Node) (es : Array StructElem)
    (parent holder : Nat) (inline : Bool) (openList : Option Nat), holder < es.size →
    (leafKids (skelList es parent holder inline openList l)).Perm
      (leafKids es ++ (skelLeafIds l).toList)
  | [], es, _, _, _, _, _ => by simp [skelList, skelLeafIds_nil]
  | n :: rest, es, parent, holder, inline, openList, hh => by
    rw [skelList, skelLeafIds_cons]
    have h1 := skelStep_leafKids n es parent holder inline openList hh
    have h2 := skelList_leafKids rest (skelStep es parent holder inline openList n).1
      parent holder inline (skelStep es parent holder inline openList n).2
      (Nat.lt_of_lt_of_le hh (size_le_skelStep n es parent holder inline openList))
    refine h2.trans ?_
    simp only [Array.toList_append, ← List.append_assoc]
    exact h1.append_right _

theorem skelStep_leafKids : ∀ (n : Struct.Node) (es : Array StructElem)
    (parent holder : Nat) (inline : Bool) (openList : Option Nat), holder < es.size →
    (leafKids (skelStep es parent holder inline openList n).1).Perm
      (leafKids es ++ (skelLeafIdsOne n).toList)
  | .leaf k l, es, parent, holder, inline, openList, hh => by
    cases l with
    | text s =>
      simpa [skelStep, skelLeafIdsOne_leaf, Struct.Leaf.held] using
        leafKids_addKid_leaf es holder k hh
    | linebreak =>
      simpa [skelStep, skelLeafIdsOne_leaf, Struct.Leaf.held] using
        leafKids_addKid_leaf es holder k hh
    | image src a =>
      simp only [skelStep, skelLeafIdsOne_leaf, leafKids_altElem]
      cases a <;> simp [Struct.Leaf.held]
    | picture a =>
      simp only [skelStep, skelLeafIdsOne_leaf, leafKids_altElem]
      cases a <;> simp [Struct.Leaf.held]
  | .node kind kids, es, parent, holder, inline, openList, hh => by
    cases kind
    case aside => simp [skelStep, skelLeafIdsOne_node, Struct.Kind.outlineDescends]
    case label =>
      rw [skelLeafIdsOne_node]
      simp only [Struct.Kind.outlineDescends, ite_true, skelStep]
      exact skelList_leafKids kids.toList es parent holder inline none hh
    case bibEntry =>
      rw [skelLeafIdsOne_node]
      simp only [Struct.Kind.outlineDescends, ite_true, skelStep]
      refine (skelList_leafKids kids.toList _ _ _ _ none (bibEntryElems_lb_lt es parent openList)).trans ?_
      rw [leafKids_bibEntryElems]
    all_goals
      rw [skelLeafIdsOne_node]
      simp only [Struct.Kind.outlineDescends, ite_true, skelStep]
      split
      · refine (skelList_leafKids kids.toList _ _ _ _ none (by simp [pushElem])).trans ?_
        rw [leafKids_pushElem_empty _ _ _ (by simp [elemOf])]
      · refine (skelList_leafKids kids.toList _ _ _ _ none
          (by simp [pushElem]; omega)).trans ?_
        rw [leafKids_pushElem_empty _ _ _ (by simp [elemOf])]

end

theorem Struct.leavesList_cons (n : Struct.Node) (l : List Struct.Node) :
    Struct.leavesList #[] (n :: l) = Struct.leavesOne #[] n ++ Struct.leavesList #[] l := by
  rw [Struct.leavesList, Struct.foldNodeList_cons_exact,
    Struct.foldNodeList_acc Struct.leavesAppends]
  rfl

mutual

/-- The skeleton's census is a sublist of the tree's own: it visits every
leaf the tree numbers, in the same order, except those under a speaker note
— which it does not descend into at all. The `Nodup` of the ids follows,
since the tree's are `List.range` (`structTree_leaves_id`). -/
theorem skelLeafIds_sublist : ∀ (l : List Struct.Node),
    (skelLeafIds l).toList.Sublist ((Struct.leavesList #[] l).toList.map Prod.fst)
  | [] => by simp [skelLeafIds_nil, Struct.leavesList, Struct.foldNodeList_nil_exact]
  | n :: rest => by
    rw [skelLeafIds_cons, Struct.leavesList_cons]
    simp only [Array.toList_append, List.map_append]
    exact (skelLeafIdsOne_sublist n).append (skelLeafIds_sublist rest)

theorem skelLeafIdsOne_sublist : ∀ (n : Struct.Node),
    (skelLeafIdsOne n).toList.Sublist ((Struct.leavesOne #[] n).toList.map Prod.fst)
  | .leaf k l => by
    cases h : l.held <;>
      simp [skelLeafIdsOne_leaf, h, Struct.leavesOne, Struct.foldNode_leaf_exact,
        Struct.leavesFold]
  | .node kind kids => by
    rw [skelLeafIdsOne_node]
    have hleaves : Struct.leavesOne #[] (.node kind kids)
        = Struct.leavesList #[] kids.toList := by
      rw [Struct.leavesOne, Struct.foldNode_node_exact]
      simp [Struct.leavesFold, Struct.leavesList]
    rw [hleaves]
    cases hd : kind.outlineDescends
    · simp
    · simpa using skelLeafIds_sublist kids.toList

end

/-- **The skeleton holds every leaf of a document's structure tree at most
once**: no two elements carry the same `.leaf k` placeholder, so a leaf's
marked content lands in one element and the parent tree names it. The
hypothesis `parentTree_covers` reads, and what makes the leaf tags a
function (`leafTags`) rather than a last-writer-wins fold.

The census is a permutation and not an equality — `addKid` is
`Array.modify`, so a leaf lands in the middle of the element array — and a
permutation is all `Nodup` needs. -/
theorem skeleton_leafKids_nodup (doc : Ir.Doc) :
    (leafKids (skeleton (Struct.ofDoc doc))).Nodup := by
  have hroot : leafKids #[rootElem] = [] := by
    simp [leafKids_eq_flatMap, leafIdsOf, rootElem]
  have hperm := skelList_leafKids (Struct.ofDoc doc).children.toList #[rootElem] 0 0 false none
    (by simp)
  rw [hroot, List.nil_append] at hperm
  rw [skeleton]
  refine hperm.nodup_iff.mpr ?_
  refine (skelLeafIds_sublist _).nodup ?_
  have hid := Struct.structTree_leaves_id doc.body
  have : (Struct.leavesList #[] (Struct.ofDoc doc).children.toList).toList.map Prod.fst
      = List.range (Struct.leaves (Struct.ofBlocks doc.body)).size := by
    rw [← hid]
    rfl
  rw [this]
  exact List.nodup_range

/-- Before filling, every marked-content reference must come from a leaf
placeholder. This premise is specific to the PDF projection: an arbitrary
`StructElem` can already carry an `.mcid` absent from the page streams. -/
def Unfilled (es : Array StructElem) : Prop :=
  ∀ e ∈ es, ∀ p m, StructKid.mcid p m ∉ e.kids

private theorem forall_modify {α : Type} (P : α → Prop) (xs : Array α)
    (hxs : ∀ x ∈ xs, P x) (i : Nat) (f : α → α)
    (hf : ∀ x, P x → P (f x)) : ∀ x ∈ xs.modify i f, P x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [Array.getElem_modify]
  split
  · exact hf _ (hxs _ (xs.getElem_mem (by simpa using hj)))
  · exact hxs _ (xs.getElem_mem (by simpa using hj))

private theorem unfilled_addKid (es : Array StructElem) (h : Unfilled es)
    (holder : Nat) (kid : StructKid) (hk : ∀ p m, kid ≠ .mcid p m) :
    Unfilled (addKid es holder kid) := by
  apply forall_modify (fun (e : StructElem) => ∀ p m, StructKid.mcid p m ∉ e.kids) es h
  intro e he p m
  simp only [Array.mem_push]
  rintro (hold | hnew)
  · exact he p m hold
  · exact hk p m hnew.symm

private theorem unfilled_pushElem (es : Array StructElem) (h : Unfilled es)
    (parent : Nat) (e : StructElem) (he : ∀ p m, StructKid.mcid p m ∉ e.kids) :
    Unfilled (pushElem es parent e).1 := by
  intro e' he'
  rcases Array.mem_push.mp he' with hold | rfl
  · exact unfilled_addKid es h parent (.elem es.size) (by simp) e' hold
  · exact he

private theorem unfilled_bibEntryElems (es : Array StructElem) (h : Unfilled es)
    (parent : Nat) (openList : Option Nat) :
    Unfilled (bibEntryElems es parent openList).1 := by
  cases openList <;>
    simp only [bibEntryElems] <;>
    repeat apply unfilled_pushElem
  all_goals first | exact h | simp

private theorem unfilled_altElem (es : Array StructElem) (h : Unfilled es)
    (parent k : Nat) (a : Ir.Alt) : Unfilled (altElem es parent k a) := by
  cases a
  case decorative => exact h
  all_goals exact unfilled_pushElem es h parent _ (by simp [figureElem])

mutual

private theorem unfilled_skelList : ∀ (l : List Struct.Node) (es : Array StructElem)
    (parent holder : Nat) (inline : Bool) (openList : Option Nat),
    Unfilled es → Unfilled (skelList es parent holder inline openList l)
  | [], _, _, _, _, _, h => h
  | n :: rest, es, parent, holder, inline, openList, h => by
    exact unfilled_skelList rest _ _ _ _ _
      (unfilled_skelStep n es parent holder inline openList h)

private theorem unfilled_skelStep : ∀ (n : Struct.Node) (es : Array StructElem)
    (parent holder : Nat) (inline : Bool) (openList : Option Nat),
    Unfilled es → Unfilled (skelStep es parent holder inline openList n).1
  | .leaf k l, es, parent, holder, inline, openList, h => by
    cases l
    case text | linebreak => exact unfilled_addKid es h holder (.leaf k) (by simp)
    case image src a | picture a => exact unfilled_altElem es h parent k a
  | .node kind kids, es, parent, holder, inline, openList, h => by
    cases kind
    case aside => exact h
    case label => exact unfilled_skelList kids.toList es parent holder inline none h
    case bibEntry =>
      exact unfilled_skelList kids.toList _ _ _ _ _
        (unfilled_bibEntryElems es h parent openList)
    all_goals
      simp only [skelStep]
      split <;> exact unfilled_skelList kids.toList _ _ _ _ _
        (unfilled_pushElem es h parent _ (by simp [elemOf]))

end

/-- Every skeleton starts without marked-content references, for any input
tree. Thus `fill` alone introduces them from the numbered page streams. -/
theorem skeleton_unfilled_contract (t : Struct.Tree) : Unfilled (skeleton t) :=
  unfilled_skelList t.children.toList #[rootElem] 0 0 false none
    (by simp [Unfilled, rootElem])

/-- A fold reaches a persistent property when any of its inputs establishes
it. The state invariant supplies the premise of that establishing step. -/
private theorem foldl_reaches {α β : Type} (I Q : β → Prop) (f : β → α → β)
    (stable : ∀ b a, I b → I (f b a))
    (keep : ∀ b a, I b → Q b → Q (f b a)) :
    ∀ (xs : List α) (b : β), I b →
      (∃ a ∈ xs, ∀ b, I b → Q (f b a)) → Q (xs.foldl f b) := by
  intro xs
  induction xs with
  | nil => simp
  | cons a rest ih =>
    intro b hb ⟨hit, hh, force⟩
    rcases List.mem_cons.mp hh with heq | hh
    · subst hit
      have pair : I (rest.foldl f (f b a)) ∧ Q (rest.foldl f (f b a)) := by
        refine List.foldlRecOn (motive := fun out => I out ∧ Q out) rest f
          ⟨stable b a hb, force b hb⟩ ?_
        intro out ho x _
        exact ⟨stable out x ho.1, keep out x ho.1 ho.2⟩
      exact pair.2
    · exact ih (f b a) (stable b a hb) ⟨hit, hh, force⟩

private theorem assignOwner_size (i : Nat) (out : Array (Option Nat)) (kid : StructKid) :
    (assignOwner i out kid).size = out.size := by
  cases kid <;> simp [assignOwner]

private theorem assignOwner_present (i k : Nat) (out : Array (Option Nat)) (kid : StructKid)
    (h : ∃ j, out[k]? = some (some j)) :
    ∃ j, (assignOwner i out kid)[k]? = some (some j) := by
  cases kid with
  | elem | mcid => exact h
  | leaf l =>
    by_cases hl : l = k
    · subst l
      obtain ⟨j, hj⟩ := h
      have hk : k < out.size := (Array.getElem?_eq_some_iff.mp hj).1
      exact ⟨i, by simp [assignOwner, hk]⟩
    · simpa [assignOwner, Array.getElem?_setIfInBounds, hl] using h

private theorem ownerKids_size (e : StructElem) (i : Nat) (out : Array (Option Nat)) :
    (e.kids.foldl (assignOwner i) out).size = out.size := by
  refine Array.foldl_induction
    (motive := fun _ (acc : Array (Option Nat)) => acc.size = out.size) rfl ?_
  intro idx acc h
  exact (assignOwner_size i acc e.kids[idx]).trans h

private theorem ownerKids_present (e : StructElem) (i k : Nat) (out : Array (Option Nat))
    (h : ∃ j, out[k]? = some (some j)) :
    ∃ j, (e.kids.foldl (assignOwner i) out)[k]? = some (some j) := by
  refine Array.foldl_induction (motive := fun _ acc => ∃ j, acc[k]? = some (some j)) h ?_
  intro idx acc h
  exact assignOwner_present i k acc e.kids[idx] h

private theorem ownerKids_reaches (e : StructElem) (i k : Nat) (out : Array (Option Nat))
    (hk : k < out.size) (hmem : StructKid.leaf k ∈ e.kids) :
    ∃ j, (e.kids.foldl (assignOwner i) out)[k]? = some (some j) := by
  rw [← Array.foldl_toList]
  apply foldl_reaches (fun acc => acc.size = out.size)
    (fun acc => ∃ j, acc[k]? = some (some j)) (assignOwner i)
    (fun acc kid h => (assignOwner_size i acc kid).trans h)
    (fun acc kid _ h => assignOwner_present i k acc kid h) _ out rfl
  refine ⟨.leaf k, by simpa using hmem, ?_⟩
  intro acc hsize
  exact ⟨i, by simp [assignOwner, hsize, hk]⟩

private theorem leafOwners_present (es : Array StructElem) (n k : Nat) (e : StructElem)
    (he : e ∈ es) (hk : k < n) (hmem : StructKid.leaf k ∈ e.kids) :
    ∃ j, (leafOwners es n)[k]? = some (some j) := by
  unfold leafOwners
  apply foldl_reaches (fun acc => acc.size = n)
    (fun acc => ∃ j, acc[k]? = some (some j)) _
    (fun acc row h => (ownerKids_size row.1 row.2 acc).trans h)
    (fun acc row _ h => ownerKids_present row.1 row.2 k acc h) _ _ (by simp)
  obtain ⟨i, hi, hie⟩ := Array.mem_iff_getElem.mp he
  refine ⟨(e, i), ?_, ?_⟩
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa using (Array.getElem?_eq_some_iff.mpr ⟨hi, hie⟩)
  · intro acc hsize
    exact ownerKids_reaches e i k acc (by omega) hmem

private theorem flatMap_owner_unique {α β : Type} (f : α → List β) (xs : List α)
    (hn : (xs.flatMap f).Nodup) {i j : Nat} {a b : α} {x : β}
    (hi : xs[i]? = some a) (hj : xs[j]? = some b)
    (ha : x ∈ f a) (hb : x ∈ f b) : i = j := by
  obtain ⟨hibound, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjbound, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  have hp := (List.pairwise_flatMap.mp (List.nodup_iff_pairwise_ne.mp hn)).2
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact False.elim (hp.rel_getElem_of_lt hibound hjbound h x ha x hb rfl)
  · exact h
  · exact False.elim (hp.rel_getElem_of_lt hjbound hibound h x hb x ha rfl)

private theorem leafIdsOf_mem (e : StructElem) (k : Nat) (h : StructKid.leaf k ∈ e.kids) :
    k ∈ leafIdsOf e :=
  List.mem_filterMap.mpr ⟨.leaf k, Array.mem_toList_iff.mpr h, rfl⟩

/-- Completeness of the owner map: a bounded, uniquely held leaf names its
actual element. Together with `leafOwners_mem`, this is the inverse of the
skeleton's leaf-to-element relation, rather than a last-writer convention. -/
theorem leafOwners_covers (es : Array StructElem) (n : Nat)
    (hnodup : (leafKids es).Nodup) (i : Nat) (e : StructElem) (k : Nat)
    (hi : es[i]? = some e) (hk : k < n) (hmem : StructKid.leaf k ∈ e.kids) :
    (leafOwners es n)[k]? = some (some i) := by
  obtain ⟨j, hj⟩ := leafOwners_present es n k e (Array.mem_of_getElem? hi) hk hmem
  obtain ⟨e', he', hk'⟩ := leafOwners_mem es n k j hj
  have hij : i = j := flatMap_owner_unique leafIdsOf es.toList hnodup
    (by simpa using hi) (by simpa using he') (leafIdsOf_mem e k hmem) (leafIdsOf_mem e' k hk')
  exact hij ▸ hj

private def PagesSound (marks : Array (Array (Nat × Nat)))
    (out : Array (Array (Nat × Nat))) : Prop :=
  ∀ (k p m : Nat), (p, m) ∈ (out[k]?).getD #[] →
    ∃ pm, marks[p]? = some pm ∧ (m, k) ∈ pm

private theorem pagesSound_kids (marks : Array (Array (Nat × Nat))) (pm : Array (Nat × Nat))
    (p : Nat) (hp : marks[p]? = some pm) (out : Array (Array (Nat × Nat)))
    (ho : PagesSound marks out) :
    PagesSound marks (pm.foldl (fun acc (m, k) => acc.modify k (·.push (p, m))) out) := by
  refine Array.foldl_induction (motive := fun _ acc => PagesSound marks acc) ho ?_
  intro idx acc hacc k p' m' hm
  rw [Array.getElem?_modify] at hm
  split at hm
  next heq =>
    cases hget : acc[k]? with
    | none => simp [hget] at hm
    | some pairs =>
      simp only [hget, Option.map_some, Option.getD_some, Array.mem_push] at hm
      rcases hm with hold | hnew
      · exact hacc k p' m' (by simpa [hget] using hold)
      · rcases Prod.mk.inj hnew with ⟨rfl, rfl⟩
        exact ⟨pm, hp, by
          simpa only [← heq, Prod.eta, Fin.getElem_fin] using pm.getElem_mem idx.isLt⟩
  next => exact hacc k p' m' hm

/-- Every filled leaf reference comes from the marks of the named page.
This is the soundness invariant of both folds in `leafPagesOf`; it does
not assume that a leaf is bounded or that stream identifiers are ordered. -/
theorem leafPagesOf_mem (n : Nat) (marks : Array (Array (Nat × Nat))) (k p m : Nat)
    (h : (p, m) ∈ ((leafPagesOf n marks)[k]?).getD #[]) :
    ∃ pm, marks[p]? = some pm ∧ (m, k) ∈ pm := by
  have base : PagesSound marks (Array.replicate n #[]) := by
    intro k p m hm
    rw [Array.getElem?_replicate] at hm
    split at hm <;> simp_all
  have sound : PagesSound marks (leafPagesOf n marks) := by
    unfold leafPagesOf
    refine List.foldlRecOn _ _ base ?_
    intro out ho row hr
    exact pagesSound_kids marks row.1 row.2 (by
      simpa using List.mk_mem_zipIdx_iff_getElem?.mp hr) out ho
  exact sound k p m h

/-- Filling an unfilled element introduces exactly the marked-content
references of its own leaves. No reference can arrive from another element
or survive from an unrelated earlier fill. -/
theorem fillKids_mcid_exact (e : StructElem) (lp : Array (Array (Nat × Nat)))
    (he : ∀ p m, StructKid.mcid p m ∉ e.kids) (p m : Nat) :
    StructKid.mcid p m ∈ e.kids.flatMap (fillKid lp) ↔
      ∃ k, StructKid.leaf k ∈ e.kids ∧ (p, m) ∈ (lp[k]?).getD #[] := by
  constructor
  · intro hm
    obtain ⟨kid, hk, hm⟩ := Array.mem_flatMap.mp hm
    cases kid with
    | elem i => simp [fillKid] at hm
    | leaf k =>
      obtain ⟨⟨p', m'⟩, hpm, h⟩ := Array.mem_map.mp hm
      cases h
      exact ⟨k, hk, hpm⟩
    | mcid p' m' => exact False.elim (he p' m' hk)
  · rintro ⟨k, hk, hpm⟩
    exact Array.mem_flatMap.mpr ⟨.leaf k, hk, Array.mem_map.mpr ⟨(p, m), hpm, rfl⟩⟩

/-- Every marked-content reference of a filled element has that element as
its parent-tree entry (ISO 32000-2 §14.7.5.4). The skeleton must contain no
earlier `.mcid` references: `fill` preserves those, and an arbitrary one
need not occur in any page stream. `skeleton_unfilled_contract` proves that premise
for the producer, while `skeleton_leafKids_nodup` supplies unique ownership. -/
theorem parentTree_covers (es : Array StructElem) (n : Nat)
    (marks : Array (Array (Nat × Nat)))
    (hpos : ∀ p (hp : p < marks.size) j (hj : j < marks[p].size), (marks[p][j]).1 = j)
    (hnodup : (leafKids es).Nodup) (hlt : ∀ k ∈ leafKids es, k < n)
    (hunfilled : Unfilled es) :
    ∀ i (hi : i < (fill es (leafPagesOf n marks)).size) p m,
      StructKid.mcid p m ∈ (fill es (leafPagesOf n marks))[i].kids →
      ((parentTreeOf marks (leafOwners es n))[p]?).bind (·[m]?) = some (some i) := by
  intro i hi p m hm
  have hie : i < es.size := by simpa [fill] using hi
  have hem := es.getElem_mem hie
  have hm' : StructKid.mcid p m ∈ es[i].kids.flatMap (fillKid (leafPagesOf n marks)) := by
    simpa only [fill, Array.getElem_map] using hm
  obtain ⟨k, hk, hpm⟩ := (fillKids_mcid_exact es[i] _ (hunfilled es[i] hem) p m).mp hm'
  have hkall : k ∈ leafKids es :=
    List.mem_flatMap.mpr ⟨es[i], Array.mem_toList_iff.mpr hem, leafIdsOf_mem es[i] k hk⟩
  have howner := leafOwners_covers es n hnodup i es[i] k
    (Array.getElem?_eq_getElem hie) (hlt k hkall) hk
  obtain ⟨pm, hp, hmark⟩ := leafPagesOf_mem n marks k p m hpm
  obtain ⟨hpbound, hpage⟩ := Array.getElem?_eq_some_iff.mp hp
  obtain ⟨j, hj, hentry⟩ := Array.mem_iff_getElem.mp hmark
  have hmj : m = j := by
    have h := hpos p hpbound j (by simpa [hpage] using hj)
    simpa [hpage, hentry] using h
  have hslot : pm[m]? = some (m, k) := by
    subst m
    exact Array.getElem?_eq_some_iff.mpr ⟨hj, hentry⟩
  simp [parentTreeOf, hp, hslot, howner]

/-- Every placeholder a skeleton holds is drawn from its input tree.
Speaker notes and decorative figures may omit leaves, but cannot invent
one; this is the range premise of the parent-tree projection. -/
theorem skeleton_leafKids_mem (t : Struct.Tree) (k : Nat) (hk : k ∈ leafKids (skeleton t)) :
    k ∈ t.leaves.toList.map Prod.fst := by
  have hperm := skelList_leafKids t.children.toList #[rootElem] 0 0 false none (by simp)
  have hroot : leafKids #[rootElem] = [] := by
    simp [leafKids_eq_flatMap, leafIdsOf, rootElem]
  rw [hroot, List.nil_append] at hperm
  exact (skelLeafIds_sublist _).subset (hperm.mem_iff.mp hk)

/-- The actual document producer satisfies every skeleton premise:
fresh references, unique owners, and in-range leaf identifiers. Only the
page-stream numbering premise remains, supplied by `numberMarks_mcids_exact`
when content streams are numbered. -/
theorem doc_parentTree_covers (doc : Ir.Doc) (marks : Array (Array (Nat × Nat)))
    (hpos : ∀ p (hp : p < marks.size) j (hj : j < marks[p].size), (marks[p][j]).1 = j) :
    let t := Struct.ofDoc doc
    let es := skeleton t
    let n := t.leaves.size
    ∀ i (hi : i < (fill es (leafPagesOf n marks)).size) p m,
      StructKid.mcid p m ∈ (fill es (leafPagesOf n marks))[i].kids →
      ((parentTreeOf marks (leafOwners es n))[p]?).bind (·[m]?) = some (some i) := by
  apply parentTree_covers _ _ marks hpos (skeleton_leafKids_nodup doc)
    _ (skeleton_unfilled_contract _)
  intro k hk
  have hm := skeleton_leafKids_mem (Struct.ofDoc doc) k hk
  change k ∈ (Struct.leaves (Struct.ofBlocks doc.body)).toList.map Prod.fst at hm
  rw [Struct.structTree_leaves_id] at hm
  exact List.mem_range.mp hm

end LeanTex.Core.Pdf
