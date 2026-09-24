import LeanTex.Core.Struct
import LeanTex.Core.PdfContent

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
  attrs : Array (String × String) := #[]
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

/-- One node, with the list the next reference entry may join. A text,
break or picture leaf is a placeholder in its holder; an image leaf is its
own `Figure`, with `/Alt` exactly when the document gave one (an empty
alternative is no alternative — the figure fails honestly rather than
hiding); a speaker note (`.aside`) is not page content and emits nothing;
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
    | .picture => (addKid es holder (.leaf k), none)
    | .image _ alt =>
      ((pushElem es parent { s := structTypeOf .figure, kids := #[.leaf k],
                             alt := if alt.isEmpty then none else some alt }).1, none)
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

/-- The element holding each leaf `k < n`: the one whose kids carry
`.leaf k`. The soundness half — an owner listed does hold the leaf — is
`leafOwners_mem`; that each leaf is held once is the skeleton's
(`skeleton_leafKids_nodup`). -/
def leafOwners (es : Array StructElem) (n : Nat) : Array (Option Nat) :=
  (es.toList.zipIdx).foldl (fun out (e, i) =>
    e.kids.foldl (fun out k =>
      match k with
      | .leaf j => out.setIfInBounds j (some i)
      | .elem _ => out
      | .mcid _ _ => out) out) (Array.replicate n none)

/-- Every owner an answer map records holds the leaf it is recorded for:
the invariant `leafOwners`' fold preserves. -/
private def OwnerSound (es : Array StructElem) (out : Array (Option Nat)) : Prop :=
  ∀ j i, out[j]? = some (some i) → ∃ e, es[i]? = some e ∧ StructKid.leaf j ∈ e.kids

private theorem ownerSound_kids {es : Array StructElem} {e : StructElem} {i : Nat}
    (hi : es[i]? = some e) {out : Array (Option Nat)} (ho : OwnerSound es out) :
    OwnerSound es (e.kids.foldl (fun out k =>
      match k with
      | .leaf j => out.setIfInBounds j (some i)
      | .elem _ => out
      | .mcid _ _ => out) out) := by
  refine Array.foldl_induction (motive := fun _ acc => OwnerSound es acc) ho ?_
  intro idx acc hacc
  have hmem : e.kids[idx.1] ∈ e.kids := e.kids.getElem_mem idx.isLt
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
    cases l <;> simp [skelStep, headingsOf_addKid, headingsOf_pushElem,
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

/-- The leaf ids the skeleton walk reaches, in preorder: every leaf outside a
speaker note. The descent is the engine's own classifier — `skelStep` emits
nothing at all for `.aside`, which is exactly what `Kind.outlineDescends`
says — so this is the walk's census and not a transcription of it. -/
def skelLeafFold : Struct.NodeFold (Array Nat) where
  leaf := fun out id _ => out.push id
  enter := fun out _ => out
  descends := Struct.Kind.outlineDescends

theorem skelLeafAppends : Struct.Appends skelLeafFold where
  leaf := by intro out id l; simp [skelLeafFold]
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
    skelLeafIdsOne (.leaf k l) = #[k] := rfl

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
        | exact Nat.le_of_lt (size_le_pushElem es parent _)
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
    cases l <;> simp only [skelStep, skelLeafIdsOne_leaf] <;>
      first
        | exact leafKids_addKid_leaf es holder k hh
        | (rw [leafKids_pushElem]; simp [leafIdsOf])
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
    simp [skelLeafIdsOne_leaf, Struct.leavesOne, Struct.foldNode_leaf_exact, Struct.leavesFold]
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

end LeanTex.Core.Pdf
