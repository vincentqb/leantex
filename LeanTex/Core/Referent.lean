module

public import LeanTex.Core.Ir

namespace LeanTex.Core.Ir

/-! Each label stands at the thing it names, where both artifacts set its anchor. -/

/-- The labels elaboration bound: the number of the heading each names, where it names one, and
every `\label`'s key; a `\hypertarget` names its own place, so it is in neither. -/
public structure ReferentKeys where
  headings : Std.HashMap String String
  labels : Std.HashSet String

/-- No label to move, as in a deck, whose labels stand on what is set next, as beamer's do. -/
public def ReferentKeys.empty : ReferentKeys := { headings := {}, labels := {} }

private def Inline.isLabel : Inline → Bool
  | .label _ => true
  | _ => false

/-- Whether an inline is a label naming the heading numbered `num`. -/
private def ReferentKeys.namesHeading (keys : ReferentKeys) (num : String) : Inline → Bool
  | .label k => keys.headings[k]? == some num
  | _ => false

/-- Whether an inline is a `\label`, which names the float it stands in. -/
private def ReferentKeys.isBound (keys : ReferentKeys) : Inline → Bool
  | .label k => keys.labels.contains k
  | _ => false

/-- The bound labels a body's top-level paragraphs hold, and the body without them, a paragraph
holding only those left out. -/
private def bodyLabels (keys : ReferentKeys) (body : Array Block) : Array Inline × Array Block :=
  body.foldl (bodyLabelStep keys) (#[], #[])
where
  bodyLabelStep (keys : ReferentKeys) (lo : Array Inline × Array Block) (b : Block) :
      Array Inline × Array Block :=
    if let .para content := b then
      let rest := content.filter (!keys.isBound ·)
      (lo.1 ++ content.filter keys.isBound,
        if rest.isEmpty && !content.isEmpty then lo.2 else lo.2.push (.para rest))
    else (lo.1, lo.2.push b)

/-- A float's bound labels at its top: its caption's start where the caption stands above, else its
body's first paragraph's (the caption package's `hypcap`). -/
private def floatLabelsTop (keys : ReferentKeys) (capAbove : Bool) (body : Array Block)
    (caption : Array Inline) : Array Block × Array Inline :=
  let (inBody, body) := bodyLabels keys body
  let labels := inBody ++ caption.filter keys.isBound
  let caption := caption.filter (!keys.isBound ·)
  if capAbove then (body, labels ++ caption)
  else if let some (.para c) := (body[0]? : Option Block) then
    (#[.para (labels ++ c)] ++ body.extract 1, caption)
  else if labels.isEmpty then (body, caption)
  else (#[.para labels] ++ body, caption)

/-- The heading a block opens, its index and number where it is a numbered one. -/
private def nextOpen (cur : Option (Nat × String)) (i : Nat) (b : Block) : Option (Nat × String) :=
  if let .section _ _ n _ := b then n.map (i, ·) else cur

/-- Each block's open heading, from block `i` on: the index and number of the last numbered heading
before it, none before one or past an unnumbered one. -/
private def openHeadings (cur : Option (Nat × String)) (i : Nat)
    (out : Array (Option (Nat × String))) : List Block → Array (Option (Nat × String))
  | [] => out
  | b :: rest => openHeadings (nextOpen cur i b) (i + 1) (out.push cur) rest

/-- The labels each heading gains: those the paragraphs under it hold that name it. -/
private def headingGains (keys : ReferentKeys) (xs : Array Block)
    (opens : Array (Option (Nat × String))) : Array (Array Inline) := Id.run do
  let mut gains : Array (Array Inline) := Array.replicate xs.size #[]
  for (b, i) in xs.zipIdx do
    if let .para content := b then
      if let some (some (j, num)) := opens[i]? then
        gains := gains.modify j (· ++ content.filter (keys.namesHeading num))
  return gains

/-- One block of the heading rule: a heading with the labels it gains, a paragraph under a numbered
heading without the labels naming it, left out where it held only those. -/
private def headingPush (keys : ReferentKeys) (opens : Array (Option (Nat × String)))
    (gains : Array (Array Inline)) (out : Array Block) (i : Nat) (b : Block) : Array Block :=
  if let .section l s n title := b then
    out.push (.section l s n (title ++ (gains[i]?.getD #[]).filter Inline.isLabel))
  else if let .para content := b then
    if let some (some (_, num)) := opens[i]? then
      let rest := content.filter (!keys.namesHeading num ·)
      if rest.isEmpty && !content.isEmpty then out else out.push (.para rest)
    else out.push b
  else out.push b

private def headingList (keys : ReferentKeys) (opens : Array (Option (Nat × String)))
    (gains : Array (Array Inline)) (out : Array Block) (i : Nat) : List Block → Array Block
  | [] => out
  | b :: rest => headingList keys opens gains (headingPush keys opens gains out i b) (i + 1) rest

/-- Each label naming a heading into that heading, from the paragraphs set under it, as hyperref
anchors a `\label` at the heading its `\@currentHref` names. -/
private def headingReferents (keys : ReferentKeys) (xs : Array Block) : Array Block :=
  let opens := openHeadings none 0 #[] xs.toList
  headingList keys opens (headingGains keys xs opens) #[] 0 xs.toList

mutual

private def referentList (keys : ReferentKeys) (out : Array Block) : List Block → Array Block
  | [] => out
  | b :: rest => referentList keys (out.push (referentOne keys b)) rest

private def referentOne (keys : ReferentKeys) : Block → Block
  | .float k n ca body caption =>
    let (body, caption) :=
      floatLabelsTop keys ca (headingReferents keys (referentList keys #[] body.toList)) caption
    .float k n ca body caption
  | .list o items => .list o (referentItems keys #[] items.toList)
  | .center body => .center (headingReferents keys (referentList keys #[] body.toList))
  | .ragged s body => .ragged s (headingReferents keys (referentList keys #[] body.toList))
  | .quote body => .quote (headingReferents keys (referentList keys #[] body.toList))
  | .abstract body => .abstract (headingReferents keys (referentList keys #[] body.toList))
  | .titled kind title body =>
    .titled kind title (headingReferents keys (referentList keys #[] body.toList))
  | .disclosure summary expanded body =>
    .disclosure summary expanded (headingReferents keys (referentList keys #[] body.toList))
  | .role n body => .role n (headingReferents keys (referentList keys #[] body.toList))
  | .link target body => .link target (headingReferents keys (referentList keys #[] body.toList))
  | .spaced g body => .spaced g (headingReferents keys (referentList keys #[] body.toList))
  | .columns cols => .columns (referentCols keys #[] cols.toList)
  | .onSteps spec body => .onSteps spec (headingReferents keys (referentList keys #[] body.toList))
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (headingReferents keys (referentList keys #[] firstPage.toList))
      (headingReferents keys (referentList keys #[] otherPage.toList))
  | .only targets body => .only targets (headingReferents keys (referentList keys #[] body.toList))
  | .nav spec body => .nav spec (headingReferents keys (referentList keys #[] body.toList))
  | .frame t s v br body => .frame t s v br (headingReferents keys (referentList keys #[] body.toList))
  | .para content => .para content
  | .equation n content => .equation n content
  | .section l st num title => .section l st num title
  | .verbatim c s sp => .verbatim c s sp
  | .algorithm n sm lines => .algorithm n sm lines
  | .note body => .note body
  | .framefoot content => .framefoot content
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .logo content => .logo content
  | .rule c nm th => .rule c nm th
  | .picture p => .picture p
  | .table cols pl pr rows rules spans => .table cols pl pr rows rules spans
  | .bibliography src style items => .bibliography src style items

private def referentItems (keys : ReferentKeys) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest =>
    referentItems keys (out.push (headingReferents keys (referentList keys #[] item.toList))) rest

private def referentCols (keys : ReferentKeys) (out : Array (BoxWidth × Array Block)) :
    List (BoxWidth × Array Block) → Array (BoxWidth × Array Block)
  | [] => out
  | (w, body) :: rest =>
    referentCols keys (out.push (w, headingReferents keys (referentList keys #[] body.toList))) rest

end

/-- Each label to the thing it names: a heading's from the paragraphs under it, a float's to the
float's top, as hyperref and the caption package anchor them. -/
public def anchorReferents (keys : ReferentKeys) (xs : Array Block) : Array Block :=
  headingReferents keys (referentList keys #[] xs.toList)

private theorem plainTextList_append' (l1 l2 : List Inline) :
    plainTextList (l1 ++ l2) = plainTextList l1 ++ plainTextList l2 := by
  induction l1 with
  | nil => simp [plainTextList]
  | cons x rest ih => simp [plainTextList, ih, String.append_assoc]

private theorem plainText_append' (a b : Array Inline) :
    plainText (a ++ b) = plainText a ++ plainText b := by
  simp [plainText, plainTextList_append']

private theorem label_text (x : Inline) (h : x.isLabel = true) : plainTextOne x = "" := by
  cases x <;> simp_all [Inline.isLabel, plainTextOne]

private theorem namesHeading_label (keys : ReferentKeys) (num : String) (x : Inline)
    (h : keys.namesHeading num x = true) : x.isLabel = true := by
  cases x <;> simp_all [ReferentKeys.namesHeading, Inline.isLabel]

private theorem isBound_label (keys : ReferentKeys) (x : Inline) (h : keys.isBound x = true) :
    x.isLabel = true := by
  cases x <;> simp_all [ReferentKeys.isBound, Inline.isLabel]

private theorem plainText_filter_named (p : Inline → Bool) (hp : ∀ x, p x = true → x.isLabel = true)
    (xs : Array Inline) : plainText (xs.filter p) = "" := by
  have h : ∀ l : List Inline, (∀ x ∈ l, p x = true) → plainTextList l = "" := by
    intro l hl
    induction l with
    | nil => simp [plainTextList]
    | cons x rest ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hl
      simp only [plainTextList]
      rw [label_text x (hp x hl.1), ih hl.2]
      rfl
  apply h
  intro x hx
  simp only [Array.toList_filter, List.mem_filter] at hx
  exact hx.2

private theorem plainText_filter_unnamed (p : Inline → Bool)
    (hp : ∀ x, p x = true → x.isLabel = true) (xs : Array Inline) :
    plainText (xs.filter (!p ·)) = plainText xs := by
  have h : ∀ l : List Inline, plainTextList (l.filter (!p ·)) = plainTextList l := by
    intro l
    induction l with
    | nil => simp [plainTextList]
    | cons x rest ih =>
      cases hx : p x
      · simp [List.filter, hx, plainTextList, ih]
      · simp [List.filter, hx, plainTextList, ih, label_text x (hp x hx)]
  simp [plainText, h]

private theorem blockTextItems_append (l1 l2 : List (Array Block)) (acc : String) :
    blockTextItems acc (l1 ++ l2) = blockTextItems (blockTextItems acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextItems]
  | cons item rest ih => simp [blockTextItems, ih]

private theorem blockTextColumns_append (l1 l2 : List (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (l1 ++ l2) = blockTextColumns (blockTextColumns acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextColumns]
  | cons c rest ih => simp [blockTextColumns, ih]

private theorem push_text (out : Array Block) (b : Block) (acc : String) :
    blockTextList acc (out.push b).toList = blockTextOne (blockTextList acc out.toList) b := by
  simp [Array.toList_push, blockTextList_append, blockTextList]

private theorem bodyLabelStep_text (keys : ReferentKeys) (lo : Array Inline × Array Block)
    (b : Block) (acc : String) :
    plainText (bodyLabels.bodyLabelStep keys lo b).1 = plainText lo.1 ∧
      blockTextList acc (bodyLabels.bodyLabelStep keys lo b).2.toList =
        blockTextOne (blockTextList acc lo.2.toList) b := by
  have hb := isBound_label keys
  unfold bodyLabels.bodyLabelStep
  split
  · rename_i content
    refine ⟨by rw [plainText_append', plainText_filter_named _ hb, String.append_empty], ?_⟩
    dsimp only
    split
    · rename_i he
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
      have hz : plainText content = "" := by
        rw [← plainText_filter_unnamed _ hb, Array.isEmpty_iff.mp he.1]
        rfl
      simp [blockTextOne, hz]
    · rw [push_text]
      simp [blockTextOne, plainText_filter_unnamed _ hb]
  · exact ⟨rfl, push_text _ _ _⟩

private theorem bodyLabels_fold (keys : ReferentKeys) (l : List Block)
    (lo : Array Inline × Array Block) (acc : String) :
    plainText (l.foldl (bodyLabels.bodyLabelStep keys) lo).1 = plainText lo.1 ∧
      blockTextList acc (l.foldl (bodyLabels.bodyLabelStep keys) lo).2.toList =
        blockTextList (blockTextList acc lo.2.toList) l := by
  induction l generalizing lo with
  | nil => simp [blockTextList]
  | cons b rest ih =>
    obtain ⟨s1, s2⟩ := bodyLabelStep_text keys lo b acc
    obtain ⟨h1, h2⟩ := ih (bodyLabels.bodyLabelStep keys lo b)
    refine ⟨h1.trans s1, ?_⟩
    rw [List.foldl_cons, h2, s2]
    rfl

private theorem bodyLabels_text (keys : ReferentKeys) (body : Array Block) (acc : String) :
    plainText (bodyLabels keys body).1 = "" ∧
      blockTextList acc (bodyLabels keys body).2.toList = blockTextList acc body.toList := by
  have h := bodyLabels_fold keys body.toList (#[], #[]) acc
  simp only [Array.foldl_toList] at h
  unfold bodyLabels
  exact ⟨h.1, by simpa [blockTextList] using h.2⟩

private theorem floatLabelsTop_text (keys : ReferentKeys) (k : FloatKind) (n : Option Nat)
    (ca : Bool) (body : Array Block) (caption : Array Inline) (acc : String) :
    blockTextOne acc (.float k n ca (floatLabelsTop keys ca body caption).1
      (floatLabelsTop keys ca body caption).2) = blockTextOne acc (.float k n ca body caption) := by
  have hbd := isBound_label keys
  have hl := (bodyLabels_text keys body "").1
  have hb := fun acc => (bodyLabels_text keys body acc).2
  have hlabels : plainText ((bodyLabels keys body).1 ++ caption.filter keys.isBound) = "" := by
    rw [plainText_append', hl, plainText_filter_named _ hbd]; rfl
  have hcap := plainText_filter_unnamed _ hbd caption
  simp only [blockTextOne]
  unfold floatLabelsTop
  by_cases hca : ca = true
  · simp only [hca, ite_true, plainText_append', hlabels, String.empty_append, hcap, hb]
  · simp only [hca, Bool.false_eq_true, ite_false]
    split
    · rename_i c hc
      obtain ⟨rest, hr⟩ : ∃ rest, (bodyLabels keys body).2.toList = .para c :: rest := by
        cases h : (bodyLabels keys body).2.toList with
        | nil => simp [← Array.getElem?_toList, h] at hc
        | cons y rest =>
          refine ⟨rest, ?_⟩
          rw [← Array.getElem?_toList, h] at hc
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          rw [hc]
      have hsz : (bodyLabels keys body).2.size = rest.length + 1 := by
        rw [← Array.length_toList, hr]; rfl
      have hx : (#[Block.para (((bodyLabels keys body).1 ++ caption.filter keys.isBound) ++ c)] ++
          (bodyLabels keys body).2.extract 1).toList = .para (((bodyLabels keys body).1 ++
            caption.filter keys.isBound) ++ c) :: rest := by
        simp [Array.toList_extract, hr, hsz]
      rw [hx, hcap, ← hb (acc ++ plainText caption), hr]
      simp [blockTextList, blockTextOne, plainText_append', hl, plainText_filter_named _ hbd]
    · split
      · rw [hcap, hb]
      · simp [blockTextList, blockTextOne, hlabels, hcap, hb]

private theorem headingPush_text (keys : ReferentKeys) (opens : Array (Option (Nat × String)))
    (gains : Array (Array Inline)) (out : Array Block) (i : Nat) (b : Block) (acc : String) :
    blockTextList acc (headingPush keys opens gains out i b).toList =
      blockTextOne (blockTextList acc out.toList) b := by
  unfold headingPush
  split
  · rw [push_text]
    simp [blockTextOne, plainText_append', plainText_filter_named _ (fun _ h => h)]
  · split
    · rename_i content _
      split
      · rename_i num _
        have hn := namesHeading_label keys num
        dsimp only
        split
        · rename_i he
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
          have hz : plainText content = "" := by
            rw [← plainText_filter_unnamed _ hn, Array.isEmpty_iff.mp he.1]
            rfl
          simp [blockTextOne, hz]
        · rw [push_text]
          simp [blockTextOne, plainText_filter_unnamed _ hn]
      · exact push_text _ _ _
    · exact push_text _ _ _

private theorem headingList_text (keys : ReferentKeys) (opens : Array (Option (Nat × String)))
    (gains : Array (Array Inline)) (l : List Block) (out : Array Block) (i : Nat) (acc : String) :
    blockTextList acc (headingList keys opens gains out i l).toList =
      blockTextList (blockTextList acc out.toList) l := by
  induction l generalizing out i with
  | nil => simp [headingList, blockTextList]
  | cons b rest ih =>
    rw [headingList, ih, headingPush_text]
    rfl

private theorem headingReferents_text (keys : ReferentKeys) (xs : Array Block) (acc : String) :
    blockTextList acc (headingReferents keys xs).toList = blockTextList acc xs.toList := by
  simp [headingReferents, headingList_text, blockTextList]

mutual

private theorem referentList_text (keys : ReferentKeys) (xs : List Block) (out : Array Block)
    (acc : String) :
    blockTextList acc (referentList keys out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [referentList, blockTextList]
  | b :: rest =>
    rw [referentList, referentList_text keys rest, push_text, referentOne_text keys b]
    rfl

private theorem referentOne_text (keys : ReferentKeys) (b : Block) (acc : String) :
    blockTextOne acc (referentOne keys b) = blockTextOne acc b := by
  match b with
  | .float k n ca body caption =>
    rw [referentOne, floatLabelsTop_text]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] _,
      blockTextList]
  | .list o items =>
    rw [referentOne]
    simp [blockTextOne, referentItems_text keys items.toList #[] acc, blockTextItems]
  | .center body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .ragged _ body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .quote body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .abstract body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .titled kind title body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] _,
      blockTextList]
  | .disclosure summary expanded body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] _,
      blockTextList]
  | .role n body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .link target body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .spaced g body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .columns cols =>
    rw [referentOne]
    simp [blockTextOne, referentCols_text keys cols.toList #[] acc, blockTextColumns]
  | .onSteps spec body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .altSteps spec firstPage otherPage =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys firstPage.toList #[],
      referentList_text keys otherPage.toList #[], blockTextList]
  | .only targets body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .nav spec body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] acc,
      blockTextList]
  | .frame t s v _ body =>
    rw [referentOne]
    simp [blockTextOne, headingReferents_text, referentList_text keys body.toList #[] _,
      blockTextList]
  | .para _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .note _ | .framefoot _
  | .pagebreak | .setPalette _ | .setTokens _ | .algorithm _ _ _ | .logo _ | .rule _ _ _
  | .picture _ | .table _ _ _ _ _ _ | .bibliography _ _ _ => rfl

private theorem referentItems_text (keys : ReferentKeys) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (referentItems keys out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [referentItems, blockTextItems]
  | item :: rest =>
    rw [referentItems, referentItems_text keys rest]
    simp [blockTextItems, headingReferents_text, referentList_text keys item.toList #[],
      blockTextList, blockTextItems_append]

private theorem referentCols_text (keys : ReferentKeys) (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (referentCols keys out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [referentCols, blockTextColumns]
  | (w, body) :: rest =>
    rw [referentCols, referentCols_text keys rest]
    simp [blockTextColumns, headingReferents_text, referentList_text keys body.toList #[],
      blockTextList, blockTextColumns_append]

end

public theorem anchorReferents_text (keys : ReferentKeys) :
    Conserves blocksText (anchorReferents keys) := fun xs => by
  simp [blocksText, anchorReferents, headingReferents_text,
    referentList_text keys xs.toList #[] "", blockTextList]

public theorem anchorReferents_para_exact (keys : ReferentKeys) (xs : Array Inline) :
    anchorReferents keys #[.para xs] = #[.para xs] := by
  simp [anchorReferents, referentList, referentOne, headingReferents, openHeadings, headingList,
    headingPush]

end LeanTex.Core.Ir
