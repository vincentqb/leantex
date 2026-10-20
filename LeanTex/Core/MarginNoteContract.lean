module

public import LeanTex.Core.MarginNote

/-! Settling margin notes moves no text: the body reads the same words in the same order. -/

namespace LeanTex.Core.MarginNote

open LeanTex.Core LeanTex.Core.Ir

private theorem plainTextList_app (l1 l2 : List Inline) :
    plainTextList (l1 ++ l2) = plainTextList l1 ++ plainTextList l2 := by
  induction l1 with
  | nil => simp [plainTextList]
  | cons x rest ih => simp [plainTextList, ih, String.append_assoc]

private theorem flatten_go (l : List Inline) (acc : Array Inline) :
    plainTextList (l.foldl flattenStep acc).toList = plainTextList acc.toList ++ plainTextList l := by
  induction l generalizing acc with
  | nil => simp [plainTextList]
  | cons x rest ih =>
    rw [List.foldl_cons, ih]
    cases x <;> simp [flattenStep, plainTextList_app, plainTextList, plainTextOne, String.append_assoc]

public theorem flatten_text : Conserves plainText flatten := fun ys => by
  show plainTextList (flatten ys).toList = plainTextList ys.toList
  unfold flatten
  rw [← Array.foldl_toList, flatten_go]
  simp [plainTextList]

public theorem inlineAll_text (xs : Array Inline) : plainText (inlineAll xs) = plainText xs :=
  mapInlinesFinish_text id (fun _ => rfl) flatten flatten_text xs

mutual

public theorem keepOne_text (x : Inline) : plainTextOne (keepOne x).1 = plainTextOne x := by
  match x with
  | .styled st body => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .colored c n body => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .located sp body => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .role n body => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .link u body => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .decorated k body => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .onSteps spec body => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .altSteps spec a b => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .cited f ks ink => simp [keepOne, plainTextOne, keepList_text, plainTextList]
  | .boxed bx body =>
    have h : plainTextList (inlineAll body).toList = plainTextList body.toList := inlineAll_text body
    simp [keepOne, plainTextOne, h]
  | .footnote n body =>
    have h : plainTextList (inlineAll body).toList = plainTextList body.toList := inlineAll_text body
    simp [keepOne, plainTextOne, h]
  | .marginNote m body =>
    have h : plainTextList (inlineAll body).toList = plainTextList body.toList := inlineAll_text body
    simp [keepOne, plainTextOne, h]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _
  | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber
  | .pageCount | .linebreak _ => simp [keepOne]

public theorem keepList_text (out : Array Inline) (n : Array Diag.Noun) (xs : List Inline) :
    plainTextList (keepList out n xs).1.toList = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [keepList, plainTextList]
  | x :: rest =>
    rw [keepList, keepList_text]
    simp [plainTextList_app, plainTextList, keepOne_text, String.append_assoc]

end

private theorem setBetween_text (x : Inline) : plainTextOne (setBetween x) = plainTextOne x := by
  cases x <;> simp [setBetween, plainTextOne]

private theorem map_setBetween_text (xs : List Inline) :
    plainTextList (xs.map setBetween) = plainTextList xs := by
  induction xs with
  | nil => simp [plainTextList]
  | cons x rest ih => simp [plainTextList, setBetween_text, ih]

private theorem leading_text (c : Array Inline) :
    plainTextList (leading c).1.toList ++ plainTextList (leading c).2.toList =
      plainTextList c.toList := by
  simp only [leading, List.toList_toArray, ← plainTextList_app, List.takeWhile_append_dropWhile]

private theorem closeBlock_text (acc : String) (b : Block) :
    blockTextOne acc (closeBlock b).1 = blockTextOne acc b := by
  unfold closeBlock
  dsimp only
  split
  · rfl
  · exact mapBlockWith_text id id (fun _ => rfl) flatten flatten_text id (fun _ => rfl) acc b

private theorem blockTextList_push (acc : String) (l : List Block) (b : Block) :
    blockTextList acc (l ++ [b]) = blockTextOne (blockTextList acc l) b := by
  simp [blockTextList_append, blockTextList]

private theorem blockTextItems_push (acc : String) (out : Array (Array Block)) (x : Array Block) :
    blockTextItems acc (out.push x).toList =
      blockTextList (blockTextItems acc out.toList) x.toList := by
  simp only [Array.toList_push]
  induction out.toList generalizing acc with
  | nil => simp [blockTextItems]
  | cons y rest ih => simp [blockTextItems, ih]

private theorem blockTextOne_para (acc : String) (c : Array Inline) :
    blockTextOne acc (.para c) = acc ++ plainTextList c.toList := rfl

private theorem blockTextList_drop_push (acc : String) (out : Array Block) (x : Block)
    (ho : out = out.pop.push x) :
    blockTextList acc out.toList = blockTextOne (blockTextList acc out.toList.dropLast) x := by
  conv => lhs; rw [ho]
  simp [blockTextList_push]

private theorem eq_pop_push {out : Array Block} {x : Block} (h : out.back? = some x) :
    out = out.pop.push x := by
  apply Array.ext'
  rw [Array.back?_eq_some_iff] at h
  obtain ⟨ys, hys⟩ := h
  simp [hys]

private theorem leadInto_text (pend : Array Inline) (b b' : Block) (acc : String)
    (h : leadInto pend b = some b') :
    blockTextOne acc b' = blockTextOne (acc ++ plainTextList pend.toList) b := by
  cases b with
  | list o s items =>
    simp only [leadInto] at h
    rcases hit : items.toList with _ | ⟨first, more⟩
    · simp [hit] at h
    · rw [hit] at h
      simp only at h
      rcases hf : first.toList with _ | ⟨b0, restB⟩
      · simp [hf] at h
      · rw [hf] at h
        cases b0 with
        | para c =>
          simp only [Option.some.injEq] at h
          subst h
          simp [blockTextOne, hit, blockTextItems, hf, blockTextList, plainText, plainTextList_app,
            String.append_assoc]
        | _ => simp at h
  | _ => simp [leadInto] at h

private theorem flushPend_text (out : Array Block) (pend : Array Inline) (n : Array Diag.Noun)
    (b : Block) (acc : String) :
    blockTextList acc (flushPend out pend n b).1.toList =
      blockTextOne (blockTextList acc out.toList ++ plainTextList pend.toList) b := by
  have hi : plainTextList (inlineAll pend).toList = plainTextList pend.toList := inlineAll_text pend
  unfold flushPend
  split
  · rename_i h
    simp [Array.isEmpty_iff.mp h, blockTextList_push, plainTextList]
  · split
    · rename_i b' hl
      simp only [Array.toList_push, blockTextList_push]
      exact leadInto_text pend b b' _ hl
    · simp [blockTextList_append, blockTextList, blockTextOne_para, hi]

mutual

public theorem settleList_text (out : Array Block) (pend : Array Inline) (n : Array Diag.Noun)
    (bs : List Block) (acc : String) :
    blockTextList acc (settleList out pend n bs).1.toList =
      blockTextList (blockTextList acc out.toList ++ plainTextList pend.toList) bs := by
  match bs with
  | [] =>
    have hi : plainTextList (inlineAll pend).toList = plainTextList pend.toList := inlineAll_text pend
    simp only [settleList]
    split
    · rename_i h
      simp [Array.isEmpty_iff.mp h, blockTextList, plainTextList]
    · simp [blockTextList_append, blockTextList, blockTextOne_para, blockTextList, hi]
  | b :: rest =>
    have hb := settleOne_text b n (blockTextList acc out.toList ++ plainTextList pend.toList)
    simp only [settleList]
    generalize hs : settleOne b n = r at hb
    obtain ⟨b', n'⟩ := r
    simp only at hb ⊢
    rw [blockTextList, ← hb]
    match b' with
    | .para c =>
      simp only
      have hl := leading_text c
      generalize (leading c) = lb at hl ⊢
      obtain ⟨lead, body⟩ := lb
      simp only at hl ⊢
      split
      · rename_i pc hback _ hpend
        have hp : pend = #[] := Array.isEmpty_iff.mp hpend
        subst hp
        have ho := blockTextList_drop_push acc out _ (eq_pop_push hback)
        split
        · rename_i hbody
          have hbe : body = #[] := Array.isEmpty_iff.mp hbody
          subst hbe
          rw [settleList_text, ho]
          simp [blockTextList_append, blockTextList, blockTextOne_para, plainTextList, plainTextList_app,
            map_setBetween_text, ← hl, String.append_assoc]
        · rw [settleList_text, ho]
          simp [blockTextList_append, blockTextList, blockTextOne_para, plainTextList, plainTextList_app,
            map_setBetween_text, ← hl, String.append_assoc]
      · split
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          obtain ⟨hbody, -⟩ := hcond
          have hbe : body = #[] := Array.isEmpty_iff.mp hbody
          subst hbe
          rw [settleList_text]
          simp [blockTextOne_para, plainTextList, plainTextList_app, ← hl, String.append_assoc]
        · rw [settleList_text]
          simp [blockTextList_append, blockTextList, blockTextOne_para, plainTextList, plainTextList_app,
            String.append_assoc]
    | .section .. | .list .. | .center _ | .ragged .. | .spaced .. | .role .. | .link ..
    | .quote .. | .abstract _ | .titled .. | .disclosure .. | .equation .. | .verbatim ..
    | .algorithm .. | .columns _ | .onSteps .. | .altSteps .. | .note _ | .only .. | .nav ..
    | .logo _ | .pagebreak | .frame .. | .framefoot _ | .setPalette _ | .setTokens _ | .rule ..
    | .picture _ | .table .. | .float .. | .bibliography .. | .contents .. | .lines _ =>
      simp only
      rw [settleList_text, flushPend_text]
      simp [plainTextList]

public theorem settleOne_text (b : Block) (n : Array Diag.Noun) (acc : String) :
    blockTextOne acc (settleOne b n).1 = blockTextOne acc b := by
  match b with
  | .para c =>
    simp [settleOne, blockTextOne_para, keepList_text, plainTextList]
  | .section l st num title =>
    have h : plainTextList (inlineAll title).toList = plainTextList title.toList := inlineAll_text title
    simp [settleOne, blockTextOne, h, plainText]
  | .list o sp items =>
    simp [settleOne, blockTextOne, settleItems_text, blockTextItems]
  | .center body => simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .ragged sd body => simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .spaced g body => simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .role nm body => simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .link t body => simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .quote q body => simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .abstract body => simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .titled k title body =>
    have h : plainTextList (inlineAll title).toList = plainTextList title.toList := inlineAll_text title
    simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList, h, plainText]
  | .disclosure summary e body =>
    have h : plainTextList (inlineAll summary).toList = plainTextList summary.toList :=
      inlineAll_text summary
    simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList, h, plainText]
  | .onSteps spec body =>
    simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .altSteps spec a c =>
    simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .only targets body =>
    simp [settleOne, blockTextOne, settleList_text, blockTextList, plainTextList]
  | .lines _ | .equation _ _ | .verbatim _ _ _ | .algorithm _ _ _ | .columns _ | .note _
  | .nav _ _ | .logo _ | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _
  | .setTokens _ | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
  | .bibliography _ _ _ | .contents _ _ =>
    simp only [settleOne]
    exact closeBlock_text acc _

public theorem settleItems_text (out : Array (Array Block)) (n : Array Diag.Noun)
    (items : List (Array Block)) (acc : String) :
    blockTextItems acc (settleItems out n items).1.toList =
      blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [settleItems, blockTextItems]
  | item :: rest =>
    simp only [settleItems]
    rw [settleItems_text, blockTextItems_push, settleList_text]
    simp [blockTextItems, blockTextList, plainTextList]

end

private theorem closeAll_text (acc : String) (l : List Block) :
    blockTextList acc (l.map fun b => (closeBlock b).1) = blockTextList acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons b rest ih => simp only [List.map_cons, blockTextList, closeBlock_text, ih]

/-- Settling a body's margin notes keeps its text: the same words, in the same order. -/
public theorem settle_text (room : Bool) (body : Array Block) :
    blocksText (settle room body).1 = blocksText body := by
  unfold settle
  split
  · rfl
  · split
    · rw [blocksText, settleList_text]
      simp [blocksText, blockTextList, plainTextList]
    · simp only [blocksText, Array.toList_map, List.map_map]
      exact closeAll_text "" body.toList

end LeanTex.Core.MarginNote
