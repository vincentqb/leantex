module

public import LeanTex.Core.HtmlResource
public import LeanTex.Core.HtmlReadProof
public import LeanTex.Core.HtmlRun
import all LeanTex.Core.Html
import all LeanTex.Core.HtmlRead
import all LeanTex.Core.HtmlReadProof
import all LeanTex.Core.HtmlResource

/-! What a parsed page runs, and the publication gate's bound on it: a closed page whose tree
reads as a stack runs only the scripts it admits. -/

namespace LeanTex.Core.HtmlRead

mutual

theorem runsInto_acc (acc : Array Run) : (d : Dom) → Dom.runsInto acc d = acc ++ Dom.runsInto #[] d
  | .text _ => by simp [Dom.runsInto]
  | .elem tag attrs kids => by
    simp only [Dom.runsInto]
    rw [runsListInto_acc (acc ++ _) kids.toList, runsListInto_acc (#[] ++ _) kids.toList]
    simp [Array.append_assoc]

theorem runsListInto_acc (acc : Array Run) :
    (l : List Dom) → Dom.runsListInto acc l = acc ++ Dom.runsListInto #[] l
  | [] => by simp [Dom.runsListInto]
  | d :: rest => by
    simp only [Dom.runsListInto]
    rw [runsListInto_acc (Dom.runsInto acc d) rest, runsInto_acc acc d,
      runsListInto_acc (Dom.runsInto #[] d) rest, Array.append_assoc]

end

theorem runs_text (s : String) : Dom.runs (.text s) = [] := rfl

theorem runs_elem (tag : String) (attrs : Array (String × String)) (kids : Array Dom) :
    Dom.runs (.elem tag attrs kids) = elemRuns tag attrs kids ++ Dom.runsList kids.toList := by
  simp only [Dom.runs, Dom.runsList, Dom.runsInto]
  rw [runsListInto_acc]
  simp

theorem runsList_nil : Dom.runsList [] = [] := rfl

theorem runsList_cons (d : Dom) (rest : List Dom) :
    Dom.runsList (d :: rest) = Dom.runs d ++ Dom.runsList rest := by
  simp only [Dom.runsList, Dom.runs, Dom.runsListInto]
  rw [runsListInto_acc]
  simp

end LeanTex.Core.HtmlRead

namespace LeanTex.Core.HtmlResource

open HtmlRead Html

/-- Whether a request is no refusal and, a script, one of `scripts`. -/
def okReq (scripts : Array String) : Request → Bool
  | .refused _ => false
  | .script js => scripts.any fun s => !s.isEmpty && js == s
  | .url _ | .localFragment _ => true

theorem okReq_of_resolves {resources : Array Embedded} {svgChecked : Array ByteArray}
    {scripts : Array String} {q : Request} (h : resolves resources svgChecked scripts q = true) :
    okReq scripts q = true := by
  cases q <;> simp_all [resolves, okReq]

/-- A run a page may make: an admitted script, white space at its ends aside. -/
def Good (scripts : Array String) (x : Run) : Prop :=
  ∃ js ∈ scripts, x = .script (trimWs js.toList)

/-! ### Requests accumulate -/

theorem foldl_append_acc {β : Type} (f : β → Array Request) (l : List β) (acc : Array Request) :
    l.foldl (fun acc b => acc ++ f b) acc = acc ++ l.foldl (fun acc b => acc ++ f b) #[] := by
  induction l generalizing acc with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldl_cons]
    rw [ih (acc ++ f b), ih (#[] ++ f b), Array.empty_append, Array.append_assoc]

theorem mem_attrRequests {tag : String} {attrs : Array (String × String)} {kv : String × String}
    (hkv : kv ∈ attrs) {q : Request} (hq : q ∈ attrRequest tag attrs kv) :
    q ∈ attrRequests tag attrs := by
  unfold attrRequests
  rw [← Array.foldl_toList]
  have hkv' : kv ∈ attrs.toList := Array.mem_toList_iff.mpr hkv
  generalize attrs.toList = l at hkv'
  induction l with
  | nil => simp at hkv'
  | cons b rest ih =>
    simp only [List.foldl_cons]
    rw [foldl_append_acc]
    rcases List.mem_cons.mp hkv' with rfl | h
    · exact Array.mem_append_left _ (by simpa using hq)
    · exact Array.mem_append_right _ (ih h)

mutual

theorem nodeRequests_acc (rta : Bool) (acc : Array Request) :
    (n : Html.Node) → nodeRequests rta acc n = acc ++ nodeRequests rta #[] n
  | .text _ => by simp [nodeRequests]
  | .style css => by cases rta <;> simp [nodeRequests]
  | .script attrs js => by
    cases rta
    · simp [nodeRequests]
    · simp only [nodeRequests, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Array.empty_append]
      split <;> split <;> simp
  | .elem tag attrs kids => by
    simp only [nodeRequests, Array.empty_append]
    rw [listRequests_acc]
    conv => rhs; rw [listRequests_acc]
    split <;> simp [Array.append_assoc]

theorem listRequests_acc (rta : Bool) (acc : Array Request) :
    (l : List Html.Node) → listRequests rta acc l = acc ++ listRequests rta #[] l
  | [] => by simp [listRequests]
  | n :: rest => by
    simp only [listRequests]
    rw [listRequests_acc rta (nodeRequests rta acc n) rest, nodeRequests_acc rta acc n,
      listRequests_acc rta (nodeRequests rta #[] n) rest, Array.append_assoc]

end

/-! ### Attributes -/

theorem toLower_lower (s : String) : s.toLower = lower s := by
  apply String.ext
  simp [String.toLower, lower]

theorem attrRequest_refused_on (tag : String) (attrs : Array (String × String))
    (kv : String × String) (h : (lower kv.1).startsWith "on" = true) :
    ∃ r, Request.refused r ∈ attrRequest tag attrs kv := by
  obtain ⟨name, value⟩ := kv
  simp only at h
  unfold attrRequest
  dsimp only
  rw [toLower_lower]
  split
  · exact ⟨_, Array.mem_singleton.mpr rfl⟩
  · simp only [h, Bool.true_or, ↓reduceIte]
    exact ⟨_, Array.mem_singleton.mpr rfl⟩

theorem attrRequest_refused_link (tag : String) (attrs : Array (String × String))
    (kv : String × String) (hs : Html.scriptLink (lower kv.1) kv.2 = true) :
    ∃ r, Request.refused r ∈ attrRequest tag attrs kv := by
  obtain ⟨name, value⟩ := kv
  simp only at hs
  unfold attrRequest
  dsimp only
  rw [toLower_lower]
  split
  · exact ⟨_, Array.mem_singleton.mpr rfl⟩
  · split
    · exact ⟨_, Array.mem_singleton.mpr rfl⟩
    · exact ⟨_, Array.mem_singleton.mpr rfl⟩

theorem attrRuns_nil {scripts : Array String} (tag : String) (attrs : Array (String × String))
    (h : (attrRequests tag attrs).all (okReq scripts) = true) :
    attrRuns (lowAttrs attrs).toList = [] := by
  have refusedNot : ∀ kv ∈ attrs, ∀ r, Request.refused r ∉ attrRequest tag attrs kv := by
    intro kv hkv r hr
    have := (Array.all_eq_true'.mp h) _ (mem_attrRequests hkv hr)
    simp [okReq] at this
  simp only [attrRuns, lowAttrs, Array.toList_map, List.flatMap_map, List.flatMap_eq_nil_iff,
    List.append_eq_nil_iff]
  intro kv hkv
  have hkv' : kv ∈ attrs := Array.mem_toList_iff.mp hkv
  constructor
  · split
    · next hon =>
      obtain ⟨r, hr⟩ := attrRequest_refused_on tag attrs kv hon
      exact absurd hr (refusedNot kv hkv' r)
    · rfl
  · split
    · next hs =>
      obtain ⟨r, hr⟩ := attrRequest_refused_link tag attrs kv hs
      exact absurd hr (refusedNot kv hkv' r)
    · rfl

theorem dataBlock_lowAttrs (attrs : Array (String × String)) :
    dataBlock (lowAttrs attrs) = (attr attrs "type" == "application/ld+json") := by
  simp only [dataBlock, lowAttrs, attr, Array.find?_map, Function.comp_def, toLower_lower]
  cases attrs.find? (fun a => lower a.1 == "type") <;> simp

/-! ### Runs of the tree the parser builds -/

theorem runsList_append (a b : List Dom) :
    Dom.runsList (a ++ b) = Dom.runsList a ++ Dom.runsList b := by
  induction a with
  | nil => simp [runsList_nil]
  | cons d rest ih => simp [runsList_cons, ih, List.append_assoc]

theorem runsList_push (K : Array Dom) (d : Dom) :
    Dom.runsList (K.push d).toList = Dom.runsList K.toList ++ Dom.runs d := by
  simp [Array.toList_push, runsList_append, runsList_cons, runsList_nil]

theorem runsList_addChar (K : Array Dom) (c : Char) :
    Dom.runsList (addChar K c).toList = Dom.runsList K.toList := by
  unfold addChar
  split
  · next s hb =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    simp [runsList_append, runsList_cons, runsList_nil, runs_text]
  · simp [runsList_append, runsList_cons, runsList_nil, runs_text]

theorem runsList_addL (K : Array Dom) (cs : List Char) :
    Dom.runsList (addL K cs).toList = Dom.runsList K.toList := by
  induction cs generalizing K with
  | nil => simp [addL]
  | cons c rest ih =>
    simp only [addL, List.foldl_cons] at ih ⊢
    rw [ih, runsList_addChar]

theorem dropWhile_ws_append {w l : List Char} (hw : ∀ c ∈ w, isWs c = true) :
    (w ++ l).dropWhile isWs = l.dropWhile isWs := by
  induction w with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.cons_append, List.dropWhile_cons, hw c (List.mem_cons_self ..), ↓reduceIte]
    exact ih fun d hd => hw d (List.mem_cons_of_mem _ hd)

theorem trimWs_pad {pre l post : List Char} (hpre : ∀ c ∈ pre, isWs c = true)
    (hpost : ∀ c ∈ post, isWs c = true) : trimWs (pre ++ l ++ post) = trimWs l := by
  unfold trimWs
  rw [List.append_assoc, dropWhile_ws_append hpre, List.dropWhile_append]
  split
  · next he =>
    have hn : l.dropWhile isWs = [] := List.isEmpty_iff.mp he
    have hp : post.dropWhile isWs = [] := by simpa using dropWhile_ws_append (l := []) hpost
    simp [hn, hp]
  · rw [List.reverse_append, dropWhile_ws_append (fun c hc => hpost c (List.mem_reverse.mp hc))]

theorem ws_padL (i : Nat) : ∀ c ∈ padL i, isWs c = true := by
  intro c hc
  simp only [padL, List.mem_replicate] at hc
  rw [hc.2]; rfl

theorem rawPayload_clean (js : String) (h : Html.holdsTerm js "</script" = false) :
    rawPayload "</script" js = js := by
  simp [rawPayload, h]

theorem passive_script : passiveTag "script" = false := by decide

theorem embedding_script : embeddingTags.contains "script" = false := by decide

theorem embedding_style : embeddingTags.contains "style" = false := by decide

theorem passive_embedding (t : String) (h : embeddingTags.contains t = true) :
    passiveTag t = false := by
  simp only [embeddingTags, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- A script node's runs, from what its requests admit. -/
theorem script_good {scripts : Array String} {attrs : Array (String × String)} {js : String}
    {rta : Bool} (h : (nodeRequests rta #[] (.script attrs js)).all (okReq scripts) = true)
    (pre post : List Char) (hpre : ∀ c ∈ pre, isWs c = true) (hpost : ∀ c ∈ post, isWs c = true) :
    ∀ x ∈ Dom.runs (.elem "script" (lowAttrs attrs)
        (addL #[] (pre ++ (rawPayload "</script" js).toList ++ post))), Good scripts x := by
  cases rta with
  | false => simp [nodeRequests, okReq] at h
  | true =>
    simp only [nodeRequests, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Array.empty_append] at h
    have hattr : (attrRequests "script" attrs).all (okReq scripts) = true := by
      split at h <;> split at h <;> simp_all
    have hbad : ((attrs.any fun a => a.1.toLower == "src") || js.contains '\u0000' ||
        Html.holdsTerm js "</script" || Html.holdsTerm js "<!--") = false := by
      cases hb : ((attrs.any fun a => a.1.toLower == "src") || js.contains '\u0000' ||
        Html.holdsTerm js "</script" || Html.holdsTerm js "<!--")
      · rfl
      · simp only [hb, ↓reduceIte] at h
        split at h <;> simp_all [okReq]
    have hterm : Html.holdsTerm js "</script" = false := by
      simp only [Bool.or_eq_false_iff] at hbad
      exact hbad.1.2
    rw [rawPayload_clean js hterm]
    intro x hx
    simp only [runs_elem, elemRuns, embedding_script, Bool.false_eq_true, ↓reduceIte,
      attrRuns_nil "script" attrs hattr, List.nil_append,
      runsList_addL, runsList_nil, List.append_nil] at hx
    split at hx
    · next hd =>
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [Bool.and_eq_true, Bool.not_eq_true', dataBlock_lowAttrs] at hd
      simp only [hbad, Bool.false_eq_true, ↓reduceIte, hd.2] at h
      have hs := (Array.all_eq_true'.mp h) _ (Array.mem_push_self ..)
      simp only [okReq, Array.any_eq_true'] at hs
      obtain ⟨s, hs, hse⟩ := hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hse
      refine ⟨s, hs, ?_⟩
      have hc := charsList_addL #[] (pre ++ js.toList ++ post)
      simp only [charsList_nil, String.toList_empty, List.nil_append] at hc
      rw [hc, trimWs_pad hpre hpost, hse.2]
    · simp at hx

theorem style_runs (cs : List Char) : Dom.runs (.elem "style" #[] (addL #[] cs)) = [] := by
  simp only [runs_elem, elemRuns, embedding_style, Bool.false_eq_true, ↓reduceIte]
  simp [attrRuns, runsList_addL, runsList_nil]

mutual

theorem fB_runs (scripts : Array String) (K : Array Dom) :
    (n : Html.Node) → (i : Nat) → (rta : Bool) →
    (nodeRequests rta #[] n).all (okReq scripts) = true →
    ∀ x ∈ Dom.runsList (fB K n i).toList, x ∈ Dom.runsList K.toList ∨ Good scripts x
  | .text t, i, _, _ => by
    intro x hx
    simp only [fB, runsList_addL] at hx
    exact Or.inl hx
  | .style css, i, _, _ => by
    intro x hx
    simp only [fB, runsList_addL, runsList_push, style_runs, List.append_nil] at hx
    exact Or.inl hx
  | .script attrs js, i, rta, h => by
    intro x hx
    simp only [fB, runsList_addL, runsList_push, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · right
      have := script_good h ['\n'] ('\n' :: padL i) (by decide)
        (by intro c hc; rcases List.mem_cons.mp hc with rfl | hc; rfl; exact ws_padL i c hc)
      exact this x (by simpa [List.append_assoc] using hx)
  | .elem tag attrs kids, i, rta, h => by
    simp only [nodeRequests, Array.empty_append] at h
    rw [listRequests_acc] at h
    have hpass : passiveTag tag.toLower = true := by
      cases hp : passiveTag tag.toLower
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
        simp [okReq] at h
      · rfl
    simp only [hpass, ↓reduceIte, Array.all_append, Bool.and_eq_true] at h
    obtain ⟨ha, hk⟩ := h
    rw [toLower_lower] at ha hpass
    have hns : (lower tag == "script") = false := by
      cases he : lower tag == "script"
      · rfl
      · rw [beq_iff_eq.mp he, passive_script] at hpass; exact absurd hpass (by decide)
    have hne : embeddingTags.contains (lower tag) = false := by
      cases he : embeddingTags.contains (lower tag)
      · rfl
      · rw [passive_embedding _ he] at hpass; exact absurd hpass (by decide)
    intro x hx
    simp only [fB, runsList_addL, runsList_push, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · right
      simp only [runs_elem, elemRuns, hne, attrRuns_nil _ attrs ha, hns, Bool.false_and,
        Bool.false_eq_true,
        ↓reduceIte, List.append_nil, List.nil_append] at hx
      split at hx
      · simp [runsList_nil] at hx
      · split at hx
        · rcases fIL_runs scripts #[] kids.toList _ hk x hx with hx | hx
          · simp [runsList_nil] at hx
          · exact hx
        · rw [runsList_addL] at hx
          rcases fBL_runs scripts _ kids.toList (i + 1) _ hk x hx with hx | hx
          · simp [runsList_addL, runsList_nil] at hx
          · exact hx

theorem fI_runs (scripts : Array String) (K : Array Dom) :
    (n : Html.Node) → (rta : Bool) →
    (nodeRequests rta #[] n).all (okReq scripts) = true →
    ∀ x ∈ Dom.runsList (fI K n).toList, x ∈ Dom.runsList K.toList ∨ Good scripts x
  | .text t, _, _ => by
    intro x hx
    simp only [fI, runsList_addL] at hx
    exact Or.inl hx
  | .style css, _, _ => by
    intro x hx
    simp only [fI, runsList_push, style_runs, List.append_nil] at hx
    exact Or.inl hx
  | .script attrs js, rta, h => by
    intro x hx
    simp only [fI, runsList_push, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · right
      have := script_good h [] [] (by simp) (by simp)
      exact this x (by simpa using hx)
  | .elem tag attrs kids, rta, h => by
    simp only [nodeRequests, Array.empty_append] at h
    rw [listRequests_acc] at h
    have hpass : passiveTag tag.toLower = true := by
      cases hp : passiveTag tag.toLower
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
        simp [okReq] at h
      · rfl
    simp only [hpass, ↓reduceIte, Array.all_append, Bool.and_eq_true] at h
    obtain ⟨ha, hk⟩ := h
    rw [toLower_lower] at ha hpass
    have hns : (lower tag == "script") = false := by
      cases he : lower tag == "script"
      · rfl
      · rw [beq_iff_eq.mp he, passive_script] at hpass; exact absurd hpass (by decide)
    have hne : embeddingTags.contains (lower tag) = false := by
      cases he : embeddingTags.contains (lower tag)
      · rfl
      · rw [passive_embedding _ he] at hpass; exact absurd hpass (by decide)
    intro x hx
    simp only [fI, runsList_push, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · right
      simp only [runs_elem, elemRuns, hne, attrRuns_nil _ attrs ha, hns, Bool.false_and,
        Bool.false_eq_true,
        ↓reduceIte, List.append_nil, List.nil_append] at hx
      split at hx
      · simp [runsList_nil] at hx
      · rcases fIL_runs scripts #[] kids.toList _ hk x hx with hx | hx
        · simp [runsList_nil] at hx
        · exact hx

theorem fBL_runs (scripts : Array String) (K : Array Dom) :
    (l : List Html.Node) → (i : Nat) → (rta : Bool) →
    (listRequests rta #[] l).all (okReq scripts) = true →
    ∀ x ∈ Dom.runsList (fBL K l i).toList, x ∈ Dom.runsList K.toList ∨ Good scripts x
  | [], _, _, _ => fun x hx => Or.inl (by simpa [fBL] using hx)
  | n :: rest, i, rta, h => by
    simp only [listRequests] at h
    rw [listRequests_acc, Array.all_append, Bool.and_eq_true] at h
    intro x hx
    simp only [fBL] at hx
    rcases fBL_runs scripts (fB K n i) rest i rta h.2 x hx with hx | hx
    · exact fB_runs scripts K n i rta h.1 x hx
    · exact Or.inr hx

theorem fIL_runs (scripts : Array String) (K : Array Dom) :
    (l : List Html.Node) → (rta : Bool) →
    (listRequests rta #[] l).all (okReq scripts) = true →
    ∀ x ∈ Dom.runsList (fIL K l).toList, x ∈ Dom.runsList K.toList ∨ Good scripts x
  | [], _, _ => fun x hx => Or.inl (by simpa [fIL] using hx)
  | n :: rest, rta, h => by
    simp only [listRequests] at h
    rw [listRequests_acc, Array.all_append, Bool.and_eq_true] at h
    intro x hx
    simp only [fIL] at hx
    rcases fIL_runs scripts (fI K n) rest rta h.2 x hx with hx | hx
    · exact fI_runs scripts K n rta h.1 x hx
    · exact Or.inr hx

end

theorem fKids_runs (scripts : Array String) (tag : String) (l : Array Html.Node)
    (h : (listRequests true #[] l.toList).all (okReq scripts) = true) :
    ∀ x ∈ Dom.runsList (fKids tag l 1).toList, Good scripts x := by
  intro x hx
  unfold fKids at hx
  split at hx
  · rcases fIL_runs scripts #[] l.toList true h x hx with hx | hx
    · simp [runsList_nil] at hx
    · exact hx
  · rw [runsList_addL] at hx
    rcases fBL_runs scripts _ l.toList 2 true h x hx with hx | hx
    · simp [runsList_addL, runsList_nil] at hx
    · exact hx

/-- What the parser builds from a closed page whose tree reads as a stack runs only admitted
scripts, white space at their ends aside: no handler, script link or embedding. -/
public theorem ClosedPage.runs_admitted {scripts : Array String} (page : ClosedPage scripts)
    (h : Html.DocOk page.lang page.head page.body = true) :
    ∃ d, HtmlRead.parse page.render = some d ∧
      ∀ x ∈ d.runs, ∃ js ∈ scripts, x = .script (trimWs js.toList) := by
  refine ⟨_, Html.parse_render_exact _ _ _ h, ?_⟩
  have hc := page.closed
  simp only [requests] at hc
  rw [listRequests_acc, Array.all_eq_true'] at hc
  have hok : ∀ q ∈ listRequests true #[] page.head.toList ++ listRequests true #[] page.body.toList,
      okReq scripts q = true := fun q hq => okReq_of_resolves (hc q hq)
  have hh : (listRequests true #[] page.head.toList).all (okReq scripts) = true :=
    Array.all_eq_true'.mpr fun q hq => hok q (Array.mem_append_left _ hq)
  have hb : (listRequests true #[] page.body.toList).all (okReq scripts) = true :=
    Array.all_eq_true'.mpr fun q hq => hok q (Array.mem_append_right _ hq)
  have hhead := fKids_runs scripts "head" page.head hh
  have hbody := fKids_runs scripts "body" page.body hb
  intro x hx
  simp [fDoc, runs_elem, runs_text, elemRuns, runsList_cons, runsList_nil, attrRuns, runsList_addL,
    embeddingTags, Html.scriptLink] at hx
  rcases hx with hx | hx
  · exact hhead x hx
  · exact hbody x hx

end LeanTex.Core.HtmlResource
