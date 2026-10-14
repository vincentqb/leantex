module

public import LeanTex.Core.CodeDoc
public import LeanTex.Core.MdDesugarContract
import all LeanTex.Core.CodeDoc

/-! # What a code file lowers into

The declared vocabulary of the code-file reader, which every raw it emits stays inside. -/

namespace LeanTex.Core.Code

open LeanTex.Core LeanTex.Core.Parse

/-- Markdown's vocabulary, the preamble declarations a code file's title and directive take, and
the document around its body. -/
@[expose] public def vocabulary : Md.Vocab :=
  { Md.vocabulary with
    ctrls := Md.vocabulary.ctrls ++ ["title", "output", "theme"]
    envs := Md.vocabulary.envs ++ ["document"] }

private theorem admitsList_append (v : Md.Vocab) (a b : List Raw) :
    v.admitsList (a ++ b) = (v.admitsList a && v.admitsList b) := by
  induction a with
  | nil => simp [Md.Vocab.admitsList]
  | cons r rest ih => simp [Md.Vocab.admitsList, ih, Bool.and_assoc]

private theorem admitsList_iff (v : Md.Vocab) (l : List Raw) :
    v.admitsList l = true ↔ ∀ r ∈ l, v.admits r = true := by
  induction l with
  | nil => simp [Md.Vocab.admitsList]
  | cons r rest ih => simp [Md.Vocab.admitsList, ih]

mutual

private theorem mono_one : (r : Raw) → Md.vocabulary.admits r = true →
    vocabulary.admits r = true
  | .word _ _, _ => rfl
  | .space, _ => rfl
  | .par _, _ => rfl
  | .ctrl n _, h => by
    simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem] at h ⊢
    simp only [vocabulary, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  | .sym c _, h => by simpa [Md.Vocab.admits, vocabulary] using h
  | .group body _, h => by
    simp only [Md.Vocab.admits] at h ⊢
    exact mono_list body.toList h
  | .math _ _ _, h => by simp [Md.Vocab.admits] at h
  | .env n body _, h => by
    simp only [Md.Vocab.admits, Bool.and_eq_true, List.contains_iff_mem] at h ⊢
    exact ⟨by simp [vocabulary, h.1], mono_list body.toList h.2⟩
  | .verb e _ _, h => by simpa [Md.Vocab.admits, vocabulary] using h

private theorem mono_list : (l : List Raw) → Md.vocabulary.admitsList l = true →
    vocabulary.admitsList l = true
  | [], _ => rfl
  | r :: rest, h => by
    simp only [Md.Vocab.admitsList, Bool.and_eq_true] at h ⊢
    exact ⟨mono_one r h.1, mono_list rest h.2⟩

end

mutual

private theorem mapPos_one (f : Pos → Pos) : (r : Raw) →
    vocabulary.admits (mapPos f r) = vocabulary.admits r
  | .word _ _ => rfl
  | .space => rfl
  | .par _ => rfl
  | .ctrl _ _ => rfl
  | .sym _ _ => rfl
  | .group body _ => by
    simp only [mapPos, Md.Vocab.admits]
    rw [mapPos_list f #[] body.toList]
    simp [Md.Vocab.admitsList]
  | .math _ _ _ => rfl
  | .env n body _ => by
    simp only [mapPos, Md.Vocab.admits]
    rw [mapPos_list f #[] body.toList]
    simp [Md.Vocab.admitsList]
  | .verb _ _ _ => rfl

private theorem mapPos_list (f : Pos → Pos) (acc : Array Raw) : (l : List Raw) →
    vocabulary.admitsList (mapPosList f acc l).toList =
      (vocabulary.admitsList acc.toList && vocabulary.admitsList l)
  | [] => by simp [mapPosList, Md.Vocab.admitsList]
  | r :: rest => by
    simp only [mapPosList]
    rw [mapPos_list f (acc.push (mapPos f r)) rest]
    simp [admitsList_append, Md.Vocab.admitsList, mapPos_one f r, Bool.and_assoc]

end

/-- Every raw of a sequence is admitted. -/
private def Adm (rs : Array Raw) : Prop := ∀ r ∈ rs, vocabulary.admits r = true

private theorem adm_mapPos (f : Pos → Pos) (rs : Array Raw) (h : ∀ r ∈ rs, Md.vocabulary.admits r) :
    Adm (mapPosList f #[] rs.toList) := by
  intro r hr
  have hl := mapPos_list f #[] rs.toList
  have hall : vocabulary.admitsList rs.toList = true :=
    (admitsList_iff _ _).mpr fun x hx => mono_one x (h x (by simpa using hx))
  rw [hall] at hl
  simp only [Md.Vocab.admitsList, Bool.and_self] at hl
  exact (admitsList_iff _ _).mp hl r (by simpa using hr)

private theorem headingBody_mem (r : Raw) (rest : List Raw) (body : Array Raw)
    (h : headingBody? r rest = some body) : ∃ p, Raw.group body p ∈ rest := by
  unfold headingBody? at h
  split at h
  · rename_i star p0 b p1 tail
    have hb : b = body := by
      split at h <;> (try split at h) <;> simp_all
    exact ⟨p1, by simp [hb]⟩
  · simp at h

private theorem openingHeading_adm (l : List Raw) (hl : ∀ r ∈ l, vocabulary.admits r = true)
    (body : Array Raw) (h : openingHeading? l = some body) : Adm body := by
  cases l with
  | nil => simp [openingHeading?] at h
  | cons r rest =>
    obtain ⟨p, hp⟩ := headingBody_mem r rest body h
    have hg := hl _ (List.mem_cons_of_mem _ hp)
    simp only [Md.Vocab.admits] at hg
    intro x hx
    exact (admitsList_iff _ _).mp hg x (by simpa using hx)

private theorem adm_push {a : Array Raw} {r : Raw} (ha : Adm a) (hr : vocabulary.admits r = true) :
    Adm (a.push r) := by
  intro x hx
  rcases Array.mem_push.mp hx with hx | rfl
  · exact ha x hx
  · exact hr

private theorem adm_append {a b : Array Raw} (ha : Adm a) (hb : Adm b) : Adm (a ++ b) := by
  intro x hx
  rcases Array.mem_append.mp hx with hx | hx
  · exact ha x hx
  · exact hb x hx

private theorem adm_group (body : Array Raw) (p : Pos) (h : Adm body) :
    vocabulary.admits (.group body p) = true := by
  simp only [Md.Vocab.admits]
  exact (admitsList_iff _ _).mpr fun r hr => h r (by simpa using hr)

private theorem title_ctrl_adm (p : Pos) :
    vocabulary.admits (.ctrl (Parse.headingControl .title) p) = true := by
  simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem]
  exact Or.inr (List.mem_map.mpr ⟨.title, by simp, rfl⟩)

private theorem retitle_adm : (l : List Raw) → (∀ r ∈ l, vocabulary.admits r = true) →
    ∀ r ∈ retitle l, vocabulary.admits r = true
  | [], _ => by simp [retitle]
  | r :: rest, hl => by
    have hrest : ∀ x ∈ rest, vocabulary.admits x = true :=
      fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [retitle]
    split
    · next p _ _ =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact title_ctrl_adm p
      · exact hrest x hx
    · exact hl

private theorem proseRaws_adm (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (seg : Seg) (opens : Bool) : Adm (proseRaws lang file starts seg opens).1 := by
  have hraws : ∀ (pr : Prose),
      Adm (mapPosList pr.place #[] (Md.desugar file pr.text .docstring).1.toList) := by
    intro pr
    apply adm_mapPos
    exact Md.desugar_vocabulary_mem _ _ .docstring
  let pr := proseIn lang seg.text (lineCol starts seg.start).1 ((lineCol starts seg.start).2 - 1)
  have h := hraws pr
  cases opens with
  | true =>
    have hl : ∀ x ∈ (mapPosList pr.place #[] (Md.desugar file pr.text .docstring).1.toList).toList,
        vocabulary.admits x = true := fun x hx => h x (by simpa using hx)
    intro r hr
    exact retitle_adm _ hl r (by simpa [proseRaws] using hr)
  | false => exact h

private theorem pieceRaws_adm (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (opens : Bool) (piece : Piece) : Adm (pieceRaws lang file starts opens piece) := by
  cases piece with
  | code start code =>
    intro r hr
    simp only [pieceRaws, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [listingRaw, Md.Vocab.admits, vocabulary, Md.vocabulary]
  | prose seg => exact proseRaws_adm lang file starts seg opens

/-- What the fold over a file's pieces keeps: its body and its title inside the vocabulary. -/
private def Inv (acc : Acc) : Prop := Adm acc.body ∧ ∀ t, acc.title = some t → Adm t

private theorem pieceStep_inv (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (acc : Acc) (piece : Piece) (h : Inv acc) : Inv (pieceStep lang file starts acc piece) := by
  have hp := pieceRaws_adm lang file starts (acc.opens piece) piece
  obtain ⟨hbody, htitle⟩ := pieceStep_exact lang file starts acc piece
  refine ⟨hbody ▸ adm_append h.1 hp, ?_⟩
  intro t ht
  rw [htitle] at ht
  split at ht
  · exact openingHeading_adm _ (fun r hr => hp r (by simpa using hr)) t ht
  · exact h.2 t ht

private theorem foldl_inv (lang : Ir.CodeLang) (file : String) (starts : Array Nat) :
    (l : List Piece) → (acc : Acc) → Inv acc → Inv (l.foldl (pieceStep lang file starts) acc)
  | [], _, h => h
  | p :: rest, acc, h => foldl_inv lang file starts rest _ (pieceStep_inv lang file starts acc p h)

private theorem directive_adm (value : String) (p : Pos) : Adm (directiveRaws value p) := by
  have one : ∀ name v, name = "theme" ∨ name = "output" →
      Adm (#[Raw.ctrl name p, .group #[.word v p] p]) := by
    intro name v hn
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rcases hn with rfl | rfl <;> simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
    · exact adm_group _ _ (by intro x hx; simp at hx; subst hx; rfl)
  have flat : ∀ (name : String) (vs : List String), (name = "theme" ∨ name = "output") →
      Adm (vs.map fun v => #[Raw.ctrl name p, .group #[.word v p] p]).toArray.flatten := by
    intro name vs hn r hr
    simp only [Array.mem_flatten, List.mem_toArray, List.mem_map] at hr
    obtain ⟨xs, ⟨v, _, rfl⟩, hx⟩ := hr
    exact one name v hn r hx
  unfold directiveRaws
  refine adm_append (flat "theme" _ (Or.inl rfl)) ?_
  split
  · intro r hr; simp at hr
  · split
    · exact one "output" _ (Or.inr rfl)
    · exact flat "output" _ (Or.inr rfl)

private theorem title_adm (acc : Acc) (h : Inv acc) (fallback : Array Raw)
    (hf : Adm fallback) : Adm (acc.title.getD fallback) := by
  cases ht : acc.title with
  | some t => simpa [ht] using h.2 t ht
  | none => simpa [ht] using hf

private theorem textRaws_adm (s : String) (p : Pos) : Adm (Md.textRaws s p) := by
  intro r hr
  rcases Md.textRaws_covers _ _ r hr with rfl | ⟨w, q, rfl⟩ <;> rfl

private theorem titleHeading_adm (t : Array Raw) (p : Pos) (h : Adm t) :
    Adm (Parse.headingRaws .title t p) := by
  rw [Parse.headingRaws_contract]
  intro r hr
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem]
    exact Or.inr (List.mem_map.mpr ⟨.title, by simp, rfl⟩)
  · rfl
  · exact adm_group _ _ h

/-- Everything a code file reads into stays inside the reader's declared vocabulary. -/
public theorem read_vocabulary_mem (lang : Ir.CodeLang) (file text : String) :
    ∀ r ∈ (read lang file text).1, vocabulary.admits r = true := by
  have hacc : Inv (readPieces lang file text) := foldl_inv lang file _ _ {} ⟨by simp [Adm], by simp⟩
  unfold read
  dsimp only
  generalize readPieces lang file text = acc at hacc ⊢
  have htitle := title_adm acc hacc _ (textRaws_adm (baseName file) {})
  refine adm_push (adm_append ?_ ?_) ?_
  · intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
    · exact adm_group _ _ htitle
  · split
    · exact directive_adm _ _
    · intro r hr; simp at hr
  · simp only [Md.Vocab.admits, Bool.and_eq_true, List.contains_iff_mem]
    refine ⟨by simp [vocabulary, Md.vocabulary], (admitsList_iff _ _).mpr fun r hr => ?_⟩
    have hbody : Adm (if acc.title.isSome then acc.body
        else Parse.headingRaws .title (acc.title.getD (Md.textRaws (baseName file) {})) {} ++
          acc.body) := by
      split
      · exact hacc.1
      · exact adm_append (titleHeading_adm _ _ htitle) hacc.1
    exact hbody r (by simpa using hr)

end LeanTex.Core.Code
