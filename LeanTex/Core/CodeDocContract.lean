module

public import LeanTex.Core.CodeDoc
public import LeanTex.Core.MdDesugarContract
import all LeanTex.Core.CodeDoc
import all LeanTex.Core.LeanStatement

/-! # What a code file lowers into

The declared vocabulary of the code-file reader, which every raw it emits stays inside. -/

namespace LeanTex.Core.Code

open LeanTex.Core LeanTex.Core.Parse

/-- Markdown's vocabulary, the preamble declarations a code file's title and directive take, the
document around its body, and the formulas a Lean statement sets as, with the zero glue a line
breaks at between them. -/
@[expose] public def vocabulary : Md.Vocab :=
  { Md.vocabulary with
    ctrls := Md.vocabulary.ctrls ++ ["title", "output", "theme", "hspace", "bibliographystyle",
      "bibliography"] ++ textSizes
    envs := Md.vocabulary.envs ++ ["document", "flushleft", Parse.linesEnv]
    formulas := true
    mathCtrls := LeanNotation.MathCtrl.all.map (·.name) }

/-- The vocabulary a page of a file of `lang` lowers into, a formula only on a Lean file's. -/
@[expose] public def vocabularyFor (lang : Ir.CodeLang) : Md.Vocab :=
  { vocabulary with formulas := lang == .lean }

private abbrev voc (b : Bool) : Md.Vocab := { vocabulary with formulas := b }

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

private theorem mathAdmitsList_append (v : Md.Vocab) (a b : List Raw) :
    v.mathAdmitsList (a ++ b) = (v.mathAdmitsList a && v.mathAdmitsList b) := by
  induction a with
  | nil => simp [Md.Vocab.mathAdmitsList]
  | cons r rest ih => simp [Md.Vocab.mathAdmitsList, ih, Bool.and_assoc]

mutual

private theorem mathMono_one (b : Bool) : (r : Raw) →
    { Md.vocabulary with formulas := b }.mathAdmits r = true → (voc b).mathAdmits r = true
  | .word _ _, _ => rfl
  | .space, _ => rfl
  | .ctrl n _, h => by
    simp only [Md.Vocab.mathAdmits, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | h
    · simp [Md.vocabulary] at h
    · exact Or.inr ⟨by simp [vocabulary, Md.vocabulary], h.2⟩
  | .sym c _, h => by simpa [Md.Vocab.mathAdmits, vocabulary] using h
  | .group body _, h => by
    simp only [Md.Vocab.mathAdmits] at h ⊢
    exact mathMono_list b body.toList h
  | .par _, h | .math .., h | .env .., h | .verb .., h => by simp [Md.Vocab.mathAdmits] at h

private theorem mathMono_list (b : Bool) : (l : List Raw) →
    { Md.vocabulary with formulas := b }.mathAdmitsList l = true →
      (voc b).mathAdmitsList l = true
  | [], _ => rfl
  | r :: rest, h => by
    simp only [Md.Vocab.mathAdmitsList, Bool.and_eq_true] at h ⊢
    exact ⟨mathMono_one b r h.1, mathMono_list b rest h.2⟩

end

mutual

private theorem mono_one (b : Bool) : (r : Raw) →
    { Md.vocabulary with formulas := b }.admits r = true → (voc b).admits r = true
  | .word _ _, _ => rfl
  | .space, _ => rfl
  | .par _, _ => rfl
  | .ctrl n _, h => by
    simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem] at h ⊢
    simp only [vocabulary, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr h
  | .sym c _, h => by simpa [Md.Vocab.admits, vocabulary] using h
  | .group body _, h => by
    simp only [Md.Vocab.admits] at h ⊢
    exact mono_list b body.toList h
  | .math _ body _, h => by
    simp only [Md.Vocab.admits, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, mathMono_list b body.toList h.2⟩
  | .env n body _, h => by
    simp only [Md.Vocab.admits, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h ⊢
    refine ⟨?_, mono_list b body.toList h.2⟩
    simp only [vocabulary, List.mem_append]
    rcases h.1 with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  | .verb e _ _, h => by simpa [Md.Vocab.admits, vocabulary] using h

private theorem mono_list (b : Bool) : (l : List Raw) →
    { Md.vocabulary with formulas := b }.admitsList l = true → (voc b).admitsList l = true
  | [], _ => rfl
  | r :: rest, h => by
    simp only [Md.Vocab.admitsList, Bool.and_eq_true] at h ⊢
    exact ⟨mono_one b r h.1, mono_list b rest h.2⟩

end

mutual

private theorem mathMap_one (b : Bool) (f : Pos → Pos) : (r : Raw) →
    (voc b).mathAdmits (mapPos f r) = (voc b).mathAdmits r
  | .word _ _ => rfl
  | .space => rfl
  | .par _ => rfl
  | .ctrl _ _ => rfl
  | .sym _ _ => rfl
  | .group body _ => by
    simp only [mapPos, Md.Vocab.mathAdmits]
    rw [mathMap_list b f #[] body.toList]
    simp [Md.Vocab.mathAdmitsList]
  | .math _ _ _ => rfl
  | .env _ _ _ => rfl
  | .verb _ _ _ => rfl

private theorem mathMap_list (b : Bool) (f : Pos → Pos) (acc : Array Raw) : (l : List Raw) →
    (voc b).mathAdmitsList (mapPosList f acc l).toList =
      ((voc b).mathAdmitsList acc.toList && (voc b).mathAdmitsList l)
  | [] => by simp [mapPosList, Md.Vocab.mathAdmitsList]
  | r :: rest => by
    simp only [mapPosList]
    rw [mathMap_list b f (acc.push (mapPos f r)) rest]
    simp [mathAdmitsList_append, Md.Vocab.mathAdmitsList, mathMap_one b f r, Bool.and_assoc]

end

mutual

private theorem mapPos_one (b : Bool) (f : Pos → Pos) : (r : Raw) →
    (voc b).admits (mapPos f r) = (voc b).admits r
  | .word _ _ => rfl
  | .space => rfl
  | .par _ => rfl
  | .ctrl _ _ => rfl
  | .sym _ _ => rfl
  | .group body _ => by
    simp only [mapPos, Md.Vocab.admits]
    rw [mapPos_list b f #[] body.toList]
    simp [Md.Vocab.admitsList]
  | .math _ body _ => by
    simp only [mapPos, Md.Vocab.admits]
    rw [mathMap_list b f #[] body.toList]
    simp [Md.Vocab.mathAdmitsList]
  | .env n body _ => by
    simp only [mapPos, Md.Vocab.admits]
    rw [mapPos_list b f #[] body.toList]
    simp [Md.Vocab.admitsList]
  | .verb _ _ _ => rfl

private theorem mapPos_list (b : Bool) (f : Pos → Pos) (acc : Array Raw) : (l : List Raw) →
    (voc b).admitsList (mapPosList f acc l).toList =
      ((voc b).admitsList acc.toList && (voc b).admitsList l)
  | [] => by simp [mapPosList, Md.Vocab.admitsList]
  | r :: rest => by
    simp only [mapPosList]
    rw [mapPos_list b f (acc.push (mapPos f r)) rest]
    simp [admitsList_append, Md.Vocab.admitsList, mapPos_one b f r, Bool.and_assoc]

end

/-- Every raw of a sequence is admitted. -/
private def Adm (b : Bool) (rs : Array Raw) : Prop := ∀ r ∈ rs, (voc b).admits r = true

variable {b : Bool}

private theorem adm_mapPos (f : Pos → Pos) (rs : Array Raw)
    (h : ∀ r ∈ rs, { Md.vocabulary with formulas := b }.admits r) :
    Adm b (mapPosList f #[] rs.toList) := by
  intro r hr
  have hl := mapPos_list b f #[] rs.toList
  have hall : (voc b).admitsList rs.toList = true :=
    (admitsList_iff _ _).mpr fun x hx => mono_one b x (h x (by simpa using hx))
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

private theorem openingHeading_adm (l : List Raw) (hl : ∀ r ∈ l, (voc b).admits r = true)
    (body : Array Raw) (h : openingHeading? l = some body) : Adm b body := by
  cases l with
  | nil => simp [openingHeading?] at h
  | cons r rest =>
    obtain ⟨p, hp⟩ := headingBody_mem r rest body h
    have hg := hl _ (List.mem_cons_of_mem _ hp)
    simp only [Md.Vocab.admits] at hg
    intro x hx
    exact (admitsList_iff _ _).mp hg x (by simpa using hx)

private theorem adm_push {a : Array Raw} {r : Raw} (ha : Adm b a) (hr : (voc b).admits r = true) :
    Adm b (a.push r) := by
  intro x hx
  rcases Array.mem_push.mp hx with hx | rfl
  · exact ha x hx
  · exact hr

private theorem adm_append {a c : Array Raw} (ha : Adm b a) (hc : Adm b c) : Adm b (a ++ c) := by
  intro x hx
  rcases Array.mem_append.mp hx with hx | hx
  · exact ha x hx
  · exact hc x hx

private theorem adm_group (body : Array Raw) (p : Pos) (h : Adm b body) :
    (voc b).admits (.group body p) = true := by
  simp only [Md.Vocab.admits]
  exact (admitsList_iff _ _).mpr fun r hr => h r (by simpa using hr)

private theorem title_ctrl_adm (p : Pos) :
    (voc b).admits (.ctrl (Parse.headingControl .title) p) = true := by
  simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem]
  exact Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨.title, by simp, rfl⟩)))

private theorem retitle_adm : (l : List Raw) → (∀ r ∈ l, (voc b).admits r = true) →
    ∀ r ∈ retitle l, (voc b).admits r = true
  | [], _ => by simp [retitle]
  | r :: rest, hl => by
    have hrest : ∀ x ∈ rest, (voc b).admits x = true :=
      fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [retitle]
    split
    · next p _ _ =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact title_ctrl_adm p
      · exact hrest x hx
    · exact hl

private theorem desugar_adm (file text : String) (k : Option (Std.HashSet String)) :
    (d : Md.Dialect) → d ≠ .document →
      ∀ r ∈ (Md.desugar file text d .document false k).1,
        { Md.vocabulary with formulas := d.formulas }.admits r = true
  | .document, h => absurd rfl h
  | .docstring, _ => Md.desugar_vocabulary_mem file text .docstring .document false k
  | .lean, _ => Md.desugar_vocabulary_mem file text .lean .document false k

private theorem proseRaws_adm (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (known : Option (Std.HashSet String)) (seg : Seg) (opens : Bool) :
    Adm (lang == .lean) (proseRaws lang file starts known seg opens).1 := by
  let k := known
  let dl : Md.Dialect := if lang == .lean then .lean else .docstring
  have hdl : dl ≠ .document := by
    show (if lang == .lean then Md.Dialect.lean else .docstring) ≠ .document
    split <;> decide
  have hf : dl.formulas = (lang == .lean) := by
    show (if lang == .lean then Md.Dialect.lean else .docstring).formulas = (lang == .lean)
    split <;> simp_all [Md.Dialect.formulas]
  have hraws : ∀ (pr : Prose),
      Adm (lang == .lean)
        (mapPosList pr.place #[] (Md.desugar file pr.text dl .document false k).1.toList) := by
    intro pr
    apply adm_mapPos
    rw [← hf]
    exact desugar_adm file pr.text k dl hdl
  let pr := (lowered lang file seg.text known (segProse lang starts seg)).1
  have h := hraws pr
  cases opens with
  | true =>
    have hl : ∀ x ∈ (mapPosList pr.place #[]
        (Md.desugar file pr.text dl .document false k).1.toList).toList,
        (voc (lang == .lean)).admits x = true := fun x hx => h x (by simpa using hx)
    intro r hr
    exact retitle_adm _ hl r (by simpa [proseRaws, k, dl] using hr)
  | false => simpa [proseRaws, k, dl] using h

private theorem caret_sym : '^' ∈ vocabulary.mathSyms := by
  simp [vocabulary, Md.vocabulary, Md.docMathSyms]

private theorem under_sym : '_' ∈ vocabulary.mathSyms := by
  simp [vocabulary, Md.vocabulary, Md.docMathSyms]

mutual

private theorem pushRaws_adm (pos : Pos) : (m : LeanNotation.Math) → (acc : Array Raw) →
    (voc true).mathAdmitsList acc.toList = true →
    (voc true).mathAdmitsList (LeanStatement.Math.pushRaws pos acc m).toList = true
  | .word _, acc, h => by
    simp [LeanStatement.Math.pushRaws, mathAdmitsList_append, h, Md.Vocab.mathAdmitsList,
      Md.Vocab.mathAdmits]
  | .ctrl c, acc, h => by
    simp only [LeanStatement.Math.pushRaws, Array.toList_push, mathAdmitsList_append, h,
      Md.Vocab.mathAdmitsList, Md.Vocab.mathAdmits, Bool.true_and, Bool.and_true, Bool.or_eq_true]
    exact Or.inl (List.contains_iff_mem.mpr
      (List.mem_map.mpr ⟨c, LeanNotation.MathCtrl.mem_all c, rfl⟩))
  | .arg body, acc, h => by
    have hb := listRaws_adm pos body #[] (by simp [Md.Vocab.mathAdmitsList])
    simp [LeanStatement.Math.pushRaws, mathAdmitsList_append, h, Md.Vocab.mathAdmitsList,
      Md.Vocab.mathAdmits, hb]
  | .sup body, acc, h => by
    have hb := listRaws_adm pos body #[] (by simp [Md.Vocab.mathAdmitsList])
    simp [LeanStatement.Math.pushRaws, mathAdmitsList_append, h, Md.Vocab.mathAdmitsList,
      Md.Vocab.mathAdmits, hb, caret_sym]
  | .sub body, acc, h => by
    have hb := listRaws_adm pos body #[] (by simp [Md.Vocab.mathAdmitsList])
    simp [LeanStatement.Math.pushRaws, mathAdmitsList_append, h, Md.Vocab.mathAdmitsList,
      Md.Vocab.mathAdmits, hb, under_sym]

private theorem listRaws_adm (pos : Pos) : (l : List LeanNotation.Math) → (acc : Array Raw) →
    (voc true).mathAdmitsList acc.toList = true →
    (voc true).mathAdmitsList (LeanStatement.Math.listRaws pos acc l).toList = true
  | [], _, h => by simpa [LeanStatement.Math.listRaws] using h
  | m :: rest, acc, h => by
    simp only [LeanStatement.Math.listRaws]
    exact listRaws_adm pos rest _ (pushRaws_adm pos m acc h)

end

private theorem textRaws_adm' (s : String) (p : Pos) : Adm b (Md.textRaws s p) := by
  intro r hr
  rcases Md.textRaws_covers _ _ r hr with rfl | ⟨w, q, rfl⟩ <;> rfl

private theorem breakRaws_adm (pos : Pos) : Adm b (breakRaws pos) := by
  intro r hr
  simp only [breakRaws, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp [Md.Vocab.admits, vocabulary]
  · exact adm_group _ _ (by intro x hx; simp at hx; subst hx; rfl)

private theorem headRaws_adm (d : LeanFacts.Decl) (pos : Pos) (link : Option String) :
    Adm b (headRaws d pos link) := by
  have hname : Adm b #[.ctrl "texttt" pos, .group (Md.textRaws d.name pos) pos] := by
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
    · exact adm_group _ _ (textRaws_adm' _ _)
  have hnamed : Adm b (nameRaws d pos link) := by
    unfold nameRaws
    split
    · intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
      · exact adm_group _ _ (by intro x hx; simp at hx; subst hx; rfl)
      · exact adm_group _ _ hname
    · exact hname
  have hlead : Adm b #[.ctrl "textbf" pos, .group #[.word d.kind.label pos] pos,
      .space, .word "(" pos] := by
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
    · simp [Md.Vocab.admits, Md.Vocab.admitsList]
    · rfl
    · rfl
  have hclose : Adm b (if d.kind == .theorem && !d.proved then
      #[.word "," pos, .space, .word "unproved)." pos] else #[.word ")." pos]) := by
    split
    · intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rfl
    · intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rfl
  unfold headRaws
  exact adm_append (adm_append hlead hnamed) hclose

private theorem formulaRaw_adm (pos : Pos) (m : Array LeanNotation.Math) :
    (voc true).admits (formulaRaw pos m) = true := by
  simp only [formulaRaw, Md.Vocab.admits, Bool.and_eq_true]
  exact ⟨by simp, by simpa using listRaws_adm pos m.toList #[] (by simp [Md.Vocab.mathAdmitsList])⟩

/-- A fold whose step keeps its raws inside the vocabulary keeps them there. -/
private theorem foldl_adm {β γ : Type} (f : Array Raw × β → γ → Array Raw × β)
    (hf : ∀ acc x, Adm b acc.1 → Adm b (f acc x).1) :
    ∀ (l : List γ) (acc : Array Raw × β), Adm b acc.1 → Adm b (l.foldl f acc).1
  | [], _, h => h
  | x :: rest, acc, h => foldl_adm f hf rest _ (hf acc x h)

private theorem displayRaws_adm (d : LeanFacts.Decl)
    (formulas : Array (Array LeanNotation.Math × Bool)) (pos : Pos) (link : Option String) :
    Adm true (displayRaws d formulas pos link) := by
  have step : ∀ (st : Array Raw × Bool) (mn : Array LeanNotation.Math × Bool), Adm true st.1 →
      Adm true (displayStep pos st mn).1 := by
    intro st mn h
    refine adm_push (adm_append h ?_) (formulaRaw_adm pos _)
    split
    · intro r hr; simp at hr; subst hr; rfl
    · exact breakRaws_adm pos
  have hbody := foldl_adm (displayStep pos) step formulas.toList (headRaws d pos link, true)
    (headRaws_adm d pos link)
  rw [Array.foldl_toList] at hbody
  intro r hr
  simp only [displayRaws, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  simp only [Md.Vocab.admits, Bool.and_eq_true]
  exact ⟨by simp [vocabulary, Md.vocabulary], (admitsList_iff _ _).mpr fun x hx =>
    hbody x (by simpa using hx)⟩

private theorem leafRaws_adm (pos : Pos) (l : LeanProse.Leaf) : Adm true (leafRaws pos l) := by
  cases l with
  | nil => intro r hr; simp [leafRaws] at hr
  | cons m rest =>
    simp only [leafRaws]
    have h : ∀ (l : List (Array LeanNotation.Math)) (acc : Array Raw × Bool), Adm true acc.1 →
        Adm true (l.foldl (fun (acc : Array Raw × Bool) q =>
          ((acc.1 ++ (if acc.2 then #[.space] else breakRaws pos)).push
            (formulaRaw pos (LeanStatement.unspaced q).1), (LeanStatement.unspaced q).2)) acc).1 := by
      intro l
      induction l with
      | nil => intro acc h; exact h
      | cons q _ ih =>
        intro acc h
        refine ih _ (adm_push (adm_append h ?_) (formulaRaw_adm pos _))
        split
        · intro r hr; simp at hr; subst hr; rfl
        · exact breakRaws_adm pos
    exact h rest _ (by intro r hr; simp at hr; subst hr; exact formulaRaw_adm pos _)

private theorem wordRaws_adm (pos : Pos) (s : String) : Adm true (wordRaws pos s) := by
  have h : ∀ (l : List String) (acc : Array Raw), Adm true acc →
      Adm true (l.foldl (fun acc w =>
        (if acc.isEmpty then acc else acc.push .space).push (.word w pos)) acc) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons w _ ih =>
      intro acc h
      refine ih _ (adm_push ?_ rfl)
      split
      · exact h
      · exact adm_push h rfl
  exact h _ #[] (by intro r hr; simp at hr)

private theorem tokRaws_adm (pos : Pos) (opening : Bool) (t : LeanProse.Tok LeanProse.Leaf) :
    Adm true (tokRaws pos opening t).1 := by
  unfold tokRaws
  split
  · split
    · intro r hr; simp at hr; subst hr; exact formulaRaw_adm pos _
    · exact wordRaws_adm pos _
  · exact leafRaws_adm pos _
  · exact leafRaws_adm pos _
  all_goals intro r hr; simp at hr

/-- A lines environment over admitted raws is admitted. -/
private theorem adm_lines (body : Array Raw) (p : Pos) (h : Adm b body) :
    (voc b).admits (.env Parse.linesEnv body p) = true := by
  simp only [Md.Vocab.admits, Bool.and_eq_true]
  exact ⟨by simp [vocabulary, Md.vocabulary],
    (admitsList_iff _ _).mpr fun x hx => h x (by simpa using hx)⟩

/-- A numbered list over admitted raws is admitted. -/
private theorem adm_enumerate (body : Array Raw) (p : Pos) (h : Adm b body) :
    (voc b).admits (.env "enumerate" body p) = true := by
  simp only [Md.Vocab.admits, Bool.and_eq_true]
  exact ⟨by simp [vocabulary, Md.vocabulary],
    (admitsList_iff _ _).mpr fun x hx => h x (by simpa using hx)⟩

private theorem adm_word (w : String) (p : Pos) : Adm b #[.word w p] := by
  intro r hr; simp at hr; subst hr; rfl

private theorem adm_pop {a : Array Raw} (h : Adm b a) : Adm b a.pop := by
  intro r hr
  rw [← Array.mem_toList_iff, Array.toList_pop] at hr
  exact h r (Array.mem_toList_iff.mp (List.dropLast_subset _ hr))

private theorem stopped_adm (pos : Pos) (raws : Array Raw) (h : Adm b raws) :
    Adm b (stopped pos raws) := by
  fun_induction stopped pos raws with
  | case1 raws n inner p hb _ _ ih =>
    have hm := h _ (Array.mem_of_back? hb)
    simp only [Md.Vocab.admits, Bool.and_eq_true] at hm
    have hin : Adm b inner := fun x hx => ((admitsList_iff _ _).mp hm.2) x (by simpa using hx)
    refine adm_push (adm_pop h) ?_
    simp only [Md.Vocab.admits, Bool.and_eq_true]
    exact ⟨hm.1, (admitsList_iff _ _).mpr fun x hx => ih hin x (by simpa using hx)⟩
  | case2 => exact adm_push h rfl
  | case3 => exact adm_push h rfl

/-- A frame whose raws are all admitted. -/
private def FAdm (f : Frame) : Prop := Adm true f.out ∧ Adm true f.cur

private theorem raws_adm (f : Frame) (pos : Pos) (h : FAdm f) : Adm true (f.raws pos) := by
  unfold Frame.raws
  split
  · exact h.1
  · split
    · exact adm_push h.1 (adm_lines _ _ h.2)
    · exact adm_append h.1 h.2

private theorem itemRaws_adm (f : Frame) (pos : Pos) (h : FAdm f) : Adm true (f.itemRaws pos) := by
  unfold Frame.itemRaws
  refine raws_adm _ pos ⟨h.1, ?_⟩
  dsimp only
  split
  · exact h.2
  · exact stopped_adm pos _ h.2

private theorem closeInto_adm (pos : Pos) (inner outer : Frame) (hi : FAdm inner)
    (ho : FAdm outer) : FAdm (closeInto pos inner outer) := by
  unfold closeInto
  split
  · exact ⟨ho.1, adm_push ho.2 (adm_lines _ _ hi.2)⟩
  · exact ⟨adm_append (adm_push ho.1 (by simp [Md.Vocab.admits, vocabulary, Md.vocabulary]))
      (itemRaws_adm inner pos hi), ho.2⟩
  · exact ⟨adm_append (adm_push ho.1 (by simp [Md.Vocab.admits, vocabulary, Md.vocabulary]))
      (itemRaws_adm inner pos hi), ho.2⟩
  · exact ⟨adm_push (raws_adm outer pos ho) (adm_enumerate _ _ hi.1), by intro r hr; simp at hr⟩

private theorem closeTop_adm (pos : Pos) (l : List Frame) (h : ∀ f ∈ l, FAdm f) :
    ∀ f ∈ closeTop pos l, FAdm f := by
  unfold closeTop
  split
  · rename_i inner outer rest
    intro f hf
    simp only [List.mem_cons] at hf h
    rcases hf with rfl | hf
    · exact closeInto_adm pos inner outer (h inner (by simp)) (h outer (by simp))
    · exact h f (by simp [hf])
  all_goals exact h

private theorem empty_adm (k : FrameKind) : FAdm (Frame.empty k) :=
  ⟨by intro r hr; simp [Frame.empty] at hr, by intro r hr; simp [Frame.empty] at hr⟩

private theorem openItem_adm (pos : Pos) (l : List Frame) (h : ∀ f ∈ l, FAdm f) :
    ∀ f ∈ openItem pos l, FAdm f := by
  unfold openItem
  split
  · rename_i f rest
    split
    · intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact empty_adm _
      · exact empty_adm _
      · exact h g (by simp [hg])
    · split
      · split
        · rename_i l more
          intro g hg
          simp only [List.mem_cons] at hg
          rcases hg with rfl | rfl | hg
          · exact empty_adm _
          · exact closeInto_adm pos f l (h f (by simp)) (h l (by simp))
          · exact h g (by simp [hg])
        · exact h
      · exact h
  · exact h

private theorem gap_adm (c : Bool) : Adm b (if c then (#[] : Array Raw) else #[.space]) := by
  split
  · intro r hr; simp at hr
  · intro r hr; simp at hr; subst hr; rfl

private theorem relAttach_adm (pos : Pos) (cur : Array Raw) (t : LeanProse.Tok LeanProse.Leaf)
    (h : Adm true cur) : ∀ c, relAttach? pos cur t = some c → Adm true c := by
  intro c hc
  unfold relAttach? at hc
  split at hc
  · split at hc
    · rename_i g body p _ hb
      simp only [Option.some.injEq] at hc
      subst hc
      have hm := h _ (Array.mem_of_back? hb)
      simp only [Md.Vocab.admits, Bool.and_eq_true] at hm
      refine adm_push (adm_pop h) ?_
      simp only [Md.Vocab.admits, Bool.and_eq_true, Array.toList_append, mathAdmitsList_append]
      exact ⟨hm.1, hm.2, by simpa using listRaws_adm pos _ #[] (by simp [Md.Vocab.mathAdmitsList])⟩
    · cases hc
  all_goals cases hc

private theorem closeRel_adm (pos : Pos) (cur : Array Raw) (h : Adm true cur) :
    Adm true (closeRel pos cur) := by
  unfold closeRel
  split
  · rename_i body p hb
    have hm := h _ (Array.mem_of_back? hb)
    simp only [Md.Vocab.admits, Bool.and_eq_true] at hm
    refine adm_push (adm_pop h) ?_
    simp only [Md.Vocab.admits, Bool.and_eq_true, Array.toList_append, mathAdmitsList_append]
    exact ⟨hm.1, hm.2, by simpa using listRaws_adm pos _ #[] (by simp [Md.Vocab.mathAdmitsList])⟩
  · exact h

private theorem closeRelIf_adm (pos : Pos) (cur : Array Raw) (c : Bool) (h : Adm true cur) :
    Adm true (if c = true then closeRel pos cur else cur) := by
  cases c
  · exact h
  · exact closeRel_adm pos cur h

private theorem gapRel_adm (pos : Pos) (c d : Bool) :
    Adm true (if c = true then (#[] : Array Raw) else if d = true then breakRaws pos else #[.space]) := by
  cases c
  · cases d
    · intro r hr; simp at hr; subst hr; rfl
    · exact breakRaws_adm pos
  · intro r hr; simp at hr

private theorem pushTok_adm (pos : Pos) (acc : SentenceAcc) (t : LeanProse.Tok LeanProse.Leaf)
    (h : ∀ f ∈ acc.1, FAdm f) : ∀ f ∈ (pushTok pos acc t).1, FAdm f := by
  obtain ⟨stack, o, ls⟩ := acc
  cases stack with
  | nil =>
    intro f hf
    simp only [pushTok, List.mem_singleton] at hf
    subst hf
    exact ⟨(empty_adm .top).1, tokRaws_adm pos o t⟩
  | cons top rest =>
    intro f hf
    simp only [pushTok] at hf
    split at hf
    · simp only [List.mem_cons] at hf h
      rcases hf with rfl | hf
      · exact h top (Or.inl rfl)
      · exact h f (Or.inr hf)
    · split at hf
      · rename_i cur hcur
        simp only [List.mem_cons] at hf h
        rcases hf with rfl | hf
        · exact ⟨(h top (Or.inl rfl)).1, relAttach_adm pos _ t (h top (Or.inl rfl)).2 _ hcur⟩
        · exact h f (Or.inr hf)
      · simp only [List.mem_cons] at hf h
        rcases hf with rfl | hf
        · exact ⟨(h top (Or.inl rfl)).1, adm_append (adm_append
            (closeRelIf_adm pos _ _ (h top (Or.inl rfl)).2) (gapRel_adm pos _ _))
            (tokRaws_adm pos o t)⟩
        · exact h f (Or.inr hf)

private theorem sentenceStep_adm (pos : Pos) (acc : SentenceAcc) (t : LeanProse.Tok LeanProse.Leaf)
    (h : ∀ f ∈ acc.1, FAdm f) : ∀ f ∈ (sentenceStep pos acc t).1, FAdm f := by
  unfold sentenceStep
  split
  · intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact empty_adm _
    · exact h f hf
  · exact openItem_adm pos acc.1 h
  · unfold closeBlock
    split
    · split
      · exact closeTop_adm pos _ (closeTop_adm pos _ h)
      · exact closeTop_adm pos _ h
    · exact closeTop_adm pos _ h
  all_goals exact pushTok_adm pos acc _ h

private theorem closeAll_adm (pos : Pos) :
    ∀ (l : List Frame), (∀ f ∈ l, FAdm f) → Adm true (closeAll pos l)
  | inner :: outer :: rest, h => by
    rw [closeAll]
    refine closeAll_adm pos _ ?_
    intro f hf
    simp only [List.mem_cons] at hf h
    rcases hf with rfl | hf
    · exact closeInto_adm pos inner outer (h inner (by simp)) (h outer (by simp))
    · exact h f (by simp [hf])
  | [top], h => by rw [closeAll]; exact raws_adm top pos (h top (by simp))
  | [], _ => by rw [closeAll]; intro r hr; simp at hr
termination_by l => l.length

private theorem sentenceRaws_adm (pos : Pos) (head : Array Raw) (hh : Adm true head)
    (toks : List (LeanProse.Tok LeanProse.Leaf)) : Adm true (sentenceRaws pos head toks) := by
  unfold sentenceRaws
  refine closeAll_adm pos _ ?_
  have hfold : ∀ (l : List (LeanProse.Tok LeanProse.Leaf)) (acc : SentenceAcc),
      (∀ f ∈ acc.1, FAdm f) → ∀ f ∈ (l.foldl (sentenceStep pos) acc).1, FAdm f := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons t _ ih => intro acc h; exact ih _ (sentenceStep_adm pos acc t h)
  refine hfold _ _ ?_
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact ⟨(empty_adm .top).1, hh⟩

private theorem wordsRaws_adm (d : LeanFacts.Decl) (s : LeanProse.Stmt LeanProse.Leaf)
    (pos : Pos) (link : Option String) : Adm true (wordsRaws d s pos link) := by
  have hbody := sentenceRaws_adm pos _ (headRaws_adm d pos link) (LeanProse.render s)
  intro r hr
  simp only [wordsRaws, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  simp only [Md.Vocab.admits, Bool.and_eq_true]
  exact ⟨by simp [vocabulary, Md.vocabulary], (admitsList_iff _ _).mpr fun x hx => hbody x (by simpa using hx)⟩

private theorem glossaryRaws_adm (facts : LeanFacts.Facts) (tb : LeanProse.Table)
    (s : LeanProse.Stmt LeanProse.Leaf) (pos : Pos) : Adm true (glossaryRaws facts tb s pos) := by
  unfold glossaryRaws
  dsimp only
  split
  · intro r hr; simp at hr
  · have hbody := fun toks =>
      sentenceRaws_adm pos #[.word "where" pos] (by intro r hr; simp at hr; subst hr; rfl) toks
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [Md.Vocab.admits, Bool.and_eq_true]
    exact ⟨by simp [vocabulary, Md.vocabulary],
      (admitsList_iff _ _).mpr fun x hx => hbody _ x (by simpa using hx)⟩

private theorem viewPara_adm (file : String) (facts : LeanFacts.Facts) (tb : LeanProse.Table)
    (withMath glossary : Bool) (link : Option String) (d : LeanFacts.Decl) (t : LeanFacts.Term)
    (v : View) : Adm true (viewPara file facts tb withMath glossary link d t v).1 := by
  cases v with
  | code => intro r hr; simp [viewPara] at hr
  | docs => intro r hr; simp [viewPara] at hr
  | math => exact displayRaws_adm _ _ _ _
  | prose =>
    simp only [viewPara]
    split
    · refine adm_append (wordsRaws_adm _ _ _ _) ?_
      split
      · exact glossaryRaws_adm _ _ _ _
      · intro r hr; simp at hr
    · split
      · intro r hr; simp at hr
      · exact displayRaws_adm _ _ _ _

private theorem piecesRaws_adm (listing : Nat → List Char → Array Raw) (paras : Array (Array Raw))
    (hl : ∀ start code, Adm b (listing start code)) (hp : ∀ p ∈ paras, Adm b p)
    (pieces : Array Piece) :
    Adm b (piecesRaws listing paras pieces) := by
  unfold piecesRaws
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List Piece) (acc : Array Raw), Adm b acc → Adm b (l.foldl (fun acc p =>
      match p with
      | .code start text => acc.append (listing start text)
      | .statement i => acc.append (paras.getD i #[])
      | .prose _ => acc) acc) from h _ _ (by intro r hr; simp at hr)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons p _ ih =>
    intro acc h
    apply ih
    cases p with
    | code start text => exact adm_append h (hl start text)
    | statement i =>
      refine adm_append h ?_
      simp only [Array.getD_eq_getD_getElem?]
      cases hi : paras[i]? with
      | none => intro r hr; simp at hr
      | some q => exact hp q (Array.mem_of_getElem? hi)
    | prose _ => exact h

private theorem fileListing_adm (starts : Array Nat) (start : Nat) (code : List Char) :
    Adm b (fileListing starts start code) := by
  unfold fileListing
  dsimp only
  split
  · intro r hr; simp at hr
  · intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [listingRaw, Md.Vocab.admits, vocabulary, Md.vocabulary]

private theorem codeFor_adm (starts : Array Nat) (src : Array Char) (segs : List Seg)
    (folds : List ProofFold) (paras : Array (Array Raw)) (hp : ∀ p ∈ paras, Adm b p)
    (head stop : Nat × Nat) : Adm b (codeFor starts src segs folds paras head stop) := by
  unfold codeFor
  exact piecesRaws_adm _ _ (fileListing_adm starts) hp _

private theorem declPara_adm (file : String) (facts : LeanFacts.Facts) (tb : LeanProse.Table)
    (starts : Array Nat) (src : Array Char) (segs : List Seg) (folds : List ProofFold)
    (paras : Array (Array Raw)) (hp : ∀ p ∈ paras, Adm true p) (code withMath glossary wanted : Bool)
    (views : List View) (link : Option String) (d : LeanFacts.Decl) :
    Adm true
      (declPara file facts tb starts src segs folds paras code withMath glossary wanted views link d).1 := by
  unfold declPara
  split
  · intro r hr; simp at hr
  · split
    · exact foldl_adm _ (fun acc v h => adm_append h (viewPara_adm file facts tb withMath glossary link d _ v))
        views (#[], #[], #[]) (by intro r hr; simp at hr)
    · split
      · intro r hr; simp at hr
      · exact codeFor_adm _ _ _ _ _ hp _ _

private theorem disclosure_adm (summary body : Array Raw) (expanded : Bool) (p : Pos)
    (hs : Adm b summary) (hb : Adm b body) : Adm b (Md.disclosureRaws summary body expanded p) := by
  obtain ⟨opts, hd, ho⟩ := Md.disclosureRaws_contract summary body expanded p
  rw [hd]
  intro r hr
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  simp only [Md.Vocab.admits, Bool.and_eq_true]
  refine ⟨by simp [vocabulary, Md.vocabulary], (admitsList_iff _ _).mpr fun x hx => ?_⟩
  have hx' : x ∈ opts ∨ x = .group summary p ∨ x ∈ body := by simpa using hx
  rcases hx' with hx | rfl | hx
  · rcases ho with rfl | rfl
    · simp at hx
    · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
  · exact adm_group _ _ hs
  · exact hb x hx

private theorem foldRaws_adm (starts : Array Nat) (src : Array Char) (f : ProofFold) :
    Adm b (foldRaws starts src f) := by
  unfold foldRaws
  split
  · intro r hr; simp at hr
  apply disclosure_adm
  · intro r hr; simp at hr; subst hr; rfl
  · intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [listingRaw, Md.Vocab.admits, vocabulary, Md.vocabulary]

private theorem withDoc_adm {β : Type} (place : DocPlace) {doc : Array Raw × Array Diag}
    {p : Array Raw × Array Diag × β} (hd : Adm true doc.1) (hp : Adm true p.1) :
    Adm true (withDoc place doc p).1 := by
  cases place
  · exact adm_append hd hp
  · exact adm_append hp hd
  · exact hp

private theorem adm_ite_fst {β : Type} {c : Prop} [Decidable c] {a e : Array Raw × β}
    (ha : Adm true a.1) (he : Adm true e.1) : Adm true (if c then a else e).1 := by
  split
  · exact ha
  · exact he

private theorem docRaws_adm (file : String) (starts : Array Nat) (src : Array Char)
    (known : Option (Std.HashSet String)) (docs : List Seg) (start : Nat × Nat) :
    Adm true (docRaws file starts src known docs start).1 := by
  unfold docRaws
  dsimp only
  split
  · rename_i seg _
    simpa using proseRaws_adm .lean file starts known seg false
  · intro r hr; simp at hr

private theorem docIf_adm (c : Bool) (file : String) (starts : Array Nat) (src : Array Char)
    (known : Option (Std.HashSet String)) (docs : List Seg) (start : Nat × Nat) :
    Adm true (if c = true then ((#[], #[]) : Array Raw × Array Diag)
      else docRaws file starts src known docs start).1 := by
  split
  · intro r hr; simp at hr
  · exact docRaws_adm file starts src known docs start

private theorem statementsFor_adm (file : String) (starts : Array Nat) (src : Array Char)
    (segs : List Seg) (showing : Showing) (declared : LeanProse.Declared) (place : LinkPlace)
    (folds : List ProofFold) (foldParas : Array (Array Raw)) (hf : ∀ p ∈ foldParas, Adm true p)
    (request : Span) (docs : List Seg) (known : Option (Std.HashSet String))
    (facts : Option LeanFacts.Facts) :
    ∀ p ∈ (statementsFor file starts src segs showing declared place folds foldParas request
      docs known facts).1, Adm true p := by
  cases facts with
  | none => intro p hp; simp [statementsFor] at hp
  | some f =>
    have h0 : ∀ p ∈ Array.replicate (2 * f.decls.size + f.failed.size) (#[] : Array Raw) ++
        foldParas, Adm true p := by
      intro p hp
      rcases Array.mem_append.mp hp with hp | hp
      · rw [Array.mem_replicate] at hp
        rw [hp.2]
        intro r hr
        simp at hr
      · exact hf p hp
    intro p hp
    simp only [statementsFor, statementsOf, Array.mem_append, Array.mem_map] at hp
    rcases hp with (⟨_, ⟨d, _, rfl⟩, rfl⟩ | ⟨_, ⟨d, _, rfl⟩, rfl⟩) | ⟨_, ⟨fl, _, rfl⟩, rfl⟩
    · exact withDoc_adm _ (docIf_adm _ _ _ _ _ _ _) (declPara_adm _ _ _ _ _ _ _ _ h0 _ _ _ _ _ _ _)
    · exact withDoc_adm _ (docIf_adm _ _ _ _ _ _ _) (declPara_adm _ _ _ _ _ _ _ _ h0 _ _ _ _ _ _ _)
    · exact adm_ite_fst (withDoc_adm _ (docRaws_adm _ _ _ _ _ _)
        (show Adm true (codeFor starts src segs folds _ fl.head fl.stop, (#[] : Array Diag), ()).1 from
          codeFor_adm starts src segs folds _ h0 _ _)) (by intro r hr; simp at hr)

private theorem pieceRaws_adm (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (hs : ∀ p ∈ page.stmts, Adm (lang == .lean) p)
    (opens : Bool) (piece : Piece) :
    Adm (lang == .lean) (pieceRaws lang file starts page opens piece) := by
  cases piece with
  | code start code =>
    simp only [pieceRaws]
    split
    · intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp [listingRaw, Md.Vocab.admits, vocabulary, Md.vocabulary]
    · intro r hr; simp at hr
  | prose seg =>
    simp only [pieceRaws]
    split
    · exact proseRaws_adm lang file starts page.cites seg opens
    · intro r hr; simp at hr
  | statement i =>
    simp only [pieceRaws, Array.getD_eq_getD_getElem?]
    cases h : page.stmts[i]? with
    | none => intro r hr; simp at hr
    | some p => exact hs p (Array.mem_of_getElem? h)

private theorem titleSource_adm (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (known : Option (Std.HashSet String)) (opens : Bool) (piece : Piece) :
    Adm (lang == .lean) (titleSource lang file starts known opens piece) := by
  cases piece with
  | prose seg => exact proseRaws_adm lang file starts known seg opens
  | code _ _ => intro r hr; simp [titleSource] at hr
  | statement _ => intro r hr; simp [titleSource] at hr

/-- What the fold over a file's pieces keeps: its body and its title inside the vocabulary. -/
private def Inv (b : Bool) (acc : Acc) : Prop := Adm b acc.body ∧ ∀ t, acc.title = some t → Adm b t

private theorem pieceStep_inv (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (hs : ∀ p ∈ page.stmts, Adm (lang == .lean) p)
    (acc : Acc) (piece : Piece) (h : Inv (lang == .lean) acc) :
    Inv (lang == .lean) (pieceStep lang file starts page acc piece) := by
  have hp := pieceRaws_adm lang file starts page hs (acc.opens piece) piece
  have hsrc := titleSource_adm lang file starts page.cites (acc.opens piece) piece
  obtain ⟨hbody, htitle⟩ := pieceStep_exact lang file starts page acc piece
  refine ⟨hbody ▸ adm_append h.1 hp, ?_⟩
  intro t ht
  rw [htitle] at ht
  split at ht
  · exact openingHeading_adm _ (fun r hr => hsrc r (by simpa using hr)) t ht
  · exact h.2 t ht

private theorem foldl_inv (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (hs : ∀ p ∈ page.stmts, Adm (lang == .lean) p) :
    (l : List Piece) → (acc : Acc) → Inv (lang == .lean) acc →
      Inv (lang == .lean) (l.foldl (pieceStep lang file starts page) acc)
  | [], _, h => h
  | p :: rest, acc, h =>
    foldl_inv lang file starts page hs rest _ (pieceStep_inv lang file starts page hs acc p h)

private theorem directive_adm (value : String) (p : Pos) : Adm b (directiveRaws value p) := by
  have one : ∀ name v, name = "theme" ∨ name = "output" →
      Adm b (#[Raw.ctrl name p, .group #[.word v p] p]) := by
    intro name v hn
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rcases hn with rfl | rfl <;> simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
    · exact adm_group _ _ (by intro x hx; simp at hx; subst hx; rfl)
  have flat : ∀ (name : String) (vs : List String), (name = "theme" ∨ name = "output") →
      Adm b (vs.map fun v => #[Raw.ctrl name p, .group #[.word v p] p]).toArray.flatten := by
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

private theorem title_adm (acc : Acc) (h : Inv b acc) (fallback : Array Raw)
    (hf : Adm b fallback) : Adm b (acc.title.getD fallback) := by
  cases ht : acc.title with
  | some t => simpa [ht] using h.2 t ht
  | none => simpa [ht] using hf

private theorem textRaws_adm (s : String) (p : Pos) : Adm b (Md.textRaws s p) := by
  intro r hr
  rcases Md.textRaws_covers _ _ r hr with rfl | ⟨w, q, rfl⟩ <;> rfl

private theorem titleHeading_adm (t : Array Raw) (p : Pos) (h : Adm b t) :
    Adm b (Parse.headingRaws .title t p) := by
  rw [Parse.headingRaws_contract]
  intro r hr
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem]
    exact Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨.title, by simp, rfl⟩)))
  · rfl
  · exact adm_group _ _ h

private theorem adm_lit {l : List Raw} (h : ∀ r ∈ l, (voc b).admits r = true) :
    Adm b l.toArray := fun r hr => h r (by simpa using hr)

private theorem adm_extract {a : Array Raw} (h : Adm b a) (i j : Nat) : Adm b (a.extract i j) := by
  intro r hr
  simp only [Array.mem_extract_iff_getElem] at hr
  obtain ⟨k, hk, rfl⟩ := hr
  exact h _ (Array.getElem_mem _)

private theorem placedBody_adm (acc : Acc) (refs : Option Refs) (style : Option String)
    (h : Adm b acc.body) : Adm b (placedBody acc refs style) := by
  have word : ∀ w p, Adm b (#[Raw.word w p] : Array Raw) := by
    intro w p x hx; simp at hx; subst hx; rfl
  unfold placedBody
  split
  · split
    · exact h
    · split
      · refine adm_append (adm_append (adm_extract h _ _) (adm_lit ?_)) (adm_extract h _ _)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rfl
        · simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem]
          exact Or.inr (List.mem_append.mpr (Or.inr (by simp)))
        · exact adm_group _ _ (word _ _)
        · exact adm_group _ _ (word _ _)
      · refine adm_append h (adm_lit ?_)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rfl
        · simp [Md.Vocab.admits, vocabulary]
        · exact adm_group _ _ (word _ _)
        · simp [Md.Vocab.admits, vocabulary]
        · exact adm_group _ _ (word _ _)
  · exact h

/-- Every view is listed, as the reader, its help and the package's check read them. -/
public theorem View.all_complete (v : View) : v ∈ View.all := by
  cases v <;> simp [View.all]

/-- The code reader's vocabulary admits no request a driver must fulfil. -/
public theorem vocabulary_requests : vocabulary.requests = [] := rfl

private theorem showingOfValues_views (lang : Ir.CodeLang) (values : List (String × String))
    (alone : Bool) : ∀ v ∈ (showingOfValues lang values alone).views,
      v = .code ∨ v.setBy lang alone = true := by
  intro v hv
  have key : ∀ (l : List View), (∀ x ∈ l, x.setBy lang alone = true) →
      v ∈ (if l.isEmpty then [View.code] else l) → v = .code ∨ v.setBy lang alone = true := by
    intro l hl hv
    split at hv
    · simp at hv; exact Or.inl hv
    · exact Or.inr (hl v hv)
  have hset : ∀ (named : List String), ∀ x ∈ (named.filterMap fun n =>
      View.all.find? fun v => v.name == n && v.setBy lang alone).eraseDups,
      x.setBy lang alone = true := by
    intro named x hx
    simp only [List.mem_eraseDups, List.mem_filterMap] at hx
    obtain ⟨n, _, hn⟩ := hx
    have := List.find?_some hn
    simp only [Bool.and_eq_true] at this
    exact this.2
  unfold showingOfValues at hv
  split at hv <;> exact key _ (hset _) hv

private theorem showingOf_statements (lang : Ir.CodeLang) (h : (lang == .lean) = false)
    (src : Array Char) : (showingOf lang src).statements = false := by
  have hv : ∀ v ∈ (showingOf lang src).views, v = .code := by
    intro v hv
    unfold showingOf at hv
    split at hv
    · simpa using hv
    · rcases showingOfValues_views lang _ false v hv with hc | hs
      · exact hc
      · cases v with
        | code => rfl
        | math | prose | docs => simp [View.setBy, h] at hs
  have hm : (showingOf lang src).views.contains .math = false := by
    cases hc : (showingOf lang src).views.contains .math
    · rfl
    · have := hv _ (List.contains_iff_mem.mp hc); cases this
  have hp : (showingOf lang src).views.contains .prose = false := by
    cases hc : (showingOf lang src).views.contains .prose
    · rfl
    · have := hv _ (List.contains_iff_mem.mp hc); cases this
  simp only [Showing.statements, Showing.math, Showing.prose, hm, hp, Bool.or_self]

/-- A page of a file of `lang` sets only what that language's vocabulary admits, so a formula only
on a Lean file's page. -/
public theorem read_vocabularyFor_mem (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) (place : LinkPlace) (refs : Option Refs) :
    ∀ r ∈ (read lang file text facts place refs).1, (vocabularyFor lang).admits r = true := by
  have hfold : ∀ (fs : List ProofFold) (p : Array Raw),
      p ∈ (fs.map (foldRaws (lineStarts text.toList.toArray) text.toList.toArray)).toArray →
      Adm (lang == .lean) p := by
    intro fs p hp
    simp only [List.mem_toArray, List.mem_map] at hp
    obtain ⟨fo, _, rfl⟩ := hp
    exact foldRaws_adm _ _ _
  have hplan : ∀ p ∈ (planOf lang file text facts place (refs.map (·.keys))).1.stmts,
      Adm (lang == .lean) p := by
    simp only [planOf]
    intro p hp
    rcases Array.mem_append.mp hp with hp | hp
    · cases hl : lang == .lean with
      | true => exact statementsFor_adm _ _ _ _ _ _ _ _ _ (hl ▸ hfold _) _ _ _ _ p hp
      | false =>
        simp [showingOf_statements lang hl, statementsFor] at hp
    · exact hfold _ p hp
  have hcited : ∀ p ∈ ((planOf lang file text facts place (refs.map (·.keys))).1.citing
      (refs.map (·.keys))).stmts,
      Adm (lang == .lean) p := by
    rw [PageSet.citing_stmts]
    exact hplan
  have hacc : Inv (lang == .lean) (readPieces lang file text
      ((planOf lang file text facts place (refs.map (·.keys))).1.citing (refs.map (·.keys)))
      (planOf lang file text facts place (refs.map (·.keys))).2.1) :=
    foldl_inv lang file _ _ hcited _ {} ⟨by simp [Adm], by simp⟩
  show ∀ r ∈ _, (voc (lang == .lean)).admits r = true
  unfold read
  dsimp only
  generalize readPieces lang file text _ _ = acc at hacc ⊢
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
  · simp only [Md.Vocab.admits, Bool.and_eq_true]
    refine ⟨by simp [vocabulary, Md.vocabulary], (admitsList_iff _ _).mpr fun r hr => ?_⟩
    have hplaced := placedBody_adm acc refs (showingOf lang text.toList.toArray).bibStyle hacc.1
    have hbody : Adm (lang == .lean) (if acc.titled then
        placedBody acc refs (showingOf lang text.toList.toArray).bibStyle
        else Parse.headingRaws .title (acc.title.getD (Md.textRaws (baseName file) {})) {} ++
          placedBody acc refs (showingOf lang text.toList.toArray).bibStyle) := by
      split
      · exact hplaced
      · exact adm_append (titleHeading_adm _ _ htitle) hplaced
    exact hbody r (by simpa using hr)

/-- Everything a code file reads into stays inside the reader's declared vocabulary. -/
public theorem read_vocabulary_mem (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) (place : LinkPlace) (refs : Option Refs) :
    ∀ r ∈ (read lang file text facts place refs).1, vocabulary.admits r = true := fun r hr =>
  Md.Vocab.admits_formulas _ r (read_vocabularyFor_mem lang file text facts place refs r hr)

/-- A Lean file's page lowers into the reader's whole vocabulary, formulas included. -/
public theorem vocabularyFor_lean : vocabularyFor .lean = vocabulary := by
  rw [vocabularyFor, beq_self_eq_true]; rfl

private theorem listingAt_adm (starts : Array Nat) (start : Nat) (code : List Char) :
    Adm b (listingAt starts start code) := by
  unfold listingAt
  dsimp only
  split
  · intro r hr; simp at hr
  · intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [Md.Vocab.admits, vocabulary, Md.vocabulary]

private theorem docsRaws_adm (file text : String) (starts : Array Nat)
    (known : Option (Std.HashSet String)) : Adm true (docsRaws file text starts known).1 := by
  unfold docsRaws
  rw [← Array.foldl_toList]
  refine foldl_adm _ (fun acc piece h => ?_) _ _ (by intro r hr; simp at hr)
  cases piece with
  | code start code => exact adm_append h (listingAt_adm _ _ _)
  | prose seg => exact adm_append h (by simpa using proseRaws_adm .lean file starts known seg false)
  | statement _ => exact h

private theorem paras_adm (file : String) (starts : Array Nat) (src : Array Char)
    (segs : List Seg) (showing : Showing) (declared : LeanProse.Declared) (place : LinkPlace)
    (folds : List ProofFold) (request : Span) (docs : List Seg)
    (known : Option (Std.HashSet String)) (facts : Option LeanFacts.Facts) :
    ∀ p ∈ (statementsFor file starts src segs showing declared place folds
      (folds.map (foldRaws starts src)).toArray request docs known facts).1 ++
      (folds.map (foldRaws starts src)).toArray, Adm true p := by
  have hfold : ∀ p ∈ (folds.map (foldRaws starts src)).toArray, Adm true p := by
    intro p hp
    simp only [List.mem_toArray, List.mem_map] at hp
    obtain ⟨fo, _, rfl⟩ := hp
    exact foldRaws_adm _ _ _
  intro p hp
  rcases Array.mem_append.mp hp with hp | hp
  · exact statementsFor_adm _ _ _ _ _ _ _ _ _ hfold _ _ _ _ p hp
  · exact hfold p hp

private theorem getD_adm {paras : Array (Array Raw)} (h : ∀ p ∈ paras, Adm b p) (k : Nat) :
    Adm b (paras.getD k #[]) := by
  simp only [Array.getD_eq_getD_getElem?]
  cases hk : paras[k]? with
  | none => intro r hr; simp at hr
  | some q => exact h q (Array.mem_of_getElem? hk)

private theorem adm_nil : Adm b #[] := by intro r hr; simp at hr

private theorem adm_ite {c : Prop} [Decidable c] {a e : Array Raw} (ha : Adm b a) (he : Adm b e) :
    Adm b (if c then a else e) := by
  split
  · exact ha
  · exact he

private theorem chosenRaws_adm (items : Array (Nat × Array Raw)) (h : ∀ x ∈ items, Adm b x.2) :
    Adm b (chosenRaws items) := by
  unfold chosenRaws
  have hm : ∀ x ∈ items.toList.mergeSort fun a b => decide (a.1 ≤ b.1), Adm b x.2 :=
    fun x hx => h x (Array.mem_toList_iff.mp (List.mem_mergeSort.mp hx))
  generalize items.toList.mergeSort (fun a b => decide (a.1 ≤ b.1)) = l at hm
  suffices ∀ acc : Array Raw, Adm b acc → Adm b (l.foldl (fun acc x => acc ++ x.2) acc) from
    this #[] (by intro r hr; simp at hr)
  induction l with
  | nil => exact fun _ h => h
  | cons x rest ih =>
    intro acc ha
    exact ih (fun y hy => hm y (List.mem_cons_of_mem _ hy)) _
      (adm_append ha (hm x (List.mem_cons_self ..)))

private theorem sizedRaws_adm (size : Option String) (pos : Pos) {raws : Array Raw}
    (h : Adm true raws) : ∀ r ∈ sizedRaws size pos raws, vocabulary.admits r = true := by
  unfold sizedRaws
  split
  · rename_i n
    split
    · rename_i hn
      intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      refine adm_group _ _ (adm_append ?_ h)
      intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [List.contains_iff_mem] at hn
      simp [Md.Vocab.admits, vocabulary, hn]
    · exact h
  · exact h

/-- A Lean inclusion sets its file as the one input environment naming it, every raw inside which
lies in the reader's declared vocabulary. -/
public theorem includeLean_vocabulary_mem (file text : String) (showing : Showing)
    (facts : Option LeanFacts.Facts) (place : LinkPlace) (request : Span) (entry : String)
    (refs : Option Refs) :
    ∃ body, (includeLean file text showing facts place request entry refs).1 =
        #[.env (Parse.keptInputEnv file) body request.pos] ∧ ∀ r ∈ body, vocabulary.admits r = true := by
  unfold includeLean
  dsimp only
  split
  · exact ⟨_, rfl, sizedRaws_adm _ _ (docsRaws_adm _ _ _ _)⟩
  · split
    · exact ⟨_, rfl, sizedRaws_adm _ _ (listingAt_adm _ _ _)⟩
    · have hp := paras_adm
      split
      · refine ⟨_, rfl, sizedRaws_adm _ _ (piecesRaws_adm _ _ (fun s t => ?_) (hp _ _ _ _ _ _ _ _ _ _ _ _) _)⟩
        split
        · exact listingAt_adm _ _ _
        · intro r hr; simp at hr
      · refine ⟨_, rfl, sizedRaws_adm _ _ (chosenRaws_adm _ ?_)⟩
        intro x hx
        simp only [Array.mem_append, Array.mem_map] at hx
        rcases hx with ⟨d, _, rfl⟩ | ⟨fl, _, rfl⟩
        · exact adm_append (adm_append (adm_ite (getD_adm (hp _ _ _ _ _ _ _ _ _ _ _ _) _) adm_nil)
            (adm_ite (piecesRaws_adm _ _ (listingAt_adm _) (hp _ _ _ _ _ _ _ _ _ _ _ _) _) adm_nil))
            (adm_ite (getD_adm (hp _ _ _ _ _ _ _ _ _ _ _ _) _) adm_nil)
        · exact piecesRaws_adm _ _ (listingAt_adm _) (hp _ _ _ _ _ _ _ _ _ _ _ _) _

end LeanTex.Core.Code
