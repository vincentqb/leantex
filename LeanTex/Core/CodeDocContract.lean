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
      "bibliography"]
    envs := Md.vocabulary.envs ++ ["document", "flushleft"]
    formulas := true
    mathCtrls := LeanNotation.MathCtrl.all.map (·.name)
    mathSyms := ['^', '_'] }

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
  | .math _ _ _, h => by simp [Md.Vocab.admits, Md.vocabulary] at h
  | .env n body _, h => by
    simp only [Md.Vocab.admits, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h ⊢
    refine ⟨?_, mono_list body.toList h.2⟩
    simp only [vocabulary, List.mem_append]
    rcases h.1 with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  | .verb e _ _, h => by simpa [Md.Vocab.admits, vocabulary] using h

private theorem mono_list : (l : List Raw) → Md.vocabulary.admitsList l = true →
    vocabulary.admitsList l = true
  | [], _ => rfl
  | r :: rest, h => by
    simp only [Md.Vocab.admitsList, Bool.and_eq_true] at h ⊢
    exact ⟨mono_one r h.1, mono_list rest h.2⟩

end

mutual

private theorem mathMap_one (f : Pos → Pos) : (r : Raw) →
    vocabulary.mathAdmits (mapPos f r) = vocabulary.mathAdmits r
  | .word _ _ => rfl
  | .space => rfl
  | .par _ => rfl
  | .ctrl _ _ => rfl
  | .sym _ _ => rfl
  | .group body _ => by
    simp only [mapPos, Md.Vocab.mathAdmits]
    rw [mathMap_list f #[] body.toList]
    simp [Md.Vocab.mathAdmitsList]
  | .math _ _ _ => rfl
  | .env _ _ _ => rfl
  | .verb _ _ _ => rfl

private theorem mathMap_list (f : Pos → Pos) (acc : Array Raw) : (l : List Raw) →
    vocabulary.mathAdmitsList (mapPosList f acc l).toList =
      (vocabulary.mathAdmitsList acc.toList && vocabulary.mathAdmitsList l)
  | [] => by simp [mapPosList, Md.Vocab.mathAdmitsList]
  | r :: rest => by
    simp only [mapPosList]
    rw [mathMap_list f (acc.push (mapPos f r)) rest]
    simp [mathAdmitsList_append, Md.Vocab.mathAdmitsList, mathMap_one f r, Bool.and_assoc]

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
  | .math _ body _ => by
    simp only [mapPos, Md.Vocab.admits]
    rw [mathMap_list f #[] body.toList]
    simp [Md.Vocab.mathAdmitsList]
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
  exact Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨.title, by simp, rfl⟩)))

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
    (known : Option (Std.HashSet String)) (seg : Seg) (opens : Bool) :
    Adm (proseRaws lang file starts known seg opens).1 := by
  let k := if lang == .lean then known else none
  have hraws : ∀ (pr : Prose),
      Adm (mapPosList pr.place #[] (Md.desugar file pr.text .docstring .document false k).1.toList) := by
    intro pr
    apply adm_mapPos
    exact Md.desugar_vocabulary_mem _ _ .docstring .document false k
  let pr := proseIn lang seg.text (lineCol starts seg.start).1 ((lineCol starts seg.start).2 - 1)
  have h := hraws pr
  cases opens with
  | true =>
    have hl : ∀ x ∈ (mapPosList pr.place #[]
        (Md.desugar file pr.text .docstring .document false k).1.toList).toList,
        vocabulary.admits x = true := fun x hx => h x (by simpa using hx)
    intro r hr
    exact retitle_adm _ hl r (by simpa [proseRaws, k] using hr)
  | false => simpa [proseRaws, k] using h

private theorem caret_sym : '^' ∈ vocabulary.mathSyms := by simp [vocabulary]

private theorem under_sym : '_' ∈ vocabulary.mathSyms := by simp [vocabulary]

mutual

private theorem pushRaws_adm (pos : Pos) : (m : LeanNotation.Math) → (acc : Array Raw) →
    vocabulary.mathAdmitsList acc.toList = true →
    vocabulary.mathAdmitsList (LeanStatement.Math.pushRaws pos acc m).toList = true
  | .word _, acc, h => by
    simp [LeanStatement.Math.pushRaws, mathAdmitsList_append, h, Md.Vocab.mathAdmitsList,
      Md.Vocab.mathAdmits]
  | .ctrl c, acc, h => by
    simp only [LeanStatement.Math.pushRaws, Array.toList_push, mathAdmitsList_append, h,
      Md.Vocab.mathAdmitsList, Md.Vocab.mathAdmits, Bool.true_and, Bool.and_true,
      List.contains_iff_mem]
    exact List.mem_map.mpr ⟨c, LeanNotation.MathCtrl.mem_all c, rfl⟩
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
    vocabulary.mathAdmitsList acc.toList = true →
    vocabulary.mathAdmitsList (LeanStatement.Math.listRaws pos acc l).toList = true
  | [], _, h => by simpa [LeanStatement.Math.listRaws] using h
  | m :: rest, acc, h => by
    simp only [LeanStatement.Math.listRaws]
    exact listRaws_adm pos rest _ (pushRaws_adm pos m acc h)

end

private theorem textRaws_adm' (s : String) (p : Pos) : Adm (Md.textRaws s p) := by
  intro r hr
  rcases Md.textRaws_covers _ _ r hr with rfl | ⟨w, q, rfl⟩ <;> rfl

private theorem breakRaws_adm (pos : Pos) : Adm (breakRaws pos) := by
  intro r hr
  simp only [breakRaws, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp [Md.Vocab.admits, vocabulary]
  · exact adm_group _ _ (by intro x hx; simp at hx; subst hx; rfl)

private theorem headRaws_adm (d : LeanFacts.Decl) (pos : Pos) (link : Option String) :
    Adm (headRaws d pos link) := by
  have hname : Adm #[.ctrl "texttt" pos, .group (Md.textRaws d.name pos) pos] := by
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
    · exact adm_group _ _ (textRaws_adm' _ _)
  have hnamed : Adm (nameRaws d pos link) := by
    unfold nameRaws
    split
    · intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
      · exact adm_group _ _ (by intro x hx; simp at hx; subst hx; rfl)
      · exact adm_group _ _ hname
    · exact hname
  have hlead : Adm #[.ctrl "textbf" pos, .group #[.word d.kind.label pos] pos,
      .space, .word "(" pos] := by
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [Md.Vocab.admits, vocabulary, Md.vocabulary]
    · simp [Md.Vocab.admits, Md.Vocab.admitsList]
    · rfl
    · rfl
  have hclose : Adm (if d.kind == .theorem && !d.proved then
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
    vocabulary.admits (formulaRaw pos m) = true := by
  simp only [formulaRaw, Md.Vocab.admits, Bool.and_eq_true]
  exact ⟨rfl, by simpa using listRaws_adm pos m.toList #[] (by simp [Md.Vocab.mathAdmitsList])⟩

/-- A fold whose step keeps its raws inside the vocabulary keeps them there. -/
private theorem foldl_adm {β γ : Type} (f : Array Raw × β → γ → Array Raw × β)
    (hf : ∀ acc x, Adm acc.1 → Adm (f acc x).1) :
    ∀ (l : List γ) (acc : Array Raw × β), Adm acc.1 → Adm (l.foldl f acc).1
  | [], _, h => h
  | x :: rest, acc, h => foldl_adm f hf rest _ (hf acc x h)

private theorem displayRaws_adm (d : LeanFacts.Decl)
    (formulas : Array (Array LeanNotation.Math × Bool)) (pos : Pos) (link : Option String) :
    Adm (displayRaws d formulas pos link) := by
  have step : ∀ (st : Array Raw × Bool) (mn : Array LeanNotation.Math × Bool), Adm st.1 →
      Adm (displayStep pos st mn).1 := by
    intro st mn h
    refine adm_push (adm_append h ?_) (formulaRaw_adm pos mn.1)
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

private theorem leafRaws_adm (pos : Pos) (l : LeanProse.Leaf) : Adm (leafRaws pos l) := by
  cases l with
  | nil => intro r hr; simp [leafRaws] at hr
  | cons m rest =>
    simp only [leafRaws]
    have h : ∀ (l : List (Array LeanNotation.Math)) (acc : Array Raw), Adm acc →
        Adm (l.foldl (fun acc q => (acc ++ breakRaws pos).push (formulaRaw pos q)) acc) := by
      intro l
      induction l with
      | nil => intro acc h; exact h
      | cons q _ ih =>
        intro acc h
        exact ih _ (adm_push (adm_append h (breakRaws_adm pos)) (formulaRaw_adm pos q))
    exact h rest _ (by intro r hr; simp at hr; subst hr; exact formulaRaw_adm pos m)

private theorem tokRaws_adm (pos : Pos) (opening : Bool) (t : LeanProse.Tok LeanProse.Leaf) :
    Adm (tokRaws pos opening t).1 := by
  unfold tokRaws
  split
  · intro r hr; simp at hr; subst hr; rfl
  · intro r hr; simp at hr; subst hr; rfl
  · exact leafRaws_adm pos _

private theorem sentenceRaws_adm (pos : Pos) (toks : List (LeanProse.Tok LeanProse.Leaf)) :
    Adm (sentenceRaws pos toks) := by
  unfold sentenceRaws
  refine adm_push (foldl_adm _ ?_ toks (#[], none, true) (by intro r hr; simp at hr)) rfl
  intro acc t h
  refine adm_append (adm_append h ?_) (tokRaws_adm pos _ t)
  split
  · intro r hr; simp at hr
  · intro r hr; simp at hr; subst hr; rfl

private theorem wordsRaws_adm (d : LeanFacts.Decl) (s : LeanProse.Stmt LeanProse.Leaf)
    (pos : Pos) (link : Option String) : Adm (wordsRaws d s pos link) := by
  have hbody := adm_append (adm_push (r := .space) (headRaws_adm d pos link) rfl)
    (sentenceRaws_adm pos (LeanProse.render s))
  intro r hr
  simp only [wordsRaws, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  simp only [Md.Vocab.admits, Bool.and_eq_true]
  exact ⟨by simp [vocabulary, Md.vocabulary], (admitsList_iff _ _).mpr fun x hx =>
    hbody x (by simpa [or_assoc] using hx)⟩

private theorem viewPara_adm (file : String) (facts : LeanFacts.Facts) (tb : LeanProse.Table)
    (withMath : Bool) (link : Option String) (d : LeanFacts.Decl) (t : LeanFacts.Term) (v : View) :
    Adm (viewPara file facts tb withMath link d t v).1 := by
  cases v with
  | code => intro r hr; simp [viewPara] at hr
  | docs => intro r hr; simp [viewPara] at hr
  | math => exact displayRaws_adm _ _ _ _
  | prose =>
    simp only [viewPara]
    split
    · exact wordsRaws_adm _ _ _ _
    · split
      · intro r hr; simp at hr
      · exact displayRaws_adm _ _ _ _

private theorem piecesRaws_adm (listing : Nat → List Char → Array Raw) (paras : Array (Array Raw))
    (hl : ∀ start code, Adm (listing start code)) (hp : ∀ p ∈ paras, Adm p) (pieces : Array Piece) :
    Adm (piecesRaws listing paras pieces) := by
  unfold piecesRaws
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List Piece) (acc : Array Raw), Adm acc → Adm (l.foldl (fun acc p =>
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
    Adm (fileListing starts start code) := by
  unfold fileListing
  dsimp only
  split
  · intro r hr; simp at hr
  · intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [listingRaw, Md.Vocab.admits, vocabulary, Md.vocabulary]

private theorem codeFor_adm (starts : Array Nat) (src : Array Char) (segs : List Seg)
    (folds : List ProofFold) (paras : Array (Array Raw)) (hp : ∀ p ∈ paras, Adm p)
    (head stop : Nat × Nat) : Adm (codeFor starts src segs folds paras head stop) := by
  unfold codeFor
  exact piecesRaws_adm _ _ (fileListing_adm starts) hp _

private theorem declPara_adm (file : String) (facts : LeanFacts.Facts) (tb : LeanProse.Table)
    (starts : Array Nat) (src : Array Char) (segs : List Seg) (folds : List ProofFold)
    (paras : Array (Array Raw)) (hp : ∀ p ∈ paras, Adm p) (code withMath wanted : Bool)
    (views : List View) (link : Option String) (d : LeanFacts.Decl) :
    Adm (declPara file facts tb starts src segs folds paras code withMath wanted views link d).1 := by
  unfold declPara
  split
  · intro r hr; simp at hr
  · split
    · exact foldl_adm _ (fun acc v h => adm_append h (viewPara_adm file facts tb withMath link d _ v))
        views (#[], #[], #[]) (by intro r hr; simp at hr)
    · split
      · intro r hr; simp at hr
      · exact codeFor_adm _ _ _ _ _ hp _ _

private theorem disclosure_adm (summary body : Array Raw) (expanded : Bool) (p : Pos)
    (hs : Adm summary) (hb : Adm body) : Adm (Md.disclosureRaws summary body expanded p) := by
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
    Adm (foldRaws starts src f) := by
  unfold foldRaws
  split
  · intro r hr; simp at hr
  apply disclosure_adm
  · intro r hr; simp at hr; subst hr; rfl
  · intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [listingRaw, Md.Vocab.admits, vocabulary, Md.vocabulary]

private theorem statementsFor_adm (file : String) (starts : Array Nat) (src : Array Char)
    (segs : List Seg) (showing : Showing) (declared : LeanProse.Declared) (place : LinkPlace)
    (folds : List ProofFold) (foldParas : Array (Array Raw)) (hf : ∀ p ∈ foldParas, Adm p)
    (request : Span) (facts : Option LeanFacts.Facts) :
    ∀ p ∈ (statementsFor file starts src segs showing declared place folds foldParas request
      facts).1, Adm p := by
  cases facts with
  | none => intro p hp; simp [statementsFor] at hp
  | some f =>
    have h0 : ∀ p ∈ Array.replicate (2 * f.decls.size + f.failed.size) (#[] : Array Raw) ++
        foldParas, Adm p := by
      intro p hp
      rcases Array.mem_append.mp hp with hp | hp
      · rw [Array.mem_replicate] at hp
        rw [hp.2]
        intro r hr
        simp at hr
      · exact hf p hp
    intro p hp
    simp only [statementsFor, statementsOf, Array.mem_append, Array.mem_map] at hp
    rcases hp with (⟨_, ⟨d, _, rfl⟩, rfl⟩ | ⟨_, ⟨d, _, rfl⟩, rfl⟩) | ⟨fl, _, rfl⟩
    · exact declPara_adm _ _ _ _ _ _ _ _ h0 _ _ _ _ _ _
    · exact declPara_adm _ _ _ _ _ _ _ _ h0 _ _ _ _ _ _
    · have hif : ∀ b : Bool, Adm (if b = true then codeFor starts src segs folds
          (Array.replicate (2 * f.decls.size + f.failed.size) #[] ++ foldParas) fl.head fl.stop
          else #[]) := by
        intro b
        cases b
        · intro r hr; simp at hr
        · simpa using codeFor_adm starts src segs folds _ h0 fl.head fl.stop
      exact hif _

private theorem pieceRaws_adm (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (hs : ∀ p ∈ page.stmts, Adm p)
    (opens : Bool) (piece : Piece) : Adm (pieceRaws lang file starts page opens piece) := by
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
    Adm (titleSource lang file starts known opens piece) := by
  cases piece with
  | prose seg => exact proseRaws_adm lang file starts known seg opens
  | code _ _ => intro r hr; simp [titleSource] at hr
  | statement _ => intro r hr; simp [titleSource] at hr

/-- What the fold over a file's pieces keeps: its body and its title inside the vocabulary. -/
private def Inv (acc : Acc) : Prop := Adm acc.body ∧ ∀ t, acc.title = some t → Adm t

private theorem pieceStep_inv (lang : Ir.CodeLang) (file : String) (starts : Array Nat)
    (page : PageSet) (hs : ∀ p ∈ page.stmts, Adm p)
    (acc : Acc) (piece : Piece) (h : Inv acc) : Inv (pieceStep lang file starts page acc piece) := by
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
    (page : PageSet) (hs : ∀ p ∈ page.stmts, Adm p) :
    (l : List Piece) → (acc : Acc) → Inv acc → Inv (l.foldl (pieceStep lang file starts page) acc)
  | [], _, h => h
  | p :: rest, acc, h =>
    foldl_inv lang file starts page hs rest _ (pieceStep_inv lang file starts page hs acc p h)

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
    exact Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨.title, by simp, rfl⟩)))
  · rfl
  · exact adm_group _ _ h

private theorem adm_lit {l : List Raw} (h : ∀ r ∈ l, vocabulary.admits r = true) :
    Adm l.toArray := fun r hr => h r (by simpa using hr)

private theorem adm_extract {a : Array Raw} (h : Adm a) (i j : Nat) : Adm (a.extract i j) := by
  intro r hr
  simp only [Array.mem_extract_iff_getElem] at hr
  obtain ⟨k, hk, rfl⟩ := hr
  exact h _ (Array.getElem_mem _)

private theorem placedBody_adm (acc : Acc) (refs : Option Refs) (style : Option String)
    (h : Adm acc.body) : Adm (placedBody acc refs style) := by
  have word : ∀ w p, Adm (#[Raw.word w p] : Array Raw) := by
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

/-- Everything a code file reads into stays inside the reader's declared vocabulary. -/
public theorem read_vocabulary_mem (lang : Ir.CodeLang) (file text : String)
    (facts : Option LeanFacts.Facts) (place : LinkPlace) (refs : Option Refs) :
    ∀ r ∈ (read lang file text facts place refs).1, vocabulary.admits r = true := by
  have hplan : ∀ p ∈ (planOf lang file text facts place).1.stmts, Adm p := by
    have hfold : ∀ (fs : List ProofFold) (p : Array Raw),
        p ∈ (fs.map (foldRaws (lineStarts text.toList.toArray) text.toList.toArray)).toArray →
        Adm p := by
      intro fs p hp
      simp only [List.mem_toArray, List.mem_map] at hp
      obtain ⟨fo, _, rfl⟩ := hp
      exact foldRaws_adm _ _ _
    simp only [planOf]
    intro p hp
    rcases Array.mem_append.mp hp with hp | hp
    · exact statementsFor_adm _ _ _ _ _ _ _ _ _ (hfold _) _ _ p hp
    · exact hfold _ p hp
  have hcited : ∀ p ∈ ((planOf lang file text facts place).1.citing (refs.map (·.keys))).stmts,
      Adm p := by
    rw [PageSet.citing_stmts]
    exact hplan
  have hacc : Inv (readPieces lang file text
      ((planOf lang file text facts place).1.citing (refs.map (·.keys)))
      (planOf lang file text facts place).2.1) :=
    foldl_inv lang file _ _ hcited _ {} ⟨by simp [Adm], by simp⟩
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
    have hbody : Adm (if acc.titled then placedBody acc refs (showingOf lang text.toList.toArray).bibStyle
        else Parse.headingRaws .title (acc.title.getD (Md.textRaws (baseName file) {})) {} ++
          placedBody acc refs (showingOf lang text.toList.toArray).bibStyle) := by
      split
      · exact hplaced
      · exact adm_append (titleHeading_adm _ _ htitle) hplaced
    exact hbody r (by simpa using hr)

private theorem listingAt_adm (starts : Array Nat) (start : Nat) (code : List Char) :
    Adm (listingAt starts start code) := by
  unfold listingAt
  dsimp only
  split
  · intro r hr; simp at hr
  · intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [Md.Vocab.admits, vocabulary, Md.vocabulary]

private theorem docsRaws_adm (file text : String) (starts : Array Nat)
    (known : Option (Std.HashSet String)) : Adm (docsRaws file text starts known).1 := by
  unfold docsRaws
  rw [← Array.foldl_toList]
  refine foldl_adm _ (fun acc piece h => ?_) _ _ (by intro r hr; simp at hr)
  cases piece with
  | code start code => exact adm_append h (listingAt_adm _ _ _)
  | prose seg => exact adm_append h (proseRaws_adm _ _ _ _ _ _)
  | statement _ => exact h

private theorem paras_adm (file : String) (starts : Array Nat) (src : Array Char)
    (segs : List Seg) (showing : Showing) (declared : LeanProse.Declared) (place : LinkPlace)
    (folds : List ProofFold) (request : Span) (facts : Option LeanFacts.Facts) :
    ∀ p ∈ (statementsFor file starts src segs showing declared place folds
      (folds.map (foldRaws starts src)).toArray request facts).1 ++
      (folds.map (foldRaws starts src)).toArray, Adm p := by
  have hfold : ∀ p ∈ (folds.map (foldRaws starts src)).toArray, Adm p := by
    intro p hp
    simp only [List.mem_toArray, List.mem_map] at hp
    obtain ⟨fo, _, rfl⟩ := hp
    exact foldRaws_adm _ _ _
  intro p hp
  rcases Array.mem_append.mp hp with hp | hp
  · exact statementsFor_adm _ _ _ _ _ _ _ _ _ hfold _ _ p hp
  · exact hfold p hp

private theorem getD_adm {paras : Array (Array Raw)} (h : ∀ p ∈ paras, Adm p) (k : Nat) :
    Adm (paras.getD k #[]) := by
  simp only [Array.getD_eq_getD_getElem?]
  cases hk : paras[k]? with
  | none => intro r hr; simp at hr
  | some q => exact h q (Array.mem_of_getElem? hk)

private theorem adm_nil : Adm #[] := by intro r hr; simp at hr

private theorem adm_ite {c : Prop} [Decidable c] {a b : Array Raw} (ha : Adm a) (hb : Adm b) :
    Adm (if c then a else b) := by
  split
  · exact ha
  · exact hb

private theorem chosenRaws_adm (items : Array (Nat × Array Raw)) (h : ∀ x ∈ items, Adm x.2) :
    Adm (chosenRaws items) := by
  unfold chosenRaws
  have hm : ∀ x ∈ items.toList.mergeSort fun a b => decide (a.1 ≤ b.1), Adm x.2 :=
    fun x hx => h x (Array.mem_toList_iff.mp (List.mem_mergeSort.mp hx))
  generalize items.toList.mergeSort (fun a b => decide (a.1 ≤ b.1)) = l at hm
  suffices ∀ acc : Array Raw, Adm acc → Adm (l.foldl (fun acc x => acc ++ x.2) acc) from
    this #[] (by intro r hr; simp at hr)
  induction l with
  | nil => exact fun _ h => h
  | cons x rest ih =>
    intro acc ha
    exact ih (fun y hy => hm y (List.mem_cons_of_mem _ hy)) _
      (adm_append ha (hm x (List.mem_cons_self ..)))

/-- A Lean inclusion sets its file as the one input environment naming it, every raw inside which
lies in the reader's declared vocabulary. -/
public theorem includeLean_vocabulary_mem (file text : String) (showing : Showing)
    (facts : Option LeanFacts.Facts) (place : LinkPlace) (request : Span) (entry : String)
    (refs : Option Refs) :
    ∃ body, (includeLean file text showing facts place request entry refs).1 =
        #[.env (Parse.inputEnv file) body request.pos] ∧ ∀ r ∈ body, vocabulary.admits r = true := by
  unfold includeLean
  dsimp only
  split
  · exact ⟨_, rfl, docsRaws_adm _ _ _ _⟩
  · split
    · exact ⟨_, rfl, listingAt_adm _ _ _⟩
    · have hp := paras_adm
      split
      · refine ⟨_, rfl, piecesRaws_adm _ _ (fun s t => ?_) (hp _ _ _ _ _ _ _ _ _ _) _⟩
        split
        · exact listingAt_adm _ _ _
        · intro r hr; simp at hr
      · refine ⟨_, rfl, chosenRaws_adm _ ?_⟩
        intro x hx
        simp only [Array.mem_append, Array.mem_map] at hx
        rcases hx with ⟨d, _, rfl⟩ | ⟨fl, _, rfl⟩
        · exact adm_append (adm_append (adm_ite (getD_adm (hp _ _ _ _ _ _ _ _ _ _) _) adm_nil)
            (adm_ite (piecesRaws_adm _ _ (listingAt_adm _) (hp _ _ _ _ _ _ _ _ _ _) _) adm_nil))
            (adm_ite (getD_adm (hp _ _ _ _ _ _ _ _ _ _) _) adm_nil)
        · exact piecesRaws_adm _ _ (listingAt_adm _) (hp _ _ _ _ _ _ _ _ _ _) _

end LeanTex.Core.Code
