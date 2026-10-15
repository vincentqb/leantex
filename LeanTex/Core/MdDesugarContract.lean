module

public import LeanTex.Core.MdDesugar
import all LeanTex.Core.MdDesugar
import all LeanTex.Core.Parse

/-! # What markdown lowers into

The declared vocabulary of the markdown desugaring, and its block shape. -/

namespace LeanTex.Core.Md

open LeanTex.Core LeanTex.Core.Parse

/-- A slice of the surface AST's vocabulary. -/
public structure Vocab where
  /-- Ordinary controls, spelled as a document spells them. -/
  ctrls : List String
  /-- Names holding a space, which no source can spell, forge or redefine. -/
  bridged : List String
  envs : List String
  verbs : List String
  syms : List Char
  /-- Whether a formula is admitted, and the controls and characters its raws may hold. -/
  formulas : Bool := false
  mathCtrls : List String := []
  mathSyms : List Char := []

/-- natbib's citation commands and declarations a markdown citation or its metadata lowers to. -/
@[expose] public def citeCtrls : List String :=
  ["citep", "citet", "citeyearpar", "citeauthor", "citetext", "citealp", "citealt", "citeyear",
   "nocite", "@natbib"]

/-- The vocabulary markdown lowers into. -/
@[expose] public def vocabulary : Vocab where
  ctrls := ["emph", "textbf", "texttt", "href", "includegraphics", "item", "hypertarget", "\\",
    "toprule", "midrule", "bottomrule", "inputlean"] ++ citeCtrls
  bridged := ([Ir.HeadingLevel.title, .h1, .h2, .h3, .h4, .h5, .h6].map Parse.headingControl) ++
    [Parse.markdownBibControl]
  envs := ["quote", "itemize", "enumerate", Parse.markdownDisclosureEnv, Parse.markdownTableEnv]
  verbs := ["verbatim", "lstlisting"]
  syms := ['[', ']', '&', '@']

mutual

/-- Whether the vocabulary admits a raw, its children included. -/
@[expose] public def Vocab.admits (v : Vocab) : Raw → Bool
  | .word _ _ => true
  | .space => true
  | .par _ => true
  | .ctrl n _ => v.ctrls.contains n || v.bridged.contains n
  | .sym c _ => v.syms.contains c
  | .group body _ => v.admitsList body.toList
  | .env n body _ => v.envs.contains n && v.admitsList body.toList
  | .verb e _ _ => v.verbs.contains e
  | .math _ body _ => v.formulas && v.mathAdmitsList body.toList

@[expose] public def Vocab.admitsList (v : Vocab) : List Raw → Bool
  | [] => true
  | r :: rest => v.admits r && v.admitsList rest

/-- Whether a formula's raw is one the vocabulary's formulas may hold, its children included. -/
@[expose] public def Vocab.mathAdmits (v : Vocab) : Raw → Bool
  | .word _ _ => true
  | .space => true
  | .ctrl n _ => v.mathCtrls.contains n
  | .sym c _ => v.mathSyms.contains c
  | .group body _ => v.mathAdmitsList body.toList
  | .par _ | .math _ _ _ | .env _ _ _ | .verb _ _ _ => false

@[expose] public def Vocab.mathAdmitsList (v : Vocab) : List Raw → Bool
  | [] => true
  | r :: rest => v.mathAdmits r && v.mathAdmitsList rest

end

/-- Every raw of a sequence is admitted. -/
private def Adm (rs : Array Raw) : Prop := ∀ r ∈ rs, vocabulary.admits r = true

private theorem admitsList_of_adm : (l : List Raw) → (∀ r ∈ l, vocabulary.admits r = true) →
    vocabulary.admitsList l = true
  | [], _ => by simp [Vocab.admitsList]
  | r :: rest, h => by
    simp only [Vocab.admitsList, Bool.and_eq_true]
    exact ⟨h r (List.mem_cons_self ..), admitsList_of_adm rest fun x hx =>
      h x (List.mem_cons_of_mem _ hx)⟩

private theorem adm_group (body : Array Raw) (p : Pos) (h : Adm body) :
    vocabulary.admits (.group body p) = true := by
  simp only [Vocab.admits]
  exact admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)

private theorem adm_empty : Adm #[] := by simp [Adm]

private theorem adm_append {a b : Array Raw} (ha : Adm a) (hb : Adm b) : Adm (a ++ b) := by
  intro r hr
  rcases Array.mem_append.mp hr with hr | hr
  · exact ha r hr
  · exact hb r hr

private theorem adm_push {a : Array Raw} {r : Raw} (ha : Adm a) (hr : vocabulary.admits r = true) :
    Adm (a.push r) := by
  intro x hx
  rcases Array.mem_push.mp hx with hx | rfl
  · exact ha x hx
  · exact hr

private theorem adm_lit {l : List Raw} (h : ∀ r ∈ l, vocabulary.admits r = true) :
    Adm l.toArray := fun r hr => h r (by simpa using hr)

private theorem adm_text (s : String) (p : Pos) : Adm (textRaws s p) := by
  intro r hr
  rcases textRaws_covers s p r hr with rfl | ⟨t, q, rfl⟩ <;> rfl

private theorem ctrl_mem (n : String) (p : Pos) (h : n ∈ vocabulary.ctrls) :
    vocabulary.admits (.ctrl n p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr h)

private theorem bridged_mem (level : Ir.HeadingLevel) :
    Parse.headingControl level ∈ vocabulary.bridged :=
  List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨level, by cases level <;> simp, rfl⟩))

private theorem bibControl_mem (p : Pos) :
    vocabulary.admits (.ctrl Parse.markdownBibControl p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr (List.mem_append.mpr (Or.inr (by simp))))

private theorem cite_mem (n : String) (p : Pos) (h : n ∈ citeCtrls) :
    vocabulary.admits (.ctrl n p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr (List.mem_append.mpr (Or.inr h)))

private theorem heading_mem (level : Ir.HeadingLevel) (p : Pos) :
    vocabulary.admits (.ctrl (Parse.headingControl level) p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr (bridged_mem level))

private theorem adm_words (ws : Array String) (p : Pos) : Adm (ws.map (Raw.word · p)) := by
  intro r hr
  obtain ⟨w, _, rfl⟩ := Array.mem_map.mp hr
  rfl

private theorem citeOpts_adm (pre post : Array Raw) (p : Pos) (hpre : Adm pre) (hpost : Adm post) :
    Adm (citeOpts pre post p) := by
  have note : ∀ r : Array Raw, Adm r → Adm (#[.sym '[' p, .group r p, .sym ']' p] : Array Raw) :=
    fun r hr => adm_lit (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rfl
      · exact adm_group _ _ hr
      · rfl)
  unfold citeOpts
  split
  · exact adm_empty
  · split
    · exact note post hpost
    · exact adm_append (note pre hpre) (note post hpost)

private theorem citeCmdRaws_adm (cmd : String) (pre post : Array Raw) (keys : Array String) (p : Pos)
    (hc : cmd ∈ citeCtrls) (hpre : Adm pre) (hpost : Adm post) :
    Adm (citeCmdRaws cmd pre post keys p) := by
  unfold citeCmdRaws
  refine adm_append (adm_append (adm_lit ?_) (citeOpts_adm pre post p hpre hpost)) (adm_lit ?_)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact cite_mem cmd p hc
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact adm_group _ _ (adm_lit (by intro y hy; simp at hy; subst hy; rfl))

/-- Every citation of a group carries admitted notes. -/
private def NotesAdm (cs : List CiteRaws) : Prop := ∀ c ∈ cs, Adm c.pre ∧ Adm c.post

private theorem textCmd_mem (m : CiteMode) : textCmd m ∈ citeCtrls := by
  cases m <;> simp [textCmd, citeCtrls]

private theorem citeTextRaws_adm (items : List CiteRaws) (p : Pos) (h : NotesAdm items) :
    Adm (citeTextRaws items p) := by
  unfold citeTextRaws
  have fold : ∀ (l : List CiteRaws) (acc : Array Raw), Adm acc → NotesAdm l →
      Adm (l.foldl (init := acc) fun acc c =>
        (if acc.isEmpty then acc else acc ++ #[.word ";" p, .space]) ++
          citeCmdRaws (textCmd c.mode) c.pre c.post #[c.key] p) := by
    intro l
    induction l with
    | nil => intro acc ha _; simpa using ha
    | cons c rest ih =>
      intro acc ha hl
      simp only [List.foldl_cons]
      refine ih _ ?_ (fun d hd => hl d (List.mem_cons_of_mem _ hd))
      have hc := hl c (List.mem_cons_self ..)
      refine adm_append ?_ (citeCmdRaws_adm _ _ _ _ _ (textCmd_mem _) hc.1 hc.2)
      split
      · exact ha
      · exact adm_append ha (adm_lit (by simp [Vocab.admits]))
  exact adm_lit (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact cite_mem _ _ (by simp [citeCtrls])
    · exact adm_group _ _ (fold items #[] adm_empty h))

private theorem natbibRaws_adm (items : List CiteRaws) (p : Pos) (h : NotesAdm items) :
    Adm (natbibRaws items p) := by
  unfold natbibRaws
  split
  · exact adm_empty
  · next one =>
    have hc := h one (List.mem_singleton_self _)
    exact citeCmdRaws_adm _ _ _ _ _ (by split <;> simp [citeCtrls]) hc.1 hc.2
  · next first rest hne =>
    have h1 := h first (List.mem_cons_self ..)
    split
    · refine citeCmdRaws_adm _ _ _ _ _ (by simp [citeCtrls]) h1.1 ?_
      cases hl : rest.getLast? with
      | none => exact adm_empty
      | some last =>
        exact (h last (List.mem_cons_of_mem _ (List.mem_of_getLast? hl))).2
    · split
      · refine adm_append (adm_append (citeCmdRaws_adm _ _ _ _ _ (by simp [citeCtrls])
          adm_empty adm_empty) (adm_lit (by simp [Vocab.admits]))) (citeTextRaws_adm _ p ?_)
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact h1
        · exact h c (List.mem_cons_of_mem _ hc)
      · exact citeTextRaws_adm _ p h

private theorem dropSpaces_adm (l : List Raw) (h : ∀ r ∈ l, vocabulary.admits r = true) :
    ∀ r ∈ dropSpaces l, vocabulary.admits r = true :=
  fun r hr => h r ((List.dropWhile_sublist _).subset hr)

private theorem dropSeparator_adm (l : List Raw) (h : ∀ r ∈ l, vocabulary.admits r = true) :
    ∀ r ∈ dropSeparator l, vocabulary.admits r = true := by
  unfold dropSeparator
  split
  · next w p rest =>
    split
    · split
      · exact dropSpaces_adm rest fun r hr => h r (List.mem_cons_of_mem _ hr)
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rfl
        · exact h r (List.mem_cons_of_mem _ hr)
    · exact h
  · exact h

private theorem postNote_adm (rs : Array Raw) (h : Adm rs) : Adm (postNote rs) := by
  unfold postNote
  have hl := dropSeparator_adm _ (dropSpaces_adm rs.toList fun r hr => h r (Array.mem_toList_iff.mp hr))
  intro r hr
  obtain ⟨x, hx, hm⟩ := List.mem_filterMap.mp (by simpa using hr)
  unfold unbraceWord at hm
  split at hm
  · split at hm
    · cases hm
    · cases hm; rfl
  · cases hm; exact hl _ hx

private theorem selectorGuard_adm (rs : Array Raw) (p : Pos) : Adm (selectorGuard rs p) := by
  unfold selectorGuard
  split
  · split
    · intro r hr
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact adm_group _ _ adm_empty
    · exact adm_empty
  · exact adm_empty

mutual

private theorem inlRaws_adm (file : String) : (x : Inl) → Adm (inlRaws file x).1
  | .text s p => by
    simp only [inlRaws]
    exact adm_text s p
  | .code s p => by
    simp only [inlRaws]
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctrl_mem _ _ (by simp [vocabulary])
      · exact adm_group _ _ (adm_text s p))
  | .soft _ => by
    simp only [inlRaws]
    exact adm_lit (by simp [Vocab.admits])
  | .hard p => by
    simp only [inlRaws]
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ctrl_mem _ _ (by simp [vocabulary]))
  | .anchor key p => by
    simp only [inlRaws]
    split
    · next rs heq =>
      unfold anchorRaws? at heq
      split at heq
      · cases heq
        exact adm_lit (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ctrl_mem _ _ (by simp [vocabulary])
          · exact adm_group _ _ (adm_lit (by simp [Vocab.admits]))
          · exact adm_group _ _ adm_empty)
      · cases heq
    · exact adm_empty
  | .emph body p => by
    simp only [inlRaws]
    have h := inlListRaws_adm file body.toList #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctrl_mem _ _ (by simp [vocabulary])
      · exact adm_group _ _ h)
  | .strong body p => by
    simp only [inlRaws]
    have h := inlListRaws_adm file body.toList #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctrl_mem _ _ (by simp [vocabulary])
      · exact adm_group _ _ h)
  | .link dest title body p => by
    simp only [inlRaws]
    have h := inlListRaws_adm file body.toList #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ctrl_mem _ _ (by simp [vocabulary])
      · exact adm_group _ _ (adm_text dest p)
      · exact adm_group _ _ h)
  | .image dest title alt p => by
    simp only [inlRaws]
    split
    · exact adm_lit (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ctrl_mem _ _ (by simp [vocabulary])
        · exact adm_group _ _ (adm_text dest p))
    · refine adm_append (adm_append (adm_lit ?_) (adm_text _ p)) (adm_lit ?_)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ctrl_mem _ _ (by simp [vocabulary])
        · rfl
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rfl
        · exact adm_group _ _ (adm_text dest p)
  | .cite items p => by
    simp only [inlRaws]
    have hn := citeItemsRaws_adm file items.toList #[] #[] (by intro c hc; simp at hc)
    unfold citeGroupRaws
    split
    · exact natbibRaws_adm _ p (fun c hc => hn c (Array.mem_toList_iff.mp hc))
    · exact adm_text _ p

private theorem inlListRaws_adm (file : String) : (l : List Inl) → (out : Array Raw) →
    (ds : Array Diag) → Adm out → Adm (inlListRaws file out ds l).1
  | [], _, _, h => by simpa [inlListRaws] using h
  | x :: rest, out, ds, h => by
    simp only [inlListRaws]
    refine inlListRaws_adm file rest _ _ (adm_append (adm_append h ?_) (inlRaws_adm file x))
    split
    · exact selectorGuard_adm _ _
    · exact adm_empty

private theorem citeItemsRaws_adm (file : String) : (l : List CiteItem) → (out : Array CiteRaws) →
    (ds : Array Diag) → (∀ c ∈ out, Adm c.pre ∧ Adm c.post) →
    ∀ c ∈ (citeItemsRaws file out ds l).1, Adm c.pre ∧ Adm c.post
  | [], _, _, h => by simpa [citeItemsRaws] using h
  | .mk key mode pre post :: rest, out, ds, h => by
    simp only [citeItemsRaws]
    refine citeItemsRaws_adm file rest _ _ ?_
    intro c hc
    rcases Array.mem_push.mp hc with hc | rfl
    · exact h c hc
    · exact ⟨inlListRaws_adm file pre.toList #[] #[] adm_empty,
        postNote_adm _ (inlListRaws_adm file post.toList #[] #[] adm_empty)⟩

end

private theorem sym_mem (c : Char) (p : Pos) (h : c ∈ vocabulary.syms) :
    vocabulary.admits (.sym c p) = true := by
  simp only [Vocab.admits]
  exact List.contains_iff_mem.mpr h

private theorem laterCellsRaws_adm (file : String) (p : Pos) : (cells : List (Array Inl)) →
    (out : Array Raw) → (ds : Array Diag) → Adm out → Adm (laterCellsRaws file p out ds cells).1
  | [], _, _, h => by simpa [laterCellsRaws] using h
  | cell :: rest, out, ds, h => by
    have hc := inlListRaws_adm file cell.toList #[] #[] adm_empty
    unfold laterCellsRaws
    rcases hr : inlListRaws file #[] #[] cell.toList with ⟨rs, cds⟩
    rw [hr] at hc
    exact laterCellsRaws_adm file p rest _ _
      (adm_push (adm_push h (sym_mem '&' p (by simp [vocabulary]))) (adm_group rs p hc))

private theorem rowCellsRaws_adm (file : String) (p : Pos) :
    (cells : List (Array Inl)) → Adm (rowCellsRaws file p cells).1
  | [] => by simpa [rowCellsRaws] using adm_empty
  | cell :: rest => by
    have hc := inlListRaws_adm file cell.toList #[] #[] adm_empty
    unfold rowCellsRaws
    exact laterCellsRaws_adm file p rest _ _ (adm_lit (by
      intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact adm_group _ p hc))

private theorem rowRaws_adm (file : String) (row : Array (Array Inl)) (p : Pos) :
    Adm (rowRaws file row p).1 := by
  unfold rowRaws
  exact adm_push (rowCellsRaws_adm file p row.toList) (ctrl_mem _ _ (by simp [vocabulary]))

private theorem rowsRaws_adm (file : String) (p : Pos) : (rows : List (Array (Array Inl))) →
    (out : Array Raw) → (ds : Array Diag) → Adm out → Adm (rowsRaws file p out ds rows).1
  | [], _, _, h => by simpa [rowsRaws] using h
  | row :: rest, out, ds, h => by
    have hr := rowRaws_adm file row p
    unfold rowsRaws
    rcases hrow : rowRaws file row p with ⟨rs, rds⟩
    rw [hrow] at hr
    exact rowsRaws_adm file p rest _ _ (adm_append h hr)

private theorem tableRaws_adm (file : String) (aligns : Array TableAlign)
    (header : Array (Array Inl)) (rows : Array (Array (Array Inl))) (p : Pos) :
    Adm (tableRaws file aligns header rows p).1 := by
  have hh := rowRaws_adm file header p
  unfold tableRaws
  rcases hhr : rowRaws file header p with ⟨hr, hds⟩
  rw [hhr] at hh
  simp only at hh
  dsimp only
  have hhead : Adm (#[.group #[.sym '@' p, .group #[] p,
      .word (String.ofList (aligns.toList.map TableAlign.specLetter)) p, .sym '@' p, .group #[] p] p,
      .ctrl "toprule" p] : Array Raw) := adm_lit (by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact adm_group _ _ (adm_lit (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact sym_mem _ _ (by simp [vocabulary])
        · exact adm_group _ _ adm_empty
        · rfl
        · exact sym_mem _ _ (by simp [vocabulary])
        · exact adm_group _ _ adm_empty))
    · exact ctrl_mem _ _ (by simp [vocabulary]))
  have hbody := rowsRaws_adm file p rows.toList _ hds
    (adm_push (adm_append hhead hh) (ctrl_mem "midrule" p (by simp [vocabulary])))
  have hfull := adm_push hbody (ctrl_mem "bottomrule" p (by simp [vocabulary]))
  exact adm_lit (by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    simp only [Vocab.admits, Bool.and_eq_true]
    exact ⟨by simp [vocabulary],
      admitsList_of_adm _ fun x hx => hfull x (Array.mem_toList_iff.mp hx)⟩)

mutual

private theorem blkRaws_adm (file : String) (refs : Array Raw) (hrefs : Adm refs) :
    (b : Blk) → Adm (blkRaws file refs b).1
  | .para body p => by
    simp only [blkRaws]
    exact adm_push (inlListRaws_adm file body.toList #[] #[] adm_empty) rfl
  | .heading level body p => by
    simp only [blkRaws, Parse.headingRaws_contract]
    have h := inlListRaws_adm file body.toList #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact heading_mem level p
      · rfl
      · exact adm_group _ _ h)
  | .code info text p => by
    simp only [blkRaws]
    split
    · exact adm_lit (by simp [Vocab.admits, vocabulary])
    · split
      · exact adm_lit (by simp [Vocab.admits, vocabulary])
      · exact adm_lit (by simp [Vocab.admits, vocabulary])
  | .rule p => by
    simp only [blkRaws]
    exact adm_empty
  | .quote body p => by
    simp only [blkRaws]
    have h := blkListRaws_adm file refs hrefs body.toList #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true]
      exact ⟨by simp [vocabulary],
        admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)⟩)
  | .disclosure summary expanded body p => by
    simp only [blkRaws, disclosureRaws]
    have hs := inlListRaws_adm file summary.toList #[] #[] adm_empty
    have hb := blkListRaws_adm file refs hrefs body.toList #[] #[] adm_empty
    have ho : Adm (if expanded then #[.sym '[' p, .word "open" p, .sym ']' p] else #[]) := by
      cases expanded
      · exact adm_empty
      · refine adm_lit ?_
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sym_mem _ _ (by simp [vocabulary])
        · rfl
        · exact sym_mem _ _ (by simp [vocabulary])
    have hall := adm_append (adm_append ho (adm_lit (l := [.group _ p])
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          exact adm_group _ _ hs))) hb
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true]
      exact ⟨by simp [vocabulary],
        admitsList_of_adm _ fun r hr => hall r (Array.mem_toList_iff.mp hr)⟩)
  | .list ordered start tight items p => by
    simp only [blkRaws]
    have h := itemsRaws_adm file refs hrefs items.toList p #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true]
      exact ⟨by cases ordered <;> simp [vocabulary],
        admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)⟩)
  | .table aligns header rows p => by
    simp only [blkRaws]
    exact tableRaws_adm file aligns header rows p
  | .lean attrs p => by
    simp only [blkRaws]
    refine adm_append (adm_append (adm_lit ?_) ?_) (adm_lit ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rfl
      · simp [Vocab.admits, vocabulary]
    · split
      · exact adm_empty
      · refine adm_lit ?_
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sym_mem _ _ (by simp [vocabulary])
        · rfl
        · exact sym_mem _ _ (by simp [vocabulary])
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact adm_group _ _ (adm_lit (by intro r hr; simp at hr; subst hr; rfl))
  | .metadata _ _ => by
    simp only [blkRaws]
    exact adm_empty
  | .refs _ => by
    simp only [blkRaws]
    exact hrefs

private theorem blkListRaws_adm (file : String) (refs : Array Raw) (hrefs : Adm refs) :
    (l : List Blk) → (out : Array Raw) →
    (ds : Array Diag) → Adm out → Adm (blkListRaws file refs out ds l).1
  | [], _, _, h => by simpa [blkListRaws] using h
  | b :: rest, out, ds, h => by
    simp only [blkListRaws]
    exact blkListRaws_adm file refs hrefs rest _ _ (adm_append h (blkRaws_adm file refs hrefs b))

private theorem itemsRaws_adm (file : String) (refs : Array Raw) (hrefs : Adm refs) :
    (l : List (Array Blk)) → (p : Pos) →
    (out : Array Raw) → (ds : Array Diag) → Adm out → Adm (itemsRaws file refs out ds l p).1
  | [], _, _, _, h => by simpa [itemsRaws] using h
  | it :: rest, p, out, ds, h => by
    simp only [itemsRaws]
    exact itemsRaws_adm file refs hrefs rest p _ _ (adm_append (adm_append
      (adm_push h (ctrl_mem _ _ (by simp [vocabulary]))) (selectorGuard_adm _ _))
      (blkListRaws_adm file refs hrefs it.toList #[] #[] adm_empty))

end

private theorem opening_adm (m : MetaRead) : Adm m.opening := by
  unfold MetaRead.opening
  split
  · exact adm_empty
  · exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact cite_mem _ _ (by simp [citeCtrls])
      · exact adm_group _ _ (adm_words _ _))

private theorem nociteRaws_adm (m : MetaRead) : Adm m.nociteRaws := by
  unfold MetaRead.nociteRaws
  split
  · exact citeCmdRaws_adm _ _ _ _ _ (by simp [citeCtrls]) adm_empty adm_empty
  · exact adm_empty

private theorem prelude_adm (m : MetaRead) : Adm m.prelude := by
  unfold MetaRead.prelude
  split
  · exact adm_empty
  · exact adm_push (opening_adm m) rfl

private theorem list_adm (m : MetaRead) : Adm m.list := by
  unfold MetaRead.list
  split
  · exact adm_empty
  · exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rfl
      · exact bibControl_mem _
      · exact adm_group _ _ (adm_lit (by intro y hy; simp at hy; subst hy; rfl))
      · exact adm_group _ _ (adm_lit (by intro y hy; simp at hy; subst hy; rfl)))

private theorem titleRaws_adm (m : MetaRead) : Adm m.titleRaws := by
  unfold MetaRead.titleRaws
  split
  · next tp _ =>
    simp only [Parse.headingRaws_contract]
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact heading_mem _ _
      · rfl
      · exact adm_group _ _ (adm_text tp.1 tp.2))
  · exact adm_empty

private theorem tail_adm (m : MetaRead) (placed : Bool) : Adm (m.tail placed) := by
  unfold MetaRead.tail
  refine adm_append ?_ ?_
  · split
    · exact adm_empty
    · exact adm_push (nociteRaws_adm m) rfl
  · split
    · exact adm_empty
    · exact adm_append (titleRaws_adm m) (list_adm m)

public theorem desugar_vocabulary_mem (file input : String) (dialect : Dialect := .document)
    (role : Role := .document) :
    ∀ r ∈ (desugar file input dialect role).1, vocabulary.admits r = true := by
  unfold desugar
  exact adm_append (adm_append (prelude_adm _) (blkListRaws_adm file _ (list_adm _) _ #[] #[]
    adm_empty)) (tail_adm _ _)

public theorem read_desugar_exact (file input : String) : read file input = desugar file input := by
  unfold read
  rfl

public theorem readIncluded_desugar_exact (file input : String) :
    readIncluded file input = desugar file input .document .included := by
  unfold readIncluded
  rfl

/-- A raw that opens a block wherever it stands. -/
@[expose] public def BlockStart (r : Raw) : Prop :=
  (∃ p, r = .par p) ∨ (∃ n p, r = .ctrl n p ∧ n ∈ vocabulary.bridged) ∨
    (∃ e s p, r = .verb e s p ∧ e ∈ vocabulary.verbs) ∨
    (∃ n b p, r = .env n b p ∧ n ∈ vocabulary.envs)

private def Starts (rs : Array Raw) : Prop := rs = #[] ∨ ∃ r ∈ rs, BlockStart r

private theorem starts_append {a b : Array Raw} (ha : Starts a) (hb : Starts b) :
    Starts (a ++ b) := by
  rcases ha with rfl | ⟨r, hr, hs⟩
  · simpa using hb
  · exact Or.inr ⟨r, Array.mem_append.mpr (Or.inl hr), hs⟩

private theorem starts_single {r : Raw} (h : BlockStart r) : Starts #[r] :=
  Or.inr ⟨r, by simp, h⟩

private theorem verb_start (e s : String) (p : Pos) (h : e ∈ vocabulary.verbs) :
    BlockStart (.verb e s p) :=
  Or.inr (Or.inr (Or.inl ⟨e, s, p, rfl, h⟩))

private theorem env_start (n : String) (b : Array Raw) (p : Pos) (h : n ∈ vocabulary.envs) :
    BlockStart (.env n b p) :=
  Or.inr (Or.inr (Or.inr ⟨n, b, p, rfl, h⟩))

private theorem blkRaws_starts (file : String) (refs : Array Raw) (hrefs : Starts refs) (b : Blk) :
    Starts (blkRaws file refs b).1 := by
  cases b with
  | para body p =>
    simp only [blkRaws]
    exact Or.inr ⟨.par p, Array.mem_push_self, Or.inl ⟨p, rfl⟩⟩
  | heading level body p =>
    simp only [blkRaws, Parse.headingRaws_contract]
    exact Or.inr ⟨.ctrl (Parse.headingControl level) p, by simp,
      Or.inr (Or.inl ⟨_, p, rfl, bridged_mem level⟩)⟩
  | code info text p =>
    simp only [blkRaws]
    split
    · exact starts_single (verb_start _ _ _ (by simp [vocabulary]))
    · split
      · exact starts_single (verb_start _ _ _ (by simp [vocabulary]))
      · exact starts_single (verb_start _ _ _ (by simp [vocabulary]))
  | rule p =>
    simp only [blkRaws]
    exact Or.inl rfl
  | quote body p =>
    simp only [blkRaws]
    exact starts_single (env_start _ _ _ (by simp [vocabulary]))
  | disclosure summary expanded body p =>
    simp only [blkRaws, disclosureRaws]
    exact starts_single (env_start _ _ _ (by simp [vocabulary]))
  | list ordered start tight items p =>
    simp only [blkRaws]
    exact starts_single (env_start _ _ _ (by cases ordered <;> simp [vocabulary]))
  | table aligns header rows p =>
    simp only [blkRaws]
    obtain ⟨body, hbody, _⟩ := tableRaws_contract file aligns header rows p
    rw [hbody]
    exact starts_single (env_start _ _ _ (by simp [vocabulary]))
  | lean attrs p =>
    simp only [blkRaws]
    exact Or.inr ⟨.par p, by simp, Or.inl ⟨p, rfl⟩⟩
  | metadata fields p =>
    simp only [blkRaws]
    exact Or.inl rfl
  | refs p =>
    simp only [blkRaws]
    exact hrefs

private theorem blkListRaws_starts (file : String) (refs : Array Raw) (hrefs : Starts refs) :
    (l : List Blk) → (out : Array Raw) →
    (ds : Array Diag) → Starts out → Starts (blkListRaws file refs out ds l).1
  | [], _, _, h => by simpa [blkListRaws] using h
  | b :: rest, out, ds, h => by
    simp only [blkListRaws]
    exact blkListRaws_starts file refs hrefs rest _ _
      (starts_append h (blkRaws_starts file refs hrefs b))

private theorem list_starts (m : MetaRead) : Starts m.list := by
  unfold MetaRead.list
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨.par m.bibPos, by simp, Or.inl ⟨_, rfl⟩⟩

private theorem prelude_starts (m : MetaRead) : Starts m.prelude := by
  unfold MetaRead.prelude
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨.par m.bibPos, Array.mem_push_self, Or.inl ⟨_, rfl⟩⟩

private theorem tail_starts (m : MetaRead) (placed : Bool) : Starts (m.tail placed) := by
  unfold MetaRead.tail
  refine starts_append ?_ ?_
  · split
    · exact Or.inl rfl
    · exact Or.inr ⟨.par m.bibPos, Array.mem_push_self, Or.inl ⟨_, rfl⟩⟩
  · split
    · exact Or.inl rfl
    · next hc =>
      rcases list_starts m with he | ⟨r, hr, hs⟩
      · simp [he] at hc
      · exact Or.inr ⟨r, Array.mem_append.mpr (Or.inr hr), hs⟩

public theorem desugar_blockStart_contract (file input : String) (dialect : Dialect := .document)
    (role : Role := .document) (h : (desugar file input dialect role).1 ≠ #[]) :
    ∃ r ∈ (desugar file input dialect role).1, BlockStart r := by
  unfold desugar at h ⊢
  exact (starts_append (starts_append (prelude_starts _)
    (blkListRaws_starts file _ (list_starts _) _ #[] #[] (Or.inl rfl))) (tail_starts _ _)).resolve_left h

public theorem vocabulary_contract :
    (∀ n ∈ vocabulary.envs, Parse.inputEnvFile? n = none ∧ n ≠ Parse.scopeEnv ∧
      Parse.splitOpen? n = none ∧ Parse.splitClose? n = none) ∧
    (∀ n ∈ vocabulary.ctrls, ' ' ∉ n.toList) ∧
    (∀ n ∈ vocabulary.bridged, ((Parse.headingControl? n).isSome ∨ n = Parse.markdownBibControl) ∧
      ' ' ∈ n.toList) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    simp only [vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      simp [Parse.inputEnvFile?, Parse.scopeEnv, Parse.splitOpen?, Parse.splitClose?,
        Parse.markdownTableEnv, Parse.markdownDisclosureEnv]
  · intro n hn
    simp only [vocabulary, citeCtrls, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨level, _, rfl⟩ := List.mem_map.mp hn
      cases level <;> simp [Parse.headingControl, Parse.headingControl?]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn
      simp [Parse.markdownBibControl]

end LeanTex.Core.Md
