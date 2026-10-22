module

public import LeanTex.Core.MdDesugar
import all LeanTex.Core.MdDesugar
import all LeanTex.Core.Parse

/-! # What markdown lowers into

The declared vocabulary of the markdown desugaring, and its block shape. -/

namespace LeanTex.Core.Md

open LeanTex.Core LeanTex.Core.Parse

private theorem attrsOf?_map (p : Pos) : (l : List (String × String)) →
    attrsOf? (l.map fun (k, v) => Raw.group #[.word k p, .word v p] p) = some l
  | [] => rfl
  | (k, v) :: rest => by simp [attrsOf?, attrsOf?_map p rest]

/-- A division's raw reads back as exactly its request, whatever its attributes hold. -/
public theorem LeanDivision.ofRaw?_raw (d : LeanDivision) (p : Pos) :
    LeanDivision.ofRaw? (d.raw p) = some d := by
  rcases d with ⟨file, attrs⟩
  simp [ofRaw?, raw, attrsOf?_map]

/-- A slice of the surface AST's vocabulary. -/
public structure Vocab where
  /-- Ordinary controls, spelled as a document spells them. -/
  ctrls : List String
  /-- Names holding a space, which no source can spell, forge or redefine. -/
  bridged : List String
  envs : List String
  /-- Environments a reader asks the driver to fulfil before elaboration, unforgeable because their
  names hold a space. -/
  requests : List String := []
  verbs : List String
  syms : List Char
  /-- Whether a formula is admitted, and the controls and characters its raws may hold. -/
  formulas : Bool := false
  mathCtrls : List String := []
  mathSyms : List Char := []
  /-- Whether a formula may also hold every control the math model reads. -/
  mathKnown : Bool := false

/-- natbib's citation commands a markdown citation or its metadata lowers to. -/
@[expose] public def citeCtrls : List String :=
  ["citep", "citet", "citeyearpar", "citeauthor", "citetext", "citealp", "citealt", "citeyear",
   "nocite"]

/-- The title block's declarations a markdown front matter lowers to. -/
@[expose] public def titleCtrls : List String :=
  ["title", "subtitle", "author", "and", "institute", "date", "maketitle"]

/-- The vocabulary the elaborator reads markdown in. -/
@[expose] public def vocabulary : Vocab where
  ctrls := ["emph", "textbf", "texttt", "href", "includegraphics", "item", "hypertarget", "\\",
    "toprule", "midrule", "bottomrule", "footnote", "marginpar"] ++ citeCtrls ++ titleCtrls
  bridged := ([Ir.HeadingLevel.title, .h1, .h2, .h3, .h4, .h5, .h6].map Parse.headingControl) ++
    [Parse.markdownBibControl, Parse.citeSetupMark, Parse.markdownImageControl,
      Parse.markdownWebControl]
  envs := ["quote", "itemize", "enumerate", "abstract", Parse.markdownDisclosureEnv, Parse.markdownTableEnv]
  verbs := ["verbatim", "lstlisting"]
  syms := ['[', ']', '&', '@']
  formulas := true
  mathSyms := docMathSyms
  mathKnown := true

/-- The vocabulary a dialect lowers into: a document's with its Lean divisions' requests, a Lean
file's documentation with its formulas. -/
@[expose] public def vocabularyFor (dialect : Dialect) : Vocab :=
  { vocabulary with requests := if dialect.divisions then [leanDivisionEnv] else []
                    formulas := dialect.formulas }

mutual

/-- Whether the vocabulary admits a raw, its children included. -/
@[expose] public def Vocab.admits (v : Vocab) : Raw → Bool
  | .word _ _ => true
  | .space => true
  | .par _ => true
  | .ctrl n _ => v.ctrls.contains n || v.bridged.contains n
  | .sym c _ => v.syms.contains c
  | .group body _ => v.admitsList body.toList
  | .env n body _ => (v.envs.contains n || v.requests.contains n) && v.admitsList body.toList
  | .verb e _ _ => v.verbs.contains e
  | .math _ body _ => v.formulas && v.mathAdmitsList body.toList

@[expose] public def Vocab.admitsList (v : Vocab) : List Raw → Bool
  | [] => true
  | r :: rest => v.admits r && v.admitsList rest

/-- Whether a formula's raw is one the vocabulary's formulas may hold, its children included. -/
@[expose] public def Vocab.mathAdmits (v : Vocab) : Raw → Bool
  | .word _ _ => true
  | .space => true
  | .ctrl n _ => v.mathCtrls.contains n || (v.mathKnown && MathParse.knownCtrl n)
  | .sym c _ => v.mathSyms.contains c
  | .group body _ => v.mathAdmitsList body.toList
  | .par _ | .math _ _ _ | .env _ _ _ | .verb _ _ _ => false

@[expose] public def Vocab.mathAdmitsList (v : Vocab) : List Raw → Bool
  | [] => true
  | r :: rest => v.mathAdmits r && v.mathAdmitsList rest

end

mutual

private theorem mathAdmits_formulas (v : Vocab) (b : Bool) : (r : Raw) →
    { v with formulas := b }.mathAdmits r = v.mathAdmits r
  | .word _ _ | .space | .ctrl _ _ | .sym _ _ | .par _ | .math .. | .env .. | .verb .. => rfl
  | .group body _ => by
    simp only [Vocab.mathAdmits]
    exact mathAdmitsList_formulas v b body.toList

private theorem mathAdmitsList_formulas (v : Vocab) (b : Bool) : (l : List Raw) →
    { v with formulas := b }.mathAdmitsList l = v.mathAdmitsList l
  | [] => rfl
  | r :: rest => by
    simp only [Vocab.mathAdmitsList, mathAdmits_formulas v b r, mathAdmitsList_formulas v b rest]

end

mutual

/-- A vocabulary admitting formulas admits whatever it admits without them. -/
public theorem Vocab.admits_formulas (v : Vocab) : (r : Raw) → v.admits r = true →
    { v with formulas := true }.admits r = true
  | .word _ _, _ => rfl
  | .space, _ => rfl
  | .par _, _ => rfl
  | .ctrl _ _, h => h
  | .sym _ _, h => h
  | .verb _ _ _, h => h
  | .group body _, h => by
    simp only [Vocab.admits] at h ⊢
    exact Vocab.admitsList_formulas v body.toList h
  | .env _ body _, h => by
    simp only [Vocab.admits, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, Vocab.admitsList_formulas v body.toList h.2⟩
  | .math _ body _, h => by
    simp only [Vocab.admits, Bool.and_eq_true] at h ⊢
    exact ⟨trivial, (mathAdmitsList_formulas v true body.toList).trans h.2⟩

public theorem Vocab.admitsList_formulas (v : Vocab) : (l : List Raw) → v.admitsList l = true →
    { v with formulas := true }.admitsList l = true
  | [], _ => rfl
  | r :: rest, h => by
    simp only [Vocab.admitsList, Bool.and_eq_true] at h ⊢
    exact ⟨Vocab.admits_formulas v r h.1, Vocab.admitsList_formulas v rest h.2⟩

end

/-- Every raw of a sequence is admitted. -/
private def Adm (d : Dialect) (rs : Array Raw) : Prop := ∀ r ∈ rs, (vocabularyFor d).admits r = true

variable {d : Dialect}

private theorem admitsList_of_adm : (l : List Raw) → (∀ r ∈ l, (vocabularyFor d).admits r = true) →
    (vocabularyFor d).admitsList l = true
  | [], _ => by simp [Vocab.admitsList]
  | r :: rest, h => by
    simp only [Vocab.admitsList, Bool.and_eq_true]
    exact ⟨h r (List.mem_cons_self ..), admitsList_of_adm rest fun x hx =>
      h x (List.mem_cons_of_mem _ hx)⟩

private theorem adm_group (body : Array Raw) (p : Pos) (h : Adm d body) :
    (vocabularyFor d).admits (.group body p) = true := by
  simp only [Vocab.admits]
  exact admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)

private theorem adm_empty : Adm d #[] := by simp [Adm]

private theorem adm_append {a b : Array Raw} (ha : Adm d a) (hb : Adm d b) : Adm d (a ++ b) := by
  intro r hr
  rcases Array.mem_append.mp hr with hr | hr
  · exact ha r hr
  · exact hb r hr

private theorem adm_push {a : Array Raw} {r : Raw} (ha : Adm d a) (hr : (vocabularyFor d).admits r = true) :
    Adm d (a.push r) := by
  intro x hx
  rcases Array.mem_push.mp hx with hx | rfl
  · exact ha x hx
  · exact hr

private theorem adm_lit {l : List Raw} (h : ∀ r ∈ l, (vocabularyFor d).admits r = true) :
    Adm d l.toArray := fun r hr => h r (by simpa using hr)

private theorem adm_text (s : String) (p : Pos) : Adm d (textRaws s p) := by
  intro r hr
  rcases textRaws_covers s p r hr with rfl | ⟨t, q, rfl⟩ <;> rfl

mutual

private theorem docMath_admits : (r : Raw) → docMathOk r = true →
    (vocabularyFor d).mathAdmits r = true
  | .word _ _, _ => rfl
  | .space, _ => rfl
  | .ctrl n _, h => by
    simp only [docMathOk] at h
    simp [Vocab.mathAdmits, vocabularyFor, vocabulary, h]
  | .sym c _, h => by
    simp only [docMathOk] at h
    simpa [Vocab.mathAdmits, vocabularyFor, vocabulary] using h
  | .group body _, h => by
    simp only [docMathOk] at h
    simp only [Vocab.mathAdmits]
    exact docMathList_admits body.toList h
  | .par _, h | .math .., h | .env .., h | .verb .., h => by simp [docMathOk] at h

private theorem docMathList_admits : (l : List Raw) → docMathOkList l = true →
    (vocabularyFor d).mathAdmitsList l = true
  | [], _ => rfl
  | r :: rest, h => by
    simp only [docMathOkList, Bool.and_eq_true] at h
    simp only [Vocab.mathAdmitsList, Bool.and_eq_true]
    exact ⟨docMath_admits r h.1, docMathList_admits rest h.2⟩

end

private theorem mathAdmitsList_append_one (v : Vocab) : (a : List Raw) → (r : Raw) →
    v.mathAdmitsList (a ++ [r]) = (v.mathAdmitsList a && v.mathAdmits r)
  | [], r => by simp [Vocab.mathAdmitsList]
  | x :: rest, r => by
    simp only [List.cons_append, Vocab.mathAdmitsList, mathAdmitsList_append_one v rest r,
      Bool.and_assoc]

mutual

private theorem mathAdmits_mapPos (v : Vocab) (f : Pos → Pos) : (r : Raw) →
    v.mathAdmits (mapPos f r) = v.mathAdmits r
  | .word _ _ | .space | .ctrl _ _ | .sym _ _ | .par _ | .math .. | .env .. | .verb .. => by
    simp only [mapPos, Vocab.mathAdmits]
  | .group body _ => by
    simp only [mapPos, Vocab.mathAdmits]
    rw [mathAdmitsList_mapPos v f #[] body.toList]
    rfl

private theorem mathAdmitsList_mapPos (v : Vocab) (f : Pos → Pos) (acc : Array Raw) :
    (l : List Raw) → v.mathAdmitsList (mapPosList f acc l).toList =
      (v.mathAdmitsList acc.toList && v.mathAdmitsList l)
  | [] => by simp [mapPosList, Vocab.mathAdmitsList]
  | r :: rest => by
    simp only [mapPosList]
    rw [mathAdmitsList_mapPos v f (acc.push (mapPos f r)) rest]
    simp only [Array.toList_push]
    rw [mathAdmitsList_append_one v acc.toList (mapPos f r), mathAdmits_mapPos v f r]
    simp only [Vocab.mathAdmitsList, Bool.and_assoc]

end

private theorem docMathAt_admits {display : Bool} {p : Pos} {raws : Array Raw} {clean : Bool}
    {r : Raw} (hf : d.formulas = true) (h : docMathAt display p raws clean = some r) :
    (vocabularyFor d).admits r = true := by
  unfold docMathAt at h
  split at h
  · split at h
    · rename_i hok
      cases h
      simp only [Bool.and_eq_true] at hok
      simp only [Vocab.admits, Bool.and_eq_true]
      refine ⟨by simp [vocabularyFor, hf], ?_⟩
      rw [mathAdmitsList_mapPos]
      simp only [Vocab.mathAdmitsList, Bool.true_and]
      exact docMathList_admits _ hok.2
    · cases h
  · cases h

private theorem docMathRaw_admits {display : Bool} {src : String} {p : Pos} {r : Raw}
    (hf : d.formulas = true) (h : docMathRaw display src p = some r) :
    (vocabularyFor d).admits r = true := by
  unfold docMathRaw at h
  exact docMathAt_admits hf h

private theorem ctrl_mem (n : String) (p : Pos) (h : n ∈ vocabulary.ctrls) :
    (vocabularyFor d).admits (.ctrl n p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr h)

private theorem bridged_mem (level : Ir.HeadingLevel) :
    Parse.headingControl level ∈ vocabulary.bridged :=
  List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨level, by cases level <;> simp, rfl⟩))

private theorem bibControl_mem (p : Pos) :
    (vocabularyFor d).admits (.ctrl Parse.markdownBibControl p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr (List.mem_append.mpr (Or.inr (by simp))))

private theorem cite_mem (n : String) (p : Pos) (h : n ∈ citeCtrls) :
    (vocabularyFor d).admits (.ctrl n p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inl (List.contains_iff_mem.mpr (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))))

private theorem heading_mem (level : Ir.HeadingLevel) (p : Pos) :
    (vocabularyFor d).admits (.ctrl (Parse.headingControl level) p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr (bridged_mem level))

private theorem adm_words (ws : Array String) (p : Pos) : Adm d (ws.map (Raw.word · p)) := by
  intro r hr
  obtain ⟨w, _, rfl⟩ := Array.mem_map.mp hr
  rfl

private theorem citeOpts_adm (pre post : Array Raw) (p : Pos) (hpre : Adm d pre) (hpost : Adm d post) :
    Adm d (citeOpts pre post p) := by
  have note : ∀ r : Array Raw, Adm d r → Adm d (#[.sym '[' p, .group r p, .sym ']' p] : Array Raw) :=
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
    (hc : cmd ∈ citeCtrls) (hpre : Adm d pre) (hpost : Adm d post) :
    Adm d (citeCmdRaws cmd pre post keys p) := by
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
private def NotesAdm (d : Dialect) (cs : List CiteRaws) : Prop := ∀ c ∈ cs, Adm d c.pre ∧ Adm d c.post

private theorem textCmd_mem (m : CiteMode) : textCmd m ∈ citeCtrls := by
  cases m <;> simp [textCmd, citeCtrls]

private theorem workText_adm (c : CiteRaws) (p : Pos) (hc : Adm d c.pre ∧ Adm d c.post) :
    Adm d (workText c p) := by
  unfold workText
  refine adm_append (adm_append ?_ (adm_lit (by simp [Vocab.admits]))) ?_
  · split
    · exact adm_empty
    · exact adm_push hc.1 rfl
  · split
    · exact adm_empty
    · exact adm_append (adm_lit (by simp [Vocab.admits])) hc.2

private theorem citeTextRaws_adm (items : List CiteRaws) (p : Pos) (h : NotesAdm d items) :
    Adm d (citeTextRaws items p) := by
  unfold citeTextRaws
  have fold : ∀ (l : List CiteRaws) (acc : Array Raw), Adm d acc → NotesAdm d l →
      Adm d (l.foldl (init := acc) fun acc c =>
        (if acc.isEmpty then acc else acc ++ #[.word ";" p, .space]) ++
          (if keyCrosses c.key then citeCmdRaws (textCmd c.mode) c.pre c.post #[c.key] p
           else workText c p)) := by
    intro l
    induction l with
    | nil => intro acc ha _; simpa using ha
    | cons c rest ih =>
      intro acc ha hl
      simp only [List.foldl_cons]
      refine ih _ ?_ (fun d hd => hl d (List.mem_cons_of_mem _ hd))
      have hc := hl c (List.mem_cons_self ..)
      refine adm_append ?_ ?_
      · split
        · exact ha
        · exact adm_append ha (adm_lit (by simp [Vocab.admits]))
      · split
        · exact citeCmdRaws_adm _ _ _ _ _ (textCmd_mem _) hc.1 hc.2
        · exact workText_adm c p hc
  exact adm_lit (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact cite_mem _ _ (by simp [citeCtrls])
    · exact adm_group _ _ (fold items #[] adm_empty h))

private theorem natbibRaws_adm (items : List CiteRaws) (p : Pos) (h : NotesAdm d items) :
    Adm d (natbibRaws items p) := by
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

private theorem citeWorksRaws_adm (file : String) (items : Array CiteRaws) (p : Pos)
    (hn : ∀ c ∈ items, Adm d c.pre ∧ Adm d c.post) : Adm d (citeWorksRaws file items p).1 := by
  have hl : NotesAdm d items.toList := fun c hc => hn c (Array.mem_toList_iff.mp hc)
  unfold citeWorksRaws
  split
  · exact adm_empty
  · dsimp only
    split
    · exact natbibRaws_adm _ p hl
    · split
      · next first hfirst =>
        have h1 : Adm d first.pre ∧ Adm d first.post := hn first (Array.mem_of_getElem? hfirst)
        split
        · split
          · refine adm_append (adm_append (citeCmdRaws_adm _ _ _ _ _ (by simp [citeCtrls])
              adm_empty adm_empty) (adm_lit (by simp [Vocab.admits]))) (citeTextRaws_adm _ p ?_)
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact h1
            · exact hl c (List.mem_of_mem_drop hc)
          · exact adm_text _ p
        · exact citeTextRaws_adm _ p hl
      · exact adm_empty

private theorem dropSpaces_adm (l : List Raw) (h : ∀ r ∈ l, (vocabularyFor d).admits r = true) :
    ∀ r ∈ dropSpaces l, (vocabularyFor d).admits r = true :=
  fun r hr => h r ((List.dropWhile_sublist _).subset hr)

private theorem dropSeparator_adm (l : List Raw) (h : ∀ r ∈ l, (vocabularyFor d).admits r = true) :
    ∀ r ∈ dropSeparator l, (vocabularyFor d).admits r = true := by
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

private theorem postNote_adm (rs : Array Raw) (h : Adm d rs) : Adm d (postNote rs) := by
  unfold postNote
  have hl := dropSeparator_adm (d := d) _ (dropSpaces_adm rs.toList fun r hr => h r (Array.mem_toList_iff.mp hr))
  intro r hr
  obtain ⟨x, hx, hm⟩ := List.mem_filterMap.mp (by simpa using hr)
  unfold unbraceWord at hm
  split at hm
  · split at hm
    · cases hm
    · cases hm; rfl
  · cases hm; exact hl _ hx

private theorem selectorGuard_adm (rs : Array Raw) (p : Pos) : Adm d (selectorGuard rs p) := by
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

private theorem inlRaws_adm (file : String) : (x : Inl) → Adm d (inlRaws file d x).1
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
  | .math display src p => by
    simp only [inlRaws]
    split
    · next r heq =>
      intro x hx
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      split at heq
      · next hf => exact docMathRaw_admits hf heq
      · cases heq
    · exact adm_lit (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ctrl_mem _ _ (by simp [vocabulary])
        · exact adm_group _ _ (adm_text _ p))
  | .note _ body p => by
    simp only [inlRaws]
    have h := inlListRaws_adm file body.toList #[] #[] (adm_empty (d := d))
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctrl_mem _ _ (by simp [vocabulary])
      · exact adm_group _ _ h)
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
    have h := inlListRaws_adm file body.toList #[] #[] (adm_empty (d := d))
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctrl_mem _ _ (by simp [vocabulary])
      · exact adm_group _ _ h)
  | .strong body p => by
    simp only [inlRaws]
    have h := inlListRaws_adm file body.toList #[] #[] (adm_empty (d := d))
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctrl_mem _ _ (by simp [vocabulary])
      · exact adm_group _ _ h)
  | .link dest title body p => by
    simp only [inlRaws]
    have h := inlListRaws_adm file body.toList #[] #[] (adm_empty (d := d))
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
    · have h := inlListRaws_adm file alt.toList #[] #[] (adm_empty (d := d))
      exact adm_lit (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · simp only [Vocab.admits, Bool.or_eq_true]
          exact Or.inr (List.contains_iff_mem.mpr (List.mem_append.mpr (Or.inr (by simp))))
        · exact adm_group _ _ h
        · exact adm_group _ _ (adm_text dest p))
    split
    · exact adm_lit (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ctrl_mem _ _ (by simp [vocabulary])
        · exact adm_group _ _ (adm_text dest p))
    · exact adm_lit (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ctrl_mem _ _ (by simp [vocabulary])
        · rfl
        · rfl
        · exact adm_group _ _ (adm_text _ p)
        · rfl
        · exact adm_group _ _ (adm_text dest p))
  | .citeText key body p => by
    simp only [inlRaws]
    have h := inlListRaws_adm file body.toList #[] #[] (adm_empty (d := d))
    refine adm_append (adm_lit ?_) (citeCmdRaws_adm _ _ _ _ _ (by simp [citeCtrls]) adm_empty adm_empty)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ctrl_mem _ _ (by simp [vocabulary])
    · exact adm_group _ _ (adm_text _ p)
    · exact adm_group _ _ h
  | .cite items p => by
    simp only [inlRaws]
    have hn := citeItemsRaws_adm file items.toList #[] #[] (by intro c hc; simp at hc)
    unfold citeGroupRaws
    dsimp only
    exact citeWorksRaws_adm file _ p fun c hc => hn c (Array.mem_filter.mp hc).1

private theorem closeLeading_adm (rs : Array Raw) (h : Adm d rs) : Adm d (closeLeading rs) := by
  unfold closeLeading
  split
  · rename_i w p rest hl
    intro r hr
    simp only [List.mem_toArray, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rfl
    · exact h r (by rw [← Array.mem_toList_iff, hl]; exact List.mem_cons_of_mem _ hr)
  · exact h

private theorem inlListRaws_adm (file : String) : (l : List Inl) → (out : Array Raw) →
    (ds : Array Diag) → Adm d out → Adm d (inlListRaws file d out ds l).1
  | [], _, _, h => by simpa [inlListRaws] using h
  | x :: rest, out, ds, h => by
    simp only [inlListRaws]
    have closed : ∀ (b : Bool) (rs : Array Raw), Adm d rs →
        Adm d (if b = true then closeLeading rs else rs) := by
      intro b rs hrs
      cases b
      · exact hrs
      · exact closeLeading_adm rs hrs
    refine inlListRaws_adm file rest _ _
      (adm_append (adm_append h ?_) (closed _ _ (inlRaws_adm file x)))
    split
    · exact selectorGuard_adm _ _
    · exact adm_empty

private theorem citeItemsRaws_adm (file : String) : (l : List CiteItem) → (out : Array CiteRaws) →
    (ds : Array Diag) → (∀ c ∈ out, Adm d c.pre ∧ Adm d c.post) →
    ∀ c ∈ (citeItemsRaws file d out ds l).1, Adm d c.pre ∧ Adm d c.post
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
    (vocabularyFor d).admits (.sym c p) = true := by
  simp only [Vocab.admits]
  exact List.contains_iff_mem.mpr h

private theorem laterCellsRaws_adm (file : String) (p : Pos) : (cells : List (Array Inl)) →
    (out : Array Raw) → (ds : Array Diag) → Adm d out →
      Adm d (laterCellsRaws (cellRaws file d) p out ds cells).1
  | [], _, _, h => by simpa [laterCellsRaws] using h
  | cell :: rest, out, ds, h => by
    have hc := inlListRaws_adm file cell.toList #[] #[] (adm_empty (d := d))
    unfold laterCellsRaws cellRaws
    rcases hr : inlListRaws file d #[] #[] cell.toList with ⟨rs, cds⟩
    rw [hr] at hc
    exact laterCellsRaws_adm file p rest _ _
      (adm_push (adm_push h (sym_mem '&' p (by simp [vocabulary]))) (adm_group rs p hc))

private theorem rowCellsRaws_adm (file : String) (p : Pos) :
    (cells : List (Array Inl)) → Adm d (rowCellsRaws (cellRaws file d) p cells).1
  | [] => by simpa [rowCellsRaws] using adm_empty
  | cell :: rest => by
    have hc := inlListRaws_adm file cell.toList #[] #[] (adm_empty (d := d))
    unfold rowCellsRaws cellRaws
    exact laterCellsRaws_adm file p rest _ _ (adm_lit (by
      intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact adm_group _ p hc))

private theorem rowRaws_adm (file : String) (row : Array (Array Inl)) (p : Pos) :
    Adm d (rowRaws (cellRaws file d) row p).1 := by
  unfold rowRaws
  exact adm_push (rowCellsRaws_adm file p row.toList) (ctrl_mem _ _ (by simp [vocabulary]))

private theorem rowsRaws_adm (file : String) (p : Pos) : (rows : List (Array (Array Inl))) →
    (out : Array Raw) → (ds : Array Diag) → Adm d out →
      Adm d (rowsRaws (cellRaws file d) p out ds rows).1
  | [], _, _, h => by simpa [rowsRaws] using h
  | row :: rest, out, ds, h => by
    have hr := rowRaws_adm (d := d) file row p
    unfold rowsRaws
    rcases hrow : rowRaws (cellRaws file d) row p with ⟨rs, rds⟩
    rw [hrow] at hr
    exact rowsRaws_adm file p rest _ _ (adm_append h hr)

private theorem tableRaws_adm (file : String) (aligns : Array TableAlign)
    (header : Array (Array Inl)) (rows : Array (Array (Array Inl))) (p : Pos) :
    Adm d (tableRaws (cellRaws file d) aligns header rows p).1 := by
  have hh := rowRaws_adm (d := d) file header p
  unfold tableRaws
  rcases hhr : rowRaws (cellRaws file d) header p with ⟨hr, hds⟩
  rw [hhr] at hh
  simp only at hh
  dsimp only
  have hhead : Adm d (#[.group #[.sym '@' p, .group #[] p,
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
  have hbody := rowsRaws_adm (d := d) file p rows.toList _ hds
    (adm_push (adm_append hhead hh) (ctrl_mem "midrule" p (by simp [vocabulary])))
  have hfull := adm_push hbody (ctrl_mem "bottomrule" p (by simp [vocabulary]))
  exact adm_lit (by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    simp only [Vocab.admits, Bool.and_eq_true]
    exact ⟨by simp [vocabularyFor, vocabulary],
      admitsList_of_adm _ fun x hx => hfull x (Array.mem_toList_iff.mp hx)⟩)

private theorem division_adm (q : LeanDivision) (p : Pos) :
    (vocabularyFor .document).admits (q.raw p) = true := by
  have hattrs : Adm .document (q.attrs.map fun (k, v) => Raw.group #[.word k p, .word v p] p) := by
    intro r hr
    obtain ⟨⟨k, v⟩, _, rfl⟩ := Array.mem_map.mp hr
    exact adm_group _ _ (adm_lit (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl))
  have hbody : Adm .document #[Raw.group #[.word q.file p] p,
      .group (q.attrs.map fun (k, v) => Raw.group #[.word k p, .word v p] p) p] := adm_lit (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact adm_group _ _ (adm_lit (by intro x hx; simp at hx; subst hx; rfl))
    · exact adm_group _ _ hattrs)
  simp only [LeanDivision.raw, Vocab.admits, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨Or.inr (by simp [vocabularyFor, Dialect.divisions]),
    admitsList_of_adm _ fun r hr => hbody r (by simpa using hr)⟩

private theorem asideLines_adm (file : String) (p : Pos) : (l : List (Array Inl)) →
    (out : Array Raw) → (ds : Array Diag) → Adm d out → Adm d (asideLines file d out ds p l).1
  | [], _, _, h => by simpa [asideLines] using h
  | body :: rest, out, ds, h => by
    simp only [asideLines]
    apply asideLines_adm file p rest
    have hb := inlListRaws_adm file body.toList #[] #[] (adm_empty (d := d))
    split
    · exact hb
    · exact adm_append (adm_push h (ctrl_mem _ _ (by simp [vocabulary]))) hb

mutual

private theorem blkRaws_adm (file : String) (refs : Array Raw) (hrefs : Adm d refs) :
    (b : Blk) → Adm d (blkRaws file refs d b).1
  | .para body p => by
    simp only [blkRaws]
    exact adm_push (inlListRaws_adm file body.toList #[] #[] adm_empty) rfl
  | .heading level body p => by
    simp only [blkRaws, Parse.headingRaws_contract]
    have h := inlListRaws_adm file body.toList #[] #[] (adm_empty (d := d))
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
    · exact adm_lit (by simp [Vocab.admits, vocabularyFor, vocabulary])
    · split
      · exact adm_lit (by simp [Vocab.admits, vocabularyFor, vocabulary])
      · exact adm_lit (by simp [Vocab.admits, vocabularyFor, vocabulary])
  | .rule p => by
    simp only [blkRaws]
    exact adm_empty
  | .quote body p => by
    simp only [blkRaws]
    have h := blkListRaws_adm file refs hrefs body.toList #[] #[] (adm_empty (d := d))
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true]
      exact ⟨by simp [vocabularyFor, vocabulary],
        admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)⟩)
  | .aside body p => by
    simp only [blkRaws]
    split
    · rename_i paras _
      have h := asideLines_adm file p paras #[] #[] (adm_empty (d := d))
      exact adm_lit (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rfl
        · exact ctrl_mem _ _ (by simp [vocabulary])
        · exact adm_group _ _ h
        · rfl)
    · exact adm_append (adm_lit (by simp [Vocab.admits]))
        (blkListRaws_adm file refs hrefs body.toList #[] #[] (adm_empty (d := d)))
  | .disclosure summary expanded body p => by
    simp only [blkRaws, disclosureRaws]
    have hs := inlListRaws_adm file summary.toList #[] #[] (adm_empty (d := d))
    have hb := blkListRaws_adm file refs hrefs body.toList #[] #[] (adm_empty (d := d))
    have ho : Adm d (if expanded then #[.sym '[' p, .word "open" p, .sym ']' p] else #[]) := by
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
      exact ⟨by simp [vocabularyFor, vocabulary],
        admitsList_of_adm _ fun r hr => hall r (Array.mem_toList_iff.mp hr)⟩)
  | .list ordered start tight items p => by
    simp only [blkRaws]
    have h := itemsRaws_adm file refs hrefs items.toList p #[] #[] (adm_empty (d := d))
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true]
      exact ⟨by cases ordered <;> simp [vocabularyFor, vocabulary],
        admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)⟩)
  | .table aligns header rows p => by
    simp only [blkRaws]
    exact tableRaws_adm file aligns header rows p
  | .lean attrs p => by
    simp only [blkRaws]
    cases d with
    | docstring => exact adm_empty
    | lean => exact adm_empty
    | document => exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rfl
      · exact division_adm _ p)
  | .metadata _ _ => by
    simp only [blkRaws]
    exact adm_empty
  | .refs _ => by
    simp only [blkRaws]
    exact hrefs
  | .note _ _ _ => by
    simp only [blkRaws]
    exact adm_empty

private theorem blkListRaws_adm (file : String) (refs : Array Raw) (hrefs : Adm d refs) :
    (l : List Blk) → (out : Array Raw) →
    (ds : Array Diag) → Adm d out → Adm d (blkListRaws file refs d out ds l).1
  | [], _, _, h => by simpa [blkListRaws] using h
  | b :: rest, out, ds, h => by
    simp only [blkListRaws]
    exact blkListRaws_adm file refs hrefs rest _ _ (adm_append h (blkRaws_adm file refs hrefs b))

private theorem itemsRaws_adm (file : String) (refs : Array Raw) (hrefs : Adm d refs) :
    (l : List (Array Blk)) → (p : Pos) →
    (out : Array Raw) → (ds : Array Diag) → Adm d out → Adm d (itemsRaws file refs d out ds l p).1
  | [], _, _, _, h => by simpa [itemsRaws] using h
  | it :: rest, p, out, ds, h => by
    simp only [itemsRaws]
    exact itemsRaws_adm file refs hrefs rest p _ _ (adm_append (adm_append
      (adm_push h (ctrl_mem _ _ (by simp [vocabulary]))) (selectorGuard_adm _ _))
      (blkListRaws_adm file refs hrefs it.toList #[] #[] adm_empty))

end

private theorem opening_adm (m : MetaRead) : Adm d m.opening := by
  unfold MetaRead.opening Parse.citeSetupRaws
  split
  · exact adm_empty
  · exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Vocab.admits, Bool.or_eq_true]
        exact Or.inr (List.contains_iff_mem.mpr (List.mem_append.mpr (Or.inr (by simp))))
      · exact adm_group _ _ fun r hr => by
          obtain ⟨d, _, rfl⟩ := Array.mem_map.mp hr
          rfl)

private theorem nociteRaws_adm (m : MetaRead) : Adm d m.nociteRaws := by
  unfold MetaRead.nociteRaws
  split
  · exact citeCmdRaws_adm _ _ _ _ _ (by simp [citeCtrls]) adm_empty adm_empty
  · exact adm_empty

private theorem layout_adm (m : MetaRead) : Adm d m.layout := by
  unfold MetaRead.layout
  split
  · exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Vocab.admits, Bool.or_eq_true]
        exact Or.inr (List.contains_iff_mem.mpr (by simp [vocabularyFor, vocabulary]))
      · exact adm_group _ _ fun r hr => by simp at hr; subst hr; rfl)
  · exact adm_empty

private theorem prelude_adm (m : MetaRead) : Adm d m.prelude := by
  unfold MetaRead.prelude
  split
  · exact adm_empty
  · exact adm_push (opening_adm m) rfl

private theorem list_adm (m : MetaRead) (cited : Bool) : Adm d (m.list cited) := by
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

private theorem titleRaws_adm (file : String) (m : MetaRead) : Adm d (m.titleRaws file d) := by
  unfold MetaRead.titleRaws
  split
  · next title q _ =>
    simp only [Parse.headingRaws_contract]
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact heading_mem _ _
      · rfl
      · exact adm_group _ _ (inlListRaws_adm file title.toList #[] #[] adm_empty))
  · exact adm_empty

private theorem tail_adm (file : String) (m : MetaRead) (cited placed : Bool) :
    Adm d (m.tail file d cited placed) := by
  unfold MetaRead.tail
  refine adm_append ?_ ?_
  · split
    · exact adm_empty
    · exact adm_push (nociteRaws_adm m) rfl
  · split
    · exact adm_empty
    · exact adm_append (titleRaws_adm file m) (list_adm m cited)

private theorem frontText_adm (file : String) (q : Pos) (t : String) :
    Adm d (frontText file d q t).1 := by
  unfold frontText
  exact inlListRaws_adm file _ #[] #[] adm_empty

private theorem frontJoin_adm (file : String) (q : Pos) (sep : Array Raw) (hs : Adm d sep)
    (l : List String) : Adm d (frontJoin file d q sep l) := by
  unfold frontJoin
  suffices h : ∀ (xs : List (String × Nat)) (init : Array Raw), Adm d init →
      Adm d (xs.foldl (fun out (p : String × Nat) =>
        (if p.2 == 0 then out else out.append sep).append (frontText file d q p.1).1) init) from
    h _ _ adm_empty
  intro xs
  induction xs with
  | nil => intro init h; exact h
  | cons x _ ih =>
    intro init h
    apply ih
    dsimp only
    split
    · exact adm_append h (frontText_adm file q x.1)
    · exact adm_append (adm_append h hs) (frontText_adm file q x.1)

private theorem frontDecl_adm (name : String) (rs : Array Raw) (q : Pos) (hn : name ∈ titleCtrls)
    (h : Adm d rs) : Adm d (frontDecl name rs q) := by
  unfold frontDecl
  exact adm_lit (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Vocab.admits, Bool.or_eq_true]
      exact Or.inl (List.contains_iff_mem.mpr (by simp [vocabularyFor, vocabulary]; simp_all [titleCtrls]))
    · exact adm_group _ _ h)

private theorem frontBlock_adm (file : String) (f : FrontMatter) : Adm d (frontBlock file d f) := by
  unfold frontBlock
  have hand : Adm d #[Raw.space, .ctrl "and" f.pos, .space] := adm_lit (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [Vocab.admits, vocabularyFor, vocabulary, titleCtrls])
  split
  · exact adm_empty
  · refine adm_append (adm_append (adm_append (adm_append (adm_append ?_ ?_) ?_) ?_) ?_) ?_
    · exact frontDecl_adm _ _ _ (by simp [titleCtrls]) (frontText_adm file _ _)
    · split
      · exact frontDecl_adm _ _ _ (by simp [titleCtrls]) (frontText_adm file _ _)
      · exact adm_empty
    · split
      · exact adm_empty
      · exact frontDecl_adm _ _ _ (by simp [titleCtrls]) (frontJoin_adm file _ _ hand _)
    · split
      · exact adm_empty
      · exact frontDecl_adm _ _ _ (by simp [titleCtrls]) (frontText_adm file _ _)
    · refine frontDecl_adm _ _ _ (by simp [titleCtrls]) ?_
      cases f.date with
      | none => exact adm_empty
      | some x => exact frontText_adm file _ x
    · exact adm_lit (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp [Vocab.admits, vocabularyFor, vocabulary, titleCtrls])

private theorem frontAbstract_adm (file : String) (f : FrontMatter) :
    Adm d (frontAbstract file d f) := by
  unfold frontAbstract
  have hpar : Adm d #[Raw.par f.pos] := adm_lit (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; rfl)
  split
  · exact adm_empty
  · exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨Or.inl (by simp [vocabularyFor, vocabulary]), admitsList_of_adm _ ?_⟩
      intro r hr
      exact frontJoin_adm file _ _ hpar _ r (by simpa using hr))

private theorem frontRaws_adm (file : String) (m : MetaRead) : Adm d (m.frontRaws file d) := by
  unfold MetaRead.frontRaws
  have h := adm_append (frontBlock_adm (d := d) file m.front) (frontAbstract_adm file m.front)
  dsimp only
  split
  · exact h
  · exact adm_push h rfl

public theorem desugar_vocabulary_mem (file input : String) (dialect : Dialect := .document)
    (role : Role := .document) (citing : Bool := false)
    (known : Option (Std.HashSet String) := none) :
    ∀ r ∈ (desugar file input dialect role citing known false).1,
      (vocabularyFor dialect).admits r = true := by
  unfold desugar bodyRaws
  refine adm_append (adm_append (adm_append (adm_append (layout_adm _) (prelude_adm _)) ?_)
    (blkListRaws_adm file _ (list_adm _ _) _ #[] #[] adm_empty)) (tail_adm _ _ _ _)
  split
  · exact frontRaws_adm file _
  · exact adm_empty

public theorem read_desugar_exact (file input : String) : read file input = desugar file input := by
  unfold read
  rfl

public theorem readIncluded_desugar_exact (file input : String) (cites : Bool) :
    readIncluded file input cites = desugar file input .document .included cites := by
  unfold readIncluded
  rfl

/-- A raw that opens a block wherever it stands. -/
@[expose] public def BlockStart (r : Raw) : Prop :=
  (∃ p, r = .par p) ∨
    (∃ n p, r = .ctrl n p ∧ n ∈ vocabulary.bridged ∧ n ≠ Parse.markdownImageControl) ∨
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

private theorem verb_start (e : String) (s : Parse.Verbatim) (p : Pos) (h : e ∈ vocabulary.verbs) :
    BlockStart (.verb e s p) :=
  Or.inr (Or.inr (Or.inl ⟨e, s, p, rfl, h⟩))

private theorem env_start (n : String) (b : Array Raw) (p : Pos) (h : n ∈ vocabulary.envs) :
    BlockStart (.env n b p) :=
  Or.inr (Or.inr (Or.inr ⟨n, b, p, rfl, h⟩))

private theorem blkRaws_starts (file : String) (refs : Array Raw) (hrefs : Starts refs) (b : Blk) :
    Starts (blkRaws file refs d b).1 := by
  cases b with
  | para body p =>
    simp only [blkRaws]
    exact Or.inr ⟨.par p, Array.mem_push_self, Or.inl ⟨p, rfl⟩⟩
  | heading level body p =>
    simp only [blkRaws, Parse.headingRaws_contract]
    exact Or.inr ⟨.ctrl (Parse.headingControl level) p, by simp,
      Or.inr (Or.inl ⟨_, p, rfl, bridged_mem level, by
        cases level <;> simp [Parse.headingControl, Parse.markdownImageControl]⟩)⟩
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
  | aside body p =>
    simp only [blkRaws]
    split
    · exact Or.inr ⟨.par p, by simp, Or.inl ⟨p, rfl⟩⟩
    · exact Or.inr ⟨.par p, by simp, Or.inl ⟨p, rfl⟩⟩
  | disclosure summary expanded body p =>
    simp only [blkRaws, disclosureRaws]
    exact starts_single (env_start _ _ _ (by simp [vocabulary]))
  | list ordered start tight items p =>
    simp only [blkRaws]
    exact starts_single (env_start _ _ _ (by cases ordered <;> simp [vocabulary]))
  | table aligns header rows p =>
    simp only [blkRaws]
    obtain ⟨body, hbody, _⟩ := tableRaws_contract (cellRaws file d) aligns header rows p
    rw [hbody]
    exact starts_single (env_start _ _ _ (by simp [vocabulary]))
  | lean attrs p =>
    simp only [blkRaws]
    cases d with
    | docstring => exact Or.inl rfl
    | lean => exact Or.inl rfl
    | document => exact Or.inr ⟨.par p, by simp [Dialect.divisions], Or.inl ⟨p, rfl⟩⟩
  | metadata fields p =>
    simp only [blkRaws]
    exact Or.inl rfl
  | refs p =>
    simp only [blkRaws]
    exact hrefs
  | note label body p =>
    simp only [blkRaws]
    exact Or.inl rfl

private theorem blkListRaws_starts (file : String) (refs : Array Raw) (hrefs : Starts refs) :
    (l : List Blk) → (out : Array Raw) →
    (ds : Array Diag) → Starts out → Starts (blkListRaws file refs d out ds l).1
  | [], _, _, h => by simpa [blkListRaws] using h
  | b :: rest, out, ds, h => by
    simp only [blkListRaws]
    exact blkListRaws_starts file refs hrefs rest _ _
      (starts_append h (blkRaws_starts file refs hrefs b))

private theorem list_starts (m : MetaRead) (cited : Bool) : Starts (m.list cited) := by
  unfold MetaRead.list
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨.par m.bibPos, by simp, Or.inl ⟨_, rfl⟩⟩

private theorem layout_starts (m : MetaRead) : Starts m.layout := by
  unfold MetaRead.layout
  split
  · rename_i q _
    refine Or.inr ⟨.ctrl Parse.markdownWebControl q, by simp, Or.inr (Or.inl ⟨_, _, rfl, ?_, ?_⟩)⟩
    · simp [vocabulary]
    · simp [Parse.markdownWebControl, Parse.markdownImageControl]
  · exact Or.inl rfl

private theorem prelude_starts (m : MetaRead) : Starts m.prelude := by
  unfold MetaRead.prelude
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨.par m.bibPos, Array.mem_push_self, Or.inl ⟨_, rfl⟩⟩

private theorem front_starts (file : String) (dialect : Dialect) (m : MetaRead) :
    Starts (m.frontRaws file dialect) := by
  unfold MetaRead.frontRaws
  dsimp only
  split
  · next h => exact Or.inl (by simpa using h)
  · exact Or.inr ⟨.par m.front.pos, Array.mem_push_self, Or.inl ⟨_, rfl⟩⟩

private theorem tail_starts (file : String) (dialect : Dialect) (m : MetaRead) (cited placed : Bool) :
    Starts (m.tail file dialect cited placed) := by
  unfold MetaRead.tail
  refine starts_append ?_ ?_
  · split
    · exact Or.inl rfl
    · exact Or.inr ⟨.par m.bibPos, Array.mem_push_self, Or.inl ⟨_, rfl⟩⟩
  · split
    · exact Or.inl rfl
    · next hc =>
      rcases list_starts m cited with he | ⟨r, hr, hs⟩
      · simp [he] at hc
      · exact Or.inr ⟨r, Array.mem_append.mpr (Or.inr hr), hs⟩

public theorem desugar_blockStart_contract (file input : String) (dialect : Dialect := .document)
    (role : Role := .document) (citing : Bool := false)
    (known : Option (Std.HashSet String) := none)
    (h : (desugar file input dialect role citing known false).1 ≠ #[]) :
    ∃ r ∈ (desugar file input dialect role citing known false).1, BlockStart r := by
  unfold desugar bodyRaws at h ⊢
  refine (starts_append (starts_append (starts_append (starts_append (layout_starts _)
    (prelude_starts _)) ?_) (blkListRaws_starts file _ (list_starts _ _) _ #[] #[] (Or.inl rfl)))
    (tail_starts _ _ _ _ _)).resolve_left h
  split
  · exact front_starts file _ _
  · exact Or.inl rfl

public theorem vocabulary_contract :
    (∀ n ∈ vocabulary.envs, Parse.inputEnvFile? n = none ∧ n ≠ Parse.scopeEnv ∧
      Parse.splitOpen? n = none ∧ Parse.splitClose? n = none) ∧
    (∀ n ∈ vocabulary.ctrls, ' ' ∉ n.toList) ∧
    (∀ n ∈ vocabulary.bridged, ((Parse.headingControl? n).isSome ∨ n = Parse.markdownBibControl ∨
      n = Parse.citeSetupMark ∨ n = Parse.markdownImageControl ∨ n = Parse.markdownWebControl) ∧
      ' ' ∈ n.toList) ∧
    (∀ n ∈ (vocabularyFor .document).requests, n ∉ vocabulary.envs ∧ Parse.inputEnvFile? n = none ∧
      ' ' ∈ n.toList) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    simp only [vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Parse.inputEnvFile?, Parse.scopeEnv, Parse.splitOpen?, Parse.splitClose?,
        Parse.markdownTableEnv, Parse.markdownDisclosureEnv]
  · intro n hn
    simp only [vocabulary, citeCtrls, titleCtrls, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨level, _, rfl⟩ := List.mem_map.mp hn
      cases level <;> simp [Parse.headingControl, Parse.headingControl?]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;>
        simp [Parse.markdownBibControl, Parse.citeSetupMark, Parse.markdownImageControl,
          Parse.markdownWebControl]
  · intro n hn
    simp only [vocabularyFor, Dialect.divisions, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    subst hn
    simp [vocabulary, leanDivisionEnv, Parse.inputEnvFile?, Parse.markdownTableEnv,
      Parse.markdownDisclosureEnv]

end LeanTex.Core.Md
