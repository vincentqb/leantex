module

public import LeanTex.Core.MdDesugar
import all LeanTex.Core.MdDesugar
import all LeanTex.Core.Parse

/-! # What markdown lowers into

Markdown's meaning is its desugaring into the surface AST (`Md.desugar`).
This module states the image of that function: a declared slice of tex's
vocabulary, closed under the desugaring of every markdown block and inline
node (`desugar_vocabulary_mem`). The statement ranges over the md AST, not
over what the reader happens to produce today, so it holds of any reader
that hands the desugaring an AST.

The vocabulary is what an included markdown file can ask of a tex host.
Its ordinary controls are ordinary: a host redefinition reaches included
markdown as it reaches the same call written in the host. Its bridged
names hold a space, so no source can spell, forge or redefine them
(`vocabulary_contract`). Its environments are names the elaborator gives a
meaning of its own.

A new desugaring arm that emits outside the vocabulary breaks the proof
below; the commit that adds the construct extends the vocabulary, and
with it what a host can reach. -/

namespace LeanTex.Core.Md

open LeanTex.Core LeanTex.Core.Parse

/-- A slice of the surface AST's vocabulary. -/
public structure Vocab where
  /-- Ordinary controls: spelled as a document spells them. -/
  ctrls : List String
  /-- Names holding a space: no source can spell, forge or redefine one. -/
  bridged : List String
  envs : List String
  verbs : List String
  syms : List Char

/-- The vocabulary markdown lowers into. -/
@[expose] public def vocabulary : Vocab where
  ctrls := ["emph", "textbf", "texttt", "href", "includegraphics", "item", "hypertarget", "\\"]
  bridged := [Ir.HeadingLevel.title, .h1, .h2, .h3, .h4, .h5, .h6].map Parse.headingControl
  envs := ["quote", "itemize", "enumerate"]
  verbs := ["verbatim", "lstlisting"]
  syms := ['[', ']']

mutual

/-- Does the vocabulary admit this raw, its children included? Text,
spaces and paragraph ends always; math never; a control, environment,
verbatim or symbol by name. The `List` companion carries the walk. -/
@[expose] public def Vocab.admits (v : Vocab) : Raw → Bool
  | .word _ _ => true
  | .space => true
  | .par _ => true
  | .ctrl n _ => v.ctrls.contains n || v.bridged.contains n
  | .sym c _ => v.syms.contains c
  | .group body _ => v.admitsList body.toList
  | .env n body _ => v.envs.contains n && v.admitsList body.toList
  | .verb e _ _ => v.verbs.contains e
  | .math _ _ _ => false

@[expose] public def Vocab.admitsList (v : Vocab) : List Raw → Bool
  | [] => true
  | r :: rest => v.admits r && v.admitsList rest

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

/-- An array literal's members, one at a time. -/
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
  List.mem_map.mpr ⟨level, by cases level <;> simp, rfl⟩

private theorem heading_mem (level : Ir.HeadingLevel) (p : Pos) :
    vocabulary.admits (.ctrl (Parse.headingControl level) p) = true := by
  simp only [Vocab.admits, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr (bridged_mem level))

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

private theorem inlListRaws_adm (file : String) : (l : List Inl) → (out : Array Raw) →
    (ds : Array Diag) → Adm out → Adm (inlListRaws file out ds l).1
  | [], _, _, h => by simpa [inlListRaws] using h
  | x :: rest, out, ds, h => by
    simp only [inlListRaws]
    exact inlListRaws_adm file rest _ _ (adm_append h (inlRaws_adm file x))

end

mutual

private theorem blkRaws_adm (file : String) : (b : Blk) → Adm (blkRaws file b).1
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
    have h := blkListRaws_adm file body.toList #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true]
      exact ⟨by simp [vocabulary],
        admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)⟩)
  | .disclosure summary body p => by
    simp only [blkRaws, disclosureRaws]
    have hs := inlListRaws_adm file summary.toList #[] #[] adm_empty
    have hb := blkListRaws_adm file body.toList #[] #[] adm_empty
    refine adm_append (adm_lit ?_) hb
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ctrl_mem _ _ (by simp [vocabulary])
    · exact adm_group _ _ hs
    · rfl
  | .list ordered start tight items p => by
    simp only [blkRaws]
    have h := itemsRaws_adm file items.toList p #[] #[] adm_empty
    exact adm_lit (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [Vocab.admits, Bool.and_eq_true]
      exact ⟨by cases ordered <;> simp [vocabulary],
        admitsList_of_adm _ fun r hr => h r (Array.mem_toList_iff.mp hr)⟩)

private theorem blkListRaws_adm (file : String) : (l : List Blk) → (out : Array Raw) →
    (ds : Array Diag) → Adm out → Adm (blkListRaws file out ds l).1
  | [], _, _, h => by simpa [blkListRaws] using h
  | b :: rest, out, ds, h => by
    simp only [blkListRaws]
    exact blkListRaws_adm file rest _ _ (adm_append h (blkRaws_adm file b))

private theorem itemsRaws_adm (file : String) : (l : List (Array Blk)) → (p : Pos) →
    (out : Array Raw) → (ds : Array Diag) → Adm out → Adm (itemsRaws file out ds l p).1
  | [], _, _, _, h => by simpa [itemsRaws] using h
  | it :: rest, p, out, ds, h => by
    simp only [itemsRaws]
    exact itemsRaws_adm file rest p _ _ (adm_append
      (adm_push h (ctrl_mem _ _ (by simp [vocabulary])))
      (blkListRaws_adm file it.toList #[] #[] adm_empty))

end

/-- **Markdown lowers into its declared vocabulary.** Every raw the
desugaring produces, at every depth, is a word, a space, a paragraph end,
or a control, environment, verbatim or symbol the vocabulary names; no
markdown source yields math, a definition, an input request or any other
control. The induction ranges over every md block and inline node, so it
is independent of the reader. -/
public theorem desugar_vocabulary_mem (file input : String) :
    ∀ r ∈ (desugar file input).1, vocabulary.admits r = true := by
  unfold desugar
  exact blkListRaws_adm file _ #[] #[] adm_empty

/-- The markdown frontend is the desugaring, exactly: what the two
theorems here state of `desugar` they state of every `.md` read. -/
public theorem read_desugar_exact (file input : String) : read file input = desugar file input := by
  unfold read
  rfl

/-- A raw that opens a block wherever it stands: a paragraph end, a bridged
heading, a display verbatim, or one of the vocabulary's environments. -/
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

private theorem blkRaws_starts (file : String) (b : Blk) : Starts (blkRaws file b).1 := by
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
  | disclosure summary body p =>
    simp only [blkRaws, disclosureRaws]
    exact Or.inr ⟨.par p, by simp, Or.inl ⟨p, rfl⟩⟩
  | list ordered start tight items p =>
    simp only [blkRaws]
    exact starts_single (env_start _ _ _ (by cases ordered <;> simp [vocabulary]))

private theorem blkListRaws_starts (file : String) : (l : List Blk) → (out : Array Raw) →
    (ds : Array Diag) → Starts out → Starts (blkListRaws file out ds l).1
  | [], _, _, h => by simpa [blkListRaws] using h
  | b :: rest, out, ds, h => by
    simp only [blkListRaws]
    exact blkListRaws_starts file rest _ _ (starts_append h (blkRaws_starts file b))

/-- **Markdown is block-shaped.** A markdown document that lowers to
anything lowers to at least one raw that opens a block: its content never
reads as a phrase continuing the text around an include. -/
public theorem desugar_blockStart_mem (file input : String)
    (h : (desugar file input).1 ≠ #[]) : ∃ r ∈ (desugar file input).1, BlockStart r := by
  unfold desugar at h ⊢
  exact (blkListRaws_starts file _ #[] #[] (Or.inl rfl)).resolve_left h

/-- The vocabulary's names, judged against the parser's reserved spellings:
its environments are ordinary environment names — no include wrapper, no
generated scope, no definer half — its ordinary controls hold no space, so
a document spells them, and its bridged names are exactly the heading
bridge's, each holding the space no source can spell. -/
public theorem vocabulary_contract :
    (∀ n ∈ vocabulary.envs, Parse.inputEnvFile? n = none ∧ n ≠ Parse.scopeEnv ∧
      Parse.splitOpen? n = none ∧ Parse.splitClose? n = none) ∧
    (∀ n ∈ vocabulary.ctrls, ' ' ∉ n.toList) ∧
    (∀ n ∈ vocabulary.bridged, (Parse.headingControl? n).isSome ∧ ' ' ∈ n.toList) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    simp only [vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      simp [Parse.inputEnvFile?, Parse.scopeEnv, Parse.splitOpen?, Parse.splitClose?]
  · intro n hn
    simp only [vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro n hn
    obtain ⟨level, _, rfl⟩ := List.mem_map.mp hn
    cases level <;> simp [Parse.headingControl, Parse.headingControl?]

end LeanTex.Core.Md
