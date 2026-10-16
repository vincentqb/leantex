module

public import LeanTex.Core.Ir

namespace LeanTex.Core.Ir

/-! The heading tree a PDF outline projects, as hyperref and beamer bookmark it. -/

/-- A heading the outline holds: its body index, its depth in the heading tree and its words. -/
public structure OutlineHeading where
  index : Nat
  depth : Nat
  title : String
  deriving Repr, BEq

/-- The anchor a bookmarked heading sets at its line, its control character in no author's name. -/
@[expose] public def outlineMark (i : Nat) : String := s!"\u001Foutline-{i}"

/-- Whether a heading is bookmarked: in a deck an unstarred section or subsection, as beamer's are;
elsewhere an unstarred heading from a part down to a subsubsection, as LaTeX lists its contents. -/
public def outlineListed (deck : Bool) (level : HeadingLevel) (starred : Bool) : Bool :=
  !starred && if deck then level == .h2 || level == .h3
    else level != .title && headingRank level ≤ 4

/-- One block of the walk: a listed heading under the open ranks below its own, which it joins. -/
private def outlineStep (deck : Bool) (ranks : Array Nat) (i : Nat) (b : Block) :
    Array Nat × Option OutlineHeading :=
  if let .section level starred _ title := b then
    if outlineListed deck level starred then
      let kept := ranks.takeWhile (· < headingRank level)
      (kept.push (headingRank level),
        some { index := i, depth := kept.size, title := (firstPageText title).trimAscii.toString })
    else (ranks, none)
  else (ranks, none)

private def outlineGo (deck : Bool) (ranks : Array Nat) (out : Array OutlineHeading) (i : Nat) :
    List Block → Array OutlineHeading
  | [] => out
  | b :: rest =>
    let (ranks', h) := outlineStep deck ranks i b
    outlineGo deck ranks' (match h with | some h => out.push h | none => out) (i + 1) rest

/-- The listed headings among the top-level blocks, in flow order, each one deeper than the last
listed heading of a higher rank before it. -/
public def outlineHeadings (doc : Doc) : Array OutlineHeading :=
  outlineGo (doc.docClass.record.model == .frame) #[] #[] 0 doc.body.toList

private theorem takeWhile_size_le (xs : Array Nat) (p : Nat → Bool) :
    (xs.takeWhile p).size ≤ xs.size := by
  rw [← Array.length_toList, ← Array.length_toList, Array.toList_takeWhile]
  exact (List.takeWhile_sublist p).length_le

/-- What the walk keeps: the open ranks are one more than the last heading's depth, none before the
first, and each heading stands at most one deeper than the one before it. -/
private def OutlineInv (ranks : Array Nat) (out : Array OutlineHeading) : Prop :=
  (match out.back? with
    | some h => ranks.size = h.depth + 1
    | none => ranks.size = 0) ∧
  (∀ h ∈ out[0]?, h.depth = 0) ∧
  ∀ k (hk : k + 1 < out.size), out[k + 1].depth ≤ out[k].depth + 1

private theorem outlineStep_inv (deck : Bool) (ranks : Array Nat) (out : Array OutlineHeading)
    (i : Nat) (b : Block) (hinv : OutlineInv ranks out) :
    OutlineInv (outlineStep deck ranks i b).1
      (match (outlineStep deck ranks i b).2 with | some h => out.push h | none => out) := by
  obtain ⟨hback, hfirst, hstep⟩ := hinv
  unfold outlineStep
  split
  · rename_i level starred n title
    split
    · dsimp only
      have hle := takeWhile_size_le ranks (· < headingRank level)
      refine ⟨by simp, ?_, ?_⟩
      · intro h hh
        rw [Array.getElem?_push] at hh
        split at hh
        · rename_i h0
          have he : out = #[] := Array.eq_empty_of_size_eq_zero h0.symm
          subst he
          simp only [Array.back?_empty] at hback
          simp only [Option.mem_def, Option.some.injEq] at hh
          subst hh
          have hr : ranks = #[] := Array.eq_empty_of_size_eq_zero hback
          subst hr
          simp
        · exact hfirst h hh
      · intro k hk
        rw [Array.size_push] at hk
        rw [Array.getElem_push, Array.getElem_push]
        by_cases hkl : k + 1 < out.size
        · simp only [hkl, dite_true, show k < out.size by omega]
          exact hstep k hkl
        · have hk1 : k + 1 = out.size := by omega
          simp only [hkl, dite_false, show k < out.size by omega, dite_true]
          have hb : out.back? = some out[k] := by
            rw [Array.back?_eq_getElem?]
            simp [show out.size - 1 = k by omega]
          rw [hb] at hback
          simp only at hback
          omega
    · exact ⟨hback, hfirst, hstep⟩
  · exact ⟨hback, hfirst, hstep⟩

private theorem outlineGo_inv (deck : Bool) (l : List Block) (ranks : Array Nat)
    (out : Array OutlineHeading) (i : Nat) (hinv : OutlineInv ranks out) :
    ∃ ranks', OutlineInv ranks' (outlineGo deck ranks out i l) := by
  induction l generalizing ranks out i with
  | nil => exact ⟨ranks, hinv⟩
  | cons b rest ih =>
    simp only [outlineGo]
    exact ih _ _ _ (outlineStep_inv deck ranks out i b hinv)

/-- The outline's first heading is at the top of the tree and each later one at most one level
deeper than the heading before it, so every nested heading has its parent before it. -/
public theorem outlineHeadings_depth_step (doc : Doc) :
    (∀ h ∈ (outlineHeadings doc)[0]?, h.depth = 0) ∧
      ∀ k (hk : k + 1 < (outlineHeadings doc).size),
        (outlineHeadings doc)[k + 1].depth ≤ (outlineHeadings doc)[k].depth + 1 := by
  obtain ⟨_, _, hfirst, hstep⟩ := outlineGo_inv (doc.docClass.record.model == .frame)
    doc.body.toList #[] #[] 0 ⟨by simp, by simp, by simp⟩
  exact ⟨hfirst, hstep⟩

end LeanTex.Core.Ir
