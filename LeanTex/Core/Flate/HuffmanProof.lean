module

import all LeanTex.Core.Flate.Huffman

namespace LeanTex.Core.Flate

namespace Canonical

def atWidth (lengths : Array Nat) (width n : Nat) : List Nat :=
  (List.range n).filter fun s => lengths[s]?.getD 0 == width

def symbols (lengths : Array Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => symbols lengths k ++ atWidth lengths (k + 1) lengths.size

def rank (lengths : Array Nat) (width n : Nat) : Nat :=
  (lengths.toList.take n).count width

def code (lengths : Array Nat) (s : Nat) : Nat :=
  let width := lengths[s]?.getD 0
  reverseBits (start (fun l => (huffCounts lengths)[l]?.getD 0) width +
    rank lengths width s) width

theorem rank_succ_exact (lengths : Array Nat) (width n : Nat) (hn : n < lengths.size) :
    rank lengths width (n + 1) =
      rank lengths width n + if lengths[n]?.getD 0 == width then 1 else 0 := by
  have hnl : n < lengths.toList.length := by simpa using hn
  simp only [rank, List.take_succ_eq_append_getElem hnl,
    List.count_append, List.count_singleton, Array.getElem_toList,
    getElem?_pos lengths n hn, Option.getD_some]

theorem atWidth_succ_exact (lengths : Array Nat) (width n : Nat) :
    atWidth lengths width (n + 1) =
      atWidth lengths width n ++
        if lengths[n]?.getD 0 == width then [n] else [] := by
  simp [atWidth, List.range_succ, List.filter_append, List.filter_cons]

theorem atWidth_length_exact (lengths : Array Nat) (width n : Nat)
    (hn : n ≤ lengths.size) :
    (atWidth lengths width n).length = rank lengths width n := by
  induction n with
  | zero => simp [atWidth, rank]
  | succ n ih =>
    rw [atWidth_succ_exact, List.length_append, ih (by omega)]
    have hi : n < lengths.toList.length := by simpa using (show n < lengths.size by omega)
    simp only [rank, List.take_succ_eq_append_getElem hi, List.count_append,
      List.count_singleton]
    have hg : lengths[n]?.getD 0 = lengths.toList[n]'hi := by
      simp [getElem?_pos lengths n (show n < lengths.size by omega)]
    rw [hg]
    split <;> simp_all

theorem atWidth_lookup_exact (lengths : Array Nat) (width n s : Nat)
    (hs : s < n) (hl : lengths[s]?.getD 0 = width) :
    let r := (atWidth lengths width s).length
    r < (atWidth lengths width n).length ∧
      (atWidth lengths width n)[r]? = some s := by
  dsimp only
  induction n with
  | zero => omega
  | succ n ih =>
    rw [atWidth_succ_exact]
    by_cases he : s = n
    · subst s
      simp [hl]
    · have hp := ih (by omega)
      constructor
      · simp only [List.length_append]
        omega
      · rw [List.getElem?_append_left hp.1]
        exact hp.2

end Canonical

theorem huffSymbols_exact (lengths : Array Nat) :
    (huffSymbols lengths).toList = Canonical.symbols lengths 15 := by
  unfold huffSymbols
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [1:16] (#[] : Array Nat) _ : Id (Array Nat)) = result
  let P (width : Nat) (out : Array Nat) : Prop :=
    out.toList = Canonical.symbols lengths (width - 1)
  have houter : P 16 result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P 16) _ 1 16 _ (by decide)
      (by simp [P, Canonical.symbols]) _ (fun _ h => h)
    intro width hw _ out hout
    change P (width + 1) (forIn [0:lengths.size] out _ : Id (Array Nat)).run
    generalize hinnerRes : (forIn [0:lengths.size] out _ : Id (Array Nat)) = inner
    let Q (n : Nat) (result : Array Nat) : Prop :=
      let entries := Canonical.atWidth lengths width n
      result.toList = out.toList ++ entries
    have hinner : Q lengths.size inner := by
      rw [← hinnerRes]
      apply Progress.forIn_range_exact Q (Q lengths.size) _ 0 lengths.size _
        (Nat.zero_le _) (by simp [Q, Canonical.atWidth]) _ (fun _ h => h)
      intro n _ _ result hr
      by_cases he : lengths[n]?.getD 0 = width
      · simp only [beq_iff_eq, he, ite_true]
        change Q (n + 1) (result.push n)
        simp only [Q, Array.toList_push, hr, Canonical.atWidth_succ_exact, beq_iff_eq, he,
          ite_true, List.append_assoc]
      · simp only [beq_iff_eq, he, ite_false]
        change Q (n + 1) result
        simpa only [Q, Canonical.atWidth_succ_exact, beq_iff_eq, he, ite_false,
          List.append_nil] using hr
    change _ = _ at hinner
    dsimp only [P] at hout ⊢
    change inner.toList = _
    rw [hinner, hout, Nat.add_sub_cancel_right,
      show width = (width - 1) + 1 by omega, Canonical.symbols]
    simp only [Nat.add_sub_cancel_right]
  exact houter

theorem codeStarts_exact (counts : Array Nat) :
    (codeStarts counts).size = 16 ∧ ∀ k,
      (codeStarts counts)[k]?.getD 0 =
        if 0 < k ∧ k < 16 then Canonical.start (fun l => counts[l]?.getD 0) k else 0 := by
  let count := fun (l : Nat) => counts[l]?.getD 0
  let P (n : Nat) (s : Array Nat × Nat) : Prop :=
    s.2 = Canonical.start count (n - 1) ∧
    s.1.size = 16 ∧ ∀ k, s.1[k]?.getD 0 =
      if 0 < k ∧ k < n then Canonical.start count k else 0
  unfold codeStarts
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [1:16] (Array.replicate 16 0, 0) _ :
    Id (Array Nat × Nat)) = result
  have hloop : P 16 result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P 16) _ 1 16 _ (by decide) ?_ ?_ (fun _ h => h)
    · refine ⟨rfl, by simp, ?_⟩
      intro k
      have hk1 : ¬(0 < k ∧ k < 1) := by omega
      rw [ite_eq_right hk1]
      by_cases hk : k < 16 <;> simp [hk]
    · intro n hn hn16 s hs
      have hc : (s.2 + counts[n - 1]?.getD 0) * 2 = Canonical.start count n := by
        rw [hs.1]
        conv => rhs; rw [show n = (n - 1) + 1 by omega, Canonical.start]
      change P (n + 1) (s.1.set! n _, _)
      rw [hc]
      refine ⟨by simp, by simpa only [Array.size_set!] using hs.2.1, ?_⟩
      intro k
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases he : n = k
      · subst k
        have hi : n < s.1.size := by have := hs.2.1; omega
        simp [hi, show 0 < n ∧ n < n + 1 by omega]
      · have he' : (0 < k ∧ k < n) ↔ (0 < k ∧ k < n + 1) := by omega
        simp only [he, ite_false, hs.2.2 k, he']
  exact hloop.2

/-- The encoder assigns precisely the canonical start plus the symbol's rank
among earlier symbols of the same width, for every bounded length vector. -/
theorem canonCodes_exact (lengths : Array Nat)
    (hb : ∀ s < lengths.size, lengths[s]?.getD 0 ≤ 15) :
    (canonCodes lengths).size = lengths.size ∧
      ∀ s < lengths.size, (canonCodes lengths)[s]?.getD 0 = Canonical.code lengths s := by
  let count := fun (l : Nat) => (huffCounts lengths)[l]?.getD 0
  let P (n : Nat) (state : Array Nat × Array Nat) : Prop :=
    state.1.size = 16 ∧
    (∀ k, 0 < k ∧ k < 16 → state.1[k]?.getD 0 =
      Canonical.start count k + Canonical.rank lengths k n) ∧
    state.2.size = lengths.size ∧
    ∀ s < lengths.size, state.2[s]?.getD 0 =
      if s < n then Canonical.code lengths s else 0
  unfold canonCodes
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:lengths.size]
    (codeStarts (huffCounts lengths), Array.replicate lengths.size 0) _ :
      Id (Array Nat × Array Nat)) = result
  have hloop : P lengths.size result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P lengths.size) _ 0 lengths.size _
      (Nat.zero_le _) ?_ ?_ (fun _ h => h)
    · refine ⟨(codeStarts_exact _).1, ?_, by simp, ?_⟩
      · intro k hk
        rw [(codeStarts_exact _).2 k]
        rw [ite_eq_left hk]
        simp only [Canonical.rank, List.take_zero, List.count_nil,
          Nat.add_zero]
        rfl
      · intro s hs
        simp [hs]
    · intro n _ hn state hp
      have hb' := hb n hn
      by_cases hpos : 0 < lengths[n]?.getD 0
      · simp only [hpos, ite_true]
        have hnext := hp.2.1 (lengths[n]?.getD 0) ⟨hpos, by omega⟩
        change P (n + 1)
          (state.1.set! (lengths[n]?.getD 0) (state.1[lengths[n]?.getD 0]?.getD 0 + 1),
            state.2.set! n (reverseCode (state.1[lengths[n]?.getD 0]?.getD 0)
              (lengths[n]?.getD 0)))
        refine ⟨by simpa only [Array.size_set!] using hp.1, ?_,
          by simpa only [Array.size_set!] using hp.2.2.1, ?_⟩
        · intro k hk
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
          by_cases he : lengths[n]?.getD 0 = k
          · have hi : k < state.1.size := by have := hp.1; omega
            simp only [he, hi, ite_true, Option.getD_some, hp.2.1 k hk,
              Canonical.rank_succ_exact _ _ _ hn, beq_self_eq_true, Nat.add_assoc]
          · simp only [he, ite_false, hp.2.1 k hk,
              Canonical.rank_succ_exact _ _ _ hn, beq_iff_eq, Nat.add_zero]
        · intro s hs
          dsimp only [Prod.snd]
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
          by_cases he : n = s
          · subst s
            have hi : n < state.2.size := by have := hp.2.2.1; omega
            simp only [hi, ite_true, Option.getD_some, Nat.lt_succ_self,
              canonCodes_reverseBits_exact, hnext]
            rfl
          · have hi : (s < n) ↔ (s < n + 1) := by omega
            simp only [he, ite_false, hp.2.2.2 s hs, hi]
      · simp only [hpos, ite_false]
        change P (n + 1) state
        refine ⟨hp.1, ?_, hp.2.2.1, ?_⟩
        · intro k hk
          have he : lengths[n]?.getD 0 ≠ k := by omega
          simp only [hp.2.1 k hk, Canonical.rank_succ_exact _ _ _ hn,
            beq_iff_eq, he, ite_false, Nat.add_zero]
        · intro s hs
          rw [hp.2.2.2 s hs]
          by_cases he : n = s
          · subst s
            have hz : lengths[n]?.getD 0 = 0 := by omega
            simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true,
              Canonical.code, hz, Canonical.reverseBits]
          · have hi : (s < n) ↔ (s < n + 1) := by omega
            simp only [hi]
  refine ⟨hloop.2.2.1, ?_⟩
  intro s hs
  simpa only [hs, ite_true] using hloop.2.2.2 s hs

theorem canonical_symbols_length_exact (lengths : Array Nat) (k : Nat) (hk : k ≤ 15) :
    (Canonical.symbols lengths k).length =
      Canonical.index (fun l => (huffCounts lengths)[l]?.getD 0) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hc : CountsFor lengths.toList (huffCounts lengths) := huffCounts_loop_exact lengths
    rw [Canonical.symbols, List.length_append, ih (by omega),
      Canonical.index, Canonical.atWidth_length_exact _ _ _ (Nat.le_refl _),
      hc.2]
    rw [ite_eq_left (show 0 < k + 1 ∧ k + 1 < 16 by omega)]
    simp only [Canonical.rank]
    rw [List.take_of_length_le (by simp)]

theorem canonical_symbols_lookup_exact (lengths : Array Nat) (width s k : Nat)
    (hw : 0 < width) (hwk : width ≤ k) (hk : k ≤ 15) (hs : s < lengths.size)
    (hl : lengths[s]?.getD 0 = width) :
    let i := Canonical.index (fun l => (huffCounts lengths)[l]?.getD 0) (width - 1) +
      Canonical.rank lengths width s
    i < (Canonical.symbols lengths k).length ∧
      (Canonical.symbols lengths k)[i]? = some s := by
  dsimp only
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Canonical.symbols]
    by_cases he : width = k + 1
    · rw [he] at hl ⊢
      have hp := Canonical.atWidth_lookup_exact lengths (k + 1) lengths.size s hs hl
      rw [Canonical.atWidth_length_exact _ _ _ (by omega)] at hp
      have hlen := canonical_symbols_length_exact lengths k (by omega)
      simp only [Nat.add_sub_cancel_right]
      rw [← hlen, List.length_append]
      refine ⟨by omega, ?_⟩
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact hp.2
    · have hp := ih (by omega) (by omega)
      refine ⟨by simp only [List.length_append]; omega, ?_⟩
      rw [List.getElem?_append_left hp.1]
      exact hp.2

/-- Every nonzero width's rank in the decoder table names the original symbol. -/
theorem mkHuff_symbols_exact (lengths : Array Nat) (s width : Nat)
    (hs : s < lengths.size) (hw : 0 < width ∧ width ≤ 15)
    (hl : lengths[s]?.getD 0 = width) :
    (mkHuff lengths).symbols[
      Canonical.index (fun l => (mkHuff lengths).counts[l]?.getD 0) (width - 1) +
        Canonical.rank lengths width s]? = some s := by
  have hp := canonical_symbols_lookup_exact lengths width s 15 hw.1 hw.2
    (Nat.le_refl _) hs hl
  simpa only [mkHuff, ← Array.getElem?_toList, huffSymbols_exact] using hp.2

/-- The rank of a present symbol is strictly below its width's count. -/
theorem canonical_rank_between (lengths : Array Nat) (s width : Nat)
    (hs : s < lengths.size) (hw : 0 < width ∧ width ≤ 15)
    (hl : lengths[s]?.getD 0 = width) :
    Canonical.rank lengths width s < (huffCounts lengths)[width]?.getD 0 := by
  have hp := Canonical.atWidth_lookup_exact lengths width lengths.size s hs hl
  have hcounts : CountsFor lengths.toList (huffCounts lengths) := huffCounts_loop_exact lengths
  rw [Canonical.atWidth_length_exact _ _ _ (by omega),
    Canonical.atWidth_length_exact _ _ _ (Nat.le_refl _)] at hp
  rw [hcounts.2 width,
    ite_eq_left (show 0 < width ∧ width < 16 by omega)]
  have htake : lengths.toList.take lengths.size = lengths.toList :=
    List.take_of_length_le (by simp)
  simpa only [Canonical.rank, htake] using hp.1

/-- Every symbol's actual encoder value is recognized by the actual decoder
table. The premises describe the length vector's bound and available code
space; no encoder/decoder equation is assumed. -/
theorem canonCodes_decode_exact (lengths : Array Nat) (r : Br) (s width : Nat)
    (hb : ∀ s < lengths.size, lengths[s]?.getD 0 ≤ 15)
    (hs : s < lengths.size) (hw : 0 < width)
    (hl : lengths[s]?.getD 0 = width)
    (hspace : Canonical.start (fun l => (huffCounts lengths)[l]?.getD 0) width +
      (huffCounts lengths)[width]?.getD 0 ≤ 2 ^ width)
    (hf : BitField r.data r.bitPos width ((canonCodes lengths)[s]?.getD 0)) :
    (mkHuff lengths).decode r =
      some (s, { r with bitPos := r.bitPos + width }) := by
  have hw15 : width ≤ 15 := by simpa only [hl] using hb s hs
  have hr := canonical_rank_between lengths s width hs ⟨hw, hw15⟩ hl
  have hcounts : CountsFor lengths.toList (huffCounts lengths) := huffCounts_loop_exact lengths
  have hz : (huffCounts lengths)[0]?.getD 0 = 0 := by
    rw [hcounts.2 0]
    rfl
  have hstart := Canonical.start_first_exact
    (fun l => (huffCounts lengths)[l]?.getD 0) hz width hw
  let c := Canonical.start (fun l => (huffCounts lengths)[l]?.getD 0) width +
    Canonical.rank lengths width s
  have hc : c < 2 ^ width := by dsimp only [c]; omega
  have hlo : Canonical.first (fun l => (mkHuff lengths).counts[l]?.getD 0)
      (width - 1) ≤ c := by
    change Canonical.first (fun l => (huffCounts lengths)[l]?.getD 0) (width - 1) ≤ c
    rw [← hstart]
    exact Nat.le_add_right ..
  have hhi : c < Canonical.first (fun l => (mkHuff lengths).counts[l]?.getD 0)
      (width - 1) + (mkHuff lengths).counts[width]?.getD 0 := by
    change c < Canonical.first (fun l => (huffCounts lengths)[l]?.getD 0)
      (width - 1) + (huffCounts lengths)[width]?.getD 0
    rw [← hstart]
    exact Nat.add_lt_add_left hr _
  have hfield : CodeField r.data r.bitPos width c := by
    apply BitField.codeField
    rw [(canonCodes_exact lengths hb).2 s hs, Canonical.code, hl] at hf
    exact hf
  rw [huff_decode_exact _ _ _ _ ⟨hw, hw15⟩ hc hfield hlo hhi]
  have hsub : c - Canonical.first (fun l => (mkHuff lengths).counts[l]?.getD 0)
      (width - 1) = Canonical.rank lengths width s := by
    change c - Canonical.first (fun l => (huffCounts lengths)[l]?.getD 0)
      (width - 1) = _
    rw [← hstart]
    exact Nat.add_sub_cancel_left ..
  rw [hsub, mkHuff_symbols_exact lengths s width hs ⟨hw, hw15⟩ hl]
  rfl

end LeanTex.Core.Flate
