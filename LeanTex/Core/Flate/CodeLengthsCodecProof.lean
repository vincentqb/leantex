module

import all LeanTex.Core.Flate.CodeLengthsReader
import all LeanTex.Core.Flate.CodeLengthsWriter
import all LeanTex.Core.Flate.BitStreamProof
import all LeanTex.Core.Flate.DecodeLoop
import LeanTex.Core.Flate.Frequencies

namespace LeanTex.Core.Flate.CodeLengths

theorem frequencies_contract (entries : Array Entry) :
    (frequencies entries).size = 19 ∧
      ∀ entry ∈ entries.toList, entry.1 < 19 →
        0 < (frequencies entries)[entry.1]?.getD 0 := by
  have h := Frequencies.count_contract (fun entry : Entry => some entry.1)
    entries (Array.replicate 19 0)
  refine ⟨by simpa only [frequencies, Array.size_replicate] using h.1, ?_⟩
  intro entry he hs
  exact h.2.2 entry he entry.1 rfl (by simpa using hs)

/-- What a covering whose entries all take one symbol spells: that length throughout for a
literal, zeros for a run of zeros, and from the start nothing for a repeat, which needs a length
before it. -/
theorem Covers.one_symbol {seq : Array Nat} {start : Nat} {out : Array Entry} {p : Nat} (s : Nat)
    (h : Covers seq start out p) (hs : ∀ e ∈ out.toList, e.1 = s) :
    (s < 16 → ∀ i, start ≤ i → i < p → seq[i]?.getD 0 = s) ∧ (s = 16 → start = 0 → p = 0) ∧
      (16 < s → ∀ i, start ≤ i → i < p → seq[i]?.getD 0 = 0) := by
  induction h with
  | empty _ =>
    exact ⟨fun _ _ h1 h2 => absurd h2 (by omega), fun _ h0 => h0.symm ▸ rfl,
      fun _ _ h1 h2 => absurd h2 (by omega)⟩
  | @push out q q' entry prior step ih =>
    have hprior := ih (fun e he => hs e (by simp [he]))
    have he : entry.1 = s := hs entry (by simp)
    have hle := prior.contract.1
    cases step with
    | literal v hv hr =>
      simp only at he
      subst he
      refine ⟨fun _ i h1 hi => ?_, fun h16 => absurd h16 (by omega),
        fun h16 => absurd h16 (by omega)⟩
      by_cases hiq : i < q
      · exact hprior.1 hv i h1 hiq
      · have heq : i = q := by omega
        subst heq
        simpa using hr.2 0 (by omega)
    | repeat16 count v hc hp prev hr =>
      simp only at he
      subst he
      exact ⟨fun h => absurd h (by omega), fun _ h0 => absurd (hprior.2.1 rfl h0) (by omega),
        fun h => absurd h (by omega)⟩
    | zeros17 count hc hr =>
      simp only at he
      subst he
      refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ i h1 hi => ?_⟩
      by_cases hiq : i < q
      · exact hprior.2.2 (by omega) i h1 hiq
      · simpa [show q + (i - q) = i by omega] using hr.2 (i - q) (by omega)
    | zeros18 count hc hr =>
      simp only at he
      subst he
      refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ i h1 hi => ?_⟩
      by_cases hiq : i < q
      · exact hprior.2.2 (by omega) i h1 hiq
      · simpa [show q + (i - q) = i by omega] using hr.2 (i - q) (by omega)

/-- The code lengths of a sequence that is not constant use two symbols of the code-length
alphabet, so its code fills its space. -/
theorem frequencies_two_live (seq : Array Nat) (hv : ∀ i < seq.size, seq[i]?.getD 0 < 16)
    (hvary : ∃ i j, i < seq.size ∧ j < seq.size ∧ seq[i]?.getD 0 ≠ seq[j]?.getD 0) :
    1 < ((Array.range (frequencies (encode seq)).size).filter
      fun s => (frequencies (encode seq))[s]?.getD 0 > 0).size := by
  have hc := encode_covers seq hv
  have hf := frequencies_contract (encode seq)
  obtain ⟨i, j, hi, hj, hne⟩ := hvary
  have hvalid := hc.contract.2.2
  have htwo : ∃ e₁ ∈ (encode seq).toList, ∃ e₂ ∈ (encode seq).toList, e₁.1 ≠ e₂.1 := by
    cases hl : (encode seq).toList with
    | nil =>
      exfalso
      have ho := hc.one_symbol 0 (by simp [hl])
      have := ho.1 (by omega) i (Nat.zero_le _) hi
      have := ho.1 (by omega) j (Nat.zero_le _) hj
      omega
    | cons e rest =>
      by_cases hall : ∀ e' ∈ (encode seq).toList, e'.1 = e.1
      · exfalso
        have ho := hc.one_symbol e.1 hall
        have he19 : e.1 < 19 := (hvalid e (by simp [hl])).1
        by_cases h16 : e.1 < 16
        · exact hne ((ho.1 h16 i (Nat.zero_le _) hi).trans
            (ho.1 h16 j (Nat.zero_le _) hj).symm)
        · by_cases h16' : e.1 = 16
          · have := ho.2.1 h16' rfl
            omega
          · exact hne ((ho.2.2 (by omega) i (Nat.zero_le _) hi).trans
              (ho.2.2 (by omega) j (Nat.zero_le _) hj).symm)
      · have hex : ∃ e' ∈ (encode seq).toList, e'.1 ≠ e.1 := by
          refine Classical.byContradiction fun hno => hall fun e' he' => ?_
          exact Classical.byContradiction fun hne' => hno ⟨e', he', hne'⟩
        obtain ⟨e', hm, hne'⟩ := hex
        exact ⟨e', by simpa [hl] using hm, e, by simp, hne'⟩
  obtain ⟨e₁, h₁, e₂, h₂, hne₂⟩ := htwo
  exact Frequencies.live_two _ e₁.1 e₂.1 (by rw [hf.1]; exact (hvalid e₁ h₁).1)
    (by rw [hf.1]; exact (hvalid e₂ h₂).1) hne₂ (hf.2 e₁ h₁ (hvalid e₁ h₁).1)
    (hf.2 e₂ h₂ (hvalid e₂ h₂).1)

theorem writeEntry_contract (lengths codes : Array Nat) (w : Bw) (entry : Entry)
    (hw : w.Valid) (hl : lengths[entry.1]?.getD 0 ≤ 16) (he : entry.2.2 ≤ 16) :
    (writeEntry lengths codes w entry).Valid ∧
      (writeEntry lengths codes w entry).Extends w := by
  have hm := push_valid w (codes[entry.1]?.getD 0) _ hw hl
  have hx := push_extends_exact w (codes[entry.1]?.getD 0) _ hw hl
  unfold writeEntry
  split
  · exact ⟨push_valid _ _ _ hm he, (push_extends_exact _ _ _ hm he).trans hx⟩
  · exact ⟨hm, hx⟩

theorem write_contract (lengths codes : Array Nat) (entries : Array Entry) (w : Bw)
    (hw : w.Valid) (hl : ∀ s : Nat, lengths[s]?.getD 0 ≤ 16)
    (he : ∀ entry ∈ entries.toList, entry.Valid) :
    (write lengths codes entries w).Valid ∧ (write lengths codes entries w).Extends w :=
  BitStream.write_contract _ entries w hw (fun entry hm w hw =>
    writeEntry_contract lengths codes w entry hw (hl entry.1)
      (by have := (he entry hm).2.1; omega))

theorem writeEntry_read_exact {seq out : Array Nat} {p q : Nat} {entry : Entry}
    (freqs : Array Nat) (w : Bw) (data : ByteArray)
    (hf : freqs.size ≤ 128) (hs : 0 < freqs[entry.1]?.getD 0)
    (hw : w.Valid) (hp : Prefix seq p out) (hstep : Step seq p entry q)
    (hr : (writeEntry (PackageMerge.lengths freqs 7)
      (canonCodes (PackageMerge.lengths freqs 7)) w entry).Realizes data) :
    ∃ out', readEntry (mkHuff (PackageMerge.lengths freqs 7))
        (out, {data, bitPos := w.position}) =
      .ok (out', {data, bitPos :=
        (writeEntry (PackageMerge.lengths freqs 7)
          (canonCodes (PackageMerge.lengths freqs 7)) w entry).position}) ∧
      Prefix seq q out' := by
  let lengths := PackageMerge.lengths freqs 7
  let codes := canonCodes lengths
  let mid := w.push (codes[entry.1]?.getD 0) (lengths[entry.1]?.getD 0)
  have hl : lengths[entry.1]?.getD 0 ≤ 16 :=
    Nat.le_trans ((PackageMerge.lengths_contract freqs 7 (by decide) hf).1.width_le entry.1)
      (by decide)
  have hm : mid.Valid := push_valid w _ _ hw hl
  have he := hstep.contract.2.2
  have hmid : (writeEntry lengths codes w entry).Extends mid := by
    unfold writeEntry
    split
    · exact push_extends_exact mid _ _ hm (by have := he.2.1; omega)
    · exact Bw.Extends.refl mid
  have hc := packageMerge_push_decode_exact freqs 7 w data entry.1 hw
    (by decide) hf hs (hr.prefix hmid)
  have hpos : mid.position = w.position + lengths[entry.1]?.getD 0 :=
    push_position_exact w _ _ hw hl
  rw [← hpos] at hc
  apply readEntry_exact (mkHuff lengths) {data, bitPos := w.position}
    {data, bitPos := mid.position}
    {data, bitPos := (writeEntry lengths codes w entry).position} hp hstep hc
  by_cases hb : 0 < entry.2.2
  · have hr' : (mid.push entry.2.1 entry.2.2).Realizes data := by
      simpa only [writeEntry, hb, ite_true] using hr
    simpa only [writeEntry, hb, ite_true] using
      push_bits_exact mid data _ _ hm (by have := he.2.1; omega) he.2.2 hr'
  · have hz : entry.2.2 = 0 := by omega
    have hv : entry.2.1 = 0 := by have := he.2.2; simp only [hz] at this; omega
    simp [writeEntry, hz, hv, Br.bits_zero_id, mid]

theorem write_steps_exact {seq out : Array Nat} {start p : Nat} {entries : Array Entry}
    (freqs : Array Nat) (w : Bw) (data : ByteArray)
    (hf : freqs.size ≤ 128) (hw : w.Valid) (hp : Prefix seq start out)
    (hc : Covers seq start entries p)
    (hs : ∀ entry ∈ entries.toList, 0 < freqs[entry.1]?.getD 0)
    (hr : (write (PackageMerge.lengths freqs 7)
      (canonCodes (PackageMerge.lengths freqs 7)) entries w).Realizes data) :
    ∃ out', DecodeLoop.Steps (readStep (mkHuff (PackageMerge.lengths freqs 7)) seq.size)
      (out, {data, bitPos := w.position}) entries.size
      (out', {data, bitPos := (write (PackageMerge.lengths freqs 7)
        (canonCodes (PackageMerge.lengths freqs 7)) entries w).position}) ∧
      Prefix seq p out' := by
  let lengths := PackageMerge.lengths freqs 7
  let codes := canonCodes lengths
  have hl : ∀ s : Nat, lengths[s]?.getD 0 ≤ 16 := fun s =>
    Nat.le_trans ((PackageMerge.lengths_contract freqs 7 (by decide) hf).1.width_le s)
      (by decide)
  induction hc with
  | empty _ => exact ⟨out, .refl _, hp⟩
  | @push entries p q entry prior step ih =>
    have hh := prior.contract
    have he := step.contract
    have hv := write_contract lengths codes entries w hw hl hh.2.2
    have hx := writeEntry_contract lengths codes (write lengths codes entries w) entry
      hv.1 (hl entry.1) (by have := he.2.2.2.1; omega)
    have hwr : write lengths codes (entries.push entry) w =
        writeEntry lengths codes (write lengths codes entries w) entry :=
      BitStream.write_push_exact _ entries w entry
    have hreal : (writeEntry lengths codes (write lengths codes entries w) entry).Realizes data :=
      hwr ▸ hr
    have hs0 : ∀ e ∈ entries.toList, 0 < freqs[e.1]?.getD 0 := by
      intro e hm
      exact hs e (by
        simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        exact Or.inl hm)
    obtain ⟨before, hsteps, hprefix⟩ := ih hs0 (hreal.prefix hx.2)
    obtain ⟨after, hread, hafter⟩ := writeEntry_read_exact freqs
      (write lengths codes entries w) data hf
      (hs entry (by simp)) hv.1 hprefix step hreal
    refine ⟨after, ?_, hafter⟩
    rw [Array.size_push, hwr]
    apply DecodeLoop.Steps.snoc hsteps
    have hlt : before.size < seq.size := by have := hprefix.1; omega
    simp only [readStep, Nat.not_le.mpr hlt, ite_false,
      bind, Except.bind, pure, Except.pure]
    rw [hread]

theorem Prefix.complete {seq out : Array Nat} (hp : Prefix seq seq.size out) :
    out = seq := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < seq.size
  · exact hp.2.2 i hi
  · have ho : ¬ i < out.size := by rw [hp.1]; exact hi
    simp only [getElem?_neg out i ho, getElem?_neg seq i hi]

theorem read_write_exact (seq : Array Nat)
    (hv : ∀ i < seq.size, seq[i]?.getD 0 < 16) (w : Bw) (data : ByteArray)
    (hw : w.Valid)
    (hr : (write (PackageMerge.lengths (frequencies (encode seq)) 7)
      (canonCodes (PackageMerge.lengths (frequencies (encode seq)) 7))
      (encode seq) w).Realizes data) :
    read (mkHuff (PackageMerge.lengths (frequencies (encode seq)) 7)) seq.size
        {data, bitPos := w.position} =
      .ok (seq, {data, bitPos :=
        (write (PackageMerge.lengths (frequencies (encode seq)) 7)
          (canonCodes (PackageMerge.lengths (frequencies (encode seq)) 7))
          (encode seq) w).position}) := by
  have hc := encode_covers seq hv
  have hf := frequencies_contract (encode seq)
  obtain ⟨out, hsteps, hp⟩ := write_steps_exact (seq := seq) (out := #[])
    (frequencies (encode seq)) w data
    (by omega) hw ⟨by simp, Nat.zero_le _, by simp⟩ hc
    (fun e he => hf.2 e he (hc.contract.2.2 e he).1) hr
  have hd : DecodeLoop.Finishes
      (readStep (mkHuff (PackageMerge.lengths (frequencies (encode seq)) 7)) seq.size)
      (out, {data, bitPos :=
        (write (PackageMerge.lengths (frequencies (encode seq)) 7)
          (canonCodes (PackageMerge.lengths (frequencies (encode seq)) 7))
          (encode seq) w).position}) 1
      (out, {data, bitPos :=
        (write (PackageMerge.lengths (frequencies (encode seq)) 7)
          (canonCodes (PackageMerge.lengths (frequencies (encode seq)) 7))
          (encode seq) w).position}) :=
    .done (by simp [readStep, hp.1, pure, Except.pure])
  have h := DecodeLoop.run_exact _ _ _ _ (seq.size + 1)
    (.malformed "deflate: code lengths overrun their table") (hsteps.finish hd)
    (by have := hc.contract.1; omega)
  simpa only [read, hp.complete] using h

end LeanTex.Core.Flate.CodeLengths
