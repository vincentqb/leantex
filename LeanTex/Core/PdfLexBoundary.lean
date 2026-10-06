module

public import LeanTex.Core.PdfLexProof
import all LeanTex.Core.PdfLex
import LeanTex.Core.LoopProgress

namespace LeanTex.Core.PdfLex

/-- The terminating byte required by PDF names, numbers and keywords. -/
@[expose] public def EndByte (c : Nat) : Prop := c = 256 ∨ isWs c = true ∨ isDelim c = true

public theorem EndByte.not_number {c : Nat} (h : EndByte c) : numByte c = false := by
  simp only [EndByte, isWs, isDelim, Bool.or_eq_true, beq_iff_eq] at h
  simp only [numByte, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

public theorem not_number_not_digit {c : Nat} (h : numByte c = false) : ¬ (48 ≤ c ∧ c ≤ 57) := by
  simp only [numByte, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  omega

public theorem number_byte {c : Nat} (h : numByte c = true) :
    c < 128 ∧ isWs c = false ∧ c ≠ 37 ∧ c ≠ 82 ∧ c ≠ 256 := by
  simp only [numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  omega

public theorem Span.first_number {b i cs} (h : Span b i cs)
    (hn : cs ≠ []) (hc : ∀ c ∈ cs, numByte c = true) : numByte (at? b i) = true := by
  cases cs with
  | nil => contradiction
  | cons c cs => rw [h.head]; exact hc c (by simp)

/-- Scanning the unsigned prefix of a numeric token either stops at a
sign/decimal point, or reaches its terminating byte. Both stops exclude
`R` after whitespace. This follows the actual scanner's consumed prefix,
without replacing it by a digit fold or assuming its result. -/
theorem uint_numeric_stops {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i cs) (hc : ∀ c ∈ cs, numByte c = true)
    (he : ¬ (48 ≤ at? b (i+cs.length) ∧ at? b (i+cs.length) ≤ 57))
    (hr : at? b (skipWs b (i+cs.length)) ≠ 82) (v : Nat) (seen : Bool) :
    ∃ n s, Loop.Stops (fun s => pure (uintStep b s)) (UIntState.mk i v seen) n s ∧
      n ≤ cs.length+1 ∧ at? b (skipWs b s.pos) ≠ 82 := by
  induction cs generalizing i v seen with
  | nil =>
    refine ⟨1, ⟨i,v,seen⟩, .done ?_, by simp, ?_⟩
    · simpa [uintStep] using (show
        (if 48 ≤ at? b i && at? b i ≤ 57 then
          ForInStep.yield (UIntState.mk (i+1) (v*10+(at? b i-48)) true)
        else .done ⟨i,v,seen⟩) = .done ⟨i,v,seen⟩ by
          simp only [List.length_nil, Nat.add_zero] at he
          simp [he])
    · simpa using hr
  | cons c cs ih =>
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · obtain ⟨n,s,hs,hn,hr⟩ := ih h.tail
        (fun d hd => hc d (by simp [hd]))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr)
        (v*10+(c-48)) true
      refine ⟨n+1,s, .yield ?_ hs, by simpa using Nat.add_le_add_right hn 1, hr⟩
      simp [uintStep, h.head, hd.1, hd.2]
    · have hp := number_byte (hc c (by simp))
      have hw : skipWs b i = i := skipWs_fixed_point (by rw [h.head]; exact hp.2.1)
        (by rw [h.head]; exact hp.2.2.1)
      refine ⟨1,⟨i,v,seen⟩,.done ?_,by simp,?_⟩
      · simp [uintStep, h.head, hd]
      · simpa [hw, h.head] using hp.2.2.2.1

public theorem tryRef_numeric_none {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i cs) (hn : cs ≠ []) (hc : ∀ c ∈ cs, numByte c = true)
    (he : EndByte (at? b (i+cs.length)))
    (hr : at? b (skipWs b (i+cs.length)) ≠ 82) : tryRef b i = none := by
  have hp := number_byte (h.first_number hn hc)
  have hw := skipWs_fixed_point hp.2.1 hp.2.2.1
  obtain ⟨n,s,hs,hsize,hstop⟩ := uint_numeric_stops h hc
    (not_number_not_digit he.not_number) hr 0 false
  have hh := Loop.forIn_range_stops_exact hs (b.size+1) (by have := h.bound; omega)
  unfold tryRef
  rw [hw]
  unfold parseUInt
  rw [hh]
  cases hseen : s.seen <;> simp [hstop, hseen]

end LeanTex.Core.PdfLex
