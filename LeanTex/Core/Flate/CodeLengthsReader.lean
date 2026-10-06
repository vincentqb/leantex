module

import all LeanTex.Core.Flate.CodeLengths
import all LeanTex.Core.Flate.Huffman
public import LeanTex.Core.Flate.Huffman
import LeanTex.Core.Flate.DecodeLoop

namespace LeanTex.Core.Flate.CodeLengths

/-- Append the run read from an RFC 1951 code-length entry. -/
def appendRun (out : Array Nat) (value count : Nat) : Array Nat := Id.run do
  let mut out := out
  for _ in [0:count] do
    out := out.push value
  return out

/-- Read one entry of the dynamic table prelude, including its extra bits. -/
def readEntry (table : Huff) (state : Array Nat × Br) :
    Except String (Array Nat × Br) := do
  let some (symbol, r) := table.decode state.2
    | .error "deflate: truncated"
  if symbol < 16 then
    return (state.1.push symbol, r)
  else if symbol == 16 then
    let some (extra, r) := r.bits 2 | .error "deflate: truncated"
    let some previous := state.1.back?
      | .error "deflate: repeat with no previous length"
    return (appendRun state.1 previous (extra + 3), r)
  else if symbol == 17 then
    let some (extra, r) := r.bits 3 | .error "deflate: truncated"
    return (appendRun state.1 0 (extra + 3), r)
  else
    let some (extra, r) := r.bits 7 | .error "deflate: truncated"
    return (appendRun state.1 0 (extra + 11), r)

/-- The state boundary of the bounded dynamic table reader. -/
def readStep (table : Huff) (count : Nat) (state : Array Nat × Br) :
    Except String (Sum (Array Nat × Br) (Array Nat × Br)) := do
  if state.1.size ≥ count then
    if state.1.size = count then return .inl state
    else .error "deflate: code lengths overrun their table"
  else
    return .inr (← readEntry table state)

/-- The production dynamic table reader. Every entry adds at least one length;
one further iteration observes the completed table. -/
public def read (table : Huff) (count : Nat) (r : Br) : Except String (Array Nat × Br) :=
  DecodeLoop.run (count + 1) (readStep table count) (#[], r)
    "deflate: code lengths overrun their table"

/-- A table prefix, indexed by how many lengths the reader has reconstructed. -/
def Prefix (seq : Array Nat) (count : Nat) (out : Array Nat) : Prop :=
  out.size = count ∧ count ≤ seq.size ∧ ∀ i < count, out[i]? = seq[i]?

theorem Prefix.push {seq out : Array Nat} {p value : Nat}
    (hp : Prefix seq p out) (hi : p < seq.size) (hv : seq[p]?.getD 0 = value) :
    Prefix seq (p + 1) (out.push value) := by
  refine ⟨by simp [hp.1], by omega, ?_⟩
  intro i hi'
  rw [Array.getElem?_push, hp.1]
  by_cases hip : i < p
  · rw [ite_eq_right (show i ≠ p by omega)]
    exact hp.2.2 i hip
  · have he : i = p := by omega
    subst i
    rw [ite_eq_left rfl]
    rw [getElem?_pos seq p hi] at hv ⊢
    simp only [Option.getD_some] at hv
    exact congrArg some hv.symm

theorem appendRun_prefix_exact {seq out : Array Nat} {p count value : Nat}
    (hp : Prefix seq p out) (hr : Run seq p count value) :
    Prefix seq (p + count) (appendRun out value count) := by
  change Prefix seq (p + count)
    (forIn [0:count] out (fun _ s => pure (.yield (s.push value))) : Id (Array Nat)).run
  apply Progress.forIn_range_exact (fun k s => Prefix seq (p + k) s)
    (Prefix seq (p + count)) _ 0 count out (Nat.zero_le _) (by simpa using hp)
    ?_ (fun _ h => h)
  intro k _ hk s hs
  change Prefix seq (p + (k + 1)) (s.push value)
  simpa only [Nat.add_assoc] using hs.push (by have := hr.1; omega) (hr.2 k hk)

theorem Prefix.back {seq out : Array Nat} {p value : Nat}
    (hp : Prefix seq p out) (hpos : 0 < p)
    (hv : seq[p - 1]?.getD 0 = value) : out.back? = some value := by
  rw [Array.back?_eq_getElem?, hp.1, hp.2.2 _ (by omega)]
  rw [getElem?_pos seq (p - 1) (by have := hp.2.1; omega)] at hv ⊢
  simp only [Option.getD_some] at hv
  exact congrArg some hv

/-- One actual RLE reader step reconstructs exactly the run certified by
`CodeLengths.Step`. The premises are the reader's concrete byte equations. -/
theorem readEntry_exact {seq out : Array Nat} {p q : Nat} {entry : Entry}
    (table : Huff) (r afterCode afterExtra : Br)
    (hp : Prefix seq p out) (hs : Step seq p entry q)
    (hc : table.decode r = some (entry.1, afterCode))
    (he : afterCode.bits entry.2.2 = some (entry.2.1, afterExtra)) :
    ∃ out', readEntry table (out, r) = .ok (out', afterExtra) ∧ Prefix seq q out' := by
  cases hs with
  | literal value hv hr =>
    have hz : afterExtra = afterCode := by
      have hb : afterCode.bits 0 = some (0, afterCode) := by
        simp [Br.bits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
      rw [hb] at he
      exact (Prod.mk.inj (Option.some.inj he)).2.symm
    subst afterExtra
    refine ⟨out.push value, ?_, hp.push (by have := hr.1; omega) ?_⟩
    · simp [readEntry, hc, hv, pure, Except.pure]
    · simpa using hr.2 0 (by omega)
  | repeat16 count value hb hpos hprev hr =>
    refine ⟨appendRun out value count, ?_, appendRun_prefix_exact hp hr⟩
    have hcount : count - 3 + 3 = count := by omega
    simp [readEntry, hc, he, hp.back hpos hprev, hcount, pure, Except.pure]
  | zeros17 count hb hr =>
    refine ⟨appendRun out 0 count, ?_, appendRun_prefix_exact hp hr⟩
    have hcount : count - 3 + 3 = count := by omega
    simp [readEntry, hc, he, hcount, pure, Except.pure]
  | zeros18 count hb hr =>
    refine ⟨appendRun out 0 count, ?_, appendRun_prefix_exact hp hr⟩
    have hcount : count - 11 + 11 = count := by omega
    simp [readEntry, hc, he, hcount, pure, Except.pure]

end LeanTex.Core.Flate.CodeLengths
