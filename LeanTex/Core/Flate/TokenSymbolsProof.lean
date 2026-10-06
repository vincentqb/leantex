import LeanTex.Core.Flate.TokenSymbols

namespace LeanTex.Core.Flate

/-- The wire code and its extra bits cover the entire requested value. These
are format bounds, independent of any input or Huffman frequencies. -/
def SymbolIn (bases extras : Array Nat) (symbol value : Nat) : Prop :=
  symbol < bases.size ∧ symbol < extras.size ∧
    extras[symbol]?.getD 0 ≤ 13 ∧ bases[symbol]?.getD 0 ≤ value ∧
    value - bases[symbol]?.getD 0 < 2 ^ (extras[symbol]?.getD 0)

instance (bases extras : Array Nat) (symbol value : Nat) :
    Decidable (SymbolIn bases extras symbol value) := by
  unfold SymbolIn
  infer_instance

set_option maxRecDepth 8192 in
/-- Exhaust the RFC's complete finite length alphabet, not a sample of
compressed inputs. Kernel reduction checks the production lookup table. -/
private theorem length_alphabet_contract :
    ∀ n : Fin 259, 3 ≤ n.val →
      SymbolIn lenBase lenExtra (lenSymTab[n.val]?.getD 0) n.val := by
  decide +kernel

theorem length_symbol_contract (len : Nat) (hl : 3 ≤ len ∧ len ≤ 258) :
    SymbolIn lenBase lenExtra (lenSymTab[len]?.getD 0) len :=
  length_alphabet_contract ⟨len, by omega⟩ hl.1

set_option maxRecDepth 8192 in
private theorem distance_low_contract :
    ∀ n : Fin 257, 0 < n.val →
      SymbolIn distBase distExtra (distSymTab1[n.val]?.getD 0) n.val := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Every high-distance bucket fits within one RFC distance code. Checking
the bucket's two endpoints covers all 128 distances inside it. -/
private theorem distance_bucket_contract :
    ∀ k : Fin 256, 2 ≤ k.val →
      let s := distSymTab2[k.val]?.getD 0
      s < distBase.size ∧ s < distExtra.size ∧ distExtra[s]?.getD 0 ≤ 13 ∧
        distBase[s]?.getD 0 ≤ k.val * 128 + 1 ∧
        k.val * 128 + 128 - distBase[s]?.getD 0 < 2 ^ (distExtra[s]?.getD 0) := by
  decide +kernel

def distanceSymbol (dist : Nat) : Nat :=
  if dist ≤ 256 then distSymTab1[dist]?.getD 0
  else distSymTab2[(dist - 1) / 128]?.getD 0

theorem distance_symbol_contract (dist : Nat) (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    SymbolIn distBase distExtra (distanceSymbol dist) dist := by
  unfold distanceSymbol
  split
  · exact distance_low_contract ⟨dist, by omega⟩ (by change 0 < dist; omega)
  · have hk : (dist - 1) / 128 < 256 := by omega
    have h := distance_bucket_contract ⟨(dist - 1) / 128, hk⟩
      (by change 2 ≤ (dist - 1) / 128; omega)
    dsimp only at h
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩ <;> omega

/-- The encoder's scalar token unpacking selects the code whose proven span
contains the original distance. -/
theorem matchOf_exact (len dist : Nat) (hl : 3 ≤ len ∧ len ≤ 258)
    (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    matchOf (matchToken len dist) = (len, dist, distanceSymbol dist) := by
  have hf := matchToken_fields_exact len dist hl hd
  have hb : (matchToken len dist &&& 32767).toNat = dist - 1 := by omega
  simp only [matchOf, hf.1, UInt32.toNat_shiftRight,
    UInt32.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow,
    hb, Nat.sub_add_cancel hd.1, distanceSymbol]

end LeanTex.Core.Flate
