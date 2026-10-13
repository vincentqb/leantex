module

public import LeanTex.Core.Flate
import all LeanTex.Core.Flate

namespace LeanTex.Core.Flate

private theorem hexDigit_utf8Size (k : Nat) :
    (['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E',
      'F'][k]?.getD '0').utf8Size = 1 := by
  cases h : (['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E',
      'F'] : List Char)[k]? with
  | none => rfl
  | some c =>
    have hm := List.mem_of_getElem? h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem hexFold_utf8ByteSize (l : List Nat) (s : String) (v : UInt64) :
    (List.foldl
      (fun b _ =>
        (String.singleton
            (['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E',
              'F'][b.snd.toNat % 16]?.getD '0') ++ b.fst,
          b.snd / 16))
      (s, v) l).fst.utf8ByteSize = s.utf8ByteSize + l.length := by
  induction l generalizing s v with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [String.utf8ByteSize_append, String.utf8ByteSize_singleton, hexDigit_utf8Size]
    omega

private theorem hex16_utf8ByteSize (x : UInt64) : (hex16 x).utf8ByteSize = 16 := by
  unfold hex16
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  simp
  simpa using hexFold_utf8ByteSize (List.range' 0 16) "" x

public theorem contentKey_size_exact (b : ByteArray) : (contentKey b).toUTF8.size = 32 := by
  simp [contentKey, hex16_utf8ByteSize]

end LeanTex.Core.Flate
