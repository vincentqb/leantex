import LeanTex.Core.Flate.FieldStream
import LeanTex.Core.Flate.BitStreamProof

namespace LeanTex.Core.Flate.FieldStream

theorem write_contract (width : Nat) (values : Array Nat) (w : Bw)
    (hw : w.Valid) (hn : width ≤ 16) :
    (write width values w).Valid ∧ (write width values w).Extends w :=
  BitStream.write_contract _ values w hw (fun _ _ w hw =>
    ⟨push_valid w _ width hw hn, push_extends_exact w _ width hw hn⟩)

private theorem push_induction {α : Type} {P : Array α → Prop}
    (empty : P #[]) (push : ∀ xs a, P xs → P (xs.push a)) (xs : Array α) : P xs := by
  have h : ∀ ys : List α, P ys.reverse.toArray := by
    intro ys
    induction ys with
    | nil => exact empty
    | cons a ys ih => simpa using push ys.reverse.toArray a ih
  simpa using h xs.toList.reverse

theorem write_steps_exact (width count : Nat) (values : Array Nat) (w : Bw) (data : ByteArray)
    (hw : w.Valid) (hn : width ≤ 16)
    (hv : ∀ v ∈ values.toList, v < 2 ^ width) (hc : values.size ≤ count)
    (hr : (write width values w).Realizes data) :
    DecodeLoop.Steps (readStep width count) (#[], {data, bitPos := w.position})
      values.size (values, {data, bitPos := (write width values w).position}) := by
  induction values using push_induction with
  | empty => exact .refl _
  | @push values value ih =>
    have hh := write_contract width values w hw hn
    have hx := push_extends_exact (write width values w) value width hh.1 hn
    have hwr : write width (values.push value) w = (write width values w).push value width :=
      BitStream.write_push_exact _ values w value
    rw [hwr] at hr ⊢
    have hs := ih (fun v hm => hv v (by simp only [Array.toList_push,
      List.mem_append, List.mem_singleton]; exact Or.inl hm))
      (by simp only [Array.size_push] at hc; omega)
      (hr.prefix hx)
    have hb := push_bits_exact (write width values w) data value width hh.1 hn
      (hv value (by simp)) hr
    rw [Array.size_push]
    apply DecodeLoop.Steps.snoc hs
    simp only [readStep, show ¬ values.size ≥ count by simp only [Array.size_push] at hc; omega,
      ite_false, hb]

theorem read_write_exact (width : Nat) (values : Array Nat) (w : Bw) (data : ByteArray)
    (hw : w.Valid) (hn : width ≤ 16)
    (hv : ∀ v ∈ values.toList, v < 2 ^ width)
    (hr : (write width values w).Realizes data) :
    read width values.size {data, bitPos := w.position} =
      .ok (values, {data, bitPos := (write width values w).position}) := by
  have hs := write_steps_exact width values.size values w data hw hn hv (Nat.le_refl _) hr
  have hd : DecodeLoop.Finishes (readStep width values.size)
      (values, {data, bitPos := (write width values w).position}) 1
      (values, {data, bitPos := (write width values w).position}) :=
    .done (by simp only [readStep, ge_iff_le, Nat.le_refl, ite_true])
  have hf := hs.finish hd
  exact DecodeLoop.run_exact _ _ _ _ (values.size + 1) "deflate: truncated" hf (by omega)

end LeanTex.Core.Flate.FieldStream
