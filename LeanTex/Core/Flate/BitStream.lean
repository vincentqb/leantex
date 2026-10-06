module

public import LeanTex.Core.Flate.BitWriter

namespace LeanTex.Core.Flate

/-- A zero-width extra field consumes neither bits nor a writer operation. -/
public def Bw.pushExtra (w : Bw) (value width : Nat) : Bw :=
  if 0 < width then w.push value width else w

namespace BitStream

/-- Shared array-writing loop. Specialization retains the scalar writer state
for each concrete emitter; proofs read this loop through its append equation. -/
@[specialize] public def write {α : Type} (emit : Bw → α → Bw) (entries : Array α)
    (initial : Bw) : Bw := Id.run do
  let mut w := initial
  for entry in entries do
    w := emit w entry
  return w

theorem write_empty_id {α : Type} (emit : Bw → α → Bw) (w : Bw) :
    write emit #[] w = w := rfl

theorem write_push_exact {α : Type} (emit : Bw → α → Bw) (entries : Array α)
    (w : Bw) (entry : α) :
    write emit (entries.push entry) w = emit (write emit entries w) entry := by
  simp only [write, ← Array.forIn_toList, Array.toList_push,
    List.forIn_pure_yield_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

end BitStream
end LeanTex.Core.Flate
