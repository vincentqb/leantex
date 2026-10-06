module

import all LeanTex.Core.PdfObj
import LeanTex.Core.LoopProgress
import Init.Data.Array.Lemmas

namespace LeanTex.Core.PdfRead.ObjReader

theorem accept_empty (v : Obj) (i : Nat) :
    accept #[] v i = .done (.result (.ok (v,i))) := rfl

private theorem set_last_push {α : Type} (xs : Array α) (a b : α) :
    (xs.push a).set! ((xs.push a).size-1) b = xs.push b := by
  simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push]

theorem accept_array (stack : Array Frame) (xs : Array Obj) (v : Obj) (i : Nat) :
    accept (stack.push (.arr xs)) v i =
      .yield (.scan (stack.push (.arr (xs.push v))) i) := by
  simp only [accept, Array.back?_push, set_last_push]

theorem accept_key (stack : Array Frame) (es : Array (String × Obj)) (k : String) (i : Nat) :
    accept (stack.push (.dct es none)) (.name k) i =
      .yield (.scan (stack.push (.dct es (some k))) i) := by
  simp only [accept, Array.back?_push, set_last_push]

theorem accept_value (stack : Array Frame) (es : Array (String × Obj))
    (k : String) (v : Obj) (i : Nat) :
    accept (stack.push (.dct es (some k))) v i =
      .yield (.scan (stack.push (.dct (es.push (k,v)) none)) i) := by
  simp only [accept, Array.back?_push, set_last_push]

/-- A finite execution of the actual transition function, retaining its
last `yield` or `done`. Its index counts transitions, so container proofs
also supply the byte-bounded loop with an adequate iteration budget. -/
inductive Runs (b : ByteArray) : State → Nat → ForInStep State → Prop
  | last {s r} : step b s = r → Runs b s 1 r
  | cons {s t n r} : step b s = .yield t → Runs b t n r → Runs b s (n+1) r

theorem Runs.yields {b : ByteArray} {s t : State} {n : Nat}
    (h : Runs b s n (.yield t)) :
    Loop.Yields (fun s => pure (step b s)) s n t := by
  generalize hr : ForInStep.yield t = r at h
  induction h with
  | last hs =>
    exact .cons (hs.trans hr.symm) .nil
  | cons hs _ ih => exact .cons hs (ih hr)

theorem Runs.stops {b : ByteArray} {s t : State} {n : Nat}
    (h : Runs b s n (.done t)) :
    Loop.Stops (fun s => pure (step b s)) s n t := by
  generalize hr : ForInStep.done t = r at h
  induction h with
  | last hs => exact .done (hs.trans hr.symm)
  | cons hs _ ih => exact .yield hs (ih hr)

theorem Runs.prepend {b : ByteArray} {s t : State} {r : ForInStep State} {m n : Nat}
    (h : Loop.Yields (fun s => pure (step b s)) s m t) (g : Runs b t n r) :
    Runs b s (m+n) r := by
  induction h with
  | nil => simpa using g
  | cons hs _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Runs.cons hs (ih g)

theorem Runs.trans {b : ByteArray} {s t : State} {r : ForInStep State} {m n : Nat}
    (h : Runs b s m (.yield t)) (g : Runs b t n r) : Runs b s (m+n) r :=
  g.prepend h.yields

/-- A successful trace is a theorem about the public reader, including
its actual bounded `forIn` loop and its early return. -/
theorem parseVal_of_runs {b : ByteArray} {i j n : Nat} {o : Obj}
    (h : Runs b (.scan #[] i) n (.done (.result (.ok (o,j)))))
    (hn : n ≤ b.size+2) : parseVal b i = .ok (o,j) := by
  unfold parseVal
  rw [Loop.forIn_range_stops_exact h.stops (b.size+2) hn]

end LeanTex.Core.PdfRead.ObjReader
