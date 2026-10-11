module

public import LeanTex.Core.Color
public import LeanTex.Core.Oklab
public import LeanTex.Core.ContrastRatio

/-!
The solver for colours the engine derives itself: a role names a hue, and a
ground chooses its lightness. A colour a document states ships as stated and
is never solved here (the document's contrast report names a pairing that
falls short); what the engine generates (`SeedPalette`) takes the tone that
meets its ground. Sources, and the rule taken from each:

* https://m3.material.io/styles/color/system/how-the-system-works —
  Material 3 tonal palettes: a key colour fixes hue and chroma, and each
  role takes a *tone* (lightness) chosen against its surface so the pair
  meets its contrast.
* https://www.radix-ui.com/colors — one named scale realizes differently
  on light and dark grounds; the hue is the identity, the lightness the
  ground's choice.
* https://www.w3.org/TR/css-color-4/#gamut-mapping — a colour outside the
  gamut loses chroma at constant lightness and hue (`Oklab.Okl.gamutMap`),
  never a per-channel clip that turns its hue.
* https://www.w3.org/TR/WCAG22/#contrast-minimum — the requirement judged,
  `contrastMilli`, the WCAG relative-luminance ratio: monotone in lightness
  moving away from the ground, which is what the bisection rides. Every
  answer re-judges the requirement itself, so no monotonicity argument is
  load-bearing.
-/

namespace LeanTex.Core.ContrastSolve

open LeanTex.Core.Ir LeanTex.Core.Contrast

/-- Bisection on structural fuel between a failing value and a passing one,
returning the passing side of the boundary; 60 halvings close the 10¹⁸
lightness axis. -/
public def bisect (pass : Int → Bool) : Nat → Int → Int → Int
  | 0, _, p => p
  | fuel + 1, f, p =>
    let mid := (f + p) / 2
    if mid == f || mid == p then p
    else if pass mid then bisect pass fuel f mid
    else bisect pass fuel mid p

/-- **A bisection answers a passing value** when it starts from one. -/
public theorem bisect_pass (pass : Int → Bool) :
    ∀ (fuel : Nat) (f p : Int), pass p = true → pass (bisect pass fuel f p) = true
  | 0, _, _, h => h
  | fuel + 1, f, p, h => by
    simp only [bisect]
    split
    · exact h
    · split
      · exact bisect_pass pass fuel _ _ ‹_›
      · exact bisect_pass pass fuel _ _ h

/-- The candidate at lightness `L` (the `labOf` 10¹⁸ scale) with chroma
scaled to `f`% of the colour's own, gamut-mapped at its lightness and hue. -/
private def realizeCand (lab : Oklab.Lab) (f : Nat) (L : Int) : Color :=
  (Oklab.Okl.gamutMap { L, a := lab.a, b := lab.b, f := f * Oklab.fracOne / 100 }).toColor

/-- The `labOf` lightness of pure white, the top of the searched axis. -/
private def realizeLMax : Int := 10 ^ 18

/-- The nearest passing lightness at one chroma fraction: both directions
searched, the boundary nearer the colour's own lightness taken; `none` when
neither end of the axis reaches the requirement at this chroma. -/
private def realizeAt (req : Nat) (ground : Color) (lab : Oklab.Lab)
    (f : Nat) : Option Color :=
  let pass := fun L => decide (req ≤ contrastMilli (realizeCand lab f L) ground)
  if pass lab.L then some (realizeCand lab f lab.L)
  else
    let up := if pass realizeLMax then some (bisect pass 60 lab.L realizeLMax) else none
    let down := if pass 0 then some (bisect pass 60 lab.L 0) else none
    match up, down with
    | some u, some d =>
      some (realizeCand lab f (if u - lab.L ≤ lab.L - d then u else d))
    | some u, none => some (realizeCand lab f u)
    | none, some d => some (realizeCand lab f d)
    | none, none => none

/-- The nearest legible colour on a ground: the colour itself when the
pair already meets `req` (milli-ratio, `contrastMilli`'s scale); otherwise
the nearest lightness at its hue and chroma that does, reducing chroma
toward the neutral axis when the full-chroma axis never reaches it; `none`
when nothing does. A colour declared in DeviceCMYK is never realized: that
would repaint the declaration in sRGB and drop its print components. -/
public def realizeNearest (req : Nat) (ground c : Color) : Option Color :=
  if req ≤ contrastMilli c ground then some c
  else if c.cmyk.isSome then none
  else
    (([100, 75, 50, 25, 0] : List Nat).findSome? fun f =>
        realizeAt req ground (Oklab.labOf c) f).bind fun cand =>
      if req ≤ contrastMilli cand ground then some cand else none

/-- The solver's answer meets the requirement: every return is guarded by
the judged quantity itself. -/
public theorem realizeNearest_meets {req : Nat} {ground c c' : Color}
    (h : realizeNearest req ground c = some c') : req ≤ contrastMilli c' ground := by
  unfold realizeNearest at h
  split at h
  next hp => cases h; exact hp
  next =>
    split at h
    next => cases h
    next =>
      match hb : ([100, 75, 50, 25, 0] : List Nat).findSome? fun f =>
          realizeAt req ground (Oklab.labOf c) f with
      | none => rw [hb] at h; cases h
      | some cand =>
        rw [hb, Option.bind_some] at h
        split at h
        next hp => cases h; exact hp
        next => cases h

private theorem realizeAt_cand {req : Nat} {ground : Color} {lab : Oklab.Lab} {f : Nat}
    {c : Color} (h : realizeAt req ground lab f = some c) : ∃ L, c = realizeCand lab f L := by
  unfold realizeAt at h
  dsimp only at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · split at h <;> (try cases h) <;> exact ⟨_, rfl⟩

/-- **The solver holds hue**: what it returns is the colour itself, or a
colour at the colour's own Oklab direction with no more than its chroma,
gamut-mapped — a lighter or darker tone, never a turned one. -/
public theorem realize_hue_between {req : Nat} {ground c c' : Color}
    (h : realizeNearest req ground c = some c') :
    c' = c ∨ ∃ o : Oklab.Okl, o.a = (Oklab.labOf c).a ∧ o.b = (Oklab.labOf c).b ∧
      o.f ≤ Oklab.fracOne ∧ c' = o.toColor := by
  unfold realizeNearest at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h
    · right
      match hb : ([100, 75, 50, 25, 0] : List Nat).findSome? fun f =>
          realizeAt req ground (Oklab.labOf c) f with
      | none => rw [hb] at h; cases h
      | some cand =>
        rw [hb, Option.bind_some] at h
        split at h
        · cases h
          obtain ⟨f, hf, hr⟩ := List.exists_of_findSome?_eq_some hb
          obtain ⟨L, rfl⟩ := realizeAt_cand hr
          have hf100 : f ≤ 100 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
            omega
          have hg := Oklab.Okl.gamutMap_between
            { L, a := (Oklab.labOf c).a, b := (Oklab.labOf c).b, f := f * Oklab.fracOne / 100 }
          refine ⟨_, hg.2.1, hg.2.2.1, ?_, rfl⟩
          have hle : f * Oklab.fracOne / 100 ≤ Oklab.fracOne := by
            have : f * Oklab.fracOne ≤ 100 * Oklab.fracOne := Nat.mul_le_mul_right _ hf100
            omega
          exact Nat.le_trans hg.2.2.2.1 hle
        · cases h

/-- ΔEOK² between two colours, at `labOf`'s scale squared. -/
public def deltaEOkSq (c c' : Color) : Int := Oklab.distSq (Oklab.labOf c) (Oklab.labOf c')

end LeanTex.Core.ContrastSolve
