module

public import LeanTex.Core.Color
public import LeanTex.Core.Oklab
public import LeanTex.Core.ContrastRatio

/-! The solver for colours the engine derives: a role names a hue and its ground chooses the
lightness (Material 3's tonal rule, Radix's scales, CSS Color 4 gamut mapping). -/

namespace LeanTex.Core.ContrastSolve

open LeanTex.Core.Ir LeanTex.Core.Contrast

/-- Bisection between a failing value and a passing one, returning the passing side; 60 halvings
close the 10¹⁸ axis. -/
public def bisect (pass : Int → Bool) : Nat → Int → Int → Int
  | 0, _, p => p
  | fuel + 1, f, p =>
    let mid := (f + p) / 2
    if mid == f || mid == p then p
    else if pass mid then bisect pass fuel f mid
    else bisect pass fuel mid p

public theorem bisect_contract (pass : Int → Bool) :
    ∀ (fuel : Nat) (f p : Int), pass p = true → pass (bisect pass fuel f p) = true
  | 0, _, _, h => h
  | fuel + 1, f, p, h => by
    simp only [bisect]
    split
    · exact h
    · split
      · exact bisect_contract pass fuel _ _ ‹_›
      · exact bisect_contract pass fuel _ _ h

/-- The passing side of the boundary nearest a guess: bisected within `guess ± span` where that
bracket straddles it, else over the whole axis. -/
public def bisectNear (pass : Int → Bool) (fuel : Nat) (f p guess span : Int) : Int :=
  let dir : Int := if p < f then -1 else 1
  let a := guess - dir * span
  let b := guess + dir * span
  if !pass a && pass b then bisect pass fuel a b else bisect pass (fuel + 8) f p

public theorem bisectNear_contract (pass : Int → Bool) (fuel : Nat) (f p guess span : Int)
    (hp : pass p = true) : pass (bisectNear pass fuel f p guess span) = true := by
  unfold bisectNear
  dsimp only
  split <;> split
  all_goals first
    | exact bisect_contract pass (fuel + 8) f p hp
    | (rename_i h
       simp only [Bool.and_eq_true] at h
       exact bisect_contract pass fuel _ _ h.2)

/-- The Oklab lightness of the grey whose WCAG luminance is `y` (10⁻⁷), at `labOf`'s scale. -/
public def greyLightness (y : Nat) : Int := (Oklab.icbrt (min y 10000000 * 10 ^ 11) : Int) * 10 ^ 12

/-- The luminance (10⁻⁷) a colour darker than `ground` has at `target` contrast to it, or a
lighter one's. -/
public def luminanceAt (ground : Color) (target : Nat) (lighter : Bool) : Nat :=
  let yg := luminance ground + 500000
  if lighter then (yg * target / 1000) - 500000 else (yg * 1000 / max target 1) - 500000

/-- The candidate at lightness `L` with `f`% of the colour's chroma, brought into the gamut. -/
private def realizeCand (lab : Oklab.Lab) (f : Nat) (L : Int) : Color :=
  (Oklab.Okl.toGamut { L, a := lab.a, b := lab.b, f := f * Oklab.fracOne / 100 }).toColor

/-- The `labOf` lightness of pure white, the top of the searched axis. -/
private def realizeLMax : Int := 10 ^ 18

/-- The passing lightness nearest `L0` at one chroma fraction, both directions searched; `none`
when neither end passes. -/
private def realizeFrom (req : Nat) (ground : Color) (lab : Oklab.Lab) (f : Nat) (L0 : Int) :
    Option Color :=
  let pass := fun L => decide (req ≤ contrastMilli (realizeCand lab f L) ground)
  if pass L0 then some (realizeCand lab f L0)
  else
    let up := if pass realizeLMax then some (bisect pass 60 L0 realizeLMax) else none
    let down := if pass 0 then some (bisect pass 60 L0 0) else none
    match up, down with
    | some u, some d =>
      some (realizeCand lab f (if u - L0 ≤ L0 - d then u else d))
    | some u, none => some (realizeCand lab f u)
    | none, some d => some (realizeCand lab f d)
    | none, none => none

/-- The nearest passing lightness at one chroma fraction, from the colour's own. -/
private def realizeAt (req : Nat) (ground : Color) (lab : Oklab.Lab) (f : Nat) : Option Color :=
  realizeFrom req ground lab f lab.L

/-- The nearest legible colour on a ground: the colour itself when it passes, else the nearest
passing one at its hue, chroma reduced where needed; `none` when nothing passes or a failing
colour is DeviceCMYK. -/
public def realizeNearest (req : Nat) (ground c : Color) : Option Color :=
  if req ≤ contrastMilli c ground then some c
  else if c.cmyk.isSome then none
  else
    (([100, 75, 50, 25, 0] : List Nat).findSome? fun f =>
        realizeAt req ground (Oklab.labOf c) f).bind fun cand =>
      if req ≤ contrastMilli cand ground then some cand else none

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

private theorem realizeFrom_cand {req : Nat} {ground : Color} {lab : Oklab.Lab} {f : Nat}
    {L0 : Int} {c : Color} (h : realizeFrom req ground lab f L0 = some c) :
    ∃ L, c = realizeCand lab f L := by
  unfold realizeFrom at h
  dsimp only at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · split at h <;> (try cases h) <;> exact ⟨_, rfl⟩

private theorem realizeAt_cand {req : Nat} {ground : Color} {lab : Oklab.Lab} {f : Nat}
    {c : Color} (h : realizeAt req ground lab f = some c) : ∃ L, c = realizeCand lab f L :=
  realizeFrom_cand h

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
          have hg := Oklab.Okl.toGamut_between
            { L, a := (Oklab.labOf c).a, b := (Oklab.labOf c).b, f := f * Oklab.fracOne / 100 }
          refine ⟨_, hg.2.1, hg.2.2.1, ?_, rfl⟩
          have hle : f * Oklab.fracOne / 100 ≤ Oklab.fracOne := by
            have : f * Oklab.fracOne ≤ 100 * Oklab.fracOne := Nat.mul_le_mul_right _ hf100
            omega
          exact Nat.le_trans hg.2.2.2.1 hle
        · cases h

/-- ΔEOK² between two colours, at `labOf`'s scale squared. -/
public def deltaEOkSq (c c' : Color) : Int := Oklab.distSq (Oklab.labOf c) (Oklab.labOf c')

/-- The `labOf` lightness a colour takes over another page: as far from it as from its own, on
its far side. -/
public def reflectL (home page c : Color) : Int :=
  max 0 (min realizeLMax ((Oklab.labOf page).L + ((Oklab.labOf home).L - (Oklab.labOf c).L)))

/-- A colour carried to a page of the other polarity: its lightness reflected, its hue and
chroma held, brought into the gamut. -/
public def reflect (home page c : Color) : Color :=
  realizeCand (Oklab.labOf c) 100 (reflectL home page c)

/-- A colour adapted to a ground of another scheme: reflected to the scheme's page, then
realized at `req` on the ground. -/
public def adapt (req : Nat) (home page c ground : Color) : Option Color :=
  let lab := Oklab.labOf c
  let L0 := reflectL home page c
  (([100, 75, 50, 25, 0] : List Nat).findSome? fun f => realizeFrom req ground lab f L0).bind
    fun cand => if req ≤ contrastMilli cand ground then some cand else none

public theorem adapt_between {req : Nat} {home page c ground c' : Color}
    (h : adapt req home page c ground = some c') :
    req ≤ contrastMilli c' ground ∧
      ∃ o : Oklab.Okl, o.a = (Oklab.labOf c).a ∧ o.b = (Oklab.labOf c).b ∧
        o.f ≤ Oklab.fracOne ∧ c' = o.toColor := by
  unfold adapt at h
  dsimp only at h
  match hb : ([100, 75, 50, 25, 0] : List Nat).findSome? fun f =>
      realizeFrom req ground (Oklab.labOf c) f (reflectL home page c) with
  | none => rw [hb] at h; cases h
  | some cand =>
    rw [hb, Option.bind_some] at h
    split at h
    · cases h
      refine ⟨‹_›, ?_⟩
      obtain ⟨f, hf, hr⟩ := List.exists_of_findSome?_eq_some hb
      obtain ⟨L, rfl⟩ := realizeFrom_cand hr
      have hf100 : f ≤ 100 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        omega
      have hg := Oklab.Okl.toGamut_between
        { L, a := (Oklab.labOf c).a, b := (Oklab.labOf c).b, f := f * Oklab.fracOne / 100 }
      refine ⟨_, hg.2.1, hg.2.2.1, ?_, rfl⟩
      have hle : f * Oklab.fracOne / 100 ≤ Oklab.fracOne := by
        have : f * Oklab.fracOne ≤ 100 * Oklab.fracOne := Nat.mul_le_mul_right _ hf100
        omega
      exact Nat.le_trans hg.2.2.2.1 hle
    · cases h

public theorem reflect_between (home page c : Color) :
    ∃ o : Oklab.Okl, o.a = (Oklab.labOf c).a ∧ o.b = (Oklab.labOf c).b ∧
      o.f ≤ Oklab.fracOne ∧ reflect home page c = o.toColor := by
  have hg := Oklab.Okl.toGamut_between
    { L := reflectL home page c, a := (Oklab.labOf c).a, b := (Oklab.labOf c).b,
      f := 100 * Oklab.fracOne / 100 }
  exact ⟨_, hg.2.1, hg.2.2.1,
    Nat.le_trans hg.2.2.2.1 (Nat.le_of_eq (Nat.mul_div_cancel_left _ (by decide))), rfl⟩

/-! ## A hue's tone at a floor -/

/-- A chroma past any sRGB colour's (blue's 0.31), so a hue's direction mapped into the gamut
stands on its edge. -/
private def edgeReach : Int := 4 * 10 ^ 17

/-- The tone of hue `h` (millidegrees) at lightness `L` with the most chroma
the gamut holds there. -/
public def edgeAt (h L : Int) : Color :=
  let dir := Oklab.ofLch 0 edgeReach h
  (Oklab.Okl.toGamut { L, a := dir.a, b := dir.b, f := Oklab.fracOne }).toColor

/-- A colour where it clears `req` on every ground. -/
private def clearing (req : Nat) (grounds : List Color) (c : Color) : Option Color :=
  if grounds.all fun g => decide (req ≤ contrastMilli c g) then some c else none

private theorem clearing_contract {req : Nat} {grounds : List Color} {c c' : Color}
    (h : clearing req grounds c = some c') : ∀ g ∈ grounds, req ≤ contrastMilli c' g := by
  unfold clearing at h
  split at h
  · rename_i hp
    cases h
    intro g hg
    exact of_decide_eq_true (List.all_eq_true.mp hp g hg)
  · cases h

/-- Whether the first ground is light: a tone reads on it toward black. -/
private def lightFirst (grounds : List Color) : Bool :=
  match grounds with
  | g :: _ => decide (contrastMilli Color.white g < contrastMilli Color.black g)
  | [] => true

/-- The lightness of the gamut-edge tone of hue `h` nearest the paper that clears `req`: the floor
sets the tone, the gamut the chroma (Material 3's tonal rule at Leonardo's contrast target). -/
public def bandL (req : Nat) (grounds : List Color) (h : Int) : Int :=
  let pass (L : Int) : Bool := (clearing req grounds (edgeAt h L)).isSome
  if lightFirst grounds then bisect pass 60 (10 ^ 18) 0 else bisect pass 60 0 (10 ^ 18)

/-- Hue `h`'s tone at the floor `req` on every ground, so hues at one floor share a lightness band
as Solarized's accents do (https://ethanschoonover.com/solarized/). -/
public def bandOn (req : Nat) (grounds : List Color) (h : Int) : Option Color :=
  clearing req grounds (edgeAt h (bandL req grounds h))

/-- **A band tone clears what it was asked to on every ground.** -/
public theorem bandOn_contract {req : Nat} {grounds : List Color} {h : Int} {c : Color}
    (hv : bandOn req grounds h = some c) : ∀ g ∈ grounds, req ≤ contrastMilli c g :=
  clearing_contract hv

/-! ## The disliked region -/

/-- The disliked region's hues, in millidegrees of OKLCH (`dislikedOk`). -/
public def dislikedLo : Int := 86700

public def dislikedHi : Int := 110400

/-- Material 3's disliked dark yellow-greens (DislikeAnalyzer after Palmer & Schloss, PNAS 2010)
as an OKLCH box holding every 8-bit colour it flags (`scripts/dislike-oracle.lean`). -/
public def disliked (c : Color) : Bool :=
  let l := Oklab.labOf c
  let h := Oklab.hueMilli l.a l.b
  decide (dislikedLo ≤ h) && decide (h ≤ dislikedHi) &&
    decide ((36 * 10 ^ 15) * (36 * 10 ^ 15) ≤ Oklab.chromaSq l) && decide (luminance c ≤ 3343000)

/-- `h` outside the disliked region's hues, else a degree past its warm edge, toward orange as a
darkening yellow turns. -/
public def clearHue (h : Int) : Int :=
  if dislikedLo ≤ h ∧ h ≤ dislikedHi then dislikedLo - 1000 else h

/-- Hue `h`'s band tone at `req`, or, where it stands in the disliked region,
the band tone of the hue just past its warm edge (`clearHue`). -/
public def bandClear (req : Nat) (grounds : List Color) (h : Int) : Option Color :=
  (bandOn req grounds h).bind fun c => if disliked c then bandOn req grounds (clearHue h) else some c

/-- **A cleared band tone clears what it was asked to on every ground.** -/
public theorem bandClear_contract {req : Nat} {grounds : List Color} {h : Int} {c : Color}
    (hv : bandClear req grounds h = some c) : ∀ g ∈ grounds, req ≤ contrastMilli c g := by
  unfold bandClear at hv
  cases hb : bandOn req grounds h with
  | none => simp [hb] at hv
  | some c0 =>
    simp only [hb, Option.bind_some] at hv
    split at hv
    · exact bandOn_contract hv
    · cases hv; exact bandOn_contract hb

end LeanTex.Core.ContrastSolve
