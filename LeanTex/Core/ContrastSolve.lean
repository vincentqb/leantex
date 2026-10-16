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

/-- The passing lightness nearest a failing `from_` on either side of it, bisected at most `fuel`
times toward each end of the axis that passes; a tie goes to the lighter side when `lighter`. -/
public def nearestPass (pass : Int → Bool) (fuel : Nat) (from_ : Int) (lighter : Bool) :
    Option Int :=
  let down := if pass 0 then some (bisect pass fuel from_ 0) else none
  let up := if pass Oklab.lightTop then some (bisect pass fuel from_ Oklab.lightTop) else none
  match down, up with
  | some d, some u =>
    some (if lighter then (if u - from_ ≤ from_ - d then u else d)
      else if from_ - d ≤ u - from_ then d else u)
  | some d, none => some d
  | none, some u => some u
  | none, none => none

public theorem nearestPass_contract {pass : Int → Bool} {fuel : Nat} {from_ : Int}
    {lighter : Bool} {L : Int} (h : nearestPass pass fuel from_ lighter = some L) :
    pass L = true := by
  have hb := bisect_contract pass fuel from_
  unfold nearestPass at h
  by_cases h0 : pass 0 = true <;> by_cases h1 : pass Oklab.lightTop = true <;>
    simp only [h0, h1, ite_true, ite_false, Bool.false_eq_true, Option.some.injEq,
      reduceCtorEq] at h <;> (try split at h) <;> (try split at h) <;>
    first | (subst h; exact hb _ h0) | (subst h; exact hb _ h1)

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

/-- The passing lightness nearest `L0` at one chroma fraction, both directions searched; `none`
when neither end passes. -/
private def realizeFrom (req : Nat) (ground : Color) (lab : Oklab.Lab) (f : Nat) (L0 : Int) :
    Option Color :=
  let pass := fun L => decide (req ≤ contrastMilli (realizeCand lab f L) ground)
  if pass L0 then some (realizeCand lab f L0)
  else (nearestPass pass 60 L0 (lighter := true)).map (realizeCand lab f)

/-- The nearest passing lightness at one chroma fraction, from the colour's own. -/
private def realizeAt (req : Nat) (ground : Color) (lab : Oklab.Lab) (f : Nat) : Option Color :=
  realizeFrom req ground lab f lab.L

/-- The nearest legible colour on a ground: the colour itself when it passes, else the nearest
passing one at the hue it shows, chroma reduced where needed, a screen colour in any model;
`none` when nothing passes. -/
public def realizeNearest (req : Nat) (ground c : Color) : Option Color :=
  if req ≤ contrastMilli c ground then some c
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
  · obtain ⟨L, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨L, rfl⟩

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
  max 0 (min Oklab.lightTop ((Oklab.labOf page).L + ((Oklab.labOf home).L - (Oklab.labOf c).L)))

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

/-- The lightness of the gamut-edge tone of hue `h` nearest the paper that clears `req` and passes
`ok`: the floor and `ok` set the tone, the gamut the chroma (Material 3's tonal rule at Leonardo's
contrast target). -/
public def bandL (req : Nat) (grounds : List Color) (h : Int) (ok : Color → Bool := fun _ => true) :
    Int :=
  let pass (L : Int) : Bool := (clearing req grounds (edgeAt h L)).any ok
  if lightFirst grounds then bisect pass 60 Oklab.lightTop 0 else bisect pass 60 0 Oklab.lightTop

/-- Hue `h`'s tone at the floor `req` on every ground passing `ok`, so hues at one floor share a
lightness band as Solarized's accents do (https://ethanschoonover.com/solarized/). -/
public def bandOn (req : Nat) (grounds : List Color) (h : Int) (ok : Color → Bool := fun _ => true) :
    Option Color :=
  (clearing req grounds (edgeAt h (bandL req grounds h ok))).filter ok

/-- **A band tone clears what it was asked to on every ground and passes `ok`.** -/
public theorem bandOn_contract {req : Nat} {grounds : List Color} {h : Int} {ok : Color → Bool}
    {c : Color} (hv : bandOn req grounds h ok = some c) :
    (∀ g ∈ grounds, req ≤ contrastMilli c g) ∧ ok c = true := by
  unfold bandOn at hv
  cases hc : clearing req grounds (edgeAt h (bandL req grounds h ok)) with
  | none => simp [hc] at hv
  | some c0 =>
    rw [hc, Option.filter_some] at hv
    split at hv
    · rename_i hk
      cases hv
      exact ⟨clearing_contract hc, by simpa using hk⟩
    · cases hv

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

/-- `h` outside the disliked region's hues, else two degrees past its warm edge, toward orange as a
darkening yellow turns, clear of an 8-bit colour's hue rounding. -/
public def clearHue (h : Int) : Int :=
  if dislikedLo ≤ h ∧ h ≤ dislikedHi then dislikedLo - 2000 else h

/-- Hue `h`'s band tone at `req`, or, where it stands in the disliked region, the band tone of the
hue just past its warm edge (`clearHue`), kept only where it stands outside the region. -/
public def bandClear (req : Nat) (grounds : List Color) (h : Int)
    (ok : Color → Bool := fun _ => true) : Option Color :=
  (bandOn req grounds h ok).bind fun c =>
    if disliked c then
      ((bandOn req grounds (clearHue h) ok).filter (!disliked ·)).orElse fun _ =>
        (bandOn req grounds (clearHue h - 2000) ok).filter (!disliked ·)
    else some c

/-- **A cleared band tone clears what it was asked to on every ground, is not disliked and passes
`ok`.** -/
public theorem bandClear_contract {req : Nat} {grounds : List Color} {h : Int} {ok : Color → Bool}
    {c : Color} (hv : bandClear req grounds h ok = some c) :
    (∀ g ∈ grounds, req ≤ contrastMilli c g) ∧ disliked c = false ∧ ok c = true := by
  unfold bandClear at hv
  cases hb : bandOn req grounds h ok with
  | none => simp [hb] at hv
  | some c0 =>
    simp only [hb, Option.bind_some] at hv
    split at hv
    · have later : ∀ {h' : Int}, (bandOn req grounds h' ok).filter (!disliked ·) = some c →
          (∀ g ∈ grounds, req ≤ contrastMilli c g) ∧ disliked c = false ∧ ok c = true := by
        intro h' hf
        cases hc : bandOn req grounds h' ok with
        | none => simp [hc] at hf
        | some c1 =>
          rw [hc, Option.filter_some] at hf
          split at hf
          · rename_i hk
            cases hf
            exact ⟨(bandOn_contract hc).1, by simpa using hk, (bandOn_contract hc).2⟩
          · cases hf
      cases h1 : (bandOn req grounds (clearHue h) ok).filter (!disliked ·) with
      | some c1 =>
        rw [h1, Option.orElse_some] at hv
        cases hv
        exact later h1
      | none =>
        rw [h1, Option.orElse_none] at hv
        exact later hv
    · rename_i hd
      cases hv
      exact ⟨(bandOn_contract hb).1, by simpa using hd, (bandOn_contract hb).2⟩

/-- `c` at hue `h`, its lightness and as much of its chroma as the gamut holds kept. -/
private def atHue (c : Color) (h : Int) : Color :=
  let l := Oklab.labOf c
  let dir := Oklab.ofLch 0 (Nat.sqrt (Oklab.chromaSq l).toNat : Int) h
  (Oklab.Okl.toGamut { L := l.L, a := dir.a, b := dir.b, f := Oklab.fracOne }).toColor

/-- `c` with its hue moved past the disliked region's warm edge where it stands in it, else `c` as
it stands. -/
public def undislike (c : Color) : Color :=
  if !disliked c then c else
  (([dislikedLo - 2000, dislikedLo - 4000, dislikedLo - 6000].map (atHue c)).find? (!disliked ·)).getD c

/-- `c` with its hue moved past the disliked region's warm edge where its hue stands among the
region's, so a darker tone of it stays out of the region. -/
public def turnPast (c : Color) : Color :=
  let l := Oklab.labOf c
  let h := Oklab.hueMilli l.a l.b
  if dislikedLo ≤ h ∧ h ≤ dislikedHi then atHue c (dislikedLo - 2000) else c

end LeanTex.Core.ContrastSolve
