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

/-- The passing side of the boundary nearest a guess: bisected within
`guess ± span` where that bracket straddles the boundary (its end toward
`f` failing, its end toward `p` passing), else over the whole axis from the
failing end `f` to the passing end `p`. A good guess spends a few
evaluations where the axis would spend many; a bad one costs two. -/
public def bisectNear (pass : Int → Bool) (fuel : Nat) (f p guess span : Int) : Int :=
  let dir : Int := if p < f then -1 else 1
  let a := guess - dir * span
  let b := guess + dir * span
  if !pass a && pass b then bisect pass fuel a b else bisect pass (fuel + 8) f p

/-- **A guided bisection answers a passing value** when the axis's passing
end passes. -/
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

/-- The Oklab lightness of the grey whose WCAG luminance is `y` (10⁻⁷ units):
a grey's linear channels are its lightness cubed, so the lightness is the
luminance's cube root, at `labOf`'s scale. A first guess for a tint or an
ink near the neutral axis. -/
public def greyLightness (y : Nat) : Int := (Oklab.icbrt (min y 10000000 * 10 ^ 11) : Int) * 10 ^ 12

/-- The luminance (10⁻⁷ units) a colour darker than `ground` has at
`target` contrast to it, or a lighter one's (`lighter`). -/
public def luminanceAt (ground : Color) (target : Nat) (lighter : Bool) : Nat :=
  let yg := luminance ground + 500000
  if lighter then (yg * target / 1000) - 500000 else (yg * 1000 / max target 1) - 500000

/-- The candidate at lightness `L` (the `labOf` 10¹⁸ scale) with chroma
scaled to `f`% of the colour's own, brought into the gamut at its lightness
and hue. -/
private def realizeCand (lab : Oklab.Lab) (f : Nat) (L : Int) : Color :=
  (Oklab.Okl.toGamut { L, a := lab.a, b := lab.b, f := f * Oklab.fracOne / 100 }).toColor

/-- The `labOf` lightness of pure white, the top of the searched axis. -/
private def realizeLMax : Int := 10 ^ 18

/-- The nearest passing lightness to `L0` at one chroma fraction: both
directions searched, the boundary nearer `L0` taken; `none` when neither end
of the axis reaches the requirement at this chroma. -/
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

/-- The nearest passing lightness at one chroma fraction, from the colour's
own lightness. -/
private def realizeAt (req : Nat) (ground : Color) (lab : Oklab.Lab) (f : Nat) : Option Color :=
  realizeFrom req ground lab f lab.L

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

/-- **The solver holds hue**: what it returns is the colour itself, or a
colour at the colour's own Oklab direction with no more than its chroma,
in gamut — a lighter or darker tone, never a turned one. -/
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

/-! ## Carrying a colour to the other polarity

A scheme of the other polarity than a colour's page (a dark screen for a
light document) keeps what the colour meant there — how far it stood from
its page — on the other side of the scheme's page: Material 3's and Radix's
rule that a hue is the identity and its tone the ground's
(https://m3.material.io/styles/color/system/how-the-system-works,
https://www.radix-ui.com/colors), its lightness reflected rather than its
channels inverted. -/

/-- The `labOf` lightness a colour takes over another page: as far from that
page as it stood from its own, on the far side of it, within the axis. -/
public def reflectL (home page c : Color) : Int :=
  max 0 (min realizeLMax ((Oklab.labOf page).L + ((Oklab.labOf home).L - (Oklab.labOf c).L)))

/-- **A colour carried to a page of the other polarity**: its lightness
reflected about the two pages (`reflectL`), its hue and chroma held, brought
into the gamut at that lightness and hue — chroma lost, never a hue turned
(CSS Color 4 §14.2). A ground or a decoration takes this alone. -/
public def reflect (home page c : Color) : Color :=
  realizeCand (Oklab.labOf c) 100 (reflectL home page c)

/-- **A colour adapted to a ground of another scheme**: carried to the
scheme's page (`reflect`), then realized at `req` on the ground — the
carried tone where it passes, else the nearest passing lightness to it at
the colour's hue and no more than its chroma, reducing chroma toward the
neutral axis only where the full chroma never passes; `none` where no tone
of the colour's hue reaches `req` on the ground. -/
public def adapt (req : Nat) (home page c ground : Color) : Option Color :=
  let lab := Oklab.labOf c
  let L0 := reflectL home page c
  (([100, 75, 50, 25, 0] : List Nat).findSome? fun f => realizeFrom req ground lab f L0).bind
    fun cand => if req ≤ contrastMilli cand ground then some cand else none

/-- **An adapted colour meets its gate, its hue held, its chroma no more than
declared** (`_between`): what `adapt` returns reads at `req` on its ground,
and is the 8-bit colour of an Oklab tone at the declared colour's own
direction with no more than its chroma, in gamut — a lighter or darker
tone, never a turned or a more saturated one. -/
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

/-- **A carried colour holds its hue and chroma** (`_between`): the 8-bit
colour of an Oklab tone at the colour's own direction and no more than its
chroma, in gamut. -/
public theorem reflect_between (home page c : Color) :
    ∃ o : Oklab.Okl, o.a = (Oklab.labOf c).a ∧ o.b = (Oklab.labOf c).b ∧
      o.f ≤ Oklab.fracOne ∧ reflect home page c = o.toColor := by
  have hg := Oklab.Okl.toGamut_between
    { L := reflectL home page c, a := (Oklab.labOf c).a, b := (Oklab.labOf c).b,
      f := 100 * Oklab.fracOne / 100 }
  exact ⟨_, hg.2.1, hg.2.2.1,
    Nat.le_trans hg.2.2.2.1 (Nat.le_of_eq (Nat.mul_div_cancel_left _ (by decide))), rfl⟩

end LeanTex.Core.ContrastSolve
