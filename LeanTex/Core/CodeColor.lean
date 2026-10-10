module

public import LeanTex.Core.Ir
public import LeanTex.Core.CodeRole
public import LeanTex.Core.PygmentsStyle
public import LeanTex.Core.ContrastRatio
import LeanTex.Core.Oklab

/-!
The colour each code role paints in (`ListingHighlight.Role`), resolved at
one site, `resolve`, for both backends. A role's own palette key
(`Role.key`) is the document's colour for it. Otherwise the role takes its
colour from the palette's roles by one rule, so every palette has code
colours of its own:

* the error role is the palette's `alert`;
* the comment role is the palette's `muted`, where it is not the ink
  itself; else the ink mixed 70:30 into the page, the muted step every
  shipped bundle declares;
* the literal role is the palette's `example`, where it is neither the ink
  nor the alert; else one more hue, the middle of the widest arc of the hue
  circle the ink's and the alert's hues leave open — the hue farthest from
  both;
* keywords and names are the ink's hue family: a tone of the ink's own hue
  where it has one and the literal's hue stands clear of it; else the ink,
  keywords set apart by weight;
* the ink role is the listing's own text colour.

A derived hue ships as a tone (`tone`): its hue at `codeChroma`, never
louder than the alert, and the lightness nearest the ground that clears
`codeTone` there — Material 3's tonal rule (a key colour fixes hue and
chroma, the ground chooses the tone), the rule `Contrast.realize` follows
too. A role the palette gives the rule nothing to read for takes the
listing style's colour for the type a reader knows the role by
(`roleStyleKind`).
-/
namespace LeanTex.Core.CodeColor

open Ir ListingHighlight PygmentsStyle

/-- The resolved table of a shipped style. -/
public def table : ListingStyle → Table
  | .default => defaultTable
  | .friendly => friendlyTable

/-- A token colour and where it comes from: `role` names the palette key it
ships under (the HTML custom property a host page may override, and the
contrast judge's key), `declared` whether the document declared the colour
— under a code role's own key, or as the palette role the rule reads —
rather than the rule deriving it or the style choosing it. -/
public structure Paint where
  color : Color
  role : Option String
  declared : Bool
  deriving Repr, BEq

/-- The type a style's colour for a role is read from: the one a reader
knows the role by. The ink has none: it sets in the listing's own colour. -/
public def roleStyleKind : Role → Option Kind
  | .ink => none
  | .keyword => some .keyword
  | .name => some .nameFunction
  | .literal => some .string
  | .comment => some .comment
  | .error => some .genericError

/-- The style's colour for a role. -/
public def styleColor (style : ListingStyle) (r : Role) : Option Color :=
  (roleStyleKind r).bind fun k => ((table style).resolvedOf k).color.map (·.1)

/-- One just-noticeable difference, ΔEOK 0.02 (CSS Color 4 §14.2.1: "one
JND is an OkLCh difference of 0.02"), at `Oklab.labOf`'s 10¹⁸ scale. A
colour nearer the neutral axis than one JND shows no hue. -/
public def jnd : Int := 2 * 10 ^ 16

/-- A derived hue's chroma: five JNDs off the neutral axis. A declared
reading of "plainly a hue beside the ink and the comment's grey, and
quieter than an accent", not a measurement. -/
public def codeChroma : Int := 5 * jnd

/-- The contrast a derived hue's tone clears on its ground, in
`contrastMilli`'s thousandths: Material 3's accent tone, 40, on its
tone-100 surface (m3.material.io/styles/color/system/how-the-system-works).
Tone is CIE L*, so the pair's WCAG 2.2 ratio is 1.05 / (Y(40) + 0.05) with
Y(40) = (56/116)³: 6.461:1. -/
public def codeTone : Nat := 21000 * 116 ^ 3 / (20 * 56 ^ 3 + 116 ^ 3)

example : codeTone = 6461 := by decide

/-- A colour's chromatic coordinates, where it shows a hue. -/
private def hue? (c : Color) : Option (Int × Int) :=
  let l := Oklab.labOf c
  if jnd * jnd ≤ Oklab.chromaSq l then some (l.a, l.b) else none

private def norm (v : Int × Int) : Int := (Nat.sqrt (v.1 * v.1 + v.2 * v.2).toNat : Int)

/-- `v` at chroma `c`. -/
private def scaled (c : Int) (v : Int × Int) : Int × Int :=
  let n := norm v
  if n == 0 then (0, 0) else (c * v.1 / n, c * v.2 / n)

/-- Two hues stand clear of each other when they lie 60° apart or more:
Material 3's tonal-spot scheme sets its tertiary accent 60° of hue from its
primary, the nearest it treats as a hue of its own. -/
private def clear (u w : Int × Int) : Bool :=
  decide (2 * (u.1 * w.1 + u.2 * w.2) ≤ norm u * norm w)

/-- The middle of the widest arc a set of hues leaves open: opposite the
one hue, or, for two, opposite the middle of the narrower arc between
them — the bisector of the wider. Two opposite hues leave two equal arcs;
the one a quarter turn on from the first is taken. -/
private def openHue : List (Int × Int) → Option (Int × Int)
  | [] => none
  | [u] => some (-u.1, -u.2)
  | u :: w :: _ =>
    let s := (u.1 * norm w + w.1 * norm u, u.2 * norm w + w.2 * norm u)
    if s == (0, 0) then some (-u.2, u.1) else some (-s.1, -s.2)

/-- The colour at Oklab lightness `L` and chromatic coordinates `(a, b)`. -/
private def lab (a b L : Int) : Color := Oklab.toColorOfLab { L, a, b }

/-- Binary search on structural fuel between a failing lightness and a
passing one, returning the passing side of the boundary. -/
private def bisect (pass : Int → Bool) : Nat → Int → Int → Int
  | 0, _, p => p
  | n + 1, f, p =>
    let mid := (f + p) / 2
    if mid == f || mid == p then p
    else if pass mid then bisect pass n f mid else bisect pass n mid p

/-- The lightness nearest `from_` at which `pass` holds, on either side, to
2⁻²⁰ of the axis: a thousandth of an 8-bit channel step. -/
private def nearestPass (pass : Int → Bool) (from_ : Int) : Option Int :=
  let down := if pass 0 then some (bisect pass 20 from_ 0) else none
  let up := if pass (10 ^ 18) then some (bisect pass 20 from_ (10 ^ 18)) else none
  match down, up with
  | some d, some u => some (if from_ - d ≤ u - from_ then d else u)
  | some d, none => some d
  | none, some u => some u
  | none, none => none

/-- A hue's tone on a ground: at chromatic coordinates `(a, b)`, the
lightness nearest the ground's at which it clears `req` there, its chroma
reduced toward the neutral axis by quarters where no lightness does. -/
public def tone (req : Nat) (ground : Color) (v : Int × Int) : Option Color :=
  let from_ := (Oklab.labOf ground).L
  ([4, 3, 2, 1, 0] : List Int).findSome? fun q =>
    let a := q * v.1 / 4
    let b := q * v.2 / 4
    (nearestPass (fun L => decide (req ≤ Contrast.contrastMilli (lab a b L) ground)) from_).bind
      fun L => if req ≤ Contrast.contrastMilli (lab a b L) ground then some (lab a b L) else none

/-- **A tone clears what it was asked to**, on its ground: every answer is
guarded by the judged ratio itself, so no search argument is load-bearing. -/
public theorem tone_meets {req : Nat} {ground c : Color} {v : Int × Int}
    (h : tone req ground v = some c) : req ≤ Contrast.contrastMilli c ground := by
  unfold tone at h
  obtain ⟨q, _, hq⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.bind_eq_some_iff] at hq
  obtain ⟨L, _, hL⟩ := hq
  split at hL
  · cases hL; assumption
  · cases hL

/-- A derived hue's tone: the code tone, or text AA where the ground leaves
no lightness for it. -/
private def hueTone (ground : Color) (v : Int × Int) : Option Color :=
  (tone codeTone ground v).orElse fun _ => tone Contrast.aaText ground v

/-- What the rule reads a role's colour from the palette as. -/
public inductive Derived where
  /-- A palette role the rule reads. -/
  | role (key : String)
  /-- A colour the rule derives from the palette's roles. -/
  | color (c : Color)
  /-- The listing's own text colour: no colour of the role's own. -/
  | ink
  /-- Nothing: the palette declares none of the roles the rule reads. -/
  | none
  deriving Repr, BEq

/-- The rule, on the ground a listing stands on: every role derived at
once, each shared value computed once. -/
public def derive (pal : Palette) (ground : Color) : RoleTable Derived :=
  let fg := pal.find? "fg"
  let alert := pal.find? "alert"
  let bg := (Design.ofPalette pal).bg
  let chroma := match alert.bind hue? with
    | some u => min codeChroma (norm u)
    | none => codeChroma
  let inkHue := if jnd ≤ chroma then fg.bind hue? else none
  let hues := inkHue.toList ++ (alert.bind hue?).toList
  let ex := (pal.find? "example").filter fun e => some e != fg && some e != alert
  let literal : Derived × Option (Int × Int) := match ex with
    | some e => (.role "example", hue? e)
    | none =>
      match (if jnd ≤ chroma then openHue hues else none).bind fun u =>
          (hueTone ground (scaled chroma u)).map (·, u) with
      | some (c, u) => (.color c, some u)
      | none => (.none, none)
  let family : Derived := match fg with
    | none => .none
    | some _ =>
      match (inkHue.filter fun u => literal.2.all (clear u)).bind
          (fun u => hueTone ground (scaled chroma u)) with
      | some c => .color c
      | none => .ink
  let comment : Derived := match pal.find? "muted", fg with
    | some m, some f => if m == f then .color (f.mix 70 bg) else .role "muted"
    | some _, none => .role "muted"
    | none, some f => .color (f.mix 70 bg)
    | none, none => .none
  { ink := .ink, keyword := family, name := family, literal := literal.1, comment
    error := match alert with
      | some _ => .role "alert"
      | none => .none }

/-- **The one resolving site for the code roles.** A role's own key first,
shipped as the document declared it; then the rule (`derive`); then the
listing style's colour for the role. A palette role the rule reads ships
as that role on the page it is declared for — the colour the document
chose, under its key, judged by the contrast report as its prose uses are
— and, on any other ground, adapted to that ground under the code role's
own key, as a colour the document did not choose there. -/
public def resolve (pal : Palette) (ground : Color) (style : ListingStyle) :
    RoleTable (Option Paint) :=
  let derived := derive pal ground
  let page := (Design.ofPalette pal).bg
  RoleTable.ofFn fun r =>
    match pal.find? r.key with
    | some c => some { color := c, role := some r.key, declared := true }
    | none =>
      match derived.get r with
      | .role key => (pal.find? key).map fun c =>
          if ground == page then { color := c, role := some key, declared := true }
          else { color := c, role := some r.key, declared := false }
      | .color c => some { color := c, role := some r.key, declared := false }
      | .ink => none
      | .none => (styleColor style r).map fun c =>
          { color := c, role := some r.key, declared := false }

/-- **A colour shipped as declared is one the palette declares, under the
key it ships under**: a code role's own, or the palette role the rule
reads. -/
public theorem resolve_declared_mem (pal : Palette) (ground : Color) (style : ListingStyle)
    (r : Role) (p : Paint) (h : (resolve pal ground style).get r = some p)
    (hd : p.declared = true) : ∃ key, p.role = some key ∧ pal.find? key = some p.color := by
  rw [resolve, RoleTable.get_ofFn] at h
  split at h
  · rename_i c hc
    cases h
    exact ⟨r.key, rfl, hc⟩
  · split at h
    · rename_i key _
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨c, hc, hp⟩ := h
      split at hp
      · subst hp; exact ⟨key, rfl, hc⟩
      · subst hp; simp at hd
    · cases h; simp at hd
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      simp at hd

/-- **Every other colour ships under the role's own key**: what the rule
derives, adapts or takes from the style is the code role's, never a
palette role's. -/
public theorem resolve_derived_exact (pal : Palette) (ground : Color) (style : ListingStyle)
    (r : Role) (p : Paint) (h : (resolve pal ground style).get r = some p)
    (hd : p.declared = false) : p.role = some r.key := by
  rw [resolve, RoleTable.get_ofFn] at h
  split at h
  · cases h; simp at hd
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, hp⟩ := h
      split at hp
      · subst hp; simp at hd
      · subst hp; rfl
    · cases h; rfl
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl

end LeanTex.Core.CodeColor
