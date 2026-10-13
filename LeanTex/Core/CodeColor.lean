module

public import LeanTex.Core.Ir
public import LeanTex.Core.CodeRole
public import LeanTex.Core.PygmentsStyle
public import LeanTex.Core.ContrastRatio
import LeanTex.Core.Oklab

/-! The colour each listing code role paints in, resolved at one site (`resolve`) for both
backends: a role's own key, else one rule over the palette's roles, else the listing style. -/
namespace LeanTex.Core.CodeColor

open Ir ListingHighlight PygmentsStyle

/-- The resolved table of a shipped style. -/
public def table : ListingStyle → Table
  | .default => defaultTable
  | .friendly => friendlyTable

/-- A token colour, the registry role it ships under, and whether the document declared it or
the style states it; only a derived colour is fitted to its ground. -/
public structure Paint where
  color : Color
  role : Option Ir.Role
  declared : Bool
  styled : Bool := false
  deriving Repr, BEq

/-- Retired palette keys, each with the role its token type paints in now. -/
public def retiredKeys : List (String × ListingHighlight.Role) :=
  [("codestring", .literal), ("codenumber", .literal), ("codebuiltin", .name),
   ("codeoperator", .ink)]

/-- The token type a style's colour for a role is read from; the ink has none. -/
public def roleStyleKind : ListingHighlight.Role → Option Kind
  | .ink => none
  | .keyword => some .keyword
  | .name => some .nameBuiltin
  | .literal => some .string
  | .comment => some .comment
  | .error => some .genericError

/-- The style's colour for a role. -/
public def styleColor (style : ListingStyle) (r : ListingHighlight.Role) : Option Color :=
  (roleStyleKind r).bind fun k => ((table style).resolvedOf k).color.map (·.1)

/-- One just-noticeable difference: a colour nearer the neutral axis shows no hue. -/
private def jnd : Int := Oklab.okJnd

/-- A derived hue's chroma: five JNDs off the neutral axis, a declared reading, no measurement. -/
public def codeChroma : Int := 5 * Oklab.okJnd

/-- The contrast a derived hue's tone clears, in thousandths: Material 3's tone 40 on tone 100,
6.461:1. -/
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

/-- Two hues stand clear of each other 60° apart or more (Material 3's tonal-spot tertiary). -/
private def clear (u w : Int × Int) : Bool :=
  decide (2 * (u.1 * w.1 + u.2 * w.2) ≤ norm u * norm w)

/-- The middle of the widest arc one or two hues leave open. -/
private def openHue : List (Int × Int) → Option (Int × Int)
  | [] => none
  | [u] => some (-u.1, -u.2)
  | u :: w :: _ =>
    let s := (u.1 * norm w + w.1 * norm u, u.2 * norm w + w.2 * norm u)
    if s == (0, 0) then some (-u.2, u.1) else some (-s.1, -s.2)

/-- Arcs within a degree of the widest count as wide as it. -/
private def arcSlack : Int := 1000

/-- The middle of the widest arc a list of hues (millidegrees) leaves open, the earliest-listed
hue's arc winning within `arcSlack`. -/
private def openArc (hs : List Int) : Option Int :=
  let width (h : Int) : Int :=
    hs.foldl (fun w h' => let d := (h' - h) % 360000; if d == 0 then w else min w d) 360000
  let widest := hs.foldl (fun w h => max w (width h)) 0
  (hs.find? fun h => widest ≤ width h + arcSlack).map fun h => (h + width h / 2) % 360000

example : openArc [88000, 268000] = some 178000 := by decide
example : openArc [88000, 268000, 178000] = some 358000 := by decide
example : openArc [255000, 42000] = some 148500 := by decide
example : openArc [255000, 165000, 30001] = some 322500 := by decide
example : openArc [255000, 165000, 29999] = some 322499 := by decide
example : openArc [] = none := by decide

/-- The colour at Oklab lightness `L` and chromatic coordinates `(a, b)`. -/
private def lab (a b L : Int) : Color := Oklab.toColorOfLab { L, a, b }

/-- Binary search between a failing lightness and a passing one, returning the passing side. -/
private def bisect (pass : Int → Bool) : Nat → Int → Int → Int
  | 0, _, p => p
  | n + 1, f, p =>
    let mid := (f + p) / 2
    if mid == f || mid == p then p
    else if pass mid then bisect pass n f mid else bisect pass n mid p

/-- The lightness nearest `from_` at which `pass` holds, on either side, to
2⁻¹⁴ of the axis: a sixtieth of an 8-bit channel step. -/
private def nearestPass (pass : Int → Bool) (from_ : Int) : Option Int :=
  let down := if pass 0 then some (bisect pass 14 from_ 0) else none
  let up := if pass (10 ^ 18) then some (bisect pass 14 from_ (10 ^ 18)) else none
  match down, up with
  | some d, some u => some (if from_ - d ≤ u - from_ then d else u)
  | some d, none => some d
  | none, some u => some u
  | none, none => none

/-- A hue's tone on a set of grounds: the lightness nearest the first ground's clearing `req` on
every one, its chroma reduced where none does. -/
public def toneOn (req : Nat) (grounds : List Color) (v : Int × Int) : Option Color :=
  let from_ := (Oklab.labOf (grounds.headD Color.white)).L
  let clears (c : Color) := grounds.all fun g => decide (req ≤ Contrast.contrastMilli c g)
  ([4, 3, 2, 1, 0] : List Int).findSome? fun q =>
    let a := q * v.1 / 4
    let b := q * v.2 / 4
    (nearestPass (fun L => clears (lab a b L)) from_).bind
      fun L => if clears (lab a b L) then some (lab a b L) else none

public theorem toneOn_contract {req : Nat} {grounds : List Color} {c : Color} {v : Int × Int}
    (h : toneOn req grounds v = some c) : ∀ g ∈ grounds, req ≤ Contrast.contrastMilli c g := by
  unfold toneOn at h
  obtain ⟨q, _, hq⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.bind_eq_some_iff] at hq
  obtain ⟨L, _, hL⟩ := hq
  split at hL
  · rename_i hc
    cases hL
    intro g hg
    exact of_decide_eq_true (List.all_eq_true.mp hc g hg)
  · cases hL

/-- A hue's tone on one ground. -/
public def tone (req : Nat) (ground : Color) (v : Int × Int) : Option Color :=
  toneOn req [ground] v

public theorem tone_meets {req : Nat} {ground c : Color} {v : Int × Int}
    (h : tone req ground v = some c) : req ≤ Contrast.contrastMilli c ground :=
  toneOn_contract h ground (List.mem_singleton.mpr rfl)

/-- A derived hue's tone on the grounds it must read on: the code tone, or
text AA where they leave no lightness for it. -/
private def hueTone (grounds : List Color) (v : Int × Int) : Option Color :=
  (toneOn codeTone grounds v).orElse fun _ => toneOn Contrast.aaText grounds v

/-- The grounds a derived hue's tone must read on: the listing's own, and under seeds the paper
and the block fills. -/
public def toneGrounds (pal : Palette) (ground : Color) : List Color :=
  match pal.seeded with
  | some st => (ground :: [st.seeds.paper, st.colors.surface, st.colors.accentWash]).eraseDups
  | none => [ground]

/-- What the rule reads a role's colour from the palette as. -/
public inductive Derived where
  /-- A palette role the rule reads. -/
  | role (r : Ir.Role)
  /-- A colour the rule derives from the palette's roles. -/
  | color (c : Color)
  /-- The listing's own text colour: no colour of the role's own. -/
  | ink
  /-- Nothing: the palette declares none of the roles the rule reads. -/
  | none
  deriving Repr, BEq

/-- The palette roles the rule reads, each skipped where it repeats an earlier role's colour. -/
private structure Reads where
  fg : Option Color
  alert : Option Color
  ex : Option Color
  muted : Option Color

private def reads (pal : Palette) : Reads :=
  let fg := Design.declared? pal .ink
  let alert := (Design.declared? pal .alert).filter fun a => some a != fg
  { fg, alert
    ex := (Design.declared? pal .example).filter fun e => some e != fg && some e != alert
    muted := (Design.declared? pal .muted).filter fun m => some m != alert }

/-- The hues the code already sets in: the ink's where it shows one, and
the alert's. -/
private def Reads.hues (p : Reads) : List (Int × Int) :=
  (p.fg.bind hue?).toList ++ (p.alert.bind hue?).toList

/-- Whether the rule leaves role `r` open, so a listing style colours it. -/
public def opens (pal : Palette) (r : ListingHighlight.Role) : Bool :=
  let p := reads pal
  match r with
  | .ink => false
  | .keyword | .name => p.fg.isNone
  | .literal => p.ex.isNone && p.hues.isEmpty
  | .comment => p.muted.isNone && p.fg.isNone
  | .error => p.alert.isNone

private theorem openHue_some (u : Int × Int) (us : List (Int × Int)) :
    (openHue (u :: us)).isSome := by
  cases us with
  | nil => rfl
  | cons w ws => simp only [openHue]; split <;> rfl

/-- A derived hue's chroma under the palette: `codeChroma`, never louder
than the alert. -/
private def Reads.chroma (p : Reads) : Int :=
  match p.alert.bind hue? with
  | some u => min codeChroma (norm u)
  | none => codeChroma

/-- The literal role, and the hue it sets in where it has one. -/
private def literalOf (p : Reads) (grounds : List Color) : Derived × Option (Int × Int) :=
  match p.ex with
  | some e => (.role .example, hue? e)
  | none =>
    match openHue p.hues with
    | some u => ((hueTone grounds (scaled p.chroma u)).elim .ink .color, some u)
    | none => (.none, none)

/-- The ink's own hue, where it stands clear of the literal's and the
error's. -/
private def inkHueClear (p : Reads) (literal error : Option (Int × Int)) : Option (Int × Int) :=
  (p.fg.bind hue?).filter fun u => literal.all (clear u) && error.all (clear u)

/-- Keywords and names: a tone of the ink's own hue where it stands clear
of both the literal's hue and the alert's, else the ink. -/
private def familyOf (p : Reads) (grounds : List Color) (literal : Option (Int × Int)) : Derived :=
  match p.fg with
  | none => .none
  | some _ =>
    match (inkHueClear p literal (p.alert.bind hue?)).bind
        (fun u => hueTone grounds (scaled p.chroma u)) with
    | some c => .color c
    | none => .ink

/-- A direction's hue, in millidegrees. -/
private def hueOfDir (v : Int × Int) : Int := Oklab.hueMilli v.1 v.2

/-- The direction of a hue (millidegrees) at the palette's derived chroma. -/
private def dirOfHue (p : Reads) (h : Int) : Int × Int :=
  let l := Oklab.ofLch 0 p.chroma h
  (l.a, l.b)

/-- A derived hue's tone on the grounds, or the ink where none reads. -/
private def tonedDir (p : Reads) (grounds : List Color) (v : Int × Int) : Derived :=
  (hueTone grounds (scaled p.chroma v)).elim .ink .color

/-- The literal under a palette generated from seeds: a named example's
(`literalOf`), else the middle of the widest arc the code's fixed hues leave
open, else the rule's own. -/
private def seededLiteral (p : Reads) (grounds : List Color) (literal : Derived × Option (Int × Int))
    (fixed : List (Int × Int)) : Derived × Option (Int × Int) :=
  match p.ex, (openArc (fixed.map hueOfDir)).map (dirOfHue p) with
  | none, some v => (tonedDir p grounds v, some v)
  | _, _ => literal

/-- The literal, keywords and names under seeds, each a hue of its own planned around the code's
fixed hues. -/
private def seededPlan (p : Reads) (grounds : List Color) (literal : Derived × Option (Int × Int))
    (declared : ListingHighlight.Role → Option Color) : Derived × Derived × Derived :=
  let ships (r : ListingHighlight.Role) (planned : Option (Int × Int)) : Option (Int × Int) :=
    match declared r with
    | some c => hue? c
    | none => planned
  let ink := ships .ink (p.fg.bind hue?)
  let others := (ships .error (p.alert.bind hue?)).toList ++ ((declared .comment).bind hue?).toList ++
    [ListingHighlight.Role.keyword, .name, .literal].filterMap fun r => (declared r).bind hue?
  let lit := seededLiteral p grounds literal (ink.toList ++ others)
  let around := others ++ (ships .literal lit.2).toList
  let keyword := (ink.filter fun u => around.all (clear u)).orElse
    fun _ => (openArc ((ink.toList ++ around).map hueOfDir)).map (dirOfHue p)
  let name := (openArc ((ink.toList ++ around ++ (ships .keyword keyword).toList).map hueOfDir)).map
    (dirOfHue p)
  match p.fg with
  | none => (lit.1, .none, .none)
  | some _ => (lit.1, keyword.elim .ink (tonedDir p grounds), name.elim .ink (tonedDir p grounds))

/-- The quietest tone of the ink's hue that reads as text on every ground, else the ink. -/
private def quietInk (f : Color) (grounds : List Color) : Derived :=
  let l := Oklab.labOf f
  match toneOn (Contrast.aaText + 100) grounds (l.a, l.b) with
  | some c => .color c
  | none => .ink

private def commentOf (p : Reads) (grounds : List Color) : Derived :=
  match p.muted, p.fg with
  | some m, some f => if m == f then quietInk f grounds else .role .muted
  | some _, none => .role .muted
  | none, some f => quietInk f grounds
  | none, none => .none

private def errorOf (p : Reads) : Derived :=
  match p.alert with
  | some _ => .role .alert
  | none => .none

private theorem familyOf_none {p : Reads} {grounds : List Color} {l : Option (Int × Int)}
    (h : familyOf p grounds l = .none) : p.fg = none := by
  unfold familyOf at h
  split at h
  · assumption
  · split at h <;> simp at h

private theorem elim_ink_ne_none {α : Type} (o : Option α) (f : α → Derived)
    (hf : ∀ a, f a ≠ .none) : o.elim .ink f ≠ .none := by
  cases o with
  | none => simp
  | some a => exact hf a

private theorem tonedDir_ne_none (p : Reads) (grounds : List Color) (v : Int × Int) :
    tonedDir p grounds v ≠ .none :=
  elim_ink_ne_none _ _ fun _ => by simp

private theorem seededPlan_keywords_none {p : Reads} {grounds : List Color}
    {l : Derived × Option (Int × Int)} {declared : ListingHighlight.Role → Option Color}
    (h : (seededPlan p grounds l declared).2.1 = .none ∨ (seededPlan p grounds l declared).2.2 = .none) :
    p.fg = none := by
  unfold seededPlan at h
  dsimp only at h
  split at h
  · assumption
  · rcases h with h | h <;> exact absurd h (elim_ink_ne_none _ _ (tonedDir_ne_none p grounds))

private theorem seededLiteral_none {p : Reads} {grounds : List Color} {l : Derived × Option (Int × Int)}
    {fixed : List (Int × Int)} (h : (seededLiteral p grounds l fixed).1 = .none) : l.1 = .none := by
  unfold seededLiteral at h
  split at h
  · exact absurd h (tonedDir_ne_none p grounds _)
  · exact h

private theorem seededPlan_literal_none {p : Reads} {grounds : List Color}
    {l : Derived × Option (Int × Int)} {declared : ListingHighlight.Role → Option Color}
    (h : (seededPlan p grounds l declared).1 = .none) : l.1 = .none := by
  unfold seededPlan at h
  dsimp only at h
  split at h <;> exact seededLiteral_none h

private theorem literalOf_none {p : Reads} {grounds : List Color}
    (h : (literalOf p grounds).1 = .none) : p.ex = none ∧ p.hues = [] := by
  unfold literalOf at h
  split at h
  · simp at h
  · rename_i he
    refine ⟨he, ?_⟩
    cases hh : p.hues with
    | nil => rfl
    | cons u us =>
      have hs := openHue_some u us
      rw [hh] at h
      split at h
      · rename_i v _
        cases hc : hueTone grounds (scaled p.chroma v) <;> simp [hc] at h
      · rename_i hn; rw [hn] at hs; simp at hs

private theorem quietInk_ne_none (f : Color) (grounds : List Color) :
    quietInk f grounds ≠ .none := by
  unfold quietInk
  dsimp only
  split <;> simp

private theorem commentOf_none {p : Reads} {grounds : List Color}
    (h : commentOf p grounds = .none) : p.muted = none ∧ p.fg = none := by
  unfold commentOf at h
  split at h
  · split at h
    · exact absurd h (quietInk_ne_none _ _)
    · simp at h
  · simp at h
  · exact absurd h (quietInk_ne_none _ _)
  · rename_i hm hf; exact ⟨hm, hf⟩

private theorem errorOf_none {p : Reads} (h : errorOf p = .none) : p.alert = none := by
  unfold errorOf at h
  split at h
  · simp at h
  · assumption

/-- The literal, keywords and names: the rule's own, or under seeds `seededPlan`'s. -/
private def planOf (pal : Palette) (p : Reads) (grounds : List Color)
    (literal : Derived × Option (Int × Int)) : Derived × Derived × Derived :=
  match pal.seeded with
  | some _ => seededPlan p grounds literal fun r => Design.declared? pal (Ir.Role.ofCode r)
  | none => let family := familyOf p grounds literal.2; (literal.1, family, family)

private theorem planOf_keywords_none {pal : Palette} {p : Reads} {grounds : List Color}
    {l : Derived × Option (Int × Int)}
    (h : (planOf pal p grounds l).2.1 = .none ∨ (planOf pal p grounds l).2.2 = .none) :
    p.fg = none := by
  unfold planOf at h
  split at h
  · exact seededPlan_keywords_none h
  · exact familyOf_none (by dsimp only at h; rcases h with h | h <;> exact h)

private theorem planOf_literal_none {pal : Palette} {p : Reads} {grounds : List Color}
    {l : Derived × Option (Int × Int)} (h : (planOf pal p grounds l).1 = .none) : l.1 = .none := by
  unfold planOf at h
  split at h
  · exact seededPlan_literal_none h
  · exact h

/-- The rule, on the ground a listing stands on: every role derived at once,
each shared value computed once. -/
public def derive (pal : Palette) (ground : Color) : RoleTable Derived :=
  let p := reads pal
  let grounds := toneGrounds pal ground
  let plan := planOf pal p grounds (literalOf p grounds)
  { ink := .ink, keyword := plan.2.1, name := plan.2.2, literal := plan.1
    comment := commentOf p grounds, error := errorOf p }

public theorem derive_none_opens (pal : Palette) (ground : Color) (r : ListingHighlight.Role)
    (h : (derive pal ground).get r = .none) : opens pal r = true := by
  cases r <;> simp only [derive, RoleTable.get] at h
  · simp at h
  · simp [opens, planOf_keywords_none (Or.inl h)]
  · simp [opens, planOf_keywords_none (Or.inr h)]
  · obtain ⟨he, hh⟩ := literalOf_none (planOf_literal_none h)
    simp [opens, he, hh]
  · obtain ⟨hm, hf⟩ := commentOf_none h
    simp [opens, hm, hf]
  · simp [opens, errorOf_none h]

/-- The one resolving site for the code roles: a role's own key, then the rule, then the listing
style's colour. -/
public def resolve (pal : Palette) (ground : Color) (style : Option ListingStyle) :
    RoleTable (Option Paint) :=
  let page := Design.printPage pal
  let derived := derive pal ground
  RoleTable.ofFn fun r =>
    match Design.declared? pal (Ir.Role.ofCode r) with
    | some c => some { color := c, role := some (Ir.Role.ofCode r), declared := true }
    | none =>
      match derived.get r with
      | .role key => (Design.declared? pal key).map fun c =>
          if ground == page then { color := c, role := some key, declared := true }
          else { color := c, role := some (Ir.Role.ofCode r), declared := false }
      | .color c => some { color := c, role := some (Ir.Role.ofCode r), declared := false }
      | .ink => none
      | .none => (styleColor (style.getD .default) r).map fun c =>
          { color := c, role := some (Ir.Role.ofCode r), declared := false
            styled := style.isSome }

public theorem resolve_declared_mem (pal : Palette) (ground : Color) (style : Option ListingStyle)
    (r : ListingHighlight.Role) (p : Paint) (h : (resolve pal ground style).get r = some p)
    (hd : p.declared = true) :
    ∃ key, p.role = some key ∧ Design.declared? pal key = some p.color := by
  rw [resolve, RoleTable.get_ofFn] at h
  split at h
  · rename_i c hc
    cases h
    exact ⟨_, rfl, hc⟩
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

public theorem resolve_derived_exact (pal : Palette) (ground : Color) (style : Option ListingStyle)
    (r : ListingHighlight.Role) (p : Paint) (h : (resolve pal ground style).get r = some p)
    (hd : p.declared = false) : p.role = some (Ir.Role.ofCode r) := by
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

/-- Whether the listing style gives role `r` its colour under the palette. -/
public def styleReads (pal : Palette) (r : ListingHighlight.Role) : Bool :=
  (Design.declared? pal (Ir.Role.ofCode r)).isNone && (roleStyleKind r).isSome && opens pal r

public theorem resolve_style_exact (pal : Palette) (ground : Color)
    (style style' : Option ListingStyle)
    (r : ListingHighlight.Role) (h : styleReads pal r = false) :
    (resolve pal ground style).get r = (resolve pal ground style').get r := by
  simp only [resolve, RoleTable.get_ofFn]
  split
  · rfl
  · rename_i hk
    split
    · rfl
    · rfl
    · rfl
    · rename_i hd
      have ho := derive_none_opens pal ground r hd
      cases hr : roleStyleKind r with
      | none => simp [styleColor, hr]
      | some _ => simp [styleReads, hk, hr, ho] at h

end LeanTex.Core.CodeColor
