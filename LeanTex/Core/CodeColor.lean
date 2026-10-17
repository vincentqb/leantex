module

public import LeanTex.Core.Ir
public import LeanTex.Core.CodeRole
public import LeanTex.Core.PygmentsStyle
public import LeanTex.Core.ContrastRatio
import LeanTex.Core.Oklab
import LeanTex.Core.ContrastSolve

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

/-- The colour at Oklab lightness `L` and chromatic coordinates `(a, b)`. -/
private def lab (a b L : Int) : Color := Oklab.toColorOfLab { L, a, b }

/-- A hue's tone on a set of grounds: the lightness nearest the first ground's clearing `req` on
every one, its chroma reduced where none does. -/
public def toneOn (req : Nat) (grounds : List Color) (v : Int × Int) : Option Color :=
  let from_ := (Oklab.labOf (grounds.headD Color.white)).L
  let clears (c : Color) := grounds.all fun g => decide (req ≤ Contrast.contrastMilli c g)
  ([4, 3, 2, 1, 0] : List Int).findSome? fun q =>
    let a := q * v.1 / 4
    let b := q * v.2 / 4
    -- 14 halvings settle a lightness to 2⁻¹⁴ of the axis, about a sixty-fourth of an 8-bit step.
    (ContrastSolve.nearestPass (fun L => clears (lab a b L)) 14 from_ (lighter := false)).map
      (lab a b)

public theorem toneOn_contract {req : Nat} {grounds : List Color} {c : Color} {v : Int × Int}
    (h : toneOn req grounds v = some c) : ∀ g ∈ grounds, req ≤ Contrast.contrastMilli c g := by
  unfold toneOn at h
  obtain ⟨q, _, hq⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hq
  intro g hg
  exact of_decide_eq_true (List.all_eq_true.mp (ContrastSolve.nearestPass_contract hL) g hg)

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

/-- The grounds a derived hue's tone must read on: the listing's own, and under seeds the paper. -/
public def toneGrounds (pal : Palette) (ground : Color) : List Color :=
  match pal.seeded with
  | some st => (ground :: [st.seeds.paper]).eraseDups
  | none => [ground]

/-- The contrast a derived colour reads at on its ground: under seeds the ink's own target on the
ink and the medium's text floor elsewhere (`GroundDepth.text`), else text AA. -/
public def codeFloor (pal : Palette) (ground : Color) : Nat :=
  match pal.seeded with
  | some st => if ground == st.seeds.ink then st.targets.inverse else st.targets.text
  | none => Contrast.aaText

/-- How far a seeded palette's coloured code roles stand from the ink and from each other at least:
five JNDs of ΔEOK, the declared distinction the seeded code test holds them to. -/
public def roleGap : Int := 5 * Oklab.okJnd

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
  /-- The alert's mark (`alertmark`): an accent that serves the page as a
  container, whose hue the code turns from where the alert is the ink. -/
  mark : Option Color

private def reads (pal : Palette) : Reads :=
  let fg := Design.declared? pal .ink
  let alert := (Design.declared? pal .alert).filter fun a => some a != fg
  { fg, alert
    ex := (Design.declared? pal .example).filter fun e => some e != fg && some e != alert
    muted := (Design.declared? pal .muted).filter fun m => some m != alert
    mark := Design.declared? pal .alertMark }

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

/-- The three hues a quarter turn on from an anchor, counter-clockwise, in
millidegrees. -/
private def slotsOf (anchor : Int) : List Int :=
  [1, 2, 3].map fun k => (anchor + 90000 * k) % 360000

/-- How far apart two hues stand, the short way round, in millidegrees. -/
private def hueDist (h h' : Int) : Int :=
  let d := (h - h') % 360000
  min d (360000 - d)

/-- A colour's hue in millidegrees, where it shows one. -/
private def hueMilliOf? (c : Color) : Option Int := (hue? c).map fun v => Oklab.hueMilli v.1 v.2

/-- The slot nearest a hue, the earliest among equals. -/
private def nearestSlot (slots : List Int) (h : Int) : Option Int :=
  slots.foldl (fun best x => match best with
    | some b => if hueDist x h < hueDist b h then some x else best
    | none => some x) none

/-- A hue's band tone at the floor on the grounds, out of the disliked region, else the ink. -/
private def vivid (floor : Nat) (grounds : List Color) (h : Int) : Derived :=
  (ContrastSolve.bandClear floor grounds h).elim .ink .color

/-- A slot's hue, or where it stands among the disliked region's hues, the region's edge two degrees
out on the side farther from the other roles' hues, so three roles stay a quarter turn apart. -/
private def placed (h : Int) (others : List Int) : Int :=
  if ContrastSolve.dislikedLo ≤ h ∧ h ≤ ContrastSolve.dislikedHi then
    let warm := ContrastSolve.dislikedLo - 2000
    let cool := ContrastSolve.dislikedHi + 2000
    let far (x : Int) : Int := others.foldl (fun m o => min m (hueDist x o)) 360000
    if far warm < far cool then cool else warm
  else h

/-- The literal, keywords and names under seeds, at the band tones of the slots a quarter turn
on from the error's hue (its key's, the alert's, the mark's, else the ink's). -/
private def seededPlan (p : Reads) (grounds : List Color) (floor : Nat)
    (literal : Derived × Option (Int × Int)) (declared : ListingHighlight.Role → Option Color) :
    Derived × Derived × Derived :=
  let shipHue (r : ListingHighlight.Role) (planned : Option Int) : Option Int :=
    match declared r with
    | some c => hueMilliOf? c
    | none => planned
  let ink := shipHue .ink (p.fg.bind hueMilliOf?)
  let marked := (p.mark.bind hueMilliOf?).map ContrastSolve.clearHue
  let anchor := ((shipHue .error (p.alert.bind hueMilliOf?)).orElse fun _ => marked).orElse fun _ => ink
  let inked : Derived := if p.fg.isSome then .ink else .none
  match anchor with
  | none => (literal.1, inked, inked)
  | some e =>
    let slots := slotsOf e
    let held := ([ListingHighlight.Role.keyword, .name, .literal].filterMap fun r =>
        (declared r).bind hueMilliOf?) ++
      (if (declared .literal).isNone then (p.ex.bind hueMilliOf?).toList else [])
    let free := slots.filter fun x => !(held.filterMap (nearestSlot slots)).contains x
    let keyword := if (declared .keyword).isSome then none else match ink with
      | some ih => nearestSlot free ih
      | none => if free.contains ((e + 180000) % 360000) then some ((e + 180000) % 360000) else free.head?
    let free := free.filter (some · != keyword)
    let lit := if p.ex.isSome || (declared .literal).isSome then none else free.head?
    let free := free.filter (some · != lit)
    let name := if (declared .name).isSome then none else free.head?
    let taken := [keyword, lit, name].filterMap id ++ held
    let derived (h : Option Int) : Derived :=
      if p.fg.isSome then h.elim .ink fun h => vivid floor grounds (placed h (taken.filter (· != h)))
      else .none
    ((match p.ex, lit with
      | none, some h => vivid floor grounds (placed h (taken.filter (· != h)))
      | _, _ => literal.1), derived keyword, derived name)

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

/-- Errors in the alert, or under seeds whose alert is the ink on a mark, the mark's hue's band
tone. -/
private def errorOf (pal : Palette) (p : Reads) (grounds : List Color) (floor : Nat) : Derived :=
  match p.alert with
  | some _ => .role .alert
  | none =>
    match pal.seeded, p.mark.bind hueMilliOf? with
    | some _, some h => vivid floor grounds (ContrastSolve.clearHue h)
    | _, _ => .none

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

private theorem vivid_ne_none (floor : Nat) (grounds : List Color) (h : Int) :
    vivid floor grounds h ≠ .none :=
  elim_ink_ne_none _ _ fun _ => by simp

private theorem seededPlan_keywords_none {p : Reads} {grounds : List Color} {floor : Nat}
    {l : Derived × Option (Int × Int)} {declared : ListingHighlight.Role → Option Color}
    (h : (seededPlan p grounds floor l declared).2.1 = .none ∨
      (seededPlan p grounds floor l declared).2.2 = .none) :
    p.fg = none := by
  cases hf : p.fg with
  | none => rfl
  | some f =>
    exfalso
    unfold seededPlan at h
    simp only [hf, Option.isSome_some, ite_true] at h
    split at h
    · rcases h with h | h <;> simp at h
    · rcases h with h | h <;> exact elim_ink_ne_none _ _ (fun _ => vivid_ne_none floor grounds _) h

private theorem seededPlan_literal_none {p : Reads} {grounds : List Color} {floor : Nat}
    {l : Derived × Option (Int × Int)} {declared : ListingHighlight.Role → Option Color}
    (h : (seededPlan p grounds floor l declared).1 = .none) : l.1 = .none := by
  unfold seededPlan at h
  dsimp only at h
  split at h
  · exact h
  · dsimp only at h
    split at h
    · exact absurd h (vivid_ne_none floor grounds _)
    · exact h

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

private theorem errorOf_none {pal : Palette} {p : Reads} {grounds : List Color} {floor : Nat}
    (h : errorOf pal p grounds floor = .none) : p.alert = none := by
  unfold errorOf at h
  split at h
  · simp at h
  · assumption

/-- The literal, keywords and names: the rule's own, or under seeds `seededPlan`'s at `floor`. -/
private def planOf (pal : Palette) (p : Reads) (grounds : List Color) (floor : Nat)
    (literal : Derived × Option (Int × Int)) : Derived × Derived × Derived :=
  match pal.seeded with
  | some _ => seededPlan p grounds floor literal fun r => Design.declared? pal (Ir.Role.ofCode r)
  | none => let family := familyOf p grounds literal.2; (literal.1, family, family)

private theorem planOf_keywords_none {pal : Palette} {p : Reads} {grounds : List Color}
    {floor : Nat} {l : Derived × Option (Int × Int)}
    (h : (planOf pal p grounds floor l).2.1 = .none ∨ (planOf pal p grounds floor l).2.2 = .none) :
    p.fg = none := by
  unfold planOf at h
  split at h
  · exact seededPlan_keywords_none h
  · exact familyOf_none (by dsimp only at h; rcases h with h | h <;> exact h)

private theorem planOf_literal_none {pal : Palette} {p : Reads} {grounds : List Color}
    {floor : Nat} {l : Derived × Option (Int × Int)} (h : (planOf pal p grounds floor l).1 = .none) :
    l.1 = .none := by
  unfold planOf at h
  split at h
  · exact seededPlan_literal_none h
  · exact h

/-- The rule, on the ground a listing stands on: every role derived at once,
each shared value computed once. -/
public def derive (pal : Palette) (ground : Color) : RoleTable Derived :=
  let p := reads pal
  let grounds := toneGrounds pal ground
  let floor := codeFloor pal ground
  let plan := planOf pal p grounds floor (literalOf p grounds)
  { ink := .ink, keyword := plan.2.1, name := plan.2.2, literal := plan.1
    comment := commentOf p grounds, error := errorOf pal p grounds floor }

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
      | .color c => some { color := c.engine, role := some (Ir.Role.ofCode r), declared := false }
      | .ink => none
      | .none => (styleColor (style.getD .default) r).map fun c =>
          { color := c.engine, role := some (Ir.Role.ofCode r), declared := false
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
