module

public import LeanTex.Core.Ir
public import LeanTex.Core.CodeRole
public import LeanTex.Core.PygmentsStyle
public import LeanTex.Core.ContrastRatio
import LeanTex.Core.Oklab

/-!
The colour each code role paints in (`ListingHighlight.Role`), resolved at
one site, `resolve`, for both backends. A role's own palette key (its
registry row, `Ir.Role.ofCode`) is the document's colour for it. Otherwise the
role takes its
colour from the palette's roles by one rule, so every palette has code
colours of its own:

* the error role is the palette's `alert`, where it is not the ink;
* the comment role is the palette's `muted`, where it is neither the ink
  nor the alert; else the quietest tone of the ink's own hue that reads as
  text, a muted step derived by a rule rather than a fixed mix;
* the literal role is the palette's `example`, where it is neither the ink
  nor the alert; else one more hue, the middle of the widest arc of the hue
  circle the ink's and the alert's hues leave open — the hue farthest from
  both;
* keywords and names are the ink's hue family: a tone of the ink's own hue
  where it has one and the literal's hue stands clear of it; else the ink,
  keywords set apart by weight. Under a palette generated from seeds, whose
  code is the generator's to complete, each takes a hue of its own instead:
  keywords the ink's where it stands clear, else the middle of the widest
  arc the hues already set leave open (`openArc`), and names the next
  widest arc's middle, so no role but the ink's sets in the ink;
* the ink role is the listing's own text colour.

A derived hue ships as a tone (`tone`): its hue at `codeChroma`, never
louder than the alert, and the lightness nearest the ground that clears
`codeTone` there — Material 3's tonal rule (a key colour fixes hue and
chroma, the ground chooses the tone), the rule `ContrastSolve.realizeNearest`
follows too. A role the palette gives the rule nothing to read for takes the
listing style's colour for the type a reader knows the role by
(`roleStyleKind`).
-/
namespace LeanTex.Core.CodeColor

open Ir ListingHighlight PygmentsStyle

/-- The resolved table of a shipped style. -/
public def table : ListingStyle → Table
  | .default => defaultTable
  | .friendly => friendlyTable

/-- A token colour and where it comes from: `role` names the registry role it
ships under (the HTML custom property a host page may override, and the
contrast judge's key), `declared` whether the document declared the colour
— under a code role's own key, or as the palette role the rule reads —
rather than the rule deriving it or the style choosing it, and `styled`
whether the listing's highlighting style states it. A declared or a styled
colour ships as stated; only what the rule derives is the engine's to fit
to its ground. -/
public structure Paint where
  color : Color
  role : Option Ir.Role
  declared : Bool
  styled : Bool := false
  deriving Repr, BEq

/-- The palette keys that once coloured one token type each, and the role
that type paints in now. They colour no listing: a role is named by its own
key (`Ir.codeKey`, the registry's), one naming scheme. -/
public def retiredKeys : List (String × ListingHighlight.Role) :=
  [("codestring", .literal), ("codenumber", .literal), ("codebuiltin", .name),
   ("codeoperator", .ink)]

/-- The type a style's colour for a role is read from: the one a reader
knows the role by. The ink has none: it sets in the listing's own colour. -/
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

/-- One just-noticeable difference (`Oklab.okJnd`): a colour nearer the
neutral axis than one JND shows no hue. -/
private def jnd : Int := Oklab.okJnd

/-- A derived hue's chroma: five JNDs off the neutral axis. A declared
reading of "plainly a hue beside the ink and the comment's grey, and
quieter than an accent", not a measurement. -/
public def codeChroma : Int := 5 * Oklab.okJnd

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

/-- The middle of the widest arc a list of hues (millidegrees) leaves open on
the hue circle: each listed hue opens the arc running counter-clockwise to
the nearest other hue listed, and between arcs equally wide the
earliest-listed hue's is taken — `openHue`'s rule for two hues, at any
count. One hue leaves the whole circle, whose middle stands opposite it. -/
private def openArc (hs : List Int) : Option Int :=
  let width (h : Int) : Int :=
    hs.foldl (fun w h' => let d := (h' - h) % 360000; if d == 0 then w else min w d) 360000
  let widest := hs.foldl (fun (acc : Option (Int × Int)) h =>
    let w := width h
    match acc with
    | some (_, best) => if best < w then some (h, w) else acc
    | none => some (h, w)) none
  widest.map fun (h, w) => (h + w / 2) % 360000

example : openArc [88000, 268000] = some 178000 := by decide
example : openArc [88000, 268000, 178000] = some 358000 := by decide
example : openArc [255000, 42000] = some 148500 := by decide
example : openArc [] = none := by decide

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
2⁻¹⁴ of the axis: a sixtieth of an 8-bit channel step. -/
private def nearestPass (pass : Int → Bool) (from_ : Int) : Option Int :=
  let down := if pass 0 then some (bisect pass 14 from_ 0) else none
  let up := if pass (10 ^ 18) then some (bisect pass 14 from_ (10 ^ 18)) else none
  match down, up with
  | some d, some u => some (if from_ - d ≤ u - from_ then d else u)
  | some d, none => some d
  | none, some u => some u
  | none, none => none

/-- A hue's tone on a set of grounds: at chromatic coordinates `(a, b)`, the
lightness nearest the first ground's at which it clears `req` on every one,
its chroma reduced toward the neutral axis by quarters where no lightness
does. -/
public def toneOn (req : Nat) (grounds : List Color) (v : Int × Int) : Option Color :=
  let from_ := (Oklab.labOf (grounds.headD Color.white)).L
  let clears (c : Color) := grounds.all fun g => decide (req ≤ Contrast.contrastMilli c g)
  ([4, 3, 2, 1, 0] : List Int).findSome? fun q =>
    let a := q * v.1 / 4
    let b := q * v.2 / 4
    (nearestPass (fun L => clears (lab a b L)) from_).bind
      fun L => if clears (lab a b L) then some (lab a b L) else none

/-- **A tone clears what it was asked to on every ground it was asked for**:
every answer is guarded by the judged ratios themselves, so no search
argument is load-bearing. -/
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

/-- **A tone clears what it was asked to**, on its ground. -/
public theorem tone_meets {req : Nat} {ground c : Color} {v : Int × Int}
    (h : tone req ground v = some c) : req ≤ Contrast.contrastMilli c ground :=
  toneOn_contract h ground (List.mem_singleton.mpr rfl)

/-- A derived hue's tone on the grounds it must read on: the code tone, or
text AA where they leave no lightness for it. -/
private def hueTone (grounds : List Color) (v : Int × Int) : Option Color :=
  (toneOn codeTone grounds v).orElse fun _ => toneOn Contrast.aaText grounds v

/-- The grounds a derived hue's tone must read on: the listing's own, and,
under a palette generated from seeds, the paper and the fills a block's body
stands on, so a token sets in one colour wherever its listing stands — and
the TeX export's one set of token macros sets it alike. -/
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

/-- The palette roles the rule reads, each passed over where it is another
role's colour already: an alert that is the ink, an example that is the
ink or the alert, a muted step that is the alert. -/
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

/-- Whether the rule leaves role `r` open: the palette gives it nothing to
read, whatever the ground. Only then does a listing style colour it. -/
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

/-- Keywords and names: a tone of the ink's own hue where it stands clear
of both the literal's hue and the alert's, else the ink. -/
private def familyOf (p : Reads) (grounds : List Color) (literal : Option (Int × Int)) : Derived :=
  match p.fg with
  | none => .none
  | some _ =>
    match ((p.fg.bind hue?).filter fun u => literal.all (clear u) &&
          (p.alert.bind hue?).all (clear u)).bind
        (fun u => hueTone grounds (scaled p.chroma u)) with
    | some c => .color c
    | none => .ink

/-- Keywords and names under a palette generated from seeds, each a hue of
its own: keywords the ink's own where it stands clear of the literal's and
the alert's, else the middle of the widest arc the hues already set (the
ink's, the alert's, the literal's) leave open; names the middle of the
widest arc left open once the keywords' hue is set too. -/
private def seededFamily (p : Reads) (grounds : List Color) (literal : Option (Int × Int)) :
    Derived × Derived :=
  match p.fg with
  | none => (.none, .none)
  | some _ =>
    let hueOf (v : Int × Int) : Int := Oklab.hueMilli v.1 v.2
    let dirOf (h : Int) : Int × Int := let l := Oklab.ofLch 0 p.chroma h; (l.a, l.b)
    let toned (v : Int × Int) : Derived := (hueTone grounds (scaled p.chroma v)).elim .ink .color
    let set := (p.hues ++ literal.toList).map hueOf
    let own := (p.fg.bind hue?).filter fun u =>
      literal.all (clear u) && (p.alert.bind hue?).all (clear u)
    let keyword := own.orElse fun _ => (openArc set).map dirOf
    let name := (openArc (set ++ (keyword.map hueOf).toList)).map dirOf
    (keyword.elim .ink toned, name.elim .ink toned)

/-- The quietest tone of the ink's own hue and chroma that still reads as
text on every ground, 0.10 above WCAG 2.2's 4.5:1: a muted step derived from
the palette by a rule, never a fixed mix. The ink itself where no lighter
tone reads. -/
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

private theorem seededFamily_none {p : Reads} {grounds : List Color} {l : Option (Int × Int)}
    (h : (seededFamily p grounds l).1 = .none ∨ (seededFamily p grounds l).2 = .none) :
    p.fg = none := by
  unfold seededFamily at h
  split at h
  · assumption
  · have toned : ∀ v : Int × Int,
        (hueTone grounds (scaled p.chroma v)).elim Derived.ink Derived.color ≠ .none :=
      fun v => elim_ink_ne_none _ _ fun _ => by simp
    rcases h with h | h <;> exact absurd h (elim_ink_ne_none _ _ toned)

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

/-- Keywords and names: the ink's hue family, or under a palette generated
from seeds a hue of their own each (`seededFamily`). -/
private def keywordsNames (pal : Palette) (p : Reads) (grounds : List Color)
    (literal : Option (Int × Int)) : Derived × Derived :=
  match pal.seeded with
  | some _ => seededFamily p grounds literal
  | none => let family := familyOf p grounds literal; (family, family)

private theorem keywordsNames_none {pal : Palette} {p : Reads} {grounds : List Color}
    {l : Option (Int × Int)}
    (h : (keywordsNames pal p grounds l).1 = .none ∨ (keywordsNames pal p grounds l).2 = .none) :
    p.fg = none := by
  unfold keywordsNames at h
  split at h
  · exact seededFamily_none h
  · exact familyOf_none (by dsimp only at h; rcases h with h | h <;> exact h)

/-- The rule, on the ground a listing stands on: every role derived at once,
each shared value computed once. -/
public def derive (pal : Palette) (ground : Color) : RoleTable Derived :=
  let p := reads pal
  let grounds := toneGrounds pal ground
  let literal := literalOf p grounds
  let family := keywordsNames pal p grounds literal.2
  { ink := .ink, keyword := family.1, name := family.2, literal := literal.1
    comment := commentOf p grounds, error := errorOf p }

/-- **The rule leaves a role to the style only where it `opens`**: on every
ground, a role the palette gives the rule something to read for derives a
colour, or the ink. -/
public theorem derive_none_opens (pal : Palette) (ground : Color) (r : ListingHighlight.Role)
    (h : (derive pal ground).get r = .none) : opens pal r = true := by
  cases r <;> simp only [derive, RoleTable.get] at h
  · simp at h
  · simp [opens, keywordsNames_none (Or.inl h)]
  · simp [opens, keywordsNames_none (Or.inr h)]
  · obtain ⟨he, hh⟩ := literalOf_none h
    simp [opens, he, hh]
  · obtain ⟨hm, hf⟩ := commentOf_none h
    simp [opens, hm, hf]
  · simp [opens, errorOf_none h]

/-- **The one resolving site for the code roles.** A role's own key first,
shipped as the document declared it; then the rule (`derive`); then the
listing style's colour for the role. A palette role the rule reads ships
as that role on the page it is declared for — the colour the document
chose, under its key, judged by the contrast report as its prose uses are
— and, on any other ground, adapted to that ground under the code role's
own key, as a colour the document did not choose there. -/
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

/-- **A colour shipped as declared is one the palette declares, under the
key it ships under**: a code role's own, or the palette role the rule
reads. -/
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

/-- **Every other colour ships under the role's own key**: what the rule
derives, adapts or takes from the style is the code role's, never a
palette role's. -/
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

/-- Whether the listing style gives role `r` its colour under the palette:
no key of the role's own, a type the style colours the role by, and
nothing for the rule to read. A style no role reads changes no page the
palette sets. -/
public def styleReads (pal : Palette) (r : ListingHighlight.Role) : Bool :=
  (Design.declared? pal (Ir.Role.ofCode r)).isNone && (roleStyleKind r).isSome && opens pal r

/-- **A role no style reads resolves alike under every style**, on every
ground: the style decides a colour only where `styleReads` says it does,
so the inert-style diagnostic judges exactly what both artifacts ship. -/
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
