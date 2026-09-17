namespace LeanTex.Core.Math

/-! Math atoms, styles, and the inter-atom spacing table: TeX's model
(TeXbook chapters 17–18, Appendix G) over OpenType MATH metrics (PLAN,
2026-09-17 M6 design entry). This file is the pure data and the theorems;
measurement against a font happens in layout. -/

/-- TeX's eight atom classes (TeXbook ch. 17): the spacing between two
adjacent atoms is a function of their classes and the style. -/
inductive MathClass where
  | ord
  | op
  | bin
  | rel
  | opening
  | closing
  | punct
  | inner
  deriving Repr, BEq, DecidableEq, Inhabited

def allClasses : List MathClass :=
  [.ord, .op, .bin, .rel, .opening, .closing, .punct, .inner]

def MathClass.label : MathClass → String
  | .ord => "ord"
  | .op => "op"
  | .bin => "bin"
  | .rel => "rel"
  | .opening => "open"
  | .closing => "close"
  | .punct => "punct"
  | .inner => "inner"

/-- The four styles with their cramped variants (TeXbook ch. 17). Cramped
styles arise under subscripts; the only difference this slice reads is the
superscript shift (`superscriptShiftUpCramped`). -/
inductive MathStyle where
  | display (cramped : Bool)
  | text (cramped : Bool)
  | script (cramped : Bool)
  | scriptscript (cramped : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

def allStyles : List MathStyle :=
  [.display false, .display true, .text false, .text true,
   .script false, .script true, .scriptscript false, .scriptscript true]

namespace MathStyle

/-- Depth in the progression display → text → script → scriptscript. -/
def rank : MathStyle → Nat
  | .display _ => 3
  | .text _ => 2
  | .script _ => 1
  | .scriptscript _ => 0

def cramped : MathStyle → Bool
  | .display c | .text c | .script c | .scriptscript c => c

/-- The style of a superscript (TeXbook p. 141): display and text scripts
set in script style, script and scriptscript in scriptscript; cramping
carries. -/
def sup : MathStyle → MathStyle
  | .display c | .text c => .script c
  | .script c | .scriptscript c => .scriptscript c

/-- The style of a subscript: the superscript's style, cramped. -/
def sub (s : MathStyle) : MathStyle :=
  match s.sup with
  | .display _ => .display true
  | .text _ => .text true
  | .script _ => .script true
  | .scriptscript _ => .scriptscript true

/-- Script styles suppress the conditional entries of the spacing table:
TeX inserts medium and thick spaces (and the parenthesized thin ones) "in
display and text styles only" (TeXbook p. 170). -/
def scriptish (s : MathStyle) : Bool :=
  s.rank ≤ 1

end MathStyle

/-- The style progression is decreasing: a script's style never ranks above
its base's, and it ranks strictly below whenever the base is not already at
the scriptscript floor. The layout recursion is structural on the formula
tree; this is what makes the style parameter it threads meaningful — sizes
cannot shrink forever, because the progression bottoms out. -/
theorem style_progression_decreasing :
    ∀ s ∈ allStyles,
      (s.sup.rank ≤ s.rank ∧ s.sub.rank ≤ s.rank) ∧
      (s.rank = 0 ∨ (s.sup.rank < s.rank ∧ s.sub.rank < s.rank)) := by decide

/-- scriptscript is the fixed point of the progression: nesting scripts
past the second level changes nothing, cramped or not. -/
theorem scriptscript_fixed_point :
    ∀ s ∈ allStyles, s.rank = 0 → s.sup = s ∧ s.sub.rank = 0 := by decide

/-- A subscript is always cramped (TeXbook p. 141). -/
theorem sub_cramped : ∀ s ∈ allStyles, s.sub.cramped = true := by decide

/-- Sanitized script scale percentages from a font's MathConstants: the
spec suggests 80/60 but declares no bounds, and "script sizes never grow"
must hold for every font, not only well-behaved ones. Clamped into (0,100]
with scriptscript no larger than script. -/
structure ScriptScales where
  script : Nat
  scriptscript : Nat
  deriving Repr, BEq, Inhabited

def ScriptScales.clamp (script scriptscript : Int) : ScriptScales :=
  { script := (script.toNat.min 100).max 1
    scriptscript := (scriptscript.toNat.min ((script.toNat.min 100).max 1)).max 1 }

/-- Font size for a style, from the base size: display and text set at the
base, script and scriptscript at the font's declared percentages. Sizes are
per style from the base, not compounding — which is why the scriptscript
floor also bounds the size. -/
def sizeFor (k : ScriptScales) (base : Int) : MathStyle → Int
  | .display _ | .text _ => base
  | .script _ => base * k.script / 100
  | .scriptscript _ => base * k.scriptscript / 100

theorem clamp_le_100 (a b : Int) : (ScriptScales.clamp a b).script ≤ 100 :=
  Nat.max_le.mpr ⟨Nat.min_le_right _ _, by decide⟩

theorem clamp_ss_le_script (a b : Int) :
    (ScriptScales.clamp a b).scriptscript ≤ (ScriptScales.clamp a b).script :=
  Nat.max_le.mpr ⟨Nat.min_le_right _ _, Nat.le_max_right _ _⟩

private theorem size_scale_le (base : Int) (hb : 0 ≤ base) (p q : Nat) (h : p ≤ q) :
    base * p / 100 ≤ base * q / 100 := by
  apply Int.ediv_le_ediv (by decide)
  exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast h) hb

private theorem size_pct_le_base (base : Int) (hb : 0 ≤ base) (p : Nat) (hp : p ≤ 100) :
    base * p / 100 ≤ base := by
  have h : base * p / 100 ≤ base * 100 / 100 := size_scale_le base hb p 100 hp
  have h2 : base * 100 / 100 = base := Int.mul_ediv_cancel _ (by decide)
  exact Int.le_trans h (Int.le_of_eq h2)

/-- Sizes shrink monotonically along the progression: for every font's
(clamped) percentages, a script's size never exceeds its base's, at every
style — so no script ever sets larger than the formula it hangs from. -/
theorem sizes_shrink (a b base : Int) (hb : 0 ≤ base) (s : MathStyle) :
    sizeFor (ScriptScales.clamp a b) base s.sup ≤
      sizeFor (ScriptScales.clamp a b) base s ∧
    sizeFor (ScriptScales.clamp a b) base s.sub ≤
      sizeFor (ScriptScales.clamp a b) base s := by
  have hsc := clamp_le_100 a b
  have hss := clamp_ss_le_script a b
  have hscript :
      base * (ScriptScales.clamp a b).scriptscript / 100 ≤
        base * (ScriptScales.clamp a b).script / 100 :=
    size_scale_le base hb _ _ hss
  have hbase : base * (ScriptScales.clamp a b).script / 100 ≤ base :=
    size_pct_le_base base hb _ hsc
  cases s <;>
    simp only [sizeFor, MathStyle.sup, MathStyle.sub] <;>
    exact ⟨by first | exact hbase | exact hscript | exact Int.le_refl _,
           by first | exact hbase | exact hscript | exact Int.le_refl _⟩

/-- Inter-atom space: none, thin (3 mu), medium (4 mu), or thick (5 mu),
where 18 mu is one em of the math font at the current style's size
(TeXbook p. 168). Set at natural width — the rubber TeX gives `\medmuskip`
and `\thickmuskip` is not modelled in this slice, deliberately: a math box
is one unbreakable, unstretchable box in the paragraph. -/
inductive MathSpace where
  | none
  | thin
  | med
  | thick
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Numerator over 18ths of an em. -/
def MathSpace.mu : MathSpace → Nat
  | .none => 0
  | .thin => 3
  | .med => 4
  | .thick => 5

/-- TeX's inter-atom spacing table (TeXbook p. 170): the space between two
adjacent atoms, and whether it survives script styles (`true` for the
unparenthesized entries; the parenthesized ones are inserted in display and
text style only). Pairs the TeXbook marks `*` cannot survive Bin
degradation (`degrade`) and are given `.none`; `spacing_agrees_with_luatex`
below shows they are never consulted. -/
def texSpacing (l r : MathClass) : MathSpace × Bool :=
  match l, r with
  | .ord, .op => (.thin, true)
  | .ord, .bin => (.med, false)
  | .ord, .rel => (.thick, false)
  | .ord, .inner => (.thin, false)
  | .op, .ord => (.thin, true)
  | .op, .op => (.thin, true)
  | .op, .rel => (.thick, false)
  | .op, .inner => (.thin, false)
  | .bin, .ord => (.med, false)
  | .bin, .op => (.med, false)
  | .bin, .opening => (.med, false)
  | .bin, .inner => (.med, false)
  | .rel, .ord => (.thick, false)
  | .rel, .op => (.thick, false)
  | .rel, .opening => (.thick, false)
  | .rel, .inner => (.thick, false)
  | .closing, .op => (.thin, true)
  | .closing, .bin => (.med, false)
  | .closing, .rel => (.thick, false)
  | .closing, .inner => (.thin, false)
  | .punct, .ord => (.thin, false)
  | .punct, .op => (.thin, false)
  | .punct, .rel => (.thin, false)
  | .punct, .opening => (.thin, false)
  | .punct, .closing => (.thin, false)
  | .punct, .punct => (.thin, false)
  | .punct, .inner => (.thin, false)
  | .inner, .ord => (.thin, false)
  | .inner, .op => (.thin, true)
  | .inner, .bin => (.med, false)
  | .inner, .rel => (.thick, false)
  | .inner, .opening => (.thin, false)
  | .inner, .punct => (.thin, false)
  | .inner, .inner => (.thin, false)
  | _, _ => (.none, false)

/-- The space the engine inserts between adjacent atoms of classes `l` and
`r` in style `s`: the table entry, with the conditional entries suppressed
in script styles. Total by construction — every pair of classes and every
style has an answer. -/
def spacing (l r : MathClass) (s : MathStyle) : MathSpace :=
  let (sp, always) := texSpacing l r
  if always || !s.scriptish then sp else .none

/-- Bin degradation, TeX's two rules (TeXbook p. 170; tex.web's
`mlist_to_hlist` first pass): a Bin atom first in the list, last in the
list, or preceded by Bin, Op, Rel, Open, or Punct becomes Ord — the rule
that sets a leading `-x` as a sign rather than a spaced operation — and a
Bin followed by Rel, Close, or Punct becomes Ord too. One forward pass
holding the previous atom pending, since the second rule rewrites it. -/
def degrade (cs : List MathClass) : List MathClass :=
  go #[] none cs |>.toList
where
  binBefore (p : Option MathClass) : Bool :=
    match p with
    | none => true
    | some .bin | some .op | some .rel | some .opening | some .punct => true
    | some _ => false
  go (acc : Array MathClass) (pending : Option MathClass) :
      List MathClass → Array MathClass
  | [] =>
    match pending with
    | some .bin => acc.push .ord
    | some p => acc.push p
    | none => acc
  | c :: rest =>
    let c := if c == .bin && binBefore pending then .ord else c
    let pending := match pending with
      | some .bin =>
        if c == .rel || c == .closing || c == .punct then some .ord else some .bin
      | p => p
    match pending with
    | some p => go (acc.push p) (some c) rest
    | none => go acc (some c) rest

/-- A Bin with nothing to bind on its left is an Ord: `$-x$` sets tight. -/
theorem bin_leading_degrades : degrade [.bin, .ord] = [.ord, .ord] := by decide

/-- Degradation changes classes, never the count or the order. -/
theorem degrade_length : ∀ cs ∈ [[MathClass.ord], [.bin, .bin], [.ord, .bin, .rel],
    [.opening, .bin, .ord, .bin], [.op, .bin, .op]],
    (degrade cs).length = cs.length := by decide

/-- What luatex inserts between the two probe atoms of
`$\mathord{z}\math<l>{x}\math<r>{y}\mathord{w}$`, read out of `\showbox`
dumps (named muskips) on TeX Live 2026, per pair and per style band — the
executable transcription of TeXbook p. 170 *after* Bin degradation. Row
order is `allClasses` for `l`, column order `allClasses` for `r`; mu
numerators (0 / 3 / 4 / 5). -/
def luatexProbe (scriptish : Bool) : List (List Nat) :=
  if scriptish then
    [[0, 3, 0, 0, 0, 0, 0, 0],
     [3, 3, 3, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0],
     [0, 3, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0],
     [0, 3, 0, 0, 0, 0, 0, 0]]
  else
    [[0, 3, 4, 5, 0, 0, 0, 3],
     [3, 3, 3, 5, 0, 0, 0, 3],
     [4, 4, 4, 5, 4, 0, 0, 4],
     [5, 5, 5, 0, 5, 0, 0, 5],
     [0, 0, 0, 0, 0, 0, 0, 0],
     [0, 3, 4, 5, 0, 0, 0, 3],
     [3, 3, 3, 3, 3, 3, 3, 3],
     [3, 3, 4, 5, 3, 0, 3, 3]]

/-- The engine's degradation-then-spacing agrees with luatex on every pair
of written classes in every style: simulating the probe — degrade
`[ord, l, r, ord]`, then read the spacing between the middle pair — gives
exactly the muskip luatex inserted, over all 64 pairs and both style bands.
This is the spacing table's correctness theorem, Bin degradation included. -/
theorem spacing_agrees_with_luatex :
    ∀ s ∈ allStyles, ∀ l ∈ allClasses, ∀ r ∈ allClasses,
      (match degrade [.ord, l, r, .ord] with
       | [_, l', r', _] => (spacing l' r' s).mu
       | _ => 1000) =
      (((luatexProbe s.scriptish).getD (allClasses.idxOf l) []).getD
        (allClasses.idxOf r) 1001) := by decide

mutual

/-- What an atom sets: one scalar, an upright word (a function name), or a
braced sub-list. The scalar of a `sym` is final — variables were mapped to
their mathematical-alphanumeric italic code points at elaboration (`x` is
U+1D465), digits and function names stay upright, per the convention TeX
and ISO 80000-2 share: variables italic, everything with a fixed meaning
upright. -/
inductive MNucleus where
  | sym (c : Char)
  | word (s : String)
  | list (body : MList)
  deriving Repr, BEq

/-- One item of a math list: an atom with its class, nucleus, and scripts,
or an explicit space. Scripts are `MList`s with `.nil` meaning none: an
empty script and an absent one set the same nothing. -/
inductive MItem where
  | atom (cls : MathClass) (nuc : MNucleus) (sup : MList) (sub : MList)
  /-- Explicit space in mu (18ths of an em at the current size); negative
  for `\!`. -/
  | space (mu : Int)
  deriving Repr, BEq

inductive MList where
  | nil
  | cons (head : MItem) (tail : MList)
  deriving Repr, BEq

end

instance : Inhabited MList := ⟨.nil⟩
instance : Inhabited MItem := ⟨.space 0⟩
instance : Inhabited MNucleus := ⟨.sym '?'⟩

def MList.ofList (xs : List MItem) : MList :=
  match xs with
  | [] => .nil
  | x :: rest => .cons x (ofList rest)

/-- The class an item contributes to spacing. Spaces carry none — spacing
is inserted only between directly adjacent atoms. -/
def MItem.classOf : MItem → Option MathClass
  | .atom cls _ _ _ => some cls
  | .space _ => none

/-- The classes of a list's atoms in order, spaces skipped: what `degrade`
normalizes and the spacing walk consumes. Shallow — each sub-list is
normalized independently, as TeX processes each mlist. -/
def MList.classes : MList → List MathClass
  | .nil => []
  | .cons (.atom cls _ _ _) rest => cls :: classes rest
  | .cons (.space _) rest => classes rest

mutual

/-- Every scalar a math list can ask the math face for, `docScalars`-style:
the driver checks coverage before layout, keeping layout pure. -/
def MItem.scalars (acc : Array Char) : MItem → Array Char
  | .atom _ nuc sup sub =>
    MList.scalarsList (MList.scalarsList (nuc.scalars acc) sup) sub
  | .space _ => acc

def MNucleus.scalars (acc : Array Char) : MNucleus → Array Char
  | .sym c => acc.push c
  | .word s => s.foldl (·.push ·) acc
  | .list body => MList.scalarsList acc body

def MList.scalarsList (acc : Array Char) : MList → Array Char
  | .nil => acc
  | .cons x rest => MList.scalarsList (x.scalars acc) rest

end

end LeanTex.Core.Math
