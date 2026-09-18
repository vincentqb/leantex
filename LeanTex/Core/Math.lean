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

/-- The cramped variant of a style: how a radicand sets (TeXbook
Appendix G rule 11 — the radicand of `\sqrt` is set in the cramped
current style). -/
def cramp : MathStyle → MathStyle
  | .display _ => .display true
  | .text _ => .text true
  | .script _ => .script true
  | .scriptscript _ => .scriptscript true

/-- The style of a fraction's numerator (TeXbook Appendix G rule 15:
display sets its numerator in text style, text in script, script and
scriptscript in scriptscript; cramping carries). -/
def fracNum : MathStyle → MathStyle
  | .display c => .text c
  | .text c => .script c
  | .script c | .scriptscript c => .scriptscript c

/-- The style of a fraction's denominator: the numerator's, cramped
(TeXbook Appendix G rule 15). -/
def fracDen (s : MathStyle) : MathStyle :=
  s.fracNum.cramp

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

/-- The fraction styles descend like the script styles (TeXbook Appendix G
rule 15): a numerator never ranks above its base, a denominator is always
cramped, and cramping preserves rank — the radicand of rule 11 sets at the
base's own size. With `sizeFor_mono_rank`, none of these constituents ever
sets larger than the formula it stands in. -/
theorem frac_styles_descend :
    ∀ s ∈ allStyles,
      s.fracNum.rank ≤ s.rank ∧ s.fracDen.rank ≤ s.rank ∧
      s.fracDen.cramped = true ∧ s.cramp.rank = s.rank := by decide

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
style — so no script ever sets larger than the formula it hangs from.
Limits are scripts (Appendix G rule 13a sets an upper limit in superscript
style and a lower limit in subscript style), so this theorem covers limit
sizes too — no restatement needed. -/
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

/-- `sizeFor` is monotone in the style's rank, over every font's clamped
percentages: a style no deeper in the progression never sets larger. This
is what turns `frac_styles_descend` into sizes — a numerator, denominator,
or radicand never sets larger than its base. -/
theorem sizeFor_mono_rank (a b base : Int) (hb : 0 ≤ base) (s s' : MathStyle)
    (h : s'.rank ≤ s.rank) :
    sizeFor (ScriptScales.clamp a b) base s' ≤
      sizeFor (ScriptScales.clamp a b) base s := by
  have hsc := clamp_le_100 a b
  have hss := clamp_ss_le_script a b
  have hscript :
      base * (ScriptScales.clamp a b).scriptscript / 100 ≤
        base * (ScriptScales.clamp a b).script / 100 :=
    size_scale_le base hb _ _ hss
  have hbase : base * (ScriptScales.clamp a b).script / 100 ≤ base :=
    size_pct_le_base base hb _ hsc
  cases s <;> cases s' <;>
    simp only [MathStyle.rank] at h <;>
    first
      | omega
      | (simp only [sizeFor] <;>
         first
           | exact Int.le_refl _
           | exact hbase
           | exact hscript
           | exact Int.le_trans hscript hbase)

/-- The size the math face sets at beside a body set at `bodySize`, chosen
so the two x-heights agree: fontspec's `Scale=MatchLowercase` rule — scale
the incoming face so its lowercase height matches the current font's
(fontspec manual, "Font selection" § Scale) — as one integer expression.
`xhB`/`upemB` are the body face's x-height and units per em in font units,
`xhM`/`upemM` the math face's; the ideal scale factor is
`(xhB/upemB) · (upemM/xhM)` and the one honest slack is the division
quantum, bounded by the agreement theorems below. -/
def mathSize (bodySize xhB upemB xhM upemM : Nat) : Nat :=
  bodySize * xhB * upemM / (upemB * xhM)

theorem mathSize_le_body_xheight (bodySize xhB upemB xhM upemM : Nat) :
    mathSize bodySize xhB upemB xhM upemM * xhM / upemM ≤
      bodySize * xhB * upemM / (upemB * upemM) := by
  unfold mathSize
  rw [Nat.div_div_eq_div_mul (bodySize * xhB * upemM) upemB xhM |>.symm]
  calc bodySize * xhB * upemM / upemB / xhM * xhM / upemM
      ≤ bodySize * xhB * upemM / upemB / upemM :=
        Nat.div_le_div_right (Nat.div_mul_le_self _ _)
    _ = bodySize * xhB * upemM / (upemB * upemM) := Nat.div_div_eq_div_mul ..

/-- One side of optical agreement: at `mathSize`, the math face's x-height
never exceeds the body's — the match errs toward the body, never past it. -/
theorem mathSize_matches (bodySize xhB upemB xhM upemM : Nat) (h : 0 < upemM) :
    mathSize bodySize xhB upemB xhM upemM * xhM / upemM ≤ bodySize * xhB / upemB := by
  have := mathSize_le_body_xheight bodySize xhB upemB xhM upemM
  rwa [Nat.mul_div_mul_right _ _ h] at this

/-- The other side: the undershoot is at most one quantum of the integer
arithmetic — the body's x-height in sp exceeds the scaled math x-height by
at most 1. The hypotheses hold for every parsed font: `upem` is normalized
positive at parse and `Font.xHeightOptical` is clamped into `(0, upem]`.
With `mathSize_matches`: after scaling, the two x-heights agree to within
one sp — the exact-ratio reading of fontspec's `MatchLowercase`, quantized. -/
theorem body_xheight_le_mathSize_next (bodySize xhB upemB xhM upemM : Nat)
    (hB : 0 < upemB) (hM : 0 < xhM) (hle : xhM ≤ upemM) :
    bodySize * xhB / upemB ≤ mathSize bodySize xhB upemB xhM upemM * xhM / upemM + 1 := by
  have hupemM : 0 < upemM := Nat.lt_of_lt_of_le hM hle
  generalize hq : mathSize bodySize xhB upemB xhM upemM = q
  have h2 : bodySize * xhB * upemM < (q + 1) * (upemB * xhM) :=
    (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hM)).mp (by simp [mathSize] at hq; omega)
  have h1 : bodySize * xhB / upemB * upemB ≤ bodySize * xhB := Nat.div_mul_le_self _ _
  have h3 : bodySize * xhB / upemB * upemB * upemM < (q + 1) * (upemB * xhM) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right upemM h1) h2
  have h4 : bodySize * xhB / upemB * upemM * upemB < (q + 1) * xhM * upemB := by
    have e1 : bodySize * xhB / upemB * upemM * upemB
        = bodySize * xhB / upemB * upemB * upemM := by ac_rfl
    have e2 : (q + 1) * xhM * upemB = (q + 1) * (upemB * xhM) := by ac_rfl
    rw [e1, e2]; exact h3
  have h5 : bodySize * xhB / upemB * upemM < (q + 1) * xhM :=
    Nat.lt_of_mul_lt_mul_right h4
  have h6 : bodySize * xhB / upemB * upemM ≤ q * xhM + upemM := by
    have e : (q + 1) * xhM = q * xhM + xhM := Nat.succ_mul q xhM
    omega
  have h7 : bodySize * xhB / upemB ≤ (q * xhM + upemM) / upemM :=
    (Nat.le_div_iff_mul_le hupemM).mpr h6
  rwa [Nat.add_div_right _ hupemM] at h7

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

/-- How a grid column places a narrower cell inside the column's width. -/
inductive ColAlign where
  | left
  | center
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The column model of a math grid. `align` alternates right- and
left-aligned columns in pairs that abut at the alignment point, each even
cell opening with an empty Ord atom so a leading relation keeps its thick
space — amsmath's `\align@preamble`, whose even columns read `{}#`
(amsmath.dtx). `gather` is one centred column. `array` takes its
alignments from the document's own column spec (`{lcr}`), text-style
cells, `\arraycolsep` padding around every column (article.cls sets
`\arraycolsep` to 5pt at the 10pt base — half an em a side). -/
inductive GridKind where
  | align
  | gather
  | array (cols : Array ColAlign)
  deriving Repr, BEq, Inhabited

/-- The alignment of column `k` under a grid kind. An `array` column past
its spec centres — the spec mismatch was already diagnosed at elaboration. -/
def GridKind.colAlign : GridKind → Nat → ColAlign
  | .align, k => if k % 2 == 0 then .right else .left
  | .gather, _ => .center
  | .array cols, k => cols.getD k .center

/-- The gap after column `k` of `n`, in mu (18ths of an em at the current
size). `align`'s pair halves abut (the alignment point is exactly the
column boundary); between pairs it takes 2 em — amsmath stretches tabskip
glue across the display width there, which a fixed-width box cannot, so
this is a stated stand-in, not a sourced constant. `array` pays
`\arraycolsep` each side of every column boundary: 5pt+5pt at the 10pt
base is 18 mu (article.cls). -/
def GridKind.gapAfter : GridKind → Nat → Nat → Nat
  | .align, k, n => if k + 1 == n then 0 else if k % 2 == 0 then 0 else 36
  | .gather, _, _ => 0
  | .array _, k, n => if k + 1 == n then 0 else 18

/-- Where column `k` starts, given each column's width and the gap that
follows it: the sum of everything before it. One definition placed cells
and the width theorem both read, so "alignment points align" is a fact
about this function — every row consults the same offsets. -/
def colOffset (cols : List (Int × Int)) (k : Nat) : Int :=
  match cols, k with
  | _, 0 => 0
  | [], _ + 1 => 0
  | (w, g) :: rest, k + 1 => w + g + colOffset rest k

/-- Past the last column, the offset is the whole grid: the assembled width
is the sum of the column widths plus the declared gaps — no drift, whatever
the widths. -/
theorem colOffset_total (cols : List (Int × Int)) :
    colOffset cols cols.length = (cols.map fun c => c.1 + c.2).foldr (· + ·) 0 := by
  induction cols with
  | nil => rfl
  | cons c rest ih =>
    simp only [colOffset, List.length, List.map, List.foldr, ih]

/-- The kern that places a box `inner` wide inside a column `outer` wide. -/
def ColAlign.pad (a : ColAlign) (outer inner : Int) : Int :=
  match a with
  | .left => 0
  | .right => outer - inner
  | .center => (outer - inner) / 2

/-- Padding stays inside the column: the cell starts at or after the
column's left edge and ends at or before its right edge — so a padded cell
can never disturb a neighbouring column's alignment point. -/
theorem pad_within (a : ColAlign) (outer inner : Int) (_h : inner ≤ outer) :
    0 ≤ a.pad outer inner ∧ a.pad outer inner + inner ≤ outer := by
  cases a <;> simp only [ColAlign.pad] <;> omega

/-- Centring is symmetric to within the one sp integer division may owe:
the space left after the cell differs from the space before it by at most
one. Also what "display limits are centred on the operator" means in sp. -/
theorem pad_center_symmetric (outer inner : Int) (_h : inner ≤ outer) :
    0 ≤ outer - (2 * ColAlign.pad .center outer inner + inner) ∧
    outer - (2 * ColAlign.pad .center outer inner + inner) ≤ 1 := by
  simp only [ColAlign.pad]
  omega

/-- The variant a delimiter (or radical, or display operator) grows to: the
first in the font's size ladder at least `target` tall, else the last —
the MATH spec orders variants by increasing size, so the last is the
largest the font offers (glyph assembly, past it, is not read in this
slice). -/
def pickVariant (target : Int) : List (Nat × Int) → Option (Nat × Int)
  | [] => none
  | [v] => some v
  | v :: rest@(_ :: _) => if target ≤ v.2 then some v else pickVariant target rest

/-- A grown delimiter covers its content whenever the font can: if any
variant reaches the target, the picked one does. With the spec's
increasing-size order this is the smallest sufficient variant; without it,
still a sufficient one. -/
theorem pickVariant_covers (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
    (hp : pickVariant target vs = some v) (hw : ∃ w ∈ vs, target ≤ w.2) :
    target ≤ v.2 := by
  induction vs with
  | nil => simp [pickVariant] at hp
  | cons x rest ih =>
    obtain ⟨w, hmem, hwt⟩ := hw
    cases rest with
    | nil =>
      simp only [pickVariant, Option.some.injEq] at hp
      rcases List.mem_singleton.mp hmem with rfl
      exact hp ▸ hwt
    | cons y t =>
      simp only [pickVariant] at hp
      split at hp
      next hx =>
        cases hp
        exact hx
      next hx =>
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact absurd hwt hx
        · exact ih hp ⟨w, hmem', hwt⟩

/-- What is picked is a variant the font really has — never an invented
glyph. -/
theorem pickVariant_mem (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
    (hp : pickVariant target vs = some v) : v ∈ vs := by
  induction vs with
  | nil => simp [pickVariant] at hp
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [pickVariant, Option.some.injEq] at hp
      subst hp
      exact List.mem_singleton_self ..
    | cons y t =>
      simp only [pickVariant] at hp
      split at hp
      next =>
        cases hp
        exact List.mem_cons_self ..
      next =>
        exact List.mem_cons_of_mem x (ih hp)

mutual

/-- What an atom sets: one scalar, an upright word (a function name), a
braced sub-list, or one of the assembled constructions — a fraction, a
radical, a `\left…\right` group, a grid. The scalar of a `sym` is final —
variables were mapped to their mathematical-alphanumeric italic code
points at elaboration (`x` is U+1D465), digits and function names stay
upright, per the convention TeX and ISO 80000-2 share: variables italic,
everything with a fixed meaning upright. -/
inductive MNucleus where
  | sym (c : Char)
  | word (s : String)
  | list (body : MList)
  /-- `\frac`/`\over`: numerator over denominator, positioned from the
  MATH constants, spaced as one Inner atom (TeXbook ch. 17 — fractions and
  `\left…\right` groups are Inner). -/
  | frac (num den : MList)
  /-- `\sqrt[deg]{body}`: `deg` is `.nil` for the plain square root. -/
  | rad (deg : MList) (body : MList)
  /-- `\left l body \right r`: `none` is the empty `.` delimiter. -/
  | delim (l : Option Char) (r : Option Char) (body : MList)
  /-- An alignment: `align`/`gather`/`array` rows, rectangular by the time
  layout sees them (`MRows.pad`; a ragged source row was diagnosed). -/
  | grid (kind : GridKind) (rows : MRows)
  deriving Repr, BEq

/-- One item of a math list: an atom with its class, nucleus, scripts, and
whether its scripts set as limits in display style (TeX's
`\displaylimits`, the default for `\sum` and the limit-taking function
names of TeXbook p. 162) — or an explicit space. Scripts are `MList`s with
`.nil` meaning none: an empty script and an absent one set the same
nothing. -/
inductive MItem where
  | atom (cls : MathClass) (nuc : MNucleus) (sup : MList) (sub : MList)
      (limits : Bool)
  /-- Explicit space in mu (18ths of an em at the current size); negative
  for `\!`. -/
  | space (mu : Int)
  deriving Repr, BEq

inductive MList where
  | nil
  | cons (head : MItem) (tail : MList)
  deriving Repr, BEq

/-- One grid row: its cells. -/
inductive MRow where
  | nil
  | cons (cell : MList) (tail : MRow)
  deriving Repr, BEq

inductive MRows where
  | nil
  | cons (row : MRow) (tail : MRows)
  deriving Repr, BEq

end

instance : Inhabited MList := ⟨.nil⟩
instance : Inhabited MItem := ⟨.space 0⟩
instance : Inhabited MNucleus := ⟨.sym '?'⟩
instance : Inhabited MRow := ⟨.nil⟩
instance : Inhabited MRows := ⟨.nil⟩

def MList.ofList (xs : List MItem) : MList :=
  match xs with
  | [] => .nil
  | x :: rest => .cons x (ofList rest)

def MRow.ofList (xs : List MList) : MRow :=
  match xs with
  | [] => .nil
  | x :: rest => .cons x (ofList rest)

def MRows.ofList (xs : List MRow) : MRows :=
  match xs with
  | [] => .nil
  | x :: rest => .cons x (ofList rest)

def MRow.cells : MRow → List MList
  | .nil => []
  | .cons c rest => c :: cells rest

def MRows.rows : MRows → List MRow
  | .nil => []
  | .cons r rest => r :: rows rest

def MRow.length (r : MRow) : Nat := r.cells.length

/-- `n` empty cells. -/
def MRow.blanks : Nat → MRow
  | 0 => .nil
  | n + 1 => .cons .nil (blanks n)

def MRow.append (r : MRow) (s : MRow) : MRow :=
  match r with
  | .nil => s
  | .cons c rest => .cons c (rest.append s)

/-- The row padded to `n` cells with empty ones — how a diagnosed ragged
row still renders everything it wrote. -/
def MRow.pad (r : MRow) (n : Nat) : MRow :=
  r.append (blanks (n - r.length))

theorem MRow.blanks_cells (n : Nat) :
    (MRow.blanks n).cells = List.replicate n .nil := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [blanks, cells, ih, List.replicate]

theorem MRow.append_cells : ∀ (r s : MRow), (r.append s).cells = r.cells ++ s.cells
  | .nil, _ => rfl
  | .cons c rest, s => by
    simp only [append, cells, append_cells rest s, List.cons_append]

/-- Padding conserves content exactly: the padded row is the original's
cells followed by empties — nothing dropped, nothing reordered, and (for
`length ≤ n`) exactly `n` cells. -/
theorem MRow.pad_cells (r : MRow) (n : Nat) :
    (r.pad n).cells = r.cells ++ List.replicate (n - r.length) .nil := by
  simp only [pad, append_cells, blanks_cells]

theorem MRow.pad_length (r : MRow) (n : Nat) (h : r.length ≤ n) :
    (r.pad n).length = n := by
  simp only [length] at h
  simp only [length, pad_cells, List.length_append, List.length_replicate]
  omega

/-- The widest row: what every row pads to. -/
def MRows.maxCols (rs : MRows) : Nat :=
  (rs.rows.map (·.length)).foldr Nat.max 0

def MRows.pad (rs : MRows) (n : Nat) : MRows :=
  match rs with
  | .nil => .nil
  | .cons r rest => .cons (r.pad n) (pad rest n)

theorem MRows.pad_rows : ∀ (rs : MRows) (n : Nat),
    (rs.pad n).rows = rs.rows.map (·.pad n)
  | .nil, _ => rfl
  | .cons r rest, n => by
    simp only [pad, rows, pad_rows rest n, List.map]

private theorem MRows.length_le_maxCols :
    ∀ (rs : MRows), ∀ r ∈ rs.rows, r.length ≤ rs.maxCols
  | .nil => by intro r h; simp [rows] at h
  | .cons x rest => by
    intro r h
    rcases List.mem_cons.mp h with rfl | h'
    · simp only [maxCols, rows, List.map, List.foldr]
      exact Nat.le_max_left _ _
    · have hrec := length_le_maxCols rest r h'
      simp only [maxCols] at hrec
      simp only [maxCols, rows, List.map, List.foldr]
      exact Nat.le_trans hrec (Nat.le_max_right _ _)

/-- A padded grid is rectangular: every row of `pad rs rs.maxCols` has
exactly `maxCols` cells — the invariant that keeps a column's alignment
point one x for every row. -/
theorem MRows.pad_rectangular (rs : MRows) :
    ∀ r ∈ (rs.pad rs.maxCols).rows, r.length = rs.maxCols := by
  intro r h
  rw [pad_rows] at h
  obtain ⟨r0, hmem, rfl⟩ := List.mem_map.mp h
  exact MRow.pad_length r0 _ (length_le_maxCols rs r0 hmem)

/-- The class an item contributes to spacing. Spaces carry none — spacing
is inserted only between directly adjacent atoms. -/
def MItem.classOf : MItem → Option MathClass
  | .atom cls _ _ _ _ => some cls
  | .space _ => none

/-- The classes of a list's atoms in order, spaces skipped: what `degrade`
normalizes and the spacing walk consumes. Shallow — each sub-list is
normalized independently, as TeX processes each mlist. -/
def MList.classes : MList → List MathClass
  | .nil => []
  | .cons (.atom cls _ _ _ _) rest => cls :: classes rest
  | .cons (.space _) rest => classes rest

mutual

/-- Every scalar a math list can ask the math face for, `docScalars`-style:
the driver checks coverage before layout, keeping layout pure. -/
def MItem.scalars (acc : Array Char) : MItem → Array Char
  | .atom _ nuc sup sub _ =>
    MList.scalarsList (MList.scalarsList (nuc.scalars acc) sup) sub
  | .space _ => acc

def MNucleus.scalars (acc : Array Char) : MNucleus → Array Char
  | .sym c => acc.push c
  | .word s => s.foldl (·.push ·) acc
  | .list body => MList.scalarsList acc body
  | .frac num den => MList.scalarsList (MList.scalarsList acc num) den
  | .rad deg body => MList.scalarsList (MList.scalarsList acc deg) body
  | .delim l r body =>
    let acc := match l with
      | some c => acc.push c
      | none => acc
    let acc := match r with
      | some c => acc.push c
      | none => acc
    MList.scalarsList acc body
  | .grid _ rows => MRows.scalarsRows acc rows

def MList.scalarsList (acc : Array Char) : MList → Array Char
  | .nil => acc
  | .cons x rest => MList.scalarsList (x.scalars acc) rest

def MRow.scalarsRow (acc : Array Char) : MRow → Array Char
  | .nil => acc
  | .cons c rest => MRow.scalarsRow (MList.scalarsList acc c) rest

def MRows.scalarsRows (acc : Array Char) : MRows → Array Char
  | .nil => acc
  | .cons r rest => MRows.scalarsRows (MRow.scalarsRow acc r) rest

end

end LeanTex.Core.Math
