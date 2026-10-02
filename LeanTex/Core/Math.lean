import LeanTex.Core.Color

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

/-- The math alphabets a formula can ask for by command (`\mathbb`,
`\mathcal`, …): each is one remap of a letter's scalar into its Unicode
Mathematical Alphanumeric Symbols form (Unicode ch. 22.2; unicode-math's
`\um_to_usv:nn` mapping does the same). `rm` is the upright alphabet, which
Unicode leaves at the ASCII letters themselves — remapping an italic
variable back is what `\mathrm` means. -/
inductive MathAlphabet where
  | bb
  | cal
  | frak
  | bf
  /-- `\symbfit`: the genuine mathematical bold-italic alphabet — bold
  italic Latin letters (U+1D468/U+1D482 blocks) and bold italic Greek
  (U+1D71C upper, U+1D736 lower, U+1D735 nabla), no digits. Symbol
  sourced (`\sym…` only). -/
  | bfit
  /-- `\symbf` with unicode-math's default `bold-style=TeX`: upright
  bold Latin, digits and Greek capitals, but bold italic lowercase Greek
  (including ∂ and the variant slots). This selects existing
  `bf`/`bfit` ranges; it has no separate Unicode block. -/
  | bfDefault
  | sf
  | tt
  | rm
  | it
  /-- `\bm`/`\boldsymbol`: a near-identity alphabet — everything stays its
  source glyph (`rangeOf` is always `none`, so coverage never marks it and
  the stack falls each scalar through to its source scalar). `\bm{O}` is an
  italic 𝑂, `\bm{5}` a plain 5, `\bm{\alpha}` an italic 𝛼: no over-bold and
  no spurious loss, matching LuaLaTeX where no bold math version is
  declared. Excluded from `allAlphabets`. -/
  | bm
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The distinct Unicode alphabets. `bfDefault` selects ranges of `bf`
and `bfit`, so it must not duplicate them in coverage or `unapply`. -/
def allAlphabets : List MathAlphabet :=
  [.bb, .cal, .frak, .bf, .bfit, .sf, .tt, .rm, .it]

/-- Whether a legacy math alphabet command takes glyphs from the selected
math symbol face or from a text-family slot. unicode-math 0.8r defaults
`mathrm`, `mathit`, `mathbf`, `mathsf`, and `mathtt` to `text`; each accepts
`=sym`. The shape alphabets and `\bm` are always symbol sourced. -/
inductive MathAlphabetSource where
  | sym
  | text
  deriving Repr, BEq, DecidableEq, Inhabited

def MathAlphabetSource.name : MathAlphabetSource → String
  | .sym => "sym"
  | .text => "text"

def MathAlphabetSource.ofName? : String → Option MathAlphabetSource
  | "sym" => some .sym
  | "text" => some .text
  | _ => none

/-- Where a math alphabet node came from, kept on the node so the resolver
knows whether to force the symbol face or consult the document policy.
`.sym` is `\sym…` — the symbol source is forced regardless of
`MathAlphabetSources`. `.doc` is a legacy `\mathrm`/`\mathit`/`\mathbf`/
`\mathsf`/`\mathtt`, `\text…`, `\bm`/`\boldsymbol`, or a plain-TeX
`\cal`/`\frak` — the document's `MathAlphabetSources` decides its source. -/
inductive AlphaSource where
  | doc
  | sym
  deriving Repr, BEq, DecidableEq, Inhabited

/-- unicode-math's five option-driven sources. Typed here even while text-slot
projection remains a scoped compatibility follow-up, so an explicit
`mathrm=sym` is not discarded and no future resolver has to recover policy
from source strings. -/
structure MathAlphabetSources where
  rm : MathAlphabetSource := .text
  it : MathAlphabetSource := .text
  bf : MathAlphabetSource := .text
  sf : MathAlphabetSource := .text
  tt : MathAlphabetSource := .text
  deriving Repr, BEq, Inhabited

def MathAlphabet.sourceKey? : String → Option MathAlphabet
  | "mathrm" => some .rm
  | "mathit" => some .it
  | "mathbf" => some .bf
  | "mathsf" => some .sf
  | "mathtt" => some .tt
  | _ => none

def MathAlphabet.sourceKey : MathAlphabet → Option String
  | .rm => some "mathrm"
  | .it => some "mathit"
  | .bf => some "mathbf"
  | .sf => some "mathsf"
  | .tt => some "mathtt"
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => none

def MathAlphabetSources.get (s : MathAlphabetSources) : MathAlphabet → MathAlphabetSource
  | .rm => s.rm
  | .it => s.it
  | .bf => s.bf
  | .sf => s.sf
  | .tt => s.tt
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => .sym

def MathAlphabetSources.set (s : MathAlphabetSources) (a : MathAlphabet)
    (source : MathAlphabetSource) : MathAlphabetSources :=
  match a with
  | .rm => { s with rm := source }
  | .it => { s with it := source }
  | .bf => { s with bf := source }
  | .sf => { s with sf := source }
  | .tt => { s with tt := source }
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => s

/-- Non-default source options as unicode-math reads them. The boundary
standalone receives the same typed policy as the page. -/
def MathAlphabetSources.options (s : MathAlphabetSources) : Array String :=
  [MathAlphabet.rm, .it, .bf, .sf, .tt].foldl (fun out a =>
    let source := s.get a
    if source == .text then out
    else out.push s!"{a.sourceKey.getD ""}={source.name}") #[]

/-- The plain letter behind a scalar the parser produces: a mathematical
italic Latin letter returns to its ASCII base (including the U+210E Planck
hole `italicVar` mapped `h` to); anything else stays. What lets one
alphabet table serve arguments whose letters were already italicized. -/
def unItalic (c : Char) : Char :=
  if c == '\u210E' then 'h'
  else if 0x1D44E ≤ c.toNat && c.toNat ≤ 0x1D467 then
    Char.ofNat ('a'.toNat + (c.toNat - 0x1D44E))
  else if 0x1D434 ≤ c.toNat && c.toNat ≤ 0x1D44D then
    Char.ofNat ('A'.toNat + (c.toNat - 0x1D434))
  else c

/-- The Letterlike Symbols holes of the Mathematical Alphanumeric block
(Unicode ch. 22.2 — the code chart marks each slot reserved, pointing into
Letterlike Symbols), as `(alphabet, letter, scalar)` rows: the scalars a
naive base-offset map would get wrong, ℝ and ℂ among them. One table read
in both directions (`hole`, `unapply`). -/
def alphaHoles : List (MathAlphabet × Char × Char) :=
  [(.cal, 'B', '\u212C'), (.cal, 'E', '\u2130'), (.cal, 'F', '\u2131'),
   (.cal, 'H', '\u210B'), (.cal, 'I', '\u2110'), (.cal, 'L', '\u2112'),
   (.cal, 'M', '\u2133'), (.cal, 'R', '\u211B'),
   (.cal, 'e', '\u212F'), (.cal, 'g', '\u210A'), (.cal, 'o', '\u2134'),
   (.frak, 'C', '\u212D'), (.frak, 'H', '\u210C'), (.frak, 'I', '\u2111'),
   (.frak, 'R', '\u211C'), (.frak, 'Z', '\u2128'),
   (.bb, 'C', '\u2102'), (.bb, 'H', '\u210D'), (.bb, 'N', '\u2115'),
   (.bb, 'P', '\u2119'), (.bb, 'Q', '\u211A'), (.bb, 'R', '\u211D'),
   (.bb, 'Z', '\u2124'),
   (.it, 'h', '\u210E')]

def MathAlphabet.hole (a : MathAlphabet) (c : Char) : Option Char :=
  (alphaHoles.find? fun (b, l, _) => b == a && l == c).map (·.2.2)

/-- Where each alphabet's `A`, `a`, and `0` start in the Mathematical
Alphanumeric block (Unicode ch. 22.2). `none` where the block has no such
run: no script, fraktur, italic, or upright-beyond-ASCII digits — those
digits stay as written, as unicode-math leaves them. `rm` is ASCII itself.
`bfit` (`\symbfit`) carries no digits: unicode-math leaves those digits at
their source scalar rather than taking the bold digit run. -/
def MathAlphabet.bases : MathAlphabet → Nat × Nat × Option Nat
  | .bb => (0x1D538, 0x1D552, some 0x1D7D8)
  | .cal => (0x1D49C, 0x1D4B6, none)
  | .frak => (0x1D504, 0x1D51E, none)
  | .bf => (0x1D400, 0x1D41A, some 0x1D7CE)
  | .bfit => (0x1D468, 0x1D482, none)
  | .bfDefault => (0x1D400, 0x1D41A, some 0x1D7CE)
  | .sf => (0x1D5A0, 0x1D5BA, some 0x1D7E2)
  | .tt => (0x1D670, 0x1D68A, some 0x1D7F6)
  | .rm => ('A'.toNat, 'a'.toNat, some '0'.toNat)
  | .it => (0x1D434, 0x1D44E, none)
  | .bm => (0x1D468, 0x1D482, none)

/-- A separately installed range of a math alphabet. unicode-math tests the
first scalar of each range before installing that range; an isolated glyph
elsewhere in the range therefore does not make the alphabet available. -/
inductive MathAlphabetRange where
  | latinUpper
  | latinLower
  | digits
  | greekUpper
  | greekLower
  | misc
  deriving Repr, BEq, DecidableEq, Inhabited

def allAlphabetRanges : List MathAlphabetRange :=
  [.latinUpper, .latinLower, .digits, .greekUpper, .greekLower, .misc]

def MathAlphabetRange.anchor : MathAlphabetRange → Char
  | .latinUpper => 'A'
  | .latinLower => 'a'
  | .digits => '0'
  | .greekUpper => 'Α'
  | .greekLower => Char.ofNat 0x1D6FC
  | .misc => '\u2207'

/-- The ranges a text family serves for a `text`-sourced alphabet: the
Latin letters and digits unicode-math's text math alphabets cover. Greek
and the miscellaneous `∇` stay math symbols under a text source (LuaLaTeX
does not pull them from the text family), so a text-sourced alphabet does
not style them. -/
def MathAlphabetRange.textServed : MathAlphabetRange → Bool
  | .latinUpper | .latinLower | .digits => true
  | .greekUpper | .greekLower | .misc => false

/-- The 58 Greek slots of Unicode's Mathematical Alphanumeric blocks
(Unicode ch. 22.2), written in their upright forms. Capital theta symbol
occupies the capital-letter hole, nabla follows omega, and ∂ and
the six variant slots follow lowercase omega. One inventory serves both
directions; `greekSlot?` also accepts the parser's italic source scalars. -/
private def uprightGreek : Array Char :=
  "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡϴΣΤΥΦΧΨΩ∇αβγδεζηθικλμνξοπρςστυφχψω∂ϵϑϰϕϱϖ".toList.toArray

private def greekSlot? (c : Char) : Option Nat :=
  if 0x1D6E2 ≤ c.toNat && c.toNat ≤ 0x1D71B then some (c.toNat - 0x1D6E2)
  else uprightGreek.findIdx? (· == c)

/-- unicode-math's default bold TeX style is a selection of two installed
ranges. Scalar mapping and face coverage read this same choice, so a face
carrying only upright bold cannot silently satisfy bold italic Greek. -/
def MathAlphabet.forRange (a : MathAlphabet) (r : MathAlphabetRange) : MathAlphabet :=
  if a == .bfDefault then
    if r == .greekLower then .bfit else .bf
  else a

/-- Selecting a canonical range twice cannot change its alphabet. -/
theorem MathAlphabet.forRange_fixed_point (a : MathAlphabet) (r : MathAlphabetRange) :
    (a.forRange r).forRange r = a.forRange r := by
  cases a <;> cases r <;> rfl

/-- The range an input scalar asks this alphabet to remap, if any. The
input is the parser's ordinary math scalar: Latin variables are already
italic, so `unItalic` recovers their source letter. -/
def MathAlphabet.rangeOf (a : MathAlphabet) (c0 : Char) : Option MathAlphabetRange :=
  if a == .bm then none
  else
  let c := unItalic c0
  let (_, _, digit) := a.bases
  if 'A' ≤ c && c ≤ 'Z' then some .latinUpper
  else if 'a' ≤ c && c ≤ 'z' then some .latinLower
  else if '0' ≤ c && c ≤ '9' && digit.isSome then some .digits
  else if a == .rm || a == .it || a == .bf || a == .bfit || a == .bfDefault then
    (greekSlot? c).map fun i =>
      if i == 25 then .misc else if i < 25 then .greekUpper else .greekLower
  else none

/-- One letter or digit under an alphabet: the Letterlike hole when the
block reserves the slot, else the base-offset scalar. Greek uses the
shared slot inventory, including identity ranges: an explicit upright or
italic selection must override an enclosing alphabet even when its
source scalar already has that shape. `bfDefault` selects its canonical
range through `forRange`, just as coverage does. -/
def MathAlphabet.apply (a : MathAlphabet) (c0 : Char) : Char :=
  let a := a.forRange ((a.rangeOf c0).getD .latinUpper)
  let c := unItalic c0
  match a.hole c with
  | some h => h
  | none =>
    let (upper, lower, digit) := a.bases
    if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (upper + (c.toNat - 'A'.toNat))
    else if 'a' ≤ c && c ≤ 'z' then Char.ofNat (lower + (c.toNat - 'a'.toNat))
    else if '0' ≤ c && c ≤ '9' then
      match digit with
      | some d => Char.ofNat (d + (c.toNat - '0'.toNat))
      | none => c
    else
      match greekSlot? c with
      | some i =>
        match a with
        | .rm => uprightGreek[i]?.getD c0
        | .it => Char.ofNat (0x1D6E2 + i)
        | .bf => Char.ofNat (0x1D6A8 + i)
        | .bfit => Char.ofNat (0x1D71C + i)
        | .bb | .cal | .frak | .bfDefault | .sf | .tt | .bm => c0
      | none => c0

def MathAlphabet.ranges (a : MathAlphabet) : List MathAlphabetRange :=
  allAlphabetRanges.filter fun r => a.rangeOf r.anchor == some r

/-- Range anchors the selected math face covers, derived once after that
face is selected. The remap decision (`remaps`) reads `covered` alone.
`sources` is orthogonal policy retained for phase-3 text-slot projection
(setting a text-sourced alphabet from its declared text family); it does
not gate remap-vs-keep. -/
structure MathAlphabetCoverage where
  sources : MathAlphabetSources := {}
  covered : Array (MathAlphabet × MathAlphabetRange) := #[]
  deriving Repr, BEq, Inhabited

def MathAlphabetCoverage.faceCovers (c : MathAlphabetCoverage)
    (a : MathAlphabet) (r : MathAlphabetRange) : Bool :=
  c.covered.contains (a.forRange r, r)

/-- Coverage is exactly the coverage of the canonical range selected by
the scalar mapper, including the two halves of default bold. -/
theorem MathAlphabetCoverage.faceCovers_forRange_exact (c : MathAlphabetCoverage)
    (a : MathAlphabet) (r : MathAlphabetRange) :
    c.faceCovers (a.forRange r) r = c.faceCovers a r := by
  simp only [faceCovers, MathAlphabet.forRange_fixed_point]

/-- Whether the shared-IR resolver remaps this range: exactly when the
selected math face carries the range anchor. A range the face does not
carry keeps its source scalar in that face — never a Unicode math scalar
per-character fallback would then satisfy from an unrelated host face —
and the whole-alphabet loss is named once (N0018) by the IR census.
`sources` no longer gates the remap: it is retained for phase-3 text-slot
projection (setting a text-sourced alphabet from its declared text family),
which is orthogonal to whether the math face covers the range. -/
def MathAlphabetCoverage.remaps (c : MathAlphabetCoverage)
    (a : MathAlphabet) (r : MathAlphabetRange) : Bool :=
  c.faceCovers a r

/-- The source in force for an alphabet node, given its provenance. A
`\sym…` node forces the symbol source; a legacy node consults the document
policy. `effectiveAlpha` pairs this with the alphabet selected by that
policy before the resolver or missing-range census pushes its stack. -/
def MathAlphabetCoverage.effectiveSource (c : MathAlphabetCoverage)
    (src : AlphaSource) (a : MathAlphabet) : MathAlphabetSource :=
  match src with
  | .sym => .sym
  | .doc => c.sources.get a

/-- Resolve provenance and document policy together. `mathbf=sym` selects
the same default TeX bold as `symbf`, including italic lowercase Greek.
Text-sourced legacy bold retains its body-face style, while explicit
`symbfup` remains upright bold. Both the artifact resolver and its loss
census consume this pair, so their canonical range selection agrees. -/
def MathAlphabetCoverage.effectiveAlpha (c : MathAlphabetCoverage)
    (src : AlphaSource) (a : MathAlphabet) : MathAlphabet × MathAlphabetSource :=
  match src, a with
  | .doc, .bf =>
    match c.sources.bf with
    | .text => (.bf, .text)
    | .sym => (.bfDefault, .sym)
  | _, _ => (a, c.effectiveSource src a)

/-- Explicit symbol alphabets retain their shape under every document
policy; upright bold cannot become default bold through a source option. -/
theorem MathAlphabetCoverage.effectiveAlpha_sym_exact (c : MathAlphabetCoverage)
    (a : MathAlphabet) : c.effectiveAlpha .sym a = (a, .sym) := by
  cases a <;> rfl

/-- Every text-sourced legacy alphabet retains its original alphabet and
source pair, including the existing body-face projection of bold. -/
theorem MathAlphabetCoverage.effectiveAlpha_text_exact (c : MathAlphabetCoverage)
    (a : MathAlphabet) (h : c.sources.get a = .text) :
    c.effectiveAlpha .doc a = (a, .text) := by
  cases a <;> simp_all [effectiveAlpha, effectiveSource, MathAlphabetSources.get]

/-- Symbol-sourced legacy bold and forced default bold select exactly the
same active pair, for all ranges and all enclosing alphabet stacks. -/
theorem MathAlphabetCoverage.effectiveAlpha_bf_sym_exact (c : MathAlphabetCoverage)
    (h : c.sources.bf = .sym) :
    c.effectiveAlpha .doc .bf = c.effectiveAlpha .sym .bfDefault := by
  simp [effectiveAlpha, effectiveSource, h]

/-- The Latin letters every alphabet maps. -/
def latinLetters : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList

/-- The (alphabet, base character) behind a mapped scalar — `apply`'s left
inverse on the letters and digits (`alpha_apply_inj` holds them inverse
over every letter). Also the layout's recovery when the math face lacks
the mapped scalar: the base character is what still renders, the alphabet
names the styling lost. A digit run shared by two alphabets (`bf`/`bfit`
both use the bold digits) answers with the first, which recovery cannot
tell apart anyway. -/
def MathAlphabet.unapply (c : Char) : Option (MathAlphabet × Char) :=
  match alphaHoles.find? fun (_, _, h) => h == c with
  | some (a, l, _) => some (a, l)
  | none =>
    let n := c.toNat
    let run (a : MathAlphabet) (base : Nat) (first : Char) (len : Nat) :
        Option (MathAlphabet × Char) :=
      if base ≤ n && n < base + len then
        some (a, Char.ofNat (first.toNat + (n - base)))
      else none
    allAlphabets.findSome? fun a =>
      let (upper, lower, digit) := a.bases
      run a upper 'A' 26 <|> run a lower 'a' 26 <|>
        (digit.bind fun d => run a d '0' 10)

/-- The alphanumeric map is injective on the letters: within one alphabet
two different letters never collide, and no two alphabets share a scalar —
`\mathcal{R}` (ℛ), `\mathbb{R}` (ℝ), `\mathfrak{R}` (ℜ), and `R` itself
are four scalars. Stated constructively: `unapply` recovers the alphabet
and the letter from every image, holes included — a left inverse, so two
distinct (alphabet, letter) pairs cannot map to one scalar. -/
theorem alpha_apply_inj :
    (allAlphabets.all fun a => latinLetters.all fun c =>
      MathAlphabet.unapply (a.apply c) == some (a, c)) = true := by decide

/-- Stable key for one alphabet in diagnostics and generated reports. -/
def MathAlphabet.name : MathAlphabet → String
  | .bb => "bb"
  | .cal => "cal"
  | .frak => "frak"
  | .bf => "bf"
  | .bfit => "bfit"
  | .bfDefault => "bf-default"
  | .sf => "sf"
  | .tt => "tt"
  | .rm => "rm"
  | .it => "it"
  | .bm => "bm"

/-- The styling an alphabet declares, for the note that names its loss. -/
def MathAlphabet.styleLabel : MathAlphabet → String
  | .bb => "double-struck"
  | .cal => "calligraphic"
  | .frak => "fraktur"
  | .bf => "bold"
  | .bfit => "bold italic"
  | .bfDefault => "bold with italic lowercase Greek"
  | .sf => "sans-serif"
  | .tt => "monospace"
  | .rm => "upright"
  | .it => "italic"
  | .bm => "bold italic"

/-- What a text face can synthesize of an alphabet's styling when the math
face lacks the mapped scalar: `(bold, italic)`. The bold and italic
alphabets keep their essence from the text face's own variants; the shape
alphabets (double-struck, calligraphic, fraktur, sans-serif, monospace)
cannot be synthesized — their base letter stands in plain, the loss
named. -/
def MathAlphabet.synthStyle : MathAlphabet → Bool × Bool
  | .bf | .bfDefault => (true, false)
  | .bfit => (true, true)
  | .it => (false, true)
  | .bm => (true, true)
  | _ => (false, false)

/-- A text family slot a resolved text-sourced math alphabet projects to.
Numbered to match the layout's `FontSet` slots — body/serif is 0, sans 1,
mono 2 (`FontSet.lookup`) — so the PDF projection is a slot lookup, never a
per-scalar host guess. Math-owned so the resolved nucleus can carry it
without `Math` importing `Ir`. -/
inductive MathTextSlot where
  | body
  | sans
  | mono
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The `FontSet` slot number (0 body, 1 sans, 2 mono). -/
def MathTextSlot.toNat : MathTextSlot → Nat
  | .body => 0
  | .sans => 1
  | .mono => 2

/-- The CSS custom property naming this slot's text family — the same
`--font-{body,sans,mono}` the text path sets (`HtmlDoc.fontStyleDecls`,
`:root`). The HTML projection of a math text slot names a family through
this variable rather than the `FontSet` index, so the two encodings of one
slot — the PDF's `toNat`, the browser's `fontVar` — partition the slots
identically (`fontVar_toNat_agree`). -/
def MathTextSlot.fontVar : MathTextSlot → String
  | .body => "--font-body"
  | .sans => "--font-sans"
  | .mono => "--font-mono"

/-- The typed style a text-sourced math alphabet resolves to: which text
family slot, and the weight/shape axes both backends project — the PDF
through `FontSet.lookup (slot, weight, italic)`, MathML through CSS
family, weight and style declarations. This is the resolved surface of `\mathrm`/`\mathit`/
`\mathbf`/`\mathsf`/`\mathtt` under unicode-math's default (text) source:
the glyph is the plain base letter set in a text family, not a Mathematical
Alphanumeric scalar. -/
structure MathTextStyle where
  slot : MathTextSlot
  bold : Bool := false
  italic : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The text-family projection of a legacy math alphabet when its source is
`text` (unicode-math's default for `mathrm`/`mathit`/`mathbf`/`mathsf`/
`mathtt`). `none` for the shape alphabets (`bb`/`cal`/`frak`) and `bfit`,
which are always symbol-sourced and have no text-slot form. `bf` is upright
bold on the body slot, `it` italic on the body slot, matching what
LuaLaTeX paints from the main family's variants. -/
def MathAlphabet.textStyle? : MathAlphabet → Option MathTextStyle
  | .rm => some { slot := .body, bold := false, italic := false }
  | .it => some { slot := .body, bold := false, italic := true }
  | .bf => some { slot := .body, bold := true, italic := false }
  | .sf => some { slot := .sans, bold := false, italic := false }
  | .tt => some { slot := .mono, bold := false, italic := false }
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => none

/-- Text alphabets serve Latin letters and digits independently of the
Unicode symbol ranges: `\mathit{5}` uses the body italic face even though
Unicode has no mathematical italic digits. Other ranges retain their
symbol classification, and a symbol source is unchanged. -/
def MathAlphabet.sourceRangeOf (a : MathAlphabet) (src : MathAlphabetSource)
    (c : Char) : Option MathAlphabetRange :=
  if src == .text && a.textStyle?.isSome then
    (MathAlphabet.rm.rangeOf c).filter (·.textServed) <|> a.rangeOf c
  else a.rangeOf c

/-- Selecting a symbol source preserves the Unicode range classifier for
every alphabet and scalar. Text-family coverage cannot invent a symbol
range, including the absent italic digits. -/
theorem MathAlphabet.sourceRangeOf_sym_exact (a : MathAlphabet) (c : Char) :
    a.sourceRangeOf .sym c = a.rangeOf c := rfl

/-- The semantic MathML `mathvariant` a resolved text style declares: the
attribute a MathML consumer reads to style the plain base letter, since the
scalar is the ASCII letter, not a Mathematical Alphanumeric code point. -/
def MathTextStyle.mathvariant : MathTextStyle → String
  | { slot := .sans, bold := b, italic := i } =>
    if b && i then "sans-serif-bold-italic"
    else if b then "bold-sans-serif"
    else if i then "sans-serif-italic"
    else "sans-serif"
  | { slot := .mono, .. } => "monospace"
  | { slot := .body, bold := b, italic := i } =>
    if b && i then "bold-italic"
    else if b then "bold"
    else if i then "italic"
    else "normal"

/-- The CSS font weight this style selects — the single owner of the
`bold → 700, else 400` mapping both backends read: the PDF passes it to
`FontSet.lookup` (Layout's `.styled` arm), the browser emits it as
`font-weight` (`MathTextStyle.css`). -/
def MathTextStyle.weight (s : MathTextStyle) : Nat :=
  if s.bold then 700 else 400

/-- The CSS declarations a resolved text style projects — the
browser-honoured counterpart of `mathvariant`. Chromium (and every WebKit
build) implements only `mathvariant="normal"` of MathML Core §3.2.2 and
ignores `bold`/`italic`/`sans-serif`/`monospace`, so the family, weight and
shape ride on real CSS instead: `font-family` names the slot's text family
through its `--font-*` variable, `font-weight` is set only when it departs
from the inherited 400, and `font-style: italic` only when italic. These
are exactly the axes `Layout` reads from the same style — `slot` through
`FontSet.lookup`'s index, `weight`, and `italic` — so neither backend owns
a second slot→family or bold→weight mapping (`fontVar_toNat_agree`,
`MathTextStyle.weight`). -/
def MathTextStyle.css (s : MathTextStyle) : String :=
  let fam := s!"font-family: var({s.slot.fontVar})"
  let wt := if s.bold then s!"; font-weight: {s.weight}" else ""
  let it := if s.italic then "; font-style: italic" else ""
  fam ++ wt ++ it

/-- The CSS family partition and the `FontSet` slot partition agree: two
slots share a `--font-*` family exactly when they share a `FontSet` index.
This proves agreement of slot identifiers, not of loaded font files or
browser fallback; those environment-dependent facts need artifact checks. -/
theorem fontVar_toNat_agree (s t : MathTextSlot) :
    s.fontVar = t.fontVar ↔ s.toNat = t.toNat := by
  cases s <;> cases t <;> decide

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
    match pending with
    | none => go acc (some c) rest
    | some p =>
      let p :=
        if p == .bin && (c == .rel || c == .closing || c == .punct) then .ord else p
      go (acc.push p) (some c) rest

/-- A Bin with nothing to bind on its left is an Ord: `$-x$` sets tight. -/
theorem bin_leading_degrades : degrade [.bin, .ord] = [.ord, .ord] := by decide

/-- The pass's size ledger: `go` emits exactly one atom per input atom, plus
the pending one. Induction over the input with the accumulator and pending
slot generalized — the match in `go`'s step maps a `some` pending to `some`
and leaves `none` alone, so each step moves one atom from input to output. -/
theorem degrade_go_length (cs : List MathClass) (acc : Array MathClass)
    (pending : Option MathClass) :
    (degrade.go acc pending cs).size
      = acc.size + (if pending.isSome then 1 else 0) + cs.length := by
  fun_induction degrade.go acc pending cs
  all_goals simp_all
  all_goals omega

/-- Degradation changes classes, never the count or the order — for every
list: the degraded class list is walked positionally beside the atom list,
so a length change would mis-pair every following space. -/
theorem degrade_length (cs : List MathClass) :
    (degrade cs).length = cs.length := by
  simp [degrade, degrade_go_length]

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
`\arraycolsep` to 5pt at the 10pt base — half an em a side), and rows
`\arraystretch` baselines apart, in permille: 1000, LaTeX's default,
unless the definition sets its own (amsmath's `\env@cases`: 1.2). `small`
is amsmath's `smallmatrix`: script-style cells centred in their columns,
`\thickspace` between columns, rows `6\ex@` apart unless their ink would
come within `1.5\ex@` (its `\lineskip` and `\lineskiplimit`), and a thin
space each side (amsmath.sty, `smallmatrix`; `\ex@` is 1 pt at the 10 pt
base, amsgen.sty's `\compute@ex@`). -/
inductive GridKind where
  | align
  | gather
  | array (cols : Array ColAlign) (stretch : Nat)
  | small
  deriving Repr, BEq, Inhabited

/-- The alignment of column `k` under a grid kind. An `array` column past
its spec centres — the spec mismatch was already diagnosed at elaboration. -/
def GridKind.colAlign : GridKind → Nat → ColAlign
  | .align, k => if k % 2 == 0 then .right else .left
  | .gather, _ => .center
  | .array cols _, k => cols.getD k .center
  | .small, _ => .center

/-- The gap after column `k` of `n`, in mu (18ths of an em at the current
size). `align`'s pair halves abut (the alignment point is exactly the
column boundary); between pairs it takes 2 em — amsmath stretches tabskip
glue across the display width there, which a fixed-width box cannot, so
this is a stated stand-in, not a sourced constant. `array` pays
`\arraycolsep` each side of every column boundary: 5pt+5pt at the 10pt
base is 18 mu (article.cls). `small` pays `\thickspace` before every
column but the first, amsmath's `.2777em`: 5 mu. -/
def GridKind.gapAfter : GridKind → Nat → Nat → Nat
  | .align, k, n => if k + 1 == n then 0 else if k % 2 == 0 then 0 else 36
  | .gather, _, _ => 0
  | .array _ _, k, n => if k + 1 == n then 0 else 18
  | .small, k, n => if k + 1 == n then 0 else 5

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

/-- An amsmath sized delimiter's `\vcenter` (amsmath.sty, `\bBigg@`):
`step`⁄2 times `\big@size`, which is 1.2 times `paren`, the height and
depth of the current `(`. -/
def bigVcenter (paren : Int) (step : Nat) : Int :=
  paren * 12 / 10 * (step : Int) / 2

/-- The least size a sized delimiter grows to over its `\vcenter`, by
TeXbook Appendix G rule 19: `\delimiterfactor` 901‰ of it, or all of it but
`\delimitershortfall` (plain TeX's 5 pt, half the 10 pt `size`); `paren`
and `size` in one unit. The PDF picks its variant by this target, and
MathML's stretch clamp is the same target in em, so both artifacts reach
the same variant. -/
def bigTarget (paren size : Int) (step : Nat) : Int :=
  let v := bigVcenter paren step
  max (v * 901 / 1000) (v - size / 2)

/-- The variant a horizontal accent stretches to: the widest in the ladder
not exceeding `target` — an accent may not overhang its base, the reverse
of a delimiter's "at least as tall" — else the first, the narrowest the
font offers. Same increasing-size order as `pickVariant`. -/
def pickWidest (target : Int) : List (Nat × Int) → Option (Nat × Int)
  | [] => none
  | [v] => some v
  | v :: rest@(w :: _) =>
    if w.2 ≤ target then pickWidest target rest else some v

/-- A stretched accent never overhangs: when the ladder's first variant
fits the target at all, the picked one fits too — with the spec's
increasing order it is the widest that does. -/
theorem pickWidest_covers (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
    (hp : pickWidest target vs = some v) (hw : ∀ w ∈ vs.take 1, w.2 ≤ target) :
    v.2 ≤ target := by
  induction vs with
  | nil => simp [pickWidest] at hp
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [pickWidest, Option.some.injEq] at hp
      exact hp ▸ hw x (by simp)
    | cons y t =>
      simp only [pickWidest] at hp
      split at hp
      next hy =>
        exact ih hp fun w hwm => by
          simp only [List.take, List.mem_singleton] at hwm
          exact hwm ▸ hy
      next =>
        cases hp
        exact hw _ (by simp [List.take])

/-- What is stretched to is a variant the font really has. -/
theorem pickWidest_mem (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
    (hp : pickWidest target vs = some v) : v ∈ vs := by
  induction vs with
  | nil => simp [pickWidest] at hp
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [pickWidest, Option.some.injEq] at hp
      subst hp
      exact List.mem_singleton_self ..
    | cons y t =>
      simp only [pickWidest] at hp
      split at hp
      next =>
        exact List.mem_cons_of_mem x (ih hp)
      next =>
        cases hp
        exact List.mem_cons_self ..

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

/-- What `\genfrac` declares beside its two operands (amsmath.sty:
`\genfrac{left}{right}{thickness}{style}{num}{den}`, of which `\frac`,
`\dfrac`, `\tfrac`, `\binom`, `\dbinom` and `\tbinom` are rows): the
delimiters around the fraction, `none` the empty one; the rule, `none` the
face's own and `some t` a thickness in sp, where 0 stacks the operands with
no rule; and the style the construct sets in, `none` the current one. -/
structure FracSpec where
  left : Option Char := none
  right : Option Char := none
  rule : Option Int := none
  style : Option MathStyle := none
  deriving Repr, BEq, Inhabited

/-- cancel.sty's four marks (v2.2): a strike through a measured subformula
— `up` (`\cancel`, the rising diagonal), `down` (`\bcancel`, the falling
one), `cross` (`\xcancel`, both) — or `to` (`\cancelto`), the rising
strike ending in an arrowhead that points at a value. -/
inductive CancelMark where
  | up
  | down
  | cross
  | to
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The style a `\cancelto` value sets in, from the package option in force
(cancel.sty's table): `step` (`smaller`, the default) one style down the
progression, `sup` (`Smaller`) a superscript's style, `same` (`samesize`)
the current one. Always uncramped: the package switches style by name. -/
inductive CancelSize where
  | same
  | step
  | sup
  deriving Repr, BEq, DecidableEq, Inhabited

def CancelSize.style : CancelSize → MathStyle → MathStyle
  | .same, .display _ => .display false
  | .same, .text _ => .text false
  | .same, .script _ => .script false
  | .same, .scriptscript _ => .scriptscript false
  | .step, .display _ => .text false
  | .step, .text _ => .script false
  | .step, _ => .scriptscript false
  | .sup, .display _ | .sup, .text _ => .script false
  | .sup, _ => .scriptscript false

/-- What a cancel mark declares beyond its operands, from the package's
load options and `\CancelColor`: `thick` under `thicklines` (the stroke
doubles, as LaTeX's `\thicklines` doubles `\thinlines`), `room` only under
`makeroom` (cancel.sty's default `\hidewidth` overlaps), the value's
style, and the marks' colour with its palette name (`none`: the colour in
force). -/
structure CancelSpec where
  thick : Bool := false
  room : Bool := false
  size : CancelSize := .step
  color : Option (Ir.Color × Option String) := none
  deriving Repr, BEq, Inhabited

/-- cancel.sty's options, read as its `\ProcessOptions` reads them: in the
order the package declares them, whatever order the document wrote them in
— so `Smaller` beats `samesize` and `overlap` beats `makeroom` — with the
names it does not declare returned for the caller to name. -/
def CancelSpec.ofOptions (opts : List String) : CancelSpec × List String :=
  let declared := ["samesize", "smaller", "Smaller", "makeroom", "overlap", "thicklines"]
  let apply (s : CancelSpec) : String → CancelSpec
    | "samesize" => { s with size := .same }
    | "smaller" => { s with size := .step }
    | "Smaller" => { s with size := .sup }
    | "makeroom" => { s with room := true }
    | "overlap" => { s with room := false }
    | "thicklines" => { s with thick := true }
    | _ => s
  (declared.foldl (fun s o => if opts.contains o then apply s o else s) {},
   opts.filter (!declared.contains ·))

/-- What a cancel mark's geometry reads, in sp at the size its struck
subformula sets at: `rule` the stroke (the math font's
`OverbarRuleThickness`, doubled under `thicklines`) and `gap` the
clearance (`OverbarVerticalGap`) — the two quantities TeX's rule 9 lays
`\overline` with, a mark drawn over a subformula — then the struck box (`w`
its advance, `top`/`bot` its ink from the baseline) and, for `\cancelto`,
the value's advance and measured ink bounds (not its baseline-inclusive
line box). `SpaceAfterScript` supplies the trailing space when room is
requested. The target's size still follows the package's style table;
its position is an attachment to the arrow tip, not a superscript. -/
structure CancelIn where
  rule : Int
  gap : Int
  w : Int
  top : Int
  bot : Int
  vw : Int := 0
  vleft : Int := 0
  vright : Int := 0
  vtop : Int := 0
  vbot : Int := 0
  space : Int := 0
  deriving Repr, BEq, Inhabited

/-- The mark box, as `(x0, y0, x1, y1)` from the construct's origin:
horizontal advance and vertical ink grown by the clearance. With room
the operand starts at `gap`; overlapping, it starts at 0. Negative kerns
can reverse the nominal horizontal endpoints, so both axes are ordered
before marks are drawn or clamped. This bounds the signed endpoints, not
the operand's horizontal glyph ink. -/
def CancelIn.box (i : CancelIn) (room : Bool) : Int × Int × Int × Int :=
  let x0 := if room then 0 else -i.gap
  let x1 := x0 + i.w + 2 * i.gap
  let y0 := i.bot - i.gap
  let y1 := i.top + i.gap
  (min x0 x1, min y0 y1, max x0 x1, max y0 y1)

/-- Every cancellation input supplies ordered bounds, including signed
advances and clearances. -/
theorem CancelIn.box_bounds_contract (i : CancelIn) (room : Bool) :
    (i.box room).1 ≤ (i.box room).2.2.1 ∧
    (i.box room).2.1 ≤ (i.box room).2.2.2 := by
  simp only [box]
  omega

/-- Ordering changes neither endpoint when the original bounds already
stand in order, including a zero width or height. -/
theorem CancelIn.box_of_ordered_exact (i : CancelIn) (room : Bool)
    (hw : 0 ≤ i.w + 2 * i.gap) (hh : i.bot - i.gap ≤ i.top + i.gap) :
    i.box room =
      (let x0 := if room then 0 else -i.gap
       (x0, i.bot - i.gap, x0 + i.w + 2 * i.gap, i.top + i.gap)) := by
  dsimp [box]
  apply Prod.ext
  · dsimp; omega
  apply Prod.ext
  · dsimp; omega
  apply Prod.ext <;> dsimp <;> omega

/-- A diagonal's length, to the sp below. -/
def cancelDiag (w h : Int) : Int :=
  Int.ofNat (Nat.sqrt (w.toNat * w.toNat + h.toNat * h.toNat))

/-- A strike: the band `rule` wide on a diagonal of the box `(x0, y0, x1,
y1)` — rising from the bottom-left corner to the top-right one, or falling
from the top-left to the bottom-right — cut by the box's own edges. So it
ends exactly in the corners and none of it leaves the box: `dx` and `dy`
are where the band's edges cross the box's, half the rule divided by the
diagonal's sine and cosine. -/
def cancelBand (rising : Bool) (x0 y0 x1 y1 rule : Int) : Array (Int × Int) :=
  let w := x1 - x0
  let h := y1 - y0
  let l := cancelDiag w h
  let dx := min w (rule * l / (2 * h))
  let dy := min h (rule * l / (2 * w))
  if rising then
    #[(x0, y0), (x0 + dx, y0), (x1, y1 - dy), (x1, y1), (x1 - dx, y1), (x0, y0 + dy)]
  else
    #[(x0, y1), (x0, y1 - dy), (x1 - dx, y0), (x1, y0), (x1, y0 + dy), (x0 + dx, y1)]

/-- A strike runs corner to corner: its first and fourth points are the two
corners of the box's diagonal, exactly — never a slope rounded to one the
drawing vocabulary happens to have. -/
theorem cancelBand_corners_exact (rising : Bool) (x0 y0 x1 y1 rule : Int) :
    (cancelBand rising x0 y0 x1 y1 rule)[0]? = some (x0, if rising then y0 else y1) ∧
    (cancelBand rising x0 y0 x1 y1 rule)[3]? = some (x1, if rising then y1 else y0) := by
  cases rising <;> exact ⟨rfl, rfl⟩

/-- A strike never leaves its box: every point of the band lies inside it,
whatever the slope, including a zero width or height. With room reserved
the box is the construct's own width. -/
theorem cancelBand_between (rising : Bool) (x0 y0 x1 y1 rule : Int)
    (hr : 0 ≤ rule) (hw : x0 ≤ x1) (hh : y0 ≤ y1) :
    ∀ p ∈ cancelBand rising x0 y0 x1 y1 rule,
      x0 ≤ p.1 ∧ p.1 ≤ x1 ∧ y0 ≤ p.2 ∧ p.2 ≤ y1 := by
  intro p hp
  simp only [cancelBand] at hp
  have hl : 0 ≤ cancelDiag (x1 - x0) (y1 - y0) := Int.natCast_nonneg _
  generalize cancelDiag (x1 - x0) (y1 - y0) = l at hl hp
  have hq1 : 0 ≤ rule * l / (2 * (y1 - y0)) :=
    Int.ediv_nonneg (Int.mul_nonneg hr hl) (by omega)
  have hq2 : 0 ≤ rule * l / (2 * (x1 - x0)) :=
    Int.ediv_nonneg (Int.mul_nonneg hr hl) (by omega)
  generalize rule * l / (2 * (y1 - y0)) = q1 at hq1 hp
  generalize rule * l / (2 * (x1 - x0)) = q2 at hq2 hp
  cases rising <;> simp only [Bool.false_eq_true, ite_false, ite_true, List.mem_toArray,
    List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with h | h | h | h | h | h <;> subst h <;> simp only <;> omega

/-- Where a cancel mark's parts stand, from the construct's origin on the
baseline: the struck subformula's start, the filled polygons the marks ink
(each strike, or the arrow's shaft then its head), the value's baseline
origin, and the construct's advance. -/
structure CancelGeom where
  shift : Int
  polys : Array (Array (Int × Int))
  valueX : Int := 0
  valueY : Int := 0
  advance : Int
  deriving Repr, BEq, Inhabited

/-- Bring a vertex inside a non-inverted box on both axes. An arrow's
perpendicular wings can otherwise cross the sides of a wide or tall box:
`cancelHead 0 0 1000 100 20` reached `(919, 122)` above a 100sp-tall box.
Vertices that already fit are unchanged (`clampBox_id`). -/
def clampBox (x0 y0 x1 y1 : Int) (p : Int × Int) : Int × Int :=
  (max x0 (min x1 p.1), max y0 (min y1 p.2))

/-- A clamped point lies in the box, on each axis, whenever the box is not
inverted. -/
theorem clampBox_between (x0 y0 x1 y1 : Int) (hw : x0 ≤ x1) (hh : y0 ≤ y1)
    (p : Int × Int) :
    x0 ≤ (clampBox x0 y0 x1 y1 p).1 ∧ (clampBox x0 y0 x1 y1 p).1 ≤ x1 ∧
    y0 ≤ (clampBox x0 y0 x1 y1 p).2 ∧ (clampBox x0 y0 x1 y1 p).2 ≤ y1 := by
  simp only [clampBox]; omega

/-- Clamping preserves every vertex already inside the box. -/
theorem clampBox_id (x0 y0 x1 y1 : Int) (p : Int × Int)
    (hx0 : x0 ≤ p.1) (hx1 : p.1 ≤ x1) (hy0 : y0 ≤ p.2) (hy1 : p.2 ≤ y1) :
    clampBox x0 y0 x1 y1 p = p := by
  apply Prod.ext <;> simp only [clampBox] <;> omega

/-- Every point of an array mapped through `clampBox` lies in the box. -/
theorem mem_map_clampBox_between (x0 y0 x1 y1 : Int) (hw : x0 ≤ x1) (hh : y0 ≤ y1)
    (arr : Array (Int × Int)) :
    ∀ p ∈ arr.map (clampBox x0 y0 x1 y1),
      x0 ≤ p.1 ∧ p.1 ≤ x1 ∧ y0 ≤ p.2 ∧ p.2 ≤ y1 := by
  intro p hp
  rw [Array.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  exact clampBox_between x0 y0 x1 y1 hw hh q

/-- The arrowhead of `\cancelto`: four strokes long and three wide (the
rule is the one length every mark counts in), its tip in the mark box's
top-right corner and its axis on the diagonal; `(tip, one wing, the
other)`, each vertex clamped into the box so a wing never overprints a
neighbour. -/
def cancelHead (x0 y0 x1 y1 rule : Int) : Array (Int × Int) :=
  let w := x1 - x0
  let h := y1 - y0
  let l := max 1 (cancelDiag w h)
  let bx := x1 - 4 * rule * w / l
  let by_ := y1 - 4 * rule * h / l
  (#[(x1, y1), (bx - 3 * rule * h / (2 * l), by_ + 3 * rule * w / (2 * l)),
    (bx + 3 * rule * h / (2 * l), by_ - 3 * rule * w / (2 * l))]).map (clampBox x0 y0 x1 y1)

/-- The arrow's shaft: the rising band from the mark box's bottom-left
corner to the head's base, cut square there — or nothing, when the box is
too small for a shaft to stand before the head. Each vertex is clamped into
the box, as the head's is. -/
def cancelShaft (x0 y0 x1 y1 rule : Int) : Array (Int × Int) :=
  let w := x1 - x0
  let h := y1 - y0
  let l := max 1 (cancelDiag w h)
  let dx := min w (rule * l / (2 * h))
  let dy := min h (rule * l / (2 * w))
  let bx := x1 - 4 * rule * w / l
  let by_ := y1 - 4 * rule * h / l
  let sx := rule * h / (2 * l)
  let sy := rule * w / (2 * l)
  if (l - 4 * rule) * l ≥ dx * w && (l - 4 * rule) * l ≥ dy * h then
    (#[(x0, y0), (x0 + dx, y0), (bx + sx, by_ - sy), (bx - sx, by_ + sy),
      (x0, y0 + dy)]).map (clampBox x0 y0 x1 y1)
  else #[]

/-- The arrowhead never leaves its box: every vertex lies inside `(x0, y0,
x1, y1)`, including a zero width or height, whatever the rule's sign. -/
theorem cancelHead_between (x0 y0 x1 y1 rule : Int) (hw : x0 ≤ x1) (hh : y0 ≤ y1) :
    ∀ p ∈ cancelHead x0 y0 x1 y1 rule,
      x0 ≤ p.1 ∧ p.1 ≤ x1 ∧ y0 ≤ p.2 ∧ p.2 ≤ y1 :=
  mem_map_clampBox_between x0 y0 x1 y1 hw hh _

/-- A drawn shaft never leaves its box: when the shaft is nonempty every
vertex lies inside a non-inverted box, including a zero width or height.
The empty shaft has no vertices to place. -/
theorem cancelShaft_between (x0 y0 x1 y1 rule : Int) (hw : x0 ≤ x1) (hh : y0 ≤ y1) :
    ∀ p ∈ cancelShaft x0 y0 x1 y1 rule,
      x0 ≤ p.1 ∧ p.1 ≤ x1 ∧ y0 ≤ p.2 ∧ p.2 ≤ y1 := by
  intro p hp
  simp only [cancelShaft] at hp
  split at hp
  · exact mem_map_clampBox_between x0 y0 x1 y1 hw hh _ p hp
  · simp only [Array.not_mem_empty] at hp

/-- Nearest integer to `n / (2 * step)`. The factor two keeps measured
ink centres exact until the final integer-coordinate rounding. -/
private def roundRay (n step : Int) : Int := (n + step) / (2 * step)

/-- Nearest-coordinate rounding leaves at most half a coordinate unit
of perpendicular error, expressed without division. -/
private theorem roundRay_between (n step : Int) (h : 0 < step) :
    -step ≤ 2 * step * roundRay n step - n ∧
    2 * step * roundRay n step - n ≤ step := by
  have hmod := Int.emod_nonneg (n + step) (show 2 * step ≠ 0 by omega)
  have hlt := Int.emod_lt_of_pos (n + step) (show 0 < 2 * step by omega)
  have he := Int.emod_add_mul_ediv (n + step) (2 * step)
  unfold roundRay
  omega

/-- The origin of a measured ink rectangle beyond a ray's tip (the local
origin), with its centre on the forward ray. Intersect that ray with the
rectangle expanded by the font's clearance: the near x edge fixes shallow
rays, the near y edge steep ones. The remaining coordinate is derived,
rounded once. A zero direction uses horizontal attachment. No slope or
glyph-specific offset is chosen. Bounds are outline hulls, not raster
centres of mass. -/
def inkRayOrigin (dx dy gap left bottom right top : Int) : Int × Int :=
  let g := max 0 gap
  if dy ≤ 0 ∨ (0 < dx ∧ (right - left + 2 * g) * dy ≤ (top - bottom + 2 * g) * dx) then
    let step := max 1 dx
    (g - left, roundRay ((right - left + 2 * g) * dy - step * (top + bottom)) step)
  else
    let step := max 1 dy
    (roundRay ((top - bottom + 2 * g) * dx - step * (right + left)) step, g - bottom)

/-- One near ink edge is exactly a nonnegative clearance beyond the tip.
This separates the target from every mark point behind the tip on that axis. -/
theorem inkRayOrigin_axis_exact (dx dy gap left bottom right top : Int) :
    let o := inkRayOrigin dx dy gap left bottom right top;
    o.1 + left = max 0 gap ∨ o.2 + bottom = max 0 gap := by
  dsimp [inkRayOrigin]
  split <;> simp

/-- The doubled ink centre is on the ray up to integer rounding: its
cross product with the direction is bounded by the larger direction
component. Thus perpendicular distance is at most half a coordinate unit.
This is geometric attachment, not a claim about perceived beauty. -/
theorem inkRayOrigin_between (dx dy gap left bottom right top : Int)
    (hx : 0 ≤ dx) (hy : 0 ≤ dy) :
    let o := inkRayOrigin dx dy gap left bottom right top;
    -(max dx dy) ≤ dx * (2 * o.2 + top + bottom) - dy * (2 * o.1 + right + left) ∧
    dx * (2 * o.2 + top + bottom) - dy * (2 * o.1 + right + left) ≤ max dx dy := by
  dsimp [inkRayOrigin]
  split
  next h =>
    by_cases hz : dx = 0
    · have hyz : dy = 0 := by omega
      simp [hz, hyz]
    · have hpos : 0 < dx := by omega
      have hm : max 1 dx = dx := by omega
      rw [hm]
      have key := roundRay_between
        ((right - left + 2 * max 0 gap) * dy - dx * (top + bottom)) dx hpos
      simp only [Int.mul_add, Int.mul_sub, Int.add_mul, Int.sub_mul,
        Int.mul_comm right dy, Int.mul_comm left dy, Int.mul_comm (max 0 gap) dy,
        Int.mul_assoc, Int.mul_left_comm dy 2, Int.mul_left_comm dx 2] at *
      omega
  next h =>
    have hpos : 0 < dy := by omega
    have hm : max 1 dy = dy := by omega
    rw [hm]
    have key := roundRay_between
      ((top - bottom + 2 * max 0 gap) * dx - dy * (right + left)) dy hpos
    simp only [Int.mul_add, Int.mul_sub, Int.add_mul, Int.sub_mul,
      Int.mul_comm top dx, Int.mul_comm bottom dx, Int.mul_comm (max 0 gap) dx,
      Int.mul_assoc, Int.mul_left_comm dy 2, Int.mul_left_comm dx 2] at *
    omega

/-- A rounded projection does not cross an integer upper bound. -/
private theorem roundRay_le (n step k : Int) (hs : 0 < step) (hn : n ≤ 2 * step * k) :
    roundRay n step ≤ k := by
  rw [roundRay, Int.ediv_le_iff_le_mul (by omega)]
  simp only [Int.mul_comm k (2 * step), Int.mul_assoc] at *
  omega

/-- Rounding a nonnegative centre cannot move it behind the origin,
including a half-coordinate tie. -/
private theorem roundRay_center_nonneg (n d s : Int) (hd : 0 < d)
    (hn : 0 ≤ n + d * s) : 0 ≤ 2 * roundRay n d + s := by
  have hm := Int.emod_nonneg (n + d) (by omega : 2 * d ≠ 0)
  have hl := Int.emod_lt_of_pos (n + d) (by omega : 0 < 2 * d)
  have he := Int.emod_add_mul_ediv (n + d) (2 * d)
  have hr : -d < 2 * d * roundRay n d - n := by
    unfold roundRay
    omega
  by_cases hc : 0 ≤ 2 * roundRay n d + s
  · exact hc
  have hc' : 2 * roundRay n d + s ≤ -1 := by omega
  have ht := Int.mul_le_mul_of_nonneg_left hc' (show 0 ≤ d by omega)
  simp only [Int.mul_add, Int.mul_neg, Int.mul_one, ← Int.mul_assoc, Int.mul_comm d 2] at ht
  omega

/-- Translating by an integer commutes with nearest-coordinate rounding. -/
private theorem roundRay_translation_exact (n step k : Int) (hs : 0 < step) :
    roundRay (n - 2 * step * k) step = roundRay n step - k := by
  unfold roundRay
  have he : n - 2 * step * k + step = n + step - (2 * step) * k := by omega
  rw [he, Int.sub_mul_ediv_left _ _ (by omega)]

/-- Re-expressing the target in another local coordinate system changes
only its origin. Invisible prefixes and raised baselines cannot change
where the measured ink attaches. -/
theorem inkRayOrigin_translation_exact (dx dy gap left bottom right top sx sy : Int) :
    inkRayOrigin dx dy gap (left + sx) (bottom + sy) (right + sx) (top + sy) =
      let o := inkRayOrigin dx dy gap left bottom right top;
      (o.1 - sx, o.2 - sy) := by
  have hw : right + sx - (left + sx) = right - left := by omega
  have hh : top + sy - (bottom + sy) = top - bottom := by omega
  dsimp [inkRayOrigin]
  rw [hw, hh]
  split
  · have he : (right - left + 2 * max 0 gap) * dy - max 1 dx * (top + sy + (bottom + sy)) =
        (right - left + 2 * max 0 gap) * dy - max 1 dx * (top + bottom) - 2 * max 1 dx * sy := by
      simp only [Int.mul_add, Int.mul_assoc]
      omega
    rw [he, roundRay_translation_exact _ _ _ (by omega)]
    apply Prod.ext <;> dsimp <;> omega
  · have he : (top - bottom + 2 * max 0 gap) * dx - max 1 dy * (right + sx + (left + sx)) =
        (top - bottom + 2 * max 0 gap) * dx - max 1 dy * (right + left) - 2 * max 1 dy * sx := by
      simp only [Int.mul_add, Int.mul_assoc]
      omega
    rw [he, roundRay_translation_exact _ _ _ (by omega)]
    apply Prod.ext <;> dsimp <;> omega

/-- For an ordered ink rectangle and a nonnegative direction, one near
edge clears the tip by exactly the font gap, while the other clears by no
more than that gap. This bounds both separation and excess distance: the
tip-to-hull distance lies between the gap and its diagonal. -/
theorem inkRayOrigin_clears_between (dx dy gap left bottom right top : Int)
    (hx : 0 ≤ dx) (hy : 0 ≤ dy) (hw : left ≤ right) (hh : bottom ≤ top) :
    let o := inkRayOrigin dx dy gap left bottom right top;
    (o.1 + left = max 0 gap ∧ o.2 + bottom ≤ max 0 gap) ∨
    (o.2 + bottom = max 0 gap ∧ o.1 + left ≤ max 0 gap) := by
  dsimp [inkRayOrigin]
  split
  next h =>
    apply Or.inl
    refine ⟨by omega, ?_⟩
    have hs : 0 < max 1 dx := by omega
    have hi : (right - left + 2 * max 0 gap) * dy ≤ (top - bottom + 2 * max 0 gap) * max 1 dx := by
      rcases h with hz | ⟨hp, hc⟩
      · have hd : dy = 0 := by omega
        rw [hd, Int.mul_zero]
        exact Int.mul_nonneg (by omega) (by omega)
      · have hm : max 1 dx = dx := by omega
        rwa [hm]
    have hn : (right - left + 2 * max 0 gap) * dy - max 1 dx * (top + bottom) ≤
        2 * max 1 dx * (max 0 gap - bottom) := by
      simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub,
        Int.mul_comm top (max 1 dx), Int.mul_comm bottom (max 1 dx),
        Int.mul_comm (max 0 gap) (max 1 dx), Int.mul_assoc] at *
      omega
    have := roundRay_le _ _ _ hs hn
    omega
  next h =>
    apply Or.inr
    refine ⟨by omega, ?_⟩
    have hp : 0 < dy := by omega
    have hm : max 1 dy = dy := by omega
    rw [hm]
    have hi : (top - bottom + 2 * max 0 gap) * dx ≤ (right - left + 2 * max 0 gap) * dy := by
      by_cases hx0 : dx = 0
      · rw [hx0, Int.mul_zero]
        exact Int.mul_nonneg (by omega) hy
      · omega
    have hn : (top - bottom + 2 * max 0 gap) * dx - dy * (right + left) ≤
        2 * dy * (max 0 gap - left) := by
      simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub,
        Int.mul_comm right dy, Int.mul_comm left dy, Int.mul_comm (max 0 gap) dy,
        Int.mul_assoc] at *
      omega
    have := roundRay_le _ _ _ hp hn
    omega

/-- The measured centre is on the forward half of the ray, bounded by the
expanded target dimensions on both axes. This also keeps the far ink edges
beyond the tip, completing the tip-to-hull clearance bound. These are
bounds on quantized outline hulls, not raster centres or contour distances. -/
theorem inkRayOrigin_forward_between (dx dy gap left bottom right top : Int)
    (hx : 0 ≤ dx) (hy : 0 ≤ dy) (hw : left ≤ right) (hh : bottom ≤ top) :
    let o := inkRayOrigin dx dy gap left bottom right top;
    0 ≤ 2 * o.1 + left + right ∧
    2 * o.1 + left + right ≤ right - left + 2 * max 0 gap ∧
    0 ≤ 2 * o.2 + bottom + top ∧
    2 * o.2 + bottom + top ≤ top - bottom + 2 * max 0 gap := by
  have hc := inkRayOrigin_clears_between dx dy gap left bottom right top hx hy hw hh
  have hnonneg :
      0 ≤ 2 * (inkRayOrigin dx dy gap left bottom right top).1 + left + right ∧
      0 ≤ 2 * (inkRayOrigin dx dy gap left bottom right top).2 + bottom + top := by
    dsimp [inkRayOrigin]
    split
    · have hp : 0 ≤ (right - left + 2 * max 0 gap) * dy :=
        Int.mul_nonneg (by omega) hy
      have key := roundRay_center_nonneg
        ((right - left + 2 * max 0 gap) * dy - max 1 dx * (top + bottom))
        (max 1 dx) (top + bottom) (by omega) (by omega)
      constructor <;> omega
    · have hp : 0 ≤ (top - bottom + 2 * max 0 gap) * dx :=
        Int.mul_nonneg (by omega) hx
      have key := roundRay_center_nonneg
        ((top - bottom + 2 * max 0 gap) * dx - max 1 dy * (right + left))
        (max 1 dy) (right + left) (by omega) (by omega)
      constructor <;> omega
  dsimp only at hc ⊢
  rcases hc with h | h <;> omega

/-- Reserve a measured horizontal interval and both logical endpoints.
The first result is a common translation; the second is the total width.
It adds only missing room, without changing any relative attachment. -/
def inkRoom (left right advance : Int) : Int × Int :=
  let pad := max 0 (-min left advance)
  (pad, pad + max 0 (max right advance))

/-- Both ink edges and the logical endpoints fit in their reservation,
including a negative advance. This is interval containment, not a spacing
preference; callers supply the measured ink and any declared clearance. -/
theorem inkRoom_covers (left right advance : Int) :
    let r := inkRoom left right advance;
    0 ≤ r.1 ∧ 0 ≤ r.1 + left ∧ r.1 + right ≤ r.2 ∧
    0 ≤ r.1 + advance ∧ r.1 + advance ≤ r.2 ∧ 0 ≤ r.2 := by
  dsimp [inkRoom]
  omega

/-- Project the ray-relative attachment into the mark's coordinate system.
Only measured target ink anchors the target; its advance is reserved later. -/
def CancelIn.valueOrigin (i : CancelIn) (room : Bool) : Int × Int :=
  let b := i.box room
  let o := inkRayOrigin (b.2.2.1 - b.1) (b.2.2.2 - b.2.1) i.gap
    i.vleft i.vbot i.vright i.vtop
  (b.2.2.1 + o.1, b.2.2.2 + o.2)

/-- A cancel mark laid out by the conventions (PLAN, 2026-09-29 cancellation
entry): the strikes corner to corner of the mark box; the arrow's head in
its top-right corner; the value's ink centre along the forward diagonal,
with font-derived clearance from the tip; and, with room, an advance that
includes both the mark box and the target's ink and logical advance before
ordinary inter-atom spacing. Overlapping, the construct
advances as its subformula does and the marks overprint as cancel.sty's. -/
def cancelGeom (mark : CancelMark) (room : Bool) (i : CancelIn) : CancelGeom :=
  let b := i.box room
  let shift := if room then i.gap else 0
  let band (rising : Bool) := cancelBand rising b.1 b.2.1 b.2.2.1 b.2.2.2 i.rule
  match mark with
  | .up => { shift, polys := #[band true], advance := if room then b.2.2.1 else i.w }
  | .down => { shift, polys := #[band false], advance := if room then b.2.2.1 else i.w }
  | .cross =>
    { shift, polys := #[band true, band false], advance := if room then b.2.2.1 else i.w }
  | .to =>
    let head := cancelHead b.1 b.2.1 b.2.2.1 b.2.2.2 i.rule
    let shaft := cancelShaft b.1 b.2.1 b.2.2.1 b.2.2.2 i.rule
    let o := i.valueOrigin room
    { shift, polys := if shaft.isEmpty then #[head] else #[shaft, head]
      valueX := o.1, valueY := o.2
      advance := if room then max b.2.2.1 (o.1 + max i.vw i.vright) + max 0 i.space else i.w }

/-- The target's measured ink centre follows the arrow's forward diagonal
to within half an sp of perpendicular rounding, independent of aspect
ratio, target depth or local baseline. The error is a cross product of
doubled coordinates, avoiding a lossy square root in the contract. -/
theorem cancelto_value_between (room : Bool) (i : CancelIn) :
    let b := i.box room
    let dx := b.2.2.1 - b.1
    let dy := b.2.2.2 - b.2.1
    let g := cancelGeom .to room i
  let error := dx * (2 * g.valueY + i.vtop + i.vbot - 2 * b.2.2.2) -
      dy * (2 * g.valueX + i.vright + i.vleft - 2 * b.2.2.1);
    -(max dx dy) ≤ error ∧ error ≤ max dx dy := by
  dsimp only
  let b := i.box room
  let o := inkRayOrigin (b.2.2.1 - b.1) (b.2.2.2 - b.2.1) i.gap
    i.vleft i.vbot i.vright i.vtop
  have hx := (i.box_bounds_contract room).1
  have hy := (i.box_bounds_contract room).2
  have ex : 2 * (cancelGeom .to room i).valueX + i.vright + i.vleft - 2 * b.2.2.1 =
      2 * o.1 + i.vright + i.vleft := by
    dsimp [cancelGeom, CancelIn.valueOrigin, o, b]; omega
  have ey : 2 * (cancelGeom .to room i).valueY + i.vtop + i.vbot - 2 * b.2.2.2 =
      2 * o.2 + i.vtop + i.vbot := by
    dsimp [cancelGeom, CancelIn.valueOrigin, o, b]; omega
  rw [ex, ey]
  exact inkRayOrigin_between _ _ _ _ _ _ _ (by omega) (by omega)

/-- The target's ink clears the entire arrow on at least one axis: its
left edge is a font gap right of every arrow point, or its bottom edge is
a font gap above every point. Positive gaps imply no ink collision. -/
theorem cancelto_value_clears_between (room : Bool) (i : CancelIn) :
    let b := i.box room
    let g := cancelGeom .to room i
    g.valueX + i.vleft = b.2.2.1 + max 0 i.gap ∨
    g.valueY + i.vbot = b.2.2.2 + max 0 i.gap := by
  have key := inkRayOrigin_axis_exact
    ((i.box room).2.2.1 - (i.box room).1) ((i.box room).2.2.2 - (i.box room).2.1)
    i.gap i.vleft i.vbot i.vright i.vtop
  dsimp only [cancelGeom, CancelIn.valueOrigin] at *
  omega

/-- The local right end reserves the mark box, placed target ink and logical
advance, followed by nonnegative script spacing. The completed assembly
also passes through `inkRoom`: an above-tip target may extend left of its
origin, requiring a common translation to reserve that side. -/
theorem cancelto_room_covers (i : CancelIn) :
    (i.box true).2.2.1 ≤ (cancelGeom .to true i).advance ∧
    (cancelGeom .to true i).valueX + i.vright ≤ (cancelGeom .to true i).advance ∧
    (cancelGeom .to true i).valueX + i.vw ≤ (cancelGeom .to true i).advance := by
  dsimp [cancelGeom]; omega

/-- `\cancelto` inks exactly its arrow: shaft then head when the box holds
a shaft, the head alone when it does not. Target placement adds no mark. -/
theorem cancelGeom_to_polys_exact (room : Bool) (i : CancelIn) :
    let b := i.box room
    (cancelGeom .to room i).polys =
      (if (cancelShaft b.1 b.2.1 b.2.2.1 b.2.2.2 i.rule).isEmpty then
          #[cancelHead b.1 b.2.1 b.2.2.1 b.2.2.2 i.rule]
        else
          #[cancelShaft b.1 b.2.1 b.2.2.1 b.2.2.2 i.rule,
            cancelHead b.1 b.2.1 b.2.2.1 b.2.2.2 i.rule]) := rfl

/-- No cancel mark paints outside its box: every vertex of every polygon
`cancelGeom` lays — each strike, or the arrow's shaft and head — lies inside
the non-inverted mark box, including a zero width or height. All four
flavors and both room settings share this bound; no sampling is involved. -/
theorem cancelGeom_polys_between (mark : CancelMark) (room : Bool) (i : CancelIn)
    (hr : 0 ≤ i.rule)
    (hw : (i.box room).1 ≤ (i.box room).2.2.1)
    (hh : (i.box room).2.1 ≤ (i.box room).2.2.2) :
    ∀ poly ∈ (cancelGeom mark room i).polys, ∀ p ∈ poly,
      (i.box room).1 ≤ p.1 ∧ p.1 ≤ (i.box room).2.2.1 ∧
      (i.box room).2.1 ≤ p.2 ∧ p.2 ≤ (i.box room).2.2.2 := by
  have band := fun rising =>
    cancelBand_between rising (i.box room).1 (i.box room).2.1 (i.box room).2.2.1
      (i.box room).2.2.2 i.rule hr hw hh
  have head :=
    cancelHead_between (i.box room).1 (i.box room).2.1 (i.box room).2.2.1
      (i.box room).2.2.2 i.rule hw hh
  have shaft :=
    cancelShaft_between (i.box room).1 (i.box room).2.1 (i.box room).2.2.1
      (i.box room).2.2.2 i.rule hw hh
  intro poly hpoly p hp
  cases mark
  case up =>
    simp only [cancelGeom, Array.mem_singleton] at hpoly
    subst hpoly; exact band true p hp
  case down =>
    simp only [cancelGeom, Array.mem_singleton] at hpoly
    subst hpoly; exact band false p hp
  case cross =>
    simp only [cancelGeom, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hpoly
    rcases hpoly with rfl | rfl
    · exact band true p hp
    · exact band false p hp
  case to =>
    simp only [cancelGeom] at hpoly
    split at hpoly
    · simp only [Array.mem_singleton] at hpoly
      subst hpoly; exact head p hp
    · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hpoly
      rcases hpoly with rfl | rfl
      · exact shaft p hp
      · exact head p hp

/-- Every mark stays in its ordered envelope even when signed input
endpoints were reversed. This is containment only: a zero-area envelope
need not yield visible ink. -/
theorem cancelGeom_envelope_between (mark : CancelMark) (room : Bool) (i : CancelIn)
    (hr : 0 ≤ i.rule) :
    ∀ poly ∈ (cancelGeom mark room i).polys, ∀ p ∈ poly,
      (i.box room).1 ≤ p.1 ∧ p.1 ≤ (i.box room).2.2.1 ∧
      (i.box room).2.1 ≤ p.2 ∧ p.2 ≤ (i.box room).2.2.2 :=
  cancelGeom_polys_between mark room i hr
    (i.box_bounds_contract room).1 (i.box_bounds_contract room).2

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
  /-- A math alphabet before the selected face has answered which ranges it
  carries. `source` records provenance: `.sym` (from `\sym…`) forces the
  symbol source, `.doc` (a legacy command) consults the document policy.
  The driver eliminates every such node with `resolveMathAlphas`
  before scalar fallback, layout, or either backend. -/
  | alpha (alphabet : MathAlphabet) (source : AlphaSource) (body : MList)
  /-- A resolved text-sourced alphabet scalar: the plain base letter `c`
  set under the typed text `style`, the only outcome `resolveMathAlphas`
  produces for a `text`-sourced alphabet (`\mathrm`, `\mathit`, `\mathbf`,
  `\mathsf`, `\mathtt` under unicode-math's default). The backends project
  `style` — the PDF to the body/sans/mono family slot with the weight and
  italic axes through `FontSet`, MathML to a `mathvariant` — so no host
  per-scalar fallback stands in for a text family. Constructed only by the
  resolver door; a `.styled` in a math tree means the tree is resolved. -/
  | styled (style : MathTextStyle) (c : Char)
  /-- A generalized fraction: numerator over denominator, positioned from
  the MATH constants — the fraction constants under a rule, the stack
  constants under none — between the delimiters and in the style its spec
  declares (TeXbook Appendix G rule 15; `\genfrac`). -/
  | frac (spec : FracSpec) (num den : MList)
  /-- `\sqrt[deg]{body}`: `deg` is `.nil` for the plain square root. -/
  | rad (deg : MList) (body : MList)
  /-- `\left l body \right r`: `none` is the empty `.` delimiter. -/
  | delim (l : Option Char) (r : Option Char) (body : MList)
  /-- A delimiter at one of amsmath's fixed sizes (`\bigl(`, `\Bigm|`):
  `\left d \vcenter to s\big@size{} \right.` with `s` = `step`⁄2, and
  `\big@size` 1.2 times the height and depth of the current `(`
  (amsmath.sty, `\bBigg@`); `none` is the empty `.`, which sets nothing. -/
  | big (d : Option Char) (step : Nat)
  /-- An alignment: `align`/`gather`/`array` rows, rectangular by the time
  layout sees them (`MRows.pad`; a ragged source row was diagnosed). -/
  | grid (kind : GridKind) (rows : MRows)
  /-- A math accent over its base: `mark` is the combining scalar
  (unicode-math's table — `\hat` is U+0302), `stretch` whether it grows
  through the face's horizontal variants to the base's width (`\widehat`).
  The U+0305 combining overline is the one mark layout draws as a rule
  from the overbar constants instead of a glyph (TeXbook Appendix G rule
  9): `\overline`'s stretch is then exact at any width. -/
  | accent (mark : Char) (stretch : Bool) (body : MList)
  /-- A cancel.sty mark over `body`: the strike (or the arrow, for `to`)
  spans the body's ink grown by the font's overbar clearance, and `value`
  (`.nil` unless `to`) sets as the struck box's superscript. Laid out by
  `Math.cancelGeom`, whose conventions are the ones stated for the user
  (PLAN, 2026-09-29 cancellation entry). -/
  | cancel (mark : CancelMark) (spec : CancelSpec) (value : MList) (body : MList)
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
  /-- A colour switch (`\color{c}`; `\textcolor{c}{x}` is `{\color{c} x}`):
  the rest of this list inks in `color`, resolved through the palette the
  text path reads, `name` its palette entry when it was one. It is TeX's
  colour whatsit — no atom, no class — so it never changes the space the
  table puts between its neighbours. -/
  | ink (color : Ir.Color) (name : Option String)
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
is inserted only between directly adjacent atoms — and neither does a
colour switch, which the spacing walk steps over. -/
def MItem.classOf : MItem → Option MathClass
  | .atom cls _ _ _ _ => some cls
  | .space _ => none
  | .ink _ _ => none

/-- The classes of a list's atoms in order, spaces and colour switches
skipped: what `degrade` normalizes and the spacing walk consumes. Shallow —
each sub-list is normalized independently, as TeX processes each mlist. -/
def MList.classes : MList → List MathClass
  | .nil => []
  | .cons (.atom cls _ _ _ _) rest => cls :: classes rest
  | .cons (.space _) rest => classes rest
  | .cons (.ink _ _) rest => classes rest

mutual

/-- Every scalar a math list can ask the math face for, `docScalars`-style:
the driver checks coverage before layout, keeping layout pure. -/
def MItem.scalars (acc : Array Char) : MItem → Array Char
  | .atom _ nuc sup sub _ =>
    MList.scalarsList (MList.scalarsList (nuc.scalars acc) sup) sub
  | .space _ => acc
  | .ink _ _ => acc

def MNucleus.scalars (acc : Array Char) : MNucleus → Array Char
  | .sym c => acc.push c
  | .styled _ c => acc.push c
  | .word s => s.foldl (·.push ·) acc
  | .list body => MList.scalarsList acc body
  | .alpha _ _ body => MList.scalarsList acc body
  | .frac spec num den =>
    -- In reading order, delimiters around the parts: the formula floor reads
    -- this walk (`Ir.formulaFloor`), so `\binom{n}{k}` reads `(nk)`.
    let acc := match spec.left with
      | some c => acc.push c
      | none => acc
    let acc := MList.scalarsList (MList.scalarsList acc num) den
    match spec.right with
    | some c => acc.push c
    | none => acc
  | .rad deg body => MList.scalarsList (MList.scalarsList acc deg) body
  | .delim l r body =>
    let acc := match l with
      | some c => acc.push c
      | none => acc
    let acc := match r with
      | some c => acc.push c
      | none => acc
    MList.scalarsList acc body
  | .big d _ =>
    match d with
    | some c => acc.push c
    | none => acc
  | .accent mark _ body =>
    -- U+0305 draws as a rule, never asked of the face; every other mark is
    -- a glyph the coverage check must see.
    let acc := if mark == '\u0305' then acc else acc.push mark
    MList.scalarsList acc body
  | .grid _ rows => MRows.scalarsRows acc rows
  -- The struck subformula, then the value it cancels to: a superscript's
  -- order, so the reading is the one `x^0` gets.
  | .cancel _ _ value body => MList.scalarsList (MList.scalarsList acc body) value

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

mutual

/-- Every scalar a math list asks the *selected math face* for. Identical to
`scalars` but a text-projected `.styled` nucleus contributes nothing: it is
set in its text family by the `.styled` layout arm (`FontSet.lookup slot`)
and its coverage is judged there — against the text face, as an E0405 when
that face lacks it — never against the math face. The math-face substitution
scan (W0009) reads this, so a scalar the sans/mono/body slot set cleanly is
never blamed on the math face and never doubled with the styled arm's own
E0405. -/
def MItem.mathScalars (acc : Array Char) : MItem → Array Char
  | .atom _ nuc sup sub _ =>
    MList.mathScalarsList (MList.mathScalarsList (nuc.mathScalars acc) sup) sub
  | .space _ => acc
  | .ink _ _ => acc

def MNucleus.mathScalars (acc : Array Char) : MNucleus → Array Char
  | .sym c => acc.push c
  | .styled _ _ => acc
  | .word s => s.foldl (·.push ·) acc
  | .list body => MList.mathScalarsList acc body
  | .alpha _ _ body => MList.mathScalarsList acc body
  | .frac spec num den =>
    let acc := match spec.left with
      | some c => acc.push c
      | none => acc
    let acc := MList.mathScalarsList (MList.mathScalarsList acc num) den
    match spec.right with
    | some c => acc.push c
    | none => acc
  | .rad deg body => MList.mathScalarsList (MList.mathScalarsList acc deg) body
  | .delim l r body =>
    let acc := match l with
      | some c => acc.push c
      | none => acc
    let acc := match r with
      | some c => acc.push c
      | none => acc
    MList.mathScalarsList acc body
  | .big d _ =>
    match d with
    | some c => acc.push c
    | none => acc
  | .accent mark _ body =>
    let acc := if mark == '\u0305' then acc else acc.push mark
    MList.mathScalarsList acc body
  | .grid _ rows => MRows.mathScalarsRows acc rows
  | .cancel _ _ value body =>
    MList.mathScalarsList (MList.mathScalarsList acc body) value

def MList.mathScalarsList (acc : Array Char) : MList → Array Char
  | .nil => acc
  | .cons x rest => MList.mathScalarsList (x.mathScalars acc) rest

def MRow.mathScalarsRow (acc : Array Char) : MRow → Array Char
  | .nil => acc
  | .cons c rest => MRow.mathScalarsRow (MList.mathScalarsList acc c) rest

def MRows.mathScalarsRows (acc : Array Char) : MRows → Array Char
  | .nil => acc
  | .cons r rest => MRows.mathScalarsRows (MRow.mathScalarsRow acc r) rest

end

mutual

/-- An alphabet applied through a parsed math list: every `sym` scalar
remaps (`MathAlphabet.apply`), a construction passes through with its
contents remapped — `\mathbf{x^2}` bolds the script too, TeX's alphabet
scope — and upright words (`\text`, function names) stay as written.
Structure, classes, and count are untouched (`remapList_classes_id`), so
remapping never moves a space the table would insert. -/
def MathAlphabet.remapList (a : MathAlphabet) : MList → MList
  | .nil => .nil
  | .cons x rest => .cons (a.remapItem x) (a.remapList rest)

def MathAlphabet.remapItem (a : MathAlphabet) : MItem → MItem
  | .atom cls nuc sup sub lim =>
    .atom cls (a.remapNucleus nuc) (a.remapList sup) (a.remapList sub) lim
  | .space mu => .space mu
  | .ink c n => .ink c n

def MathAlphabet.remapNucleus (a : MathAlphabet) : MNucleus → MNucleus
  | .sym c => .sym (a.apply c)
  | .styled sty c => .styled sty c
  | .word s => .word s
  | .list body => .list (a.remapList body)
  | .alpha b src body => .alpha b src body
  | .frac spec num den => .frac spec (a.remapList num) (a.remapList den)
  | .rad deg body => .rad (a.remapList deg) (a.remapList body)
  | .delim l r body => .delim l r (a.remapList body)
  | .big d step => .big d step
  | .accent mark stretch body => .accent mark stretch (a.remapList body)
  | .grid kind rows => .grid kind (a.remapRows rows)
  | .cancel mark spec value body =>
    .cancel mark spec (a.remapList value) (a.remapList body)

def MathAlphabet.remapRow (a : MathAlphabet) : MRow → MRow
  | .nil => .nil
  | .cons cell rest => .cons (a.remapList cell) (a.remapRow rest)

def MathAlphabet.remapRows (a : MathAlphabet) : MRows → MRows
  | .nil => .nil
  | .cons row rest => .cons (a.remapRow row) (a.remapRows rest)

end

/-- Remapping is the identity on the classes projection: the spacing walk
sees the same list before and after, so an alphabet changes glyphs, never
the space between them. -/
theorem MathAlphabet.remapList_classes_id (a : MathAlphabet) :
    ∀ l : MList, (a.remapList l).classes = l.classes
  | .nil => rfl
  | .cons (.atom _ _ _ _ _) rest => by
    simp only [remapList, remapItem, MList.classes, remapList_classes_id a rest]
  | .cons (.space _) rest => by
    simp only [remapList, remapItem, MList.classes, remapList_classes_id a rest]
  | .cons (.ink _ _) rest => by
    simp only [remapList, remapItem, MList.classes, remapList_classes_id a rest]

private def usedInk (ink : Option (Ir.Color × Option String))
    (acc : Array (Ir.Color × Option String)) : Array (Ir.Color × Option String) :=
  match ink with
  | some p => acc.push p
  | none => acc

mutual

/-- Colours used by math atoms and generated marks, with their palette
names. A switch changes the inherited ink but is not itself a use.
Sublists, scripts and grid cells keep their enclosing ink on return. -/
def MList.inks (ink : Option (Ir.Color × Option String))
    (acc : Array (Ir.Color × Option String)) :
    MList → Array (Ir.Color × Option String)
  | .nil => acc
  | .cons (.ink c n) rest => MList.inks (some (c, n)) acc rest
  | .cons x rest => MList.inks ink (MItem.inks ink acc x) rest

def MItem.inks (ink : Option (Ir.Color × Option String))
    (acc : Array (Ir.Color × Option String)) :
    MItem → Array (Ir.Color × Option String)
  | .atom _ nuc sup sub _ =>
    MList.inks ink (MList.inks ink (MNucleus.inks ink acc nuc) sup) sub
  | .space _ | .ink _ _ => acc

def MNucleus.inks (ink : Option (Ir.Color × Option String))
    (acc : Array (Ir.Color × Option String)) :
    MNucleus → Array (Ir.Color × Option String)
  | .sym c => if c.isWhitespace then acc else usedInk ink acc
  | .styled _ c => if c.isWhitespace then acc else usedInk ink acc
  | .word s => if s.toList.any (!·.isWhitespace) then usedInk ink acc else acc
  | .list body => MList.inks ink acc body
  | .alpha _ _ body => MList.inks ink acc body
  | .frac spec num den =>
    let acc := if spec.rule.all (· > 0) || spec.left.isSome || spec.right.isSome
      then usedInk ink acc else acc
    MList.inks ink (MList.inks ink acc num) den
  | .rad deg body => MList.inks ink (MList.inks ink (usedInk ink acc) deg) body
  | .delim l r body =>
    MList.inks ink (if l.isSome || r.isSome then usedInk ink acc else acc) body
  | .big d _ => if d.isSome then usedInk ink acc else acc
  | .accent _ _ body => MList.inks ink (usedInk ink acc) body
  | .grid _ rows => MRows.inks ink acc rows
  | .cancel _ spec value body =>
    let markInk := spec.color <|> ink
    MList.inks markInk (MList.inks ink (usedInk markInk acc) body) value

def MRow.inks (ink : Option (Ir.Color × Option String))
    (acc : Array (Ir.Color × Option String)) :
    MRow → Array (Ir.Color × Option String)
  | .nil => acc
  | .cons c rest => MRow.inks ink (MList.inks ink acc c) rest

def MRows.inks (ink : Option (Ir.Color × Option String))
    (acc : Array (Ir.Color × Option String)) :
    MRows → Array (Ir.Color × Option String)
  | .nil => acc
  | .cons r rest => MRows.inks ink (MRow.inks ink acc r) rest

end

mutual

/-- Every colour of a math list replaced through `f`, with its palette
name — the formula's share of contrast realization, the map
`Ir.recolorRoles` applies to a text run's colour. Nothing else moves
(`mapInk_scalars`). -/
def MList.mapInk (f : Ir.Color → Option String → Ir.Color) : MList → MList
  | .nil => .nil
  | .cons x rest => .cons (MItem.mapInk f x) (MList.mapInk f rest)

def MItem.mapInk (f : Ir.Color → Option String → Ir.Color) : MItem → MItem
  | .atom cls nuc sup sub lim =>
    .atom cls (MNucleus.mapInk f nuc) (MList.mapInk f sup) (MList.mapInk f sub) lim
  | .space mu => .space mu
  | .ink c n => .ink (f c n) n

def MNucleus.mapInk (f : Ir.Color → Option String → Ir.Color) : MNucleus → MNucleus
  | .sym c => .sym c
  | .styled sty c => .styled sty c
  | .word s => .word s
  | .list body => .list (MList.mapInk f body)
  | .alpha a src body => .alpha a src (MList.mapInk f body)
  | .frac spec num den => .frac spec (MList.mapInk f num) (MList.mapInk f den)
  | .rad deg body => .rad (MList.mapInk f deg) (MList.mapInk f body)
  | .delim l r body => .delim l r (MList.mapInk f body)
  | .big d step => .big d step
  | .accent mark stretch body => .accent mark stretch (MList.mapInk f body)
  | .grid kind rows => .grid kind (MRows.mapInk f rows)
  | .cancel mark spec value body =>
    .cancel mark { spec with color := spec.color.map fun (c, n) => (f c n, n) }
      (MList.mapInk f value) (MList.mapInk f body)

def MRow.mapInk (f : Ir.Color → Option String → Ir.Color) : MRow → MRow
  | .nil => .nil
  | .cons c rest => .cons (MList.mapInk f c) (MRow.mapInk f rest)

def MRows.mapInk (f : Ir.Color → Option String → Ir.Color) : MRows → MRows
  | .nil => .nil
  | .cons r rest => .cons (MRow.mapInk f r) (MRows.mapInk f rest)

end

mutual

/-- Recolouring a formula keeps every scalar in place, so its text census
and every plain-text reading of it (`Ir.formulaFloor`) are the ones the
page had before contrast realization. -/
theorem MList.mapInk_scalars (f : Ir.Color → Option String → Ir.Color) :
    ∀ (l : MList) (acc : Array Char), (MList.mapInk f l).scalarsList acc = l.scalarsList acc
  | .nil, _ => rfl
  | .cons x rest, acc => by
    simp only [MList.mapInk, MList.scalarsList, MItem.mapInk_scalars f x,
      MList.mapInk_scalars f rest]

theorem MItem.mapInk_scalars (f : Ir.Color → Option String → Ir.Color) :
    ∀ (x : MItem) (acc : Array Char), (MItem.mapInk f x).scalars acc = x.scalars acc
  | .atom _ nuc sup sub _, acc => by
    simp only [MItem.mapInk, MItem.scalars, MNucleus.mapInk_scalars f nuc,
      MList.mapInk_scalars f sup, MList.mapInk_scalars f sub]
  | .space _, _ => rfl
  | .ink _ _, _ => rfl

theorem MNucleus.mapInk_scalars (f : Ir.Color → Option String → Ir.Color) :
    ∀ (n : MNucleus) (acc : Array Char), (MNucleus.mapInk f n).scalars acc = n.scalars acc
  | .sym _, _ => rfl
  | .styled _ _, _ => rfl
  | .word _, _ => rfl
  | .list body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f body]
  | .alpha _ _ body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f body]
  | .frac _ num den, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f num,
      MList.mapInk_scalars f den]
  | .rad deg body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f deg,
      MList.mapInk_scalars f body]
  | .delim _ _ body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f body]
  | .big _ _, _ => rfl
  | .accent _ _ body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f body]
  | .grid _ rows, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MRows.mapInk_scalars f rows]
  | .cancel _ _ value body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f body,
      MList.mapInk_scalars f value]

theorem MRow.mapInk_scalars (f : Ir.Color → Option String → Ir.Color) :
    ∀ (r : MRow) (acc : Array Char), (MRow.mapInk f r).scalarsRow acc = r.scalarsRow acc
  | .nil, _ => rfl
  | .cons c rest, acc => by
    simp only [MRow.mapInk, MRow.scalarsRow, MList.mapInk_scalars f c,
      MRow.mapInk_scalars f rest]

theorem MRows.mapInk_scalars (f : Ir.Color → Option String → Ir.Color) :
    ∀ (rs : MRows) (acc : Array Char), (MRows.mapInk f rs).scalarsRows acc = rs.scalarsRows acc
  | .nil, _ => rfl
  | .cons r rest, acc => by
    simp only [MRows.mapInk, MRows.scalarsRows, MRow.mapInk_scalars f r,
      MRows.mapInk_scalars f rest]

end

/-- What resolving one scalar under a stack produces: a plain math scalar
(`sym`), or the plain base letter carried under a resolved text style
(`styled`) when a `text`-sourced alphabet took it. The two outcomes a
resolved `.sym` nucleus becomes. -/
inductive Resolved where
  | sym (c : Char)
  | styled (style : MathTextStyle) (c : Char)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- unicode-math-luatex.sty's `\__um_prepare_mathstyle:n` sets `\fam=-1`
on every symbol-alphabet entry, even if `\__um_switch_to:n` installs no
range. Clear an inherited text family, but keep its scalar: an enclosing
text command's `\use@mathgroup` already switched Latin to literal mathcodes.
The near-identity `.bm` wrapper is not such an alphabet: bm.sty retains
the enclosing family for a digit (`\mathit{\bm{5}}`). It currently also
represents `\boldsymbol`, whose distinct family semantics need a separate
parser constructor; preserve that wrapper's existing behavior here. -/
def Resolved.inAlphabet (a : MathAlphabet) (src : MathAlphabetSource) : Resolved → Resolved
  | .sym c => .sym c
  | .styled sty c =>
    if src = .sym ∧ a ≠ .bm then .sym c else .styled sty c

private theorem Resolved.inAlphabet_sym_covers (r : Resolved) (a : MathAlphabet)
    (ha : a ≠ .bm) : ∃ c, r.inAlphabet a .sym = .sym c := by
  cases r with
  | sym c => exact ⟨c, rfl⟩
  | styled sty c => exact ⟨c, by simp [Resolved.inAlphabet, ha]⟩

/-- Resolve one scalar under a stack of active alphabets, innermost first.
The first alphabet that classifies `c` into one of its ranges decides:

* a `text`-sourced legacy alphabet (`\mathrm`/`\mathit`/`\mathbf`/`\mathsf`/
  `\mathtt` under unicode-math's default) wins on the Latin/digit ranges a
  text family serves — the plain base letter (`unItalic c`) under that
  alphabet's typed style, projected to a text family by the backends;
* a `sym`-sourced range the selected face carries remaps
  (`MathAlphabet.apply`);
* a `sym`-sourced range the face does not carry retains the enclosing
  scalar mapping, but clears its text-family selection. The same reset
  applies when the alphabet has no range for `c`, such as italic digits;
* the near-identity `.bm` wrapper retains its enclosing resolution.

With the stack exhausted the source scalar stands (`.sym c`). Structural
recursion on the list, so total by construction. -/
def resolveCharStack (coverage : MathAlphabetCoverage) :
    List (MathAlphabet × MathAlphabetSource) → Char → Resolved
  | [], c => .sym c
  | (a, src) :: rest, c =>
    Resolved.inAlphabet a src <| match a.sourceRangeOf src c with
    | some r =>
      match a.textStyle? with
      | some sty =>
        if src == .text && r.textServed then .styled sty (unItalic c)
        else if coverage.remaps a r then .sym (a.apply c)
        else resolveCharStack coverage rest c
      | none =>
        if coverage.remaps a r then .sym (a.apply c)
        else resolveCharStack coverage rest c
    | none => resolveCharStack coverage rest c

/-- A `text`-sourced alphabet wins the Latin/digit ranges it serves: the
resolved scalar is the plain base letter under its typed style, ahead of any
outer alphabet — the innermost-first order the resolver rests on. -/
theorem resolveCharStack_text (coverage : MathAlphabetCoverage)
    (a : MathAlphabet) (src : MathAlphabetSource)
    (rest : List (MathAlphabet × MathAlphabetSource)) (c : Char) (r : MathAlphabetRange)
    (sty : MathTextStyle) (hr : a.sourceRangeOf src c = some r) (hst : a.textStyle? = some sty)
    (hsrc : src = .text) (hserved : r.textServed = true) :
    resolveCharStack coverage ((a, src) :: rest) c = .styled sty (unItalic c) := by
  have hcond : (src == .text && r.textServed) = true := by
    rw [hsrc, hserved]; rfl
  simp only [resolveCharStack, hr, hst, hcond, ite_true]
  subst src
  rfl

/-- A `sym`-sourced range the selected face carries remaps to the alphabet's
mathematical-alphanumeric scalar. -/
theorem resolveCharStack_sym_cover (coverage : MathAlphabetCoverage)
    (a : MathAlphabet) (src : MathAlphabetSource)
    (rest : List (MathAlphabet × MathAlphabetSource)) (c : Char) (r : MathAlphabetRange)
    (hr : a.rangeOf c = some r) (hst : a.textStyle? = none)
    (hcov : coverage.remaps a r = true) :
    resolveCharStack coverage ((a, src) :: rest) c = .sym (a.apply c) := by
  simp [resolveCharStack, MathAlphabet.sourceRangeOf, hr, hst, hcov,
    Resolved.inAlphabet]

/-- Every symbol alphabet selects the math family, for every scalar,
coverage table and enclosing stack. Absent ranges and absent coverage
cannot retain an outer text style. The near-identity `.bm` wrapper is not
a symbol alphabet. -/
theorem resolveCharStack_sym_covers (coverage : MathAlphabetCoverage)
    (a : MathAlphabet) (rest : List (MathAlphabet × MathAlphabetSource)) (c : Char)
    (ha : a ≠ .bm) :
    ∃ d, resolveCharStack coverage ((a, .sym) :: rest) c = .sym d := by
  rw [resolveCharStack]
  exact Resolved.inAlphabet_sym_covers _ a ha

/-- A boundary with no covered remap keeps the enclosing scalar mapping
and applies only its family rule: symbol alphabets reset it, the `.bm`
wrapper preserves it. The premise also includes scalars outside all of the
alphabet's ranges; it is independent of a font name. -/
theorem resolveCharStack_sym_fallback_exact (coverage : MathAlphabetCoverage)
    (a : MathAlphabet) (rest : List (MathAlphabet × MathAlphabetSource))
    (c : Char) (hcov : ∀ r, a.rangeOf c = some r → coverage.remaps a r = false) :
    resolveCharStack coverage ((a, .sym) :: rest) c =
      (resolveCharStack coverage rest c).inAlphabet a .sym := by
  simp only [resolveCharStack, MathAlphabet.sourceRangeOf_sym_exact]
  cases hr : a.rangeOf c with
  | none => rfl
  | some r =>
    have hne : (MathAlphabetSource.sym == MathAlphabetSource.text) = false := rfl
    cases a.textStyle? <;> simp [hcov r hr, hne]

/-- The empty stack leaves the source scalar untouched: only an active
alphabet can change a glyph. The base fact the resolver rests on. -/
theorem resolveCharStack_nil (coverage : MathAlphabetCoverage) (c : Char) :
    resolveCharStack coverage [] c = .sym c := rfl

mutual

/-- Resolve alphabet boundaries in one structural walk. `active` is the
stack of alphabets in force, innermost first; a nested command pushes onto
it, as a nested TeX group nests scopes. Each scalar takes the innermost
active alphabet whose range the face covers; a symbol alphabet resets the
text family even when its scalar mapping falls through. The near-identity
`.bm` wrapper preserves its enclosing resolution. The public entry starts
with an empty stack. -/
def resolveAlphaList (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) : MList → MList
  | .nil => .nil
  | .cons x rest =>
    .cons (resolveAlphaItem coverage active x)
      (resolveAlphaList coverage active rest)

def resolveAlphaItem (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) : MItem → MItem
  | .atom cls nuc sup sub lim =>
    .atom cls (resolveAlphaNucleus coverage active nuc)
      (resolveAlphaList coverage active sup)
      (resolveAlphaList coverage active sub) lim
  | .space mu => .space mu
  | .ink c n => .ink c n

def resolveAlphaNucleus (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) : MNucleus → MNucleus
  | .sym c =>
    match resolveCharStack coverage active c with
    | .sym c' => .sym c'
    | .styled sty c' => .styled sty c'
  | .styled sty c => .styled sty c
  | .word s => .word s
  | .list body => .list (resolveAlphaList coverage active body)
  | .alpha a src body => .list (resolveAlphaList coverage (coverage.effectiveAlpha src a :: active) body)
  | .frac spec num den => .frac spec
      (resolveAlphaList coverage active num)
      (resolveAlphaList coverage active den)
  | .rad deg body => .rad (resolveAlphaList coverage active deg)
      (resolveAlphaList coverage active body)
  | .delim l r body => .delim l r (resolveAlphaList coverage active body)
  | .big d step => .big d step
  | .accent mark stretch body =>
      .accent mark stretch (resolveAlphaList coverage active body)
  | .grid kind rows => .grid kind (resolveAlphaRows coverage active rows)
  | .cancel mark spec value body => .cancel mark spec
      (resolveAlphaList coverage active value)
      (resolveAlphaList coverage active body)

def resolveAlphaRow (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) : MRow → MRow
  | .nil => .nil
  | .cons cell rest => .cons (resolveAlphaList coverage active cell)
      (resolveAlphaRow coverage active rest)

def resolveAlphaRows (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) : MRows → MRows
  | .nil => .nil
  | .cons row rest => .cons (resolveAlphaRow coverage active row)
      (resolveAlphaRows coverage active rest)

end

/-- Resolve every typed alphabet boundary against one selected face's
coverage. This runs before the document scalar census and both backends. -/
def resolveMathAlphas (coverage : MathAlphabetCoverage) (body : MList) : MList :=
  resolveAlphaList coverage [] body

/-- The alphabet a stack blames for a scalar left at its source glyph, if
any: walking innermost-first, the first alphabet that classifies `c` into a
range decides. A `text`-sourced alphabet on a range it serves is never a
loss — it projects to a text family (`.styled`). A range the face covers
remaps — no loss. For an unavailable range, inspect the enclosing answer
after this boundary's `inAlphabet` reset: a discarded text family cannot
account for the request. Name the loss only when that answer keeps `c`
and the alphabet would have changed it (`apply c ≠ c`), so an identity
remap is not named. Mirrors
`resolveCharStack` exactly, so the N0018 census reports the alphabet the
reader asked for and could not get. -/
def missingCharAlpha (coverage : MathAlphabetCoverage) :
    List (MathAlphabet × MathAlphabetSource) → Char → Option MathAlphabet
  | [], _ => none
  | (a, src) :: rest, c =>
    match a.sourceRangeOf src c with
    | some r =>
      match a.textStyle? with
      | some _ =>
        if src == .text && r.textServed then none
        else if coverage.remaps a r then none
        else
          match (resolveCharStack coverage rest c).inAlphabet a src with
          | .sym c' => if c' == c && a.apply c != c then some a else none
          | .styled _ _ => none
      | none =>
        if coverage.remaps a r then none
        else
          match (resolveCharStack coverage rest c).inAlphabet a src with
          | .sym c' => if c' == c && a.apply c != c then some a else none
          | .styled _ _ => none
    | none => missingCharAlpha coverage rest c

/-- The census names only scalars the resolver left at their source: if
`missingCharAlpha` blames an alphabet for `c`, the stack kept `c` as a plain
math scalar rather than remapping or text-styling it. This is a resolver
fact; it does not establish that the retained scalar exists in a font, or
that a later fallback diagnostic cannot also name it. -/
theorem missingCharAlpha_kept (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (c : Char),
      (missingCharAlpha coverage active c).isSome →
        resolveCharStack coverage active c = .sym c
  | [], c => by simp [missingCharAlpha]
  | (a, src) :: rest, c => by
    intro h
    rw [missingCharAlpha] at h
    rw [resolveCharStack]
    cases hr : a.sourceRangeOf src c with
    | none =>
      simp only [hr] at h ⊢
      rw [missingCharAlpha_kept coverage rest c h]
      rfl
    | some r =>
      simp only [hr] at h ⊢
      cases hst : a.textStyle? with
      | none =>
        simp only [hst] at h ⊢
        cases hcov : coverage.remaps a r with
        | true => exact absurd h (by simp [hcov])
        | false =>
          simp only [hcov, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hrc : (resolveCharStack coverage rest c).inAlphabet a src with
          | styled s d => exact absurd h (by simp [hrc])
          | sym c' =>
            by_cases hcc : (c' == c && (a.apply c != c)) = true
            · have hcceq : c' = c := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hcc; exact hcc.1
              simp [hcceq]
            · exact absurd h (by simp [hrc, hcc])
      | some sty =>
        simp only [hst] at h ⊢
        cases htext : (src == .text && r.textServed) with
        | true => exact absurd h (by simp [htext])
        | false =>
          cases hcov : coverage.remaps a r with
          | true => exact absurd h (by simp [htext, hcov])
          | false =>
            simp only [htext, hcov, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases hrc : (resolveCharStack coverage rest c).inAlphabet a src with
            | styled s d => exact absurd h (by simp [hrc])
            | sym c' =>
              by_cases hcc : (c' == c && (a.apply c != c)) = true
              · have hcceq : c' = c := by
                  simp only [Bool.and_eq_true, beq_iff_eq] at hcc; exact hcc.1
                simp [hcceq]
              · exact absurd h (by simp [hrc, hcc])

/-- An unavailable, nonidentity symbol request whose resolver keeps the
source scalar is named, including when its boundary discards an enclosing
text family. This is the converse accounting fact for a classified range. -/
theorem missingCharAlpha_sym_named (coverage : MathAlphabetCoverage)
    (a : MathAlphabet) (rest : List (MathAlphabet × MathAlphabetSource))
    (c : Char) (r : MathAlphabetRange)
    (hr : a.rangeOf c = some r) (hcov : coverage.remaps a r = false)
    (happly : a.apply c ≠ c)
    (hkeep : resolveCharStack coverage ((a, .sym) :: rest) c = .sym c) :
    missingCharAlpha coverage ((a, .sym) :: rest) c = some a := by
  have hsrc : (MathAlphabetSource.sym == MathAlphabetSource.text) = false := rfl
  cases hsty : a.textStyle? <;>
    simp [resolveCharStack, MathAlphabet.sourceRangeOf_sym_exact, hr, hsty, hcov, hsrc] at hkeep <;>
    simp [missingCharAlpha, MathAlphabet.sourceRangeOf_sym_exact, hr, hsty, hcov, hsrc,
      hkeep, happly]

private def noteMissingAlpha (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) (out : Array MathAlphabet) (c : Char) :
    Array MathAlphabet :=
  match missingCharAlpha coverage active c with
  | some a => if out.contains a then out else out.push a
  | none => out

mutual

/-- The diagnostic census accompanying `resolveAlphaList`: one entry per
alphabet whose active range stayed at its source scalar. The accumulator
makes repetition idempotent and keeps first-use order. -/
private def missingAlphaList (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) (out : Array MathAlphabet) :
    MList → Array MathAlphabet
  | .nil => out
  | .cons x rest => missingAlphaList coverage active
      (missingAlphaItem coverage active out x) rest

private def missingAlphaItem (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) (out : Array MathAlphabet) :
    MItem → Array MathAlphabet
  | .atom _ nuc sup sub _ =>
    let out := missingAlphaNucleus coverage active out nuc
    let out := missingAlphaList coverage active out sup
    missingAlphaList coverage active out sub
  | .space _ => out
  | .ink _ _ => out

private def missingAlphaNucleus (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) (out : Array MathAlphabet) :
    MNucleus → Array MathAlphabet
  | .sym c => noteMissingAlpha coverage active out c
  | .styled _ _ => out
  | .word _ => out
  | .list body => missingAlphaList coverage active out body
  | .alpha a src body => missingAlphaList coverage (coverage.effectiveAlpha src a :: active) out body
  | .frac _ num den => missingAlphaList coverage active
      (missingAlphaList coverage active out num) den
  | .rad deg body => missingAlphaList coverage active
      (missingAlphaList coverage active out deg) body
  | .delim _ _ body => missingAlphaList coverage active out body
  | .big _ _ => out
  | .accent _ _ body => missingAlphaList coverage active out body
  | .grid _ rows => missingAlphaRows coverage active out rows
  | .cancel _ _ value body => missingAlphaList coverage active
      (missingAlphaList coverage active out body) value

private def missingAlphaRow (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) (out : Array MathAlphabet) :
    MRow → Array MathAlphabet
  | .nil => out
  | .cons cell rest => missingAlphaRow coverage active
      (missingAlphaList coverage active out cell) rest

private def missingAlphaRows (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) (out : Array MathAlphabet) :
    MRows → Array MathAlphabet
  | .nil => out
  | .cons row rest => missingAlphaRows coverage active
      (missingAlphaRow coverage active out row) rest

end

def missingMathAlphas (coverage : MathAlphabetCoverage)
    (body : MList) : Array MathAlphabet :=
  missingAlphaList coverage [] #[] body

mutual

/-- No unresolved alphabet boundary remains in this math tree. -/
def MList.alphaFree : MList → Bool
  | .nil => true
  | .cons x rest => x.alphaFree && rest.alphaFree

def MItem.alphaFree : MItem → Bool
  | .atom _ nuc sup sub _ => nuc.alphaFree && (sup.alphaFree && sub.alphaFree)
  | .space _ | .ink _ _ => true

def MNucleus.alphaFree : MNucleus → Bool
  | .sym _ | .word _ => true
  | .styled _ _ => true
  | .list body => body.alphaFree
  | .alpha _ _ _ => false
  | .frac _ num den => num.alphaFree && den.alphaFree
  | .rad deg body => deg.alphaFree && body.alphaFree
  | .delim _ _ body => body.alphaFree
  | .big _ _ => true
  | .accent _ _ body => body.alphaFree
  | .grid _ rows => rows.alphaFree
  | .cancel _ _ value body => value.alphaFree && body.alphaFree

def MRow.alphaFree : MRow → Bool
  | .nil => true
  | .cons cell rest => cell.alphaFree && rest.alphaFree

def MRows.alphaFree : MRows → Bool
  | .nil => true
  | .cons row rest => row.alphaFree && rest.alphaFree

end

mutual

private theorem resolveAlphaList_covers (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) :
    ∀ body, (resolveAlphaList coverage active body).alphaFree = true
  | .nil => rfl
  | .cons x rest => by
    simp [resolveAlphaList, MList.alphaFree,
      resolveAlphaItem_covers coverage active x,
      resolveAlphaList_covers coverage active rest]

private theorem resolveAlphaItem_covers (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) :
    ∀ item, (resolveAlphaItem coverage active item).alphaFree = true
  | .space _ => rfl
  | .ink _ _ => rfl
  | .atom _ nuc sup sub _ => by
    simp [resolveAlphaItem, MItem.alphaFree,
      resolveAlphaNucleus_covers coverage active nuc,
      resolveAlphaList_covers coverage active sup,
      resolveAlphaList_covers coverage active sub]

private theorem resolveAlphaNucleus_covers (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) :
    ∀ nucleus, (resolveAlphaNucleus coverage active nucleus).alphaFree = true
  | .sym c => by
    simp only [resolveAlphaNucleus]
    cases resolveCharStack coverage active c <;> rfl
  | .styled _ _ => rfl
  | .word _ => rfl
  | .list body => by
    simpa [resolveAlphaNucleus, MNucleus.alphaFree] using
      resolveAlphaList_covers coverage active body
  | .alpha a src body => by
    simpa [resolveAlphaNucleus, MNucleus.alphaFree] using
      resolveAlphaList_covers coverage (coverage.effectiveAlpha src a :: active) body
  | .frac _ num den => by
    simp [resolveAlphaNucleus, MNucleus.alphaFree,
      resolveAlphaList_covers coverage active num,
      resolveAlphaList_covers coverage active den]
  | .rad deg body => by
    simp [resolveAlphaNucleus, MNucleus.alphaFree,
      resolveAlphaList_covers coverage active deg,
      resolveAlphaList_covers coverage active body]
  | .delim _ _ body => by
    simpa [resolveAlphaNucleus, MNucleus.alphaFree] using
      resolveAlphaList_covers coverage active body
  | .big _ _ => rfl
  | .accent _ _ body => by
    simpa [resolveAlphaNucleus, MNucleus.alphaFree] using
      resolveAlphaList_covers coverage active body
  | .grid _ rows => by
    simpa [resolveAlphaNucleus, MNucleus.alphaFree] using
      resolveAlphaRows_covers coverage active rows
  | .cancel _ _ value body => by
    simp [resolveAlphaNucleus, MNucleus.alphaFree,
      resolveAlphaList_covers coverage active value,
      resolveAlphaList_covers coverage active body]

private theorem resolveAlphaRow_covers (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) :
    ∀ row, (resolveAlphaRow coverage active row).alphaFree = true
  | .nil => rfl
  | .cons cell rest => by
    simp [resolveAlphaRow, MRow.alphaFree,
      resolveAlphaList_covers coverage active cell,
      resolveAlphaRow_covers coverage active rest]

private theorem resolveAlphaRows_covers (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) :
    ∀ rows, (resolveAlphaRows coverage active rows).alphaFree = true
  | .nil => rfl
  | .cons row rest => by
    simp [resolveAlphaRows, MRows.alphaFree,
      resolveAlphaRow_covers coverage active row,
      resolveAlphaRows_covers coverage active rest]

end

/-- Every alphabet boundary is eliminated before a backend can see it. -/
theorem resolveMathAlphas_covers (coverage : MathAlphabetCoverage) (body : MList) :
    (resolveMathAlphas coverage body).alphaFree = true :=
  resolveAlphaList_covers coverage [] body

mutual

private theorem resolveAlphaList_nil_id (coverage : MathAlphabetCoverage) :
    ∀ body, body.alphaFree = true → resolveAlphaList coverage [] body = body
  | .nil, _ => rfl
  | .cons x rest, h => by
    simp only [MList.alphaFree, Bool.and_eq_true] at h
    rw [resolveAlphaList, resolveAlphaItem_nil_id coverage x h.1,
      resolveAlphaList_nil_id coverage rest h.2]

private theorem resolveAlphaItem_nil_id (coverage : MathAlphabetCoverage) :
    ∀ item, item.alphaFree = true → resolveAlphaItem coverage [] item = item
  | .space _, _ => rfl
  | .ink _ _, _ => rfl
  | .atom cls nuc sup sub lim, h => by
    simp only [MItem.alphaFree, Bool.and_eq_true] at h
    rw [resolveAlphaItem, resolveAlphaNucleus_nil_id coverage nuc h.1,
      resolveAlphaList_nil_id coverage sup h.2.1,
      resolveAlphaList_nil_id coverage sub h.2.2]

private theorem resolveAlphaNucleus_nil_id (coverage : MathAlphabetCoverage) :
    ∀ nucleus, nucleus.alphaFree = true →
      resolveAlphaNucleus coverage [] nucleus = nucleus
  | .sym _, _ => rfl
  | .styled _ _, _ => rfl
  | .word _, _ => rfl
  | .list body, h => by
    rw [resolveAlphaNucleus, resolveAlphaList_nil_id coverage body h]
  | .alpha _ _ _, h => by simp [MNucleus.alphaFree] at h
  | .frac spec num den, h => by
    simp only [MNucleus.alphaFree, Bool.and_eq_true] at h
    rw [resolveAlphaNucleus,
      resolveAlphaList_nil_id coverage num h.1,
      resolveAlphaList_nil_id coverage den h.2]
  | .rad deg body, h => by
    simp only [MNucleus.alphaFree, Bool.and_eq_true] at h
    rw [resolveAlphaNucleus,
      resolveAlphaList_nil_id coverage deg h.1,
      resolveAlphaList_nil_id coverage body h.2]
  | .delim l r body, h => by
    rw [resolveAlphaNucleus, resolveAlphaList_nil_id coverage body h]
  | .big _ _, _ => rfl
  | .accent mark stretch body, h => by
    rw [resolveAlphaNucleus, resolveAlphaList_nil_id coverage body h]
  | .grid kind rows, h => by
    rw [resolveAlphaNucleus, resolveAlphaRows_nil_id coverage rows h]
  | .cancel mark spec value body, h => by
    simp only [MNucleus.alphaFree, Bool.and_eq_true] at h
    rw [resolveAlphaNucleus,
      resolveAlphaList_nil_id coverage value h.1,
      resolveAlphaList_nil_id coverage body h.2]

private theorem resolveAlphaRow_nil_id (coverage : MathAlphabetCoverage) :
    ∀ row, row.alphaFree = true → resolveAlphaRow coverage [] row = row
  | .nil, _ => rfl
  | .cons cell rest, h => by
    simp only [MRow.alphaFree, Bool.and_eq_true] at h
    rw [resolveAlphaRow, resolveAlphaList_nil_id coverage cell h.1,
      resolveAlphaRow_nil_id coverage rest h.2]

private theorem resolveAlphaRows_nil_id (coverage : MathAlphabetCoverage) :
    ∀ rows, rows.alphaFree = true → resolveAlphaRows coverage [] rows = rows
  | .nil, _ => rfl
  | .cons row rest, h => by
    simp only [MRows.alphaFree, Bool.and_eq_true] at h
    rw [resolveAlphaRows, resolveAlphaRow_nil_id coverage row h.1,
      resolveAlphaRows_nil_id coverage rest h.2]

end

/-- An already-resolved math list is unchanged. -/
theorem resolveMathAlphas_id (coverage : MathAlphabetCoverage) (body : MList)
    (h : body.alphaFree = true) :
    resolveMathAlphas coverage body = body :=
  resolveAlphaList_nil_id coverage body h

/-- Resolution is idempotent: its output is already the backend form. -/
theorem resolveMathAlphas_fixed_point (coverage : MathAlphabetCoverage) (body : MList) :
    resolveMathAlphas coverage (resolveMathAlphas coverage body) =
      resolveMathAlphas coverage body :=
  resolveMathAlphas_id coverage _ (resolveMathAlphas_covers coverage body)

mutual

private theorem missingAlphaList_nil_id (coverage : MathAlphabetCoverage) :
    ∀ out body, MList.alphaFree body = true →
      missingAlphaList coverage [] out body = out
  | _, .nil, _ => rfl
  | out, .cons x rest, h => by
    simp only [MList.alphaFree, Bool.and_eq_true] at h
    rw [missingAlphaList, missingAlphaItem_nil_id coverage out x h.1,
      missingAlphaList_nil_id coverage out rest h.2]

private theorem missingAlphaItem_nil_id (coverage : MathAlphabetCoverage) :
    ∀ out item, MItem.alphaFree item = true →
      missingAlphaItem coverage [] out item = out
  | _, .space _, _ => rfl
  | _, .ink _ _, _ => rfl
  | out, .atom _ nuc sup sub _, h => by
    simp only [MItem.alphaFree, Bool.and_eq_true] at h
    rw [missingAlphaItem, missingAlphaNucleus_nil_id coverage out nuc h.1,
      missingAlphaList_nil_id coverage out sup h.2.1,
      missingAlphaList_nil_id coverage out sub h.2.2]

private theorem missingAlphaNucleus_nil_id (coverage : MathAlphabetCoverage) :
    ∀ out nucleus, MNucleus.alphaFree nucleus = true →
      missingAlphaNucleus coverage [] out nucleus = out
  | _, .sym _, _ => rfl
  | _, .styled _ _, _ => rfl
  | _, .word _, _ => rfl
  | out, .list body, h => by
    rw [missingAlphaNucleus, missingAlphaList_nil_id coverage out body h]
  | _, .alpha _ _ _, h => by simp [MNucleus.alphaFree] at h
  | out, .frac _ num den, h => by
    simp only [MNucleus.alphaFree, Bool.and_eq_true] at h
    rw [missingAlphaNucleus, missingAlphaList_nil_id coverage out num h.1,
      missingAlphaList_nil_id coverage out den h.2]
  | out, .rad deg body, h => by
    simp only [MNucleus.alphaFree, Bool.and_eq_true] at h
    rw [missingAlphaNucleus, missingAlphaList_nil_id coverage out deg h.1,
      missingAlphaList_nil_id coverage out body h.2]
  | out, .delim _ _ body, h => by
    rw [missingAlphaNucleus, missingAlphaList_nil_id coverage out body h]
  | _, .big _ _, _ => rfl
  | out, .accent _ _ body, h => by
    rw [missingAlphaNucleus, missingAlphaList_nil_id coverage out body h]
  | out, .grid _ rows, h => by
    rw [missingAlphaNucleus, missingAlphaRows_nil_id coverage out rows h]
  | out, .cancel _ _ value body, h => by
    simp only [MNucleus.alphaFree, Bool.and_eq_true] at h
    rw [missingAlphaNucleus, missingAlphaList_nil_id coverage out body h.2,
      missingAlphaList_nil_id coverage out value h.1]

private theorem missingAlphaRow_nil_id (coverage : MathAlphabetCoverage) :
    ∀ out row, MRow.alphaFree row = true →
      missingAlphaRow coverage [] out row = out
  | _, .nil, _ => rfl
  | out, .cons cell rest, h => by
    simp only [MRow.alphaFree, Bool.and_eq_true] at h
    rw [missingAlphaRow, missingAlphaList_nil_id coverage out cell h.1,
      missingAlphaRow_nil_id coverage out rest h.2]

private theorem missingAlphaRows_nil_id (coverage : MathAlphabetCoverage) :
    ∀ out rows, MRows.alphaFree rows = true →
      missingAlphaRows coverage [] out rows = out
  | _, .nil, _ => rfl
  | out, .cons row rest, h => by
    simp only [MRows.alphaFree, Bool.and_eq_true] at h
    rw [missingAlphaRows, missingAlphaRow_nil_id coverage out row h.1,
      missingAlphaRows_nil_id coverage out rest h.2]

end

/-- An alpha-free tree contributes no whole-alphabet loss, for any coverage. -/
theorem missingMathAlphas_alphaFree_exact (coverage : MathAlphabetCoverage) (body : MList)
    (h : body.alphaFree = true) : missingMathAlphas coverage body = #[] :=
  missingAlphaList_nil_id coverage #[] body h

/-- Resolution spends its whole-alphabet census; a second pass adds no note. -/
theorem missingMathAlphas_resolve_exact (coverage : MathAlphabetCoverage) (body : MList) :
    missingMathAlphas coverage (resolveMathAlphas coverage body) = #[] :=
  missingMathAlphas_alphaFree_exact coverage _ (resolveMathAlphas_covers coverage body)

/-- Resolving an alphabet stack is the identity on the classes projection,
for any stack: `MList.classes` reads only the item-level atom class and
never the nucleus, so rewriting a `.sym` glyph or turning an `.alpha`
scope into a `.list` leaves the class sequence — and thus the spacing the
walk inserts — untouched. The stack analogue of `remapList_classes_id`. -/
theorem resolveAlphaList_classes (coverage : MathAlphabetCoverage)
    (active : List (MathAlphabet × MathAlphabetSource)) :
    ∀ l : MList, (resolveAlphaList coverage active l).classes = l.classes
  | .nil => rfl
  | .cons (.atom _ _ _ _ _) rest => by
    simp only [resolveAlphaList, resolveAlphaItem, MList.classes,
      resolveAlphaList_classes coverage active rest]
  | .cons (.space _) rest => by
    simp only [resolveAlphaList, resolveAlphaItem, MList.classes,
      resolveAlphaList_classes coverage active rest]
  | .cons (.ink _ _) rest => by
    simp only [resolveAlphaList, resolveAlphaItem, MList.classes,
      resolveAlphaList_classes coverage active rest]

/-- The top-level resolver leaves the class sequence — and the spacing it
drives — exactly as elaborated. -/
theorem resolveMathAlphas_classes (coverage : MathAlphabetCoverage) (body : MList) :
    (resolveMathAlphas coverage body).classes = body.classes :=
  resolveAlphaList_classes coverage [] body

/-- An optional delimiter push preserves an accumulator-size equality. -/
private theorem optPush_size_congr (o : Option Char) (acc₁ acc₂ : Array Char)
    (h : acc₁.size = acc₂.size) :
    (match o with | some c => acc₁.push c | none => acc₁).size
      = (match o with | some c => acc₂.push c | none => acc₂).size := by
  cases o <;> simp [Array.size_push, h]

mutual

/-- Resolving an alphabet stack preserves the scalar count: it rewrites each
`.sym` glyph one-for-one and turns an `.alpha` scope into a `.list` — which
`MNucleus.scalars` reads identically — while every word, delimiter, accent
mark, and grid cell is carried through unchanged. Stated over equal-size
accumulators so the walk's threading composes; the top-level corollary
takes `#[]`. Glyphs change; the count does not. -/
private theorem resolveAlphaList_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (l : MList) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaList coverage active l).scalarsList acc₁).size
        = (MList.scalarsList acc₂ l).size
  | _, .nil, _, _, hs => by simp [resolveAlphaList, MList.scalarsList, hs]
  | active, .cons x rest, acc₁, acc₂, hs => by
    simp only [resolveAlphaList, MList.scalarsList]
    apply resolveAlphaList_scalars_size coverage active rest
    exact resolveAlphaItem_scalars_size coverage active x acc₁ acc₂ hs

private theorem resolveAlphaItem_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (item : MItem) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaItem coverage active item).scalars acc₁).size
        = (MItem.scalars acc₂ item).size
  | _, .space _, _, _, hs => by simp [resolveAlphaItem, MItem.scalars, hs]
  | _, .ink _ _, _, _, hs => by simp [resolveAlphaItem, MItem.scalars, hs]
  | active, .atom _ nuc sup sub _, acc₁, acc₂, hs => by
    simp only [resolveAlphaItem, MItem.scalars]
    apply resolveAlphaList_scalars_size coverage active sub
    apply resolveAlphaList_scalars_size coverage active sup
    exact resolveAlphaNucleus_scalars_size coverage active nuc acc₁ acc₂ hs

private theorem resolveAlphaNucleus_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (nuc : MNucleus) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaNucleus coverage active nuc).scalars acc₁).size
        = (MNucleus.scalars acc₂ nuc).size
  | active, .sym c, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus]
    cases resolveCharStack coverage active c <;>
      simp [MNucleus.scalars, Array.size_push, hs]
  | _, .styled _ _, _, _, hs => by
    simp [resolveAlphaNucleus, MNucleus.scalars, Array.size_push, hs]
  | _, .word s, _, _, hs => by
    simp [resolveAlphaNucleus, MNucleus.scalars, hs]
  | active, .list body, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    exact resolveAlphaList_scalars_size coverage active body acc₁ acc₂ hs
  | active, .alpha a src body, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    exact resolveAlphaList_scalars_size coverage (coverage.effectiveAlpha src a :: active) body acc₁ acc₂ hs
  | active, .frac spec num den, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    apply optPush_size_congr spec.right
    apply resolveAlphaList_scalars_size coverage active den
    apply resolveAlphaList_scalars_size coverage active num
    exact optPush_size_congr spec.left acc₁ acc₂ hs
  | active, .rad deg body, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    apply resolveAlphaList_scalars_size coverage active body
    exact resolveAlphaList_scalars_size coverage active deg acc₁ acc₂ hs
  | active, .delim l r body, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    apply resolveAlphaList_scalars_size coverage active body
    apply optPush_size_congr r
    exact optPush_size_congr l acc₁ acc₂ hs
  | _, .big d _, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    cases d <;> simp [Array.size_push, hs]
  | active, .accent mark _ body, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    apply resolveAlphaList_scalars_size coverage active body
    by_cases hm : (mark == '\u0305') = true
    · simp [hm, hs]
    · simp [hm, Array.size_push, hs]
  | active, .grid _ rows, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    exact resolveAlphaRows_scalars_size coverage active rows acc₁ acc₂ hs
  | active, .cancel _ _ value body, acc₁, acc₂, hs => by
    simp only [resolveAlphaNucleus, MNucleus.scalars]
    apply resolveAlphaList_scalars_size coverage active value
    exact resolveAlphaList_scalars_size coverage active body acc₁ acc₂ hs

private theorem resolveAlphaRow_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (row : MRow) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaRow coverage active row).scalarsRow acc₁).size
        = (MRow.scalarsRow acc₂ row).size
  | _, .nil, _, _, hs => by simp [resolveAlphaRow, MRow.scalarsRow, hs]
  | active, .cons cell rest, acc₁, acc₂, hs => by
    simp only [resolveAlphaRow, MRow.scalarsRow]
    apply resolveAlphaRow_scalars_size coverage active rest
    exact resolveAlphaList_scalars_size coverage active cell acc₁ acc₂ hs

private theorem resolveAlphaRows_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (rows : MRows) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaRows coverage active rows).scalarsRows acc₁).size
        = (MRows.scalarsRows acc₂ rows).size
  | _, .nil, _, _, hs => by simp [resolveAlphaRows, MRows.scalarsRows, hs]
  | active, .cons row rest, acc₁, acc₂, hs => by
    simp only [resolveAlphaRows, MRows.scalarsRows]
    apply resolveAlphaRows_scalars_size coverage active rest
    exact resolveAlphaRow_scalars_size coverage active row acc₁ acc₂ hs

end

/-- The resolver preserves the document scalar count: the coverage check the
driver runs before layout sees exactly as many scalars after resolution as
before, so an alphabet changes which glyph each scalar asks the face for,
never how many. The registry `_covers`/`_id` chain governs shape; this
governs count. -/
theorem resolveMathAlphas_scalars_size (coverage : MathAlphabetCoverage) (body : MList) :
    ((resolveMathAlphas coverage body).scalarsList #[]).size
      = (MList.scalarsList #[] body).size :=
  resolveAlphaList_scalars_size coverage [] body #[] #[] rfl

/-- Source override survives to resolution. A `\sym…` node's effective
source is forced `sym` (`effectiveSource .sym a = .sym`, regardless of the
document's `MathAlphabetSources`), so on a range the selected face carries
it remaps to the alphabet's mathematical-alphanumeric scalar — `\symsf{R}`
maps into the math sans range even under a default `mathsf=text`, exactly
as it would under an all-sym policy. The text-slot branch is never taken
for a forced-sym push, because `.sym ≠ .text`. -/
theorem resolveCharStack_forcedSym_exact (coverage : MathAlphabetCoverage)
    (a : MathAlphabet) (rest : List (MathAlphabet × MathAlphabetSource))
    (c : Char) (r : MathAlphabetRange)
    (hr : a.rangeOf c = some r) (hcov : coverage.remaps a r = true) :
    resolveCharStack coverage ((a, coverage.effectiveSource .sym a) :: rest) c
      = .sym (a.apply c) := by
  show resolveCharStack coverage ((a, .sym) :: rest) c = .sym (a.apply c)
  simp only [resolveCharStack, MathAlphabet.sourceRangeOf_sym_exact, hr]
  have hne : (MathAlphabetSource.sym == MathAlphabetSource.text) = false := rfl
  cases a.textStyle? <;> simp [hcov, hne, Resolved.inAlphabet]

end LeanTex.Core.Math
