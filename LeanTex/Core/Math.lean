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
  /-- `\bm`/`\boldsymbol`: everything bold, variables staying italic —
  bold italic letters, bold digits, bold italic lowercase Greek — where
  `\mathbf` (`bf`) sets upright bold, LaTeX's split (bm package docs §1;
  amsldoc §9.1 on `\boldsymbol`). -/
  | bfit
  | sf
  | tt
  | rm
  | it
  deriving Repr, BEq, DecidableEq, Inhabited

def allAlphabets : List MathAlphabet :=
  [.bb, .cal, .frak, .bf, .bfit, .sf, .tt, .rm, .it]

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
`bfit` digits are the bold digits: Unicode encodes no italic digits, and
bold is the half of `\bm`'s meaning a digit can carry. -/
def MathAlphabet.bases : MathAlphabet → Nat × Nat × Option Nat
  | .bb => (0x1D538, 0x1D552, some 0x1D7D8)
  | .cal => (0x1D49C, 0x1D4B6, none)
  | .frak => (0x1D504, 0x1D51E, none)
  | .bf => (0x1D400, 0x1D41A, some 0x1D7CE)
  | .bfit => (0x1D468, 0x1D482, some 0x1D7CE)
  | .sf => (0x1D5A0, 0x1D5BA, some 0x1D7E2)
  | .tt => (0x1D670, 0x1D68A, some 0x1D7F6)
  | .rm => ('A'.toNat, 'a'.toNat, some '0'.toNat)
  | .it => (0x1D434, 0x1D44E, none)

/-- One letter or digit under an alphabet: the Letterlike hole when the
block reserves the slot, else the base-offset scalar; a char the alphabet
does not cover stays itself, so the map is total and `\mathbb{+}` keeps
its plus. Greek: only the bold alphabets touch it — `bf` embolden the
upright capitals (U+1D6A8 block), `bfit` also the italic lowercase
(U+1D736 block, one uniform offset across the letters and their variant
forms) and `∇` — LaTeX's `\mathbf`/`\bm` split. -/
def MathAlphabet.apply (a : MathAlphabet) (c0 : Char) : Char :=
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
    else if (a == .bf || a == .bfit) && 0x391 ≤ c.toNat && c.toNat ≤ 0x3A9 then
      Char.ofNat (0x1D6A8 + (c.toNat - 0x391))
    else if a == .bfit && 0x1D6FC ≤ c.toNat && c.toNat ≤ 0x1D71B then
      Char.ofNat (c.toNat + 0x3A)
    else if a == .bfit && c == '\u2207' then Char.ofNat 0x1D6C1
    else c0

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

/-- The styling an alphabet declares, for the note that names its loss. -/
def MathAlphabet.styleLabel : MathAlphabet → String
  | .bb => "double-struck"
  | .cal => "calligraphic"
  | .frak => "fraktur"
  | .bf => "bold"
  | .bfit => "bold italic"
  | .sf => "sans-serif"
  | .tt => "monospace"
  | .rm => "upright"
  | .it => "italic"

/-- What a text face can synthesize of an alphabet's styling when the math
face lacks the mapped scalar: `(bold, italic)`. The bold and italic
alphabets keep their essence from the text face's own variants; the shape
alphabets (double-struck, calligraphic, fraktur, sans-serif, monospace)
cannot be synthesized — their base letter stands in plain, the loss
named. -/
def MathAlphabet.synthStyle : MathAlphabet → Bool × Bool
  | .bf => (true, false)
  | .bfit => (true, true)
  | .it => (false, true)
  | _ => (false, false)

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
  /-- A math accent over its base: `mark` is the combining scalar
  (unicode-math's table — `\hat` is U+0302), `stretch` whether it grows
  through the face's horizontal variants to the base's width (`\widehat`).
  The U+0305 combining overline is the one mark layout draws as a rule
  from the overbar constants instead of a glyph (TeXbook Appendix G rule
  9): `\overline`'s stretch is then exact at any width. -/
  | accent (mark : Char) (stretch : Bool) (body : MList)
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
  | .accent mark _ body =>
    -- U+0305 draws as a rule, never asked of the face; every other mark is
    -- a glyph the coverage check must see.
    let acc := if mark == '\u0305' then acc else acc.push mark
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

def MathAlphabet.remapNucleus (a : MathAlphabet) : MNucleus → MNucleus
  | .sym c => .sym (a.apply c)
  | .word s => .word s
  | .list body => .list (a.remapList body)
  | .frac num den => .frac (a.remapList num) (a.remapList den)
  | .rad deg body => .rad (a.remapList deg) (a.remapList body)
  | .delim l r body => .delim l r (a.remapList body)
  | .accent mark stretch body => .accent mark stretch (a.remapList body)
  | .grid kind rows => .grid kind (a.remapRows rows)

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

end LeanTex.Core.Math
