module

public import LeanTex.Core.Color
public import LeanTex.Core.Dim
public import LeanTex.Core.DesignRole
import LeanTex.Core.DeriveBEq

namespace LeanTex.Core.Math

/-! Math atoms, styles, the inter-atom spacing table and math lists: TeX's model (TeXbook
ch. 17–18, Appendix G) over OpenType MATH metrics, as pure data and theorems. -/

/-- TeX's eight atom classes (TeXbook ch. 17). -/
public inductive MathClass where
  | ord
  | op
  | bin
  | rel
  | opening
  | closing
  | punct
  | inner
  deriving Repr, BEq, DecidableEq, Inhabited

public def allClasses : List MathClass :=
  [.ord, .op, .bin, .rel, .opening, .closing, .punct, .inner]

public def MathClass.label : MathClass → String
  | .ord => "ord"
  | .op => "op"
  | .bin => "bin"
  | .rel => "rel"
  | .opening => "open"
  | .closing => "close"
  | .punct => "punct"
  | .inner => "inner"

/-- The four styles and their cramped variants (TeXbook ch. 17). -/
public inductive MathStyle where
  | display (cramped : Bool)
  | text (cramped : Bool)
  | script (cramped : Bool)
  | scriptscript (cramped : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

public def allStyles : List MathStyle :=
  [.display false, .display true, .text false, .text true,
   .script false, .script true, .scriptscript false, .scriptscript true]

namespace MathStyle

/-- Depth in the progression display → text → script → scriptscript. -/
public def rank : MathStyle → Nat
  | .display _ => 3
  | .text _ => 2
  | .script _ => 1
  | .scriptscript _ => 0

public def cramped : MathStyle → Bool
  | .display c | .text c | .script c | .scriptscript c => c

/-- The style of a superscript (TeXbook p. 141); cramping carries. -/
public def sup : MathStyle → MathStyle
  | .display c | .text c => .script c
  | .script c | .scriptscript c => .scriptscript c

/-- The style of a subscript: the superscript's style, cramped. -/
public def sub (s : MathStyle) : MathStyle :=
  match s.sup with
  | .display _ => .display true
  | .text _ => .text true
  | .script _ => .script true
  | .scriptscript _ => .scriptscript true

/-- The cramped variant of a style, how a radicand sets (TeXbook Appendix G rule 11). -/
public def cramp : MathStyle → MathStyle
  | .display _ => .display true
  | .text _ => .text true
  | .script _ => .script true
  | .scriptscript _ => .scriptscript true

/-- The uncramped variant of a style, how a fresh formula in a box starts. -/
public def uncramp : MathStyle → MathStyle
  | .display _ => .display false
  | .text _ => .text false
  | .script _ => .script false
  | .scriptscript _ => .scriptscript false

/-- The style of a fraction's numerator (TeXbook Appendix G rule 15); cramping carries. -/
public def fracNum : MathStyle → MathStyle
  | .display c => .text c
  | .text c => .script c
  | .script c | .scriptscript c => .scriptscript c

/-- The style of a fraction's denominator: the numerator's, cramped
(TeXbook Appendix G rule 15). -/
public def fracDen (s : MathStyle) : MathStyle :=
  s.fracNum.cramp

/-- Script styles, which suppress the conditional spacing entries (TeXbook p. 170). -/
public def scriptish (s : MathStyle) : Bool :=
  s.rank ≤ 1

end MathStyle

public theorem style_progression_decreasing :
    ∀ s ∈ allStyles,
      (s.sup.rank ≤ s.rank ∧ s.sub.rank ≤ s.rank) ∧
      (s.rank = 0 ∨ (s.sup.rank < s.rank ∧ s.sub.rank < s.rank)) := by decide

public theorem scriptscript_fixed_point :
    ∀ s ∈ allStyles, s.rank = 0 → s.sup = s ∧ s.sub.rank = 0 := by decide

public theorem sub_cramped : ∀ s ∈ allStyles, s.sub.cramped = true := by decide

public theorem frac_styles_descend :
    ∀ s ∈ allStyles,
      s.fracNum.rank ≤ s.rank ∧ s.fracDen.rank ≤ s.rank ∧
      s.fracDen.cramped = true ∧ s.cramp.rank = s.rank := by decide

/-- A font's script scale percentages, clamped into (0,100] with scriptscript ≤ script. -/
public structure ScriptScales where
  script : Nat
  scriptscript : Nat
  deriving Repr, BEq, Inhabited

public def ScriptScales.clamp (script scriptscript : Int) : ScriptScales :=
  { script := (script.toNat.min 100).max 1
    scriptscript := (scriptscript.toNat.min ((script.toNat.min 100).max 1)).max 1 }

/-- Font size for a style: the base for display and text, the font's percentages for scripts,
never compounding. -/
public def sizeFor (k : ScriptScales) (base : Int) : MathStyle → Int
  | .display _ | .text _ => base
  | .script _ => base * k.script / 100
  | .scriptscript _ => base * k.scriptscript / 100

public theorem clamp_le_100 (a b : Int) : (ScriptScales.clamp a b).script ≤ 100 :=
  Nat.max_le.mpr ⟨Nat.min_le_right _ _, by decide⟩

public theorem clamp_ss_le_script (a b : Int) :
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

public theorem sizes_shrink (a b base : Int) (hb : 0 ≤ base) (s : MathStyle) :
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

public theorem sizeFor_mono_rank (a b base : Int) (hb : 0 ≤ base) (s s' : MathStyle)
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
      | (simp only [sizeFor]
         first
           | exact Int.le_refl _
           | exact hbase
           | exact hscript
           | exact Int.le_trans hscript hbase)

/-- The math face's size beside a body at `bodySize` so the two x-heights agree: fontspec's
`Scale=MatchLowercase`, in integers. -/
public def mathSize (bodySize xhB upemB xhM upemM : Nat) : Nat :=
  bodySize * xhB * upemM / (upemB * xhM)

public theorem mathSize_le_body_xheight (bodySize xhB upemB xhM upemM : Nat) :
    mathSize bodySize xhB upemB xhM upemM * xhM / upemM ≤
      bodySize * xhB * upemM / (upemB * upemM) := by
  unfold mathSize
  rw [Nat.div_div_eq_div_mul (bodySize * xhB * upemM) upemB xhM |>.symm]
  calc bodySize * xhB * upemM / upemB / xhM * xhM / upemM
      ≤ bodySize * xhB * upemM / upemB / upemM :=
        Nat.div_le_div_right (Nat.div_mul_le_self _ _)
    _ = bodySize * xhB * upemM / (upemB * upemM) := Nat.div_div_eq_div_mul ..

public theorem mathSize_matches (bodySize xhB upemB xhM upemM : Nat) (h : 0 < upemM) :
    mathSize bodySize xhB upemB xhM upemM * xhM / upemM ≤ bodySize * xhB / upemB := by
  have := mathSize_le_body_xheight bodySize xhB upemB xhM upemM
  rwa [Nat.mul_div_mul_right _ _ h] at this

public theorem body_xheight_le_mathSize_next (bodySize xhB upemB xhM upemM : Nat)
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

/-- The math alphabets a formula can ask for by command, each a remap into Unicode's
Mathematical Alphanumeric Symbols; `rm` is the ASCII letters. -/
public inductive MathAlphabet where
  | bb
  | cal
  | frak
  | bf
  /-- `\symbfit`: the bold-italic Latin and Greek alphabet, without digits. -/
  | bfit
  /-- `\symbf` under unicode-math's `bold-style=TeX`: upright bold, lowercase Greek bold italic. -/
  | bfDefault
  | sf
  | tt
  | rm
  | it
  /-- `\bm`/`\boldsymbol`: a near-identity alphabet that keeps every source glyph. -/
  | bm
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The distinct Unicode alphabets: neither `bfDefault`, a selection of `bf` and `bfit`, nor
`bm`. -/
public def allAlphabets : List MathAlphabet :=
  [.bb, .cal, .frak, .bf, .bfit, .sf, .tt, .rm, .it]

/-- Whether a legacy math alphabet takes glyphs from the math symbol face or a text slot. -/
public inductive MathAlphabetSource where
  | sym
  | text
  deriving Repr, BEq, DecidableEq, Inhabited

public def MathAlphabetSource.name : MathAlphabetSource → String
  | .sym => "sym"
  | .text => "text"

public def MathAlphabetSource.ofName? : String → Option MathAlphabetSource
  | "sym" => some .sym
  | "text" => some .text
  | _ => none

/-- Where a math alphabet node came from: `.sym` forces the symbol source, `.doc` reads the
document's policy. -/
public inductive AlphaSource where
  | doc
  | sym
  deriving Repr, BEq, DecidableEq, Inhabited

/-- unicode-math's five option-driven alphabet sources. -/
public structure MathAlphabetSources where
  rm : MathAlphabetSource := .text
  it : MathAlphabetSource := .text
  bf : MathAlphabetSource := .text
  sf : MathAlphabetSource := .text
  tt : MathAlphabetSource := .text
  deriving Repr, BEq, Inhabited

public def MathAlphabet.sourceKey? : String → Option MathAlphabet
  | "mathrm" => some .rm
  | "mathit" => some .it
  | "mathbf" => some .bf
  | "mathsf" => some .sf
  | "mathtt" => some .tt
  | _ => none

public def MathAlphabet.sourceKey : MathAlphabet → Option String
  | .rm => some "mathrm"
  | .it => some "mathit"
  | .bf => some "mathbf"
  | .sf => some "mathsf"
  | .tt => some "mathtt"
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => none

public def MathAlphabetSources.get (s : MathAlphabetSources) : MathAlphabet → MathAlphabetSource
  | .rm => s.rm
  | .it => s.it
  | .bf => s.bf
  | .sf => s.sf
  | .tt => s.tt
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => .sym

public def MathAlphabetSources.set (s : MathAlphabetSources) (a : MathAlphabet)
    (source : MathAlphabetSource) : MathAlphabetSources :=
  match a with
  | .rm => { s with rm := source }
  | .it => { s with it := source }
  | .bf => { s with bf := source }
  | .sf => { s with sf := source }
  | .tt => { s with tt := source }
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => s

/-- Non-default source options as unicode-math spells them. -/
public def MathAlphabetSources.options (s : MathAlphabetSources) : Array String :=
  [MathAlphabet.rm, .it, .bf, .sf, .tt].foldl (fun out a =>
    let source := s.get a
    if source == .text then out
    else out.push s!"{a.sourceKey.getD ""}={source.name}") #[]

/-- The plain letter behind a parsed scalar: a math italic Latin letter's ASCII base. -/
def unItalic (c : Char) : Char :=
  if c == '\u210E' then 'h'
  else if 0x1D44E ≤ c.toNat && c.toNat ≤ 0x1D467 then
    Char.ofNat ('a'.toNat + (c.toNat - 0x1D44E))
  else if 0x1D434 ≤ c.toNat && c.toNat ≤ 0x1D44D then
    Char.ofNat ('A'.toNat + (c.toNat - 0x1D434))
  else c

/-- The Letterlike Symbols holes of the Mathematical Alphanumeric block, as `(alphabet, letter,
scalar)` rows. -/
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

/-- Where each alphabet's `A`, `a` and `0` start in the Mathematical Alphanumeric block; `none`
where it has no such run. -/
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

/-- A separately installed range of a math alphabet, available when its first scalar is. -/
public inductive MathAlphabetRange where
  | latinUpper
  | latinLower
  | digits
  | greekUpper
  | greekLower
  | misc
  deriving Repr, BEq, DecidableEq, Inhabited

def allAlphabetRanges : List MathAlphabetRange :=
  [.latinUpper, .latinLower, .digits, .greekUpper, .greekLower, .misc]

public def MathAlphabetRange.anchor : MathAlphabetRange → Char
  | .latinUpper => 'A'
  | .latinLower => 'a'
  | .digits => '0'
  | .greekUpper => 'Α'
  | .greekLower => Char.ofNat 0x1D6FC
  | .misc => '\u2207'

/-- The ranges a text family serves for a `text`-sourced alphabet: Latin letters and digits. -/
public def MathAlphabetRange.textServed : MathAlphabetRange → Bool
  | .latinUpper | .latinLower | .digits => true
  | .greekUpper | .greekLower | .misc => false

/-- The 58 Greek slots of Unicode's Mathematical Alphanumeric blocks, in upright form. -/
private def uprightGreek : Array Char :=
  "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡϴΣΤΥΦΧΨΩ∇αβγδεζηθικλμνξοπρςστυφχψω∂ϵϑϰϕϱϖ".toList.toArray

private def greekSlot? (c : Char) : Option Nat :=
  if 0x1D6E2 ≤ c.toNat && c.toNat ≤ 0x1D71B then some (c.toNat - 0x1D6E2)
  else uprightGreek.findIdx? (· == c)

/-- The installed alphabet a range of `a` selects, default bold splitting into `bf` and `bfit`. -/
public def MathAlphabet.forRange (a : MathAlphabet) (r : MathAlphabetRange) : MathAlphabet :=
  if a == .bfDefault then
    if r == .greekLower then .bfit else .bf
  else a

/-- The range an input scalar asks this alphabet to remap, if any. -/
public def MathAlphabet.rangeOf (a : MathAlphabet) (c0 : Char) : Option MathAlphabetRange :=
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

/-- One letter, digit or Greek scalar under an alphabet: the Letterlike hole where the block
reserves the slot, else the base-offset scalar. -/
public def MathAlphabet.apply (a : MathAlphabet) (c0 : Char) : Char :=
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

public def MathAlphabet.ranges (a : MathAlphabet) : List MathAlphabetRange :=
  allAlphabetRanges.filter fun r => a.rangeOf r.anchor == some r

/-- The range anchors the selected math face covers, with the document's source policy. -/
public structure MathAlphabetCoverage where
  sources : MathAlphabetSources := {}
  covered : Array (MathAlphabet × MathAlphabetRange) := #[]
  deriving Repr, BEq, Inhabited

public def MathAlphabetCoverage.faceCovers (c : MathAlphabetCoverage)
    (a : MathAlphabet) (r : MathAlphabetRange) : Bool :=
  c.covered.contains (a.forRange r, r)

/-- Whether the resolver remaps this range: exactly when the math face carries its anchor. -/
public def MathAlphabetCoverage.remaps (c : MathAlphabetCoverage)
    (a : MathAlphabet) (r : MathAlphabetRange) : Bool :=
  c.faceCovers a r

/-- The source in force for an alphabet node; `\sym…` forces the symbol source. -/
public def MathAlphabetCoverage.effectiveSource (c : MathAlphabetCoverage)
    (src : AlphaSource) (a : MathAlphabet) : MathAlphabetSource :=
  match src with
  | .sym => .sym
  | .doc => c.sources.get a

/-- The alphabet and source in force for a node, under provenance and document policy. -/
public def MathAlphabetCoverage.effectiveAlpha (c : MathAlphabetCoverage)
    (src : AlphaSource) (a : MathAlphabet) : MathAlphabet × MathAlphabetSource :=
  match src, a with
  | .doc, .bf =>
    match c.sources.bf with
    | .text => (.bf, .text)
    | .sym => (.bfDefault, .sym)
  | _, _ => (a, c.effectiveSource src a)

/-- The Latin letters every alphabet maps. -/
public def latinLetters : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList

/-- The (alphabet, base character) behind a mapped scalar, `apply`'s left inverse. -/
public def MathAlphabet.unapply (c : Char) : Option (MathAlphabet × Char) :=
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

public theorem alpha_apply_inj :
    (allAlphabets.all fun a => latinLetters.all fun c =>
      MathAlphabet.unapply (a.apply c) == some (a, c)) = true := by decide

/-- Stable key for one alphabet in diagnostics and generated reports. -/
public def MathAlphabet.name : MathAlphabet → String
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
public def MathAlphabet.styleLabel : MathAlphabet → String
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

/-- The `(bold, italic)` a text face can synthesize of an alphabet's styling. -/
public def MathAlphabet.synthStyle : MathAlphabet → Bool × Bool
  | .bf | .bfDefault => (true, false)
  | .bfit => (true, true)
  | .it => (false, true)
  | .bm => (true, true)
  | _ => (false, false)

/-- A text family slot a text-sourced math alphabet projects to, numbered as `FontSet`'s. -/
public inductive MathTextSlot where
  | body
  | sans
  | mono
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The `FontSet` slot number (0 body, 1 sans, 2 mono). -/
public def MathTextSlot.toNat : MathTextSlot → Nat
  | .body => 0
  | .sans => 1
  | .mono => 2

/-- The CSS custom property naming this slot's text family. -/
public def MathTextSlot.fontVar : MathTextSlot → String
  | .body => "--font-body"
  | .sans => "--font-sans"
  | .mono => "--font-mono"

/-- The typed style a text-sourced math alphabet resolves to: a text slot, weight and shape. -/
public structure MathTextStyle where
  slot : MathTextSlot
  bold : Bool := false
  italic : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A legacy alphabet's text-family projection under a `text` source; `none` for the shape
alphabets and `bfit`. -/
public def MathAlphabet.textStyle? : MathAlphabet → Option MathTextStyle
  | .rm => some { slot := .body, bold := false, italic := false }
  | .it => some { slot := .body, bold := false, italic := true }
  | .bf => some { slot := .body, bold := true, italic := false }
  | .sf => some { slot := .sans, bold := false, italic := false }
  | .tt => some { slot := .mono, bold := false, italic := false }
  | .bb | .cal | .frak | .bfit | .bfDefault | .bm => none

/-- The range a scalar asks under a source; a text source serves Latin letters and digits. -/
public def MathAlphabet.sourceRangeOf (a : MathAlphabet) (src : MathAlphabetSource)
    (c : Char) : Option MathAlphabetRange :=
  if src == .text && a.textStyle?.isSome then
    (MathAlphabet.rm.rangeOf c).filter (·.textServed) <|> a.rangeOf c
  else a.rangeOf c

public theorem MathAlphabet.sourceRangeOf_sym_exact (a : MathAlphabet) (c : Char) :
    a.sourceRangeOf .sym c = a.rangeOf c := (rfl)

/-- The MathML `mathvariant` a resolved text style declares. -/
public def MathTextStyle.mathvariant : MathTextStyle → String
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

public def MathTextStyle.weight (s : MathTextStyle) : Nat :=
  if s.bold then 700 else 400

/-- The CSS declarations a resolved text style projects: its family, and its weight and style
where they depart from the inherited ones. -/
public def MathTextStyle.css (s : MathTextStyle) : String :=
  let fam := s!"font-family: var({s.slot.fontVar})"
  let wt := if s.bold then s!"; font-weight: {s.weight}" else ""
  let it := if s.italic then "; font-style: italic" else ""
  fam ++ wt ++ it

public theorem fontVar_toNat_agree (s t : MathTextSlot) :
    s.fontVar = t.fontVar ↔ s.toNat = t.toNat := by
  cases s <;> cases t <;> decide

/-- Inter-atom space: none, thin (3 mu), medium (4 mu) or thick (5 mu), at natural width
(TeXbook p. 168). -/
public inductive MathSpace where
  | none
  | thin
  | med
  | thick
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Numerator over 18ths of an em. -/
public def MathSpace.mu : MathSpace → Nat
  | .none => 0
  | .thin => 3
  | .med => 4
  | .thick => 5

/-- TeX's inter-atom spacing table (TeXbook p. 170), and whether each entry survives script
styles. -/
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

/-- The space between adjacent atoms of classes `l` and `r` in style `s`. -/
public def spacing (l r : MathClass) (s : MathStyle) : MathSpace :=
  let (sp, always) := texSpacing l r
  if always || !s.scriptish then sp else .none

/-- Bin degradation, TeX's two rules (TeXbook p. 170), in one forward pass. -/
public def degrade (cs : List MathClass) : List MathClass :=
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

public theorem bin_leading_degrades : degrade [.bin, .ord] = [.ord, .ord] := by decide

theorem degrade_go_length (cs : List MathClass) (acc : Array MathClass)
    (pending : Option MathClass) :
    (degrade.go acc pending cs).size
      = acc.size + (if pending.isSome then 1 else 0) + cs.length := by
  fun_induction degrade.go acc pending cs
  all_goals simp_all
  all_goals omega

public theorem degrade_length (cs : List MathClass) :
    (degrade cs).length = cs.length := by
  simp [degrade, degrade_go_length]

/-- The muskips luatex inserts between two probe atoms, per class pair and style band, read
from `\showbox` on TeX Live 2026. -/
public def luatexProbe (scriptish : Bool) : List (List Nat) :=
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

public theorem spacing_agrees_with_luatex :
    ∀ s ∈ allStyles, ∀ l ∈ allClasses, ∀ r ∈ allClasses,
      (match degrade [.ord, l, r, .ord] with
       | [_, l', r', _] => (spacing l' r' s).mu
       | _ => 1000) =
      (((luatexProbe s.scriptish).getD (allClasses.idxOf l) []).getD
        (allClasses.idxOf r) 1001) := by decide

/-- How a grid column places a narrower cell inside the column's width. -/
public inductive ColAlign where
  | left
  | center
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The column model of a math grid: amsmath's `align` pairs, `gather`, `array` and
`smallmatrix`. -/
public inductive GridKind where
  | align
  /-- amsmath's `aligned`: `align`'s pairs `\minalignsep` apart, after the last too where
  `trailing`. -/
  | aligned (trailing : Bool)
  | gather
  /-- A column spec, the document's or an amsmath environment's, rows `\arraystretch` apart in
  permille. -/
  | array (cols : Array ColAlign) (stretch : Nat)
  /-- amsmath's `smallmatrix`: rows `6\ex@` apart, `\lineskip` `1.5\ex@`, `\ex@` 1 pt at 10 pt. -/
  | small
  deriving Repr, BEq, Inhabited

/-- The alignment of column `k`; an `array` column past its spec centres. -/
public def GridKind.colAlign : GridKind → Nat → ColAlign
  | .align, k | .aligned _, k => if k % 2 == 0 then .right else .left
  | .gather, _ => .center
  | .array cols _, k => cols.getD k .center
  | .small, _ => .center

/-- The gap after column `k` of `n` in mu: 2 em between `align` pairs (standing in for stretched
tabskip), `\arraycolsep` both sides in `array`, `\thickspace` in `small`. -/
public def GridKind.gapAfter : GridKind → Nat → Nat → Nat
  | .align, k, n => if k + 1 == n then 0 else if k % 2 == 0 then 0 else 36
  | .aligned _, _, _ => 0
  | .gather, _, _ => 0
  | .array _ _, k, n => if k + 1 == n then 0 else 18
  | .small, k, n => if k + 1 == n then 0 else 5

/-- amsmath's `\minalignsep`, 10 pt (amsmath.sty): the space `aligned` stands after a pair. -/
public def minAlignSep : Dim.Length := Dim.pt 10

/-- The length gap after column `k` of `n`: `aligned`'s `\minalignsep` after each pair. -/
public def GridKind.pairSep : GridKind → Nat → Nat → Dim.Length
  | .aligned t, k, n =>
    if k % 2 == 0 then 0 else if k + 1 == n && !t then 0 else minAlignSep
  | .align, _, _ | .gather, _, _ | .array _ _, _, _ | .small, _, _ => 0

/-- Where column `k` starts: the widths and gaps of every column before it. -/
public def colOffset (cols : List (Dim.Length × Dim.Length)) (k : Nat) : Dim.Length :=
  match cols, k with
  | _, 0 => 0
  | [], _ + 1 => 0
  | (w, g) :: rest, k + 1 => w + g + colOffset rest k

public theorem colOffset_total (cols : List (Dim.Length × Dim.Length)) :
    colOffset cols cols.length = (cols.map fun c => c.1 + c.2).foldr (· + ·) 0 := by
  induction cols with
  | nil => rfl
  | cons c rest ih =>
    simp only [colOffset, List.length, List.map, List.foldr, ih]

/-- The kern that places a box `inner` wide inside a column `outer` wide. -/
public def ColAlign.pad (a : ColAlign) (outer inner : Dim.Length) : Dim.Length :=
  match a with
  | .left => 0
  | .right => outer - inner
  | .center => (outer - inner) / 2

public theorem pad_within (a : ColAlign) (outer inner : Dim.Length) (h : inner ≤ outer) :
    0 ≤ a.pad outer inner ∧ a.pad outer inner + inner ≤ outer := by
  cases a <;> simp only [ColAlign.pad] <;> length_omega

public theorem pad_center_symmetric (outer inner : Dim.Length) :
    0 ≤ outer - (2 * ColAlign.pad .center outer inner + inner) ∧
    outer - (2 * ColAlign.pad .center outer inner + inner) ≤ Dim.Length.quantum := by
  simp only [ColAlign.pad]
  length_omega

/-- The first variant at least `target` tall in the font's increasing ladder, else the last. -/
public def pickVariant (target : Int) : List (Nat × Int) → Option (Nat × Int)
  | [] => none
  | [v] => some v
  | v :: rest@(_ :: _) => if target ≤ v.2 then some v else pickVariant target rest

/-- An amsmath sized delimiter's `\vcenter` (`\bBigg@`): `step`⁄2 times 1.2 `paren`. -/
public def bigVcenter (paren : Int) (step : Nat) : Int :=
  paren * 12 / 10 * (step : Int) / 2

/-- The least size a sized delimiter grows to (TeXbook Appendix G rule 19): 901‰ of its
`\vcenter`, or all of it but 5 pt at the 10 pt `size`. -/
public def bigTarget (paren size : Int) (step : Nat) : Int :=
  let v := bigVcenter paren step
  max (v * 901 / 1000) (v - size / 2)

/-- The widest variant not exceeding `target`, else the narrowest. -/
public def pickWidest (target : Int) : List (Nat × Int) → Option (Nat × Int)
  | [] => none
  | [v] => some v
  | v :: rest@(w :: _) =>
    if w.2 ≤ target then pickWidest target rest else some v

public theorem pickWidest_covers (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
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

public theorem pickWidest_mem (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
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

public theorem pickVariant_covers (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
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

public theorem pickVariant_mem (target : Int) (vs : List (Nat × Int)) (v : Nat × Int)
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

/-- What `\genfrac` declares beside its operands: delimiters, rule thickness (`none` the face's,
0 no rule) and style (`none` the current one). -/
public structure FracSpec where
  left : Option Char := none
  right : Option Char := none
  rule : Option Dim.Length := none
  style : Option MathStyle := none
  deriving Repr, BEq, Inhabited

/-- cancel.sty's four marks: `\cancel`, `\bcancel`, `\xcancel` and `\cancelto`. -/
public inductive CancelMark where
  | up
  | down
  | cross
  | to
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The style a `\cancelto` value sets in, from the package option in force; never cramped. -/
public inductive CancelSize where
  | same
  | step
  | sup
  deriving Repr, BEq, DecidableEq, Inhabited

public def CancelSize.style : CancelSize → MathStyle → MathStyle
  | .same, .display _ => .text false
  | .same, .text _ => .text false
  | .same, .script _ => .script false
  | .same, .scriptscript _ => .scriptscript false
  | .step, .display _ => .text false
  | .step, .text _ => .script false
  | .step, _ => .scriptscript false
  | .sup, .display _ | .sup, .text _ => .script false
  | .sup, _ => .scriptscript false

/-- What a cancel mark declares beyond its operands, from the package's options and
`\CancelColor`. -/
public structure CancelSpec where
  thick : Bool := false
  room : Bool := false
  size : CancelSize := .step
  color : Option (Ir.Color × Option Ir.ColorRef) := none
  deriving Repr, BEq, Inhabited

/-- cancel.sty's options in its declaration order, and the names it does not declare. -/
public def CancelSpec.ofOptions (opts : List String) : CancelSpec × List String :=
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

/-- What a cancel mark's geometry reads, in base units: the stroke width, the struck box, a
`\cancelto` value's advance and measured ink, and the text-size MATH parameters its superscript
reads. -/
public structure CancelIn where
  rule : Int
  w : Int
  top : Int
  bot : Int
  vw : Int := 0
  vleft : Int := 0
  vright : Int := 0
  vtop : Int := 0
  vbot : Int := 0
  vdepth : Int := 0
  axis : Int := 0
  supDrop : Int := 0
  supUp : Int := 0
  deriving Repr, BEq, Inhabited

/-- A measured target paints only when both axes have nonzero extent. -/
public def CancelIn.hasValueInk (i : CancelIn) : Bool :=
  i.vleft != i.vright && i.vbot != i.vtop

public theorem CancelIn.hasValueInk_contract (i : CancelIn) :
    i.hasValueInk = true ↔ i.vleft ≠ i.vright ∧ i.vbot ≠ i.vtop := by
  simp [hasValueInk]

/-- Measured cancellation in the active math font and style, ink apart from advance. -/
public structure CancelMetric where
  em : Int
  input : CancelIn
  bodyLeft : Int
  bodyRight : Int
  deriving Repr, BEq, Inhabited

/-- TeX's point in base units, the unit cancel.sty states its lengths in. -/
public def cancelPt : Int := (Dim.pt 1).units

/-- A tenth of a point, for cancel.sty's fractional lengths. -/
public def cancelTenths (n : Int) : Int := n * cancelPt / 10

/-- cancel.sty's stroke widths, `\thinlines` and `\thicklines`. -/
public def cancelRule (thick : Bool) : Int := cancelTenths (if thick then 8 else 4)

/-- The arrowhead `\vector` draws, depth from tip to back and half the back's width: line10's
under `\thinlines`, linew10's heavier one under `\thicklines`. -/
public def cancelHeadDepth (thick : Bool) : Int := (if thick then 597 else 397) * cancelPt / 100

public def cancelHeadHalf (thick : Bool) : Int := (if thick then 220 else 149) * cancelPt / 100

/-- A `\cancel` stroke as cancel.sty v2.2's `\@can@slash` draws it: slope as run and rise, and
its horizontal extent, picked by the struck box's aspect. -/
public def cancelSlash (w t : Int) : Nat × Nat × Int :=
  let p := cancelPt
  let ww := max w (2 * p)
  let tt := max t (6 * p)
  if tt < ww then
    let w8 := max ww (8 * p)
    let (run, rise) : Nat × Nat := match (5 * tt / w8).toNat with
      | 0 => (6, 1) | 1 => (4, 1) | 2 => (2, 1) | 3 => (4, 3) | _ => (1, 1)
    (run, rise, w8 + 2 * p)
  else
    let t8 := max tt (8 * p) + 2 * p
    match (5 * ww / t8).toNat with
    | 0 => (1, 6, 16 * t8 / 100)
    | 1 => (1, 4, t8 / 4)
    | 2 => (1, 2, t8 / 2)
    | 3 => (3, 4, 3 * t8 / 4)
    | _ => (1, 1, t8)

/-- cancel.sty's `\line` slopes, as run and rise. -/
public def cancelSlashSlopes : List (Nat × Nat) :=
  [(6, 1), (4, 1), (2, 1), (4, 3), (1, 1), (1, 6), (1, 4), (1, 2), (3, 4)]

public theorem cancelSlash_slope_mem (w t : Int) :
    ((cancelSlash w t).1, (cancelSlash w t).2.1) ∈ cancelSlashSlopes := by
  unfold cancelSlash
  dsimp only
  split
  · split <;> simp [cancelSlashSlopes]
  · split <;> simp [cancelSlashSlopes]

/-- A `\cancelto` vector as cancel.sty v2.2's `\@cancelto` sets it: slope as run and rise, the
horizontal extent `len` its head included, the invisible lead `back` before it, and the value's
kern and lift past the tip. -/
public structure CancelVector where
  run : Nat
  rise : Nat
  len : Int
  back : Int
  kern : Int
  lift : Int
  deriving Repr, BEq, Inhabited

public def cancelVector (w t : Int) : CancelVector :=
  let p := cancelPt
  let ww := max w (2 * p)
  let tt := max t (4 * p)
  let wide (add : Int) := max (ww + add * p) (9 * p) + p
  if tt < ww then
    match (5 * tt / ww).toNat with
    | 0 | 1 => ⟨4, 1, wide 5, 3 * p, cancelTenths 13, 2 * p⟩
    | 2 => ⟨4, 2, wide 4, 3 * p, cancelTenths 13, 2 * p⟩
    | 3 => ⟨4, 3, wide 3, 3 * p, cancelTenths 8, 2 * p⟩
    | _ => ⟨1, 1, wide 2, 3 * p, cancelTenths 3, 3 * p⟩
  else
    let t3 := tt + 3 * p
    let t6 := t3 + 3 * p
    match (5 * ww / t3).toNat with
    | 0 | 1 => ⟨1, 4, t6 / 4, cancelTenths 8, cancelTenths (-12), 4 * p⟩
    | 2 => ⟨1, 2, t6 / 2, cancelTenths 12, cancelTenths (-7), 4 * p⟩
    | 3 => ⟨3, 4, 3 * t6 / 4, cancelTenths 15, cancelTenths (-2), cancelTenths 35⟩
    | _ => ⟨1, 1, t6, 2 * p, cancelTenths 3, 3 * p⟩

/-- cancel.sty's `\vector` slopes, as run and rise. -/
public def cancelVectorSlopes : List (Nat × Nat) :=
  [(4, 1), (4, 2), (4, 3), (1, 1), (1, 4), (1, 2), (3, 4)]

public theorem cancelVector_slope_mem (w t : Int) :
    ((cancelVector w t).run, (cancelVector w t).rise) ∈ cancelVectorSlopes := by
  unfold cancelVector
  dsimp only
  split
  · split <;> simp [cancelVectorSlopes]
  · split <;> simp [cancelVectorSlopes]

public theorem cancelVector_run_pos (w t : Int) : 0 < (cancelVector w t).run := by
  unfold cancelVector
  dsimp only
  split
  · split <;> simp
  · split <;> simp

/-- A segment's length, to the base unit below. -/
public def cancelLength (dx dy : Int) : Int :=
  Int.ofNat (Nat.sqrt (dx.natAbs * dx.natAbs + dy.natAbs * dy.natAbs))

/-- A stroke `rule` wide on the centre line from `p` to `q`, square-ended. -/
public def cancelBand (p q : Int × Int) (rule : Int) : Array (Int × Int) :=
  let dx := q.1 - p.1
  let dy := q.2 - p.2
  let l := max 1 (cancelLength dx dy)
  let nx := -dy * rule / (2 * l)
  let ny := dx * rule / (2 * l)
  #[(p.1 + nx, p.2 + ny), (q.1 + nx, q.2 + ny), (q.1 - nx, q.2 - ny), (p.1 - nx, p.2 - ny)]

/-- An arrowhead at `q` pointing away from `p`, line10's depth and back. -/
public def cancelHead (thick : Bool) (p q : Int × Int) : Array (Int × Int) :=
  let dx := q.1 - p.1
  let dy := q.2 - p.2
  let l := max 1 (cancelLength dx dy)
  let bx := q.1 - dx * cancelHeadDepth thick / l
  let by_ := q.2 - dy * cancelHeadDepth thick / l
  let hw := cancelHeadHalf thick
  #[q, (bx + dy * hw / l, by_ - dx * hw / l), (bx - dy * hw / l, by_ + dx * hw / l)]

/-- The shaft's end: the head's back, or the tail where the head is the whole arrow. -/
public def cancelHeadBack (thick : Bool) (p q : Int × Int) : Int × Int :=
  let dx := q.1 - p.1
  let dy := q.2 - p.2
  let l := max 1 (cancelLength dx dy)
  if l ≤ cancelHeadDepth thick then p
  else (q.1 - dx * cancelHeadDepth thick / l, q.2 - dy * cancelHeadDepth thick / l)

/-- Where a cancel mark's parts stand from the construct's origin on the baseline: the struck
box's shift, each stroke's centre line, the polygons painting them, the value's origin and the
advance. -/
public structure CancelGeom where
  shift : Int
  strokes : Array ((Int × Int) × (Int × Int))
  polys : Array (Array (Int × Int))
  valueX : Int := 0
  valueY : Int := 0
  advance : Int
  deriving Repr, BEq, Inhabited

/-- A `\cancel` stroke centred on the struck box, rising or falling at cancel.sty's slope. -/
public def cancelSlashStroke (i : CancelIn) (shift : Int) (rising : Bool) :
    (Int × Int) × (Int × Int) :=
  let (run, rise, len) := cancelSlash i.w (i.top - i.bot)
  let r := len * rise / run
  let x0 := (2 * shift + i.w - len) / 2
  let y0 := (i.top + i.bot - r) / 2
  if rising then ((x0, y0), (x0 + len, y0 + r)) else ((x0, y0 + r), (x0 + len, y0))

/-- cancel.sty's `\@cancelto` row: the vector box's left edge, the struck box's shift and the
advance, overlapping its neighbours or making room. -/
public def cancelToRow (i : CancelIn) (v : CancelVector) (room : Bool) : Int × Int × Int :=
  if room then
    let tail := v.kern + i.vw
    let col := max (v.back + v.len + tail) (i.w + tail)
    (-v.back + (col - (v.back + v.len + tail)) / 2, -v.back + (col - i.w - tail) / 2,
      col - v.back)
  else ((i.w - v.back - v.len) / 2, 0, i.w)

/-- A cancel mark laid out as cancel.sty v2.2 sets it: each stroke at its quantised slope centred
on the struck box, a `\cancelto` vector's box centred there too, its value a text-style
superscript on that box past the tip. -/
public def cancelGeom (mark : CancelMark) (room : Bool) (i : CancelIn) : CancelGeom :=
  match mark with
  | .up | .down | .cross =>
    let (_, _, len) := cancelSlash i.w (i.top - i.bot)
    let shift := if room then max 0 ((len - i.w) / 2) else 0
    let strokes := match mark with
      | .up => #[cancelSlashStroke i shift true]
      | .down => #[cancelSlashStroke i shift false]
      | _ => #[cancelSlashStroke i shift true, cancelSlashStroke i shift false]
    { shift, strokes, polys := strokes.map fun (p, q) => cancelBand p q i.rule
      advance := if room then max len i.w else i.w }
  | .to =>
    let v := cancelVector i.w (i.top - i.bot)
    let (x0, shift, advance) := cancelToRow i v room
    let h := (v.len + v.back) * v.rise / v.run
    let yb := (i.top + i.bot - h) / 2
    let start := (x0 + v.back, yb + v.back * v.rise / v.run)
    let tip := (x0 + v.back + v.len, yb + h)
    let drop := i.supDrop
    let up := max (i.axis + h - h / 2 - drop) i.supUp
    { shift, strokes := #[(start, tip)]
      polys :=
        let thick := cancelRule false < i.rule
        let back := cancelHeadBack thick start tip
        if back == start then #[cancelHead thick start tip]
        else #[cancelBand start back i.rule, cancelHead thick start tip]
      valueX := tip.1 + v.kern
      -- The value's `\boxmaxdepth` of half a point raises a deeper one.
      valueY := yb + h / 2 - i.axis + up + v.lift + max 0 (i.vdepth - cancelTenths 5)
      advance }

public theorem cancelGeom_slash_centre_between (mark : CancelMark) (room : Bool) (i : CancelIn)
    (h : mark ≠ .to) :
    let g := cancelGeom mark room i
    ∀ s ∈ g.strokes,
      (s.1.1 + s.2.1 - (2 * g.shift + i.w)).natAbs ≤ 1 ∧
      (s.1.2 + s.2.2 - (i.top + i.bot)).natAbs ≤ 1 := by
  dsimp only
  intro s hs
  have key : ∀ rising, let t := cancelSlashStroke i (cancelGeom mark room i).shift rising
      (t.1.1 + t.2.1 - (2 * (cancelGeom mark room i).shift + i.w)).natAbs ≤ 1 ∧
      (t.1.2 + t.2.2 - (i.top + i.bot)).natAbs ≤ 1 := by
    intro rising
    simp only [cancelSlashStroke]
    split <;> dsimp only <;> omega
  cases mark <;> simp only [cancelGeom, ne_eq, not_true_eq_false] at h hs ⊢
  all_goals first
    | (simp only [Array.mem_singleton] at hs; subst hs; exact key _)
    | (simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hs
       rcases hs with rfl | rfl <;> exact key _)

/-- The value stands a fixed kern past the tip and the vector's box is centred on the struck
box. -/
public theorem cancelto_anchor_exact (room : Bool) (i : CancelIn) :
    let v := cancelVector i.w (i.top - i.bot)
    let g := cancelGeom .to room i
    let h := (v.len + v.back) * v.rise / v.run
    (∀ s ∈ g.strokes, g.valueX = s.2.1 + v.kern ∧
      (2 * (s.2.2 - h) + h - (i.top + i.bot)).natAbs ≤ 1) := by
  dsimp only
  intro s hs
  simp only [cancelGeom, Array.mem_singleton] at hs ⊢
  subst hs
  dsimp only
  omega

/-- A value deeper than half a point rises by the excess, as its `\boxmaxdepth` makes it. -/
public theorem cancelto_depth_lift_exact (room : Bool) (i : CancelIn) (d : Int) :
    (cancelGeom .to room { i with vdepth := d }).valueY =
      (cancelGeom .to room { i with vdepth := 0 }).valueY + max 0 (d - cancelTenths 5) := by
  simp only [cancelGeom, cancelToRow]
  have : max 0 (0 - cancelTenths 5) = 0 := by simp only [cancelTenths, cancelPt]; decide
  omega

/-- With room made, the value's advance ends inside the mark's and the vector starts at or after
its origin. -/
public theorem cancelto_room_covers (i : CancelIn) :
    let g := cancelGeom .to true i
    g.valueX + i.vw ≤ g.advance ∧ ∀ s ∈ g.strokes, 0 ≤ s.1.1 := by
  dsimp only
  simp only [cancelGeom, cancelToRow, ite_true, Array.mem_singleton, forall_eq]
  omega

mutual

/-- What an atom sets: a scalar, an upright word, a sub-list, or an assembled construction. -/
public inductive MNucleus where
  | sym (c : Char)
  | word (s : String)
  | list (body : MList)
  /-- A math alphabet before the selected face answers which ranges it carries. -/
  | alpha (alphabet : MathAlphabet) (source : AlphaSource) (body : MList)
  /-- A resolved text-sourced alphabet scalar: the plain base letter under its text style. -/
  | styled (style : MathTextStyle) (c : Char)
  /-- A generalized fraction (TeXbook Appendix G rule 15; `\genfrac`). -/
  | frac (spec : FracSpec) (num den : MList)
  /-- `\sqrt[deg]{body}`: `deg` is `.nil` for the plain square root. -/
  | rad (deg : MList) (body : MList)
  /-- `\left l body \right r`: `none` is the empty `.` delimiter. -/
  | delim (l : Option Char) (r : Option Char) (body : MList)
  /-- A delimiter at one of amsmath's fixed sizes (`\bigl(`); `none` is the empty `.`. -/
  | big (d : Option Char) (step : Nat)
  /-- An alignment's rows, rectangular by the time layout sees them. -/
  | grid (kind : GridKind) (rows : MRows)
  /-- A math accent over its base: `mark` the combining scalar, `stretch` whether it grows to
  the base's width. -/
  | accent (mark : Char) (stretch : Bool) (body : MList)
  /-- A cancel.sty mark over `body`; `value` is `.nil` unless the mark is `to`. -/
  | cancel (mark : CancelMark) (spec : CancelSpec) (value : MList) (body : MList)
  deriving Repr

/-- One item of a math list: an atom with its class, nucleus, scripts and limits flag, a space,
or a colour switch. -/
public inductive MItem where
  | atom (cls : MathClass) (nuc : MNucleus) (sup : MList) (sub : MList)
      (limits : Bool)
  /-- Explicit space in mu (18ths of an em at the current size); negative
  for `\!`. -/
  | space (mu : Int)
  /-- A colour switch: the rest of this list inks in `color`; no atom, no class. -/
  | ink (color : Ir.Color) (name : Option Ir.ColorRef)
  deriving Repr

public inductive MList where
  | nil
  | cons (head : MItem) (tail : MList)
  deriving Repr

/-- One grid row: its cells. -/
public inductive MRow where
  | nil
  | cons (cell : MList) (tail : MRow)
  deriving Repr

public inductive MRows where
  | nil
  | cons (row : MRow) (tail : MRows)
  deriving Repr

end

deriving_structural_beq MNucleus

public instance : Inhabited MList := ⟨.nil⟩
public instance : Inhabited MItem := ⟨.space 0⟩
public instance : Inhabited MNucleus := ⟨.sym '?'⟩
public instance : Inhabited MRow := ⟨.nil⟩
public instance : Inhabited MRows := ⟨.nil⟩

public def MList.ofList (xs : List MItem) : MList :=
  match xs with
  | [] => .nil
  | x :: rest => .cons x (ofList rest)

public def MRow.ofList (xs : List MList) : MRow :=
  match xs with
  | [] => .nil
  | x :: rest => .cons x (ofList rest)

public def MRows.ofList (xs : List MRow) : MRows :=
  match xs with
  | [] => .nil
  | x :: rest => .cons x (ofList rest)

public def MRow.cells : MRow → List MList
  | .nil => []
  | .cons c rest => c :: cells rest

public def MRows.rows : MRows → List MRow
  | .nil => []
  | .cons r rest => r :: rows rest

public def MRow.length (r : MRow) : Nat := r.cells.length

/-- `n` empty cells. -/
def MRow.blanks : Nat → MRow
  | 0 => .nil
  | n + 1 => .cons .nil (blanks n)

def MRow.append (r : MRow) (s : MRow) : MRow :=
  match r with
  | .nil => s
  | .cons c rest => .cons c (rest.append s)

/-- The row padded to `n` cells with empty ones. -/
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

theorem MRow.pad_cells (r : MRow) (n : Nat) :
    (r.pad n).cells = r.cells ++ List.replicate (n - r.length) .nil := by
  simp only [pad, append_cells, blanks_cells]

theorem MRow.pad_length (r : MRow) (n : Nat) (h : r.length ≤ n) :
    (r.pad n).length = n := by
  simp only [length] at h
  simp only [length, pad_cells, List.length_append, List.length_replicate]
  omega

/-- The widest row: what every row pads to. -/
public def MRows.maxCols (rs : MRows) : Nat :=
  (rs.rows.map (·.length)).foldr Nat.max 0

public def MRows.pad (rs : MRows) (n : Nat) : MRows :=
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

public theorem MRows.pad_rectangular (rs : MRows) :
    ∀ r ∈ (rs.pad rs.maxCols).rows, r.length = rs.maxCols := by
  intro r h
  rw [pad_rows] at h
  obtain ⟨r0, hmem, rfl⟩ := List.mem_map.mp h
  exact MRow.pad_length r0 _ (length_le_maxCols rs r0 hmem)

/-- The class an item contributes to spacing; spaces and colour switches carry none. -/
public def MItem.classOf : MItem → Option MathClass
  | .atom cls _ _ _ _ => some cls
  | .space _ => none
  | .ink _ _ => none

/-- The classes of a list's atoms in order, spaces and colour switches skipped. -/
public def MList.classes : MList → List MathClass
  | .nil => []
  | .cons (.atom cls _ _ _ _) rest => cls :: classes rest
  | .cons (.space _) rest => classes rest
  | .cons (.ink _ _) rest => classes rest

mutual

/-- Every scalar a math item sets, counting a `.styled` nucleus's text-face scalar only when
`styled`. -/
@[expose] public def MItem.scalars (styled : Bool) (acc : Array Char) : MItem → Array Char
  | .atom _ nuc sup sub _ =>
    MList.scalarsList styled (MList.scalarsList styled (nuc.scalars styled acc) sup) sub
  | .space _ => acc
  | .ink _ _ => acc

@[expose] public def MNucleus.scalars (styled : Bool) (acc : Array Char) : MNucleus → Array Char
  | .sym c => acc.push c
  | .styled _ c => if styled then acc.push c else acc
  | .word s => s.foldl (·.push ·) acc
  | .list body => MList.scalarsList styled acc body
  | .alpha _ _ body => MList.scalarsList styled acc body
  | .frac spec num den =>
    let acc := match spec.left with
      | some c => acc.push c
      | none => acc
    let acc := MList.scalarsList styled (MList.scalarsList styled acc num) den
    match spec.right with
    | some c => acc.push c
    | none => acc
  | .rad deg body => MList.scalarsList styled (MList.scalarsList styled acc deg) body
  | .delim l r body =>
    let acc := match l with
      | some c => acc.push c
      | none => acc
    let acc := match r with
      | some c => acc.push c
      | none => acc
    MList.scalarsList styled acc body
  | .big d _ =>
    match d with
    | some c => acc.push c
    | none => acc
  | .accent mark _ body =>
    -- U+0305 draws as a rule, never asked of the face.
    let acc := if mark == '\u0305' then acc else acc.push mark
    MList.scalarsList styled acc body
  | .grid _ rows => MRows.scalarsRows styled acc rows
  | .cancel _ _ value body =>
    MList.scalarsList styled (MList.scalarsList styled acc body) value

@[expose] public def MList.scalarsList (styled : Bool) (acc : Array Char) : MList → Array Char
  | .nil => acc
  | .cons x rest => MList.scalarsList styled (x.scalars styled acc) rest

@[expose] public def MRow.scalarsRow (styled : Bool) (acc : Array Char) : MRow → Array Char
  | .nil => acc
  | .cons c rest => MRow.scalarsRow styled (MList.scalarsList styled acc c) rest

@[expose] public def MRows.scalarsRows (styled : Bool) (acc : Array Char) : MRows → Array Char
  | .nil => acc
  | .cons r rest => MRows.scalarsRows styled (MRow.scalarsRow styled acc r) rest

end

private def usedInk (ink : Option (Ir.Color × Option Ir.ColorRef))
    (acc : Array (Ir.Color × Option Ir.ColorRef)) : Array (Ir.Color × Option Ir.ColorRef) :=
  match ink with
  | some p => acc.push p
  | none => acc

mutual

/-- The colours math atoms and generated marks use, with their palette names. -/
public def MList.inks (ink : Option (Ir.Color × Option Ir.ColorRef))
    (acc : Array (Ir.Color × Option Ir.ColorRef)) :
    MList → Array (Ir.Color × Option Ir.ColorRef)
  | .nil => acc
  | .cons (.ink c n) rest => MList.inks (some (c, n)) acc rest
  | .cons x rest => MList.inks ink (MItem.inks ink acc x) rest

def MItem.inks (ink : Option (Ir.Color × Option Ir.ColorRef))
    (acc : Array (Ir.Color × Option Ir.ColorRef)) :
    MItem → Array (Ir.Color × Option Ir.ColorRef)
  | .atom _ nuc sup sub _ =>
    MList.inks ink (MList.inks ink (MNucleus.inks ink acc nuc) sup) sub
  | .space _ | .ink _ _ => acc

def MNucleus.inks (ink : Option (Ir.Color × Option Ir.ColorRef))
    (acc : Array (Ir.Color × Option Ir.ColorRef)) :
    MNucleus → Array (Ir.Color × Option Ir.ColorRef)
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

def MRow.inks (ink : Option (Ir.Color × Option Ir.ColorRef))
    (acc : Array (Ir.Color × Option Ir.ColorRef)) :
    MRow → Array (Ir.Color × Option Ir.ColorRef)
  | .nil => acc
  | .cons c rest => MRow.inks ink (MList.inks ink acc c) rest

def MRows.inks (ink : Option (Ir.Color × Option Ir.ColorRef))
    (acc : Array (Ir.Color × Option Ir.ColorRef)) :
    MRows → Array (Ir.Color × Option Ir.ColorRef)
  | .nil => acc
  | .cons r rest => MRows.inks ink (MRow.inks ink acc r) rest

end

mutual

/-- Every colour of a math list replaced through `f`, with its palette name. -/
@[expose] public def MList.mapInk (f : Ir.Color → Option Ir.ColorRef → Ir.Color) : MList → MList
  | .nil => .nil
  | .cons x rest => .cons (MItem.mapInk f x) (MList.mapInk f rest)

@[expose] public def MItem.mapInk (f : Ir.Color → Option Ir.ColorRef → Ir.Color) : MItem → MItem
  | .atom cls nuc sup sub lim =>
    .atom cls (MNucleus.mapInk f nuc) (MList.mapInk f sup) (MList.mapInk f sub) lim
  | .space mu => .space mu
  | .ink c n => .ink (f c n) n

@[expose] public def MNucleus.mapInk (f : Ir.Color → Option Ir.ColorRef → Ir.Color) : MNucleus → MNucleus
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

@[expose] public def MRow.mapInk (f : Ir.Color → Option Ir.ColorRef → Ir.Color) : MRow → MRow
  | .nil => .nil
  | .cons c rest => .cons (MList.mapInk f c) (MRow.mapInk f rest)

@[expose] public def MRows.mapInk (f : Ir.Color → Option Ir.ColorRef → Ir.Color) : MRows → MRows
  | .nil => .nil
  | .cons r rest => .cons (MRow.mapInk f r) (MRows.mapInk f rest)

end

mutual

public theorem MList.mapInk_scalars (f : Ir.Color → Option Ir.ColorRef → Ir.Color)
    (styled : Bool) :
    ∀ (l : MList) (acc : Array Char),
      (MList.mapInk f l).scalarsList styled acc = l.scalarsList styled acc
  | .nil, _ => rfl
  | .cons x rest, acc => by
    simp only [MList.mapInk, MList.scalarsList, MItem.mapInk_scalars f styled x,
      MList.mapInk_scalars f styled rest]

theorem MItem.mapInk_scalars (f : Ir.Color → Option Ir.ColorRef → Ir.Color)
    (styled : Bool) :
    ∀ (x : MItem) (acc : Array Char), (MItem.mapInk f x).scalars styled acc = x.scalars styled acc
  | .atom _ nuc sup sub _, acc => by
    simp only [MItem.mapInk, MItem.scalars, MNucleus.mapInk_scalars f styled nuc,
      MList.mapInk_scalars f styled sup, MList.mapInk_scalars f styled sub]
  | .space _, _ => rfl
  | .ink _ _, _ => rfl

theorem MNucleus.mapInk_scalars (f : Ir.Color → Option Ir.ColorRef → Ir.Color)
    (styled : Bool) :
    ∀ (n : MNucleus) (acc : Array Char),
      (MNucleus.mapInk f n).scalars styled acc = n.scalars styled acc
  | .sym _, _ => rfl
  | .styled _ _, _ => rfl
  | .word _, _ => rfl
  | .list body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f styled body]
  | .alpha _ _ body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f styled body]
  | .frac _ num den, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f styled num,
      MList.mapInk_scalars f styled den]
  | .rad deg body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f styled deg,
      MList.mapInk_scalars f styled body]
  | .delim _ _ body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f styled body]
  | .big _ _, _ => rfl
  | .accent _ _ body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f styled body]
  | .grid _ rows, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MRows.mapInk_scalars f styled rows]
  | .cancel _ _ value body, acc => by
    simp only [MNucleus.mapInk, MNucleus.scalars, MList.mapInk_scalars f styled body,
      MList.mapInk_scalars f styled value]

theorem MRow.mapInk_scalars (f : Ir.Color → Option Ir.ColorRef → Ir.Color)
    (styled : Bool) :
    ∀ (r : MRow) (acc : Array Char),
      (MRow.mapInk f r).scalarsRow styled acc = r.scalarsRow styled acc
  | .nil, _ => rfl
  | .cons c rest, acc => by
    simp only [MRow.mapInk, MRow.scalarsRow, MList.mapInk_scalars f styled c,
      MRow.mapInk_scalars f styled rest]

theorem MRows.mapInk_scalars (f : Ir.Color → Option Ir.ColorRef → Ir.Color)
    (styled : Bool) :
    ∀ (rs : MRows) (acc : Array Char),
      (MRows.mapInk f rs).scalarsRows styled acc = rs.scalarsRows styled acc
  | .nil, _ => rfl
  | .cons r rest, acc => by
    simp only [MRows.mapInk, MRows.scalarsRows, MRow.mapInk_scalars f styled r,
      MRows.mapInk_scalars f styled rest]

end

/-- What resolving one scalar under a stack produces: a math scalar or a styled base letter. -/
public inductive Resolved where
  | sym (c : Char)
  | styled (style : MathTextStyle) (c : Char)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A symbol alphabet clears an inherited text family but keeps its scalar; `.bm` keeps both. -/
def Resolved.inAlphabet (a : MathAlphabet) (src : MathAlphabetSource) : Resolved → Resolved
  | .sym c => .sym c
  | .styled sty c =>
    if src = .sym ∧ a ≠ .bm then .sym c else .styled sty c

private theorem Resolved.inAlphabet_sym_covers (r : Resolved) (a : MathAlphabet)
    (ha : a ≠ .bm) : ∃ c, r.inAlphabet a .sym = .sym c := by
  cases r with
  | sym c => exact ⟨c, rfl⟩
  | styled sty c => exact ⟨c, by simp [Resolved.inAlphabet, ha]⟩

/-- Resolve one scalar under a stack of active alphabets, innermost first: a text-sourced alphabet
with a text style styles a range it serves, a covered range remaps, and anything else falls through
to the enclosing stack under `Resolved.inAlphabet`'s family reset. -/
public def resolveCharStack (coverage : MathAlphabetCoverage) :
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

theorem resolveCharStack_sym_covers (coverage : MathAlphabetCoverage)
    (a : MathAlphabet) (rest : List (MathAlphabet × MathAlphabetSource)) (c : Char)
    (ha : a ≠ .bm) :
    ∃ d, resolveCharStack coverage ((a, .sym) :: rest) c = .sym d := by
  rw [resolveCharStack]
  exact Resolved.inAlphabet_sym_covers _ a ha

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

mutual

/-- Resolve alphabet boundaries in one structural walk; `active` is the stack, innermost first. -/
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

/-- Resolve every typed alphabet boundary against one selected face's coverage. -/
public def resolveMathAlphas (coverage : MathAlphabetCoverage) (body : MList) : MList :=
  resolveAlphaList coverage [] body

/-- The alphabet a stack blames for a scalar left at its source glyph, mirroring
`resolveCharStack`. -/
public def missingCharAlpha (coverage : MathAlphabetCoverage) :
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

public theorem missingCharAlpha_kept (coverage : MathAlphabetCoverage) :
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

public theorem missingCharAlpha_sym_named (coverage : MathAlphabetCoverage)
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

/-- The alphabets whose active range stayed at its source scalar, first use first. -/
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

public def missingMathAlphas (coverage : MathAlphabetCoverage)
    (body : MList) : Array MathAlphabet :=
  missingAlphaList coverage [] #[] body

mutual

/-- No unresolved alphabet boundary remains in this math tree. -/
@[expose] public def MList.alphaFree : MList → Bool
  | .nil => true
  | .cons x rest => x.alphaFree && rest.alphaFree

@[expose] public def MItem.alphaFree : MItem → Bool
  | .atom _ nuc sup sub _ => nuc.alphaFree && (sup.alphaFree && sub.alphaFree)
  | .space _ | .ink _ _ => true

@[expose] public def MNucleus.alphaFree : MNucleus → Bool
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

@[expose] public def MRow.alphaFree : MRow → Bool
  | .nil => true
  | .cons cell rest => cell.alphaFree && rest.alphaFree

@[expose] public def MRows.alphaFree : MRows → Bool
  | .nil => true
  | .cons row rest => row.alphaFree && rest.alphaFree

end

mutual

/-- Does this math tree set a scalar in a text family slot: a text style's, or a text-sourced
alphabet's under the document's sources? -/
@[expose] public def MList.setsText (slot : MathTextSlot) (src : MathAlphabetSources) :
    MList → Bool
  | .nil => false
  | .cons x rest => x.setsText slot src || rest.setsText slot src

@[expose] public def MItem.setsText (slot : MathTextSlot) (src : MathAlphabetSources) :
    MItem → Bool
  | .atom _ nuc sup sub _ =>
    nuc.setsText slot src || (sup.setsText slot src || sub.setsText slot src)
  | .space _ | .ink _ _ => false

@[expose] public def MNucleus.setsText (slot : MathTextSlot) (src : MathAlphabetSources) :
    MNucleus → Bool
  | .sym _ | .word _ => false
  | .styled style _ => style.slot == slot
  | .list body => body.setsText slot src
  | .alpha a origin body =>
    (a.textStyle?.any (·.slot == slot) && origin == .doc && src.get a == .text) ||
      body.setsText slot src
  | .frac _ num den => num.setsText slot src || den.setsText slot src
  | .rad deg body => deg.setsText slot src || body.setsText slot src
  | .delim _ _ body => body.setsText slot src
  | .big _ _ => false
  | .accent _ _ body => body.setsText slot src
  | .grid _ rows => rows.setsText slot src
  | .cancel _ _ value body => value.setsText slot src || body.setsText slot src

@[expose] public def MRow.setsText (slot : MathTextSlot) (src : MathAlphabetSources) :
    MRow → Bool
  | .nil => false
  | .cons cell rest => cell.setsText slot src || rest.setsText slot src

@[expose] public def MRows.setsText (slot : MathTextSlot) (src : MathAlphabetSources) :
    MRows → Bool
  | .nil => false
  | .cons row rest => row.setsText slot src || rest.setsText slot src

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

public theorem resolveMathAlphas_covers (coverage : MathAlphabetCoverage) (body : MList) :
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

public theorem resolveMathAlphas_id (coverage : MathAlphabetCoverage) (body : MList)
    (h : body.alphaFree = true) :
    resolveMathAlphas coverage body = body :=
  resolveAlphaList_nil_id coverage body h

public theorem resolveMathAlphas_fixed_point (coverage : MathAlphabetCoverage) (body : MList) :
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

public theorem missingMathAlphas_alphaFree_exact (coverage : MathAlphabetCoverage) (body : MList)
    (h : body.alphaFree = true) : missingMathAlphas coverage body = #[] :=
  missingAlphaList_nil_id coverage #[] body h

public theorem missingMathAlphas_resolve_exact (coverage : MathAlphabetCoverage) (body : MList) :
    missingMathAlphas coverage (resolveMathAlphas coverage body) = #[] :=
  missingMathAlphas_alphaFree_exact coverage _ (resolveMathAlphas_covers coverage body)

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

public theorem resolveMathAlphas_classes (coverage : MathAlphabetCoverage) (body : MList) :
    (resolveMathAlphas coverage body).classes = body.classes :=
  resolveAlphaList_classes coverage [] body

private theorem optPush_size_congr (o : Option Char) (acc₁ acc₂ : Array Char)
    (h : acc₁.size = acc₂.size) :
    (match o with | some c => acc₁.push c | none => acc₁).size
      = (match o with | some c => acc₂.push c | none => acc₂).size := by
  cases o <;> simp [Array.size_push, h]

mutual

private theorem resolveAlphaList_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (l : MList) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaList coverage active l).scalarsList true acc₁).size
        = (MList.scalarsList true acc₂ l).size
  | _, .nil, _, _, hs => by simp [resolveAlphaList, MList.scalarsList, hs]
  | active, .cons x rest, acc₁, acc₂, hs => by
    simp only [resolveAlphaList, MList.scalarsList]
    apply resolveAlphaList_scalars_size coverage active rest
    exact resolveAlphaItem_scalars_size coverage active x acc₁ acc₂ hs

private theorem resolveAlphaItem_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (item : MItem) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaItem coverage active item).scalars true acc₁).size
        = (MItem.scalars true acc₂ item).size
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
      ((resolveAlphaNucleus coverage active nuc).scalars true acc₁).size
        = (MNucleus.scalars true acc₂ nuc).size
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
      ((resolveAlphaRow coverage active row).scalarsRow true acc₁).size
        = (MRow.scalarsRow true acc₂ row).size
  | _, .nil, _, _, hs => by simp [resolveAlphaRow, MRow.scalarsRow, hs]
  | active, .cons cell rest, acc₁, acc₂, hs => by
    simp only [resolveAlphaRow, MRow.scalarsRow]
    apply resolveAlphaRow_scalars_size coverage active rest
    exact resolveAlphaList_scalars_size coverage active cell acc₁ acc₂ hs

private theorem resolveAlphaRows_scalars_size (coverage : MathAlphabetCoverage) :
    ∀ (active : List (MathAlphabet × MathAlphabetSource)) (rows : MRows) (acc₁ acc₂ : Array Char),
      acc₁.size = acc₂.size →
      ((resolveAlphaRows coverage active rows).scalarsRows true acc₁).size
        = (MRows.scalarsRows true acc₂ rows).size
  | _, .nil, _, _, hs => by simp [resolveAlphaRows, MRows.scalarsRows, hs]
  | active, .cons row rest, acc₁, acc₂, hs => by
    simp only [resolveAlphaRows, MRows.scalarsRows]
    apply resolveAlphaRows_scalars_size coverage active rest
    exact resolveAlphaRow_scalars_size coverage active row acc₁ acc₂ hs

end

public theorem resolveMathAlphas_scalars_size (coverage : MathAlphabetCoverage) (body : MList) :
    ((resolveMathAlphas coverage body).scalarsList true #[]).size
      = (MList.scalarsList true #[] body).size :=
  resolveAlphaList_scalars_size coverage [] body #[] #[] rfl

public theorem resolveCharStack_forcedSym_exact (coverage : MathAlphabetCoverage)
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
