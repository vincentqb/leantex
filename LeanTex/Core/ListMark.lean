module

public import LeanTex.Core.Ir

/-! List markers per kind and nesting level: LaTeX's class defaults (classes.dtx, §Enumerate,
§Itemize), with decoders proving an ordered list shows its order. -/

namespace LeanTex.Core.ListMark

open LeanTex.Core

/-- Decimal digits of `n`, least significant first. -/
public def digitsRev (n : Nat) : List Char :=
  if h : n < 10 then [Nat.digitChar n]
  else Nat.digitChar (n % 10) :: digitsRev (n / 10)

def digitVal (c : Char) : Nat :=
  if c.toNat ≥ 48 then c.toNat - 48 else 0

/-- Decoder for `digitsRev`, the injectivity witness. -/
def undigitsRev : List Char → Nat
  | [] => 0
  | c :: cs => digitVal c + 10 * undigitsRev cs

theorem digitVal_digitChar {d : Nat} (h : d < 10) : digitVal (Nat.digitChar d) = d := by
  simp [digitVal, Nat.toNat_digitChar_of_lt_ten h]

theorem undigitsRev_digitsRev (n : Nat) : undigitsRev (digitsRev n) = n := by
  unfold digitsRev
  split
  · next h => simp [undigitsRev, digitVal_digitChar h]
  · next h =>
    simp [undigitsRev, digitVal_digitChar (Nat.mod_lt n (by omega)),
      undigitsRev_digitsRev (n / 10)]
    omega

theorem digitChar_ascii {d : Nat} (h : d < 10) :
    48 ≤ (Nat.digitChar d).toNat ∧ (Nat.digitChar d).toNat ≤ 57 := by
  rw [Nat.toNat_digitChar_of_lt_ten h]
  omega

public theorem digitsRev_digits {n : Nat} {c : Char} (h : c ∈ digitsRev n) :
    48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  unfold digitsRev at h
  split at h
  · next hn =>
    simp at h
    subst h
    exact digitChar_ascii hn
  · next hn =>
    simp at h
    cases h with
    | inl h =>
      subst h
      exact digitChar_ascii (Nat.mod_lt n (by omega))
    | inr h => exact digitsRev_digits h

/-- `\@arabic`: 1, 2, 3, … -/
@[expose] public def arabicN (n : Nat) : String := String.ofList (digitsRev n).reverse

public theorem arabicN_inj {m n : Nat} (h : arabicN m = arabicN n) : m = n := by
  have hl : (digitsRev m).reverse = (digitsRev n).reverse := String.ofList_inj.mp h
  have : digitsRev m = digitsRev n := by
    have := congrArg List.reverse hl
    simpa using this
  calc m = undigitsRev (digitsRev m) := (undigitsRev_digitsRev m).symm
    _ = undigitsRev (digitsRev n) := by rw [this]
    _ = n := undigitsRev_digitsRev n

/-- `\@alph` / `\@Alph`: a–z (A–Z) for 1–26, else arabic where LaTeX stops with "Counter too
large"; `base` is `'a'.toNat` or `'A'.toNat`. -/
public def letterN (base : Nat) (n : Nat) : String :=
  if 1 ≤ n ∧ n ≤ 26 then String.ofList [Char.ofNat (base + (n - 1))]
  else arabicN n

public def alphN : Nat → String := letterN 'a'.toNat
@[expose] public def AlphN : Nat → String := letterN 'A'.toNat

theorem toNat_ofNat_letter {base k : Nat} (hb : base = 97 ∨ base = 65) (hk : k < 26) :
    (Char.ofNat (base + k)).toNat = base + k := by
  have hv : Nat.isValidChar (base + k) := by
    unfold Nat.isValidChar
    omega
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]
  omega

public theorem letterN_inj {base m n : Nat} (hb : base = 97 ∨ base = 65)
    (h : letterN base m = letterN base n) : m = n := by
  unfold letterN at h
  split at h <;> split at h
  · next hm hn =>
    have hl := String.ofList_inj.mp h
    have hc : Char.ofNat (base + (m - 1)) = Char.ofNat (base + (n - 1)) := by
      simpa using hl
    have := congrArg Char.toNat hc
    rw [toNat_ofNat_letter hb (by omega), toNat_ofNat_letter hb (by omega)] at this
    omega
  · next hm hn =>
    have hl := String.ofList_inj.mp h
    have hmem : Char.ofNat (base + (m - 1)) ∈ (digitsRev n).reverse := by
      rw [← hl]; simp
    have hd := digitsRev_digits (List.mem_reverse.mp hmem)
    have hcm : (Char.ofNat (base + (m - 1))).toNat = base + (m - 1) :=
      toNat_ofNat_letter hb (by omega)
    omega
  · next hm hn =>
    have hl := String.ofList_inj.mp h
    have hmem : Char.ofNat (base + (n - 1)) ∈ (digitsRev m).reverse := by
      rw [hl]; simp
    have hd := digitsRev_digits (List.mem_reverse.mp hmem)
    have hcn : (Char.ofNat (base + (n - 1))).toNat = base + (n - 1) :=
      toNat_ofNat_letter hb (by omega)
    omega
  · exact arabicN_inj h

/-- The subtractive table, value-descending, as `\romannumeral` produces. -/
def romanTable : List (Nat × String) :=
  [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"),
   (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]

/-- `\@roman`: i, ii, iii, iv, … -/
public def romanN (n : Nat) : String :=
  let (out, _) := romanTable.foldl (fun (acc, r) (v, s) =>
    (acc ++ String.join (List.replicate (r / v) s), r % v)) ("", n)
  out

/-- A counter's value in a numeral style, as `\arabic`, `\alph`, `\Alph`, `\roman` and `\Roman`
set it. -/
public def numText (style : Ir.NumStyle) (n : Nat) : String :=
  match style with
  | .arabic => arabicN n
  | .alph => alphN n
  | .uAlph => AlphN n
  | .roman => romanN n
  | .uRoman => (romanN n).toUpper
  | .gobble => ""

/-- The page's folio as its numeral style sets it. -/
public def folioText (s : Ir.PageState) : String := numText s.style s.folio

def romanCharVal (c : Char) : Nat :=
  if c = 'm' then 1000 else if c = 'd' then 500 else if c = 'c' then 100
  else if c = 'l' then 50 else if c = 'x' then 10 else if c = 'v' then 5
  else if c = 'i' then 1 else 0

/-- Decoder for `romanN`: a value standing before a larger one subtracts. -/
public def romanVal : List Char → Nat
  | [] => 0
  | c :: rest =>
    let v := romanCharVal c
    match rest.head? with
    | some c' => if v < romanCharVal c' then romanVal rest - v else v + romanVal rest
    | none => v

/-- `\labelenumi`..`\labelenumiv`: the numbering with the level's own punctuation (classes.dtx),
levels 1–4. -/
public def enumLabel (level n : Nat) : String :=
  match level with
  | 2 => "(" ++ alphN n ++ ")"
  | 3 => romanN n ++ "."
  | 4 => AlphN n ++ "."
  | _ => arabicN n ++ "."

/-- Two item numbers never share a label; roman, level 3, is checked by the suite instead. -/
public theorem enumLabel_inj {level m n : Nat} (hl : level ≠ 3)
    (h : enumLabel level m = enumLabel level n) : m = n := by
  match level, hl with
  | 2, _ =>
    simp only [enumLabel] at h
    have h2 := (String.append_left_inj ")").mp h
    exact letterN_inj (.inl rfl) ((String.append_right_inj "(").mp h2)
  | 4, _ =>
    simp only [enumLabel] at h
    exact letterN_inj (.inr rfl) ((String.append_left_inj ".").mp h)
  | 3, h3 => exact absurd rfl h3
  | 0, _ =>
    simp only [enumLabel] at h
    exact arabicN_inj ((String.append_left_inj ".").mp h)
  | 1, _ =>
    simp only [enumLabel] at h
    exact arabicN_inj ((String.append_left_inj ".").mp h)
  | k + 5, _ =>
    simp only [enumLabel] at h
    exact arabicN_inj ((String.append_left_inj ".").mp h)

/-- `\labelitemi`..`\labelitemiv` (classes.dtx), each with an ASCII stand-in. -/
def itemGlyph (level : Nat) : Char × Char :=
  match level with
  | 2 => ('–', '-')   -- \bfseries\textendash
  | 3 => ('∗', '*')   -- \textasteriskcentered (U+2217)
  | 4 => ('·', '.')   -- \textperiodcentered
  | _ => ('•', '*')   -- \textbullet

/-- The itemize marker: the class glyph when a face covers it, else its stand-in. -/
public def itemMark (level : Nat) (haveGlyph : Bool) : Char :=
  let (c, standin) := itemGlyph level
  if haveGlyph then c else standin

public theorem itemMark_adjacent_distinct :
    ∀ level, level ≥ 1 → level ≤ 3 → ∀ b1 b2,
      itemMark level b1 ≠ itemMark (level + 1) b2 := by
  intro level h1 h3 b1 b2
  match level, h1, h3 with
  | 1, _, _ | 2, _, _ | 3, _, _ => cases b1 <;> cases b2 <;> decide

/-- One item's default marker as inline content, through the same text path as a declared one. -/
public def marker (ordered : Bool) (level n : Nat) (covered : Char → Bool) :
    Array Ir.Inline :=
  if ordered then #[.text (enumLabel level n)]
  else
    let s := String.ofList [itemMark level (covered (itemGlyph level).1)]
    if level = 2 then #[.styled .bold #[.text s]] else #[.text s]

public theorem ordered_marker_shows_order (level n : Nat) (covered : Char → Bool) :
    Ir.plainText (marker true level n covered) = enumLabel level n := by
  simp [marker, Ir.plainText, Ir.plainTextList, Ir.plainTextOne]

/-- The scalars a list at this level may ask a face for, for the driver's fallback scan. -/
public def scalars (ordered : Bool) (level : Nat) : String :=
  if ordered then
    match level with
    | 2 => "abcdefghijklmnopqrstuvwxyz()"
    | 3 => "mdclxvi."
    | 4 => "ABCDEFGHIJKLMNOPQRSTUVWXYZ."
    | _ => "0123456789."
  else
    let (c, standin) := itemGlyph level
    String.ofList [c, standin]

end LeanTex.Core.ListMark
