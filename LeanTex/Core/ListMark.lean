module

public import LeanTex.Core.Ir

/-! List markers: what stands before an item, per list kind and nesting
level. The values are LaTeX's class defaults, from the documented source
(`classes.dtx`, LaTeX2e base, §Enumerate/§Itemize): enumerate counts
arabic / alph / roman / Alph with the level's own punctuation
(`\labelenumi{\theenumi.}`, `\labelenumii{(\theenumii)}`,
`\labelenumiii{\theenumiii.}`, `\labelenumiv{\theenumiv.}`), and itemize
marks bullet / bold en-dash / centered asterisk / centered dot
(`\labelitemi`..`\labelitemiv`). The numbering functions carry their own
decoders, so "an ordered list shows its order" is a theorem about these
functions, not an eyeballed rendering. -/

-- Ir is a signature dependency of `marker` and its text contract. The two
-- exposed formatting wrappers are unfolded by HtmlDoc's anchor proof and
-- Elab's appendix-number proof; the digit decoder and roman table stay internal.

namespace LeanTex.Core.ListMark

open LeanTex.Core

-- Arabic -----------------------------------------------------------------------

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

/-- Every char the arabic encoding emits is an ASCII digit. -/
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

-- Alph / alph ------------------------------------------------------------------

/-- `\@alph` / `\@Alph`: a–z (A–Z) for 1–26; LaTeX errors past 26
("Counter too large"), leantex degrades to arabic so something still
renders. `base` is `'a'.toNat` or `'A'.toNat`. -/
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
  · -- both single letters: the code point recovers the index
    next hm hn =>
    have hl := String.ofList_inj.mp h
    have hc : Char.ofNat (base + (m - 1)) = Char.ofNat (base + (n - 1)) := by
      simpa using hl
    have := congrArg Char.toNat hc
    rw [toNat_ofNat_letter hb (by omega), toNat_ofNat_letter hb (by omega)] at this
    omega
  · -- a letter is never an arabic string: digits stop at 57, letters start at 65
    next hm hn =>
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

-- Roman ------------------------------------------------------------------------

/-- The subtractive table, value-descending, as `\romannumeral` produces. -/
def romanTable : List (Nat × String) :=
  [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"),
   (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]

/-- `\@roman`: i, ii, iii, iv, … Injectivity is checked executably in the
test suite over LaTeX's whole counter range (`romanVal` round-trips on
1–32767); it is a tested property, not a theorem. -/
public def romanN (n : Nat) : String :=
  let (out, _) := romanTable.foldl (fun (acc, r) (v, s) =>
    (acc ++ String.join (List.replicate (r / v) s), r % v)) ("", n)
  out

def romanCharVal (c : Char) : Nat :=
  if c = 'm' then 1000 else if c = 'd' then 500 else if c = 'c' then 100
  else if c = 'l' then 50 else if c = 'x' then 10 else if c = 'v' then 5
  else if c = 'i' then 1 else 0

/-- Decoder: a value standing before a larger one subtracts. The test
oracle for `romanN`; only well-formed input reaches it. -/
public def romanVal : List Char → Nat
  | [] => 0
  | c :: rest =>
    let v := romanCharVal c
    match rest.head? with
    | some c' => if v < romanCharVal c' then romanVal rest - v else v + romanVal rest
    | none => v

-- Labels -----------------------------------------------------------------------

/-- `\labelenumi`..`\labelenumiv`: the numbering with the level's own
punctuation (classes.dtx). Levels are 1-based and already clamped to 1–4
by the caller. -/
public def enumLabel (level n : Nat) : String :=
  match level with
  | 2 => "(" ++ alphN n ++ ")"
  | 3 => romanN n ++ "."
  | 4 => AlphN n ++ "."
  | _ => arabicN n ++ "."

/-- Order is shown: within one enumerate, two distinct item numbers never
share a label. Levels 1, 2 and 4 are theorems through the decoders above;
level 3 (roman) is the executable round-trip check in the test suite. -/
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

-- Itemize ----------------------------------------------------------------------

/-- `\labelitemi`..`\labelitemiv` (classes.dtx): bullet, en dash, centered
asterisk, centered dot — with an ASCII stand-in per level for a machine
where no face covers the glyph, so a marker never renders as nothing. The
stand-ins keep adjacent levels distinct whichever of the pair degrades. -/
def itemGlyph (level : Nat) : Char × Char :=
  match level with
  | 2 => ('–', '-')   -- \bfseries\textendash
  | 3 => ('∗', '*')   -- \textasteriskcentered (U+2217)
  | 4 => ('·', '.')   -- \textperiodcentered
  | _ => ('•', '*')   -- \textbullet

/-- The itemize marker character: the class glyph when a face covers it,
its stand-in otherwise. A function of the level alone — no item index —
which is the "depth is shown" invariant by construction. -/
public def itemMark (level : Nat) (haveGlyph : Bool) : Char :=
  let (c, standin) := itemGlyph level
  if haveGlyph then c else standin

/-- Depth is shown: adjacent itemize levels never share a marker, whether
either side renders its class glyph or its stand-in. -/
public theorem itemMark_adjacent_distinct :
    ∀ level, level ≥ 1 → level ≤ 3 → ∀ b1 b2,
      itemMark level b1 ≠ itemMark (level + 1) b2 := by
  intro level h1 h3 b1 b2
  match level, h1, h3 with
  | 1, _, _ | 2, _, _ | 3, _, _ => cases b1 <;> cases b2 <;> decide

-- The marker as content ---------------------------------------------------------

/-- The default marker for one item, as inline content: enumerate numbers
per level, itemize marks per level, both through the same text path as any
declared marker — so the font/fallback machinery and its diagnostics apply
to defaults and overrides alike. `covered` says whether any loaded face
sets a char; the class glyph degrades to its stand-in rather than to
nothing. The level-2 itemize dash is bold, as `\labelitemii` says. -/
public def marker (ordered : Bool) (level n : Nat) (covered : Char → Bool) :
    Array Ir.Inline :=
  if ordered then #[.text (enumLabel level n)]
  else
    let s := String.ofList [itemMark level (covered (itemGlyph level).1)]
    if level = 2 then #[.styled .bold #[.text s]] else #[.text s]

/-- An ordered list's marker shows its order: the marker content of item
`n` is exactly the level's numbering label (classes.dtx's
`\labelenumi`..`\labelenumiv`, the census's marker-kind fact as a theorem).
`enumLabel_inj` adds that two indices never share it. -/
public theorem ordered_marker_shows_order (level n : Nat) (covered : Char → Bool) :
    Ir.plainText (marker true level n covered) = enumLabel level n := by
  simp [marker, Ir.plainText, Ir.plainTextList, Ir.plainTextOne]

/-- The scalars a list at this level may ask a face for, so the driver's
fallback scan covers default markers before layout begins. Enumerate labels
are ASCII (letters, digits, the parentheses and dot); itemize needs the
level's class glyph, its stand-in riding along. -/
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
