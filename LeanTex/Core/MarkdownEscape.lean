module

public import LeanTex.Core.MarkdownDoc
import all LeanTex.Core.MarkdownDoc
import all LeanTex.Core.CiteKey

/-! The twin's text escapes read back: under a model of how CommonMark's inline scan reads a run of
text, the escaped spelling of any text reads as that text. -/

namespace LeanTex.Core.MarkdownDoc

/-- ASCII punctuation, the characters a backslash escapes (CommonMark §2.4). -/
@[expose] public def asciiPunct (c : Char) : Bool :=
  "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList.contains c

/-- Whether an unescaped character opens inline markup (CommonMark §6), a pipe outside a cell where
`pipes`, or a citation where `ats`. -/
@[expose] public def opensInline (pipes ats : Bool) (prev : Option Char) (c : Char)
    (rest : List Char) : Bool :=
  c == '`' || c == '*' || c == '_' || c == '[' || c == ']' || c == '<' || c == '&' ||
    c == '\\' || c == '\n' || c == '\r' || (pipes && c == '|') ||
    (ats && c == '@' && citeOpens prev rest)

/-- A run of text as the inline scan reads its markup: an escaped punctuation character as itself,
the decimal reference to a line end as that line end, and no reading where unescaped markup opens;
the typography smart punctuation sets and the white space it folds are `Text.norm`'s. -/
@[expose] public def readText (pipes ats : Bool) : Option Char → List Char → Option (List Char)
  | _, [] => some []
  | _, '\\' :: c :: rest =>
    if asciiPunct c then (readText pipes ats (some c) rest).map (c :: ·) else none
  | _, '&' :: '#' :: '1' :: '0' :: ';' :: rest =>
    (readText pipes ats (some '\n') rest).map ('\n' :: ·)
  | _, '&' :: '#' :: '1' :: '3' :: ';' :: rest =>
    (readText pipes ats (some '\r') rest).map ('\r' :: ·)
  | prev, c :: rest =>
    if opensInline pipes ats prev c rest then none
    else (readText pipes ats (some c) rest).map (c :: ·)

private theorem escapeCharsFrom_head (pipes ats : Bool) (q : Option Char) (d : Char)
    (t : List Char) :
    (escapeCharsFrom pipes ats q (d :: t)).head? = some '\\' ∨
      (escapeCharsFrom pipes ats q (d :: t)).head? = some '&' ∨
      (escapeCharsFrom pipes ats q (d :: t)).head? = some d := by
  simp only [escapeCharsFrom]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

private theorem citeOpens_escape (pipes ats : Bool) (prev q : Option Char) (rest : List Char)
    (h : citeOpens prev rest = false) :
    citeOpens prev (escapeCharsFrom pipes ats q rest) = false := by
  cases rest with
  | nil => simpa [escapeCharsFrom] using h
  | cons d t =>
    unfold citeOpens at h ⊢
    cases hp : !(prev.any CiteKey.isAlnum)
    · rfl
    · simp only [Bool.true_and] at h ⊢
      rcases escapeCharsFrom_head pipes ats q d t with hd | hd | hd <;> rw [hd]
      · decide
      · decide
      · rw [hp, Bool.true_and] at h; exact h

private theorem readText_plain (pipes ats : Bool) (prev : Option Char) (c : Char)
    (rest : List Char) (hb : c ≠ '\\') (ha : c ≠ '&')
    (ho : opensInline pipes ats prev c rest = false) :
    readText pipes ats prev (c :: rest) = (readText pipes ats (some c) rest).map (c :: ·) := by
  rw [readText.eq_def]
  split
  · next h => cases h
  · next h => cases h; exact absurd rfl hb
  · next h => cases h; exact absurd rfl ha
  · next h => cases h; exact absurd rfl ha
  · next heq =>
    injection heq with h1 h2
    subst h1 h2
    simp [ho]

/-- The escaped spelling of any text after `prev` reads back, under the model, as that text. -/
public theorem escapeCharsFrom_read_id (pipes ats : Bool) :
    (prev : Option Char) → (l : List Char) →
      readText pipes ats prev (escapeCharsFrom pipes ats prev l) = some l
  | _, [] => by simp [escapeCharsFrom, readText]
  | prev, c :: rest => by
    have ih := escapeCharsFrom_read_id pipes ats (some c) rest
    simp only [escapeCharsFrom]
    split
    · next he =>
      have hp : asciiPunct c = true := by
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at he
        rcases he with (((((((((h | h) | h) | h) | h) | h) | ⟨-, h⟩) | h) | h) | ⟨⟨h, -⟩, -⟩) <;>
          (subst h; decide)
      rw [readText.eq_def]
      simp [hp, ih]
    · next he =>
      split
      · next hn =>
        have : c = '\n' := by simpa using hn
        subst this
        rw [readText.eq_def]
        simp [ih]
      · next hn =>
        split
        · next hr =>
          have : c = '\r' := by simpa using hr
          subst this
          rw [readText.eq_def]
          simp [ih]
        · next hr =>
          simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, not_or, not_and] at he
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := he
          have ho : opensInline pipes ats prev c (escapeCharsFrom pipes ats (some c) rest) = false := by
            simp only [opensInline, Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff]
            refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩, h8⟩, h9⟩, h1⟩, by simpa using hn⟩,
              by simpa using hr⟩, ?_⟩, ?_⟩
            · cases pipes
              · exact Or.inl rfl
              · exact Or.inr (h7 rfl)
            · by_cases hat : (ats && c == '@') = true
              · simp only [Bool.and_eq_true, beq_iff_eq] at hat
                right
                have hc : citeOpens prev rest = false := by
                  cases hcr : citeOpens prev rest
                  · rfl
                  · exact absurd hcr (by simpa using h10 ⟨hat.2, hat.1⟩)
                exact citeOpens_escape pipes ats prev (some c) rest hc
              · left
                cases ats <;> simp_all
          rw [readText_plain pipes ats prev c _ h1 h9 ho, ih]
          rfl

/-- The escaped spelling of any text reads back, under the model, as that text. -/
public theorem escape_read_id (pipes ats : Bool) (l : List Char) :
    readText pipes ats none (escapeChars pipes ats l) = some l :=
  escapeCharsFrom_read_id pipes ats none l

end LeanTex.Core.MarkdownDoc
