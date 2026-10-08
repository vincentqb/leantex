module

namespace LeanTex.Core.Ir

/-- A document title and the six body heading ranks. A body `h1` shares
the title's rank, not its furniture or uniqueness semantics. HTML and PDF
both define exactly six heading ranks (HTML §4.3.6; ISO 32000-2 §14.8.4.4);
the type cannot ask either artifact to invent a seventh. -/
public inductive HeadingLevel where
  | title | h1 | h2 | h3 | h4 | h5 | h6
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Inhabited

/-- Preserve the native section indices: title 0, section 1, subsection 2,
subsubsection 3. The body h1 is deliberately explicit. These finite
instances admit no out-of-range heading. -/
public instance : OfNat HeadingLevel 0 := ⟨.title⟩
public instance : OfNat HeadingLevel 1 := ⟨.h2⟩
public instance : OfNat HeadingLevel 2 := ⟨.h3⟩
public instance : OfNat HeadingLevel 3 := ⟨.h4⟩

/-- Keep the native IR dump's established indices, while distinguishing a
body h1 from the title. Serialization of artifacts reads `headingRank`. -/
public instance : ToString HeadingLevel where
  toString
    | .title => "0"
    | .h1 => "h1"
    | .h2 => "1"
    | .h3 => "2"
    | .h4 => "3"
    | .h5 => "4"
    | .h6 => "5"

/-- The one structural rank shared by HTML, tagged PDF and Markdown.
A title and a body h1 coexist at rank one; neither consumes a body rank. -/
@[expose] public def headingRank : HeadingLevel → Nat
  | .title | .h1 => 1
  | .h2 => 2
  | .h3 => 3
  | .h4 => 4
  | .h5 => 5
  | .h6 => 6

/-- CommonMark's ATX and setext ranks name body headings, never a title. -/
public def HeadingLevel.ofRank? : Nat → Option HeadingLevel
  | 1 => some .h1
  | 2 => some .h2
  | 3 => some .h3
  | 4 => some .h4
  | 5 => some .h5
  | 6 => some .h6
  | _ => none

/-- The style slot belongs to the heading's semantic identity. The title
does not lend its template to a body h1. Existing native slots keep their
meanings; new body ranks have their own slots. -/
public def HeadingLevel.element : HeadingLevel → String
  | .title => "titlepage"
  | .h1 => "heading1"
  | .h2 => "section"
  | .h3 => "subsection"
  | .h4 => "subsubsection"
  | .h5 => "heading5"
  | .h6 => "heading6"

/-- Every heading that can enter the IR has an artifact-defined rank. -/
public theorem headingRank_between (level : HeadingLevel) :
    1 ≤ headingRank level ∧ headingRank level ≤ 6 := by
  cases level <;> simp [headingRank]

/-- Reading back a body rank retains its identity, including body h1. -/
public theorem HeadingLevel.ofRank?_exact (level : HeadingLevel)
    (h : level ≠ .title) :
    ofRank? (headingRank level) = some level := by
  cases level <;> simp_all [ofRank?, headingRank]

/-- No two distinct body levels collapse to one artifact rank. -/
public theorem headingRank_inj (a b : HeadingLevel)
    (ha : a ≠ .title) (hb : b ≠ .title)
    (h : headingRank a = headingRank b) : a = b := by
  have he := congrArg HeadingLevel.ofRank? h
  rw [HeadingLevel.ofRank?_exact a ha, HeadingLevel.ofRank?_exact b hb] at he
  exact Option.some.inj he

end LeanTex.Core.Ir
