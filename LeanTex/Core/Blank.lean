module

namespace LeanTex.Core

/-- **A character that shows nothing a reader can read**: Unicode
`White_Space` (PropList.txt — 0009–000D, 0020, 0085, 00A0, 1680, 2000–200A,
2028, 2029, 202F, 205F, 3000), the C0 and C1 controls, and the
`Default_Ignorable_Code_Point` characters (DerivedCoreProperties.txt — the
soft hyphen, the joiners and marks of 200B–200F and 202A–202E, 2060–206F,
the variation selectors, the byte order mark, the tag characters), which a
renderer draws as nothing. An accessible name of nothing else is empty to a
reader however many characters it holds: a stricter test than axe's
`summary-name` rule, which trims the spaces among them alone. -/
@[expose] public def blankChar (c : Char) : Bool :=
  let n := c.toNat
  n ≤ 0x20 || (0x7F ≤ n && n ≤ 0xA0) || n == 0xAD || n == 0x34F || n == 0x61C ||
  n == 0x115F || n == 0x1160 || n == 0x1680 || n == 0x17B4 || n == 0x17B5 ||
  (0x180B ≤ n && n ≤ 0x180F) || (0x2000 ≤ n && n ≤ 0x200F) ||
  (0x2028 ≤ n && n ≤ 0x202F) || (0x205F ≤ n && n ≤ 0x206F) || n == 0x3000 ||
  n == 0x3164 || (0xFE00 ≤ n && n ≤ 0xFE0F) || n == 0xFEFF || n == 0xFFA0 ||
  (0xFFF0 ≤ n && n ≤ 0xFFF8) || (0x1BCA0 ≤ n && n ≤ 0x1BCA3) ||
  (0x1D173 ≤ n && n ≤ 0x1D17A) || (0xE0000 ≤ n && n ≤ 0xE0FFF)

/-- Does a string hold a character a reader can read (`blankChar`)? -/
@[expose] public def holdsText (s : String) : Bool := s.toList.any (!blankChar ·)

end LeanTex.Core
