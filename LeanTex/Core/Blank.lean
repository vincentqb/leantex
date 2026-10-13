module

namespace LeanTex.Core

/-- A character a reader cannot read: Unicode `White_Space`, the C0 and C1 controls, and the
`Default_Ignorable_Code_Point` characters. -/
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
