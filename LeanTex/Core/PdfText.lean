module

public import LeanTex.Core.PdfObj
public import LeanTex.Core.Hex
public import LeanTex.Core.Xml

namespace LeanTex.Core.PdfRead

/-! The strings the writer spells from author text: each a literal whose body escapes its
delimiters, or UTF-16BE hex, so it reads back as one string (`literal_representable`,
`textString_representable`). -/

/-- One byte of a literal string's body: a parenthesis or backslash escaped, a return as `\r`. -/
@[expose] public def literalByte (c : Nat) : List Nat :=
  if c == 40 || c == 41 || c == 92 then [92, c] else if c == 13 then [92, 114] else [c]

/-- Bytes as a literal string (§7.3.4.2). -/
@[expose] public def literalBytes (bs : List Nat) : List Nat :=
  40 :: bs.flatMap literalByte ++ [41]

/-- A character's UTF-16BE code units as upper-case hexadecimal digits. -/
@[expose] public def utf16Hex (c : Char) : String :=
  let n := c.toNat
  if n < 0x10000 then
    Hex.digits true 4 n
  else
    let v := n - 0x10000
    Hex.digits true 4 (0xD800 + v / 1024) ++ Hex.digits true 4 (0xDC00 + v % 1024)

/-- A text string's bytes (§7.9.2.2): ASCII as a literal, anything else as UTF-16BE hex after the
byte-order mark. -/
@[expose] public def textStringBytes (s : String) : List Nat :=
  if s.toList.all (·.toNat < 0x80) then literalBytes (s.toList.map Char.toNat)
  else 60 :: ("FEFF" ++ String.join (s.toList.map utf16Hex)).toList.map Char.toNat ++ [62]

/-- A byte list as a string object's verbatim bytes. -/
@[expose] public def strOf (bs : List Nat) : Obj := .str ⟨(bs.map Nat.toUInt8).toArray⟩

/-- A byte string, such as a URI (§7.9.2.4), as a literal. -/
@[expose] public def literal (bs : ByteArray) : Obj := strOf (literalBytes (bs.data.toList.map UInt8.toNat))

/-- A text string, such as the document's title, as one string object. -/
@[expose] public def textString (s : String) : Obj := strOf (textStringBytes s)

/-- One character of XMP character data: markup as an entity, a return as a reference that line-end
normalization keeps, a character XML does not admit dropped. -/
@[expose] public def xmpChar (c : Char) : List Char :=
  if c == '&' then "&amp;".toList
  else if c == '<' then "&lt;".toList
  else if c == '>' then "&gt;".toList
  else if c == '\r' then "&#13;".toList
  else if Xml.xmlChar c.toNat then [c]
  else []

/-- Text as XMP character data (`xmpText_admitted`). -/
@[expose] public def xmpText (s : String) : String := String.ofList (s.toList.flatMap xmpChar)

end LeanTex.Core.PdfRead
