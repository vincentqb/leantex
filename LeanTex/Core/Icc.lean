module

public import Init.Data.ByteArray.Basic

namespace LeanTex.Core.Icc

/-! An ICC profile's header and description ([ICC1] §7.2, §9.2.41), read from its bytes. -/

/-- The header fields a PDF output intent is judged by. -/
public structure Header where
  /-- The major and minor version, `(4, 2)` for 4.2. -/
  version : Nat × Nat
  /-- The profile class signature, `prtr` for an output device. -/
  deviceClass : String
  /-- The data colour space signature, `CMYK`, `RGB ` or `GRAY`. -/
  colorSpace : String
  deriving Repr, BEq, Inhabited

private def u8 (b : ByteArray) (i : Nat) : Nat := (b[i]?.map (·.toNat)).getD 0

private def u32 (b : ByteArray) (i : Nat) : Nat :=
  ((u8 b i * 256 + u8 b (i + 1)) * 256 + u8 b (i + 2)) * 256 + u8 b (i + 3)

private def sig (b : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat (u8 b (i + k)))

/-- The header of a well-formed profile: its size field the file's length and its `acsp` mark. -/
public def header? (b : ByteArray) : Option Header :=
  if b.size < 132 || u32 b 0 != b.size || sig b 36 != "acsp" then none
  else some { version := (u8 b 8, u8 b 9 / 16), deviceClass := sig b 12, colorSpace := sig b 16 }

/-- The channel count of a data colour space a PDF output intent may name. -/
public def components : String → Option Nat
  | "GRAY" => some 1
  | "RGB " => some 3
  | "CMYK" => some 4
  | _ => none

/-- The tag table's `(offset, size)` for a tag signature. -/
private def tag? (b : ByteArray) (name : String) : Option (Nat × Nat) :=
  let n := u32 b 128
  ((List.range (min n ((b.size - 132) / 12))).find? fun k => sig b (132 + 12 * k) == name).map
    fun k => (u32 b (136 + 12 * k), u32 b (140 + 12 * k))

/-- A `desc` tag's text: v2's textDescriptionType ASCII, or v4's first multiLocalizedUnicode record. -/
public def description? (b : ByteArray) : Option String := do
  let (off, size) ← tag? b "desc"
  guard (off + size ≤ b.size ∧ 12 ≤ size)
  match sig b off with
  | "desc" =>
    let n := u32 b (off + 8)
    guard (off + 12 + n ≤ b.size)
    let cs := ((List.range n).map fun k => u8 b (off + 12 + k)).takeWhile (· != 0)
    return String.ofList (cs.map Char.ofNat)
  | "mluc" =>
    guard (u32 b (off + 8) ≠ 0)
    let len := u32 b (off + 20)
    let start := off + u32 b (off + 24)
    guard (start + len ≤ b.size)
    let units := (List.range (len / 2)).map fun k =>
      u8 b (start + 2 * k) * 256 + u8 b (start + 2 * k + 1)
    return String.ofList ((units.takeWhile (· != 0)).map Char.ofNat)
  | _ => none

end LeanTex.Core.Icc
