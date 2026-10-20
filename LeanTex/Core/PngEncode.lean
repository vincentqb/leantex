module

import LeanTex.Core.Flate

/-! PNG writing [PNG] from sample rows or a zlib stream of already-filtered rows.

Bibliography: [references.bib](../../docs/references.bib) -/

namespace LeanTex.Core.PngEncode

/-- The CRC-32 lookup table (ISO/IEC 15948 Annex D): polynomial
`0xEDB88320`, reflected. -/
private def crcTable : Array UInt32 := (Array.range 256).map fun (n : Nat) => Id.run do
  let mut c : UInt32 := n.toUInt32
  for _ in [0:8] do
    c := if c &&& 1 != 0 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
  return c

/-- The CRC-32 of a byte run, as PNG computes it over a chunk's type and
data. -/
public def crc32 (b : ByteArray) : UInt32 := Id.run do
  let t := crcTable
  let mut c : UInt32 := 0xFFFFFFFF
  for x in b do
    c := (t[((c ^^^ x.toUInt32) &&& 0xFF).toNat]?.getD 0) ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

/-- A four-byte big-endian number. -/
public def be32 (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 256 % 256),
    UInt8.ofNat (n % 256)]⟩

/-- The four bytes of a chunk type this module writes (ISO/IEC 15948 §5.4). -/
public def tagIHDR : ByteArray := ⟨#[73, 72, 68, 82]⟩
public def tagPLTE : ByteArray := ⟨#[80, 76, 84, 69]⟩
public def tagIDAT : ByteArray := ⟨#[73, 68, 65, 84]⟩
public def tagIEND : ByteArray := ⟨#[73, 69, 78, 68]⟩

/-- One chunk: its length, type, data and the CRC over type and data. -/
public def chunk (ty : ByteArray) (data : ByteArray) : ByteArray :=
  let body := ty ++ data
  be32 data.size ++ body ++ be32 (crc32 body).toNat

/-- The PNG signature. -/
public def signature : ByteArray := ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩

/-- An image's header: its size in pixels, bit depth and colour type (0
grey, 2 truecolour, 3 indexed, 4 grey with alpha, 6 truecolour with
alpha). -/
public structure Header where
  width : Nat
  height : Nat
  bitDepth : Nat
  colorType : Nat
  deriving Repr, BEq, Inhabited

/-- A header the colour-type table admits without a palette (§11.2.2 Table 11.1), its size in
32 bits. -/
@[expose] public def Header.Plain (h : Header) : Prop :=
  0 < h.width ∧ h.width < 2 ^ 32 ∧ 0 < h.height ∧ h.height < 2 ^ 32 ∧
    ((h.colorType = 0 ∧ h.bitDepth ∈ [1, 2, 4, 8, 16]) ∨
      ((h.colorType = 2 ∨ h.colorType = 4 ∨ h.colorType = 6) ∧ h.bitDepth ∈ [8, 16]))

/-- The `IHDR` chunk's data: no interlace, the one compression and filter
method PNG defines. -/
public def ihdr (h : Header) : ByteArray :=
  be32 h.width ++ be32 h.height ++ ⟨#[UInt8.ofNat h.bitDepth, UInt8.ofNat h.colorType, 0, 0, 0]⟩

/-- A PNG from a zlib stream of filtered rows, the stream as the one `IDAT`; `palette` is an
indexed image's `PLTE`. -/
public def encodeIdat (h : Header) (zlib : ByteArray) (palette : Option ByteArray := none) : ByteArray :=
  signature ++ chunk tagIHDR (ihdr h) ++
    (match palette with
     | some p => chunk tagPLTE p
     | none => ByteArray.empty) ++
    chunk tagIDAT zlib ++ chunk tagIEND ByteArray.empty

/-- The samples per pixel of a colour type. -/
public def channels : Nat → Nat
  | 0 => 1
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 6 => 4
  | _ => 1

/-- One row's bytes at a bit depth. -/
public def rowBytes (h : Header) : Nat := (h.width * channels h.colorType * h.bitDepth + 7) / 8

/-- A PNG from rows of samples, `rowBytes h` bytes each, top first, each behind filter byte 0. -/
public def encode (h : Header) (rows : ByteArray) (palette : Option ByteArray := none) : ByteArray :=
  let rb := rowBytes h
  let filtered := Id.run do
    let mut out := ByteArray.emptyWithCapacity ((rb + 1) * h.height)
    for r in [0:h.height] do
      out := out.push 0
      out := out ++ rows.extract (r * rb) (r * rb + rb)
    return out
  encodeIdat h (Flate.deflate filtered) palette

end LeanTex.Core.PngEncode
