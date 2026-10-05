import LeanTex.Core.Binary

namespace LeanTex.Core.Pdf.Xref

/-! The writer's cross-reference fields, ISO 32000-2 §7.5.8.3, `/W [1 4 2]`.
The field widths are the file format, not a claim that arbitrary natural
numbers fit. These laws are artifact-specific byte bookkeeping. -/

/-- One cross-reference row: type, byte offset or object-stream number,
generation or index within the object stream. -/
def row (kind : UInt8) (first second : Nat) : ByteArray :=
  let kindBytes := Binary.natBE 1 kind.toNat
  let firstBytes := Binary.natBE 4 first
  let secondBytes := Binary.natBE 2 second
  kindBytes ++ firstBytes ++ secondBytes

@[simp] theorem row_size_exact (kind : UInt8) (first second : Nat) :
    (row kind first second).size = 7 := by
  simp [row]

/-- Every field reads back at its declared offset, inside any surrounding
file, provided the two integer fields are representable. -/
theorem row_fields_exact (kind : UInt8) (first second : Nat)
    (hfirst : first < 256 ^ 4) (hsecond : second < 256 ^ 2)
    (pre post : ByteArray) :
    Binary.readNatBE 1 (pre ++ row kind first second ++ post) pre.size =
      some kind.toNat ∧
    Binary.readNatBE 4 (pre ++ row kind first second ++ post) (pre.size + 1) =
      some first ∧
    Binary.readNatBE 2 (pre ++ row kind first second ++ post) (pre.size + 5) =
      some second := by
  constructor
  · simpa only [row, ByteArray.append_assoc] using
      Binary.readNatBE_natBE_id 1 kind.toNat kind.toNat_lt_size pre
        (Binary.natBE 4 first ++ Binary.natBE 2 second ++ post)
  constructor
  · simpa only [row, ByteArray.append_assoc, ByteArray.size_append,
      Binary.natBE_size] using
      Binary.readNatBE_natBE_id 4 first hfirst
        (pre ++ Binary.natBE 1 kind.toNat) (Binary.natBE 2 second ++ post)
  · simpa only [row, ByteArray.append_assoc, ByteArray.size_append,
      Binary.natBE_size, Nat.add_assoc] using
      Binary.readNatBE_natBE_id 2 second hsecond
        (pre ++ Binary.natBE 1 kind.toNat ++ Binary.natBE 4 first) post

/-- The field factorization preserves the writer's existing seven bytes,
including truncation outside the representable domain. -/
theorem row_bytes_exact (kind : UInt8) (first second : Nat) :
    row kind first second =
      [kind, UInt8.ofNat (first / 16777216), UInt8.ofNat (first / 65536 % 256),
        UInt8.ofNat (first / 256 % 256), UInt8.ofNat (first % 256),
        UInt8.ofNat (second / 256 % 256), UInt8.ofNat (second % 256)].toByteArray := by
  simp only [row, Binary.natBE, UInt8.ofNat_toNat, Nat.div_div_eq_div_mul]
  simp only [show 256 * 256 = 65536 from rfl,
    show 65536 * 256 = 16777216 from rfl]
  simp only [show 256 = 2 ^ 8 from rfl, UInt8.ofNat_mod_size]
  rfl

end LeanTex.Core.Pdf.Xref
