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

/-- The three row types of §7.5.8.3. The second field of a compressed
entry is an index, not an object number or a byte offset. -/
inductive Entry where
  | free (next generation : Nat)
  | direct (offset generation : Nat)
  | compressed (stream index : Nat)
  deriving Repr, BEq

def Entry.fields : Entry → UInt8 × Nat × Nat
  | .free next gen => (0, next, gen)
  | .direct off gen => (1, off, gen)
  | .compressed stm idx => (2, stm, idx)

/-- Precisely the two representability requirements of `/W [1 4 2]`.
This is a numeric input domain, independent of encoding or decoding. -/
def Entry.Fits (e : Entry) : Prop :=
  e.fields.2.1 < 256 ^ 4 ∧ e.fields.2.2 < 256 ^ 2

def Entry.bytes (e : Entry) : ByteArray :=
  row e.fields.1 e.fields.2.1 e.fields.2.2

@[simp] theorem Entry.bytes_size (e : Entry) : e.bytes.size = 7 :=
  row_size_exact _ _ _

/-- The actual writer's accumulator for its cross-reference payload. -/
def encodeList (out : ByteArray) : List Entry → ByteArray
  | [] => out
  | e :: es => encodeList (out ++ e.bytes) es

def encode (es : Array Entry) : ByteArray :=
  encodeList ByteArray.empty es.toList

theorem encodeList_bytes (out : ByteArray) (es : List Entry) :
    encodeList out es = out ++ encodeList ByteArray.empty es := by
  induction es generalizing out with
  | nil => simp [encodeList]
  | cons e es ih =>
    simp only [encodeList]
    rw [ih (out ++ e.bytes), ih (ByteArray.empty ++ e.bytes)]
    simp [ByteArray.append_assoc]

theorem encodeList_append (out : ByteArray) (xs ys : List Entry) :
    encodeList out (xs ++ ys) = encodeList (encodeList out xs) ys := by
  induction xs generalizing out with
  | nil => rfl
  | cons e es ih => exact ih _

theorem encodeList_size (out : ByteArray) (es : List Entry) :
    (encodeList out es).size = out.size + 7 * es.length := by
  induction es generalizing out with
  | nil => simp [encodeList]
  | cons e es ih =>
    simp only [encodeList, ih, ByteArray.size_append, Entry.bytes_size, List.length_cons]
    omega

@[simp] theorem encode_size_exact (es : Array Entry) :
    (encode es).size = 7 * es.size := by
  simp [encode, encodeList_size]

/-- All three fields of any row in the writer's payload, at the byte
position determined by its index. Prefix and suffix bytes are arbitrary.
Only this row needs to fit; nothing is assumed about the encoder. -/
theorem encode_entry_fields_exact (before after : Array Entry) (e : Entry)
    (he : e.Fits) (pre post : ByteArray) :
    let data := pre ++ encode (before ++ #[e] ++ after) ++ post
    let pos := pre.size + 7 * before.size
    Binary.readNatBE 1 data pos = some e.fields.1.toNat ∧
    Binary.readNatBE 4 data (pos + 1) = some e.fields.2.1 ∧
    Binary.readNatBE 2 data (pos + 5) = some e.fields.2.2 := by
  have hbytes :
      encode (before ++ #[e] ++ after) = encode before ++ e.bytes ++ encode after := by
    simp only [encode, Array.toList_append,
      encodeList_append, encodeList]
    rw [encodeList_bytes]
  simpa only [hbytes, ByteArray.append_assoc, Entry.bytes, ByteArray.size_append,
    encode_size_exact, Nat.add_assoc] using
    row_fields_exact e.fields.1 e.fields.2.1 e.fields.2.2 he.1 he.2
      (pre ++ encode before) (encode after ++ post)

end LeanTex.Core.Pdf.Xref
