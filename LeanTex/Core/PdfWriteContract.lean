import LeanTex.Core.Pdf

namespace LeanTex.Core.Pdf

/-! Numeric domains for the PDF bytes this writer actually emits.
These bounds concern artifact storage, not the document IR or a viewer's
interpretation of font programs. No predicate below calls a PDF parser. -/

/-- The fixed `/W [1 4 2]` fields and this reader's decompression limit.
An object-stream index is zero-based, so 65536 compressed objects fit;
65537 do not. Outline items consume that same shared index space along
with the catalog, pages, fonts, metadata, and structure objects.

The byte offsets are measured on the actual serialized direct objects.
The two decoded payload bounds cover the xref and the object stream that
the structural reader must inflate. They do not certify cached page
operators, copied image streams, font program validity, or viewer output. -/
def WritePlan.WithinBounds (p : WritePlan) : Prop :=
  p.compressed.length ≤ 256 ^ 2 ∧
  p.serialized.1.size < 256 ^ 4 ∧
  p.table.objStmId < 256 ^ 4 ∧
  p.table.size < 256 ^ 4 ∧
  (objectStream p.compressed).bytes.size ≤ PdfRead.maxDecoded ∧
  (Xref.encode p.entries).size ≤ PdfRead.maxDecoded

instance (p : WritePlan) : Decidable p.WithinBounds :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A checked boundary for the numeric PDF format limits. The unchecked
`write` remains the byte-producing function whose composition is proved;
callers can reject an out-of-domain plan before accepting its bytes. -/
def WritePlan.checked (p : WritePlan) : Except String ByteArray :=
  if p.WithinBounds then .ok p.bytes
  else .error "PDF exceeds its object-index, offset, or decoded-stream limit"

theorem WritePlan.checked_exact (p : WritePlan) (b : ByteArray) :
    p.checked = .ok b ↔ p.WithinBounds ∧ p.bytes = b := by
  simp only [checked]
  split
  · simp_all
  · simp_all

/-- The checked domain proves all encoded field bounds on the actual
writer entries, including every offset from the serializer. -/
theorem WritePlan.entries_fits (p : WritePlan) (h : p.WithinBounds) :
    ∀ e ∈ p.entries, e.Fits :=
  writerXrefEntries_fits p.table p.head p.rows p.compressed h.2.1 h.2.2.1 h.1

/-- Oversized object streams are refused independently of compression
ratio or successful parsing of some wrapped entries. -/
theorem WritePlan.compressed_limit_gated (p : WritePlan) (b : ByteArray)
    (h : p.checked = .ok b) : p.compressed.length ≤ 65536 := by
  exact ((p.checked_exact b).mp h).1.1

/-- Each selected xref row retains all its fields at its actual byte
position. This theorem composes the numeric check with the real encoder;
the reader's stream traversal is a separate remaining proof. -/
theorem WritePlan.xref_fields_exact (p : WritePlan) (h : p.WithinBounds)
    (i : Nat) (e : Xref.Entry) (hi : p.entries[i]? = some e) :
    Binary.readNatBE 1 (Xref.encode p.entries) (7 * i) = some e.fields.1.toNat ∧
    Binary.readNatBE 4 (Xref.encode p.entries) (7 * i + 1) = some e.fields.2.1 ∧
    Binary.readNatBE 2 (Xref.encode p.entries) (7 * i + 5) = some e.fields.2.2 := by
  simpa only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    Nat.zero_add] using
    Xref.encode_index_fields_exact p.entries i e hi
      (p.entries_fits h e (Array.mem_of_getElem? hi)) ByteArray.empty ByteArray.empty

end LeanTex.Core.Pdf
