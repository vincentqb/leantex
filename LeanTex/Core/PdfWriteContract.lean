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

/-- Typed numeric refusals, carrying the observed count or byte size.
The CLI translates these values to its diagnostic registry. Core does
not format diagnostics or decide publication policy. -/
inductive WriteError where
  | objectIndex (count : Nat)
  | byteOffset (bytes : Nat)
  | objectNumber (number : Nat)
  | tableSize (count : Nat)
  | objectStreamSize (bytes : Nat)
  | xrefStreamSize (bytes : Nat)
  deriving BEq, Repr

/-- Check cheap allocation bounds first, then measure once. The body and
xref payload used by the remaining checks are retained for emission.
Calling this function does not repeat serialization or compression to
evaluate `WithinBounds`; the theorem relates those independent spellings.
Accepted artifacts are held to this boundary when their publisher uses
only this function's successful result. -/
def WritePlan.checked (p : WritePlan) : Except WriteError ByteArray :=
  if p.compressed.length ≤ 256 ^ 2 then
    if p.table.objStmId < 256 ^ 4 then
      if p.table.size < 256 ^ 4 then
        let m := p.measure
        if m.body.size < 256 ^ 4 then
          if m.objectPayloadSize ≤ PdfRead.maxDecoded then
            if m.xrefPayload.size ≤ PdfRead.maxDecoded then
              .ok (m.bytes p.table)
            else .error (.xrefStreamSize m.xrefPayload.size)
          else .error (.objectStreamSize m.objectPayloadSize)
        else .error (.byteOffset m.body.size)
      else .error (.tableSize p.table.size)
    else .error (.objectNumber p.table.objStmId)
  else .error (.objectIndex p.compressed.length)

theorem WritePlan.checked_exact (p : WritePlan) (b : ByteArray) :
    p.checked = .ok b ↔ p.WithinBounds ∧ p.bytes = b := by
  unfold checked
  split <;> rename_i hc
  · split <;> rename_i ho
    · split <;> rename_i hs
      · dsimp only
        split <;> rename_i hb
        · split <;> rename_i hp
          · split <;> rename_i hx
            · simp_all [WithinBounds, measure_body_exact, measure_xref_exact,
                measure_object_size_exact, WritePlan.bytes]
            · simp_all [WithinBounds, measure_xref_exact]; omega
          · simp_all [WithinBounds, measure_object_size_exact]; omega
        · simp_all [WithinBounds, measure_body_exact]; omega
      · simp_all [WithinBounds]; omega
    · simp_all [WithinBounds]; omega
  · simp_all [WithinBounds]; omega

/-- Every refusal falsifies a numeric premise of the writer contract. -/
theorem WritePlan.checked_error_gated (p : WritePlan) (e : WriteError)
    (h : p.checked = .error e) : ¬ p.WithinBounds := by
  intro hb
  have he := (p.checked_exact p.bytes).2 ⟨hb, rfl⟩
  rw [h] at he
  contradiction

/-- The producer boundary for positioned pages. It takes the same cache
inputs as `write`; callers publish its successful bytes directly and
translate `WriteError` to a typed diagnostic on refusal. -/
def writeChecked (geom : Layout.Geom) (fs : Font.FontSet) (pages : Array Layout.PageOut)
    (info : Ir.Meta := {}) (imgs : Image.Store := {})
    (outline : Array Layout.OutlineEntry := #[])
    (streams : Array (ByteArray × Option ByteArray) := #[])
    (tree : Struct.Tree := ⟨#[]⟩) (ops : Array (Array ContentOp) := #[])
    (programs : Array (ByteArray × Bool) := #[]) : Except WriteError ByteArray :=
  (prepare geom fs pages info imgs outline streams tree ops programs).checked

/-- Success checks the numeric domain and returns exactly the actual
writer's bytes for every input and cache argument. It does not assume
successful parsing, decompression, or font validity. -/
theorem writeChecked_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry) (streams : Array (ByteArray × Option ByteArray))
    (tree : Struct.Tree) (ops : Array (Array ContentOp))
    (programs : Array (ByteArray × Bool)) (b : ByteArray) :
    writeChecked geom fs pages info imgs outline streams tree ops programs = .ok b ↔
      (prepare geom fs pages info imgs outline streams tree ops programs).WithinBounds ∧
      write geom fs pages info imgs outline streams tree ops programs = b := by
  exact WritePlan.checked_exact _ b

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

/-- The actual subsection reader recovers every location encoded in a
checked plan's retained xref payload. Stream traversal and inflation are
still required to connect this payload reading to the complete file. -/
theorem WritePlan.xref_locations_exact (p : WritePlan) (h : p.WithinBounds)
    (x0 : PdfRead.Xref) (hx : x0.locs = {}) (k : Nat) :
    (PdfRead.readXrefSubsection p.measure.xrefPayload 1 4 2 0 p.entries.size 0 x0).1.locs[k]? =
      p.entries[k]?.bind PdfRead.xrefEntryLocation := by
  rw [p.measure_xref_exact, PdfRead.readXrefSubsection_locations_exact p.entries
    (p.entries_fits h) p.entries.size (Nat.le_refl _) x0 hx]
  split
  · rfl
  · rename_i hk
    simp [show p.entries.size ≤ k by omega]

/-- The complete emitted file's footer recovers the exact byte position
where the writer put its xref object. This includes the actual backward
scan and decimal parsing, before xref stream traversal. -/
theorem WritePlan.startxref_exact (p : WritePlan) (h : p.WithinBounds) :
    PdfRead.readStartxref p.bytes = .ok p.measure.body.size := by
  unfold WritePlan.bytes WriteMeasurement.bytes
  apply PdfRead.readStartxref_footer_exact
  simpa only [p.measure_body_exact] using h.2.1

end LeanTex.Core.Pdf
