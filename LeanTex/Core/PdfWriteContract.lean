module

public import LeanTex.Core.Pdf
public import LeanTex.Core.PdfEncoding
public import LeanTex.Core.PdfFooter
import all LeanTex.Core.Pdf

namespace LeanTex.Core.Pdf

/-! Checked storage and source-spelling domains for the actual writer.
These bounds concern artifact bytes, not a viewer's interpretation of
font programs. No predicate below calls a PDF parser. -/

/-- The storage the structural reader needs, and nothing the format
itself would refuse: offsets that fit 64 bits, so the `startxref` decimal
lies in the reader's search window, and decoded object and xref streams
inside the reader's decompression limit. The xref field widths are not a
bound — the writer sizes them to the rows (`entries_fits`) — and every
object stream holds at most `objStmCapacity` objects whatever the
document's size (`chunks_between`).

The byte offsets are measured on the actual serialized direct objects.
The decoded payload bounds cover the xref and the object streams that
the structural reader must inflate. They do not certify cached page
operators, copied image streams, font program validity, or viewer output. -/
@[expose] public def WritePlan.WithinBounds (p : WritePlan) : Prop :=
  p.serialized.1.size < 2 ^ 64 ∧
  (∀ c ∈ p.chunks, (objectStream c).bytes.size ≤ PdfRead.maxDecoded) ∧
  (Xref.encode p.widths p.entries).size ≤ PdfRead.maxDecoded

public instance (p : WritePlan) : Decidable p.WithinBounds := by
  unfold WritePlan.WithinBounds
  infer_instance

/-- Every compressed source object uses the encoder's supported grammar.
This finite check inspects names, numbers, strings, and nested containers
before serialization; it never asks the reader for an answer. -/
@[expose] public def WritePlan.Encodable (p : WritePlan) : Prop :=
  p.compressed.all (fun e => e.2.encodable) = true

public instance (p : WritePlan) : Decidable p.Encodable := by
  unfold WritePlan.Encodable
  infer_instance

/-- The complete checked source domain: storage and decoded sizes, plus
the grammar of every object placed in an object stream. Native
direct-stream dictionaries have their own unconditional spelling proofs;
imported resource graphs retain their separate acceptance requirements. -/
@[expose] public def WritePlan.WithinDomain (p : WritePlan) : Prop :=
  p.WithinBounds ∧ p.Encodable

public instance (p : WritePlan) : Decidable p.WithinDomain := by
  unfold WritePlan.WithinDomain
  infer_instance

public theorem WritePlan.encodable_contract (p : WritePlan) (h : p.Encodable) :
    ∀ e ∈ p.compressed, e.2.Representable := by
  intro e he
  exact e.2.encodable_contract ((List.all_eq_true.mp h) e he)

private theorem WritePlan.find_unencodable_none (p : WritePlan) :
    p.compressed.find? (fun e => !e.2.encodable) = none ↔ p.Encodable := by
  simp [Encodable, List.find?_eq_none]

/-- Typed refusals, carrying the observed byte size or object id. The CLI
translates these values to its diagnostic registry. Core does not format
diagnostics or decide publication policy. -/
public inductive WriteError where
  | byteOffset (bytes : Nat)
  | objectStreamSize (bytes : Nat)
  | xrefStreamSize (bytes : Nat)
  | objectSpelling (id : Nat)
  | inkRaster (page : Nat)
  deriving BEq, Repr

/-- Check source spellings first, then measure once. The body and xref
payload used by the remaining checks are retained for emission. Calling
this function does not repeat serialization or compression to evaluate
`WithinDomain`; the theorem relates those independent spellings.
Accepted artifacts are held to this boundary when their publisher uses
only this function's successful result. -/
public def WritePlan.checked (p : WritePlan) : Except WriteError ByteArray :=
  match p.compressed.find? (fun e => !e.2.encodable) with
  | some e => .error (.objectSpelling e.1)
  | none =>
    let m := p.measure
    if m.body.size < 2 ^ 64 then
      if m.objectPayloadSize ≤ PdfRead.maxDecoded then
        if m.xrefPayload.size ≤ PdfRead.maxDecoded then
          .ok (m.bytes p.table)
        else .error (.xrefStreamSize m.xrefPayload.size)
      else .error (.objectStreamSize m.objectPayloadSize)
    else .error (.byteOffset m.body.size)

public theorem WritePlan.checked_exact (p : WritePlan) (b : ByteArray) :
    p.checked = .ok b ↔ p.WithinDomain ∧ p.bytes = b := by
  unfold checked
  cases he : p.compressed.find? (fun e => !e.2.encodable) with
  | some e =>
    have hn : ¬ p.Encodable := by
      intro h
      have hh := p.find_unencodable_none.mpr h
      rw [he] at hh
      contradiction
    simp [WithinDomain, hn]
  | none =>
    have hspell := p.find_unencodable_none.mp he
    have hobj := p.measure_object_size_exact PdfRead.maxDecoded
    dsimp only
    split <;> rename_i hb
    · split <;> rename_i hp
      · split <;> rename_i hx
        · simp_all [WithinDomain, WithinBounds, measure_body_exact, measure_xref_exact,
            WritePlan.bytes]
        · simp_all [WithinDomain, WithinBounds, measure_xref_exact]
          intro _ h
          omega
      · simp_all [WithinDomain, WithinBounds]
        intro _ hall
        obtain ⟨c, hc, hlt⟩ := hobj
        have := hall c hc
        omega
    · simp_all [WithinDomain, WithinBounds, measure_body_exact]
      intro h
      omega

/-- Every refusal falsifies a storage or source-grammar premise. -/
public theorem WritePlan.checked_error_gated (p : WritePlan) (e : WriteError)
    (h : p.checked = .error e) : ¬ p.WithinDomain := by
  intro hb
  have he := (p.checked_exact p.bytes).2 ⟨hb, rfl⟩
  rw [h] at he
  contradiction

/-- The producer boundary for positioned pages. It takes the same cache
inputs as `write`; callers publish its successful bytes directly and
translate `WriteError` to a typed diagnostic on refusal. -/
public def writeChecked (geom : Layout.Geom) (fs : Font.FontSet) (pages : Array Layout.PageOut)
    (info : Ir.Meta := {}) (imgs : Image.Store := {})
    (outline : Array Layout.OutlineEntry := #[])
    (streams : Array (ByteArray × Option ByteArray) := #[])
    (tree : Struct.Tree := ⟨#[]⟩) (ops : Array (Array ContentOp) := #[])
    (programs : Array (ByteArray × Bool) := #[]) : Except WriteError ByteArray :=
  -- premise: ofPictureIn_imageFree_exact — the ink Layout places is a lowered
  -- picture's, which paints no raster; the refusal guards every other caller.
  match inkRasterPage? pages with
  | some i => .error (.inkRaster i)
  | none => (prepare geom fs pages info imgs outline streams tree ops programs).checked

/-- Success checks the source domain — no page's ink paints a raster the
writer has no image table for, the storage bounds, the spellings — and
returns exactly the actual writer's bytes for every input and cache
argument. It does not assume successful parsing, decompression, or font
validity. -/
public theorem writeChecked_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry) (streams : Array (ByteArray × Option ByteArray))
    (tree : Struct.Tree) (ops : Array (Array ContentOp))
    (programs : Array (ByteArray × Bool)) (b : ByteArray) :
    writeChecked geom fs pages info imgs outline streams tree ops programs = .ok b ↔
      inkRasterPage? pages = none ∧
      (prepare geom fs pages info imgs outline streams tree ops programs).WithinDomain ∧
      write geom fs pages info imgs outline streams tree ops programs = b := by
  unfold writeChecked
  cases h : inkRasterPage? pages with
  | some i => simp
  | none =>
    simpa [write] using
      WritePlan.checked_exact (prepare geom fs pages info imgs outline streams tree ops programs) b

/-- Every row of the actual xref payload fits the widths the plan
declares, with no premise: the widths are read off these rows. -/
public theorem WritePlan.entries_fits (p : WritePlan) :
    ∀ e ∈ p.entries, e.Fits p.widths :=
  writerXrefEntries_fits _ _ _ _

/-- Every object stream the plan writes holds at least one and at most
`objStmCapacity` objects, for every document: reading one compressed
object inflates one such stream, never the whole file's objects. -/
public theorem WritePlan.chunks_between (p : WritePlan) :
    ∀ c ∈ p.chunks, 0 < c.length ∧ c.length ≤ objStmCapacity :=
  objStmChunks_between _

/-- Each selected xref row retains all its fields at its actual byte
position, `p.widths.row` bytes per id. This theorem composes the field
widths with the real encoder; the complete file's traversal is composed
in `WritePlan.readXref_exact`. -/
public theorem WritePlan.xref_fields_exact (p : WritePlan)
    (i : Nat) (e : Xref.Entry) (hi : p.entries[i]? = some e) :
    Binary.readNatBE 1 (Xref.encode p.widths p.entries) (p.widths.row * i) =
      some e.fields.1.toNat ∧
    Binary.readNatBE p.widths.first (Xref.encode p.widths p.entries) (p.widths.row * i + 1) =
      some e.fields.2.1 ∧
    Binary.readNatBE p.widths.second (Xref.encode p.widths p.entries)
      (p.widths.row * i + 1 + p.widths.first) = some e.fields.2.2 := by
  simpa only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    Nat.zero_add] using
    Xref.encode_index_fields_exact p.widths p.entries i e hi
      (p.entries_fits e (Array.mem_of_getElem? hi)) ByteArray.empty ByteArray.empty

/-- The actual subsection reader recovers every location encoded in a
plan's retained xref payload, at the widths the plan declares.
`WritePlan.readXref_exact` composes this reading with the actual footer,
object parser, and inflation. -/
public theorem WritePlan.xref_locations_exact (p : WritePlan)
    (x0 : PdfRead.Xref) (hx : x0.locs = {}) (k : Nat) :
    (PdfRead.readXrefSubsection p.measure.xrefPayload 1 p.widths.first p.widths.second
      0 p.entries.size 0 x0).1.locs[k]? =
      p.entries[k]?.bind PdfRead.xrefEntryLocation := by
  rw [p.measure_xref_exact, PdfRead.readXrefSubsection_locations_exact p.widths p.entries
    p.entries_fits p.entries.size (Nat.le_refl _) x0 hx]
  split
  · rfl
  · rename_i hk
    simp [show p.entries.size ≤ k by omega]

/-- The complete emitted file's footer recovers the exact byte position
where the writer put its xref object. This includes the actual backward
scan and decimal parsing, before xref stream traversal. -/
public theorem WritePlan.startxref_exact (p : WritePlan) (h : p.WithinBounds) :
    PdfRead.readStartxref p.bytes = .ok p.measure.body.size := by
  unfold WritePlan.bytes WriteMeasurement.bytes
  apply PdfRead.readStartxref_footer_exact
  simpa only [p.measure_body_exact] using h.1

end LeanTex.Core.Pdf
