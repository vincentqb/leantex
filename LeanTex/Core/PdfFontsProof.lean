module

public import LeanTex.Core.PdfPlanRecovery
public import LeanTex.Core.PdfPrepareFonts
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfWriteContract
import all LeanTex.Core.PdfCensus

namespace LeanTex.Core.Pdf
open PdfRead PdfCensus

/-! Font embedding in the actual serialized artifact. These contracts
follow the production reader from the file header through xref decoding,
object recovery, font dictionaries, and descriptor references. They
certify the structural embedding census, not the validity of an external
font program or the semantics of a viewer. -/

private theorem byte_get (b : ByteArray) (n : Nat) : b[n]? = b.data[n]? := rfl

private theorem WritePlan.head_suffix (p : WritePlan) :
    ∃ tail, p.bytes = p.head ++ tail := by
  obtain ⟨tail, ht⟩ := p.direct_suffix_exact
  rw [serialize, serializeList_bytes] at ht
  exact ⟨_, ht.trans (ByteArray.append_assoc ..)⟩

/-- Both supported PDF versions retain their header in the complete
emitted byte array, irrespective of the following object payloads. -/
public theorem prepare_header_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let b := (prepare geom fs pages info imgs outline streams tree ops programs).bytes
    (b[0]? == some 37 && b[1]? == some 80 && b[2]? == some 68 &&
      b[3]? == some 70) = true := by
  dsimp only
  obtain ⟨tail, ht⟩ :=
    (prepare geom fs pages info imgs outline streams tree ops programs).head_suffix
  rw [ht]
  have hh : (prepare geom fs pages info imgs outline streams tree ops programs).head =
      (if info.pdfVersion == some "1.7" then "%PDF-1.7\n%" else "%PDF-2.0\n%").toUTF8 ++
        ⟨#[0xE2, 0xE3, 0xCF, 0xD3]⟩ ++ "\n".toUTF8 := rfl
  rw [hh]
  split <;> simp only [byte_get, ByteArray.data_append, Array.getElem?_append,
    String.toUTF8_eq_toByteArray] <;> rfl

/-- The bounded replacement for the unrestricted font-embedding claim:
the actual writer's bytes pass the actual reader's font census.

The decidable premise checks source grammar, field widths, serialized
offsets, and decoded payload sizes. Parser correctness, compression,
allocation, object enumeration, and descriptor recovery are proved,
not premises. As in the original obligation, the image store is empty:
foreign PDF resource graphs have a separate acceptance boundary.
Page streams, structure trees, and cached font programs remain arbitrary. -/
public theorem write_fonts_embedded_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool))
    (h : (prepare geom fs pages info {} outline streams tree ops programs).WithinDomain) :
    (census (write geom fs pages info {} outline streams tree ops programs)).map
      (·.fontsEmbedded) = .ok true := by
  let p := prepare geom fs pages info {} outline streams tree ops programs
  have hn := prepare_native_exact geom fs pages info outline streams tree ops programs
  have ha := prepare_allocated_exact geom fs pages info {} outline streams tree ops programs
  obtain ⟨es, he, hf, href⟩ :=
    p.objects_recovered_exact h.1 ha (p.encodable_contract h.2) hn
      (prepare_compressed_ne_nil geom fs pages info {} outline streams tree ops programs)
  have hh := prepare_header_exact geom fs pages info {} outline streams tree ops programs
  change (p.bytes[0]? == some 37 && p.bytes[1]? == some 80 &&
    p.bytes[2]? == some 68 && p.bytes[3]? == some 70) = true at hh
  have hcensus := prepare_census_fonts_exact geom fs pages info {} outline streams tree ops
    programs (p.readback.trailer.getD (.dict #[])) es.val
    (by
      intro e hm
      have hmem := Array.mem_filter.mp hm
      exact hf e hmem.1 (beq_iff_eq.mp hmem.2))
    href
  change (census p.bytes).map (·.fontsEmbedded) = .ok true
  unfold census
  simp only [hh, ↓reduceIte, pure, bind, Except.bind, Except.pure,
    p.readback_exact h.1, he, Except.map, hcensus]

/-- Successful checked production establishes the complete font census
contract on the returned bytes. The publisher needs no separate storage
or grammar premise; the API that produced the artifact checked both. -/
public theorem writeChecked_fonts_embedded_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool))
    (b : ByteArray)
    (h : writeChecked geom fs pages info {} outline streams tree ops programs = .ok b) :
    (census b).map (·.fontsEmbedded) = .ok true := by
  obtain ⟨domain, hb⟩ := (writeChecked_exact geom fs pages info {} outline streams
    tree ops programs b).mp h
  rw [← hb]
  exact write_fonts_embedded_exact geom fs pages info outline streams tree ops programs domain

end LeanTex.Core.Pdf
