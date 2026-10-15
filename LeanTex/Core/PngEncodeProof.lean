module

public import LeanTex.Core.PngEncode
public import LeanTex.Core.Image
import all LeanTex.Core.PngEncode
import all LeanTex.Core.Image

/-! `probe_encode_exact`: the image probe reads a file `encodeIdat` wrote as exactly the header and
stream it was written from; the CRCs are not read. -/

namespace LeanTex.Core.PngEncode

open LeanTex.Core

private theorem get?_append (a b : ByteArray) (i : Nat) :
    (a ++ b)[i]? = if i < a.size then a[i]? else b[i - a.size]? := by
  split
  · rename_i h
    rw [getElem?_pos (a ++ b) i (by simp; omega), getElem?_pos a i h, ByteArray.getElem_append_left h]
  · rename_i h
    by_cases h2 : i - a.size < b.size
    · rw [getElem?_pos (a ++ b) i (by simp; omega), getElem?_pos b _ h2,
        ByteArray.getElem_append_right (by omega)]
    · rw [getElem?_neg (a ++ b) i (by simp; omega), getElem?_neg b _ h2]

private theorem size_mk (l : List UInt8) : (ByteArray.mk l.toArray).size = l.length := by
  simp [ByteArray.size]

private theorem get?_mk (l : List UInt8) (i : Nat) : (ByteArray.mk l.toArray)[i]? = l[i]? := by
  by_cases h : i < l.length
  · rw [getElem?_pos (ByteArray.mk l.toArray) i (by simpa [size_mk] using h), List.getElem?_eq_getElem h]
    simp [ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg (ByteArray.mk l.toArray) i (by simpa [size_mk] using h),
      List.getElem?_eq_none (by omega)]

private theorem size_be32 (n : Nat) : (be32 n).size = 4 := rfl
private theorem size_signature : signature.size = 8 := rfl
private theorem size_tag_ihdr : tagIHDR.size = 4 := rfl
private theorem size_tag_idat : tagIDAT.size = 4 := rfl
private theorem size_tag_iend : tagIEND.size = 4 := rfl
private theorem size_ihdr (h : Header) : (ihdr h).size = 13 := rfl

private theorem sliceEq_reads (b : ByteArray) (i : Nat) (pat : List Nat) :
    Image.sliceEq b i pat = pat.zipIdx.all fun (v, k) => Image.u8? b (i + k) == some v := rfl

/-- A read of the written file at a fixed offset, by its layout. -/
local macro "png_read" : tactic => `(tactic| simp +arith +decide only [Image.u8?, Image.u16be?,
    Image.u32be?, sliceEq_reads, encodeIdat, chunk, get?_append, ByteArray.size_append, size_be32,
    size_signature, size_tag_ihdr, size_tag_idat, size_tag_iend, size_ihdr, ByteArray.size_empty, ihdr,
    Nat.reduceSub, ↓reduceIte, size_mk, get?_mk, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, be32, signature, Image.pngSig,
    tagIHDR, tagIDAT, tagIEND, List.zipIdx_cons, List.zipIdx_nil, List.all_cons, List.all_nil,
    Bool.and_true, Option.bind_some, bind, pure, UInt8.toNat_ofNat', Option.some.injEq, Nat.reducePow,
    Nat.add_sub_add_left, Nat.add_sub_cancel_left, Nat.sub_self])

private theorem forIn_three {ε β : Type} (n : Nat) (init : β) (f : Nat → β → Except ε (ForInStep β)) :
    forIn [:n + 3] init f = forIn (0 :: 1 :: 2 :: List.range' 3 n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size, List.range'_succ]

private theorem size_encodeIdat (h : Header) (z : ByteArray) :
    (encodeIdat h z).size = (z.size + 54) + 3 := by
  simp only [encodeIdat, chunk, ByteArray.size_append, size_be32, size_signature, size_tag_ihdr,
    size_tag_idat, size_tag_iend, size_ihdr, ByteArray.size_empty]
  omega

public theorem probe_encode_exact (h : Header) (z : ByteArray) (hh : h.Plain)
    (hz : 0 < z.size ∧ z.size < 2 ^ 32) :
    Image.probe (encodeIdat h z) =
      .ok { format := .png, pxW := h.width, pxH := h.height, bitDepth := h.bitDepth,
            colorType := h.colorType, iccIsZlib := true, payload := z } := by
  obtain ⟨hw0, hw, hh0, hh1, hc⟩ := hh
  have r0 : Image.sliceEq (encodeIdat h z) 0 Image.pngSig = true := by png_read
  have r8 : Image.u32be? (encodeIdat h z) 8 = some 13 := by png_read
  have r12 : Image.sliceEq (encodeIdat h z) 12 [73, 72, 68, 82] = true := by png_read
  have r16 : Image.u32be? (encodeIdat h z) 16 = some h.width := by png_read; omega
  have r20 : Image.u32be? (encodeIdat h z) 20 = some h.height := by png_read; omega
  have hd : h.bitDepth < 256 := by rcases hc with ⟨-, hd⟩ | ⟨-, hd⟩ <;> simp at hd <;> omega
  have ht : h.colorType < 256 := by rcases hc with ⟨hd, -⟩ | ⟨hd, -⟩ <;> omega
  have r24 : Image.u8? (encodeIdat h z) 24 = some h.bitDepth := by png_read; omega
  have r25 : Image.u8? (encodeIdat h z) 25 = some h.colorType := by png_read; omega
  have r28 : Image.u8? (encodeIdat h z) 28 = some 0 := by png_read
  have hwh : (h.width == 0 || h.height == 0) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
  have hmem : h.bitDepth ∈ [1, 2, 4, 8, 16] := by
    rcases hc with ⟨-, hd⟩ | ⟨-, hd⟩
    · exact hd
    · simp at hd ⊢; omega
  have hcont : [1, 2, 4, 8, 16].contains h.bitDepth = true := by simpa using hmem
  have hsp : ∃ space alpha, Image.pngSpace h.colorType = some (space, alpha) ∧
      (space == Image.Space.indexed) = false ∧
      (space == Image.Space.rgb && alpha.isNone && decide (h.bitDepth < 8)) = false ∧
      (alpha.isSome && decide (h.bitDepth < 8)) = false := by
    rcases hc with ⟨hc, _⟩ | ⟨hc, hd⟩
    · exact ⟨.gray, none, by simp [hc, Image.pngSpace], rfl, rfl, rfl⟩
    · simp at hd
      have h8 : decide (h.bitDepth < 8) = false := by simp; omega
      rcases hc with hc | hc | hc <;> rw [hc] <;> simp only [Image.pngSpace]
      · exact ⟨_, _, rfl, rfl, by rw [h8]; rfl, rfl⟩
      · exact ⟨_, _, rfl, rfl, rfl, by rw [h8]; rfl⟩
      · exact ⟨_, _, rfl, rfl, by rw [h8]; rfl, by rw [h8]; rfl⟩
  obtain ⟨space, alpha, hsp, hni, hrgb, halpha⟩ := hsp
  have q12 : Image.u8? (encodeIdat h z) 12 = some 73 := by png_read
  have s12d : Image.sliceEq (encodeIdat h z) 12 [73, 68, 65, 84] = false := by png_read
  have s12e : Image.sliceEq (encodeIdat h z) 12 [73, 69, 78, 68] = false := by png_read
  have q33 : Image.u32be? (encodeIdat h z) 33 = some z.size := by png_read; omega
  have q37 : Image.u8? (encodeIdat h z) 37 = some 73 := by png_read
  have s37d : Image.sliceEq (encodeIdat h z) 37 [73, 68, 65, 84] = true := by png_read
  have e41 : (encodeIdat h z).extract 41 (z.size + 41) = z := by
    have hsplit : encodeIdat h z = (signature ++ chunk tagIHDR (ihdr h) ++ be32 z.size ++ tagIDAT) ++
        (z ++ (be32 (crc32 (tagIDAT ++ z)).toNat ++ chunk tagIEND ByteArray.empty)) := by
      simp only [encodeIdat, chunk, ByteArray.append_assoc, ByteArray.append_empty]
    have hP : (signature ++ chunk tagIHDR (ihdr h) ++ be32 z.size ++ tagIDAT).size = 41 := by
      simp [chunk, ByteArray.size_append, size_be32, size_signature, size_tag_ihdr, size_tag_idat, size_ihdr]
    rw [hsplit, ByteArray.extract_append, hP, ByteArray.extract_eq_empty_iff.mpr (by omega),
      ByteArray.empty_append, Nat.sub_self, Nat.add_sub_cancel]
    exact ByteArray.extract_append_eq_left rfl
  have q45 : Image.u32be? (encodeIdat h z) (z.size + 45) = some 0 := by png_read
  have q49 : Image.u8? (encodeIdat h z) (z.size + 49) = some 73 := by png_read
  have s49d : Image.sliceEq (encodeIdat h z) (z.size + 49) [73, 68, 65, 84] = false := by png_read
  have s49e : Image.sliceEq (encodeIdat h z) (z.size + 49) [73, 69, 78, 68] = true := by png_read
  have hze : z.isEmpty = false := by
    simp only [ByteArray.isEmpty, beq_eq_false_iff_ne]; omega
  unfold Image.probe
  simp only [r0, ↓reduceIte]
  unfold Image.probePng
  simp only [r0, r8, r12, r16, r20, r24, r25, r28, hwh, hcont, hsp, hrgb, halpha, beq_self_eq_true,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true]
  rw [size_encodeIdat, forIn_three]
  simp only [List.forIn_cons]
  simp +arith only [r8, q12, s12d, s12e, q33, q37, s37d, e41, q45, q49, s49d, s49e, Nat.reduceAdd,
    Nat.reduceBEq, Bool.false_and, Bool.true_and, ↓reduceIte, Bool.false_eq_true, pure_bind,
    bind_pure_comp, ByteArray.empty_append]
  simp only [hze, hni, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

end LeanTex.Core.PngEncode
