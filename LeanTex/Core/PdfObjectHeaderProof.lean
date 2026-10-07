module

public import LeanTex.Core.Pdf
public import LeanTex.Core.PdfRead
import LeanTex.Core.PdfNumber
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfRead

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! The object stream's decimal header records positions in its own
payload. The invariant below follows the reader's actual `forIn`, with
one pair consumed at every iteration. It does not assume a successful
reader result. -/

/-- The producer's payload positions, before any fixed-width encoding.
The increment is the exact rendered value size and its terminating LF. -/
public def objectStreamPositions (offset : Nat) : List (Nat × Obj) → List (Nat × Nat)
  | [] => []
  | (id,v)::xs => (id,offset) :: objectStreamPositions (offset+v.render.size+1) xs

@[simp] public theorem objectStreamPositions_length (offset : Nat) (xs : List (Nat × Obj)) :
    (objectStreamPositions offset xs).length = xs.length := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih => simp only [objectStreamPositions, List.length_cons, ih]

private def headerBytesFrom (acc : ByteArray) : List (Nat × Nat) → ByteArray
  | [] => acc
  | (num,off)::xs => headerBytesFrom (acc ++ (s!"{num} {off} ").toUTF8) xs

private def headerBytes (xs : List (Nat × Nat)) : ByteArray :=
  headerBytesFrom ByteArray.empty xs

private theorem headerBytesFrom_exact (xs : List (Nat × Nat)) (acc : ByteArray) :
    headerBytesFrom acc xs = acc ++ headerBytes xs := by
  induction xs generalizing acc with
  | nil => simp [headerBytesFrom, headerBytes]
  | cons p ps ih =>
    simp only [headerBytesFrom]
    rw [ih]
    change _ = acc ++ headerBytesFrom ByteArray.empty (p::ps)
    rw [headerBytesFrom, ih]
    simp only [ByteArray.empty_append, ByteArray.append_assoc]

private theorem headerBytes_cons (p : Nat × Nat) (xs : List (Nat × Nat)) :
    headerBytes (p::xs) = (s!"{p.1} {p.2} ").toUTF8 ++ headerBytes xs := by
  unfold headerBytes
  rw [headerBytesFrom, headerBytesFrom_exact]
  simp only [ByteArray.empty_append, headerBytes]

private theorem objectStreamList_header_bytes (xs : List (Nat × Obj))
    (s : ObjectStream) :
    (objectStreamList s xs).header.toUTF8 =
      s.header.toUTF8 ++ headerBytes (objectStreamPositions s.payload.size xs) := by
  induction xs generalizing s with
  | nil => simp only [objectStreamList, objectStreamPositions, headerBytes, headerBytesFrom,
      ByteArray.append_empty]
  | cons x xs ih =>
    rw [objectStreamList, ih]
    simp only [ObjectStream.push, objectStreamPositions, headerBytes_cons,
      utf8_append, ByteArray.size_push, ByteArray.size_append,
      ByteArray.append_assoc]

private theorem pair_octets (num off : Nat) :
    octets (s!"{num} {off} ").toUTF8 =
      octets (toString num).toUTF8 ++
        32 :: (octets (toString off).toUTF8 ++ [32]) := by
  simp only [utf8_append, octets_append, List.append_assoc]
  simp only [String.toUTF8_eq_toByteArray]
  rfl

private def headerStep (b : ByteArray) (_ : Nat)
    (s : Nat × Array (Nat × Nat)) : Except String (ForInStep (Nat × Array (Nat × Nat))) :=
  match parseUInt b (skipWs b s.1) with
  | some (num,j) =>
    match parseUInt b (skipWs b j) with
    | some (off,k) => .ok (.yield (k,s.2.push (num,off)))
    | _ => .error "malformed PDF: unreadable object stream header"
  | _ => .error "malformed PDF: unreadable object stream header"

private theorem header_first {b : ByteArray} {i : Nat} {xs : List (Nat × Nat)}
    (hn : xs ≠ []) (h : PdfLex.Span b i (octets (headerBytes xs))) :
    isWs (at? b i) = false ∧ at? b i ≠ 37 := by
  cases xs with
  | nil => exact (hn rfl).elim
  | cons p ps =>
    simp only [headerBytes_cons, octets_append, pair_octets] at h
    have hd := ObjReader.numeric_first h.append_left.append_left
      (Number.nat_nonempty p.1) (nat_numeric p.1)
    exact ⟨(number_byte hd).2.1,(number_byte hd).2.2.1⟩

private theorem header_loop_exact (xs : List (Nat × Nat)) (counters : List Nat)
    (hc : counters.length = xs.length) {b : ByteArray} {start i : Nat}
    (h : PdfLex.Span b start (octets (headerBytes xs)))
    (hw : xs ≠ [] → skipWs b i = start) (acc : Array (Nat × Nat)) :
    ((forIn counters (i,acc) (headerStep b)).bind (fun s => .ok s.2)) =
      .ok (acc ++ xs.toArray) := by
  induction xs generalizing counters start i acc with
  | nil =>
    have he : counters = [] := List.eq_nil_of_length_eq_zero hc
    simp only [he, List.forIn_nil, pure, Except.bind, Except.pure,
      List.toArray, Array.append_empty]
  | cons p ps ih =>
    cases counters with
    | nil => simp at hc
    | cons counter counters =>
      have hw := hw (by simp)
      simp only [headerBytes_cons, octets_append, pair_octets] at h
      have hnum := h.append_left.append_left
      have hsep : PdfLex.Span b (start+(toString p.1).toUTF8.size)
          (32 :: (octets (toString p.2).toUTF8 ++ [32])) := by
        simpa only [octets_length] using h.append_left.append_right
      have hoff := hsep.tail.append_left
      have hend : PdfLex.Span b (start+(toString p.1).toUTF8.size+1+(toString p.2).toUTF8.size)
          [32] := by simpa only [octets_length] using hsep.tail.append_right
      have htail : PdfLex.Span b (start+(toString p.1).toUTF8.size+1+(toString p.2).toUTF8.size+1)
          (octets (headerBytes ps)) := by
        simpa only [List.length_append, List.length_cons, List.length_nil, octets_length,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.zero_add] using h.append_right
      have hnumRead := parse_nat hnum (Or.inr (Or.inl (by rw [hsep.head]; rfl)))
      have hnOff := ObjReader.numeric_first hoff (Number.nat_nonempty p.2) (nat_numeric p.2)
      have hoffSkip := skipWs_one_exact hsep.head (number_byte hnOff).2.1
        (number_byte hnOff).2.2.1 (by
          have := hsep.bound
          simp only [List.length_cons, List.length_append, List.length_nil] at this
          omega)
      have hoffRead := parse_nat hoff (Or.inr (Or.inl (by rw [hend.head]; rfl)))
      have hnext := ih counters (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hc)
        (i := start+(toString p.1).toUTF8.size+1+(toString p.2).toUTF8.size)
        htail (fun hn => skipWs_one_exact hend.head
          (header_first hn htail).1 (header_first hn htail).2
          (by
            have := hend.bound
            simp only [List.length_cons, List.length_nil] at this
            omega)) (acc.push p)
      rw [List.forIn_cons]
      simp only [headerStep, hw, hnumRead, hoffSkip, hoffRead, bind, Except.bind]
      simpa only [ObjReader.push_append_toArray, Except.bind] using hnext

/-- Actual header parsing recovers the producer's complete ordered
position transcript, including the empty stream. Every offset is the
size of the preceding rendered values; this is an arbitrary-input proof,
not a collection of sample headers. -/
public theorem objectStream_header_exact (xs : List (Nat × Obj)) :
    readObjectStreamHeader (objectStream xs).bytes xs.length =
      .ok (objectStreamPositions 0 xs).toArray := by
  have hh : (objectStream xs).header.toUTF8 =
      headerBytes (objectStreamPositions 0 xs) := by
    simpa only [objectStream, ByteArray.size_empty,
      show "".toUTF8 = ByteArray.empty from by simp,
      ByteArray.empty_append] using objectStreamList_header_bytes xs {}
  have hs : PdfLex.Span (objectStream xs).bytes 0
      (octets (headerBytes (objectStreamPositions 0 xs))) := by
    rw [ObjectStream.bytes, hh]
    simpa only [octets, ByteArray.empty_append, ByteArray.size_empty] using
      PdfLex.Span.of_bytes ByteArray.empty (headerBytes (objectStreamPositions 0 xs))
        (objectStream xs).payload
  unfold readObjectStreamHeader
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  have hp := header_loop_exact (objectStreamPositions 0 xs)
    (List.range' 0 xs.length) (by simp) hs
    (fun hn => skipWs_fixed_point (header_first hn hs).1 (header_first hn hs).2) #[]
  simp only [Array.empty_append, Except.bind] at hp
  apply Eq.trans ?_ hp
  congr 2

end LeanTex.Core.Pdf
