import LeanTex.Core.Dim
import LeanTex.Core.PdfObj
import LeanTex.Core.PdfReadProof
import LeanTex.Core.PdfFooter
import LeanTex.Core.PdfXref
import LeanTex.Core.Binary
import LeanTex.Core.Flate
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

namespace LeanTex.Core.PdfRead

open LeanTex.Core.Dim
open PdfLex

/-! # Reading a PDF page as a form XObject

The asset half of PLAN's graphics boundary: `\includegraphics{file.pdf}` —
and every boundary result — embeds a selected page of an existing PDF as a
form XObject, defaulting to page 1, so vector stays vector. This module is
the pure reader: a total function over a `ByteArray` that follows the
cross-reference (classic tables *and* xref streams with object streams —
modern lualatex output uses the streams), selects in physical `/Kids`
order, takes the page's box, concatenates its decoded content streams, and
copies its `/Resources` dictionary with the whole object graph behind it —
fonts, XObjects, ExtGState — renumbered into a local space the writer
offsets. Stream payloads (font programs above all) are copied verbatim,
never re-parsed. A PDF the reader cannot follow is a named error value,
never a crash: every read is bounds-checked and every loop bounded by the
input's size (the `Ink` reader discipline).

The trust label: the engine claims the *box* — placement and measurement
from the file's own page box — never the contents of the copied streams.
Structure and section references are ISO 32000-2. -/

/-- Decompressed streams are capped: a hostile deflate stream can claim a
1000× expansion, and a reader that honours it is a memory bomb. 64 MiB
holds any figure this engine should meet; past it the file is refused by
name. -/
def maxDecoded : Nat := 1 <<< 26

-- ## Objects (§7.3)

/-- A numeric object in sp: `72` or `595.276`, exact to the sp. -/
def Obj.sp? (o : Obj) : Option Sp :=
  match o with
  | .int n => some (n * spPerPt)
  | .real raw => Id.run do
    let s := raw.toList
    let (neg, s) := match s with
      | '-' :: rest => (true, rest)
      | '+' :: rest => (false, rest)
      | _ => (false, s)
    let mut ip : Nat := 0
    let mut seen := false
    let mut rest := s
    for _ in [0:raw.length + 1] do
      match rest with
      | c :: tl =>
        if c.isDigit then
          ip := ip * 10 + (c.toNat - 48)
          seen := true
          rest := tl
        else
          break
      | [] => break
    let mut num : Nat := 0
    let mut den : Nat := 1
    match rest with
    | '.' :: tl =>
      rest := tl
      for _ in [0:raw.length + 1] do
        match rest with
        | c :: tl =>
          if c.isDigit && den < 1000000000 then
            num := num * 10 + (c.toNat - 48)
            den := den * 10
            seen := true
            rest := tl
          else if c.isDigit then
            rest := tl
          else
            break
        | [] => break
    | _ => pure ()
    if !seen || !rest.isEmpty then
      return none
    let v : Int := ip * 65536 + ((num * 65536 + den / 2) / den : Nat)
    return some (if neg then -v else v)
  | _ => none

-- ## The cross-reference (§7.5)

/-- Where an object lives: at a byte offset, or inside an object stream. -/
inductive Loc where
  | direct (off : Nat)
  | inStm (stm : Nat) (idx : Nat)
  deriving Inhabited

/-- `num gen obj <value>` at a byte offset (§7.3.10). Returns the object
number the file spells there, the value, and the position after it, where
`stream` may follow. -/
private def parseIndirectAt (b : ByteArray) (off : Nat) :
    Except String (Nat × Obj × Nat) := do
  let some (num, i) := parseUInt b (skipWs b off)
    | throw "malformed PDF: no object number at a cross-referenced offset"
  let some (_, j) := parseUInt b (skipWs b i)
    | throw "malformed PDF: no generation number at a cross-referenced offset"
  let some k := keywordAt b (skipWs b j) "obj"
    | throw "malformed PDF: 'obj' missing at a cross-referenced offset"
  let (v, after) ← parseVal b k
  return (num, v, after)

/- The indirect-object invariant is stated on the actual byte span, before
stream decoding. It consumes the writer's decimal header and the already
proved value grammar; no reader result is a hypothesis. -/
private theorem nat_start_skip {b : ByteArray} {i : Nat} (n : Nat)
    (hs : Span b i (octets (toString n).toUTF8)) : skipWs b i = i := by
  rw [numeric_octets _ (nat_numeric n)] at hs
  have hn : (toString n).toList.map Char.toNat ≠ [] := by
    simp
  have hp := number_byte (hs.first_number hn (by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact nat_numeric n d hd))
  exact skipWs_fixed_point hp.2.1 hp.2.2.1

private theorem parseIndirectAt_render_span_exact {b : ByteArray} {i : Nat}
    (n : Nat) (o : Obj) (ho : o.Representable)
    (hs : Span b i (octets (s!"{n} 0 obj\n").toUTF8 ++ octets o.render))
    (he : ObjReader.Stop b (i + (s!"{n} 0 obj\n").toUTF8.size + o.render.size)) :
    parseIndirectAt b i = .ok (n, o, i + (s!"{n} 0 obj\n").toUTF8.size + o.render.size) := by
  have hhead : (s!"{n} 0 obj\n").toUTF8 = (toString n).toUTF8 ++ " 0 obj\n".toUTF8 := rfl
  simp only [hhead, octets_append, List.append_assoc, ByteArray.size_append,
    show " 0 obj\n".toUTF8.size = 7 from rfl, ← Nat.add_assoc] at hs he ⊢
  let q := i + (toString n).toUTF8.size
  have hnum := hs.append_left
  have hrest : Span b q (32 :: 48 :: 32 :: 111 :: 98 :: 106 :: 10 :: octets o.render) := by
    simpa only [octets_length, show octets " 0 obj\n".toUTF8 = [32,48,32,111,98,106,10] from rfl,
      List.cons_append, List.nil_append] using hs.append_right
  have hb : q + 7 ≤ b.size := by
    have h := hrest.bound
    simp only [List.length_cons] at h
    omega
  have h32 : at? b q = 32 := hrest.head
  have h48 : at? b (q+1) = 48 := hrest.tail.head
  have hsp : at? b (q+2) = 32 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hrest.tail.tail.head
  have h111 : at? b (q+3) = 111 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hrest.tail.tail.tail.head
  have hlf : at? b (q+6) = 10 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hrest.tail.tail.tail.tail.tail.tail.head
  have hobj : Span b (q+3) (octets "obj".toUTF8) := by
    change Span b (q+3) [111,98,106]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      hrest.tail.tail.tail.append_left (cs := [111,98,106]) (ds := 10 :: octets o.render)
  have hov : Span b (q+7) (octets o.render) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hrest.tail.tail.tail.tail.tail.tail.tail
  have he' : ObjReader.Stop b (q+7+o.render.size) := he
  have hstart := ho.reads.start hov he'.boundary he'.marker
  have hskip0 := nat_start_skip n hnum
  have hn := parse_nat hnum (Or.inr (Or.inl (by rw [h32]; rfl)))
  have hskip1 : skipWs b q = q+1 := skipWs_one_exact h32
    (by rw [h48]; rfl) (by rw [h48]; decide) (by omega)
  have hz : parseUInt b (q+1) = some (0,q+2) := by
    have hzspan : Span b (q+1) (octets (toString (0 : Nat)).toUTF8) :=
      hrest.tail.append_left (cs := [48]) (ds := 32 :: 111 :: 98 :: 106 :: 10 :: octets o.render)
    have hend : EndByte (at? b ((q+1)+(toString (0 : Nat)).toUTF8.size)) := by
      change EndByte (at? b (q+1+1))
      rw [show q+1+1=q+2 by omega, hsp]
      exact Or.inr (Or.inl rfl)
    simpa only [show (toString (0 : Nat)).toUTF8.size = 1 from rfl,
      Nat.add_assoc, Nat.reduceAdd] using parse_nat hzspan hend
  have hskip2 : skipWs b (q+2) = q+3 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using skipWs_one_exact hsp
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, h111] using (show isWs 111 = false from rfl))
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, h111] using (show (111 : Nat) ≠ 37 by decide))
      (by omega)
  have hkey : keywordAt b (q+3) "obj" = some (q+6) := by
    have hend : EndByte (at? b (q+3+"obj".toUTF8.size)) := by
      change EndByte (at? b (q+3+3))
      rw [show q+3+3=q+6 by omega, hlf]
      exact Or.inr (Or.inl rfl)
    simpa only [show "obj".toUTF8.size = 3 from rfl, Nat.add_assoc, Nat.reduceAdd] using
      keywordAt_exact hobj hend
  have hskip3 : skipWs b (q+6) = q+7 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using skipWs_whitespace_exact
      (by rw [hlf]; rfl)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hstart.whitespace)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hstart.comment)
      (by omega : q+6 < b.size)
  have hp := parseVal_render_span_exact o ho hov he' hskip3
  change parseIndirectAt b i = .ok (n,o,q+7+o.render.size)
  simp only [parseIndirectAt, hskip0, hn]
  change (do
    let some (_, j) := parseUInt b (skipWs b q) | throw _
    let some k := keywordAt b (skipWs b j) "obj" | throw _
    let (v, after) ← parseVal b k
    return (n,v,after)) = _
  simp only [hskip1, hz, hskip2, hkey, hp]
  rfl

/-- Decode one stream's data by its declared filter: none, or
`/FlateDecode`, with a PNG predictor honoured when `/DecodeParms` declares
one (§7.4.4). Any other filter is a refusal naming it. -/
def decodeStream (dict : Obj) (raw : ByteArray) : Except String ByteArray := do
  let filter := dict.get? "Filter"
  let parms := (dict.get? "DecodeParms").bind fun d =>
    match d with
    | .arr xs => xs[0]?
    | _ => some d
  let flate ← match filter with
    | none => return raw
    | some (.name "FlateDecode") => pure true
    | some (.arr #[.name "FlateDecode"]) => pure true
    | some (.name f) => throw s!"PDF stream filter /{f} is not supported"
    | some _ => throw "PDF stream filter chains are not supported"
  let _ := flate
  let cap := match (dict.get? "DL").bind Obj.int? with
    | some n => if 0 ≤ n && n.toNat ≤ maxDecoded then n.toNat else maxDecoded
    | none => maxDecoded
  let data ← Flate.inflate raw cap
  -- The zlib trailer (RFC 1950 §2.2) is checked here, where the reader
  -- judges a file: `Flate.inflate` leaves it to its callers, and a byte
  -- corrupted inside a Huffman block otherwise decodes to quiet garbage.
  let n := raw.size
  let stated := (raw[n - 4]?.getD 0).toNat * 16777216 + (raw[n - 3]?.getD 0).toNat * 65536 +
    (raw[n - 2]?.getD 0).toNat * 256 + (raw[n - 1]?.getD 0).toNat
  if n < 4 || stated != Flate.adler32 data then
    throw "malformed PDF: a stream's data does not match its Adler-32 checksum"
  match parms.bind (·.get? "Predictor") |>.bind Obj.int? with
  | some p =>
    if p ≥ 10 then
      let columns := (((parms.bind (·.get? "Columns")).bind Obj.int?).getD 1).toNat
      let colors := (((parms.bind (·.get? "Colors")).bind Obj.int?).getD 1).toNat
      let bpc := (((parms.bind (·.get? "BitsPerComponent")).bind Obj.int?).getD 8).toNat
      let bpp := max 1 (colors * bpc / 8)
      let rowBytes := max 1 (columns * colors * bpc / 8)
      let rows := data.size / (rowBytes + 1)
      Flate.pngUnfilter data rows rowBytes bpp
    else if p ≤ 1 then
      return data
    else
      throw s!"PDF stream predictor {p} is not supported"
  | none => return data

/-- A big-endian field of `w` bytes at `i`; a zero-width field reads 0. -/
private def beField (data : ByteArray) (i w : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:w] do
    v := v * 256 + (data[i + k]?.getD 0).toNat
  return v

/- The loop is progress-indexed by its field width. The equation below is
a proof about the forIn loop above, not a replacement implementation. -/
private theorem beField_succ (data : ByteArray) (i w : Nat) :
    beField data i (w+1) = beField data i w * 256 + (data[i+w]?.getD 0).toNat := by
  unfold beField
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [List.forIn_pure_yield_eq_foldl]
  simp [List.range'_concat, List.foldl_append]
private theorem beField_read (data : ByteArray) (i w v : Nat)
    (h : Binary.readNatBE w data i = some v) : beField data i w = v := by
  induction w generalizing v with
  | zero => simpa [Binary.readNatBE, beField] using h
  | succ w ih =>
    simp only [Binary.readNatBE, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨n,hn,b,hb,hv⟩ := h
    change some (n * 256 + b.toNat) = some v at hv
    have hv := Option.some.inj hv
    subst v
    rw [beField_succ, ih n hn, hb]
    rfl

/-- The object location represented by a writer entry. Free entries do
not contribute to the reader's live-object map. This is a semantic
projection; it does not encode or parse any bytes. -/
def xrefEntryLocation : Pdf.Xref.Entry → Option Loc
  | .free _ _ => none
  | .direct off _ => some (.direct off)
  | .compressed stm idx => some (.inStm stm idx)

/-- The location carried by one cross-reference-stream row. A free,
unknown, or truncated row contributes no live object; a zero-width type
field has the PDF-specified default of one (§7.5.8.3). -/
def readXrefRow (data : ByteArray) (base w0 w1 w2 : Nat) : Option Loc :=
  if base + (w0+w1+w2) ≤ data.size then
    let f1 := if w0 == 0 then 1 else beField data base w0
    let f2 := beField data (base+w0) w1
    let f3 := beField data (base+w0+w1) w2
    if f1 == 1 then some (.direct f2)
    else if f1 == 2 then some (.inStm f2 f3)
    else none
  else none

/-- The actual reader recovers the location of any encoded writer row,
inside arbitrary surrounding bytes. The only premise beyond selecting
the row is its numeric representability; no parsing result is assumed. -/
theorem readXrefRow_encode_exact (es : Array Pdf.Xref.Entry) (i : Nat)
    (e : Pdf.Xref.Entry) (hi : es[i]? = some e) (he : e.Fits)
    (pre post : ByteArray) :
    readXrefRow (pre ++ Pdf.Xref.encode es ++ post) (pre.size+7*i) 1 4 2 =
      match (generalizing := false) e with
      | .free _ _ => none
      | .direct off _ => some (.direct off)
      | .compressed stm idx => some (.inStm stm idx) := by
  have fields := Pdf.Xref.encode_index_fields_exact es i e hi he pre post
  have a := beField_read _ _ _ _ fields.1
  have b := beField_read _ _ _ _ fields.2.1
  have c := beField_read _ _ _ _ fields.2.2
  have ib := (Array.getElem?_eq_some_iff.mp hi).1
  have bound : pre.size+7*i+(1+4+2) ≤ (pre ++ Pdf.Xref.encode es ++ post).size := by
    simp only [ByteArray.size_append, Pdf.Xref.encode_size_exact]
    omega
  simp only [readXrefRow, bound, ↓reduceIte, show (1 == 0) = false from rfl,
    Nat.reduceAdd, Bool.false_eq_true]
  rw [a,b]
  have cc : beField (pre ++ Pdf.Xref.encode es ++ post) (pre.size+7*i+1+4) 2 =
      e.fields.2.2 := by simpa only [Nat.add_assoc, Nat.reduceAdd] using c
  rw [cc]
  cases e <;> rfl

/-- The cross-reference as read: where every listed object lives, the
catalog's number, the newest section's trailer dictionary (a classic
trailer, or the cross-reference stream's own dictionary — the two carry
the same keys, §7.5.8.2), and the offset `startxref` named. -/
structure Xref where
  locs : Std.HashMap Nat Loc := {}
  root : Option Nat := none
  trailer : Option Obj := none
  start : Nat := 0

private def Xref.add (x : Xref) (num : Nat) (l : Loc) : Xref :=
  if x.locs.contains num then x else { x with locs := x.locs.insert num l }

/-- The newest trailer wins: a section already recorded keeps its
dictionary, as its entries keep their locations. -/
private def Xref.seen (x : Xref) (trailer : Obj) : Xref :=
  let x := if x.trailer.isNone then { x with trailer := some trailer } else x
  if x.root.isNone then
    if let some (.ref r _) := trailer.get? "Root" then { x with root := some r } else x
  else x

/-- Consume one `/Index` subsection of decoded xref rows. The second
result is the next physical row, distinct from the subsection's starting
object number. The same loop serves the stream reader and its proofs. -/
def readXrefSubsection (data : ByteArray) (w0 w1 w2 start count row0 : Nat)
    (x0 : Xref) : Xref × Nat := Id.run do
  let mut x := x0
  let mut row := row0
  for e in [0:count] do
    let base := row * (w0+w1+w2)
    x := match readXrefRow data base w0 w1 w2 with
      | some loc => x.add (start+e) loc
      | none => x
    row := row+1
  return (x,row)

private theorem readXrefSubsection_succ (data : ByteArray)
    (w0 w1 w2 start count row0 : Nat) (x0 : Xref) :
    readXrefSubsection data w0 w1 w2 start (count+1) row0 x0 =
      let (x,row) := readXrefSubsection data w0 w1 w2 start count row0 x0
      (match readXrefRow data (row*(w0+w1+w2)) w0 w1 w2 with
        | some loc => x.add (start+count) loc
        | none => x, row+1) := by
  unfold readXrefSubsection
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [List.forIn_pure_yield_eq_foldl]
  simp [List.range'_concat, List.foldl_append]

/-- Progress of the actual subsection loop through physical rows. -/
theorem readXrefSubsection_row_exact (data : ByteArray)
    (w0 w1 w2 start count row0 : Nat) (x0 : Xref) :
    (readXrefSubsection data w0 w1 w2 start count row0 x0).2 = row0+count := by
  induction count with
  | zero => simp [readXrefSubsection]
  | succ count ih => simp only [readXrefSubsection_succ, ih, Nat.add_assoc]

/-- Every consumed, representable row is recovered in the actual reader
map at its object number. Unconsumed rows are absent. The empty initial
map is the newest xref section's state, and the induction advances the
physical row and object number together. -/
theorem readXrefSubsection_locations_exact (es : Array Pdf.Xref.Entry)
    (hf : ∀ e ∈ es, e.Fits) (count : Nat) (hc : count ≤ es.size)
    (x0 : Xref) (hx : x0.locs = {}) :
    ∀ k, (readXrefSubsection (Pdf.Xref.encode es) 1 4 2 0 count 0 x0).1.locs[k]? =
      if k < count then es[k]?.bind xrefEntryLocation else none := by
  induction count with
  | zero => intro k; simp [readXrefSubsection, hx]
  | succ n ih =>
    have hn : n < es.size := by omega
    have old := ih (by omega)
    have hr := readXrefRow_encode_exact es n es[n] (by simp) (hf _ (Array.getElem_mem hn))
      ByteArray.empty ByteArray.empty
    simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
      Nat.zero_add] at hr
    change readXrefRow (Pdf.Xref.encode es) (7*n) 1 4 2 = xrefEntryLocation es[n] at hr
    have fresh : (readXrefSubsection (Pdf.Xref.encode es) 1 4 2 0 n 0 x0).1.locs.contains n = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, old]
      simp
    intro k
    rw [readXrefSubsection_succ]
    simp only [readXrefSubsection_row_exact, Nat.zero_add, Nat.reduceAdd,
      Nat.mul_comm n 7, hr]
    have thisN : es[n]? = some es[n] := Array.getElem?_eq_getElem hn
    cases he : es[n] with
    | free next gen =>
      simp only [xrefEntryLocation]
      rw [old]
      by_cases hkn : k = n
      · subst k; simp [thisN, he, xrefEntryLocation]
      · have hlt : (k < n+1) = (k < n) := propext (by omega)
        simp only [hlt]
    | direct off gen =>
      simp only [xrefEntryLocation, Xref.add, fresh, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.getElem?_insert]
      by_cases hkn : n = k
      · subst k; simp [thisN, he, xrefEntryLocation]
      · simp only [beq_iff_eq, hkn, ↓reduceIte, old]
        have hlt : (k < n+1) = (k < n) := propext (by omega)
        simp only [hlt]
    | compressed stm idx =>
      simp only [xrefEntryLocation, Xref.add, fresh, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.getElem?_insert]
      by_cases hkn : n = k
      · subst k; simp [thisN, he, xrefEntryLocation]
      · simp only [beq_iff_eq, hkn, ↓reduceIte, old]
        have hlt : (k < n+1) = (k < n) := propext (by omega)
        simp only [hlt]

/-- The actual reader's live-object count for a writer table with object
zero free and every nonzero object live. These are properties of the
semantic entries, not assumptions about successful parsing. -/
theorem readXrefSubsection_size_exact (es : Array Pdf.Xref.Entry)
    (hf : ∀ e ∈ es, e.Fits)
    (hzero : es[0]?.bind xrefEntryLocation = none)
    (hlive : ∀ i, 0 < i → i < es.size → (es[i]?.bind xrefEntryLocation).isSome = true)
    (count : Nat) (hc : count ≤ es.size) (x0 : Xref) (hx : x0.locs = {}) :
    (readXrefSubsection (Pdf.Xref.encode es) 1 4 2 0 count 0 x0).1.locs.size = count-1 := by
  induction count with
  | zero => simp [readXrefSubsection, hx]
  | succ n ih =>
    have hn : n < es.size := by omega
    have old := readXrefSubsection_locations_exact es hf n (by omega) x0 hx
    have hr := readXrefRow_encode_exact es n es[n] (by simp) (hf _ (Array.getElem_mem hn))
      ByteArray.empty ByteArray.empty
    simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
      Nat.zero_add] at hr
    change readXrefRow (Pdf.Xref.encode es) (7*n) 1 4 2 = xrefEntryLocation es[n] at hr
    have fresh : (readXrefSubsection (Pdf.Xref.encode es) 1 4 2 0 n 0 x0).1.locs.contains n = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, old]
      simp
    rw [readXrefSubsection_succ]
    simp only [readXrefSubsection_row_exact, Nat.zero_add, Nat.reduceAdd, Nat.mul_comm n 7, hr]
    have thisN : es[n]? = some es[n] := Array.getElem?_eq_getElem hn
    cases he : es[n] with
    | free next gen =>
      have hn0 : n = 0 := by
        by_cases hh : n = 0
        · exact hh
        · have := hlive n (by omega) hn
          simp [thisN, he, xrefEntryLocation] at this
      simp only [xrefEntryLocation]
      rw [ih (by omega), hn0]
    | direct off gen =>
      have hn0 : 0 < n := by
        by_cases hh : n = 0
        · subst n
          simp [thisN, he, xrefEntryLocation] at hzero
        · omega
      simp only [xrefEntryLocation, Xref.add, fresh, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.size_insert, ih (by omega)]
      simp only [Std.HashMap.mem_iff_contains, fresh, Bool.false_eq_true, ↓reduceIte]
      omega
    | compressed stm idx =>
      have hn0 : 0 < n := by
        by_cases hh : n = 0
        · subst n
          simp [thisN, he, xrefEntryLocation] at hzero
        · omega
      simp only [xrefEntryLocation, Xref.add, fresh, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.size_insert, ih (by omega)]
      simp only [Std.HashMap.mem_iff_contains, fresh, Bool.false_eq_true, ↓reduceIte]
      omega

/-- Reading rows preserves the trailer, root, and startxref metadata. -/
theorem readXrefSubsection_metadata_exact (data : ByteArray)
    (w0 w1 w2 start count row0 : Nat) (x0 : Xref) :
    let x := (readXrefSubsection data w0 w1 w2 start count row0 x0).1
    x.root = x0.root ∧ x.trailer = x0.trailer ∧ x.start = x0.start := by
  induction count with
  | zero => simp [readXrefSubsection]
  | succ n ih =>
    cases hp : readXrefSubsection data w0 w1 w2 start n row0 x0 with
    | mk x row =>
      simp only [readXrefSubsection_succ, hp]
      simp only [hp] at ih
      cases hr : readXrefRow data (row*(w0+w1+w2)) w0 w1 w2 with
      | none => exact ih
      | some loc =>
        simp only [Xref.add]
        split <;> exact ih

/-- One classic xref section (§7.5.4) at `off`: subsections of 20-byte
entries, then the trailer dictionary. Returns the updated table and the
`/Prev` and `/XRefStm` offsets, if declared. -/
private def readClassicSection (b : ByteArray) (off : Nat) (x0 : Xref) :
    Except String (Xref × Option Nat × Option Nat) := Id.run do
  let mut x := x0
  let some i0 := keywordAt b (skipWs b off) "xref"
    | return .error "malformed PDF: no 'xref' at the startxref offset"
  let mut i := i0
  for _ in [0:b.size + 1] do
    i := skipWs b i
    if (keywordAt b i "trailer").isSome then
      break
    let some (start, j) := parseUInt b i
      | return .error "malformed PDF: unreadable xref subsection header"
    let some (count, k) := parseUInt b (skipWs b j)
      | return .error "malformed PDF: unreadable xref subsection header"
    i := k
    for e in [0:count] do
      i := skipWs b i
      let some (v1, j1) := parseUInt b i
        | return .error "malformed PDF: unreadable xref entry"
      let some (_, j2) := parseUInt b (skipWs b j1)
        | return .error "malformed PDF: unreadable xref entry"
      let j3 := skipWs b j2
      let kind := at? b j3
      if kind == 110 then  -- n
        x := x.add (start + e) (.direct v1)
      else if kind != 102 then  -- f
        return .error "malformed PDF: xref entry is neither in use nor free"
      i := j3 + 1
  let some t := keywordAt b (skipWs b i) "trailer"
    | return .error "malformed PDF: xref table without a trailer"
  match parseVal b t with
  | .error e => return .error e
  | .ok (trailer, _) =>
    x := x.seen trailer
    let prev := ((trailer.get? "Prev").bind Obj.int?).map (·.toNat)
    let xstm := ((trailer.get? "XRefStm").bind Obj.int?).map (·.toNat)
    return .ok (x, prev, xstm)

/-- One cross-reference stream (§7.5.8) at `off`. -/
private def readStreamSection (b : ByteArray) (off : Nat) (x0 : Xref) :
    Except String (Xref × Option Nat) := do
  let (_, dict, j) ← parseIndirectAt b off
  let some k := keywordAt b (skipWs b j) "stream"
    | throw "malformed PDF: a cross-reference stream has no stream"
  let dataStart := if at? b k == 13 && at? b (k + 1) == 10 then k + 2
    else if at? b k == 10 then k + 1 else k
  let some len := (dict.get? "Length").bind Obj.int?
    | throw "malformed PDF: a cross-reference stream has no direct /Length"
  if len < 0 || dataStart + len.toNat > b.size then
    throw "truncated PDF: a cross-reference stream overruns the file"
  let data ← decodeStream dict (b.extract dataStart (dataStart + len.toNat))
  let some (.arr ws) := dict.get? "W"
    | throw "malformed PDF: a cross-reference stream has no /W"
  let w0 := ((ws[0]?.bind Obj.int?).getD 1).toNat
  let w1 := ((ws[1]?.bind Obj.int?).getD 0).toNat
  let w2 := ((ws[2]?.bind Obj.int?).getD 0).toNat
  let rowW := w0 + w1 + w2
  if rowW == 0 then
    throw "malformed PDF: a cross-reference stream declares empty rows"
  let some size := (dict.get? "Size").bind Obj.int?
    | throw "malformed PDF: a cross-reference stream has no /Size"
  let index : Array Int := match dict.get? "Index" with
    | some (.arr xs) => xs.filterMap Obj.int?
    | _ => #[0, size]
  let mut x := x0.seen dict
  let mut row := 0
  for p in [0:index.size / 2] do
    let start := ((index[2 * p]?).getD 0).toNat
    let count := ((index[2 * p + 1]?).getD 0).toNat
    let (x',row') := readXrefSubsection data w0 w1 w2 start count row x
    x := x'
    row := row'
  let prev := ((dict.get? "Prev").bind Obj.int?).map (·.toNat)
  return (x, prev)

/-- Follow `startxref` and the `/Prev` chain over every cross-reference
section, classic or stream (a hybrid file's `/XRefStm` too). Newest
section first: an entry already seen is never overridden. -/
private def readXrefFrom (b : ByteArray) (off0 : Nat) : Except String Xref := Id.run do
  let mut work : Array Nat := #[off0]
  let mut seen : Array Nat := #[]
  let mut x : Xref := { start := off0 }
  for _ in [0:64] do
    let some off := work.back? | break
    work := work.pop
    if seen.contains off then
      continue
    seen := seen.push off
    if (keywordAt b (skipWs b off) "xref").isSome then
      match readClassicSection b off x with
      | .error e => return .error e
      | .ok (x', prev, xstm) =>
        x := x'
        if let some p := prev then work := work.push p
        if let some p := xstm then work := work.push p
    else
      match readStreamSection b off x with
      | .error e => return .error e
      | .ok (x', prev) =>
        x := x'
        if let some p := prev then work := work.push p
  if !work.isEmpty then
    return .error "malformed PDF: the cross-reference chain is longer than 64 sections"
  return .ok x

/-- Read the footer, then traverse the sections it names. -/
def readXref (b : ByteArray) : Except String Xref := do
  readXrefFrom b (← readStartxref b)

private theorem indirect_stream_span {b : ByteArray} {i : Nat}
    (n : Nat) (dict : Obj) (hd : dict.Representable) (raw : ByteArray)
    (hs : Span b i (octets (s!"{n} 0 obj\n").toUTF8 ++
      octets dict.render ++ octets "\nstream\n".toUTF8 ++ octets raw)) :
    let j := i + (s!"{n} 0 obj\n").toUTF8.size + dict.render.size
    parseIndirectAt b i = .ok (n, dict, j) ∧
      keywordAt b (skipWs b j) "stream" = some (j+7) ∧
      at? b (j+7) = 10 ∧ j+8+raw.size ≤ b.size ∧
      b.extract (j+8) (j+8+raw.size) = raw := by
  dsimp only
  let j := i + (s!"{n} 0 obj\n").toUTF8.size + dict.render.size
  have hs' : Span b i ((octets (s!"{n} 0 obj\n").toUTF8 ++ octets dict.render) ++
      (octets "\nstream\n".toUTF8 ++ octets raw)) := by
    simpa only [List.append_assoc] using hs
  have ht : Span b j ([10,115,116,114,101,97,109,10] ++ octets raw) := by
    simpa only [List.length_append, octets_length, ← Nat.add_assoc,
      show octets "\nstream\n".toUTF8 = [10,115,116,114,101,97,109,10] from rfl]
      using hs'.append_right
  have hlf : at? b j = 10 := ht.head
  have hs0 : at? b (j+1) = 115 := ht.tail.head
  have hs7 : at? b (j+7) = 10 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using ht.tail.tail.tail.tail.tail.tail.tail.head
  have hb : j+8+raw.size ≤ b.size := by
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd,
      octets_length, ← Nat.add_assoc] using ht.bound
  have he : ObjReader.Stop b j := .whitespace
    (by rw [hlf]; rfl) (by omega) (.non_numeric
      (by rw [hs0]; rfl) (by rw [hs0]; decide) (by rw [hs0]; decide)
      (by rw [hs0]; omega))
  have hi := parseIndirectAt_render_span_exact n dict hd hs'.append_left he
  have hk0 : skipWs b j = j+1 := skipWs_whitespace_exact (by rw [hlf]; rfl)
    (by rw [hs0]; rfl) (by rw [hs0]; decide) (by omega)
  have hk : keywordAt b (j+1) "stream" = some (j+7) := by
    have hs' : Span b (j+1) (octets "stream".toUTF8) :=
      ht.tail.append_left (cs := [115,116,114,101,97,109]) (ds := 10 :: octets raw)
    have hEnd : EndByte (at? b (j+1+"stream".toUTF8.size)) := by
      change EndByte (at? b (j+1+6))
      rw [show j+1+6=j+7 by omega, hs7]
      exact Or.inr (Or.inl rfl)
    simpa only [show "stream".toUTF8.size = 6 from rfl, Nat.add_assoc, Nat.reduceAdd]
      using keywordAt_exact hs' hEnd
  have hr : Span b (j+8) (octets raw) := by
    have hraw := ht.tail.tail.tail.tail.tail.tail.tail.tail
    change Span b (j+1+1+1+1+1+1+1+1) (octets raw) at hraw
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hraw
  exact ⟨hi, hk0 ▸ hk, hs7, hb, hr.extract_exact⟩

private theorem readStreamSection_span_exact {b : ByteArray} {i : Nat}
    (n : Nat) (dict : Obj) (hd : dict.Representable) (raw data : ByteArray)
    (count : Nat) (x0 : Xref)
    (hs : Span b i (octets (s!"{n} 0 obj\n").toUTF8 ++
      octets dict.render ++ octets "\nstream\n".toUTF8 ++ octets raw))
    (hl : dict.get? "Length" = some (.int raw.size))
    (hf : decodeStream dict raw = .ok data)
    (hw : dict.get? "W" = some (.arr #[.int 1, .int 4, .int 2]))
    (hc : dict.get? "Size" = some (.int count))
    (hx : dict.get? "Index" = some (.arr #[.int 0, .int count]))
    (hp : dict.get? "Prev" = none) :
    readStreamSection b i x0 =
      .ok ((readXrefSubsection data 1 4 2 0 count 0 (x0.seen dict)).1, none) := by
  obtain ⟨hi,hk,hb,hbound,he⟩ := indirect_stream_span n dict hd raw hs
  have hbound' : ¬ (i + (s!"{n} 0 obj\n").toUTF8.size + dict.render.size + 7 + 1 + raw.size > b.size) := by omega
  have he' : b.extract (i + (s!"{n} 0 obj\n").toUTF8.size + dict.render.size + 7 + 1)
      (i + (s!"{n} 0 obj\n").toUTF8.size + dict.render.size + 7 + 1 + raw.size) = raw := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using he
  simp only [readStreamSection, hi, bind, Except.bind, pure, Except.pure]
  simp only [hk, hb, hl, Option.bind_some, Obj.int?, Int.toNat_natCast,
    show ((10 : Nat) == 13) = false from rfl, Bool.false_and, Bool.false_eq_true,
    beq_self_eq_true, ↓reduceIte, show ¬((raw.size : Int) < 0) from Int.not_lt.mpr (Int.natCast_nonneg _),
    hbound', decide_false, Bool.or_self, he', hf, hw, hc, hx, hp]
  simp [Obj.int?, Array.filterMap, Std.Legacy.Range.forIn_eq_forIn_range',
    bind, pure]
  simp only [Id.run, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv,
    List.range', List.forIn_cons, List.forIn_nil, pure, bind, Except.bind, Except.pure]
  rfl

private theorem readXrefFrom_stream_exact (b : ByteArray) (off : Nat) (x : Xref)
    (hn : keywordAt b (skipWs b off) "xref" = none)
    (hs : readStreamSection b off {start := off} = .ok (x, none)) :
    readXrefFrom b off = .ok x := by
  unfold readXrefFrom
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [show List.range' 0 64 = 0 :: 1 :: List.range' 2 62 from rfl, List.forIn_cons]
  simp [hn, hs, Array.back?, Array.pop, pure, bind, Id.run]

private theorem readXref_span_exact {b : ByteArray} {i : Nat}
    (n : Nat) (dict : Obj) (hd : dict.Representable) (raw data : ByteArray)
    (count root : Nat)
    (hs : Span b i (octets (s!"{n} 0 obj\n").toUTF8 ++
      octets dict.render ++ octets "\nstream\n".toUTF8 ++ octets raw))
    (ht : readStartxref b = .ok i)
    (hl : dict.get? "Length" = some (.int raw.size))
    (hf : decodeStream dict raw = .ok data)
    (hw : dict.get? "W" = some (.arr #[.int 1, .int 4, .int 2]))
    (hc : dict.get? "Size" = some (.int count))
    (hx : dict.get? "Index" = some (.arr #[.int 0, .int count]))
    (hp : dict.get? "Prev" = none)
    (hr : dict.get? "Root" = some (.ref root 0)) :
    readXref b = .ok ((readXrefSubsection data 1 4 2 0 count 0
      {start := i, root := some root, trailer := some dict}).1) := by
  have hn : Span b i (octets (toString n).toUTF8) := by
    have hs' := hs
    rw [show (s!"{n} 0 obj\n").toUTF8 = (toString n).toUTF8 ++ " 0 obj\n".toUTF8 from rfl,
      octets_append] at hs'
    simpa only [List.append_assoc] using hs'.append_left.append_left.append_left.append_left
  have hk : keywordAt b (skipWs b i) "xref" = none := by
    rw [nat_start_skip n hn]
    apply keywordAt_ne (by decide)
    change at? b i ≠ 120
    rw [numeric_octets _ (nat_numeric n)] at hn
    have hh := hn.first_number (by simp) (by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact nat_numeric n d hd)
    simp only [numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
    omega
  have hsec := readStreamSection_span_exact n dict hd raw data count
    {start := i} hs hl hf hw hc hx hp
  have hx' : ({start := i} : Xref).seen dict =
      {start := i, root := some root, trailer := some dict} := by
    simp [Xref.seen, hr]
  rw [hx'] at hsec
  simp only [readXref, ht, bind, Except.bind]
  exact readXrefFrom_stream_exact b i _ hk hsec

/-- The actual footer scan, indirect-object parser, stream boundary,
subsection loop, and section traversal recover a single emitted xref
stream. The codec premise is local to its payload and is discharged by
the writer's compression contract when this lemma is composed. -/
theorem readXref_stream_exact (pre : ByteArray) (n : Nat)
    (dict : Obj) (hd : dict.Representable) (raw data : ByteArray)
    (count root : Nat) (hi : pre.size < 256^4)
    (hl : dict.get? "Length" = some (.int raw.size))
    (hf : decodeStream dict raw = .ok data)
    (hw : dict.get? "W" = some (.arr #[.int 1, .int 4, .int 2]))
    (hc : dict.get? "Size" = some (.int count))
    (hx : dict.get? "Index" = some (.arr #[.int 0, .int count]))
    (hp : dict.get? "Prev" = none)
    (hr : dict.get? "Root" = some (.ref root 0)) :
    readXref (pre ++ (s!"{n} 0 obj\n").toUTF8 ++ dict.render ++ "\nstream\n".toUTF8 ++
        raw ++ "\nendstream\nendobj\n".toUTF8 ++ (s!"startxref\n{pre.size}\n%%EOF\n").toUTF8) =
      .ok ((readXrefSubsection data 1 4 2 0 count 0
        {start := pre.size, root := some root, trailer := some dict}).1) := by
  apply readXref_span_exact n dict hd raw data count root
  · have hh := Span.of_bytes pre ((s!"{n} 0 obj\n").toUTF8 ++ dict.render ++
        "\nstream\n".toUTF8 ++ raw)
        ("\nendstream\nendobj\n".toUTF8 ++ (s!"startxref\n{pre.size}\n%%EOF\n").toUTF8)
    change Span _ _ (octets ((s!"{n} 0 obj\n").toUTF8 ++ dict.render ++
      "\nstream\n".toUTF8 ++ raw)) at hh
    simpa only [octets_append, ← ByteArray.append_assoc] using hh
  · exact readStartxref_footer_exact _ _ hi
  · exact hl
  · exact hf
  · exact hw
  · exact hc
  · exact hx
  · exact hp
  · exact hr

-- ## Fetching objects

private structure Reader where
  b : ByteArray
  locs : Std.HashMap Nat Loc

/-- Bootstrap an object stream's indirect `/Length`: §7.5.7 excludes
these length objects from object streams. A single direct integer,
never a chain or a recursive dependency on another object stream. -/
private def Reader.directIntAt (r : Reader) (num : Nat) : Option Int := do
  if let some (.direct off) := r.locs.get? num then
    if let .ok (_, .int n, _) := parseIndirectAt r.b off then
      return n
  none

/-- The raw (still encoded) stream bytes after an object's value at `j`,
when `stream` stands there (§7.3.8): `/Length` direct or one indirect hop,
and `endstream` where the length says it ends — a length that stops short
or overruns is refused, never read through. -/
private def Reader.streamAfterWith (r : Reader) (intAt : Nat → Option Int)
    (v : Obj) (j : Nat) :
    Except String (Option ByteArray) := do
  let k := skipWs r.b j
  match keywordAt r.b k "stream" with
  | none => return none
  | some m =>
    let dataStart := if at? r.b m == 13 && at? r.b (m + 1) == 10 then m + 2
      else if at? r.b m == 10 then m + 1 else m
    let len ← match (v.get? "Length") with
      | some (.int n) => pure n
      | some (.ref ln _) =>
        -- Even when enumerated as an ordinary object, an object stream
        -- cannot bootstrap from a compressed length (§7.5.7).
        let length := if v.get? "Type" == some (.name "ObjStm")
          then r.directIntAt ln else intAt ln
        match length with
        | some n => pure n
        | none => throw "malformed PDF: an indirect /Length does not resolve"
      | _ => throw "malformed PDF: a stream has no /Length"
    if len < 0 || dataStart + len.toNat > r.b.size then
      throw "truncated PDF: a stream overruns the file"
    let dataEnd := dataStart + len.toNat
    unless (keywordAt r.b (skipWs r.b dataEnd) "endstream").isSome do
      throw "malformed PDF: a stream's /Length does not reach its endstream"
    return some (r.b.extract dataStart dataEnd)

/-- An object stream (§7.5.7) decoded: its data, the header's
`(objnum, offset)` pairs in order, and `/First`. -/
private def Reader.objStm (r : Reader) (stm : Nat) :
    Except String (ByteArray × Array (Nat × Nat) × Nat) := do
  let some (.direct off) := r.locs.get? stm
    | throw "malformed PDF: an object stream is not at a direct offset"
  let (_, sd, j) ← parseIndirectAt r.b off
  let some raw ← r.streamAfterWith r.directIntAt sd j
    | throw "malformed PDF: an object stream has no data"
  let data ← decodeStream sd raw
  let some n := (sd.get? "N").bind Obj.int?
    | throw "malformed PDF: an object stream has no /N"
  let some first := (sd.get? "First").bind Obj.int?
    | throw "malformed PDF: an object stream has no /First"
  let mut i := 0
  let mut pairs : Array (Nat × Nat) := #[]
  for _ in [0:n.toNat] do
    let some (onum, j1) := parseUInt data (skipWs data i)
      | throw "malformed PDF: unreadable object stream header"
    let some (ooff, j2) := parseUInt data (skipWs data j1)
      | throw "malformed PDF: unreadable object stream header"
    i := j2
    pairs := pairs.push (onum, ooff)
  return (data, pairs, first.toNat)

/-- Fetch the value without reading its stream. A direct object also
returns the position after its value; compressed objects cannot carry
streams (§7.5.7). Separating these readings lets a compressed integer
supply an ordinary stream's length without making object lookup recursive.
An object the table does not list is null (§7.3.10). -/
private def Reader.valueAt (r : Reader) (num : Nat) :
    Except String (Obj × Option Nat) := do
  match r.locs.get? num with
  | none => return (.null, none)
  | some (.direct off) =>
    let (_, v, j) ← parseIndirectAt r.b off
    return (v, some j)
  | some (.inStm stm idx) =>
    let (data, pairs, first) ← r.objStm stm
    let some (_, ooff) := pairs[idx]?
      | throw "malformed PDF: an object stream index is out of range"
    let (v, _) ← parseVal data (first + ooff)
    return (v, none)

/-- One resolved integer, independent of its physical storage. The value
reader's object-stream bootstrap only uses `directIntAt`, so this cannot
re-enter itself, even on cyclic or malformed references. -/
private def Reader.intAt (r : Reader) (num : Nat) : Option Int :=
  (r.valueAt num).toOption.bind (fun (v, _) => v.int?)

/-- Artifact-specific shape facts about the actual value reader: arbitrary
integer values, offsets and object-stream indices, conditional on parsing
those values. These do not claim every arbitrary byte string parses. -/
private theorem Reader.intAt_direct_exact (r : Reader) (num off header j : Nat) (n : Int)
    (hloc : r.locs.get? num = some (.direct off))
    (hval : parseIndirectAt r.b off = .ok (header, .int n, j)) :
    r.intAt num = some n := by
  simp only [Reader.intAt, Reader.valueAt, hloc, hval]
  rfl

private theorem Reader.intAt_compressed_exact (r : Reader) (num stm idx first header off j : Nat)
    (n : Int) (data : ByteArray) (pairs : Array (Nat × Nat))
    (hloc : r.locs.get? num = some (.inStm stm idx))
    (hstm : r.objStm stm = .ok (data, pairs, first))
    (hidx : pairs[idx]? = some (header, off))
    (hval : parseVal data (first + off) = .ok (.int n, j)) :
    r.intAt num = some n := by
  simp only [Reader.intAt, Reader.valueAt, hloc, hstm]
  dsimp only [Bind.bind, Except.bind]
  simp only [hidx, hval]
  rfl

/-- Artifact-specific bootstrap restriction: no compressed entry can
supply an object stream's own length, including a self or mutual cycle. -/
private theorem Reader.directIntAt_compressed_exact (r : Reader) (num stm idx : Nat)
    (hloc : r.locs.get? num = some (.inStm stm idx)) :
    r.directIntAt num = none := by
  simp only [Reader.directIntAt, hloc]

/-- Fetch an object's value and its raw (still encoded) stream, if any. -/
private def Reader.get (r : Reader) (num : Nat) :
    Except String (Obj × Option ByteArray) := do
  let (v, after) ← r.valueAt num
  let raw ← match after with
    | none => pure none
    | some j => r.streamAfterWith r.intAt v j
  return (v, raw)

/-- One level of indirection: a `ref` fetched, anything else unchanged. -/
private def Reader.deref (r : Reader) (o : Obj) : Except String Obj := do
  match o with
  | .ref n _ => return (← r.get n).1
  | _ => return o

/-- Resolve an array before selecting its ordered stream references.
For a single stream retain the original reference, not its dictionary. -/
private def Reader.contentParts (r : Reader) (contents : Obj) : Except String (Array Obj) := do
  match ← r.deref contents with
  | .arr xs => return xs
  | _ => return #[contents]

/-- Artifact-specific: every resolved array is preserved exactly,
including order, multiplicity and the empty value, whichever storage
form supplied it. The premise is the reader's actual dereference. -/
private theorem Reader.contentParts_array_exact (r : Reader) (contents : Obj) (xs : Array Obj)
    (h : r.deref contents = .ok (.arr xs)) :
    r.contentParts contents = .ok xs := by
  simp only [Reader.contentParts, h]
  rfl

/-- Artifact-specific: resolving a single stream's dictionary does not
replace the reference from which the caller reads its stream bytes. -/
private theorem Reader.contentParts_stream_exact (r : Reader) (num gen : Nat)
    (es : Array (String × Obj)) (raw : ByteArray)
    (h : r.get num = .ok (.dict es, some raw)) :
    r.contentParts (.ref num gen) = .ok #[.ref num gen] := by
  simp only [Reader.contentParts, Reader.deref, h]
  rfl

-- ## Every object (§7.5.4, §7.5.7): the substrate a census reads

/-- One object the cross-reference lists, fetched: where the table put it,
the number the file spells beside it — `num gen obj` at a direct offset,
or its object stream's header pair — its value, and its raw (still
encoded) stream bytes when it carries one. `header` is data the reader
keeps rather than a check it made, so `wf` below can restate the check as
a property the type carries. -/
structure Entry where
  num : Nat
  loc : Loc
  header : Nat
  val : Obj
  stream : Option ByteArray
  deriving Inhabited

/-- The file spells the object under the number the table lists it by. -/
def Entry.wf (e : Entry) : Bool := e.header == e.num

def entriesWf (es : Array Entry) : Bool := es.all Entry.wf

/-- **`objects_num_covers`** (the `_covers` statement, artifact-specific:
a fact of the file's own bookkeeping, with no IR statement behind it):
every object `objects` hands back is spelled in the file under the number
the cross-reference lists it by — at its offset, or in its object stream's
header. A cross-reference row pointing at the wrong object, or an object
stream whose header pairs were permuted, is refused by name before this
value exists; the subtype carries the property, as `readForm`'s does. -/
theorem objects_num_covers (es : { es : Array Entry // entriesWf es }) :
    ∀ e ∈ es.val, e.header = e.num := by
  intro e he
  have h := es.property
  simp only [entriesWf, Array.all_eq_true_iff_forall_mem, Entry.wf, beq_iff_eq] at h
  exact h e he

/-- Decode an entry's stream through its declared filter. -/
def Entry.decoded (e : Entry) : Except String (Option ByteArray) :=
  match e.stream with
  | none => pure none
  | some raw => (decodeStream e.val raw).map some

/-- Every object a read cross-reference lists, in object-number order,
each fetched and checked against the number the file spells for it. The
strict reading the engine applies to its own output and a census applies
to any: `startxref` must name the exact start of a section (§7.5.5 — a
tolerant reader skips whitespace, and would pass an offset off by one),
every number lies below the trailer's `/Size`, every object stream's
header agrees with the table, every stream's `/Length` reaches its
`endstream`. Object streams are decoded once each. -/
def objectsOf (b : ByteArray) (x : Xref) :
    Except String { es : Array Entry // entriesWf es } := do
  let s := x.start
  if isWs (at? b s) || at? b s == 256 ||
      (s > 0 && !(isWs (at? b (s - 1)) || isDelim (at? b (s - 1)))) then
    throw "malformed PDF: startxref does not point at the start of a cross-reference section"
  let size? := ((x.trailer.bind (·.get? "Size")).bind Obj.int?).map (·.toNat)
  let r : Reader := { b, locs := x.locs }
  let nums := x.locs.keysArray.qsort (· < ·)
  let mut stms : Std.HashMap Nat (ByteArray × Array (Nat × Nat) × Nat) := {}
  let mut es : Array Entry := #[]
  let mut afters : Std.HashMap Nat Nat := {}
  for num in nums do
    if let some size := size? then
      if num ≥ size then
        throw s!"malformed PDF: object {num} lies beyond the trailer's /Size {size}"
    match x.locs.get? num with
    | none => pure ()
    | some (.direct off) =>
      let (header, val, j) ← parseIndirectAt b off
      if header != num then
        throw s!"malformed PDF: object {num} is not at its cross-referenced offset (the file spells {header} there)"
      afters := afters.insert num j
      es := es.push { num, loc := .direct off, header, val, stream := none }
    | some (.inStm stm idx) =>
      let (data, pairs, first) ← match stms.get? stm with
        | some t => pure t
        | none =>
          let t ← r.objStm stm
          stms := stms.insert stm t
          pure t
      let some (header, ooff) := pairs[idx]?
        | throw s!"malformed PDF: object {num} is indexed beyond object stream {stm}'s header"
      if header != num then
        throw s!"malformed PDF: object stream {stm} lists {header} where the cross-reference names {num}"
      let (val, _) ← parseVal data (first + ooff)
      es := es.push { num, loc := .inStm stm idx, header, val, stream := none }
  -- All values are now available, including compressed length integers.
  -- Reuse them instead of decoding object streams again for each length.
  let ints := es.foldl (fun ints e =>
    match e.val.int? with
    | some n => ints.insert e.num n
    | none => ints) ({} : Std.HashMap Nat Int)
  es ← es.mapM fun e => do
    match afters.get? e.num with
    | none => return e
    | some j =>
      let stream ← r.streamAfterWith ints.get? e.val j
      return { e with stream }
  if h : entriesWf es then
    return ⟨es, h⟩
  else
    throw "malformed PDF: an object's spelled number disagrees with the cross-reference"

def objects (b : ByteArray) : Except String { es : Array Entry // entriesWf es } := do
  unless at? b 0 == 37 && at? b 1 == 80 && at? b 2 == 68 && at? b 3 == 70 do
    throw "not a PDF file (no %PDF header)"
  objectsOf b (← readXref b)

/-- The newest trailer dictionary (§7.5.5): `/Root`, `/Info`, `/Size`. -/
def trailer (b : ByteArray) : Except String Obj := do
  let x ← readXref b
  return x.trailer.getD (.dict #[])

-- ## Page selection (§7.7.3)

/-- A page selected by its physical, one-based position in `/Kids` order. -/
inductive PageSelection where
  | first
  | last
  | number (oneBased : Nat)
  deriving Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

private structure Page where
  node : Obj
  mediaBox : Option Obj
  cropBox : Option Obj
  resources : Option Obj
  rotate : Option Obj

/-- Walk `/Kids` depth-first, counting actual `/Type /Page` leaves and
carrying inheritable attributes (§7.7.3.4). `/Count` never decides a page's
ordinal or whether the traversal is finished. The first or numbered leaf
can return immediately; the last requires an exhausted worklist.
Revisited indirect nodes are malformed, and exhausting the reader's
xref-sized visit bound also refuses, even when a leaf has been seen. -/
private def selectPage (r : Reader) (root : Nat) (selection : PageSelection) :
    Except String (Nat × Page) := do
  if selection == .number 0 then
    throw "PDF page number 0 is invalid; page numbers start at 1"
  let (catalog, _) ← r.get root
  let some pagesRef := catalog.get? "Pages"
    | throw "malformed PDF: the catalog has no /Pages"
  let mut work : Array (Obj × Option Obj × Option Obj × Option Obj × Option Obj) :=
    #[(pagesRef, none, none, none, none)]
  let mut seen : Std.HashMap Nat Unit := {}
  let mut count := 0
  let mut latest : Option (Nat × Page) := none
  for _ in [0:r.locs.size + 2] do
    let some (nodeRef, mb, cb, res, rot) := work.back? | break
    work := work.pop
    if let .ref num _ := nodeRef then
      if seen.contains num then
        throw s!"malformed PDF: cycle or repeated node {num} in the page tree"
      seen := seen.insert num ()
    let node ← r.deref nodeRef
    let mb := (node.get? "MediaBox").or mb
    let cb := (node.get? "CropBox").or cb
    let res := (node.get? "Resources").or res
    -- A declaration overrides inheritance even when its value is zero.
    let rot := (node.get? "Rotate").or rot
    if node.get? "Type" matches some (.name "Page") then
      count := count + 1
      let found : Nat × Page :=
        (count, { node, mediaBox := mb, cropBox := cb, resources := res, rotate := rot })
      if selection == .first || selection == .number count then
        return found
      latest := some found
    else
      match node.get? "Kids" with
      | some (.arr kids) =>
        -- Depth-first: the first kid is visited first, so it is pushed last.
        for k in [0:kids.size] do
          if let some kid := kids[kids.size - 1 - k]? then
            work := work.push (kid, mb, cb, res, rot)
      | _ => throw "malformed PDF: a page tree node has neither /Type /Page nor /Kids"
  unless work.isEmpty do
    throw "malformed PDF: the page tree exceeds its cross-reference"
  match selection, latest with
  | .last, some found => return found
  | .number n, _ =>
    throw s!"PDF page {n} is out of range (the file has {count} pages)"
  | _, _ => throw "malformed PDF: no page found in the page tree"

/-- The shared file validation and selection path for form inclusion and
physical page-number resolution. -/
private def readPage (b : ByteArray) (page : PageSelection) :
    Except String (Reader × (Nat × Page)) := do
  unless at? b 0 == 37 && at? b 1 == 80 && at? b 2 == 68 && at? b 3 == 70 do
    throw "not a PDF file (no %PDF header)"
  let x ← readXref b
  let some root := x.root
    | throw "malformed PDF: no /Root in any trailer"
  let r : Reader := { b, locs := x.locs }
  return (r, ← selectPage r root page)

/-- Resolve a selection to its one-based physical page number, using the
same `/Kids` traversal and selection checks as `readForm`. Contents and
resource streams need not be decoded to resolve an ordinal. -/
def pageNumber (b : ByteArray) (page : PageSelection := .first) : Except String Nat := do
  let (_, selected) ← readPage b page
  return selected.1

-- ## The copied graph, renumbered

/-- A fragment of a serialized object: raw bytes, or a hole naming a copied
object by its local index — the writer fills each hole with its own object
number. Holes are only ever created beside an enqueued target, and `wf`
below re-checks the closure so the guarantee is carried by the type. -/
inductive Chunk where
  | bytes (b : ByteArray)
  | ref (l : Nat)
  deriving Inhabited

/-- One copied object: its serialized value, and its verbatim (still
encoded) stream payload when it has one — a font program is bytes in,
bytes out, never re-parsed. -/
structure XObjOut where
  chunks : Array Chunk
  stream : Option ByteArray := none
  deriving Inhabited

private structure SerSt where
  assign : Std.HashMap Nat Nat := {}
  queue : Array Nat := #[]

private def SerSt.localOf (st : SerSt) (num : Nat) : SerSt × Nat :=
  match st.assign.get? num with
  | some l => (st, l)
  | none =>
    let l := st.queue.size
    ({ assign := st.assign.insert num l, queue := st.queue.push num }, l)

private def pushStr (out : Array Chunk) (s : String) : Array Chunk :=
  out.push (.bytes s.toUTF8)

/-- Re-escape a name on the way out (§7.3.5): regular characters ride,
everything else is `#`-coded. -/
private def nameOut (n : String) : String := Id.run do
  let hexDigit (v : Nat) : Char := ("0123456789ABCDEF".toList[v % 16]?).getD '0'
  let mut out := "/"
  for c in n.toList do
    let v := c.toNat
    if 33 ≤ v && v ≤ 126 && !isDelim v && v != 35 then
      out := out.push c
    else
      out := out ++ String.ofList ['#', hexDigit (v / 16), hexDigit v]
  return out

mutual
/-- Serialize an object into chunks, references becoming holes and their
targets enqueued: the one place a `Chunk.ref` is made. -/
private def serObj (st : SerSt) (out : Array Chunk) : Obj → SerSt × Array Chunk
  | .null => (st, pushStr out "null")
  | .bool true => (st, pushStr out "true")
  | .bool false => (st, pushStr out "false")
  | .int n => (st, pushStr out (toString n))
  | .real raw => (st, pushStr out raw)
  | .str raw => (st, out.push (.bytes raw))
  | .name n => (st, pushStr out (nameOut n))
  | .arr xs =>
    let (st, out) := serList st (pushStr out "[ ") xs.toList
    (st, pushStr out "]")
  | .dict es =>
    let (st, out) := serPairs st (pushStr out "<< ") es.toList
    (st, pushStr out ">>")
  | .ref num _ =>
    let (st, l) := st.localOf num
    (st, out.push (.ref l))

private def serList (st : SerSt) (out : Array Chunk) :
    List Obj → SerSt × Array Chunk
  | [] => (st, out)
  | x :: rest =>
    let (st, out) := serObj st out x
    serList st (pushStr out " ") rest

private def serPairs (st : SerSt) (out : Array Chunk) :
    List (String × Obj) → SerSt × Array Chunk
  | [] => (st, out)
  | (k, v) :: rest =>
    let (st, out) := serObj st (pushStr (pushStr out (nameOut k)) " ") v
    serPairs st (pushStr out " ") rest
end

-- ## The result

/-- A selected page of a read PDF, ready to embed: the page box in sp, the
decoded content, and the `/Resources` graph renumbered into `objects`'
local space. The engine claims the box; the copied streams stay opaque. -/
structure Form where
  x0 : Sp
  y0 : Sp
  x1 : Sp
  y1 : Sp
  content : ByteArray
  resources : Array Chunk
  objects : Array XObjOut
  deriving Inhabited

def Form.w (f : Form) : Sp := f.x1 - f.x0

def Form.h (f : Form) : Sp := f.y1 - f.y0

private def chunksWf (n : Nat) (cs : Array Chunk) : Bool :=
  cs.all fun c => match c with
    | .ref l => l < n
    | .bytes _ => true

/-- Every hole in the copied graph points into `objects`: the writer can
renumber the whole graph without meeting a dangling reference. -/
def Form.wf (f : Form) : Bool :=
  chunksWf f.objects.size f.resources &&
  f.objects.all (fun o => chunksWf f.objects.size o.chunks)

/-- **`resources_closed`** (the `_covers` statement): a form the reader
hands back never carries a dangling reference — every object the copied
page references is copied, renumbered into the local space. This is what
makes "vector stays vector" true in a viewer: a form whose `/Resources`
named a font object the file did not carry would render blank or error.
The reader returns the subtype, so the property is carried by the type:
`readForm`'s one success path checks `wf` and refuses otherwise. -/
theorem resources_closed (f : { f : Form // f.wf }) : f.val.wf = true :=
  f.property

/-- The composite placement map on one axis, as an exact rational
`(numerator, denominator)`: the form's `/Matrix` normalizes its box
`[lo, hi]` to `[0, 1]` (ISO 32000-2 §8.10.1: the matrix maps form space
into the space the `Do` executes in) and the image path's
`cm len 0 0 len' dst dst'` (§8.3.4) maps that to `[dst, dst + len]`.
`placeX lo hi dst len p = ((p - lo) * len + dst * (hi - lo), hi - lo)`. -/
def placeX (lo hi dst len p : Int) : Int × Int :=
  ((p - lo) * len + dst * (hi - lo), hi - lo)

/-- **`form_bbox_exact`**: the placed box is the page box scaled to the
requested size, exactly, in the rational arithmetic the emitted `/Matrix`
and `cm` render to decimals: the box's low edge lands on `dst` and its
high edge on `dst + len` — `value * den = num` is the fraction read
without dividing. The decimal rendering rounds each matrix entry once, at
the ninth digit (`ratString` in the writer), the same one-unit story as
every `Sp.toPtString`. -/
theorem form_bbox_exact (lo hi dst len : Int) (h : lo < hi) :
    (placeX lo hi dst len lo).1 = dst * (placeX lo hi dst len lo).2 ∧
    (placeX lo hi dst len hi).1 = (dst + len) * (placeX lo hi dst len hi).2 ∧
    0 < (placeX lo hi dst len lo).2 := by
  refine ⟨by simp [placeX], ?_, by simp [placeX]; omega⟩
  show (hi - lo) * len + dst * (hi - lo) = (dst + len) * (hi - lo)
  rw [Int.add_mul, Int.mul_comm (hi - lo) len]
  omega

/-- Read a selected page of a PDF into an embeddable form, defaulting to
page 1: the box (CropBox when declared, else MediaBox — pdfTeX's rule for
PDF inclusion), the decoded content streams concatenated, and the resources
graph copied and renumbered. Total over arbitrary bytes; anything the
reader cannot follow is a named error. -/
def readForm (b : ByteArray) (page : PageSelection := .first) :
    Except String { f : Form // f.wf } := do
  let (r, selected) ← readPage b page
  let page := selected.2
  -- The box: CropBox over MediaBox, elements resolved one level and read
  -- as numbers, corners normalized.
  let some boxObj := page.cropBox.or page.mediaBox
    | throw "malformed PDF: the selected page has no /MediaBox"
  let boxObj ← r.deref boxObj
  let nums ← match boxObj with
    | .arr xs =>
      if xs.size != 4 then
        throw "malformed PDF: the page box is not four numbers"
      else
        let mut out : Array Sp := #[]
        for e in xs do
          match (← r.deref e).sp? with
          | some v => out := out.push v
          | none => throw "malformed PDF: an unreadable number in the page box"
        pure out
    | _ => throw "malformed PDF: the page box is not an array"
  let x0 := min (nums[0]?.getD 0) (nums[2]?.getD 0)
  let x1 := max (nums[0]?.getD 0) (nums[2]?.getD 0)
  let y0 := min (nums[1]?.getD 0) (nums[3]?.getD 0)
  let y1 := max (nums[1]?.getD 0) (nums[3]?.getD 0)
  if x0 == x1 || y0 == y1 then
    throw "malformed PDF: the page box is empty"
  match (← r.deref (page.rotate.getD (.int 0))).int?.getD 0 with
  | 0 => pure ()
  | rot => throw s!"PDF page /Rotate {rot} is not supported; re-export unrotated"
  -- The content: one stream or an array, each decoded, joined by newlines
  -- (§7.8.2: the division between streams occurs only between operators).
  let mut content := ByteArray.empty
  match page.node.get? "Contents" with
  | none => pure ()
  | some contents =>
    let parts ← r.contentParts contents
    for part in parts do
      let num ← match part with
        | .ref n _ => pure n
        | _ => throw "malformed PDF: page contents are not references"
      let (cd, raw?) ← r.get num
      let some raw := raw?
        | throw "malformed PDF: a content stream has no data"
      let data ← decodeStream cd raw
      content := content ++ data
      content := content.push 10
  -- The resources graph, copied whole and renumbered.
  let mut st : SerSt := {}
  let resObj := page.resources.getD (.dict #[])
  let (st1, resChunks) := serObj st #[] resObj
  st := st1
  let mut objects : Array XObjOut := #[]
  let mut qi := 0
  for _ in [0:b.size + 2] do
    if qi ≥ st.queue.size then
      break
    let some orig := st.queue[qi]? | break
    qi := qi + 1
    let (v, raw?) ← r.get orig
    match raw? with
    | none =>
      let (st', chunks) := serObj st #[] v
      st := st'
      objects := objects.push { chunks }
    | some raw =>
      -- The dict re-serializes with its `/Length` made direct — the raw
      -- bytes are already in hand — so an indirect length never needs a
      -- copied integer object.
      let es : Array (String × Obj) := match v with
        | .dict es => es.filter (fun kv => kv.1 != "Length")
        | _ => #[]
      let (st', chunks) := serObj st #[]
        (.dict (es.push ("Length", .int raw.size)))
      st := st'
      objects := objects.push { chunks, stream := some raw }
  if qi < st.queue.size then
    throw "malformed PDF: the resource graph is larger than the file"
  let f : Form := { x0, y0, x1, y1, content, resources := resChunks, objects }
  if h : f.wf then
    return ⟨f, h⟩
  else
    throw "malformed PDF: the resource graph did not close"

end LeanTex.Core.PdfRead
