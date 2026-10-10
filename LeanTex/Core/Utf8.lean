module

/-! # Bytes as text

A file the engine reads as UTF-8 reaches it through `readWith` — `read`
where no other encoding stands by — and every byte array reads: `go`
recurses on a measure, so decoding is total by construction, with no fuel.
A well-formed UTF-8 sequence is its scalar; each maximal subpart of an
ill-formed one is one U+FFFD, the substitution the Unicode Standard
recommends (§3.9, "U+FFFD Substitution of Maximal Subparts") and the WHATWG
Encoding Standard's UTF-8 decoder performs. The byte offset of every
replaced subpart travels with the text, so a reader is told where a file is
not UTF-8 instead of the file being refused.

Another encoding can read the bytes UTF-8 does not claim (`decodeWith`);
whatever it is, a file that is UTF-8 reads as UTF-8 (`decodeWith_valid_id`).

The laws: well-formed input reads unchanged (`decode_valid_id`), and a
reading that reports nothing replaced nothing (`decode_accounts`), so the
offsets account for every byte the text does not carry; a well-formed
prefix reads as written and moves the offsets after it
(`decode_valid_prefix_exact`); one byte that starts no character between two
texts is exactly one U+FFFD at its own offset (`decode_one_bad_exact`); a
leading byte-order mark changes nothing but where offsets count from
(`readWith_bom_exact`); and the text a file reads as reads back as itself
(`read_fixed_point`). An ASCII byte of a text's UTF-8 is that character of
the text (`ascii_byte_mem`), so a scan of the bytes answers for the
characters. -/

namespace LeanTex.Core.Utf8

/-- Bytes read as text, and where they were not text. -/
public structure Decoded where
  /-- Each well-formed sequence's scalar, and U+FFFD for each maximal
  ill-formed subpart. -/
  text : String
  /-- The byte offset of each replaced subpart, in reading order. -/
  bad : Array Nat
  deriving Repr, BEq, DecidableEq

private def byteIn (bs : ByteArray) (j : Nat) (lo hi : UInt8) : Bool :=
  match bs[j]? with
  | some b => lo ≤ b && b ≤ hi
  | none => false

/-- What a lead byte asks of the bytes after it, as the WHATWG decoder reads
it: how many continuation bytes, and the range the first of them must fall
in (narrower after E0, ED, F0 and F4, which is how overlong forms,
surrogates and scalars past U+10FFFF are refused at their second byte). -/
private def lead (b : UInt8) : Nat × UInt8 × UInt8 :=
  if b < 0xC2 then (0, 0x80, 0xBF)
  else if b ≤ 0xDF then (1, 0x80, 0xBF)
  else if b == 0xE0 then (2, 0xA0, 0xBF)
  else if b == 0xED then (2, 0x80, 0x9F)
  else if b ≤ 0xEF then (2, 0x80, 0xBF)
  else if b == 0xF0 then (3, 0x90, 0xBF)
  else if b == 0xF4 then (3, 0x80, 0x8F)
  else if b ≤ 0xF3 then (3, 0x80, 0xBF)
  else (0, 0x80, 0xBF)

/-- The length of the maximal subpart at `i`: the lead byte and the
continuation bytes the decoder accepts before the first it refuses, which is
left for the next step. -/
private def subpart (bs : ByteArray) (i : Nat) : Nat :=
  let r := lead (bs[i]?.getD 0)
  if r.1 = 0 || !byteIn bs (i + 1) r.2.1 r.2.2 then 1
  else if r.1 = 1 || !byteIn bs (i + 2) 0x80 0xBF then 2
  else if r.1 = 2 || !byteIn bs (i + 3) 0x80 0xBF then 3
  else 4

/-- The bytes one U+FFFD stands for where the bytes at `i` start no
character: the maximal subpart there, as the decoder consumes it. -/
public def replacedRun (bs : ByteArray) (i : Nat) : Nat := subpart bs i

private theorem subpart_pos (bs : ByteArray) (i : Nat) : 0 < subpart bs i := by
  simp only [subpart]
  split
  · decide
  · split
    · decide
    · split <;> decide

/-- The loop. Where no well-formed sequence starts, the fallback may read
the one byte there as a character of another encoding; otherwise the
maximal subpart is one U+FFFD. -/
private def go (fb : UInt8 → Option Char) (bs : ByteArray) (i : Nat) (out : String)
    (bad : Array Nat) : String × Array Nat :=
  if i < bs.size then
    match bs.utf8DecodeChar? i with
    | some c => go fb bs (i + c.utf8Size) (out.push c) bad
    | none =>
      match fb (bs[i]?.getD 0) with
      | some c => go fb bs (i + 1) (out.push c) bad
      | none => go fb bs (i + subpart bs i) (out.push '�') (bad.push i)
  else (out, bad)
termination_by bs.size - i
decreasing_by
  · have := c.utf8Size_pos; omega
  · omega
  · have := subpart_pos bs i; omega

/-- Decode UTF-8, reading each byte no well-formed sequence claims through
`fb`: the bytes of a file that are not UTF-8 read in the encoding its
document declares, and the rest stay UTF-8. Well-formed input is checked in
one pass and taken whole (`decodeWith_eq_go` holds the fast path to the
loop). -/
public def decodeWith (fb : UInt8 → Option Char) (bs : ByteArray) : Decoded :=
  if h : bs.validateUTF8 = true then
    ⟨String.fromUTF8 bs (ByteArray.validateUTF8_eq_true_iff.mp h), #[]⟩
  else
    let r := go fb bs 0 "" #[]
    ⟨r.1, r.2⟩

private def noFallback : UInt8 → Option Char := fun _ => none

/-- Decode with replacement: every ill-formed subpart is U+FFFD. -/
public def decode (bs : ByteArray) : Decoded := decodeWith noFallback bs


/-- The accumulators are a prefix of the answer: what `go` adds from `i`
does not depend on what it was handed. -/
private theorem go_acc (fb : UInt8 → Option Char) (bs : ByteArray) (i : Nat) (out : String)
    (bad : Array Nat) :
    go fb bs i out bad = (out ++ (go fb bs i "" #[]).1, bad ++ (go fb bs i "" #[]).2) := by
  rw [go.eq_def fb bs i out bad, go.eq_def fb bs i "" #[]]
  split
  · split
    · rename_i c _
      rw [go_acc fb bs (i + c.utf8Size) (out.push c) bad,
        go_acc fb bs (i + c.utf8Size) ("".push c) #[]]
      rw [String.push_eq_append, String.push_eq_append, String.append_assoc, String.empty_append]
      simp
    · split
      · rename_i c _
        rw [go_acc fb bs (i + 1) (out.push c) bad, go_acc fb bs (i + 1) ("".push c) #[]]
        rw [String.push_eq_append, String.push_eq_append, String.append_assoc,
          String.empty_append]
        simp
      · rw [go_acc fb bs (i + subpart bs i) (out.push '�') (bad.push i),
          go_acc fb bs (i + subpart bs i) ("".push '�') (#[].push i)]
        rw [String.push_eq_append, String.push_eq_append, String.append_assoc,
          String.empty_append, Array.push_eq_append, Array.push_eq_append, Array.append_assoc,
          Array.empty_append]
  · simp
termination_by bs.size - i
decreasing_by
  all_goals first
    | (have := Char.utf8Size_pos ‹Char›; omega)
    | omega
    | (have := subpart_pos bs i; omega)


private theorem get?_shift (pre suf : ByteArray) (k : Nat) :
    (pre ++ suf)[pre.size + k]? = suf[k]? := by
  by_cases h : k < suf.size
  · rw [getElem?_pos (pre ++ suf) (pre.size + k) (by rw [ByteArray.size_append]; omega),
      getElem?_pos suf k h, ByteArray.getElem_append_right (by omega)]
    simp
  · rw [getElem?_neg (pre ++ suf) (pre.size + k) (by rw [ByteArray.size_append]; omega),
      getElem?_neg suf k h]

private theorem decodeChar_shift (pre suf : ByteArray) (j : Nat) :
    (pre ++ suf).utf8DecodeChar? (pre.size + j) = suf.utf8DecodeChar? j := by
  rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract,
    ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract (b := suf), ByteArray.size_append,
    ByteArray.extract_append_size_add]

private theorem subpart_shift (pre suf : ByteArray) (j : Nat) :
    subpart (pre ++ suf) (pre.size + j) = subpart suf j := by
  simp only [subpart, byteIn, Nat.add_assoc, get?_shift]
  rfl

/-- Decoding past a prefix is decoding the suffix: what `go` reads at
`pre.size + j` is the suffix's byte `j`, so its answer is the suffix's with
every offset moved by the prefix. -/
private theorem go_shift (fb : UInt8 → Option Char) (pre suf : ByteArray) (j : Nat) :
    go fb (pre ++ suf) (pre.size + j) "" #[] =
      ((go fb suf j "" #[]).1, (go fb suf j "" #[]).2.map (pre.size + ·)) := by
  rw [go.eq_def fb (pre ++ suf) (pre.size + j) "" #[], go.eq_def fb suf j "" #[]]
  simp only [ByteArray.size_append, Nat.add_lt_add_iff_left, decodeChar_shift, subpart_shift,
    get?_shift]
  by_cases hj : j < suf.size
  · simp only [hj, ite_true]
    cases hc : suf.utf8DecodeChar? j with
    | some c =>
      simp only []
      rw [go_acc fb (pre ++ suf), go_acc fb suf, Nat.add_assoc,
        go_shift fb pre suf (j + c.utf8Size)]
      simp
    | none =>
      simp only []
      cases hf : fb (suf[j]?.getD 0) with
      | some c =>
        simp only []
        rw [go_acc fb (pre ++ suf), go_acc fb suf, Nat.add_assoc, go_shift fb pre suf (j + 1)]
        simp
      | none =>
        simp only []
        rw [go_acc fb (pre ++ suf), go_acc fb suf, Nat.add_assoc,
          go_shift fb pre suf (j + subpart suf j)]
        simp
  · simp [hj]
termination_by suf.size - j
decreasing_by
  all_goals first
    | (have := Char.utf8Size_pos ‹Char›; omega)
    | omega
    | (have := subpart_pos suf j; omega)


private theorem size_singleton (c : Char) : [c].utf8Encode.size = c.utf8Size := by
  simp [List.utf8Encode_singleton]

/-- A well-formed prefix decodes to its own characters, and the rest is
decoded as if it stood alone. -/
private theorem go_valid_prefix (fb : UInt8 → Option Char) (l : List Char) (bs : ByteArray) :
    go fb (l.utf8Encode ++ bs) 0 "" #[] =
      (String.ofList l ++ (go fb bs 0 "" #[]).1,
        (go fb bs 0 "" #[]).2.map (l.utf8Encode.size + ·)) := by
  induction l generalizing bs with
  | nil => simp [ByteArray.empty_append]
  | cons c l ih =>
    have hsplit : (c :: l).utf8Encode ++ bs = [c].utf8Encode ++ (l.utf8Encode ++ bs) := by
      rw [List.utf8Encode_cons, ByteArray.append_assoc]
    have hsize : (c :: l).utf8Encode.size = c.utf8Size + l.utf8Encode.size := by
      rw [List.utf8Encode_cons, ByteArray.size_append, size_singleton]
    have hpos : 0 < ([c].utf8Encode ++ (l.utf8Encode ++ bs)).size := by
      rw [ByteArray.size_append, size_singleton]; have := c.utf8Size_pos; omega
    rw [hsplit, go.eq_def]
    simp only [hpos, ↓reduceIte, List.utf8DecodeChar?_utf8Encode_singleton_append]
    rw [go_acc, Nat.zero_add, ← size_singleton c, ← Nat.add_zero [c].utf8Encode.size, go_shift, ih,
      hsize, size_singleton]
    simp only [String.push_eq_append, String.empty_append, String.ofList_cons,
      String.append_assoc, Array.empty_append, Array.map_map]
    refine Prod.ext rfl ?_
    simp only []
    congr 1
    funext x
    simp only [Function.comp_apply]
    omega


private theorem toUTF8_eq_utf8Encode (s : String) : s.toUTF8 = s.toList.utf8Encode := by
  conv => lhs; rw [← String.ofList_toList (s := s)]
  simp

/-- Well-formed bytes decode to the string they encode, with nothing to
report. -/
private theorem go_valid (fb : UInt8 → Option Char) (s : String) :
    go fb s.toUTF8 0 "" #[] = (s, #[]) := by
  have h := go_valid_prefix fb s.toList ByteArray.empty
  rw [ByteArray.append_empty, ← toUTF8_eq_utf8Encode] at h
  rw [h, go.eq_def]
  simp [ByteArray.size_empty]

/-- **The fast path changes nothing.** Well-formed input skips the
replacing loop and is taken whole; the answer is the loop's all the same, so
every statement about the loop is a statement about `decode`. -/
private theorem decodeWith_eq_go (fb : UInt8 → Option Char) (bs : ByteArray) :
    decodeWith fb bs = ⟨(go fb bs 0 "" #[]).1, (go fb bs 0 "" #[]).2⟩ := by
  unfold decodeWith
  split
  · rename_i h
    have hv := ByteArray.validateUTF8_eq_true_iff.mp h
    have := go_valid fb (String.fromUTF8 bs hv)
    simp only [String.toUTF8_eq_toByteArray] at this
    change go fb bs 0 "" #[] = _ at this
    rw [this]
  · rfl

private theorem decode_eq_go (bs : ByteArray) :
    decode bs = ⟨(go noFallback bs 0 "" #[]).1, (go noFallback bs 0 "" #[]).2⟩ :=
  decodeWith_eq_go noFallback bs

/-- **Well-formed input reads unchanged, whatever it might have been read
as.** The UTF-8 of a string decodes to that string with nothing replaced,
and no fallback encoding is ever consulted: a declared encoding cannot
change a file that is UTF-8. -/
public theorem decodeWith_valid_id (fb : UInt8 → Option Char) (s : String) :
    decodeWith fb s.toUTF8 = ⟨s, #[]⟩ := by
  rw [decodeWith_eq_go, go_valid]

/-- **Well-formed input reads unchanged.** Every byte array that is the
UTF-8 of a string decodes to that string with no replacement — the
guarantee that reading a valid file as text loses nothing. -/
public theorem decode_valid_id (s : String) : decode s.toUTF8 = ⟨s, #[]⟩ :=
  decodeWith_valid_id noFallback s

/-- The bytes a character was decoded from are its encoding. -/
private theorem extract_char (bs : ByteArray) (i : Nat) (c : Char)
    (h : bs.utf8DecodeChar? i = some c) :
    bs.extract i (i + c.utf8Size) = (String.utf8EncodeChar c).toByteArray := by
  have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
  rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h
  rw [String.toByteArray_utf8EncodeChar_of_utf8DecodeChar?_eq_some h, ByteArray.extract_extract,
    Nat.add_zero, Nat.min_eq_left hle]

/-- Where `go` replaces nothing from `i` on, its text is the bytes from `i`. -/
private theorem go_accounts (bs : ByteArray) (i : Nat)
    (h : (go noFallback bs i "" #[]).2 = #[]) :
    (go noFallback bs i "" #[]).1.toByteArray = bs.extract i bs.size := by
  rw [go.eq_def] at h ⊢
  by_cases hi : i < bs.size
  · simp only [hi, ↓reduceIte] at h ⊢
    cases hc : bs.utf8DecodeChar? i with
    | some c =>
      simp only [hc] at h ⊢
      rw [go_acc] at h ⊢
      simp only [Array.empty_append] at h
      have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some hc
      rw [String.toByteArray_append, go_accounts bs (i + c.utf8Size) h, String.toByteArray_push,
        String.toByteArray_empty, ByteArray.empty_append, List.utf8Encode_singleton,
        ← extract_char bs i c hc,
        ← ByteArray.extract_eq_extract_append_extract (i + c.utf8Size) (by omega) hle]
    | none =>
      simp only [hc, noFallback] at h
      rw [go_acc] at h
      simp at h
  · simp only [hi, ↓reduceIte, String.toByteArray_empty]
    exact (ByteArray.extract_eq_empty_iff.mpr (by omega)).symm
termination_by bs.size - i
decreasing_by have := Char.utf8Size_pos ‹Char›; omega

/-- **Nothing reported is nothing replaced.** A reading with no offsets is
the bytes themselves: the offsets account for every byte the text does not
carry, so an empty report is a byte-for-byte reading. -/
public theorem decode_accounts (bs : ByteArray) (h : (decode bs).bad = #[]) :
    (decode bs).text.toUTF8 = bs := by
  rw [decode_eq_go] at h ⊢
  rw [String.toUTF8_eq_toByteArray, go_accounts bs 0 h, ByteArray.extract_zero_size]

/-- What `go` reports from `i` on is a byte at or past `i`. -/
private theorem go_bad_mem (fb : UInt8 → Option Char) (bs : ByteArray) (i : Nat)
    (out : String) (bad : Array Nat) (x : Nat) (h : x ∈ (go fb bs i out bad).2) :
    x ∈ bad ∨ (i ≤ x ∧ x < bs.size) := by
  rw [go.eq_def] at h
  split at h
  · rename_i hi
    split at h
    · rename_i c _
      rcases go_bad_mem fb bs (i + c.utf8Size) (out.push c) bad x h with hm | ⟨hl, hr⟩
      · exact Or.inl hm
      · exact Or.inr ⟨by omega, hr⟩
    · split at h
      · rename_i c _
        rcases go_bad_mem fb bs (i + 1) (out.push c) bad x h with hm | ⟨hl, hr⟩
        · exact Or.inl hm
        · exact Or.inr ⟨by omega, hr⟩
      · rcases go_bad_mem fb bs (i + subpart bs i) (out.push '�') (bad.push i) x h with
          hm | ⟨hl, hr⟩
        · rcases Array.mem_push.mp hm with hm | rfl
          · exact Or.inl hm
          · exact Or.inr ⟨Nat.le_refl _, hi⟩
        · exact Or.inr ⟨by omega, hr⟩
  · exact Or.inl h
termination_by bs.size - i
decreasing_by
  all_goals first
    | (have := Char.utf8Size_pos ‹Char›; omega)
    | omega
    | (have := subpart_pos bs i; omega)

/-- **Every offset names a byte of the input.** A replacement's offset is
where its subpart starts in the bytes decoded, never past their end. -/
public theorem decodeWith_bad_between (fb : UInt8 → Option Char) (bs : ByteArray) (x : Nat)
    (h : x ∈ (decodeWith fb bs).bad) : x < bs.size := by
  rw [decodeWith_eq_go] at h
  rcases go_bad_mem fb bs 0 "" #[] x h with hm | ⟨_, hr⟩
  · simp at hm
  · exact hr

public theorem decode_bad_between (bs : ByteArray) (x : Nat) (h : x ∈ (decode bs).bad) :
    x < bs.size :=
  decodeWith_bad_between noFallback bs x h

/-- **A well-formed prefix is read as written.** Decoding the UTF-8 of `s`
followed by any bytes is `s` followed by the decoding of those bytes, every
replacement's offset moved past `s` — so a replacement never reaches back
into text before it. -/
public theorem decode_valid_prefix_exact (s : String) (bs : ByteArray) :
    decode (s.toUTF8 ++ bs) =
      ⟨s ++ (decode bs).text, (decode bs).bad.map (s.utf8ByteSize + ·)⟩ := by
  rw [decode_eq_go, decode_eq_go, toUTF8_eq_utf8Encode, go_valid_prefix, String.ofList_toList,
    ← toUTF8_eq_utf8Encode, String.toUTF8_eq_toByteArray, String.size_toByteArray]


private theorem byteAll {P : UInt8 → Prop} (h : ∀ n : Fin 256, P (UInt8.ofNat n.val)) :
    ∀ x : UInt8, P x := by
  intro x
  simpa using h ⟨x.toNat, x.toNat_lt⟩

/-- A first byte is never a continuation byte. -/
private theorem first_not_cont : ∀ x : UInt8, x.IsUTF8FirstByte → x < 0x80 ∨ 0xC0 ≤ x :=
  byteAll (by decide +kernel)

/-- Every lead's first continuation range lies inside the continuation bytes. -/
private theorem lead_range : ∀ b : UInt8, 0x80 ≤ (lead b).2.1 ∧ (lead b).2.2 ≤ 0xBF :=
  byteAll (by decide +kernel)

private theorem getElem_of_eq {a b : ByteArray} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  subst h; rfl

/-- Text's first byte is a first byte. -/
private theorem first_isFirst (t : String) (h : 0 < t.toUTF8.size) :
    (t.toUTF8[0]'h).IsUTF8FirstByte := by
  obtain ⟨l, rfl⟩ := t.exists_eq_ofList
  cases l with
  | nil => simp at h
  | cons c l =>
    have he : (String.ofList (c :: l)).toUTF8 =
        (String.utf8EncodeChar c).toByteArray ++ l.utf8Encode := by
      rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode_cons,
        List.utf8Encode_singleton]
    rw [getElem_of_eq he 0 h]
    exact ByteArray.isUTF8FirstByte_getElem_zero_utf8EncodeChar_append

private theorem size_one (b : UInt8) : (ByteArray.mk #[b]).size = 1 := rfl

private theorem size_lone (b : UInt8) (t : String) :
    (ByteArray.mk #[b] ++ t.toUTF8).size = t.toUTF8.size + 1 := by
  rw [ByteArray.size_append, size_one]; omega

/-- A byte at or past 0x80 followed by text starts no character: either it
leads none, or the character it leads would need the text's first byte as a
continuation, and a first byte never is one. -/
private theorem lone_none (b : UInt8) (hb : 0x80 ≤ b) (t : String) :
    (ByteArray.mk #[b] ++ t.toUTF8).utf8DecodeChar? 0 = none := by
  cases h : (ByteArray.mk #[b] ++ t.toUTF8).utf8DecodeChar? 0 with
  | none => rfl
  | some c =>
    exfalso
    have henc := String.toByteArray_utf8EncodeChar_of_utf8DecodeChar?_eq_some h
    have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
    rw [size_lone] at hle
    rcases c.utf8Size_eq with h1 | h2 | h3 | h4
    · have hlen : 0 < (String.utf8EncodeChar c).toByteArray.size := by simp [h1]
      have e0 := getElem_of_eq henc 0 hlen
      rw [List.getElem_toByteArray, ByteArray.getElem_extract,
        ByteArray.getElem_append_left (by rw [size_one]; omega)] at e0
      simp only [String.utf8EncodeChar_eq_singleton h1, List.getElem_cons_zero] at e0
      have hb0 : (ByteArray.mk #[b])[0 + 0]'(by rw [size_one]; omega) = b := rfl
      rw [hb0] at e0
      have hv : c.val.toNat ≤ 127 := Char.utf8Size_eq_one_iff.mp h1
      have hbn : 128 ≤ b.toNat := hb
      rw [← e0] at hbn
      simp only [UInt32.toNat_toUInt8] at hbn
      omega
    all_goals
      have hlen : 1 < (String.utf8EncodeChar c).toByteArray.size := by simp; omega
      have e1 := getElem_of_eq henc 1 hlen
      rw [List.getElem_toByteArray, ByteArray.getElem_extract,
        ByteArray.getElem_append_right (by rw [size_one]; omega)] at e1
      have hnot : ¬ ((String.utf8EncodeChar c)[1]'(by simp; omega)).IsUTF8FirstByte := by
        rw [UInt8.isUTF8FirstByte_getElem_utf8EncodeChar]; omega
      rw [e1] at hnot
      simp only [size_one, Nat.zero_add, Nat.sub_self] at hnot
      exact hnot (first_isFirst t (by omega))


/-- A byte that starts no character, before text, is a subpart by itself:
the text's first byte is never a continuation the lead could accept. -/
private theorem subpart_lone (b : UInt8) (t : String) :
    subpart (ByteArray.mk #[b] ++ t.toUTF8) 0 = 1 := by
  have h0 : (ByteArray.mk #[b] ++ t.toUTF8)[0]?.getD 0 = b := by
    rw [getElem?_pos _ 0 (by rw [size_lone]; omega), ByteArray.getElem_append_left (by rw [size_one]; omega)]
    rfl
  have hin : byteIn (ByteArray.mk #[b] ++ t.toUTF8) 1 (lead b).2.1 (lead b).2.2 = false := by
    have hs := get?_shift (ByteArray.mk #[b]) t.toUTF8 0
    rw [size_one] at hs
    simp only [byteIn, hs]
    cases ht : t.toUTF8[0]? with
    | none => rfl
    | some x =>
      obtain ⟨hlt, hx⟩ := getElem?_eq_some_iff.mp ht
      have hf := first_isFirst t hlt
      rw [hx] at hf
      have hr := lead_range b
      rcases first_not_cont x hf with hl | hl
      · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        left
        simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at hl hr ⊢
        simp at hl hr ⊢
        omega
      · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        right
        simp only [UInt8.le_iff_toNat_le] at hl hr ⊢
        simp at hl hr ⊢
        omega
  simp only [subpart, h0, hin, Bool.not_false, Bool.or_true, ↓reduceIte]

/-- One byte that starts no character, before text, reads as one U+FFFD
and then the text. -/
private theorem go_lone (b : UInt8) (hb : 0x80 ≤ b) (t : String) :
    go noFallback (ByteArray.mk #[b] ++ t.toUTF8) 0 "" #[] = ("�" ++ t, #[0]) := by
  rw [go.eq_def]
  simp only [size_lone, Nat.zero_lt_succ, ↓reduceIte, lone_none b hb t, subpart_lone, noFallback]
  rw [go_acc, Nat.zero_add, ← size_one b, ← Nat.add_zero (ByteArray.mk #[b]).size, go_shift,
    go_valid]
  simp only [String.push_eq_append, String.empty_append, Array.map_empty]
  rfl

/-- **The replacement law.** A byte at or past 0x80 that no well-formed
sequence around it can claim — between any two texts — reads as exactly one
U+FFFD, reported at its own offset, and both texts read as written. This is
the acceptance shape of a file with one bad byte: one replacement character
and one offset to name. -/
public theorem decode_one_bad_exact (s t : String) (b : UInt8) (hb : 0x80 ≤ b) :
    decode (s.toUTF8 ++ ByteArray.mk #[b] ++ t.toUTF8) =
      ⟨s ++ "�" ++ t, #[s.utf8ByteSize]⟩ := by
  rw [ByteArray.append_assoc, decode_valid_prefix_exact, decode_eq_go (ByteArray.mk #[b] ++ t.toUTF8),
    go_lone b hb t]
  simp [String.append_assoc]


/-- The byte-order mark: U+FEFF as UTF-8. -/
@[expose] public def bom : ByteArray := ⟨#[0xEF, 0xBB, 0xBF]⟩

private theorem bom_eq : bom = (String.utf8EncodeChar '\uFEFF').toByteArray := rfl

/-- Does a byte-order mark start at `i`? -/
private def bomAt (bs : ByteArray) (i : Nat) : Bool := decide (bs.extract i (i + 3) = bom)

private theorem lt_of_bomAt {bs : ByteArray} {i : Nat} (h : bomAt bs i = true) : i < bs.size := by
  have h := congrArg ByteArray.size (of_decide_eq_true h)
  rw [ByteArray.size_extract] at h
  have : bom.size = 3 := rfl
  omega

/-- The offset of the first byte past the byte-order marks that start at `i`. -/
private def marks (bs : ByteArray) (i : Nat) : Nat :=
  if h : bomAt bs i = true then marks bs (i + 3) else i
termination_by bs.size - i
decreasing_by have := lt_of_bomAt h; omega

/-- How many leading bytes are byte-order marks. Every leading mark is
skipped, not only the first: a second U+FEFF at the very start of a text
joins nothing to nothing, so it is a mark doubled by a tool, never content. -/
public def bomLen (bs : ByteArray) : Nat := marks bs 0

/-- **A file's bytes as text.** Leading byte-order marks are not text and
are skipped, as the WHATWG decoder and LuaTeX's reader skip one; what
follows is decoded with replacement, `fb` reading the bytes UTF-8 does not
claim. Offsets name the file's own bytes, the marks included. -/
public def readWith (fb : UInt8 → Option Char) (bs : ByteArray) : Decoded :=
  let k := bomLen bs
  let d := decodeWith fb (bs.extract k bs.size)
  ⟨d.text, d.bad.map (k + ·)⟩

/-- `readWith` where no other encoding stands by: every byte UTF-8 does not
claim is part of a U+FFFD. -/
public def read (bs : ByteArray) : Decoded := readWith noFallback bs

private theorem bomAt_shift (pre suf : ByteArray) (j : Nat) :
    bomAt (pre ++ suf) (pre.size + j) = bomAt suf j := by
  simp only [bomAt, Nat.add_assoc, ByteArray.extract_append_size_add]

private theorem marks_shift (pre suf : ByteArray) (j : Nat) :
    marks (pre ++ suf) (pre.size + j) = pre.size + marks suf j := by
  rw [marks.eq_def (pre ++ suf), marks.eq_def suf]
  simp only [bomAt_shift]
  split
  · rw [Nat.add_assoc, marks_shift pre suf (j + 3)]
  · rfl
termination_by suf.size - j
decreasing_by have := lt_of_bomAt ‹_›; omega

private theorem extract_min_size (a : ByteArray) (i j : Nat) :
    a.extract i (min j a.size) = a.extract i j := by
  rw [ByteArray.ext_iff]
  simp only [ByteArray.data_extract]
  rw [Array.extract_eq_extract_right]
  have : a.size = a.data.size := rfl
  rw [this]
  omega

/-- The bytes past `marks` start no mark. -/
private theorem marks_stop (bs : ByteArray) (i : Nat) :
    bomAt (bs.extract (marks bs i) bs.size) 0 = false := by
  rw [marks.eq_def]
  split
  · exact marks_stop bs (i + 3)
  · rename_i h
    simp only [Bool.not_eq_true] at h
    rw [← h]
    simp only [bomAt, ByteArray.extract_extract, Nat.add_zero, extract_min_size]
termination_by bs.size - i
decreasing_by have := lt_of_bomAt ‹_›; omega


/-- **A leading mark changes nothing but where offsets count from.** The
text a file reads as is the text it reads as without one more byte-order
mark in front; only the replacement offsets move, by the mark's three
bytes. -/
public theorem readWith_bom_exact (fb : UInt8 → Option Char) (bs : ByteArray) :
    readWith fb (bom ++ bs) = ⟨(readWith fb bs).text, (readWith fb bs).bad.map (3 + ·)⟩ := by
  have h0 : bomAt (bom ++ bs) 0 = true := by
    simp only [bomAt, Nat.zero_add, ByteArray.extract_append_eq_left (a := bom) (b := bs) (i := 3) rfl]
    simp
  have hk : bomLen (bom ++ bs) = 3 + bomLen bs := by
    unfold bomLen
    rw [marks.eq_def]
    simp only [h0, dite_true]
    exact marks_shift bom bs 0
  have he : (bom ++ bs).extract (3 + bomLen bs) (bom ++ bs).size =
      bs.extract (bomLen bs) bs.size := by
    rw [ByteArray.size_append]
    exact ByteArray.extract_append_size_add (a := bom)
  simp only [readWith, hk, he, Array.map_map]
  congr 2
  funext x
  simp only [Function.comp_apply]
  omega

/-- **Every offset names a byte of the file**, marks included. -/
public theorem readWith_bad_between (fb : UInt8 → Option Char) (bs : ByteArray) (x : Nat)
    (h : x ∈ (readWith fb bs).bad) : x < bs.size := by
  simp only [readWith, Array.mem_map] at h
  obtain ⟨y, hy, rfl⟩ := h
  have := decodeWith_bad_between fb _ y hy
  rw [ByteArray.size_extract] at this
  omega

/-- Text whose bytes start with a mark starts with U+FEFF. -/
private theorem head_of_bomAt (t : String) (h : bomAt t.toUTF8 0 = true) :
    t.toList.head? = some '\uFEFF' := by
  have he : t.toUTF8.extract 0 3 = bom := of_decide_eq_true h
  have hlt := lt_of_bomAt h
  have hsize : 3 ≤ t.toUTF8.size := by
    have := congrArg ByteArray.size he
    rw [ByteArray.size_extract] at this
    have : bom.size = 3 := rfl
    omega
  have hsplit : t.toUTF8 = bom ++ t.toUTF8.extract 3 t.toUTF8.size := by
    rw [← he, ← ByteArray.extract_eq_extract_append_extract 3 (by omega) (by omega),
      ByteArray.extract_zero_size]
  have hdec : t.toUTF8.utf8DecodeChar? 0 = some '\uFEFF' := by
    rw [hsplit, bom_eq, ByteArray.utf8DecodeChar?_utf8EncodeChar_append]
  obtain ⟨l, rfl⟩ := t.exists_eq_ofList
  cases l with
  | nil => simp at hlt
  | cons c l =>
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
      List.utf8DecodeChar?_utf8Encode_cons] at hdec
    simp [hdec]

/-- **Text that does not start with U+FEFF reads unchanged**, whatever
encoding stands by for the bytes UTF-8 does not claim. -/
public theorem readWith_valid_id (fb : UInt8 → Option Char) (s : String)
    (h : s.toList.head? ≠ some '\uFEFF') : readWith fb s.toUTF8 = ⟨s, #[]⟩ := by
  have h0 : bomAt s.toUTF8 0 = false := by
    cases hb : bomAt s.toUTF8 0 with
    | false => rfl
    | true => exact absurd (head_of_bomAt s hb) h
  have hk : bomLen s.toUTF8 = 0 := by
    unfold bomLen
    rw [marks.eq_def]
    simp only [h0, Bool.false_eq_true, ↓reduceDIte]
  simp only [readWith, hk, ByteArray.extract_zero_size, decodeWith_valid_id]
  simp

/-- What decoding bytes that start no mark yields starts with no U+FEFF:
the first character is the one the first bytes encode, or U+FFFD. -/
private theorem head_of_decode (e : ByteArray) (h : bomAt e 0 = false) :
    (decode e).text.toList.head? ≠ some '\uFEFF' := by
  rw [decode_eq_go, go.eq_def]
  by_cases hpos : 0 < e.size
  · simp only [hpos, ↓reduceIte]
    cases hc : e.utf8DecodeChar? 0 with
    | some c =>
      simp only []
      rw [go_acc]
      simp only [String.toList_append, String.toList_push, String.toList_empty, List.nil_append,
        List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
      intro hcf
      subst hcf
      have henc := String.toByteArray_utf8EncodeChar_of_utf8DecodeChar?_eq_some hc
      rw [← bom_eq] at henc
      have hb : bomAt e 0 = true := by
        simp only [bomAt]
        have : ('\uFEFF' : Char).utf8Size = 3 := by decide
        rw [this] at henc
        simp [henc]
      rw [hb] at h
      exact Bool.noConfusion h
    | none =>
      simp only [noFallback]
      rw [go_acc]
      simp
  · simp [hpos]

/-- **Reading is idempotent.** The text a file reads as reads back as
itself, with nothing replaced: marks are gone once read, and what remains
is text. -/
public theorem read_fixed_point (bs : ByteArray) :
    read (read bs).text.toUTF8 = ⟨(read bs).text, #[]⟩ :=
  readWith_valid_id noFallback _ (head_of_decode _ (marks_stop bs 0))

/-- `readWith_bom_exact` where no other encoding stands by. -/
public theorem read_bom_exact (bs : ByteArray) :
    read (bom ++ bs) = ⟨(read bs).text, (read bs).bad.map (3 + ·)⟩ :=
  readWith_bom_exact noFallback bs

/-- `readWith_valid_id` where no other encoding stands by. -/
public theorem read_valid_id (s : String) (h : s.toList.head? ≠ some '\uFEFF') :
    read s.toUTF8 = ⟨s, #[]⟩ :=
  readWith_valid_id noFallback s h

private theorem first_lt : ∀ x : UInt8, x.IsUTF8FirstByte → x < 0xF8 :=
  byteAll (by decide +kernel)

/-- **A text's UTF-8 starts below 0xF8**, where every well-formed sequence
starts: no text saved as UTF-8 begins with a UTF-16 byte-order mark. -/
public theorem toUTF8_head_between (s : String) (x : UInt8) (h : s.toUTF8[0]? = some x) :
    x < 0xF8 := by
  obtain ⟨hlt, hx⟩ := getElem?_eq_some_iff.mp h
  have hf := first_isFirst s hlt
  rw [hx] at hf
  exact first_lt x hf

private theorem or80 : ∀ x : UInt8, 0x80 ≤ x ||| 0x80 := byteAll (by decide +kernel)
private theorem orC0 : ∀ x : UInt8, 0x80 ≤ x ||| 0xc0 := byteAll (by decide +kernel)
private theorem orE0 : ∀ x : UInt8, 0x80 ≤ x ||| 0xe0 := byteAll (by decide +kernel)
private theorem orF0 : ∀ x : UInt8, 0x80 ≤ x ||| 0xf0 := byteAll (by decide +kernel)

/-- An ASCII byte in a character's UTF-8 is that character, encoded alone:
every byte of a longer encoding has its high bit set. -/
private theorem ascii_of_mem_encode (c : Char) (b : UInt8) (hb : b < 0x80)
    (h : b ∈ String.utf8EncodeChar c) : c.val.toUInt8 = b ∧ c.utf8Size = 1 := by
  have high (x : UInt8) (hx : 0x80 ≤ x) (he : b = x) : False := by
    subst he; exact absurd hb (UInt8.not_lt.mpr hx)
  rcases c.utf8Size_eq with h1 | h2 | h3 | h4
  · rw [String.utf8EncodeChar_eq_singleton h1, List.mem_singleton] at h
    exact ⟨h.symm, h1⟩
  · rw [String.utf8EncodeChar_eq_cons_cons h2] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · exact (high _ (orC0 _) h).elim
    · exact (high _ (or80 _) h).elim
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h3] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact (high _ (orE0 _) h).elim
    · exact (high _ (or80 _) h).elim
    · exact (high _ (or80 _) h).elim
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h4] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact (high _ (orF0 _) h).elim
    · exact (high _ (or80 _) h).elim
    · exact (high _ (or80 _) h).elim
    · exact (high _ (or80 _) h).elim

/-- **An ASCII byte of a text's UTF-8 is that character of the text.** No
byte below 0x80 occurs inside a longer sequence, so a scan of a text's
bytes for an ASCII character answers for its characters. -/
public theorem ascii_byte_mem (s : String) (c : Char) (hc : c.val < 0x80) (i : Nat)
    (hi : i < s.toUTF8.size) (h : s.toUTF8[i] = c.val.toUInt8) : c ∈ s.toList := by
  have hmem : s.toUTF8[i] ∈ s.toList.flatMap String.utf8EncodeChar := by
    have hl : s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
      rw [toUTF8_eq_utf8Encode, List.utf8Encode, List.toList_data_toByteArray]
    rw [← hl, ByteArray.getElem_eq_getElem_data]
    exact Array.getElem_mem_toList _
  obtain ⟨d, hd, hb⟩ := List.mem_flatMap.mp hmem
  have hc' : c.val.toNat < 128 := UInt32.lt_iff_toNat_lt.mp hc
  have hcb : c.val.toUInt8 < 0x80 := by
    apply UInt8.lt_iff_toNat_lt.mpr
    rw [UInt32.toNat_toUInt8]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hc'
  rw [h] at hb
  obtain ⟨hv, h1⟩ := ascii_of_mem_encode d _ hcb hb
  have hd7 : d.val.toNat ≤ 127 := Char.utf8Size_eq_one_iff.mp h1
  have hvn := congrArg UInt8.toNat hv
  rw [UInt32.toNat_toUInt8, UInt32.toNat_toUInt8] at hvn
  have hceq : d = c := by
    apply Char.ext
    apply UInt32.toNat_inj.mp
    omega
  exact hceq ▸ hd

end LeanTex.Core.Utf8
