import LeanTex.Core.Flate.BitPacking
import LeanTex.Core.Flate.Canonical
import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate

/-! # Flate: inflate and a stored-block deflate

`inflate` decodes a zlib stream (RFC 1950 wrapping RFC 1951 deflate): what a
PNG's IDAT holds. It exists for the PNG forms whose samples cannot pass
through to a PDF `/FlateDecode` stream untouched — an alpha channel must be
split into a colour plane and an SMask, which means really decoding. It is a
total function: every read is bounds-checked, every loop bounded by the
input's bit count or the declared output size, and a malformed stream is an
error value, never a hang or a crash.

`deflateStored` is the way back: a valid zlib stream of stored (uncompressed)
blocks plus the Adler-32, which any inflater — a PDF viewer's included —
accepts. Recompression is not this engine's job; correctness is. -/

private structure Br where
  data : ByteArray
  bitPos : Nat

private def Br.bit (r : Br) : Option (Nat × Br) :=
  match r.data[r.bitPos / 8]? with
  | none => none
  | some b => some ((b.toNat >>> (r.bitPos % 8)) &&& 1, { r with bitPos := r.bitPos + 1 })

/-- Read `n ≤ 16` bits, LSB-first. The accumulator is a `UInt64`: a `Nat`
shift has no scalar fast path in the runtime. -/
private def Br.bits (r : Br) (n : Nat) : Option (Nat × Br) := Id.run do
  let mut r := r
  let mut v : UInt64 := 0
  for k in [0:n] do
    match r.bit with
    | none => return none
    | some (b, r') =>
      v := v ||| (b.toUInt64 <<< k.toUInt64)
      r := r'
  return some (v.toNat, r)

/-- A little-endian bit field in the actual input bytes. -/
def BitField (data : ByteArray) (start width value : Nat) : Prop :=
  start + width ≤ data.size * 8 ∧
    ∀ k < width,
      ((data[(start + k) / 8]?.getD 0).toNat >>> ((start + k) % 8)) &&& 1 =
        (value >>> k) &&& 1

/-- Reading a present field recovers its entire value and advances exactly its width.
This invariant follows the existing early-return loop and its `UInt64` accumulator. -/
theorem bitField_bits_exact (r : Br) (n v : Nat) (hn : n < 64)
    (hv : v < 2 ^ n) (hf : BitField r.data r.bitPos n v) :
    r.bits n = some (v, { r with bitPos := r.bitPos + n }) := by
  have hb (k : Nat) (hk : k < n) :
      ({r with bitPos := r.bitPos + k} : Br).bit =
        some ((v >>> k) &&& 1, {r with bitPos := r.bitPos + (k + 1)}) := by
    have hindex : (r.bitPos + k) / 8 < r.data.size := by
      have := hf.1
      omega
    have heq := hf.2 k hk
    simp only [getElem?_pos r.data ((r.bitPos + k) / 8) hindex, Option.getD_some] at heq
    simp only [Br.bit, getElem?_pos r.data ((r.bitPos + k) / 8) hindex, heq, Nat.add_assoc]
  let P (k : Nat) (s : Option (Option (Nat × Br)) × Br × UInt64) : Prop :=
    s = (none, {r with bitPos := r.bitPos + k}, (v % 2 ^ k).toUInt64)
  unfold Br.bits
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:n] (none, r, (0 : UInt64)) _ :
    Id (Option (Option (Nat × Br)) × Br × UInt64)) = result
  have hloop : P n result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P n) _ 0 n _ (Nat.zero_le _)
      (by simp [P, Nat.mod_one]) _ (fun _ h => h)
    intro k _ hk s hs
    dsimp only [P] at hs
    subst s
    rw [hb k hk]
    change (none, {r with bitPos := r.bitPos + (k + 1)},
      (v % 2 ^ k).toUInt64 ||| (((v >>> k) &&& 1).toUInt64 <<< k.toUInt64)) = _
    congr 2
    apply UInt64.toNat_inj.mp
    rw [BitPacking.appendBit_exact v k (by omega)]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (Nat.mod_lt v (Nat.two_pow_pos (k + 1)))
      (Nat.pow_le_pow_right (by decide) (show k + 1 ≤ 64 by omega)))).symm
  dsimp only [P] at hloop
  rw [hloop]
  simp only [Nat.mod_eq_of_lt hv, Nat.toUInt64, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv
    (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hn)))]


/-- A canonical Huffman table: `counts[len]` codes of each length, and the
symbols in canonical order. The construction never fails; an over-subscribed
set of lengths simply fails to decode, which the caller reports. -/
private structure Huff where
  counts : Array Nat
  symbols : Array Nat

/-- Exact width buckets: zero and widths above the RFC's 15-bit limit do
not contribute to the table, including its unused zero-width bucket. -/
def CountsFor (lengths : List Nat) (counts : Array Nat) : Prop :=
  counts.size = 16 ∧ ∀ k, counts[k]?.getD 0 =
    if 0 < k ∧ k < 16 then lengths.count k else 0

/-- The shared counting loop in both Huffman table builders counts precisely
the widths it has consumed. -/
theorem huffCounts_loop_exact (lengths : Array Nat) :
    CountsFor lengths.toList (Id.run do
      let mut counts := Array.replicate 16 0
      for l in lengths do
        if l > 0 && l < 16 then
          counts := counts.set! l (counts[l]?.getD 0 + 1)
      return counts) := by
  simp only [Id.run, bind, pure]
  apply Progress.forIn_array_exact CountsFor (CountsFor lengths.toList) _ lengths _
  · constructor
    · simp
    · intro k
      by_cases hk : k < 16 <;> simp [hk]
  · intro before l _ _ counts hc
    simp only [Id.run, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hl : 0 < l ∧ l < 16
    · simp only [hl]
      change CountsFor (before ++ [l]) (counts.set! l (counts[l]?.getD 0 + 1))
      refine ⟨by simpa only [Array.size_set!] using hc.1, ?_⟩
      intro k
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases he : l = k
      · subst k
        have hi : l < counts.size := by have := hc.1; omega
        simp only [ite_true, hi, Option.getD_some]
        rw [hc.2 l]
        simp [hl]
      · simp only [he, ite_false, hc.2 k, List.count_append,
          List.count_singleton, beq_iff_eq, Nat.add_zero]
    · simp only [hl, ite_false]
      change CountsFor (before ++ [l]) counts
      refine ⟨hc.1, ?_⟩
      intro k
      rw [hc.2 k, List.count_append, List.count_singleton]
      by_cases hk : 0 < k ∧ k < 16
      · have he : l ≠ k := by rintro rfl; exact hl hk
        simp only [hk, beq_iff_eq, he, ite_false, Nat.add_zero]
      · simp only [hk, ite_false]
  · intro counts hc
    exact hc

private def mkHuff (lengths : Array Nat) : Huff := Id.run do
  let mut counts : Array Nat := Array.replicate 16 0
  for l in lengths do
    if l > 0 && l < 16 then
      counts := counts.set! l (counts[l]! + 1)
  let mut symbols : Array Nat := #[]
  for len in [1:16] do
    for s in [0:lengths.size] do
      if lengths[s]! == len then
        symbols := symbols.push s
  return { counts, symbols }

/-- The decoder's actual table contains exactly the declared width counts. -/
theorem mkHuff_counts_exact (lengths : Array Nat) :
    CountsFor lengths.toList (mkHuff lengths).counts := by
  simpa only [mkHuff, Id.run, bind, pure, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Nat.default_eq_zero] using huffCounts_loop_exact lengths

/-- Decode one symbol, MSB-first, bounded by the 15-bit maximum length. -/
private def Huff.decode (h : Huff) (r : Br) : Option (Nat × Br) := Id.run do
  let mut code := 0
  let mut first := 0
  let mut index := 0
  let mut r := r
  for len in [1:16] do
    match r.bit with
    | none => return none
    | some (b, r') =>
      r := r'
      code := code * 2 + b
      let count := h.counts[len]?.getD 0
      if code < first + count then
        return some (h.symbols[index + (code - first)]?.getD 0, r)
      index := index + count
      first := (first + count) * 2
  return none

/-- A codeword's most-significant-first bits in the actual byte stream. -/
def CodeField (data : ByteArray) (start width code : Nat) : Prop :=
  start + width ≤ data.size * 8 ∧
    ∀ k < width,
      ((data[(start + k) / 8]?.getD 0).toNat >>> ((start + k) % 8)) &&& 1 =
        code / 2 ^ (width - 1 - k) % 2

/-- The actual bounded Huffman decoder recognizes every code in its canonical
interval. Earlier lengths cannot consume a prefix of that code. -/
theorem huff_decode_exact (h : Huff) (r : Br) (width code : Nat)
    (hw : 1 ≤ width ∧ width ≤ 15) (hcode : code < 2 ^ width)
    (hf : CodeField r.data r.bitPos width code)
    (hlo : Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) ≤ code)
    (hhi : code <
      Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) +
        h.counts[width]?.getD 0) :
    h.decode r = some
      (h.symbols[Canonical.index (fun k => h.counts[k]?.getD 0) (width - 1) +
        (code - Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1))]?.getD 0,
        {r with bitPos := r.bitPos + width}) := by
  let count := fun (k : Nat) => h.counts[k]?.getD 0
  let answer := some
    (h.symbols[Canonical.index count (width - 1) +
      (code - Canonical.first count (width - 1))]?.getD 0,
      {r with bitPos := r.bitPos + width})
  let P (k : Nat) (s : Option (Option (Nat × Br)) × Nat × Nat × Nat × Br) : Prop :=
    k ≤ width ∧ s = (none, code / 2 ^ (width + 1 - k),
      Canonical.first count (k - 1), Canonical.index count (k - 1),
      {r with bitPos := r.bitPos + (k - 1)})
  let Q (s : Option (Option (Nat × Br)) × Nat × Nat × Nat × Br) : Prop :=
    s.1 = some answer
  have hb (k : Nat) (hk : 1 ≤ k) (hkw : k ≤ width) :
      ({r with bitPos := r.bitPos + (k - 1)} : Br).bit =
        some (code / 2 ^ (width - k) % 2,
          {r with bitPos := r.bitPos + k}) := by
    have hindex : (r.bitPos + (k - 1)) / 8 < r.data.size := by
      have := hf.1
      omega
    have heq := hf.2 (k - 1) (by omega)
    have he1 : width - 1 - (k - 1) = width - k := by omega
    have he2 : r.bitPos + (k - 1) + 1 = r.bitPos + k := by omega
    simp only [getElem?_pos r.data ((r.bitPos + (k - 1)) / 8) hindex,
      Option.getD_some, he1] at heq
    simp only [Br.bit, getElem?_pos r.data ((r.bitPos + (k - 1)) / 8) hindex,
      heq, he2]
  unfold Huff.decode
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [1:16] (none, 0, 0, 0, r) _ :
    Id (Option (Option (Nat × Br)) × Nat × Nat × Nat × Br)) = result
  have hloop : Q result := by
    rw [← hres]
    apply Progress.forIn_range_exact P Q _ 1 16 _ (by decide) ?_ ?_ ?_
    · simp [P, Canonical.first, Canonical.index, Nat.div_eq_of_lt hcode, hw.1]
    · intro k hk _ s hs
      obtain ⟨hkw, hs⟩ := hs
      subst s
      rw [hb k hk hkw]
      dsimp only
      have he : width + 1 - k = (width - k) + 1 := by omega
      rw [he, Canonical.readBit_prefix_exact]
      by_cases hlast : k = width
      · subst k
        simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
        have hhi' : code <
            Canonical.first count (width - 1) + h.counts[width]?.getD 0 := hhi
        simp only [hhi', ite_true, Id.run, Q, answer]
      · have hskip := Canonical.first_prefix_between count width k code hk (by omega) hlo
        have hskip' : ¬ code / 2 ^ (width - k) <
            Canonical.first count (k - 1) + h.counts[k]?.getD 0 := Nat.not_lt.mpr hskip
        simp only [hskip', ite_false]
        change k + 1 ≤ width ∧
          (none, code / 2 ^ (width - k),
            (Canonical.first count (k - 1) + count k) * 2,
            Canonical.index count (k - 1) + count k,
            {r with bitPos := r.bitPos + k}) = _
        refine ⟨by omega, ?_⟩
        have hk1 : k - 1 + 1 = k := by omega
        have hw1 : width + 1 - (k + 1) = width - k := by omega
        have hfirst : Canonical.first count k =
            (Canonical.first count (k - 1) + count k) * 2 := by
          simpa only [hk1] using
            (show Canonical.first count (k - 1 + 1) =
              (Canonical.first count (k - 1) + count (k - 1 + 1)) * 2 from rfl)
        have hindex : Canonical.index count k =
            Canonical.index count (k - 1) + count k := by
          simpa only [hk1] using
            (show Canonical.index count (k - 1 + 1) =
              Canonical.index count (k - 1) + count (k - 1 + 1) from rfl)
        simp only [hw1, Nat.add_sub_cancel_right, hfirst, hindex]
    · intro s hs
      have := hs.1
      omega
  change result.1 = some answer at hloop
  rw [hloop]

private def lenBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
    67, 83, 99, 115, 131, 163, 195, 227, 258]

private def lenExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4,
    5, 5, 5, 5, 0]

private def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
    769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

private def distExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
    11, 11, 12, 12, 13, 13]

/-- The fixed litlen table (RFC 1951 §3.2.6). -/
private def fixedLit : Huff :=
  mkHuff (Array.ofFn (n := 288) fun i =>
    if i < 144 then 8 else if i < 256 then 9 else if i < 280 then 7 else 8)

private def fixedDist : Huff :=
  mkHuff (Array.replicate 30 5)

/-- The order code-length code lengths arrive in (RFC 1951 §3.2.7). -/
private def clOrder : Array Nat :=
  #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- One compressed block's symbol loop: decode litlen symbols into `out`
until the end-of-block code. Bounded by `maxOut`: a stream that emits more
than the caller declared is malformed for the caller's purpose. -/
private def inflateBlock (lit dist : Huff) (r0 : Br) (out0 : ByteArray)
    (maxOut : Nat) : Except String (ByteArray × Br) := Id.run do
  let mut r := r0
  let mut out := out0
  for _ in [0:maxOut + 2] do
    let some (sym, r1) := lit.decode r
      | return .error "deflate: truncated block"
    r := r1
    if sym == 256 then
      return .ok (out, r)
    else if sym < 256 then
      if out.size ≥ maxOut then
        return .error "deflate: output exceeds the declared size"
      out := out.push (UInt8.ofNat sym)
    else
      let i := sym - 257
      let some base := lenBase[i]? | return .error "deflate: bad length code"
      let some extra := lenExtra[i]? | return .error "deflate: bad length code"
      let some (e, r2) := r.bits extra | return .error "deflate: truncated"
      r := r2
      let len := base + e
      let some (dsym, r3) := dist.decode r | return .error "deflate: truncated"
      r := r3
      let some dbase := distBase[dsym]? | return .error "deflate: bad distance code"
      let some dextra := distExtra[dsym]? | return .error "deflate: bad distance code"
      let some (de, r4) := r.bits dextra | return .error "deflate: truncated"
      r := r4
      let d := dbase + de
      if d == 0 || d > out.size then
        return .error "deflate: distance before the start of output"
      if out.size + len > maxOut then
        return .error "deflate: output exceeds the declared size"
      for _ in [0:len] do
        out := out.push (out[out.size - d]?.getD 0)
  return .error "deflate: block did not end"

/-- Inflate a zlib stream into at most `maxOut` bytes (the caller knows the
size a PNG's samples must have; anything else is malformed). The Adler-32
trailer is not verified: the sample data is judged by its shape, as chunk
CRCs are. -/
def inflate (data : ByteArray) (maxOut : Nat) : Except String ByteArray := Id.run do
  let some cmf := data[0]? | return .error "zlib: empty stream"
  let some flg := data[1]? | return .error "zlib: truncated header"
  if cmf.toNat % 16 != 8 then
    return .error "zlib: not deflate"
  if flg.toNat / 32 % 2 == 1 then
    return .error "zlib: preset dictionary is not supported"
  let mut r : Br := { data, bitPos := 16 }
  let mut out := ByteArray.empty
  -- Every block consumes at least three bits, so the bit count bounds the
  -- block loop.
  for _ in [0:8 * data.size / 3 + 2] do
    let some (bfinal, r1) := r.bit | return .error "deflate: truncated"
    let some (btype, r2) := r1.bits 2 | return .error "deflate: truncated"
    r := r2
    if btype == 0 then
      -- Stored: skip to the byte boundary, LEN, ~LEN, raw copy.
      let byte := (r.bitPos + 7) / 8
      let some l0 := data[byte]? | return .error "deflate: truncated stored block"
      let some l1 := data[byte + 1]? | return .error "deflate: truncated stored block"
      let len := l0.toNat + 256 * l1.toNat
      if byte + 4 + len > data.size then
        return .error "deflate: stored block overruns the stream"
      if out.size + len > maxOut then
        return .error "deflate: output exceeds the declared size"
      out := out ++ data.extract (byte + 4) (byte + 4 + len)
      r := { r with bitPos := 8 * (byte + 4 + len) }
    else if btype == 1 then
      match inflateBlock fixedLit fixedDist r out maxOut with
      | .error e => return .error e
      | .ok (out', r') =>
        out := out'
        r := r'
    else if btype == 2 then
      let some (hlit, ra) := r.bits 5 | return .error "deflate: truncated"
      let some (hdist, rb) := ra.bits 5 | return .error "deflate: truncated"
      let some (hclen, rc) := rb.bits 4 | return .error "deflate: truncated"
      r := rc
      let nlit := hlit + 257
      let ndist := hdist + 1
      let mut clLengths : Array Nat := Array.replicate 19 0
      for k in [0:hclen + 4] do
        let some (v, r') := r.bits 3 | return .error "deflate: truncated"
        r := r'
        clLengths := clLengths.set! (clOrder[k]?.getD 0) v
      let clHuff := mkHuff clLengths
      let mut lengths : Array Nat := #[]
      for _ in [0:nlit + ndist + 1] do
        if lengths.size ≥ nlit + ndist then
          break
        let some (sym, r') := clHuff.decode r | return .error "deflate: truncated"
        r := r'
        if sym < 16 then
          lengths := lengths.push sym
        else if sym == 16 then
          let some (e, r2) := r.bits 2 | return .error "deflate: truncated"
          r := r2
          let some prev := lengths.back? | return .error "deflate: repeat with no previous length"
          for _ in [0:e + 3] do
            lengths := lengths.push prev
        else if sym == 17 then
          let some (e, r2) := r.bits 3 | return .error "deflate: truncated"
          r := r2
          for _ in [0:e + 3] do
            lengths := lengths.push 0
        else
          let some (e, r2) := r.bits 7 | return .error "deflate: truncated"
          r := r2
          for _ in [0:e + 11] do
            lengths := lengths.push 0
      if lengths.size != nlit + ndist then
        return .error "deflate: code lengths overrun their table"
      let lit := mkHuff (lengths.extract 0 nlit)
      let dist := mkHuff (lengths.extract nlit (nlit + ndist))
      match inflateBlock lit dist r out maxOut with
      | .error e => return .error e
      | .ok (out', r') =>
        out := out'
        r := r'
    else
      return .error "deflate: reserved block type"
    if bfinal == 1 then
      return .ok out
  return .error "deflate: no final block"

/-- Adler-32 (RFC 1950 §8.2). Both sums ride in one `UInt64` — `s2` in
the high word, `s1` in the low — and reduce modulo 65521 once per 5552
bytes, zlib's `NMAX`: the longest run after which both still fit their
words. The byte loop then divides nothing and carries one scalar. -/
def adler32 (data : ByteArray) : Nat := Id.run do
  let mut s : UInt64 := 1
  let mut i := 0
  for _ in [0:data.size / 5552 + 1] do
    let stop := min data.size (i + 5552)
    for k in [i:stop] do
      let s1 := (s &&& 0xFFFFFFFF) + (data[k]?.getD 0).toUInt64
      s := (((s >>> 32) + s1) <<< 32) ||| s1
    s := (((s >>> 32) % 65521) <<< 32) ||| ((s &&& 0xFFFFFFFF) % 65521)
    i := stop
  return ((s >>> 32) * 65536 + (s &&& 0xFFFFFFFF)).toNat

/-- Four bytes of `v`'s low 32 bits, most significant first, pushed onto
`b`. One site for the spelling: RFC 1950's Adler trailer, the image cache's
fixed-width header fields and a synthetic sfnt's offsets are the same four
divisions, and a copy that drops a `% 256` is a byte wrong on the boundary
rather than obviously broken. Here beside `fnv64` and `contentKey`, the
byte-level answers the modules above this one share.
-/
def pushBe32 (b : ByteArray) (v : Nat) : ByteArray :=
  (((b.push (UInt8.ofNat (v / 16777216 % 256))).push
    (UInt8.ofNat (v / 65536 % 256))).push
    (UInt8.ofNat (v / 256 % 256))).push (UInt8.ofNat (v % 256))

/-- A zlib stream of stored blocks: bytes back into a shape `/FlateDecode`
accepts, without owning a compressor. -/
def deflateStored (raw : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  out := out.push 0x78
  out := out.push 0x01
  let mut i := 0
  -- One block per 65535 bytes; an empty input still needs its final block.
  for _ in [0:raw.size / 65535 + 2] do
    let len := min 65535 (raw.size - i)
    let final := i + len ≥ raw.size
    out := out.push (if final then 1 else 0)
    out := out.push (UInt8.ofNat (len % 256))
    out := out.push (UInt8.ofNat (len / 256))
    out := out.push (UInt8.ofNat (255 - len % 256))
    out := out.push (UInt8.ofNat (255 - len / 256))
    out := out ++ raw.extract i (i + len)
    i := i + len
    if final then
      break
  return pushBe32 out (adler32 raw)

/-! ## Deflate: a real compressor (RFC 1951)

LZ77 over a hash chain in the 32 KiB window (§2, "distances up to 32K
bytes and lengths up to 258 bytes"), then one dynamic-Huffman block
(§3.2.7) whose two code sets are optimal length-limited Huffman codes
built by boundary package-merge. The engine owns both halves of the round
trip — `deflate` emits only symbols `inflate`'s tables decode — and the
statement is `inflate_deflate_id` (staged in `Obligations/`; the
executable oracle is `scripts/flate-fuzz.lean`, which also cross-checks
every stream against a foreign inflater). Pure and total: every loop is
bounded by the input size or a table's length. -/

/-- A bit writer, LSB-first within each byte (RFC 1951 §3.1.1: "bits of
each byte starting with the least-significant"). Huffman codes arrive
already bit-reversed (`canonCodes`), so one writer serves codes and extra
bits alike. Fewer than eight bits are pending between pushes, so a push
of at most sixteen drains at most two bytes. Fixed-width arithmetic
throughout: `Nat`'s shift is an out-of-line bignum call with no scalar
fast path (measured at ~80 ns; it was three quarters of the compressor). -/
private structure Bw where
  out : ByteArray
  bits : UInt64
  nbits : UInt64

/-- Append `n` bits of `v` (`n ≤ 16`). -/
private def Bw.pushU (w : Bw) (v n : UInt64) : Bw :=
  let bits := w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)
  let nbits := w.nbits + n
  if nbits ≥ 16 then
    { out := (w.out.push bits.toUInt8).push (bits >>> 8).toUInt8
      bits := bits >>> 16
      nbits := nbits - 16 }
  else if nbits ≥ 8 then
    { out := w.out.push bits.toUInt8
      bits := bits >>> 8
      nbits := nbits - 8 }
  else
    { w with bits, nbits }

private def Bw.push (w : Bw) (v n : Nat) : Bw := w.pushU v.toUInt64 n.toUInt64

private def Bw.flush (w : Bw) : ByteArray :=
  if w.nbits == 0 then w.out else w.out.push w.bits.toUInt8

/-- The writer has fewer than one byte pending and no set bits above it. -/
def Bw.Valid (w : Bw) : Prop :=
  w.nbits.toNat < 8 ∧ w.bits.toNat < 2 ^ w.nbits.toNat

theorem pushU_payload_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    (w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)).toNat =
      w.bits.toNat + v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat := by
  have hn64 : n.toNat < 64 := by omega
  have hmask : (v &&& ((1 <<< n) - 1)).toNat = v.toNat % 2 ^ n.toNat := by
    simpa only [Nat.toUInt64, UInt64.ofNat_toNat] using
      BitPacking.takeBits_exact v n.toNat hn64
  have hhi : (v &&& ((1 <<< n) - 1)).toNat < 2 ^ (64 - w.nbits.toNat) := by
    rw [hmask]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by have := hw.1; omega))
  have hp := BitPacking.packBits_exact
    (v &&& ((1 <<< n) - 1)).toNat w.bits.toNat w.nbits.toNat
    (by have := hw.1; omega) hw.2 hhi
  simp only [Nat.toUInt64, UInt64.ofNat_toNat] at hp
  rw [hmask] at hp
  simpa only [UInt64.or_comm, Nat.add_comm] using hp

theorem pushU_payload_between (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    (w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)).toNat <
      2 ^ (w.nbits.toNat + n.toNat) := by
  rw [pushU_payload_exact w v n hw hn, Nat.add_comm, Nat.pow_add]
  have hm := Nat.mod_lt v.toNat (Nat.two_pow_pos n.toNat)
  calc
    v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat + w.bits.toNat
      < v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat + 2 ^ w.nbits.toNat :=
        Nat.add_lt_add_left hw.2 _
    _ = (v.toNat % 2 ^ n.toNat + 1) * 2 ^ w.nbits.toNat := by
      rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 2 ^ n.toNat * 2 ^ w.nbits.toNat := Nat.mul_le_mul_right _ hm
    _ = _ := Nat.mul_comm _ _


/-- Draining the packed payload emits exactly its complete bytes and retains
exactly its high, incomplete byte. No runtime arithmetic wraps. -/
theorem pushU_pending_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    let total := w.nbits.toNat + n.toNat
    let payload := w.bits.toNat + v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat
    (w.pushU v n).nbits.toNat = total % 8 ∧
      (w.pushU v n).bits.toNat = payload / 2 ^ (total / 8 * 8) ∧
      (w.pushU v n).out.size = w.out.size + total / 8 := by
  have hw8 := hw.1
  have hsum : (w.nbits + n).toNat = w.nbits.toNat + n.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hp := pushU_payload_exact w v n hw hn
  dsimp only
  unfold Bw.pushU
  dsimp only
  split
  · rename_i h16
    have ht : 16 ≤ w.nbits.toNat + n.toNat := by
      simpa [UInt64.le_iff_toNat_le, hsum] using h16
    have hd : (w.nbits.toNat + n.toNat) / 8 = 2 := by omega
    simp only [UInt64.toNat_sub_of_le _ _ h16, hsum, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow, hp, ByteArray.size_push, hd, UInt64.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
    constructor
    · omega
    · constructor
      · trivial
      · trivial
  · rename_i h16
    have ht : w.nbits.toNat + n.toNat < 16 := by
      simp [UInt64.le_iff_toNat_le, hsum] at h16
      omega
    split
    · rename_i h8
      have ht8 : 8 ≤ w.nbits.toNat + n.toNat := by
        simpa [UInt64.le_iff_toNat_le, hsum] using h8
      have hd : (w.nbits.toNat + n.toNat) / 8 = 1 := by omega
      simp only [UInt64.toNat_sub_of_le _ _ h8, hsum, UInt64.toNat_shiftRight,
        Nat.shiftRight_eq_div_pow, hp, ByteArray.size_push, hd, UInt64.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
      constructor
      · omega
      · exact ⟨trivial, trivial⟩
    · rename_i h8
      have ht8 : w.nbits.toNat + n.toNat < 8 := by
        simp [UInt64.le_iff_toNat_le, hsum] at h8
        omega
      simp only [hsum, hp, Nat.div_eq_of_lt ht8, Nat.mod_eq_of_lt ht8,
        Nat.zero_mul, Nat.pow_zero, Nat.div_one, Nat.add_zero, and_self]


/-- The pending-bit invariant is preserved by every supported writer push. -/
theorem pushU_valid (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) : (w.pushU v n).Valid := by
  have hp := pushU_pending_exact w v n hw hn
  have hb := pushU_payload_between w v n hw hn
  rw [pushU_payload_exact w v n hw hn] at hb
  unfold Bw.Valid
  constructor
  · rw [hp.1]
    exact Nat.mod_lt _ (by decide)
  · rw [hp.1, hp.2.1]
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    rw [← Nat.pow_add]
    have he : (w.nbits.toNat + n.toNat) % 8 +
        (w.nbits.toNat + n.toNat) / 8 * 8 = w.nbits.toNat + n.toNat := by omega
    rw [he]
    exact hb

/-- A push advances the bit position by exactly its field width. -/
theorem pushU_position_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    8 * (w.pushU v n).out.size + (w.pushU v n).nbits.toNat =
      8 * w.out.size + w.nbits.toNat + n.toNat := by
  have hp := pushU_pending_exact w v n hw hn
  rw [hp.1, hp.2.2]
  omega


/-- Optimal length-limited Huffman code lengths by boundary package-merge
(Larmore & Hirschberg 1990): lengths ≤ `limit`, zero for a symbol never
seen, and a single-symbol alphabet gets the one-bit code RFC 1951 §3.2.7
expects. Sound whenever the live alphabet fits the limit (`n ≤ 2^limit`;
286 ≤ 2¹⁵ and 19 ≤ 2⁷ for the two uses here). The counting formulation:
with items sorted ascending and a leaf preferred on weight ties, the
leaves inside any package-list prefix are the rarest symbols, so each
level only records which of its packages are leaves, and the walk back
from the solution prefix (2n−2 packages) adds one bit to the `leaves`
rarest symbols per level — no symbol sets, no per-level sort. -/
private def pmLengths (freqs : Array Nat) (limit : Nat) : Array Nat := Id.run do
  let syms := (Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0
  let n := syms.size
  if n == 0 then
    return Array.replicate freqs.size 0
  if n == 1 then
    return (Array.replicate freqs.size 0).set! (syms[0]?.getD 0) 1
  let sorted := syms.qsort fun a b => (freqs[a]?.getD 0) < (freqs[b]?.getD 0)
  let itemW := sorted.map fun s => freqs[s]?.getD 0
  let mut weights : Array Nat := itemW
  let mut leafFlags : Array Bool := Array.replicate n true
  let mut levels : Array (Array Bool) := #[]
  for _ in [1:limit] do
    levels := levels.push leafFlags
    let mut mw : Array Nat := #[]
    let mut k := 0
    for _ in [0:weights.size / 2] do
      mw := mw.push ((weights[k]?.getD 0) + (weights[k + 1]?.getD 0))
      k := k + 2
    -- Merge the (sorted) items back in, leaf first on ties.
    let mut w2 : Array Nat := Array.mkEmpty (n + mw.size)
    let mut f2 : Array Bool := Array.mkEmpty (n + mw.size)
    let mut a := 0
    let mut b := 0
    for _ in [0:n + mw.size] do
      if a < n && (b ≥ mw.size || itemW[a]?.getD 0 ≤ mw[b]?.getD 0) then
        w2 := w2.push (itemW[a]?.getD 0)
        f2 := f2.push true
        a := a + 1
      else if b < mw.size then
        w2 := w2.push (mw[b]?.getD 0)
        f2 := f2.push false
        b := b + 1
    weights := w2
    leafFlags := f2
  levels := levels.push leafFlags
  let mut lens := Array.replicate freqs.size 0
  let mut take := 2 * n - 2
  for li in [0:levels.size] do
    let flags := levels[levels.size - 1 - li]?.getD #[]
    let mut leaves := 0
    let mut merged := 0
    for j in [0:take] do
      if flags[j]?.getD true then leaves := leaves + 1 else merged := merged + 1
    for j in [0:leaves] do
      let s := sorted[j]?.getD 0
      lens := lens.set! s (lens[s]?.getD 0 + 1)
    take := 2 * merged
    if take == 0 then break
  return lens

/-- Canonical codes from lengths — the same assignment `mkHuff` decodes
(RFC 1951 §3.2.2), each code's bits reversed so the LSB-first writer
emits them most-significant first as §3.1.1 requires. -/
private def canonCodes (lengths : Array Nat) : Array Nat := Id.run do
  let mut blCount := Array.replicate 16 0
  for l in lengths do
    if l > 0 && l < 16 then
      blCount := blCount.set! l (blCount[l]?.getD 0 + 1)
  let mut nextCode := Array.replicate 16 0
  let mut code := 0
  for b in [1:16] do
    code := (code + blCount[b - 1]?.getD 0) * 2
    nextCode := nextCode.set! b code
  let mut codes := Array.replicate lengths.size 0
  for s in [0:lengths.size] do
    let l := lengths[s]?.getD 0
    if l > 0 then
      let c := nextCode[l]?.getD 0
      nextCode := nextCode.set! l (c + 1)
      let mut rev := 0
      let mut v := c
      for _ in [0:l] do
        rev := rev * 2 + v % 2
        v := v / 2
      codes := codes.set! s rev
  return codes

/-- The bit-reversal loop used by `canonCodes` has exactly the declared bit order.
The invariant records both the reversed prefix and the unconsumed code suffix. -/
theorem canonCodes_reverseBits_exact (code width : Nat) :
    (Id.run do
      let mut rev := 0
      let mut v := code
      for _ in [0:width] do
        rev := rev * 2 + v % 2
        v := v / 2
      return rev) = Canonical.reverseBits code width := by
  let P (k : Nat) (s : Nat × Nat) : Prop :=
    s = (Canonical.reverseBits code k, code / 2 ^ k)
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:width] (0, code) _ : Id (Nat × Nat)) = result
  have hloop : P width result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P width) _ 0 width _ (Nat.zero_le _)
      (by simp [P, Canonical.reverseBits]) _ (fun _ h => h)
    intro k _ _ s hs
    dsimp only [P] at hs
    subst s
    change (Canonical.reverseBits code k * 2 + code / 2 ^ k % 2,
      code / 2 ^ k / 2) = _
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    rfl
  dsimp only [P] at hloop
  rw [hloop]

/-- Largest length code whose base is ≤ `len` — code 285 alone covers 258
(RFC 1951 §3.2.5's table). -/
private def lenSymOf (len : Nat) : Nat := Id.run do
  let mut sym := 0
  for k in [0:lenBase.size] do
    if lenBase[k]?.getD 999 ≤ len then sym := k
  return sym

private def distSymOf (d : Nat) : Nat := Id.run do
  let mut sym := 0
  for k in [0:distBase.size] do
    if distBase[k]?.getD 99999 ≤ d then sym := k
  return sym

/-- `len → length code`, indexed directly by the length (3–258). -/
private def lenSymTab : Array Nat := (Array.range 259).map lenSymOf

/-- `dist → distance code` for distances ≤ 256. -/
private def distSymTab1 : Array Nat := (Array.range 257).map distSymOf

/-- Distances past 256 bucket by `(d-1) >>> 7`: every base past 256 is
≡ 1 (mod 128), so a bucket never straddles two codes. -/
private def distSymTab2 : Array Nat := (Array.range 256).map fun k => distSymOf (k * 128 + 1)

/-- One LZ77 token: a literal byte, or bit 31 set with `(len-3) <<< 15`
and `dist-1` packed beside it. -/
private def matchToken (len dist : Nat) : UInt32 :=
  (0x80000000 : UInt32) ||| ((len - 3).toUInt32 <<< 15) ||| (dist - 1).toUInt32

/-- Match payload and tag occupy disjoint bits throughout the RFC range. -/
theorem matchToken_toNat (len dist : Nat) (hl : 3 ≤ len ∧ len ≤ 258)
    (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    (matchToken len dist).toNat = 2147483648 + (len - 3) * 32768 + (dist - 1) := by
  have hlow31 : (len - 3) * 32768 + (dist - 1) < 2 ^ 31 := by omega
  have hl32 : len - 3 < 2 ^ 32 := by omega
  have hd32 : dist - 1 < 2 ^ 32 := by omega
  have hs32 : (len - 3) * 32768 < 2 ^ 32 := by clear hlow31; omega
  have hd15 : dist - 1 < 2 ^ 15 := by omega
  simp only [matchToken, UInt32.toNat_or, UInt32.toNat_shiftLeft, Nat.toUInt32,
    UInt32.toNat_ofNat', UInt32.reduceToNat, Nat.reduceMod,
    Nat.mod_eq_of_lt hl32, Nat.mod_eq_of_lt hd32, Nat.shiftLeft_eq,
    Nat.reducePow, Nat.mod_eq_of_lt hs32]
  rw [Nat.or_assoc]
  have hlo : ((len - 3) * 32768 ||| (dist - 1)) =
      (len - 3) * 32768 + (dist - 1) := by
    simpa only [Nat.shiftLeft_eq, Nat.reducePow] using
      BitPacking.or_shift_exact (len - 3) (dist - 1) 15 hd15
  rw [hlo, Nat.or_comm]
  change _ ||| 2 ^ 31 = _
  rw [Nat.or_two_pow_eq_add_of_lt hlow31]
  simp only [Nat.reducePow, Nat.add_assoc, Nat.add_comm]

/-- The actual scalar token reader recovers both fields without truncation. -/
theorem matchToken_fields_exact (len dist : Nat) (hl : 3 ≤ len ∧ len ≤ 258)
    (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    (((matchToken len dist >>> 15) &&& 255).toNat + 3 = len) ∧
      ((matchToken len dist &&& 32767).toNat + 1 = dist) ∧
      256 ≤ (matchToken len dist).toNat := by
  simp only [UInt32.toNat_and, UInt32.toNat_shiftRight, UInt32.reduceToNat,
    Nat.reduceMod, matchToken_toNat len dist hl hd, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  have mask8 (x : Nat) : x &&& 255 = x % 256 :=
    Nat.and_two_pow_sub_one_eq_mod x 8
  have mask15 (x : Nat) : x &&& 32767 = x % 32768 :=
    Nat.and_two_pow_sub_one_eq_mod x 15
  rw [mask8, mask15]
  omega


/-- A match token read back: its length, its distance, and the distance
code that distance selects — the inverse of `matchToken`'s packing, spelled
once for the two loops that read every token (frequencies, then bits). The
bit work stays in `UInt32`: a `Nat` shift is an out-of-line bignum call
with no scalar fast path, which is `Bw`'s own lesson one loop out. -/
private def matchOf (t : UInt32) : Nat × Nat × Nat :=
  let distBits := t &&& 32767
  let dist := distBits.toNat + 1
  ((((t >>> 15) &&& 255).toNat + 3, dist,
    if dist ≤ 256 then distSymTab1[dist]?.getD 0
    else distSymTab2[(distBits >>> 7).toNat]?.getD 0))

/-- The three-byte rolling hash: Knuth's multiplicative constant over the
window the next match must open with. `UInt64` arithmetic — the product
stays under 2⁵⁶ — for the same reason as `Bw`; one bounds check covers
the three reads. Callers only ask where the window is whole. -/
private def hash3 (raw : ByteArray) (mask i : Nat) : Nat :=
  if h : i + 2 < raw.size then
    (((((raw[i]'(by omega)).toUInt64 <<< 16) ^^^ ((raw[i + 1]'(by omega)).toUInt64 <<< 8) ^^^
      raw[i + 2].toUInt64) * 2654435761) >>> 17 &&& mask.toUInt64).toNat
  else 0

/-- Longest common run at `c`/`i`, `fuel` the caller's bound (`limit ≤
258`, in range by the caller's `c < i` and `limit ≤ raw.size - i`). Tail
recursion: the byte loop carries no boxed loop state — this is the
innermost loop of the compressor — and `c < i` makes one bounds check
serve both reads. -/
private def matchLen (raw : ByteArray) (c i : Nat) (hci : c < i) : Nat → Nat → Nat
  | 0, l => l
  | fuel + 1, l =>
    if h : i + l < raw.size then
      if raw[c + l]'(by omega) == raw[i + l] then matchLen raw c i hci fuel (l + 1) else l
    else l

theorem matchLen_between (raw : ByteArray) (c i : Nat) (hci : c < i)
    (fuel l : Nat) (hl : l ≤ raw.size - i) :
    l ≤ matchLen raw c i hci fuel l ∧
      matchLen raw c i hci fuel l ≤ min (l + fuel) (raw.size - i) := by
  induction fuel generalizing l with
  | zero => simp [matchLen, hl]
  | succ fuel ih =>
    rw [matchLen]
    split
    · split
      · have hm := ih (l + 1) (by omega)
        simp only [Nat.le_min] at hm ⊢
        omega
      · simp [Nat.le_min, hl]
    · simp [Nat.le_min, hl]

theorem matchLen_agree (raw : ByteArray) (c i : Nat) (hci : c < i)
    (fuel l k : Nat) (hlo : l ≤ k) (hhi : k < matchLen raw c i hci fuel l) :
    raw[c + k]? = raw[i + k]? := by
  induction fuel generalizing l with
  | zero => simp only [matchLen] at hhi; omega
  | succ fuel ih =>
    rw [matchLen] at hhi
    split at hhi
    · rename_i hin
      split at hhi
      · rename_i heq
        by_cases hkl : k = l
        · subst k
          simpa [getElem?_pos, hin, show c + l < raw.size by omega] using
            congrArg some (beq_iff_eq.mp heq)
        · exact ih (l + 1) (by omega) hhi
      · omega
    · omega

/-- The hash tables as one array: `head` in the first `mask + 1` slots,
the `prev` ring in the next — one value threads the walk, no pair to
allocate per step. -/
private def prevSlot (mask c : Nat) : Nat := mask + 1 + (c &&& mask)

/-- A match packed for return: `len <<< 16 ||| dist`, a scalar. -/
private def packMatch (len dist : Nat) : UInt64 :=
  (len.toUInt64 <<< 16) ||| dist.toUInt64

theorem packMatch_exact (len dist : Nat) (hl : len < 2 ^ 48) (hd : dist < 65536) :
    (packMatch len dist >>> 16).toNat = len ∧
      (packMatch len dist &&& 65535).toNat = dist := by
  exact BitPacking.unpackBits_exact len dist 16 (by decide) hd hl

/-- Walk the hash chain for the best match at `i`: candidates verified
byte-wise (a stale ring entry can only cost a candidate, never
correctness), the walk cut short by a match of 64+ (zlib's `good_length`
shape). -/
private def bestMatch (raw : ByteArray) (tab : Array Nat) (mask i limit : Nat) :
    Nat → Nat → Nat → Nat → UInt64
  | 0, _, best, bestDist => packMatch best bestDist
  | fuel + 1, c, best, bestDist =>
    if hci : c < i then
      if i - c > 32768 || best ≥ 64 || best == limit then packMatch best bestDist
      else
        -- A longer match must extend past `best`: one compare rejects most.
        let next := tab[prevSlot mask c]?.getD i
        let longer := if h : i + best < raw.size then raw[c + best]'(by omega) == raw[i + best]
          else false
        if longer then
          let l := matchLen raw c i hci limit 0
          if l > best then bestMatch raw tab mask i limit fuel next l (i - c)
          else bestMatch raw tab mask i limit fuel next best bestDist
        else bestMatch raw tab mask i limit fuel next best bestDist
    else packMatch best bestDist

/-- A verified source match. Zero length is the initial search result; every
positive result stays within the input and the RFC 1951 distance window. -/
def Backref (raw : ByteArray) (i len dist : Nat) : Prop :=
  dist ≤ 32768 ∧
    (len = 0 ∨
      (0 < dist ∧ dist ≤ i ∧ i + len ≤ raw.size ∧
        ∀ k < len, raw[i - dist + k]? = raw[i + k]?))

private theorem bestMatch_run (raw : ByteArray) (tab : Array Nat) (mask i limit : Nat)
    (fuel c best dist : Nat) (hbest : best ≤ limit)
    (hmatch : Backref raw i best dist) :
    ∃ len d, bestMatch raw tab mask i limit fuel c best dist = packMatch len d ∧
      best ≤ len ∧ len ≤ limit ∧ Backref raw i len d := by
  induction fuel generalizing c best dist with
  | zero =>
    exact ⟨best, dist, rfl, Nat.le_refl _, hbest, hmatch⟩
  | succ fuel ih =>
    rw [bestMatch]
    split
    · rename_i hci
      split
      · exact ⟨best, dist, rfl, Nat.le_refl _, hbest, hmatch⟩
      · rename_i hgo
        dsimp only
        generalize hlonger : (if h : i + best < raw.size then
          raw[c + best]'(by omega) == raw[i + best] else false) = longer
        split
        · split
          · rename_i hlong
            have hm := matchLen_between raw c i hci limit 0 (Nat.zero_le _)
            simp only [Nat.zero_add, Nat.le_min] at hm
            have href : Backref raw i (matchLen raw c i hci limit 0) (i - c) := by
              refine ⟨?_, Or.inr ⟨by omega, by omega, by omega, ?_⟩⟩
              · simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at hgo
                omega
              · intro k hk
                rw [Nat.sub_sub_self (Nat.le_of_lt hci)]
                exact matchLen_agree raw c i hci limit 0 k (Nat.zero_le _) hk
            obtain ⟨len, d, heq, hlo, hhi, hd⟩ :=
              ih _ _ _ hm.2.1 href
            exact ⟨len, d, heq, by omega, hhi, hd⟩
          · exact ih _ _ _ hbest hmatch
        · exact ih _ _ _ hbest hmatch
    · exact ⟨best, dist, rfl, Nat.le_refl _, hbest, hmatch⟩

/-- Hash contents only choose candidates; each returned byte has been compared
to the input. The field-width premise prevents scalar result truncation. -/
theorem bestMatch_covers (raw : ByteArray) (tab : Array Nat) (mask i limit : Nat)
    (hlimit : limit < 2 ^ 48) (fuel c best dist : Nat) (hbest : best ≤ limit)
    (hmatch : Backref raw i best dist) :
    let m := bestMatch raw tab mask i limit fuel c best dist
    best ≤ (m >>> 16).toNat ∧ (m >>> 16).toNat ≤ limit ∧
      Backref raw i (m >>> 16).toNat (m &&& 65535).toNat := by
  obtain ⟨len, d, heq, hlo, hhi, hd⟩ :=
    bestMatch_run raw tab mask i limit fuel c best dist hbest hmatch
  dsimp only
  rw [heq]
  have hp := packMatch_exact len d (by omega) (by have := hd.1; omega)
  rw [hp.1, hp.2]
  exact ⟨hlo, hhi, hd⟩


/-- Enter positions `j, j+1, …` (`fuel` many) into the hash tables. -/
private def insertHashes (raw : ByteArray) (mask : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, tab => tab
  | fuel + 1, j, tab =>
    if j + 3 ≤ raw.size then
      let hj := hash3 raw mask j
      let old := tab[hj]?.getD j
      insertHashes raw mask fuel (j + 1) ((tab.set! hj j).set! (prevSlot mask j) old)
    else
      tab

/-- One LZ77 step per call, `fuel` bounding the walk (every step advances
`i` by at least one): greedy longest-match, and the interior positions of
a long match left out of the table (zlib's fast strategy) so runs cost
O(1) per match, not per byte. -/
private def tokGo (raw : ByteArray) (mask : Nat) :
    Nat → Nat → Array Nat → Array UInt32 → Array UInt32
  | 0, _, _, tokens => tokens
  | fuel + 1, i, tab, tokens =>
    let n := raw.size
    if i ≥ n then tokens
    else if i + 3 > n then
      tokGo raw mask fuel (i + 1) tab (tokens.push (raw[i]?.getD 0).toUInt32)
    else
      let h := hash3 raw mask i
      let limit := min 258 (n - i)
      let m := bestMatch raw tab mask i limit 32 (tab[h]?.getD i) 0 0
      let best := (m >>> 16).toNat
      if best ≥ 3 then
        let tab := insertHashes raw mask (if best ≤ 32 then best else 1) i tab
        tokGo raw mask fuel (i + best) tab (tokens.push (matchToken best (m &&& 65535).toNat))
      else
        let old := tab[h]?.getD i
        tokGo raw mask fuel (i + 1) ((tab.set! h i).set! (prevSlot mask i) old)
          (tokens.push (raw[i]?.getD 0).toUInt32)

/-- LZ77 over a hash chain, chain bounded at 32 candidates. The table
scales with the input — allocating and zeroing 64K entries is the whole
cost of deflating a 2 KiB content stream — and a smaller ring only ever
loses candidates, never correctness. `raw.size` is the sentinel: no
position yet under this hash. -/
private def tokenize (raw : ByteArray) : Array UInt32 :=
  let n := raw.size
  let mask := if n ≥ 65536 then 32767 else 4095
  tokGo raw mask n 0 (Array.replicate (2 * (mask + 1)) n) #[]

/-- The tokens spell exactly the indicated input interval. A match may overlap
its own destination: the byte equality quantifies over every copied position. -/
inductive TokensFor (raw : ByteArray) : Nat → Array UInt32 → Nat → Prop
  | empty (i : Nat) (hi : i ≤ raw.size) : TokensFor raw i #[] i
  | literal {start i : Nat} {tokens : Array UInt32}
      (earlier : TokensFor raw start tokens i) (hi : i < raw.size) :
      TokensFor raw start (tokens.push (raw[i]?.getD 0).toUInt32) (i + 1)
  | backref {start i len dist : Nat} {tokens : Array UInt32}
      (earlier : TokensFor raw start tokens i) (hlen : 3 ≤ len ∧ len ≤ 258)
      (href : Backref raw i len dist) :
      TokensFor raw start (tokens.push (matchToken len dist)) (i + len)

private theorem tokGo_tokens (raw : ByteArray) (mask fuel start i : Nat)
    (tab : Array Nat) (tokens : Array UInt32) (hi : i ≤ raw.size)
    (hf : raw.size - i ≤ fuel) (hp : TokensFor raw start tokens i) :
    TokensFor raw start (tokGo raw mask fuel i tab tokens) raw.size := by
  induction fuel generalizing i tab tokens with
  | zero =>
    have heq : i = raw.size := by omega
    simpa only [tokGo, heq] using hp
  | succ fuel ih =>
    rw [tokGo]
    dsimp only
    split
    · have heq : i = raw.size := by omega
      simpa only [heq] using hp
    · rename_i hlt
      split
      · exact ih _ _ _ (by omega) (by omega) (.literal hp (by omega))
      · have hm := bestMatch_covers raw tab mask i (min 258 (raw.size - i))
          (by have := Nat.min_le_left 258 (raw.size - i); omega) 32 (tab[hash3 raw mask i]?.getD i) 0 0
          (Nat.zero_le _) ⟨by decide, Or.inl rfl⟩
        dsimp only at hm
        split
        · rename_i hmatch
          have href := hm.2.2
          have hpos := href.2.resolve_left (by omega)
          exact ih _ _ _ (by omega) (by omega)
            (.backref hp ⟨by omega, by have := hm.2.1; omega⟩ href)
        · exact ih _ _ _ (by omega) (by omega) (.literal hp (by omega))

/-- The hash-chain tokenizer spells every input byte, for any input size. -/
theorem tokenize_covers (raw : ByteArray) : TokensFor raw 0 (tokenize raw) raw.size := by
  exact tokGo_tokens raw _ raw.size 0 0 _ #[] (Nat.zero_le _) (by omega)
    (.empty 0 (Nat.zero_le _))

/-- The code-length sequence's run-length form (RFC 1951 §3.2.7): symbols
0–18 with each one's extra-bits payload. -/
private def clRle (seq : Array Nat) : Array (Nat × Nat × Nat) := Id.run do
  let mut rle : Array (Nat × Nat × Nat) := #[]
  let mut p := 0
  for _ in [0:seq.size] do
    if p ≥ seq.size then break
    let v := seq[p]?.getD 0
    let mut r := 1
    for _ in [0:seq.size] do
      if p + r < seq.size && seq[p + r]?.getD 99 == v then r := r + 1 else break
    if v == 0 then
      if r < 3 then
        for _ in [0:r] do
          rle := rle.push (0, 0, 0)
        p := p + r
      else if r ≤ 10 then
        rle := rle.push (17, r - 3, 3)
        p := p + r
      else
        let take := min r 138
        rle := rle.push (18, take - 11, 7)
        p := p + take
    else
      rle := rle.push (v, 0, 0)
      p := p + 1
      let mut left := r - 1
      for _ in [0:seq.size] do
        if left ≥ 3 then
          let take := min left 6
          rle := rle.push (16, take - 3, 2)
          left := left - take
          p := p + take
        else break
      for _ in [0:2] do
        if left > 0 then
          rle := rle.push (v, 0, 0)
          p := p + 1
          left := left - 1
  return rle

/-- Compress to a zlib stream (RFC 1950 wrapping RFC 1951): LZ77 tokens in
one dynamic-Huffman block, both code sets optimal for this data. Any
inflater accepts the result; the engine's own `inflate` inverting it is
`inflate_deflate_id` (staged; fuzz-checked by `scripts/flate-fuzz.lean`).
`deflateStored` stays for callers that must never pay compression time. -/
def deflate (raw : ByteArray) : ByteArray := Id.run do
  let tokens := tokenize raw
  -- Frequencies; end-of-block is always sent exactly once.
  let mut litFreq : Array Nat := Array.replicate 286 0
  let mut distFreq : Array Nat := Array.replicate 30 0
  for t in tokens do
    if t < 256 then
      let lit := t.toNat
      litFreq := litFreq.set! lit (litFreq[lit]?.getD 0 + 1)
    else
      let (len, _, ds) := matchOf t
      let ls := 257 + (lenSymTab[len]?.getD 0)
      litFreq := litFreq.set! ls (litFreq[ls]?.getD 0 + 1)
      distFreq := distFreq.set! ds (distFreq[ds]?.getD 0 + 1)
  litFreq := litFreq.set! 256 1
  let litLens := pmLengths litFreq 15
  let distLens := pmLengths distFreq 15
  let litCodes := canonCodes litLens
  let distCodes := canonCodes distLens
  let mut nlit := 257
  for s in [0:litLens.size] do
    if litLens[s]?.getD 0 > 0 then nlit := max nlit (s + 1)
  let mut ndist := 1
  for s in [0:distLens.size] do
    if distLens[s]?.getD 0 > 0 then ndist := max ndist (s + 1)
  let rle := clRle (litLens.extract 0 nlit ++ distLens.extract 0 ndist)
  let mut clFreq : Array Nat := Array.replicate 19 0
  for (s, _, _) in rle do
    clFreq := clFreq.set! s (clFreq[s]?.getD 0 + 1)
  let clLens := pmLengths clFreq 7
  let clCodes := canonCodes clLens
  let mut nclen := 4
  for k in [0:clOrder.size] do
    if clLens[clOrder[k]?.getD 0]?.getD 0 > 0 then nclen := k + 1
  -- 0x78 0x9C: deflate, 32 KiB window, no preset dictionary, and
  -- (CMF·256 + FLG) ≡ 0 (mod 31) as RFC 1950 §2.2 requires.
  let mut w : Bw := { out := (ByteArray.empty.push 0x78).push 0x9C, bits := 0, nbits := 0 }
  w := w.push 1 1
  w := w.push 2 2
  w := w.push (nlit - 257) 5
  w := w.push (ndist - 1) 5
  w := w.push (nclen - 4) 4
  for k in [0:nclen] do
    w := w.push (clLens[clOrder[k]?.getD 0]?.getD 0) 3
  for (s, ev, eb) in rle do
    w := w.push (clCodes[s]?.getD 0) (clLens[s]?.getD 0)
    if eb > 0 then
      w := w.push ev eb
  for t in tokens do
    if t < 256 then
      let lit := t.toNat
      w := w.push (litCodes[lit]?.getD 0) (litLens[lit]?.getD 0)
    else
      let (len, dist, di) := matchOf t
      let li := lenSymTab[len]?.getD 0
      w := w.push (litCodes[257 + li]?.getD 0) (litLens[257 + li]?.getD 0)
      let leb := lenExtra[li]?.getD 0
      if leb > 0 then
        w := w.push (len - (lenBase[li]?.getD 0)) leb
      w := w.push (distCodes[di]?.getD 0) (distLens[di]?.getD 0)
      let deb := distExtra[di]?.getD 0
      if deb > 0 then
        w := w.push (dist - (distBase[di]?.getD 0)) deb
  w := w.push (litCodes[256]?.getD 0) (litLens[256]?.getD 0)
  let mut out := w.flush
  return pushBe32 out (adler32 raw)

/-- FNV-1a over bytes: the content hash the PDF trailer ID and the
driver's content-keyed caches share. Not cryptographic — a fingerprint
for change detection, as ISO 32000-2 §14.4 asks of the file ID. -/
def fnv64 (seed : UInt64) (b : ByteArray) : UInt64 := Id.run do
  let mut h := seed
  for byte in b do
    h := (h ^^^ byte.toUInt64) * 1099511628211
  return h

/-- Sixteen hex digits of a 64-bit hash. -/
def hex16 (x : UInt64) : String := Id.run do
  let digits := "0123456789ABCDEF".toList.toArray
  let mut s := ""
  let mut v := x
  for _ in [0:16] do
    s := String.ofList [digits[(v % 16).toNat]?.getD '0'] ++ s
    v := v / 16
  return s

/-- A 128-bit content key: two independent FNV-64 passes, hex. The key a
content-addressed cache files a value under — 32 filename-safe chars. -/
def contentKey (b : ByteArray) : String :=
  hex16 (fnv64 14695981039346656037 b) ++ hex16 (fnv64 1099511628211 b)

/-! ## A byte array as one equation

`build n f` is the `n`-byte array whose byte `j` is `f` of the `j` bytes
before it. Every derived plane below is spelled this way so that it *is*
a statement — `getElem?_build` reads byte `j` off the definition, no loop
to unroll — while the run stays one tail-recursive push per byte into a
uniquely owned, pre-sized array. -/

@[specialize] def build (n : Nat) (f : ByteArray → UInt8) : ByteArray :=
  go (ByteArray.emptyWithCapacity n)
where
  @[specialize] go (out : ByteArray) : ByteArray :=
    if _ : out.size < n then go (out.push (f out)) else out
  termination_by n - out.size
  decreasing_by simp only [ByteArray.size_push]; omega

theorem build.go_of_le (n : Nat) (f : ByteArray → UInt8) (out : ByteArray)
    (h : n ≤ out.size) : build.go n f out = out := by
  rw [build.go]
  simp [Nat.not_lt.mpr h]

theorem build.go_succ (n : Nat) (f : ByteArray → UInt8) (out : ByteArray)
    (h : out.size ≤ n) :
    build.go (n + 1) f out = (build.go n f out).push (f (build.go n f out)) := by
  rw [build.go]
  simp only [show out.size < n + 1 by omega, ↓reduceDIte]
  by_cases hlt : out.size < n
  · rw [build.go_succ n f (out.push (f out)) (by simp only [ByteArray.size_push]; omega)]
    conv => rhs; rw [build.go]
    simp [hlt]
  · have heq : n ≤ out.size := Nat.not_lt.mp hlt
    rw [build.go_of_le (n + 1) f _ (by simp only [ByteArray.size_push]; omega),
      build.go_of_le n f out heq]
termination_by n - out.size
decreasing_by simp only [ByteArray.size_push]; omega

theorem build_zero (f : ByteArray → UInt8) : build 0 f = ByteArray.empty :=
  build.go_of_le 0 f _ (Nat.zero_le _)

theorem build_succ (n : Nat) (f : ByteArray → UInt8) :
    build (n + 1) f = (build n f).push (f (build n f)) :=
  build.go_succ n f (ByteArray.emptyWithCapacity (n + 1)) (Nat.zero_le _)

theorem size_build (n : Nat) (f : ByteArray → UInt8) : (build n f).size = n := by
  induction n with
  | zero => rw [build_zero]; rfl
  | succ n ih => rw [build_succ, ByteArray.size_push, ih]

theorem getElem?_push (a : ByteArray) (b : UInt8) (i : Nat) :
    (a.push b)[i]? = if i < a.size then a[i]? else if i = a.size then some b else none := by
  by_cases h1 : i < a.size
  · rw [getElem?_pos (a.push b) i (by rw [ByteArray.size_push]; omega), getElem?_pos a i h1]
    simp only [h1, ↓reduceIte, ByteArray.getElem_eq_getElem_data, ByteArray.data_push]
    exact congrArg some (Array.getElem_push_lt h1)
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i = a.size
    · subst h2
      rw [getElem?_pos (a.push b) a.size (by rw [ByteArray.size_push]; omega)]
      simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_push, Array.getElem_push]
    · simp only [h2, ↓reduceIte]
      exact getElem?_neg (a.push b) i (by rw [ByteArray.size_push]; omega)

/-- Byte `j` of `build n f` is `f` of the `j` bytes before it: the equation
the whole array is. -/
theorem getElem?_build (n : Nat) (f : ByteArray → UInt8) (j : Nat) (hj : j < n) :
    (build n f)[j]? = some (f (build j f)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [build_succ, getElem?_push, size_build]
    by_cases h : j < n
    · simp [h, ih h]
    · have : j = n := by omega
      subst this
      simp

/-- One reconstructed byte (ISO/IEC 15948 §9.2, the five filter types): the
raw byte plus its prediction from the left, upper, and upper-left
neighbours, modulo 256. Types above 4 predict as Paeth here and are
refused before this is reached (`pngUnfilter`). -/
def predict (f x left up upLeft : Nat) : Nat :=
  (x + (if f == 0 then 0 else if f == 1 then left else if f == 2 then up
    else if f == 3 then (left + up) / 2
    else
      -- Paeth: the neighbour closest to the linear estimate.
      let p : Int := (left : Int) + up - upLeft
      let pa := (p - left).natAbs
      let pb := (p - up).natAbs
      let pc := (p - upLeft).natAbs
      if pa ≤ pb && pa ≤ pc then left else if pb ≤ pc then up else upLeft)) % 256

/-- Byte `out.size` of the plane whose first `out.size` bytes are `out`:
row `j / rowBytes`, column `j % rowBytes`, predicted from the plane's own
earlier bytes `bpp` to the left and `rowBytes` above (ISO/IEC 15948 §9).
Total over any bytes — a missing input byte reads as 0. -/
def unfilterByte (raw : ByteArray) (rowBytes bpp : Nat) (out : ByteArray) : UInt8 :=
  let j := out.size
  let r := j / rowBytes
  let i := j % rowBytes
  let f := (raw[r * (1 + rowBytes)]?.getD 0).toNat
  let x := (raw[r * (1 + rowBytes) + 1 + i]?.getD 0).toNat
  let left := if bpp ≤ i then (out[j - bpp]?.getD 0).toNat else 0
  let up := if rowBytes ≤ j then (out[j - rowBytes]?.getD 0).toNat else 0
  let upLeft := if rowBytes ≤ j ∧ bpp ≤ i then (out[j - rowBytes - bpp]?.getD 0).toNat
    else 0
  UInt8.ofNat (predict f x left up upLeft)

/-- Every reconstructed sample of a predicted stream, as one equation
(`unfilterByte`); `pngUnfilter` is the checked door in front of it. -/
def unfilterAll (raw : ByteArray) (pxH rowBytes bpp : Nat) : ByteArray :=
  build (pxH * rowBytes) (unfilterByte raw rowBytes bpp)

/-- Two byte arrays agreeing at every index are one. -/
theorem ext_of_getElem? (a b : ByteArray) (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]? = b[i]?) : a = b := by
  apply ByteArray.ext_getElem hs
  intro i hi hi'
  have := h i hi
  rw [getElem?_pos a i hi, getElem?_pos b i hi'] at this
  exact Option.some.inj this

/-- Reverse the per-scanline PNG filters (ISO/IEC 15948 §9): each row opens
with its filter type, predicting from the left, above, and above-left bytes
at `bpp` distance. Total: the geometry is checked against the input once,
then `unfilterAll` is the plane. Two consumers share it: the image tests'
semantic route, and PDF streams whose `/DecodeParms` declare a PNG
predictor — cross-reference streams routinely do (ISO 32000-2 §7.4.4.4,
Predictor 10–15). -/
def pngUnfilter (raw : ByteArray) (pxH rowBytes bpp : Nat) :
    Except String ByteArray :=
  if raw.size < pxH * (1 + rowBytes) then
    .error "corrupt PNG: truncated scanlines"
  else if ∀ r < pxH, (raw[r * (1 + rowBytes)]?.getD 0).toNat ≤ 4 then
    .ok (unfilterAll raw pxH rowBytes bpp)
  else
    .error "corrupt PNG: a scanline filter type above 4"

/-- A byte array is exactly the source prefix through `n`. -/
def BytePrefix (raw : ByteArray) (n : Nat) (out : ByteArray) : Prop :=
  out.size = n ∧ n ≤ raw.size ∧ ∀ k < n, out[k]? = raw[k]?

theorem BytePrefix.push {raw out : ByteArray} {n : Nat} {b : UInt8}
    (hp : BytePrefix raw n out) (hn : n < raw.size) (hb : some b = raw[n]?) :
    BytePrefix raw (n + 1) (out.push b) := by
  refine ⟨by simp [hp.1], by omega, ?_⟩
  intro k hk
  rw [getElem?_push, hp.1]
  by_cases hkn : k < n
  · rw [ite_eq_left hkn]
    exact hp.2.2 k hkn
  · have heq : k = n := by omega
    subst k
    rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
    exact hb

/-- The inflater's actual overlapping-copy loop extends a verified prefix.
The invariant advances with the loop index, so completion states its length. -/
theorem backref_copy_exact (raw out : ByteArray) (i len dist : Nat)
    (hp : BytePrefix raw i out) (href : Backref raw i len dist) :
    let copied := Id.run do
      let mut result := out
      for _ in [0:len] do
        result := result.push (result[result.size - dist]?.getD 0)
      return result
    BytePrefix raw (i + len) copied := by
  change BytePrefix raw (i + len)
    (forIn [0:len] out (fun _ result =>
      pure (.yield (result.push (result[result.size - dist]?.getD 0)))) : Id ByteArray).run
  apply Progress.forIn_range_exact (fun k result => BytePrefix raw (i + k) result)
    (BytePrefix raw (i + len)) _ 0 len out (Nat.zero_le _)
    (by simpa using hp) _ (fun _ h => h)
  intro k _ hk result hresult
  have hnonempty := href.2.resolve_left (by omega)
  have hj : result.size - dist < i + k := by have := hresult.1; omega
  have hrange : i + k < raw.size := by omega
  have hsame : result.size - dist = i - dist + k := by have := hresult.1; omega
  have hr : result[result.size - dist]? = some (raw[i + k]'hrange) := by
    rw [hresult.2.2 _ hj, hsame, hnonempty.2.2.2 k hk]
    simp only [getElem?_pos, hrange]
  change BytePrefix raw (i + (k + 1))
    (result.push (result[result.size - dist]?.getD 0))
  rw [hr]
  simpa only [Nat.add_assoc, Option.getD_some] using
    hresult.push hrange (by simp only [getElem?_pos, hrange])

/-- The infinite zero-padded bit view of completed bytes and pending payload. -/
private def Bw.bitValue (w : Bw) (i : Nat) : Bool :=
  if i < 8 * w.out.size then
    ((w.out[i / 8]?.getD 0).toNat).testBit (i % 8)
  else w.bits.toNat.testBit (i - 8 * w.out.size)

private theorem drainByte_bits_exact (out : ByteArray) (bits n n' : UInt64) (i : Nat) :
    ({out := out.push bits.toUInt8, bits := bits >>> 8, nbits := n'} : Bw).bitValue i =
      ({out, bits, nbits := n} : Bw).bitValue i := by
  unfold Bw.bitValue
  dsimp only
  rw [ByteArray.size_push]
  by_cases h : i < 8 * out.size
  · have h' : i < 8 * (out.size + 1) := by omega
    have hi : i / 8 < out.size := by omega
    simp only [h, h', ite_true, getElem?_push, hi]
  · by_cases h' : i < 8 * (out.size + 1)
    · have hi : i / 8 = out.size := by omega
      have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
      have he : i - 8 * out.size = i % 8 := by omega
      simp only [h, h', ite_true, ite_false, getElem?_push, hi, Nat.lt_irrefl,
        Option.getD_some, UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow, hk,
        decide_true, Bool.true_and, he]
    · have he : 8 + (i - 8 * (out.size + 1)) = i - 8 * out.size := by omega
      simp [h, h', UInt64.toNat_shiftRight, Nat.testBit_shiftRight, he]

private theorem pushU_drain_bits (w : Bw) (v n : UInt64) (i : Nat) :
    (w.pushU v n).bitValue i =
      ({ w with
          bits := w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)
          nbits := w.nbits + n } : Bw).bitValue i := by
  let p := w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)
  have hr : (p >>> 8) >>> 8 = p >>> 16 := by
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_shiftRight, ← Nat.shiftRight_add]
  unfold Bw.pushU
  dsimp only
  split
  · change ({ out := (w.out.push p.toUInt8).push (p >>> 8).toUInt8
              bits := p >>> 16
              nbits := _ } : Bw).bitValue i = _
    rw [← hr]
    exact (drainByte_bits_exact (w.out.push p.toUInt8) (p >>> 8) 0 0 i).trans
      (drainByte_bits_exact w.out p 0 0 i)
  · split
    · exact drainByte_bits_exact w.out p 0 0 i
    · rfl

/-- Appending a field preserves every old bit and supplies exactly its new bits. -/
private theorem pushU_bits_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) (i : Nat)
    (hi : i < 8 * w.out.size + w.nbits.toNat + n.toNat) :
    (w.pushU v n).bitValue i =
      if i < 8 * w.out.size + w.nbits.toNat then w.bitValue i
      else v.toNat.testBit (i - (8 * w.out.size + w.nbits.toNat)) := by
  rw [pushU_drain_bits]
  by_cases ho : i < 8 * w.out.size
  · have hp : i < 8 * w.out.size + w.nbits.toNat := by omega
    simp only [Bw.bitValue, ho, hp, ite_true]
  · have hp := BitPacking.packField_bits_exact w.bits.toNat v.toNat
      w.nbits.toNat n.toNat (i - 8 * w.out.size) hw.2 (by omega)
    simp only [Bw.bitValue, ho, ite_false, pushU_payload_exact w v n hw hn]
    rw [hp]
    by_cases hh : i < 8 * w.out.size + w.nbits.toNat
    · have hl : i - 8 * w.out.size < w.nbits.toNat := by omega
      simp only [hh, hl, ite_true]
    · have hl : ¬ i - 8 * w.out.size < w.nbits.toNat := by omega
      have he : i - 8 * w.out.size - w.nbits.toNat =
          i - (8 * w.out.size + w.nbits.toNat) := by omega
      simp only [hh, hl, ite_false, he]

private theorem flush_position_between (w : Bw) (hw : w.Valid) :
    8 * w.out.size + w.nbits.toNat ≤ 8 * w.flush.size := by
  by_cases hn : w.nbits = 0
  · simp [Bw.flush, hn]
  · simp only [Bw.flush, beq_iff_eq, hn, ite_false, ByteArray.size_push]
    have := hw.1
    omega

private theorem flush_bits_exact (w : Bw) (hw : w.Valid) (i : Nat)
    (hi : i < 8 * w.out.size + w.nbits.toNat) :
    ((w.flush[i / 8]?.getD 0).toNat).testBit (i % 8) = w.bitValue i := by
  by_cases hn : w.nbits = 0
  · have ho : i < 8 * w.out.size := by simpa [hn] using hi
    simp only [Bw.flush, hn, beq_self_eq_true, ite_true, Bw.bitValue, ho]
  · by_cases ho : i < 8 * w.out.size
    · have hb : i / 8 < w.out.size := by omega
      simp only [Bw.flush, beq_iff_eq, hn, ite_false, Bw.bitValue, ho, ite_true,
        getElem?_push, hb]
    · have hs := hw.1
      have hb : i / 8 = w.out.size := by omega
      have he : i - 8 * w.out.size = i % 8 := by omega
      have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
      simp only [Bw.flush, beq_iff_eq, hn, ite_false, Bw.bitValue, ho,
        getElem?_push, hb, Nat.lt_irrefl, ite_true, Option.getD_some,
        UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow, hk, decide_true,
        Bool.true_and, he]

/-- A field already written, including the writer's pending incomplete byte. -/
private def Bw.Field (w : Bw) (start width value : Nat) : Prop :=
  start + width ≤ 8 * w.out.size + w.nbits.toNat ∧
    ∀ k < width, w.bitValue (start + k) = value.testBit k

private theorem Bw.Field.pushU (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) {start width value : Nat} (hf : w.Field start width value) :
    (w.pushU v n).Field start width value := by
  constructor
  · rw [pushU_position_exact w v n hw hn]
    have := hf.1
    omega
  · intro k hk
    have hh : start + k < 8 * w.out.size + w.nbits.toNat := by have := hf.1; omega
    rw [pushU_bits_exact w v n hw hn _ (by omega)]
    simpa only [hh, ite_true] using hf.2 k hk

private theorem pushU_field_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    (w.pushU v n).Field (8 * w.out.size + w.nbits.toNat) n.toNat v.toNat := by
  constructor
  · rw [pushU_position_exact w v n hw hn]
    exact Nat.le_refl _
  · intro k hk
    have hh : ¬ 8 * w.out.size + w.nbits.toNat + k <
        8 * w.out.size + w.nbits.toNat := by omega
    rw [pushU_bits_exact w v n hw hn _ (by omega)]
    simp only [hh, ite_false, Nat.add_sub_cancel_left]

private theorem Bw.Field.flush (w : Bw) (hw : w.Valid) {start width value : Nat}
    (hf : w.Field start width value) : BitField w.flush start width value := by
  constructor
  · simpa only [Nat.mul_comm] using Nat.le_trans hf.1 (flush_position_between w hw)
  · intro k hk
    have hi : start + k < 8 * w.out.size + w.nbits.toNat := by have := hf.1; omega
    have he := congrArg Bool.toNat ((flush_bits_exact w hw _ hi).trans (hf.2 k hk))
    simpa only [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using he

/-- A field pushed through the actual writer is read back by the actual reader. -/
theorem pushU_read_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) (hv : v.toNat < 2 ^ n.toNat) :
    ({data := (w.pushU v n).flush, bitPos := 8 * w.out.size + w.nbits.toNat} : Br).bits
        n.toNat =
      some (v.toNat, { data := (w.pushU v n).flush
                       bitPos := 8 * w.out.size + w.nbits.toNat + n.toNat }) := by
  exact bitField_bits_exact _ _ _ (by omega) hv
    (Bw.Field.flush (w.pushU v n) (pushU_valid w v n hw hn)
      (pushU_field_exact w v n hw hn))

/-- Reversing the encoder's value turns the writer's little-endian field into
the decoder's most-significant-first codeword. -/
theorem BitField.codeField {data : ByteArray} {start width code : Nat}
    (hf : BitField data start width (Canonical.reverseBits code width)) :
    CodeField data start width code := by
  refine ⟨hf.1, ?_⟩
  intro k hk
  rw [hf.2 k hk]
  have hb := congrArg Bool.toNat (Canonical.reverseBits_bit_exact code width k hk)
  simpa only [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using hb

/-- A bounded canonical code written by the actual bit writer is decoded by
the actual Huffman decoder, at any valid starting byte alignment. The table
interval identifies the decoded symbol; constructing that interval is separate. -/
theorem push_huff_decode_exact (w : Bw) (h : Huff) (width code : Nat)
    (hw : w.Valid) (hwidth : 1 ≤ width ∧ width ≤ 15) (hcode : code < 2 ^ width)
    (hlo : Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) ≤ code)
    (hhi : code <
      Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) +
        h.counts[width]?.getD 0) :
    h.decode
      { data := (w.push (Canonical.reverseBits code width) width).flush
        bitPos := 8 * w.out.size + w.nbits.toNat } =
      some
        (h.symbols[Canonical.index (fun k => h.counts[k]?.getD 0) (width - 1) +
          (code - Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1))]?.getD 0,
          { data := (w.push (Canonical.reverseBits code width) width).flush
            bitPos := 8 * w.out.size + w.nbits.toNat + width }) := by
  have hn64 : width < 2 ^ 64 := by omega
  have hn : width.toUInt64.toNat = width := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn64]
  have hr64 : Canonical.reverseBits code width < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Canonical.reverseBits_between _ _)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hr : (Canonical.reverseBits code width).toUInt64.toNat =
      Canonical.reverseBits code width := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hr64]
  have hn16 : width.toUInt64.toNat ≤ 16 := by omega
  apply huff_decode_exact _ _ _ _ hwidth hcode _ hlo hhi
  apply BitField.codeField
  simpa only [Bw.push, hn, hr] using
    (Bw.Field.flush
      (w.pushU (Canonical.reverseBits code width).toUInt64 width.toUInt64)
      (pushU_valid w _ _ hw hn16)
      (pushU_field_exact w _ _ hw hn16))

end LeanTex.Core.Flate
