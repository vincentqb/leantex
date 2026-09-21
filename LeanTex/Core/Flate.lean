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

/-- A canonical Huffman table: `counts[len]` codes of each length, and the
symbols in canonical order. The construction never fails; an over-subscribed
set of lengths simply fails to decode, which the caller reports. -/
private structure Huff where
  counts : Array Nat
  symbols : Array Nat

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

/-- Adler-32 (RFC 1950 §8.2). -/
def adler32 (data : ByteArray) : Nat := Id.run do
  let mut s1 := 1
  let mut s2 := 0
  for b in data do
    s1 := (s1 + b.toNat) % 65521
    s2 := (s2 + s1) % 65521
  return s2 * 65536 + s1

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
  let a := adler32 raw
  out := out.push (UInt8.ofNat (a / 16777216 % 256))
  out := out.push (UInt8.ofNat (a / 65536 % 256))
  out := out.push (UInt8.ofNat (a / 256 % 256))
  out := out.push (UInt8.ofNat (a % 256))
  return out

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

/-- The three-byte rolling hash: Knuth's multiplicative constant over the
window the next match must open with. `UInt64` arithmetic — the product
stays under 2⁵⁶ — for the same reason as `Bw`. -/
private def hash3 (raw : ByteArray) (mask i : Nat) : Nat :=
  (((((raw[i]?.getD 0).toUInt64 <<< 16) ^^^ ((raw[i + 1]?.getD 0).toUInt64 <<< 8) ^^^
    (raw[i + 2]?.getD 0).toUInt64) * 2654435761) >>> 17 &&& mask.toUInt64).toNat

/-- Longest common run at `c`/`i`, `fuel` the caller's bound (`limit ≤
258`, in range by the caller's `c < i` and `limit ≤ raw.size - i`). Tail
recursion: the byte loop carries no boxed loop state — this is the
innermost loop of the compressor. -/
private def matchLen (raw : ByteArray) (c i : Nat) : Nat → Nat → Nat
  | 0, l => l
  | fuel + 1, l =>
    if raw[c + l]?.getD 0 == raw[i + l]?.getD 1 then matchLen raw c i fuel (l + 1)
    else l

/-- The hash tables as one array: `head` in the first `mask + 1` slots,
the `prev` ring in the next — one value threads the walk, no pair to
allocate per step. -/
private def prevSlot (mask c : Nat) : Nat := mask + 1 + (c &&& mask)

/-- A match packed for return: `len <<< 16 ||| dist`, a scalar. -/
private def packMatch (len dist : Nat) : UInt64 :=
  (len.toUInt64 <<< 16) ||| dist.toUInt64

/-- Walk the hash chain for the best match at `i`: candidates verified
byte-wise (a stale ring entry can only cost a candidate, never
correctness), the walk cut short by a match of 64+ (zlib's `good_length`
shape). -/
private def bestMatch (raw : ByteArray) (tab : Array Nat) (mask i limit : Nat) :
    Nat → Nat → Nat → Nat → UInt64
  | 0, _, best, bestDist => packMatch best bestDist
  | fuel + 1, c, best, bestDist =>
    if c ≥ i || i - c > 32768 || best ≥ 64 || best == limit then packMatch best bestDist
    else
      -- A longer match must extend past `best`: one compare rejects most.
      let next := tab[prevSlot mask c]?.getD i
      if raw[c + best]?.getD 0 == raw[i + best]?.getD 0 then
        let l := matchLen raw c i limit 0
        if l > best then bestMatch raw tab mask i limit fuel next l (i - c)
        else bestMatch raw tab mask i limit fuel next best bestDist
      else bestMatch raw tab mask i limit fuel next best bestDist

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
    let t := t.toNat
    if t < 256 then
      litFreq := litFreq.set! t (litFreq[t]?.getD 0 + 1)
    else
      let len := ((t >>> 15) &&& 255) + 3
      let dist := (t &&& 32767) + 1
      let ls := 257 + (lenSymTab[len]?.getD 0)
      litFreq := litFreq.set! ls (litFreq[ls]?.getD 0 + 1)
      let ds := if dist ≤ 256 then distSymTab1[dist]?.getD 0
        else distSymTab2[(dist - 1) >>> 7]?.getD 0
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
    let t := t.toNat
    if t < 256 then
      w := w.push (litCodes[t]?.getD 0) (litLens[t]?.getD 0)
    else
      let len := ((t >>> 15) &&& 255) + 3
      let dist := (t &&& 32767) + 1
      let li := lenSymTab[len]?.getD 0
      w := w.push (litCodes[257 + li]?.getD 0) (litLens[257 + li]?.getD 0)
      let leb := lenExtra[li]?.getD 0
      if leb > 0 then
        w := w.push (len - (lenBase[li]?.getD 0)) leb
      let di := if dist ≤ 256 then distSymTab1[dist]?.getD 0
        else distSymTab2[(dist - 1) >>> 7]?.getD 0
      w := w.push (distCodes[di]?.getD 0) (distLens[di]?.getD 0)
      let deb := distExtra[di]?.getD 0
      if deb > 0 then
        w := w.push (dist - (distBase[di]?.getD 0)) deb
  w := w.push (litCodes[256]?.getD 0) (litLens[256]?.getD 0)
  let mut out := w.flush
  let a := adler32 raw
  out := out.push (UInt8.ofNat (a / 16777216 % 256))
  out := out.push (UInt8.ofNat (a / 65536 % 256))
  out := out.push (UInt8.ofNat (a / 256 % 256))
  out := out.push (UInt8.ofNat (a % 256))
  return out

/-- Apply the PNG Up filter (type 2, ISO/IEC 15948 §9.2) to every row:
each byte becomes its difference from the byte above, and each row opens
with its filter type — the shape `pngUnfilter` inverts and a PDF reader's
Predictor 15 undoes (ISO 32000-2 §7.4.4.4). Re-encoded image planes go
through this before `deflate`: sample deltas compress far better than
samples. -/
def upFilter (px : ByteArray) (pxH rowBytes : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (px.size + pxH)
  for r in [0:pxH] do
    out := out.push 2
    for k in [0:rowBytes] do
      let x := (px[r * rowBytes + k]?.getD 0).toNat
      let up := if r == 0 then 0 else (px[(r - 1) * rowBytes + k]?.getD 0).toNat
      out := out.push (UInt8.ofNat ((x + 256 - up) % 256))
  return out

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

/-- Reverse the per-scanline PNG filters (ISO/IEC 15948 §9): each row opens
with its filter type, predicting from the left, above, and above-left bytes
at `bpp` distance. Total: bounds-checked reads, loops bounded by the
declared geometry. Two consumers share it: PNG sample planes that must
really decode (`Image.decodePng`) and PDF streams whose `/DecodeParms`
declare a PNG predictor — cross-reference streams routinely do
(ISO 32000-2 §7.4.4.4, Predictor 10–15). -/
def pngUnfilter (raw : ByteArray) (pxH rowBytes bpp : Nat) :
    Except String ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut pos := 0
  for _ in [0:pxH] do
    let some ft := raw[pos]? | return .error "corrupt PNG: truncated scanlines"
    pos := pos + 1
    if pos + rowBytes > raw.size then
      return .error "corrupt PNG: truncated scanlines"
    let f := ft.toNat
    if f > 4 then
      return .error s!"corrupt PNG: filter type {f}"
    let rowStart := out.size
    for i in [0:rowBytes] do
      let x := (raw[pos + i]?.getD 0).toNat
      let left := if i ≥ bpp then (out[rowStart + i - bpp]?.getD 0).toNat else 0
      let up := if rowStart ≥ rowBytes then
          (out[rowStart + i - rowBytes]?.getD 0).toNat else 0
      let upLeft := if rowStart ≥ rowBytes && i ≥ bpp then
          (out[rowStart + i - rowBytes - bpp]?.getD 0).toNat else 0
      let v :=
        if f == 0 then x
        else if f == 1 then x + left
        else if f == 2 then x + up
        else if f == 3 then x + (left + up) / 2
        else
          -- Paeth: the neighbour closest to the linear estimate.
          let p : Int := (left : Int) + up - upLeft
          let pa := (p - left).natAbs
          let pb := (p - up).natAbs
          let pc := (p - upLeft).natAbs
          x + (if pa ≤ pb && pa ≤ pc then left else if pb ≤ pc then up else upLeft)
      out := out.push (UInt8.ofNat (v % 256))
    pos := pos + rowBytes
  return .ok out

end LeanTex.Core.Flate
