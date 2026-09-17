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

private def Br.bits (r : Br) (n : Nat) : Option (Nat × Br) := Id.run do
  let mut r := r
  let mut v := 0
  for k in [0:n] do
    match r.bit with
    | none => return none
    | some (b, r') =>
      v := v ||| (b <<< k)
      r := r'
  return some (v, r)

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

end LeanTex.Core.Flate
