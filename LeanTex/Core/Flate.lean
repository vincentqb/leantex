module

import LeanTex.Core.Flate.BlockStream
import all LeanTex.Core.Flate.BitWriter
import all LeanTex.Core.Flate.TokenSymbols

namespace LeanTex.Core.Flate

/-! # Flate: bounded zlib compression and decompression

`inflate` decodes a zlib stream (RFC 1950 wrapping RFC 1951 deflate): what a
PNG's IDAT holds. It exists for the PNG forms whose samples cannot pass
through to a PDF `/FlateDecode` stream untouched — an alpha channel must be
split into a colour plane and an SMask, which means really decoding. It is a
total function: every read is bounds-checked, every loop bounded by the
input's bit count or the declared output size, and a malformed stream is an
error value, never a hang or a crash.

`deflate` writes a dynamic-Huffman block from the hash-chain LZ77 tokenizer,
followed by its Adler-32 checksum. `deflateStored` is the uncompressed option
for callers that do not need compression. Both emit the standard zlib
wrapper that a PDF viewer's `/FlateDecode` reader accepts. -/

/-- Inflate a zlib stream into at most `maxOut` bytes (the caller knows the
size a PNG's samples must have; anything else is malformed). The Adler-32
trailer is not verified: the sample data is judged by its shape, as chunk
CRCs are. -/
public def inflate (data : ByteArray) (maxOut : Nat) : Except String ByteArray := do
  let some cmf := data[0]? | .error "zlib: empty stream"
  let some flg := data[1]? | .error "zlib: truncated header"
  if cmf.toNat % 16 != 8 then .error "zlib: not deflate"
  else if flg.toNat / 32 % 2 == 1 then .error "zlib: preset dictionary is not supported"
  else BlockStream.read {data, bitPos := 16} ByteArray.empty maxOut

/-- Adler-32 (RFC 1950 §8.2). Both sums ride in one `UInt64` — `s2` in
the high word, `s1` in the low — and reduce modulo 65521 once per 5552
bytes, zlib's `NMAX`: the longest run after which both still fit their
words. The byte loop then divides nothing and carries one scalar. -/
public def adler32 (data : ByteArray) : Nat := Id.run do
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
public def deflateStored (raw : ByteArray) : ByteArray := Id.run do
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
statement is `inflate_deflate_id` in `Flate/RoundtripProof.lean`. The
executable oracle `scripts/flate-fuzz.lean` also cross-checks every stream
against a foreign inflater. Pure and total: every loop is
bounded by the input size or a table's length. -/

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
def tokenize (raw : ByteArray) : Array UInt32 :=
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

/-- 0x78 0x9C declares deflate, a 32 KiB window, and no preset dictionary;
CMF·256 + FLG is divisible by 31 (RFC 1950 §2.2). -/
def zlibWriter : Bw :=
  {out := (ByteArray.empty.push 0x78).push 0x9C, bits := 0, nbits := 0}

/-- The production writer before its final byte flush and checksum. -/
def deflateWriter (raw : ByteArray) : Bw :=
  BlockStream.write (tokenize raw) zlibWriter

/-- Compress to a zlib stream (RFC 1950 wrapping RFC 1951): LZ77 tokens in
one dynamic-Huffman block, both code sets optimal for this data. The
engine's own `inflate` inverts it by `inflate_deflate_id` in
`Flate/RoundtripProof.lean`; `scripts/flate-fuzz.lean` also checks foreign zlib.
`deflateStored` stays for callers that must never pay compression time. -/
public def deflate (raw : ByteArray) : ByteArray :=
  pushBe32 (deflateWriter raw).flush (adler32 raw)

/-- FNV-1a over bytes: the content hash the PDF trailer ID and the
driver's content-keyed caches share. Not cryptographic — a fingerprint
for change detection, as ISO 32000-2 §14.4 asks of the file ID. -/
public def fnv64 (seed : UInt64) (b : ByteArray) : UInt64 := Id.run do
  let mut h := seed
  for byte in b do
    h := (h ^^^ byte.toUInt64) * 1099511628211
  return h

/-- Sixteen hex digits of a 64-bit hash. -/
public def hex16 (x : UInt64) : String := Id.run do
  let digits := "0123456789ABCDEF".toList.toArray
  let mut s := ""
  let mut v := x
  for _ in [0:16] do
    s := String.ofList [digits[(v % 16).toNat]?.getD '0'] ++ s
    v := v / 16
  return s

/-- A 128-bit content key: two independent FNV-64 passes, hex. The key a
content-addressed cache files a value under — 32 filename-safe chars. -/
public def contentKey (b : ByteArray) : String :=
  hex16 (fnv64 14695981039346656037 b) ++ hex16 (fnv64 1099511628211 b)

/-! ## A byte array as one equation

`build n f` is the `n`-byte array whose byte `j` is `f` of the `j` bytes
before it. Every derived plane below is spelled this way so that it *is*
a statement — `getElem?_build` reads byte `j` off the definition, no loop
to unroll — while the run stays one tail-recursive push per byte into a
uniquely owned, pre-sized array. -/

@[specialize] public def build (n : Nat) (f : ByteArray → UInt8) : ByteArray :=
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

public theorem size_build (n : Nat) (f : ByteArray → UInt8) : (build n f).size = n := by
  induction n with
  | zero => rw [build_zero]; rfl
  | succ n ih => rw [build_succ, ByteArray.size_push, ih]

/-- Byte `j` of `build n f` is `f` of the `j` bytes before it: the equation
the whole array is. -/
public theorem getElem?_build (n : Nat) (f : ByteArray → UInt8) (j : Nat) (hj : j < n) :
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
public def predict (f x left up upLeft : Nat) : Nat :=
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
@[expose] public def unfilterByte (raw : ByteArray) (rowBytes bpp : Nat) (out : ByteArray) : UInt8 :=
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
@[expose] public def unfilterAll (raw : ByteArray) (pxH rowBytes bpp : Nat) : ByteArray :=
  build (pxH * rowBytes) (unfilterByte raw rowBytes bpp)

/-- Two byte arrays agreeing at every index are one. -/
public theorem ext_of_getElem? (a b : ByteArray) (hs : a.size = b.size)
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
@[expose] public def pngUnfilter (raw : ByteArray) (pxH rowBytes bpp : Nat) :
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


end LeanTex.Core.Flate
