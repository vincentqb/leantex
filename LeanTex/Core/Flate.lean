module

import LeanTex.Core.Flate.BlockStream
import LeanTex.Core.Flate.BitPacking
import LeanTex.Core.Flate.BitWriter
import LeanTex.Core.Flate.Progress
import LeanTex.Core.Flate.TokenSymbols
import LeanTex.Core.Hex

namespace LeanTex.Core.Flate

/-! Bounded zlib compression and decompression (RFC 1950 wrapping RFC 1951), and the checksums,
content keys and PNG scanline unfiltering beside them. -/

/-- Inflates a zlib stream into at most `maxOut` bytes; the Adler-32 trailer is not verified. -/
public def inflate (data : ByteArray) (maxOut : Nat) : Except String ByteArray := do
  let some cmf := data[0]? | .error "zlib: empty stream"
  let some flg := data[1]? | .error "zlib: truncated header"
  if cmf.toNat % 16 != 8 then .error "zlib: not deflate"
  else if flg.toNat / 32 % 2 == 1 then .error "zlib: preset dictionary is not supported"
  else BlockStream.read {data, bitPos := 16} ByteArray.empty maxOut

/-- Adler-32 (RFC 1950 §8.2). -/
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

/-- Pushes the low 32 bits of `v` onto `b`, most significant byte first. -/
def pushBe32 (b : ByteArray) (v : Nat) : ByteArray :=
  (((b.push (UInt8.ofNat (v / 16777216 % 256))).push
    (UInt8.ofNat (v / 65536 % 256))).push
    (UInt8.ofNat (v / 256 % 256))).push (UInt8.ofNat (v % 256))

/-- A zlib stream of stored, uncompressed blocks. -/
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

private def hash3 (raw : ByteArray) (mask i : Nat) : Nat :=
  if h : i + 2 < raw.size then
    (((((raw[i]'(by omega)).toUInt64 <<< 16) ^^^ ((raw[i + 1]'(by omega)).toUInt64 <<< 8) ^^^
      raw[i + 2].toUInt64) * 2654435761) >>> 17 &&& mask.toUInt64).toNat
  else 0

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

/-- The `prev` ring's slot for position `c`; `head` holds the table's first `mask + 1` slots. -/
private def prevSlot (mask c : Nat) : Nat := mask + 1 + (c &&& mask)

private def packMatch (len dist : Nat) : UInt64 :=
  (len.toUInt64 <<< 16) ||| dist.toUInt64

theorem packMatch_exact (len dist : Nat) (hl : len < 2 ^ 48) (hd : dist < 65536) :
    (packMatch len dist >>> 16).toNat = len ∧
      (packMatch len dist &&& 65535).toNat = dist := by
  exact BitPacking.unpackBits_exact len dist 16 (by decide) hd hl

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

/-- A verified source match: zero length, or a run within the input and the 32 KiB window. -/
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


private def insertHashes (raw : ByteArray) (mask : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, tab => tab
  | fuel + 1, j, tab =>
    if j + 3 ≤ raw.size then
      let hj := hash3 raw mask j
      let old := tab[hj]?.getD j
      insertHashes raw mask fuel (j + 1) ((tab.set! hj j).set! (prevSlot mask j) old)
    else
      tab

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

/-- LZ77 tokens over a hash chain bounded at 32 candidates. -/
def tokenize (raw : ByteArray) : Array UInt32 :=
  let n := raw.size
  let mask := if n ≥ 65536 then 32767 else 4095
  tokGo raw mask n 0 (Array.replicate (2 * (mask + 1)) n) #[]

/-- The tokens spell exactly the input between the two positions; a match may overlap its destination. -/
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

theorem tokenize_covers (raw : ByteArray) : TokensFor raw 0 (tokenize raw) raw.size := by
  exact tokGo_tokens raw _ raw.size 0 0 _ #[] (Nat.zero_le _) (by omega)
    (.empty 0 (Nat.zero_le _))

/-- A writer holding the zlib header 0x78 0x9C: deflate, a 32 KiB window, no preset dictionary
(RFC 1950 §2.2). -/
def zlibWriter : Bw :=
  {out := (ByteArray.empty.push 0x78).push 0x9C, bits := 0, nbits := 0}

/-- The compressor's writer before its final flush and checksum. -/
def deflateWriter (raw : ByteArray) : Bw :=
  BlockStream.write (tokenize raw) zlibWriter

/-- Compresses to a zlib stream: LZ77 tokens in one dynamic-Huffman block, then the Adler-32 checksum. -/
public def deflate (raw : ByteArray) : ByteArray :=
  pushBe32 (deflateWriter raw).flush (adler32 raw)

/-- The FNV-64 offset basis, the seed of every single FNV fingerprint. -/
@[expose] public def fnvOffset : UInt64 := 14695981039346656037

/-- The FNV-64 prime, also the seed of a 128-bit key's second pass. -/
@[expose] public def fnvPrime : UInt64 := 1099511628211

/-- FNV-1a over bytes, a non-cryptographic fingerprint for change detection. -/
public def fnv64 (seed : UInt64) (b : ByteArray) : UInt64 := Id.run do
  let mut h := seed
  for byte in b do
    h := (h ^^^ byte.toUInt64) * fnvPrime
  return h

/-- Sixteen hex digits of a 64-bit hash. -/
public def hex16 (x : UInt64) : String := Hex.digits true 16 x.toNat

/-- A 128-bit content key: two independent FNV-64 passes as 32 hex digits. -/
public def contentKey (b : ByteArray) : String :=
  hex16 (fnv64 fnvOffset b) ++ hex16 (fnv64 fnvPrime b)

/-- The `n`-byte array whose byte `j` is `f` of the `j` bytes before it. -/
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

/-- One PNG-reconstructed byte (ISO/IEC 15948 §9.2): the raw byte plus its filter's prediction,
modulo 256. -/
public def predict (f x left up upLeft : Nat) : Nat :=
  (x + (if f == 0 then 0 else if f == 1 then left else if f == 2 then up
    else if f == 3 then (left + up) / 2
    else
      let p : Int := (left : Int) + up - upLeft
      let pa := (p - left).natAbs
      let pb := (p - up).natAbs
      let pc := (p - upLeft).natAbs
      if pa ≤ pb && pa ≤ pc then left else if pb ≤ pc then up else upLeft)) % 256

/-- The next byte of a PNG-unfiltered plane from the bytes before it; a missing input byte reads as 0. -/
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

/-- Every unfiltered byte of a `pxH`-row plane, without the geometry check. -/
@[expose] public def unfilterAll (raw : ByteArray) (pxH rowBytes bpp : Nat) : ByteArray :=
  build (pxH * rowBytes) (unfilterByte raw rowBytes bpp)

public theorem ext_of_getElem? (a b : ByteArray) (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]? = b[i]?) : a = b := by
  apply ByteArray.ext_getElem hs
  intro i hi hi'
  have := h i hi
  rw [getElem?_pos a i hi, getElem?_pos b i hi'] at this
  exact Option.some.inj this

/-- Reverses the per-scanline PNG filters (ISO/IEC 15948 §9) after checking the geometry against the input. -/
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
