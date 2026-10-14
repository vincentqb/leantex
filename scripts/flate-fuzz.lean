/-
Fuzz the codec against python3's zlib: inflate inverts deflate on random, adversarial, fixture and
PDF-writer bytes, and refuses and reads exactly what zlib does but the Adler-32 trailer.
Usage: lake build && lake env lean --run scripts/flate-fuzz.lean
-/
import LeanTex

open LeanTex.Core

def nextRand (s : UInt64) : UInt64 × UInt64 :=
  let s := s ^^^ (s >>> 12)
  let s := s ^^^ (s <<< 25)
  let s := s ^^^ (s >>> 27)
  (s, s * 2685821657736338717)

def rand (s : UInt64) (bound : Nat) : Nat × UInt64 :=
  let (s, v) := nextRand s
  (v.toNat % bound, s)

def die (msg : String) : IO Unit := do
  IO.eprintln s!"flate-fuzz: FAIL {msg}"
  IO.Process.exit 1

def checkOwn (label : String) (b : ByteArray) : IO Unit := do
  match Flate.inflate (Flate.deflate b) b.size with
  | .ok out =>
    unless out == b do die s!"{label}: round trip differs ({out.size} of {b.size} bytes)"
  | .error e => die s!"{label}: inflate refused its own deflate: {e}"

def checkForeign (dir : System.FilePath) (label : String) (b : ByteArray) : IO Unit := do
  let zPath := dir / "z.bin"
  let rPath := dir / "r.bin"
  IO.FS.writeBinFile zPath (Flate.deflate b)
  let out ← IO.Process.output { cmd := "python3", args := #["-c",
    "import zlib,sys; open(sys.argv[2],'wb').write(zlib.decompress(open(sys.argv[1],'rb').read()))",
    zPath.toString, rPath.toString] }
  if out.exitCode != 0 then
    die s!"{label}: foreign inflater refused the stream: {out.stderr}"
  unless (← IO.FS.readBinFile rPath) == b do
    die s!"{label}: foreign inflater decoded different bytes"

def check (dir : System.FilePath) (label : String) (b : ByteArray) : IO Unit := do
  checkOwn label b
  checkForeign dir label b

def lsbBits (v n : Nat) : Array Bool := (Array.range n).map fun i => (v >>> i) % 2 == 1

def msbBits (code len : Nat) : Array Bool :=
  (Array.range len).map fun i => (code >>> (len - 1 - i)) % 2 == 1

def packBits (bits : Array Bool) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut cur := 0
  for h : i in [0:bits.size] do
    if bits[i] then cur := cur + 2 ^ (i % 8)
    if i % 8 == 7 then
      out := out.push (UInt8.ofNat cur)
      cur := 0
  if bits.size % 8 != 0 then out := out.push (UInt8.ofNat cur)
  return out

def be32 (v : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (v / 16777216 % 256), UInt8.ofNat (v / 65536 % 256),
    UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)]

/-- The integer Kraft sum of `lengths` at `width` bits. -/
def kraft (lengths : Array Nat) (width : Nat) : Nat :=
  lengths.foldl (fun acc l => if 0 < l && l ≤ width then acc + 2 ^ (width - l) else acc) 0

/-- A zlib stream of one final dynamic block: the code-length code's lengths `cl` by symbol, each
literal/length and distance length written as its `clCode` codeword, then the data codewords,
closed by the Adler-32 of `plain`. -/
def dynamicStream (cl : Array Nat) (clCode : Nat → Nat × Nat) (lit dist : Array Nat)
    (data : Array (Nat × Nat)) (plain : ByteArray) : ByteArray := Id.run do
  let order := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
  let ordered : Array Nat := order.map fun s => cl[s]?.getD 0
  let mut n := ordered.size
  for _ in [0:15] do
    if n > 4 && ordered[n - 1]?.getD 0 == 0 then n := n - 1
  let mut bits : Array Bool := #[true] ++ lsbBits 2 2 ++ lsbBits (lit.size - 257) 5 ++
    lsbBits (dist.size - 1) 5 ++ lsbBits (n - 4) 4
  for v in ordered.extract 0 n do bits := bits ++ lsbBits v 3
  for v in lit do
    let (c, l) := clCode v
    bits := bits ++ msbBits c l
  for v in dist do
    let (c, l) := clCode v
    bits := bits ++ msbBits c l
  for (c, l) in data do bits := bits ++ msbBits c l
  return ByteArray.mk #[0x78, 0x01] ++ packBits bits ++ be32 (Flate.adler32 plain)

/-- Lengths over `n` symbols giving one bit to `A`, to the end of block and to each of `extra`. -/
def oneBit (n : Nat) (extra : List Nat := []) : Array Nat :=
  (Array.range n).map fun s => if s == 65 || s == 256 || extra.contains s then 1 else 0

/-- What python3's zlib inflates `z` to, or `none` when it refuses it. -/
def foreignInflate (dir : System.FilePath) (z : ByteArray) : IO (Option ByteArray) := do
  let zPath := dir / "z.bin"
  let rPath := dir / "r.bin"
  IO.FS.writeBinFile zPath z
  let out ← IO.Process.output { cmd := "python3", args := #["-c",
    "import zlib,sys; open(sys.argv[2],'wb').write(zlib.decompress(open(sys.argv[1],'rb').read()))",
    zPath.toString, rPath.toString] }
  if out.exitCode != 0 then return none
  return some (← IO.FS.readBinFile rPath)

def refusedByBoth (dir : System.FilePath) (label : String) (z : ByteArray) : IO Unit := do
  if let .ok out := Flate.inflate z 65536 then
    die s!"{label}: inflate accepted a stream zlib refuses ({out.size} bytes out)"
  if (← foreignInflate dir z).isSome then die s!"{label}: the foreign inflater accepted it"

/-- What python3's zlib inflates each stream to, `none` where it refuses it, in one run: whole
zlib streams, or raw deflate when `raw`. -/
def foreignBatch (dir : System.FilePath) (raw : Bool) (zs : Array ByteArray) :
    IO (Array (Option ByteArray)) := do
  let inPath := dir / "batch.in"
  let outPath := dir / "batch.out"
  let mut buf := ByteArray.empty
  for z in zs do buf := buf ++ be32 z.size ++ z
  IO.FS.writeBinFile inPath buf
  let script := "import zlib,sys\n" ++
    "d=open(sys.argv[1],'rb').read(); o=bytearray(); i=0; w=-15 if sys.argv[3]=='raw' else 15\n" ++
    "while i < len(d):\n" ++
    "  n=int.from_bytes(d[i:i+4],'big'); z=d[i+4:i+4+n]; i+=4+n\n" ++
    "  try:\n" ++
    "    r=zlib.decompress(z,w); o+=b'\\x01'+len(r).to_bytes(4,'big')+r\n" ++
    "  except Exception:\n" ++
    "    o+=b'\\x00'\n" ++
    "open(sys.argv[2],'wb').write(o)\n"
  let run ← IO.Process.output { cmd := "python3", args := #["-I", "-c", script,
    inPath.toString, outPath.toString, if raw then "raw" else "zlib"] }
  if run.exitCode != 0 then die s!"the foreign batch failed: {run.stderr}"
  let o ← IO.FS.readBinFile outPath
  let mut out : Array (Option ByteArray) := #[]
  let mut i := 0
  for _ in [0:zs.size] do
    if o[i]?.getD 0 == 1 then
      let n := (o.extract (i + 1) (i + 5)).foldl (fun a b => a * 256 + b.toNat) 0
      out := out.push (some (o.extract (i + 5) (i + 5 + n)))
      i := i + 5 + n
    else
      out := out.push none
      i := i + 1
  return out

/-- The engine and zlib agree on each stream, refusing it or reading the same bytes; a raw
stream is read behind the two-byte header `78 01`. -/
def agree (dir : System.FilePath) (label : String) (raw : Bool) (zs : Array ByteArray) :
    IO Nat := do
  let foreign ← foreignBatch dir raw zs
  let mut read := 0
  for (z, k) in zs.zipIdx do
    let own := (Flate.inflate (if raw then ByteArray.mk #[0x78, 0x01] ++ z else z) (1 <<< 22)).toOption
    unless own == foreign[k]?.join do
      die s!"{label} #{k}: inflate {if own.isSome then "read" else "refused"} it, zlib \
{if (foreign[k]?.join).isSome then "read" else "refused"} it ({z.size} bytes)"
    if own.isSome then read := read + 1
  return read

/-- Random lengths over `n` symbols, each at most `maxLen`, whose Kraft sum overflows the code
space, the end of block given a length when `eob`. -/
def overSubscribed (s : UInt64) (n maxLen : Nat) (eob : Bool) : Array Nat × UInt64 := Id.run do
  let mut s := s
  let mut lens := Array.replicate n 0
  if eob then
    let (l, s1) := rand s maxLen
    s := s1
    lens := lens.set! 256 (l + 1)
  for _ in [0:4 * n + 64] do
    if kraft lens maxLen > 2 ^ maxLen then break
    let (k, s1) := rand s n
    let (l, s2) := rand s1 maxLen
    s := s2
    lens := lens.set! k (l + 1)
  if kraft lens maxLen ≤ 2 ^ maxLen then lens := ((lens.set! 0 1).set! 1 1).set! 2 1
  return (lens, s)

/-- Each of a dynamic block's three tables over-subscribed, by hand and at random: the engine
and zlib both refuse the stream, and the block written with complete tables both inflate. -/
def tableChecks (dir : System.FilePath) : IO Unit := do
  let aa := "AA".toUTF8
  let data := #[(0, 1), (0, 1), (1, 1)]
  let bit (v : Nat) : Nat × Nat := (v, 1)
  let complete := dynamicStream #[1, 1] bit (oneBit 257) #[0] data aa
  unless (Flate.inflate complete 65536).toOption == some aa do
    die "complete tables: inflate did not read AA"
  unless (← foreignInflate dir complete) == some aa do
    die "complete tables: the foreign inflater did not read AA"
  let clOver := (Array.replicate 19 0).set! 0 1 |>.set! 1 1 |>.set! 18 1
  refusedByBoth dir "over-subscribed code-length code"
    (dynamicStream clOver bit (oneBit 257) #[0] data aa)
  refusedByBoth dir "over-subscribed literal/length code"
    (dynamicStream #[1, 1] bit (oneBit 258 [257]) #[0] data aa)
  refusedByBoth dir "over-subscribed distance code"
    (dynamicStream #[1, 1] bit (oneBit 257) #[1, 1, 1] data aa)
  let nibble (v : Nat) : Nat × Nat := (v, 4)
  let flat := Array.replicate 16 4
  let mut s : UInt64 := 0x2545F4914F6CDD1D
  for k in [0:40] do
    let (nlit, s1) := rand s 30
    let (lit, s2) := overSubscribed s1 (257 + nlit) 15 true
    let (ndist, s3) := rand s2 28
    let (dist, s4) := overSubscribed s3 (ndist + 3) 15 false
    let (cl, s5) := overSubscribed s4 19 7 false
    s := s5
    refusedByBoth dir s!"random over-subscribed literal/length code #{k}"
      (dynamicStream flat nibble lit #[0] #[(0, 16)] aa)
    refusedByBoth dir s!"random over-subscribed distance code #{k}"
      (dynamicStream flat nibble (oneBit 257) dist data aa)
    refusedByBoth dir s!"random over-subscribed code-length code #{k}"
      (dynamicStream cl bit (oneBit 257) #[0] data aa)

/-- Random lengths over `n` symbols, each at most `maxLen`, leaving the code space incomplete in
none of the shapes zlib admits: two codes at least, the end of block one of them when `eob`. -/
def incomplete (s : UInt64) (n maxLen : Nat) (eob : Bool) : Array Nat × UInt64 := Id.run do
  let mut s := s
  let mut lens := Array.replicate n 0
  if eob then lens := lens.set! 256 maxLen
  let (stop, s0) := rand s (4 * n)
  s := s0
  for _ in [0:stop + 2] do
    let (k, s1) := rand s n
    let (l, s2) := rand s1 maxLen
    s := s2
    let trial := lens.set! k (l + 1)
    if kraft trial maxLen < 2 ^ maxLen then lens := trial
  if (lens.filter (· > 0)).size < 2 then
    lens := lens.set! (if eob then 0 else 1) maxLen
    lens := if (lens.filter (· > 0)).size < 2 then lens.set! 2 maxLen else lens
  return (lens, s)

/-- Random lengths over `n` symbols filling the code space, each at most `maxLen`: two one-bit
codes, the first `first`, then codes split at random. -/
def complete (s : UInt64) (n maxLen first : Nat) : Array Nat × UInt64 := Id.run do
  let mut s := s
  let (other, s0) := rand s n
  s := s0
  let second := if other == first then (first + 1) % n else other
  let mut lens := ((Array.replicate n 0).set! first 1).set! second 1
  let (splits, s1) := rand s (2 * n)
  s := s1
  for _ in [0:splits] do
    let (a, s2) := rand s n
    let (b, s3) := rand s2 n
    s := s3
    let la := lens[a]?.getD 0
    if 0 < la && la < maxLen && lens[b]?.getD 0 == 0 then
      lens := (lens.set! a (la + 1)).set! b (la + 1)
  return (lens, s)

/-- Each table left incomplete at random, zlib's admitted incomplete shapes, the zlib header's
every value, stored blocks' lengths, the alphabets' declared sizes and random deflate bodies: the
engine refuses and reads exactly what zlib does. -/
def parityChecks (dir : System.FilePath) : IO Unit := do
  let aa := "AA".toUTF8
  let data := #[(0, 1), (0, 1), (1, 1)]
  let bit (v : Nat) : Nat × Nat := (v, 1)
  let nibble (v : Nat) : Nat × Nat := (v, 4)
  let flat := Array.replicate 16 4
  let mut s : UInt64 := 0x6A09E667F3BCC908
  for k in [0:40] do
    let (nlit, s1) := rand s 30
    let (lit, s2) := incomplete s1 (257 + nlit) 15 true
    let (ndist, s3) := rand s2 28
    let (dist, s4) := incomplete s3 (ndist + 3) 15 false
    let (cl, s5) := incomplete s4 19 7 false
    s := s5
    refusedByBoth dir s!"random incomplete literal/length code #{k}"
      (dynamicStream flat nibble lit #[0] #[(0, 16)] aa)
    refusedByBoth dir s!"random incomplete distance code #{k}"
      (dynamicStream flat nibble (oneBit 257) dist data aa)
    refusedByBoth dir s!"random incomplete code-length code #{k}"
      (dynamicStream cl bit (oneBit 257) #[0] data aa)
  let only (n : Nat) (assign : List (Nat × Nat)) : Array Nat :=
    (Array.range n).map fun i => ((assign.find? (·.1 == i)).map (·.2)).getD 0
  let admitted := #[
    dynamicStream flat nibble (only 257 [(256, 1)]) #[0] #[(0, 1)] ByteArray.empty,
    dynamicStream flat nibble (only 258 [(65, 1), (256, 2), (257, 2)]) #[1]
      #[(0, 1), (3, 2), (0, 1), (2, 2)] "AAAA".toUTF8,
    dynamicStream flat nibble (only 257 [(65, 1), (256, 1)]) #[0] #[(0, 1), (1, 1)] "A".toUTF8]
  let readAdmitted ← agree dir "an incomplete shape zlib admits" false admitted
  unless readAdmitted == admitted.size do die "an incomplete shape zlib admits went unread"
  let trailer := be32 1
  let headers := (Array.range 65536).map fun v =>
    ByteArray.mk #[UInt8.ofNat (v / 256), UInt8.ofNat (v % 256), 3, 0] ++ trailer
  let readHeaders ← agree dir "a zlib header" false headers
  let mut stored : Array ByteArray := #[]
  for k in [0:2000] do
    let (len, s1) := rand s 24
    let (noise, s2) := rand s1 65536
    s := s2
    let nlen := if k % 2 == 0 then 65535 - len else noise
    stored := stored.push (ByteArray.mk #[1, UInt8.ofNat len, 0, UInt8.ofNat (nlen % 256),
      UInt8.ofNat (nlen / 256)] ++ ByteArray.mk (Array.replicate len 66))
  let readStored ← agree dir "a stored block" true stored
  let mut sizes : Array ByteArray := #[]
  for hlit in [0:32] do
    for hdist in [0:32] do
      let z := dynamicStream flat nibble (only (257 + hlit) [(65, 1), (256, 1)])
        (Array.replicate (hdist + 1) 0) #[(0, 1), (1, 1)] "A".toUTF8
      sizes := sizes.push z
  let readSizes ← agree dir "a declared alphabet size" false sizes
  let mut bodies : Array ByteArray := #[]
  for _ in [0:20000] do
    let (size, s1) := rand s 300
    let (first, s2) := rand s1 256
    s := s2
    let mut b : Array UInt8 := #[UInt8.ofNat ((first &&& 0xF9) ||| 0x04)]
    for _ in [0:size] do
      let (v, s3) := rand s 256
      s := s3
      b := b.push (UInt8.ofNat v)
    bodies := bodies.push (ByteArray.mk b)
  let readBodies ← agree dir "a random dynamic body" true bodies
  let mut blocks : Array ByteArray := #[]
  for _ in [0:5000] do
    let (nlit, s1) := rand s 30
    let (lit, s2) := complete s1 (257 + nlit) 15 256
    let (ndist, s3) := rand s2 30
    let (dist, s4) := complete s3 (ndist + 1) 15 0
    let (bits, s5) := rand s4 64
    s := s5
    let mut data : Array (Nat × Nat) := #[]
    for _ in [0:bits] do
      let (v, s6) := rand s 256
      s := s6
      data := data.push (v, 8)
    blocks := blocks.push (dynamicStream flat nibble lit (if ndist == 0 then #[0] else dist) data
      ByteArray.empty)
  let rawBlocks := blocks.map fun z => z.extract 2 (z.size - 4)
  let readRaw ← agree dir "a random complete block" true rawBlocks
  IO.println s!"flate-fuzz: zlib parity: {readAdmitted} admitted shapes, \
{readHeaders} of {headers.size} headers, {readStored} of {stored.size} stored blocks, \
{readSizes} of {sizes.size} alphabet sizes, {readBodies} of {bodies.size} random bodies and \
{readRaw} of {rawBlocks.size} random complete blocks read alike, the rest refused alike"

/-- Every `/FlateDecode` stream the engine's PDF writer emitted, inflated back, found by
the writer's own spelling. -/
def pdfStreams (pdf : ByteArray) : IO (Array ByteArray) := do
  let pat := " >>\nstream\n".toUTF8
  let mut out : Array ByteArray := #[]
  let mut i := 0
  for _ in [0:pdf.size] do
    if i + pat.size > pdf.size then break
    if (pdf.extract i (i + pat.size)) != pat then
      i := i + 1
      continue
    let head := String.ofList ((pdf.extract (i - min i 400) i).toList.map fun v =>
      Char.ofNat (min v.toNat 127))
    let dataOff := i + pat.size
    let some len := ((head.splitOn " /Length ").getLast?.bind fun p =>
        (p.splitOn " ").head?.bind (·.toNat?)) | i := i + 1; continue
    if (head.splitOn "/FlateDecode").length ≥ 2 then
      match Flate.inflate (pdf.extract dataOff (dataOff + len)) (len * 400 + 65536) with
      | .ok plain => out := out.push plain
      | .error e => die s!"stream at {dataOff}: {e}"
    i := dataOff + len
  return out

def main : IO Unit := do
  let dir ← IO.FS.createTempDir
  -- Degenerate and adversarial shapes.
  check dir "empty" ByteArray.empty
  check dir "one byte" (ByteArray.mk #[42])
  check dir "two bytes" (ByteArray.mk #[0, 255])
  check dir "all zero 100k" (ByteArray.mk (Array.replicate 100000 0))
  check dir "all same 70000" (ByteArray.mk (Array.replicate 70000 7))
  check dir "period 2" (ByteArray.mk (Array.ofFn (n := 65536) fun i => UInt8.ofNat (i % 2)))
  check dir "period 3" (ByteArray.mk (Array.ofFn (n := 999) fun i => UInt8.ofNat (i % 3)))
  check dir "ascending" (ByteArray.mk (Array.ofFn (n := 300000) fun i => UInt8.ofNat (i % 256)))
  check dir "text-like" (String.join (List.replicate 2000
    "the quick brown fox jumps over the lazy dog — pack my box. ")).toUTF8
  tableChecks dir
  parityChecks dir
  -- The shipped alpha fixture's planes: the exact bytes the PDF writer embeds.
  let alpha ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
  match Image.decode alpha with
  | .ok { data, alpha := .soft smask _, .. } =>
    match Flate.inflate data (32 * (1 + 48 * 3)), Flate.inflate smask (32 * (1 + 48)) with
    | .ok c, .ok a =>
      check dir "fixture colour plane (filtered)" c
      check dir "fixture alpha plane (filtered)" a
    | _, _ => die "fixture planes did not inflate"
  | .ok _ => die "fixture planned without a soft mask"
  | .error e => die s!"fixture refused: {e}"
  -- Every stream the writer emitted for the bench's underline document, judged twice.
  let pdfPath := dir / "underline.pdf"
  let built ← IO.Process.output {
    cmd := ".lake/build/bin/leantex"
    args := #["-q", "build", "bench/underline.tex", "-o", pdfPath.toString] }
  if built.exitCode != 0 then die s!"underline build failed: {built.stderr}"
  let streams ← pdfStreams (← IO.FS.readBinFile pdfPath)
  if streams.size < 45 then die s!"underline: {streams.size} flate streams, expected 45+"
  for (b, k) in streams.zipIdx do
    check dir s!"underline stream #{k} ({b.size} bytes)" b
  -- Random blobs, random sizes: incompressible input must survive too.
  let mut s : UInt64 := 0x9E3779B97F4A7C15
  for k in [0:40] do
    let (size, s1) := rand s 200000
    s := s1
    let mut arr : Array UInt8 := Array.mkEmpty size
    for _ in [0:size] do
      let (v, s2) := rand s 256
      s := s2
      arr := arr.push (UInt8.ofNat v)
    check dir s!"random #{k} ({size} bytes)" (ByteArray.mk arr)
  -- Mixed compressible and random segments, block statistics favouring neither extreme.
  for k in [0:10] do
    let (a, s1) := rand s 50000
    let (b, s2) := rand s1 50000
    s := s2
    let mut arr : Array UInt8 := Array.mkEmpty (a + b + 30000)
    for _ in [0:a] do
      let (v, s3) := rand s 256
      s := s3
      arr := arr.push (UInt8.ofNat v)
    for i in [0:30000] do
      arr := arr.push (UInt8.ofNat (i % 17))
    for _ in [0:b] do
      let (v, s3) := rand s 7
      s := s3
      arr := arr.push (UInt8.ofNat v)
    check dir s!"mixed #{k}" (ByteArray.mk arr)
  IO.FS.removeDirAll dir
  IO.println "flate-fuzz: all passed"
