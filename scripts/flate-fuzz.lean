/-
Fuzz the codec against python3's zlib: inflate inverts deflate on random, adversarial, fixture and
PDF-writer bytes, and refuses each over-subscribed Huffman table zlib refuses.
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
    die s!"{label}: inflate accepted an over-subscribed table ({out.size} bytes out)"
  if (← foreignInflate dir z).isSome then die s!"{label}: the foreign inflater accepted it"

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
