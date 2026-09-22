/-
Fuzz the compressor. Run from the repository root:

  lake env lean --run scripts/flate-fuzz.lean

The claim under test is `inflate_deflate_id`'s statement — the engine's
own inflate inverts its deflate on every input — witnessed here on random
and adversarial byte strings, the shipped fixtures' decoded planes, and
every stream the PDF writer emits for the bench's underline document
(needs `lake build` first: the built binary produces them).
Two graders judge every stream: the engine's `inflate`, and a foreign
inflater (python3's zlib) so a defect the engine's decoder happens to
forgive is still caught. An executable oracle, not a theorem: it witnesses
the round trip on megabytes of input, it does not prove it.
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

/-- Every `/FlateDecode` stream the engine's PDF writer emitted for a
document, inflated back to the bytes it compressed: the writer's own
spelling (`/Length n >>\nstream\n`) is the anchor. -/
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
  -- The shipped alpha fixture's planes: the exact bytes the PDF writer embeds.
  let alpha ← IO.FS.readBinFile "tests/corpus/rects-alpha.png"
  match Image.decode alpha with
  | .ok { data, alpha := .soft smask _, .. } =>
    match Flate.inflate data (32 * (1 + 48 * 3)), Flate.inflate smask (32 * (1 + 48)) with
    | .ok c, .ok a =>
      check dir "fixture colour plane (filtered)" c
      check dir "fixture alpha plane (filtered)" a
    | _, _ => die "fixture planes did not inflate"
  | .ok _ => die "fixture planned without a soft mask"
  | .error e => die s!"fixture refused: {e}"
  -- The bench's underline document: 45 pages of content streams, the
  -- text-shaped input the compressor is tuned on — every stream the
  -- writer emitted for it, re-deflated here and judged twice.
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
  -- Mixed compressible/random segments: block statistics that favour
  -- neither extreme.
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
