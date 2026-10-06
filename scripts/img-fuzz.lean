/-
Fuzz the image probe and planner. Run from the repository root:

  lake env lean --run scripts/img-fuzz.lean

Totality is the claim (never a crash, a verdict for every input) plus the
anchors: the pristine fixtures probe and plan to their known sizes, the
colour-keyed synthetics to their exact masks or their refusal, the
profiled, oriented and ancillary-chunk synthetics to their source facts
and ledger entries, and every recognised-but-unembeddable header to a
refusal that names its format (never a lie). Every truncation length of
the shipped fixtures and the synthetics, single-byte mutants at seeded
random offsets, and random blobs go through `Image.probe` and
`Image.plan`. This is an executable oracle, not a theorem: it witnesses
totality on millions of bytes of input, it does not prove it.
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
  IO.eprintln s!"img-fuzz: FAIL {msg}"
  IO.Process.exit 1

-- Synthetic PNGs (structure only, CRCs zero; the probe never checks them).
def be32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

def chunk (tag : String) (data : List UInt8) : List UInt8 :=
  be32 data.length ++ (tag.toList.map fun c => UInt8.ofNat c.toNat) ++ data ++ [0, 0, 0, 0]

def pngOf (bd ct : Nat) (extra : List UInt8) : ByteArray :=
  ⟨([137, 80, 78, 71, 13, 10, 26, 10] ++
    chunk "IHDR" (be32 4 ++ be32 4 ++ [UInt8.ofNat bd, UInt8.ofNat ct, 0, 0, 0]) ++
    extra ++ chunk "IDAT" [0, 1, 2, 3] ++ chunk "IEND" []).toArray⟩

def keyedPng (bd ct : Nat) (plte trns : List UInt8) : ByteArray :=
  pngOf bd ct ((if plte.isEmpty then [] else chunk "PLTE" plte) ++ chunk "tRNS" trns)

-- Synthetic JPEG headers: SOI, the given segments, SOF0, SOS.
def jpegSeg (m : Nat) (payload : List UInt8) : List UInt8 :=
  let len := payload.length + 2
  [0xFF, UInt8.ofNat m, UInt8.ofNat (len / 256), UInt8.ofNat (len % 256)] ++ payload

def jpegOf (apps : List UInt8) : ByteArray :=
  ⟨([0xFF, 0xD8] ++ apps ++
    [0xFF, 0xC0, 0, 17, 8, 0, 1, 0, 2, 3, 1, 0x11, 0, 2, 0x11, 0, 3, 0x11, 0] ++
    [0xFF, 0xDA]).toArray⟩

def exifApp1 (o : Nat) : List UInt8 :=
  jpegSeg 0xE1 ([0x45, 0x78, 0x69, 0x66, 0, 0, 0x4D, 0x4D, 0, 42] ++ be32 8 ++ [0, 1] ++
    [0x01, 0x12, 0, 3] ++ be32 1 ++ [0, UInt8.ofNat o, 0, 0] ++ be32 0)

def iccApp2 (seq count : Nat) (data : List UInt8) : List UInt8 :=
  jpegSeg 0xE2 ([0x49, 0x43, 0x43, 0x5F, 0x50, 0x52, 0x4F, 0x46, 0x49, 0x4C, 0x45, 0,
    UInt8.ofNat seq, UInt8.ofNat count] ++ data)

def plan (b : ByteArray) : Except String Image.Plan :=
  Image.probe b >>= Image.plan Image.PlanParams.default

def keyOf (pl : Image.Plan) : Array Nat :=
  match pl.alpha with
  | .colorKey ks => ks
  | .opaque => #[]
  | .soft _ _ => #[]

def main : IO Unit := do
  let png ← IO.FS.readBinFile "testdata/corpus/rects.png"
  let jpg ← IO.FS.readBinFile "testdata/corpus/rects.jpg"
  let pdf ← IO.FS.readBinFile "testdata/corpus/figures/box.pdf"
  let keyedIdx := keyedPng 8 3 [0, 0, 0, 255, 255, 255, 255, 0, 0] [255, 0, 0]
  let keyedRgb := keyedPng 8 2 [] [0, 1, 0, 2, 0, 3]
  let keyed16 := keyedPng 16 2 [] [1, 0, 2, 0, 3, 0]
  let keyedGray := keyedPng 4 0 [] [0, 15]
  let partialIdx := keyedPng 8 3 [0, 0, 0, 255, 255, 255, 255, 0, 0] [0, 128, 255]
  let profile : List UInt8 := (List.range 40).map fun k => UInt8.ofNat (k * 7 % 256)
  let iccpPng := pngOf 8 2 (chunk "iCCP" ([0x69, 0x63, 0x63, 0, 0] ++
    (Flate.deflateStored ⟨profile.toArray⟩).toList))
  let ancillaryPng := pngOf 8 0 (chunk "sRGB" [0] ++ chunk "gAMA" (be32 45455) ++
    chunk "cHRM" ((List.range 8).flatMap fun k => be32 (k + 1)))
  let exifJpg := jpegOf (exifApp1 6)
  let iccJpg := jpegOf (iccApp2 2 2 [4, 5, 6] ++ iccApp2 1 2 [1, 2, 3])
  let le24 (n : Nat) : List UInt8 :=
    [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n / 65536 % 256)]
  let webp : ByteArray := ⟨([0x52, 0x49, 0x46, 0x46] ++ (be32 30).reverse ++
    [0x57, 0x45, 0x42, 0x50, 0x56, 0x50, 0x38, 0x58] ++ (be32 10).reverse ++ [0, 0, 0, 0] ++
    le24 299 ++ le24 199).toArray⟩
  let avif : ByteArray := ⟨(be32 20 ++ [0x66, 0x74, 0x79, 0x70, 0x61, 0x76, 0x69, 0x66] ++ be32 0 ++
    [0x6D, 0x69, 0x66, 0x31, 0x61, 0x76, 0x69, 0x66] ++ be32 20 ++ [0x69, 0x73, 0x70, 0x65] ++
    be32 0 ++ be32 640 ++ be32 480).toArray⟩
  let jxl : ByteArray := ⟨#[0xFF, 0x0A, 0x41, 0]⟩
  let jp2 : ByteArray := ⟨([0, 0, 0, 0x0C, 0x6A, 0x50, 0x20, 0x20, 0x0D, 0x0A, 0x87, 0x0A] ++
    be32 22 ++ [0x69, 0x68, 0x64, 0x72] ++ be32 3 ++ be32 4 ++ [0, 3, 7, 7, 0, 0]).toArray⟩
  let j2k : ByteArray := ⟨([0xFF, 0x4F, 0xFF, 0x51, 0, 41, 0, 0] ++ be32 10 ++ be32 6 ++
    be32 2 ++ be32 1).toArray⟩
  -- The anchors: the pristine files probe and plan to the sizes
  -- images-note.md records, the keyed synthetics to their exact masks or
  -- their refusal, the profiled and oriented ones to their ledger entries,
  -- and each unembeddable header to a refusal opening with its format's
  -- name. A fuzzer that cannot tell a lie from a verdict tests nothing.
  match plan keyedIdx with
  | .ok pl =>
    unless keyOf pl == #[1, 2] do die s!"keyed indexed png planned to mask {keyOf pl}"
  | .error e => die s!"keyed indexed png refused: {e}"
  match plan keyedRgb with
  | .ok pl =>
    unless keyOf pl == #[1, 1, 2, 2, 3, 3] do
      die s!"keyed rgb png planned to mask {keyOf pl}"
  | .error e => die s!"keyed rgb png refused: {e}"
  match plan keyedGray with
  | .ok pl =>
    unless keyOf pl == #[15, 15] do die s!"keyed grey png planned to mask {keyOf pl}"
  | .error e => die s!"keyed grey png refused: {e}"
  if (plan partialIdx).isOk then die "partial indexed transparency embedded opaque"
  if (plan keyed16).isOk then die "16-bit colour key embedded (readers drop it)"
  match Image.probe iccpPng, plan iccpPng with
  | .ok s, .ok pl =>
    unless s.iccIsZlib && s.icc.size > 0 && pl.losses == #[.iccDropped] do
      die "profiled png: profile not read, or its drop not in the ledger"
  | _, _ => die "profiled png refused"
  match Image.probe ancillaryPng, plan ancillaryPng with
  | .ok s, .ok pl =>
    unless s.srgbIntent == some 0 && s.gamma == some 45455 && s.chrm.isSome &&
        pl.losses.isEmpty do
      die "ancillary chunks not read as source facts"
  | _, _ => die "ancillary png refused"
  match Image.probe exifJpg, plan exifJpg with
  | .ok s, .ok pl =>
    unless s.orientation == 6 && pl.losses == #[.orientationDropped] do
      die "oriented jpeg: tag not read, or its drop not in the ledger"
  | _, _ => die "oriented jpeg refused"
  match Image.probe iccJpg, plan iccJpg with
  | .ok s, .ok pl =>
    unless s.icc == ⟨#[1, 2, 3, 4, 5, 6]⟩ && !s.iccIsZlib && pl.losses == #[.iccDropped] do
      die "jpeg profile pieces not concatenated in order, or not in the ledger"
  | _, _ => die "profiled jpeg refused"
  for (name, b, w, h) in [("WebP", webp, 300, 200), ("AVIF", avif, 640, 480),
      ("JPEG XL", jxl, 8, 8), ("JPEG 2000", jp2, 4, 3), ("JPEG 2000", j2k, 8, 5)] do
    match Image.probe b with
    | .ok s =>
      unless s.pxW == w && s.pxH == h do die s!"{name} header probed to {s.pxW}x{s.pxH}"
    | .error e => die s!"{name} header refused by the probe: {e}"
    match plan b with
    | .ok _ => die s!"{name} embedded"
    | .error e => unless e.startsWith name do die s!"{name} refusal does not name it: {e}"
  match plan png with
  | .ok pl =>
    unless pl.pxW == 64 && pl.pxH == 40 && pl.filter == .flatePredictor do
      die s!"png planned to {pl.pxW}x{pl.pxH}"
  | .error e => die s!"pristine png refused: {e}"
  match plan jpg with
  | .ok pl =>
    unless pl.pxW == 64 && pl.pxH == 40 && pl.filter == .dct do
      die s!"jpg planned to {pl.pxW}x{pl.pxH}"
  | .error e => die s!"pristine jpg refused: {e}"
  -- The PDF fixture is the engine's own output (figures/box.tex): a 90x54mm
  -- card, 255x153 whole points.
  match plan pdf with
  | .ok pl =>
    unless pl.pxW == 255 && pl.pxH == 153 && pl.form.isSome do
      die s!"pdf planned to {pl.pxW}x{pl.pxH}"
  | .error e => die s!"pristine pdf refused: {e}"
  let mut verdicts := 0
  let mut oks := 0
  let synthetics := [keyedIdx, keyedRgb, keyedGray, partialIdx, keyed16, iccpPng, ancillaryPng,
    exifJpg, iccJpg, webp, avif, jxl, jp2, j2k]
  -- Every truncation length of both raster fixtures and the synthetics.
  for base in png :: jpg :: synthetics do
    for n in [0:base.size + 1] do
      if (plan (base.extract 0 n)).isOk then oks := oks + 1
      verdicts := verdicts + 1
  -- The PDF fixture is ~100 KB, so its truncations are strided: every
  -- length below 512, then 2048 evenly spaced cuts across the rest.
  for n in [0:512] do
    if (plan (pdf.extract 0 n)).isOk then oks := oks + 1
    verdicts := verdicts + 1
  for k in [0:2048] do
    let n := 512 + (pdf.size - 512) * k / 2048
    if (plan (pdf.extract 0 n)).isOk then oks := oks + 1
    verdicts := verdicts + 1
  -- Single-byte mutants at seeded random offsets, all 256 values at some;
  -- the synthetics' mutants walk every header arm with every payload.
  let mut s : UInt64 := 88172645463325252
  for base in png :: jpg :: pdf :: synthetics do
    for _ in [0:4000] do
      let (i, s') := rand s base.size
      let (v, s'') := rand s' 256
      s := s''
      let mutant := base.set! i (UInt8.ofNat v)
      if (plan mutant).isOk then oks := oks + 1
      verdicts := verdicts + 1
  -- Random blobs, some opening with each signature so the walkers run.
  for _ in [0:2000] do
    let (len, s') := rand s 512
    let mut blob := ByteArray.empty
    let mut st := s'
    for _ in [0:len] do
      let (v, st') := rand st 256
      st := st'
      blob := blob.push (UInt8.ofNat v)
    s := st
    for prefix_ in [ByteArray.empty, ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩,
        ⟨#[0xFF, 0xD8]⟩, ⟨#[0x25, 0x50, 0x44, 0x46, 0x2D]⟩,
        ⟨#[0x52, 0x49, 0x46, 0x46, 0, 0, 0, 0, 0x57, 0x45, 0x42, 0x50]⟩,
        ⟨#[0, 0, 0, 20, 0x66, 0x74, 0x79, 0x70, 0x61, 0x76, 0x69, 0x66]⟩,
        ⟨#[0xFF, 0x0A]⟩,
        ⟨#[0, 0, 0, 0x0C, 0x4A, 0x58, 0x4C, 0x20, 0x0D, 0x0A, 0x87, 0x0A]⟩,
        ⟨#[0, 0, 0, 0x0C, 0x6A, 0x50, 0x20, 0x20, 0x0D, 0x0A, 0x87, 0x0A]⟩,
        ⟨#[0xFF, 0x4F, 0xFF, 0x51]⟩] do
      if (plan (prefix_ ++ blob)).isOk then oks := oks + 1
      verdicts := verdicts + 1
  IO.println s!"img-fuzz: {verdicts} inputs, {oks} planned, rest refused, no crash, no lie"
