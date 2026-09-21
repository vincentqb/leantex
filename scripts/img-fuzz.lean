/-
Fuzz the image decoders. Run from the repository root:

  lake env lean --run scripts/img-fuzz.lean

Totality is the claim (never a crash, a verdict for every input) plus the
anchor that the pristine fixtures decode to their known sizes and the
colour-keyed synthetics to their exact masks or their refusal (never a
lie). Every truncation length of the shipped fixtures and the keyed
synthetics, single-byte mutants at seeded random offsets, and random blobs
go through `Image.decode`. This is
an executable oracle, not a theorem: it witnesses totality on millions of
bytes of input, it does not prove it.
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

-- Synthetic colour-keyed PNGs: the anchors for the tRNS path (structure
-- only, CRCs zero; the decoder never checks them).
def be32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

def chunk (tag : String) (data : List UInt8) : List UInt8 :=
  be32 data.length ++ (tag.toList.map fun c => UInt8.ofNat c.toNat) ++ data ++ [0, 0, 0, 0]

def keyedPng (bd ct : Nat) (plte trns : List UInt8) : ByteArray :=
  ⟨([137, 80, 78, 71, 13, 10, 26, 10] ++
    chunk "IHDR" (be32 4 ++ be32 4 ++ [UInt8.ofNat bd, UInt8.ofNat ct, 0, 0, 0]) ++
    (if plte.isEmpty then [] else chunk "PLTE" plte) ++
    chunk "tRNS" trns ++ chunk "IDAT" [0, 1, 2, 3] ++ chunk "IEND" []).toArray⟩

def main : IO Unit := do
  let png ← IO.FS.readBinFile "tests/corpus/rects.png"
  let jpg ← IO.FS.readBinFile "tests/corpus/rects.jpg"
  let pdf ← IO.FS.readBinFile "tests/corpus/figures/box.pdf"
  let keyedIdx := keyedPng 8 3 [0, 0, 0, 255, 255, 255, 255, 0, 0] [255, 0, 0]
  let keyedRgb := keyedPng 8 2 [] [0, 1, 0, 2, 0, 3]
  let keyed16 := keyedPng 16 2 [] [1, 0, 2, 0, 3, 0]
  let keyedGray := keyedPng 4 0 [] [0, 15]
  let partialIdx := keyedPng 8 3 [0, 0, 0, 255, 255, 255, 255, 0, 0] [0, 128, 255]
  -- The anchor: the pristine files decode to the sizes images-note.md
  -- records, and the keyed synthetics to their exact masks or their
  -- refusal. A fuzzer that cannot tell a lie from a verdict tests nothing.
  match Image.decode keyedIdx with
  | .ok inf =>
    unless inf.colorKey == #[1, 2] do die s!"keyed indexed png decoded to mask {inf.colorKey}"
  | .error e => die s!"keyed indexed png refused: {e}"
  match Image.decode keyedRgb with
  | .ok inf =>
    unless inf.colorKey == #[1, 1, 2, 2, 3, 3] do
      die s!"keyed rgb png decoded to mask {inf.colorKey}"
  | .error e => die s!"keyed rgb png refused: {e}"
  match Image.decode keyedGray with
  | .ok inf =>
    unless inf.colorKey == #[15, 15] do die s!"keyed grey png decoded to mask {inf.colorKey}"
  | .error e => die s!"keyed grey png refused: {e}"
  if (Image.decode partialIdx).isOk then die "partial indexed transparency embedded opaque"
  if (Image.decode keyed16).isOk then die "16-bit colour key embedded (readers drop it)"
  match Image.decode png with
  | .ok inf =>
    unless inf.pxW == 64 && inf.pxH == 40 && inf.format == .png do
      die s!"png decoded to {inf.pxW}x{inf.pxH}"
  | .error e => die s!"pristine png refused: {e}"
  match Image.decode jpg with
  | .ok inf =>
    unless inf.pxW == 64 && inf.pxH == 40 && inf.format == .jpeg do
      die s!"jpg decoded to {inf.pxW}x{inf.pxH}"
  | .error e => die s!"pristine jpg refused: {e}"
  -- The PDF fixture is the engine's own output (figures/box.tex): a 90x54mm
  -- card, 255x153 whole points.
  match Image.decode pdf with
  | .ok inf =>
    unless inf.pxW == 255 && inf.pxH == 153 && inf.format == .pdf do
      die s!"pdf decoded to {inf.pxW}x{inf.pxH}"
  | .error e => die s!"pristine pdf refused: {e}"
  let mut verdicts := 0
  let mut oks := 0
  -- Every truncation length of both raster fixtures and the keyed synthetics.
  for base in [png, jpg, keyedIdx, keyedRgb, keyedGray, partialIdx, keyed16] do
    for n in [0:base.size + 1] do
      if (Image.decode (base.extract 0 n)).isOk then oks := oks + 1
      verdicts := verdicts + 1
  -- The PDF fixture is ~100 KB, so its truncations are strided: every
  -- length below 512, then 2048 evenly spaced cuts across the rest.
  for n in [0:512] do
    if (Image.decode (pdf.extract 0 n)).isOk then oks := oks + 1
    verdicts := verdicts + 1
  for k in [0:2048] do
    let n := 512 + (pdf.size - 512) * k / 2048
    if (Image.decode (pdf.extract 0 n)).isOk then oks := oks + 1
    verdicts := verdicts + 1
  -- Single-byte mutants at seeded random offsets, all 256 values at some;
  -- the keyed synthetics' mutants walk the tRNS arm with every payload.
  let mut s : UInt64 := 88172645463325252
  for base in [png, jpg, pdf, keyedIdx, keyedRgb, keyedGray, partialIdx, keyed16] do
    for _ in [0:4000] do
      let (i, s') := rand s base.size
      let (v, s'') := rand s' 256
      s := s''
      let mutant := base.set! i (UInt8.ofNat v)
      if (Image.decode mutant).isOk then oks := oks + 1
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
        ⟨#[0xFF, 0xD8]⟩, ⟨#[0x25, 0x50, 0x44, 0x46, 0x2D]⟩] do
      if (Image.decode (prefix_ ++ blob)).isOk then oks := oks + 1
      verdicts := verdicts + 1
  IO.println s!"img-fuzz: {verdicts} inputs, {oks} decoded, rest refused, no crash, no lie"
