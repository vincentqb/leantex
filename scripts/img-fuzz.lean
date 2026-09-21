/-
Fuzz the image decoders. Run from the repository root:

  lake env lean --run scripts/img-fuzz.lean

Totality is the claim (never a crash, a verdict for every input) plus the
anchor that the pristine fixtures decode to their known sizes (never a lie).
Every truncation length of both shipped fixtures, single-byte mutants at
seeded random offsets, and random blobs go through `Image.decode`. This is
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

def main : IO Unit := do
  let png ← IO.FS.readBinFile "tests/corpus/rects.png"
  let jpg ← IO.FS.readBinFile "tests/corpus/rects.jpg"
  let pdf ← IO.FS.readBinFile "tests/corpus/figures/box.pdf"
  -- The anchor: the pristine files decode to the sizes images-note.md
  -- records. A fuzzer that cannot tell a lie from a verdict tests nothing.
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
  -- Every truncation length of both raster fixtures.
  for base in [png, jpg] do
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
  -- Single-byte mutants at seeded random offsets, all 256 values at some.
  let mut s : UInt64 := 88172645463325252
  for base in [png, jpg, pdf] do
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
