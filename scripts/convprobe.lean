import LeanTex.Cli.ImageAssets

/-! A single conversion, driven through the real `ImageAssets.picFace` — the
same `byteConv`/`ConvCache`/atomic-rename path a build uses. The cache IO
oracle (`scripts/conv-cache-io.lean`) spawns many of these concurrently
against one shared `XDG_CACHE_HOME` with a stub `pdftocairo` on `PATH`, so
they race to fill one slot; each prints the length and a checksum of the
bytes it was served, and the oracle proves no writer ever published a
an incomplete file. Hermetic: the stub tool decides the bytes, no real converter
or network is touched. -/

private def checksum (b : ByteArray) : Nat :=
  b.foldl (fun acc x => (acc * 131 + x.toNat) % 1000000007) 1

def main : IO UInt32 := do
  -- Any stable, non-empty payload: the stub `pdftocairo` ignores the input
  -- content, so every probe hashes to one shared slot.
  let input := "%PDF-1.7\nprobe source\n%%EOF\n".toUTF8
  match ← LeanTex.Cli.ImageAssets.picFace input with
  | .ok bytes =>
    IO.println s!"OK {bytes.size} {checksum bytes}"
    return 0
  | .error e =>
    IO.println s!"ERR {e}"
    return 1
