import LeanTex.Cli.ImageAssets

/-! A single conversion, driven through the real `ImageAssets.picFace` — the
same `byteConv`/`ConvCache`/atomic-rename path a build uses. The cache IO
oracle (`scripts/conv-cache-io.lean`) spawns many of these concurrently
against one shared `XDG_CACHE_HOME` with a stub `pdftocairo` on `PATH`, so
they race to fill one slot; each prints the length and a checksum of the
bytes it was served, and the oracle proves no writer ever published an
incomplete file. Hermetic: the stub tool decides the bytes, no real converter
or network is touched. -/

private def checksum (b : ByteArray) : Nat :=
  b.foldl (fun acc x => (acc * 131 + x.toNat) % 1000000007) 1

/-- A minimal, parseable, font-free single-page PDF, with a correct xref
table and trailer. `picFace`'s typed precondition (`ConvCache.pdfSelfContained`)
reads the file's census before it runs the tool and refuses any PDF that does
not embed every font; a font-free page is vacuously embedded, so this input
passes the gate and reaches the stub. The stub ignores the bytes, so every
probe still hashes to one shared slot. -/
private def probeSource : ByteArray := Id.run do
  let content := "0 0 20 20 re f"
  let objs : Array String := #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 100 100] >>",
    "<< /Type /Page /Parent 2 0 R /Contents 4 0 R >>",
    s!"<< /Length {content.utf8ByteSize} >>\nstream\n{content}\nendstream"]
  let mut out := "%PDF-1.7\n"
  let mut offsets : Array Nat := #[]
  for (obj, i) in objs.zipIdx do
    offsets := offsets.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{obj}\nendobj\n"
  let xref := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for offset in offsets do
    let digits := toString offset
    let padded := String.ofList (List.replicate (10 - digits.length) '0') ++ digits
    out := out ++ s!"{padded} 00000 n \n"
  out := out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\n"
  out := out ++ s!"startxref\n{xref}\n%%EOF\n"
  return out.toUTF8

def main : IO UInt32 := do
  match ← LeanTex.Cli.ImageAssets.picFace probeSource with
  | .ok bytes =>
    IO.println s!"OK {bytes.size} {checksum bytes}"
    return 0
  | .error e =>
    IO.println s!"ERR {e}"
    return 1
