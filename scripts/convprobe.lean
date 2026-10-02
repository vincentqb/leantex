import LeanTex.Cli.ImageAssets

open LeanTex.Core LeanTex.Cli

private def probeSource (font : Bool) : ByteArray := Id.run do
  let content := if font then "BT /F1 12 Tf (Sample) Tj ET" else "0 0 20 20 re f"
  let mut objs := #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 100 100] >>",
    "<< /Type /Page /Parent 2 0 R /Contents 4 0 R" ++
      (if font then " /Resources << /Font << /F1 5 0 R >> >>" else "") ++ " >>",
    s!"<< /Length {content.utf8ByteSize} >>\nstream\n{content}\nendstream"]
  if font then objs := objs.push "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>"
  let mut out := "%PDF-1.7\n"
  let mut offsets : Array Nat := #[]
  for (obj, i) in objs.zipIdx do
    offsets := offsets.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{obj}\nendobj\n"
  let xref := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for offset in offsets do
    let digits := toString offset
    out := out ++ String.ofList (List.replicate (10 - digits.length) '0') ++ digits ++ " 00000 n \n"
  return (out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n").toUTF8

def main (args : List String) : IO UInt32 := do
  let result ← match args with
    | ["svg", file] => ImageAssets.svgPoster (← IO.FS.readBinFile file)
    | ["last", file] => ImageAssets.svgPoster (← IO.FS.readBinFile file) .last
    | ["pic"] => ImageAssets.picFace (probeSource false)
    | _ => ImageAssets.pdfSvg (probeSource (args.contains "font")) .first
  match result with
  | .ok bytes =>
    IO.println s!"OK {bytes.size} {Flate.contentKey bytes}"
    return 0
  | .error why =>
    IO.println s!"ERR {why}"
    return 1
