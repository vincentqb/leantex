import Tests.Support
import LeanTex.Cli.ImageAssets

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- A minimal raw PDF from a list of object bodies (object `n` is the `n`th,
1-based), with a correct xref table and a trailer naming object 1 as
`/Root`. The engine's own reader parses it; the fonts are declared by hand
so a file can carry an *unembedded* one — which the writer never emits, so
no engine-produced fixture could exercise the refusal. -/
private def rawPdf (objs : Array String) : ByteArray := Id.run do
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

private def stream (content : String) (attrs : String := "") : String :=
  s!"<< /Length {content.utf8ByteSize} {attrs} >>\nstream\n{content}\nendstream"

/-- A one-page PDF whose single font is a subsetted Type 1 face with its
program embedded via `/FontFile3`: the census reads it as fully embedded. -/
private def embeddedFontPdf : ByteArray := rawPdf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] \
/Resources << /Font << /F1 5 0 R >> >> >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R >>",
  stream "BT /F1 12 Tf 20 100 Td (Synthetic) Tj ET",
  "<< /Type /Font /Subtype /Type1 /BaseFont /ABCDEF+Synthetic /FontDescriptor 6 0 R >>",
  "<< /Type /FontDescriptor /FontName /ABCDEF+Synthetic /Flags 4 /FontFile3 7 0 R >>",
  stream "CFFPROGRAMBYTES" "/Subtype /Type1C"]

/-- The same page with the font left unembedded — a standard-fourteen base
font, with no `FontDescriptor` and so no `FontFile*`. This is exactly the
file whose browser face would depend on the host's installed fonts, so the
precondition must refuse it. -/
private def unembeddedFontPdf : ByteArray := rawPdf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] \
/Resources << /Font << /F1 5 0 R >> >> >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R >>",
  stream "BT /F1 12 Tf 20 100 Td (Synthetic) Tj ET",
  "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>"]

/-- A page with no font at all: fonts-embedded is vacuously true, so the
precondition admits it — nothing can be substituted. -/
private def noFontPdf : ByteArray := rawPdf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R >>",
  stream "0 0 20 20 re f"]

/-- The PDF-fonts precondition: a host PDF→SVG conversion (`pdftocairo`)
must never depend on the machine's installed fonts, so a PDF handed to it is
refused deterministically — before the cache or the tool — unless the file's
own read-side census says every font embeds its program. All fixtures are
synthetic raw PDFs; the refusal needs no converter, so this oracle is
hermetic. -/
def pdfFontEmbeddingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The read-side census agrees with the fixtures it is judging.
  t "embedded fixture: census reads every font as embedded"
    (match pdfCensusOf embeddedFontPdf with | .ok c => c.fontsEmbedded | .error _ => false)
  t "unembedded fixture: census reads a font as not embedded"
    (match pdfCensusOf unembeddedFontPdf with | .ok c => !c.fontsEmbedded | .error _ => false)
  -- The typed precondition accepts the embedded and font-free files and
  -- refuses the unembedded one with the single shared reason.
  t "precondition admits an all-embedded PDF"
    (ConvCache.pdfSelfContained embeddedFontPdf == .ok ())
  t "precondition admits a font-free PDF (vacuously embedded)"
    (ConvCache.pdfSelfContained noFontPdf == .ok ())
  t "precondition refuses an unembedded-font PDF with the exact reason"
    (ConvCache.pdfSelfContained unembeddedFontPdf == .error ConvCache.unembeddedFontReason)
  -- A file the census cannot read is refused, never admitted: embedding
  -- cannot be shown, so the conversion would not be host-independent.
  t "precondition refuses an input that is not a readable PDF"
    (match ConvCache.pdfSelfContained "this is not a pdf".toUTF8 with
      | .error _ => true | .ok () => false)
  -- Exactly the PDF-reading ops carry the gate.
  t "the PDF-reading ops carry the gate; the SVG ops do not"
    (ConvCache.Op.readsPdf (.pdfPage 2) && ConvCache.Op.readsPdf .picFace &&
      !ConvCache.Op.readsPdf .svgPdf && !ConvCache.Op.readsPdf .svgPoster &&
      !ConvCache.Op.readsPdf .validate)
  -- The gate fires inside byteConv before any cache lookup or tool run: the
  -- refusal comes back with no converter installed and nothing cached.
  let page ← ImageAssets.byteConv (.pdfPage 1) unembeddedFontPdf
  t "byteConv .pdfPage refuses an unembedded-font PDF before the tool"
    (page == .error ConvCache.unembeddedFontReason)
  let face ← ImageAssets.byteConv .picFace unembeddedFontPdf
  t "byteConv .picFace refuses an unembedded-font PDF before the tool"
    (face == .error ConvCache.unembeddedFontReason)
  -- The driver's browser-face paths route through the same gate, so the
  -- refusal reason is what surfaces (as the W0605 text) rather than a
  -- host-dependent face.
  let svg ← ImageAssets.pdfSvg unembeddedFontPdf .first
  t "pdfSvg refuses an unembedded-font PDF with the font reason"
    (match svg with | .error e => hasStr e "does not embed every font" | .ok _ => false)
  let pic ← ImageAssets.picFace unembeddedFontPdf
  t "picFace refuses an unembedded-font PDF with the font reason"
    (match pic with | .error e => hasStr e "does not embed every font" | .ok _ => false)

end Tests
