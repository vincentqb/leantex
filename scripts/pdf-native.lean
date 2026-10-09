/-
The pdf-native tier: how far the engine draws a PDF figure itself.

  lake env lean --run scripts/pdf-native.lean               regenerate the `pdf-native` tier
  lake env lean --run scripts/pdf-native.lean --check       gate it (hermetic)
  lake env lean --run scripts/pdf-native.lean --selftest    the tier's cases
  lake env lean --run scripts/pdf-native.lean --fixtures    rewrite the hand-written fixture

Each item is a committed, invented PDF in testdata/pdf-native, made by a
tool the reader meets in practice — cairo through rsvg-convert, lualatex in
the repository's shipped faces, the engine's own writer — or written here by
hand in matplotlib's dialect (`matplotlibDialect`): PROVENANCE.txt names how
each was made, SHA256SUMS pins the bytes. Its value is what the importer
(`PdfGfx.importPage`) makes of page 1:

  2  drawn with nothing lost
  1  drawn, with its losses named
  0  refused

*The structural half is pending*: a 2 will also require the figure to equal
its committed reference as the other importer reads it (pdftocairo's SVG,
read by the SVG importer), once that importer lands. Until then a 2 is the
importer's own verdict. Hermetic: committed bytes only, no tool.
-/
import LeanTex
import scripts.Board

open LeanTex.Core Scoreboard

namespace PdfNative

def dir : String := "testdata/pdf-native"

/-- The tier's items: the committed fixtures, in a fixed order. -/
def fixtures : Array String :=
  #["cairo-chart.pdf", "leantex-strokes.pdf", "lualatex-shade.pdf", "lualatex-text.pdf",
    "matplotlib-dialect.pdf"]

/-- One PDF's value: the importer's verdict on page 1. -/
def value (pdf : ByteArray) : Int :=
  match PdfGfx.importPage pdf with
  | .error _ => 0
  | .ok imp => if imp.figure.losses.isEmpty then 2 else 1

/-- A one-file PDF of the given objects, numbered from 1, the first the
catalog: a classic cross-reference table and trailer. -/
def pdfOf (objects : Array String) : ByteArray := Id.run do
  let mut text := "%PDF-1.7\n"
  let mut offsets : Array Nat := #[]
  for (object, i) in objects.zipIdx do
    offsets := offsets.push text.utf8ByteSize
    text := text ++ s!"{i + 1} 0 obj\n{object}\nendobj\n"
  let xref := text.utf8ByteSize
  text := text ++ s!"xref\n0 {objects.size + 1}\n0000000000 65535 f \n"
  for offset in offsets do
    let digits := toString offset
    text := text ++ "".pushn '0' (10 - digits.length) ++ digits ++ " 00000 n \n"
  return (text ++ s!"trailer\n<< /Size {objects.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n").toUTF8

def stream (body : String) (dict : String := "") : String :=
  s!"<< /Length {body.utf8ByteSize} {dict}>>\nstream\n{body}\nendstream"

/-- **The hand-written matplotlib-dialect fixture**: what matplotlib's PDF
backend spells, invented content — a Type 3 font whose glyphs are `d1`
procedures that fill, with Differences and a ToUnicode CMap; an alpha
ExtGState; a marker form painted three times with the state it inherits; a
clip rectangle; a dashed line; an image under a soft mask, its samples in
ASCIIHex. -/
def matplotlibDialect : ByteArray := pdfOf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 120] /Contents 4 0 R /Resources \
<< /Font << /F1 5 0 R >> /ExtGState << /A1 << /Type /ExtGState /CA 0.8 /ca 0.8 >> \
/A2 << /Type /ExtGState /CA 1 /ca 1 >> >> /XObject << /M0 6 0 R /I1 7 0 R >> >> >>",
  stream "1 g 0 0 200 120 re f\n\
q 20 20 160 80 re W n\n\
/A1 gs 0.12 0.47 0.71 RG 0.12 0.47 0.71 rg 1.5 w 1 J 1 j\n\
20 30 m 60 70 l 100 50 l 140 90 l 180 60 l S\n\
q 1 0 0 1 60 70 cm /M0 Do Q\n\
q 1 0 0 1 100 50 cm /M0 Do Q\n\
q 1 0 0 1 140 90 cm /M0 Do Q\n\
Q\n\
/A2 gs [3 2] 0 d 0 0 0 RG 0.5 w 20 20 m 180 20 l S\n\
q 16 0 0 16 160 96 cm /I1 Do Q\n\
0 0 0 rg BT /F1 10 Tf 30 104 Td (ab) Tj ET",
  "<< /Type /Font /Subtype /Type3 /FontBBox [0 0 600 700] /FontMatrix [0.001 0 0 0.001 0 0] \
/CharProcs << /a 8 0 R /b 9 0 R >> /Encoding << /Type /Encoding /Differences [97 /a /b] >> \
/FirstChar 97 /LastChar 98 /Widths [600 600] /ToUnicode 10 0 R >>",
  stream "0 -3 m 1.66 -3 3 -1.66 3 0 c 3 1.66 1.66 3 0 3 c -1.66 3 -3 1.66 -3 0 c \
-3 -1.66 -1.66 -3 0 -3 c h B" "/Type /XObject /Subtype /Form /BBox [-4 -4 4 4] ",
  stream (String.join ((List.range 16).map fun i => if (i + i / 4) % 2 == 0 then "c03030" else "3060c0") ++ ">")
    "/Type /XObject /Subtype /Image /Width 4 /Height 4 /ColorSpace /DeviceRGB /BitsPerComponent 8 \
/Filter /ASCIIHexDecode /SMask 11 0 R ",
  stream "600 0 0 0 600 700 d1 100 0 m 500 0 l 300 700 l h f",
  stream "600 0 0 0 600 700 d1 100 0 m 500 0 l 500 700 l 100 700 l h f",
  stream "/CIDInit /ProcSet findresource begin 12 dict begin begincmap \
/CMapName /Placeholder-UCS def 1 begincodespacerange <00> <ff> endcodespacerange \
1 beginbfrange <61> <62> <0061> endbfrange endcmap end end",
  stream "00406080406080ff6080ffff80ffffff>"
    "/Type /XObject /Subtype /Image /Width 4 /Height 4 /ColorSpace /DeviceGray /BitsPerComponent 8 \
/Filter /ASCIIHexDecode "]

/-- The fixture's pins: `SHA256SUMS`, each line `<hash>  <file>`. -/
def pinFaults : IO (Array String) := do
  let sums := dir ++ "/SHA256SUMS"
  let entries ← match parsePins sums (← readFileOr sums) with
    | .ok es => pure es
    | .error e => return #[e]
  let mut faults : Array String := #[]
  for f in fixtures do
    match entries.find? (·.path == f) with
    | none => faults := faults.push s!"{sums}: no pin for {f}"
    | some e =>
      let p := dir ++ "/" ++ f
      if !(← System.FilePath.pathExists p) then faults := faults.push s!"{p}: pinned, and absent"
      else if sha256Hex (← IO.FS.readBinFile p) != e.pin then
        faults := faults.push s!"{p}: not the bytes its pin in {sums} names"
  return faults

def measureTier : IO (Array String × Array Row) := do
  let faults ← pinFaults
  unless faults.isEmpty do
    for f in faults do IO.eprintln f
    return (#[], #[])
  let mut rows : Array Row := #[]
  let mut counts := #[0, 0, 0]
  for f in fixtures do
    let v := value (← IO.FS.readBinFile (dir ++ "/" ++ f))
    counts := counts.modify v.toNat (· + 1)
    rows := rows.push { item := f, value := v }
  return (#[
    "# corpus: testdata/pdf-native, invented figures made by cairo (rsvg-convert), lualatex in the \
shipped faces, the engine's writer, and by hand in matplotlib's dialect (PROVENANCE.txt, SHA256SUMS)",
    "# value: PdfGfx.importPage on page 1 — 2 drawn with nothing lost, 1 drawn with its losses \
named, 0 refused; the structural half (equality with the other importer's reading) is pending",
    s!"# counts: {counts[2]!} at 2, {counts[1]!} at 1, {counts[0]!} at 0"], rows)

def selftest : IO UInt32 := tierSelftest "pdf-native" fun expect => do
  let committed ← IO.FS.readBinFile (dir ++ "/matplotlib-dialect.pdf")
  expect "the hand-written fixture is the file this script writes (--fixtures)"
    (committed == matplotlibDialect)
  expect "every fixture is pinned" (← pinFaults).isEmpty
  expect "a figure drawn with nothing lost is 2" (value matplotlibDialect == 2)
  let type1 := pdfOf #[
    "<< /Type /Catalog /Pages 2 0 R >>", "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 50 50] /Contents 4 0 R \
/Resources << /Font << /F1 5 0 R >> >> >>",
    stream "BT /F1 12 Tf (x) Tj ET",
    "<< /Type /Font /Subtype /Type1 /BaseFont /Placeholder >>"]
  expect "a figure drawn with a loss named is 1" (value type1 == 1)
  expect "a refused file is 0" (value "not a PDF".toUTF8 == 0)

end PdfNative

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--fixtures"] =>
    IO.FS.writeBinFile (PdfNative.dir ++ "/matplotlib-dialect.pdf") PdfNative.matplotlibDialect
    IO.println s!"wrote {PdfNative.dir}/matplotlib-dialect.pdf"
    return 0
  | _ => tierMain "pdf-native" .raw PdfNative.measureTier PdfNative.selftest args
