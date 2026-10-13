/-
The pdf-native tier: `PdfGfx.importPage`'s verdict on each committed invented PDF, 2 drawn
whole, 1 with losses named, 0 refused.
Usage: lake env lean --run scripts/pdf-native.lean [--check | --selftest | --fixtures]
-/
import LeanTex
import scripts.Board

open LeanTex.Core Scoreboard

namespace PdfNative

def dir : String := "testdata/pdf-native"

/-- The tier's items: the committed fixtures, in a fixed order. -/
def fixtures : Array String :=
  #["cairo-chart.pdf", "geometry-dialect.pdf", "leantex-strokes.pdf", "lualatex-shade.pdf",
    "lualatex-strokedtext.pdf", "lualatex-text.pdf", "matplotlib-dialect.pdf", "print-dialect.pdf",
    "text-dialect.pdf"]

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

/-- The hand-written matplotlib-dialect fixture: a Type 3 font of filled `d1` glyphs with
Differences and a ToUnicode CMap, an alpha ExtGState, a marker form painted three times, a
clip, a dash, and a soft-masked ASCIIHex image. -/
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

/-- The hand-written print-dialect fixture: device CMYK fills and strokes, a CMYK image,
an indexed image over a CMYK base, and a CMYK axial shading. -/
def printDialect : ByteArray := pdfOf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 120] /Contents 4 0 R /Resources \
<< /XObject << /I1 5 0 R /I2 6 0 R >> /Shading << /S0 7 0 R >> >> >>",
  stream "0 0 0 0 k 0 0 200 120 re f\n\
0 0 0 1 k 10 70 40 40 re f\n\
1 0 0 0 k 60 70 40 40 re f\n\
0 1 0 0 k 110 70 40 40 re f\n\
0 0 1 0 k 160 70 30 40 re f\n\
0.2 0.6 0 0.1 K 3 w 10 60 m 190 60 l S\n\
q 10 10 180 40 re W n q 180 0 0 40 10 10 cm /S0 sh Q Q\n\
q 30 0 0 30 20 15 cm /I1 Do Q\n\
q 30 0 0 30 150 15 cm /I2 Do Q",
  stream (String.join ((List.range 16).map fun i =>
      if (i + i / 4) % 2 == 0 then "00ff0000" else "ff00002a") ++ ">")
    "/Type /XObject /Subtype /Image /Width 4 /Height 4 /ColorSpace /DeviceCMYK /BitsPerComponent 8 \
/Filter /ASCIIHexDecode ",
  stream "00010201>"
    "/Type /XObject /Subtype /Image /Width 2 /Height 2 /ColorSpace [/Indexed /DeviceCMYK 2 \
<000000ff 00ffff00 ff000000>] /BitsPerComponent 8 /Filter /ASCIIHexDecode ",
  "<< /ShadingType 2 /ColorSpace /DeviceCMYK /Coords [0 0 1 0] \
/Function << /FunctionType 2 /Domain [0 1] /C0 [0 0.8 0 0] /C1 [1 0.8 0 0] /N 1 >> /Extend [true true] >>"]

/-- The hand-written geometry fixture: shapes whose drawing turns on ISO 32000-2 §8.5.3,
zero- and negative-extent rectangles, a dashed curve, degenerate subpaths under each cap,
a negative `re` clip, and inline images. -/
def geometryDialect : ByteArray := pdfOf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 120] /Contents 4 0 R >>",
  stream "1 g 0 0 200 120 re f\n\
0 0 0 RG 1.5 w 10 105 60 0 re S\n\
10 20 0 70 re S\n\
[6 3] 0 d 0.8 0.1 0.1 RG 1 w 190 110 -60 -40 re S\n\
[4 2] 1 d 0.1 0.5 0.1 RG 2 w 30 40 m 30 60 50 80 70 80 c 90 80 110 60 110 40 c S\n\
[] 0 d 0 0 0.8 RG 6 w 2 J 140 20 m 140 20 l S\n\
1 J 160 20 m h S\n\
0 J 180 20 m 180 20 l S\n\
q 120 35 -30 -20 re W n 0.9 0.6 0.1 rg 80 5 50 40 re f Q\n\
q 20 0 0 20 140 40 cm BI /W 2 /H 2 /CS /RGB /BPC 8 /F /AHx ID ff000000ff000000ffffff00> EI Q\n\
q 20 0 0 20 165 40 cm BI /W 2 /H 1 /CS /G /BPC 8 /F /AHx ID 20e0> EI Q"]

/-- The hand-written text fixture: leading and `T*`, character and word spacing,
horizontal scaling, rise, both quote operators, a `TJ` adjustment and a rotated matrix,
over a Type 3 font with a ToUnicode CMap. -/
def textDialect : ByteArray := pdfOf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 120] /Contents 4 0 R /Resources \
<< /Font << /F1 5 0 R >> >> >>",
  stream "1 g 0 0 200 120 re f 0 g\n\
BT /F1 12 Tf 14 TL 10 100 Td (ab ab) Tj T* 2 Tc (ab ab) Tj T* 0 Tc 6 Tw (ab ab) Tj\n\
T* 0 Tw 150 Tz (ab ab) Tj T* 100 Tz (a) Tj 4 Ts (b) Tj 0 Ts (a) Tj\n\
(ab) ' 1 3 (ab ab) \" [(a) -600 (b) 300 (a)] TJ ET\n\
BT 0.6 0.8 -0.8 0.6 150 20 Tm /F1 14 Tf (abba) Tj ET",
  "<< /Type /Font /Subtype /Type3 /FontBBox [0 0 600 700] /FontMatrix [0.001 0 0 0.001 0 0] \
/CharProcs << /a 6 0 R /b 7 0 R /space 8 0 R >> /Encoding << /Type /Encoding /Differences [32 /space 97 /a /b] >> \
/FirstChar 32 /LastChar 98 /Widths [250 " ++ String.join (List.replicate 64 "0 ") ++ "600 600] /ToUnicode 9 0 R >>",
  stream "600 0 0 0 600 700 d1 100 0 m 500 0 l 300 700 l h f",
  stream "600 0 0 0 600 700 d1 100 0 m 500 0 l 500 700 l 100 700 l h f",
  stream "250 0 d0",
  stream "/CIDInit /ProcSet findresource begin 12 dict begin begincmap \
/CMapName /Placeholder-UCS def 1 begincodespacerange <00> <ff> endcodespacerange \
2 beginbfchar <20> <0020> <61> <0061> endbfchar 1 beginbfrange <62> <62> <0062> endbfrange endcmap end end"]

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
shipped faces, the engine's writer, and by hand in matplotlib's and a print workflow's dialects and \
over PDF's geometry rules and text state (PROVENANCE.txt, SHA256SUMS)",
    "# value: PdfGfx.importPage on page 1 — 2 drawn with nothing lost, 1 drawn with its losses \
named, 0 refused; the structural half (equality with the other importer's reading) is pending",
    s!"# counts: {counts[2]!} at 2, {counts[1]!} at 1, {counts[0]!} at 0"], rows)

def selftest : IO UInt32 := tierSelftest "pdf-native" fun expect => do
  let committed ← IO.FS.readBinFile (dir ++ "/matplotlib-dialect.pdf")
  expect "the hand-written fixture is the file this script writes (--fixtures)"
    (committed == matplotlibDialect)
  let printed ← IO.FS.readBinFile (dir ++ "/print-dialect.pdf")
  expect "the hand-written print fixture is the file this script writes (--fixtures)"
    (printed == printDialect)
  let shaped ← IO.FS.readBinFile (dir ++ "/geometry-dialect.pdf")
  expect "the hand-written geometry fixture is the file this script writes (--fixtures)"
    (shaped == geometryDialect)
  let texted ← IO.FS.readBinFile (dir ++ "/text-dialect.pdf")
  expect "the hand-written text fixture is the file this script writes (--fixtures)"
    (texted == textDialect)
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
    IO.FS.writeBinFile (PdfNative.dir ++ "/print-dialect.pdf") PdfNative.printDialect
    IO.FS.writeBinFile (PdfNative.dir ++ "/geometry-dialect.pdf") PdfNative.geometryDialect
    IO.FS.writeBinFile (PdfNative.dir ++ "/text-dialect.pdf") PdfNative.textDialect
    IO.println s!"wrote {PdfNative.dir}/matplotlib-dialect.pdf, print-dialect.pdf, geometry-dialect.pdf \
and text-dialect.pdf"
    return 0
  | _ => tierMain "pdf-native" .raw PdfNative.measureTier PdfNative.selftest args
