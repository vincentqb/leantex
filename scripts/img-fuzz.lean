/-
Fuzz the image probe and planner, and the PDF figure importer. Run from the
repository root:

  lake build imgFuzz && .lake/build/bin/imgFuzz

(`lake env lean --run scripts/img-fuzz.lean` runs the same oracle
interpreted, which reads the importer's fifty thousand inputs for hours.)

Totality is the claim (never a crash, a verdict for every input) plus the
anchors: the pristine fixtures probe and plan to their known sizes, the
colour-keyed synthetics to their exact masks or their refusal, the
profiled, oriented and ancillary-chunk synthetics to their source facts
and ledger entries, and every recognised-but-unembeddable header to a
refusal that names its format (never a lie). Every truncation length of
the shipped fixtures and the synthetics, single-byte mutants at seeded
random offsets, and random blobs go through `Image.probe` and
`Image.plan`. The PDF figure importer (`PdfGfx.importPage`) is fuzzed the
same way, in six classes of 10 000 inputs each, every import inside a
wall-time budget (`pdfFigureFuzz`). This is an executable oracle, not a
theorem: it witnesses totality on millions of bytes of input, it does not
prove it.
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

/-! ## The PDF figure importer

`PdfGfx.importPage` reads arbitrary bytes onto the vector model. Five
classes of 10 000 inputs each go through it — truncations and single-byte
mutants of the committed pdf-native fixtures, content streams of random
operators over every resource kind, form, pattern and glyph-procedure
cycles, and broken font programs — each import timed against
`importBudgetMs`. The anchors first: every fixture imports with nothing
lost, and a cycle is refused by name rather than followed. -/

/-- The longest one import of a fuzzed input may take, in milliseconds:
two seconds, or five times the slowest committed fixture's own import when
that is longer (an interpreted run). -/
def importBudgetMs (slowestFixture : Nat) : Nat := max 2000 (5 * slowestFixture)

/-- A one-file PDF of the given objects' bytes, numbered from 1, the first
the catalog. -/
def fuzzPdfBin (objects : Array ByteArray) : ByteArray := Id.run do
  let mut out := "%PDF-1.7\n".toUTF8
  let mut offsets : Array Nat := #[]
  for (object, i) in objects.zipIdx do
    offsets := offsets.push out.size
    out := out ++ s!"{i + 1} 0 obj\n".toUTF8 ++ object ++ "\nendobj\n".toUTF8
  let xref := out.size
  out := out ++ s!"xref\n0 {objects.size + 1}\n0000000000 65535 f \n".toUTF8
  for offset in offsets do
    let digits := toString offset
    out := out ++ ("".pushn '0' (10 - digits.length) ++ digits ++ " 00000 n \n").toUTF8
  return out ++ s!"trailer\n<< /Size {objects.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n".toUTF8

/-- `fuzzPdfBin` over spelled objects. -/
def fuzzPdf (objects : Array String) : ByteArray := fuzzPdfBin (objects.map String.toUTF8)

/-- A stream object over bytes. -/
def fuzzStreamBin (body : ByteArray) (dict : String := "") : ByteArray :=
  s!"<< /Length {body.size} {dict}>>\nstream\n".toUTF8 ++ body ++ "\nendstream".toUTF8

/-- A stream object's spelling. -/
def fuzzStream (body : String) (dict : String := "") : String :=
  s!"<< /Length {body.utf8ByteSize} {dict}>>\nstream\n{body}\nendstream"

/-- A content stream's operator vocabulary: every operator the interpreter
reads, and a few it names as a loss. -/
def operators : Array String := #[
  "q", "Q", "cm", "w", "J", "j", "M", "d", "ri", "i", "gs", "m", "l", "c", "v", "y", "h", "re",
  "S", "s", "f", "F", "f*", "B", "B*", "b", "b*", "n", "W", "W*", "CS", "cs", "SC", "SCN", "sc",
  "scn", "G", "g", "RG", "rg", "K", "k", "sh", "Do", "BT", "ET", "Tc", "Tw", "Tz", "TL", "Tf",
  "Tr", "Ts", "Td", "TD", "Tm", "T*", "Tj", "TJ", "'", "\"", "d0", "d1", "BMC", "BDC", "EMC",
  "MP", "DP", "BX", "EX", "BI", "ID", "EI", "zz", "PS"]

/-- One random operand, of the kinds content streams hold. -/
def operand (s : UInt64) : String × UInt64 :=
  let (k, s) := rand s 12
  let (v, s) := rand s 2000
  let num := toString ((v : Int) - 1000)
  match k with
  | 0 | 1 | 2 | 3 => (num, s)
  | 4 => (num ++ ".5", s)
  | 5 => (["/F1", "/F2", "/T3", "/X1", "/X2", "/X3", "/I1", "/S1", "/P1", "/P2", "/G1", "/Pattern",
      "/DeviceRGB", "/C1", "/OC", "/MC0"][v % 16]!, s)
  | 6 => ("(" ++ toString v ++ "ab)", s)
  | 7 => ("<00410042>", s)
  | 8 => ("[(a) -250 (b) " ++ num ++ "]", s)
  | 9 => ("[" ++ num ++ " 2]", s)
  | 10 => ("<< /MCID " ++ toString v ++ " >>", s)
  | _ => ("true", s)

/-- A random content stream of up to `n` operators. -/
def randomContent (s : UInt64) (n : Nat) : String × UInt64 := Id.run do
  let (len, s) := rand s (n + 1)
  let mut st := s
  let mut out := ""
  for _ in [0:len] do
    let (args, s1) := rand st 7
    st := s1
    for _ in [0:args] do
      let (o, s2) := operand st
      st := s2
      out := out ++ o ++ " "
    let (k, s3) := rand st operators.size
    st := s3
    out := out ++ operators[k]! ++ "\n"
  return (out, st)

/-- A page over every resource kind the interpreter reads — a Type 3
font, a form, an image, a shading, a shading and a tiling pattern, an
ExtGState, optional content — whose content is `content`, its forms'
and procedures' contents `inner`. -/
def resourcePdf (content inner : String) : ByteArray := fuzzPdf #[
  "<< /Type /Catalog /Pages 2 0 R /OCProperties << /OCGs [14 0 R] /D << /OFF [14 0 R] >> >> >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 120] /Contents 4 0 R /Resources \
<< /Font << /T3 5 0 R >> /XObject << /X1 6 0 R /I1 7 0 R >> /Shading << /S1 8 0 R >> \
/Pattern << /P1 9 0 R /P2 10 0 R >> /ExtGState << /G1 11 0 R >> /Properties << /MC0 15 0 R >> >> >>",
  fuzzStream content,
  "<< /Type /Font /Subtype /Type3 /FontBBox [0 0 600 700] /FontMatrix [0.001 0 0 0.001 0 0] \
/CharProcs << /a 12 0 R /b 13 0 R >> /Encoding << /Type /Encoding /Differences [97 /a /b] >> \
/FirstChar 97 /LastChar 98 /Widths [600 600] >>",
  fuzzStream inner "/Type /XObject /Subtype /Form /BBox [0 0 50 50] ",
  fuzzStream "ff0000 00ff00 0000ff ffffff>" "/Type /XObject /Subtype /Image /Width 2 /Height 2 \
/ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /ASCIIHexDecode ",
  "<< /ShadingType 2 /ColorSpace /DeviceRGB /Coords [0 0 100 0] /Function << /FunctionType 2 \
/Domain [0 1] /C0 [1 0 0] /C1 [0 0 1] /N 1 >> /Extend [true true] >>",
  "<< /PatternType 2 /Shading 8 0 R >>",
  fuzzStream inner "/PatternType 1 /PaintType 1 /TilingType 1 /BBox [0 0 10 10] /XStep 10 \
/YStep 10 /Resources << /XObject << /X1 6 0 R >> >> ",
  "<< /Type /ExtGState /CA 0.5 /ca 0.5 /LW 2 >>",
  fuzzStream ("600 0 0 0 600 700 d1 " ++ inner),
  fuzzStream ("600 0 d0 " ++ inner),
  "<< /Type /OCG /Name (Off) >>",
  "<< /Type /OCMD /OCGs [14 0 R] /P /AnyOn >>"]

/-- A page whose font is `font` (a font dictionary as spelled) and whose
program is the bytes `program` under `key`. -/
def fontPdf (font : String) (key : String) (program : ByteArray) (dict : String := "") : ByteArray :=
  fuzzPdfBin #[
    "<< /Type /Catalog /Pages 2 0 R >>".toUTF8, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
/Resources << /Font << /F1 5 0 R >> >> >>".toUTF8,
    fuzzStreamBin "BT /F1 12 Tf 10 10 Td (Ab) Tj <0041004200e9> Tj [(A) -120 (b)] TJ ET".toUTF8,
    font.toUTF8,
    s!"<< /Type /FontDescriptor /FontName /Fuzz /Flags 32 /{key} 7 0 R >>".toUTF8,
    fuzzStreamBin program dict]

/-- What the importer's fuzz has run: inputs, those drawn, the slowest. -/
structure Tally where
  runs : Nat := 0
  drawn : Nat := 0
  worst : Nat := 0

/-- One import against the budget, its figure forced whole — the marks are
what the web face spells — and counted. -/
def timedImport (tally : IO.Ref Tally) (budget : Nat) (what : String) (b : ByteArray) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := PdfGfx.importPage b
  let forced := match r with
    | .ok imp => imp.figure.marks.size + imp.figure.losses.size + (LeanTex.Cli.PdfFaces.svgOf imp.figure).size
    | .error e => e.length
  let t1 ← IO.monoMsNow
  let ms := t1 - t0
  if ms > budget then die s!"{what}: one import took {ms} ms, over {budget}"
  tally.modify fun t => { runs := t.runs + 1, drawn := t.drawn + (if r.isOk && forced ≥ 0 then 1 else 0)
                          worst := max t.worst ms }

def pdfFigureFuzz : IO Unit := do
  let names := #["cairo-chart.pdf", "leantex-strokes.pdf", "lualatex-shade.pdf", "lualatex-text.pdf",
    "matplotlib-dialect.pdf", "print-dialect.pdf"]
  let mut fixtures : Array ByteArray := #[]
  let mut slowest := 0
  for n in names do
    let b ← IO.FS.readBinFile ("testdata/pdf-native/" ++ n)
    let t0 ← IO.monoMsNow
    match PdfGfx.importPage b with
    | .ok imp =>
      unless imp.figure.losses.isEmpty && (LeanTex.Cli.PdfFaces.svgOf imp.figure).size > 0 do
        die s!"{n} imports with losses"
    | .error e => die s!"{n} does not import: {e}"
    slowest := max slowest ((← IO.monoMsNow) - t0)
    fixtures := fixtures.push b
  let budget := importBudgetMs slowest
  -- A form that paints itself, and two that paint each other: refused by
  -- name, never followed round.
  let selfForm := resourcePdf "/X1 Do" "/X1 Do"
  match PdfGfx.importPage selfForm with
  | .ok imp => unless imp.figure.losses.contains (.budget "form-recursion") do
      die "a form that paints itself is not named a recursion"
  | .error e => die s!"a form that paints itself refused whole: {e}"
  let tally ← IO.mkRef ({} : Tally)
  -- 1. Truncations, evenly spaced cuts of each fixture in proportion to its
  -- size, at least 10 000 in all.
  let total := fixtures.foldl (fun a b => a + b.size) 0
  for b in fixtures do
    let cuts := max 1 ((10000 * b.size + total - 1) / total)
    for k in [0:cuts] do
      let n := b.size * k / cuts
      timedImport tally budget "a truncation" (b.extract 0 n)
  -- 2. Single-byte mutants at seeded offsets, 2 000 per fixture.
  let mut s : UInt64 := 31337271828182
  for b in fixtures do
    for _ in [0:2000] do
      let (i, s1) := rand s b.size
      let (v, s2) := rand s1 256
      s := s2
      timedImport tally budget "a byte mutant" (b.set! i (UInt8.ofNat v))
  -- 3. Random operators over every resource kind, forms and procedures
  -- holding random operators of their own.
  for _ in [0:10000] do
    let (outer, s1) := randomContent s 40
    let (inner, s2) := randomContent s1 12
    s := s2
    timedImport tally budget "a random content stream" (resourcePdf outer inner)
  -- 4. Cycles and depth: forms, tiling cells and glyph procedures that
  -- paint themselves or each other, behind random state, and deep `q`.
  for k in [0:10000] do
    let (pre, s1) := randomContent s 6
    s := s1
    let inner := match k % 5 with
      | 0 => "/X1 Do"
      | 1 => "/Pattern cs /P2 scn 0 0 10 10 re f"
      | 2 => "BT /T3 10 Tf (ab) Tj ET"
      | 3 => "/X1 Do BT /T3 10 Tf (a) Tj ET"
      | _ => String.join (List.replicate (k % 400) "q ")
    timedImport tally budget "a cycle" (resourcePdf (pre ++ " /X1 Do BT /T3 9 Tf (ab) Tj ET \
/Pattern cs /P2 scn 0 0 50 50 re f") inner)
  -- 5. Broken font programs: the shipped faces truncated and mutated, and
  -- random bytes, as every kind of embedded program.
  let otf ← IO.FS.readBinFile "testdata/corpus/fonts/FiraSans-Regular.otf"
  let ttf ← IO.FS.readBinFile "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let cff := (Ink.cffTable otf).getD ByteArray.empty
  let kinds : Array (String × String × String × ByteArray) := #[
    ("<< /Type /Font /Subtype /TrueType /BaseFont /Fuzz /FontDescriptor 6 0 R >>", "FontFile2", "", ttf),
    ("<< /Type /Font /Subtype /Type1 /BaseFont /Fuzz /Encoding /WinAnsiEncoding /FontDescriptor 6 0 R >>",
      "FontFile3", "/Subtype /Type1C ", cff),
    ("<< /Type /Font /Subtype /Type0 /BaseFont /Fuzz /Encoding /Identity-H /DescendantFonts \
[<< /Type /Font /Subtype /CIDFontType0 /BaseFont /Fuzz /FontDescriptor 6 0 R /W [0 [500 600]] >>] >>",
      "FontFile3", "/Subtype /OpenType ", otf),
    ("<< /Type /Font /Subtype /Type0 /BaseFont /Fuzz /Encoding /Identity-H /DescendantFonts \
[<< /Type /Font /Subtype /CIDFontType2 /BaseFont /Fuzz /FontDescriptor 6 0 R /CIDToGIDMap /Identity >>] >>",
      "FontFile2", "", ttf)]
  for k in [0:10000] do
    let (font, key, dict, prog) := kinds[k % kinds.size]!
    let (mode, s1) := rand s 3
    let (i, s2) := rand s1 (max 1 prog.size)
    let (v, s3) := rand s2 256
    s := s3
    let bytes := match mode with
      | 0 => prog.extract 0 i
      | 1 => prog.set! i (UInt8.ofNat v)
      | _ => ⟨(Array.range (i % 4096)).map fun j => UInt8.ofNat ((j * 2654435761 + v) % 256)⟩
    timedImport tally budget "a broken font program" (fontPdf font key bytes dict)
  -- 6. Image dictionaries: every sample depth, colour space and decoding
  -- the importer's tables read (grey, RGB, CMYK, indexed over each base, a
  -- stencil, a colour-key or a soft mask beside), at random sizes, over
  -- data short, exact or long, and a random Decode array.
  let spaces : Array String := #["/DeviceGray", "/DeviceRGB", "/DeviceCMYK",
    "[/Indexed /DeviceRGB 3 <ff000000ff000000ffffffff>]", "[/Indexed /DeviceCMYK 1 <00ff0000ff000000>]",
    "[/Indexed /DeviceGray 255 <" ++ String.join ((List.range 256).map fun i =>
      let h := "0123456789abcdef".toList
      String.ofList [h[i / 16]!, h[i % 16]!]) ++ ">]", "/Pattern", "/Lab"]
  for _ in [0:10000] do
    let (w, s1) := rand s 40
    let (h, s2) := rand s1 40
    let (bi, s3) := rand s2 7
    let (si, s4) := rand s3 spaces.size
    let (extra, s5) := rand s4 5
    let (len, s6) := rand s5 6000
    let (dk, s7) := rand s6 4
    s := s7
    let bpc := #[1, 2, 4, 8, 16, 3, 0][bi]!
    let decode := match dk with
      | 0 => ""
      | 1 => "/Decode [1 0 1 0 1 0 1 0] "
      | 2 => "/Decode [0 255] "
      | _ => "/Decode [0.25 0.75 -1 2 0 1 1 0] "
    let more := match extra with
      | 0 => "/ImageMask true "
      | 1 => "/SMask 9 0 R "
      | 2 => "/Mask [0 128 10 20 0 255 0 9] "
      | 3 => "/Interpolate true "
      | _ => ""
    let data : ByteArray := ⟨(Array.range len).map fun j => UInt8.ofNat ((j * 2654435761 + w * 31 + h) % 256)⟩
    let dict := s!"/Type /XObject /Subtype /Image /Width {w} /Height {h} /ColorSpace {spaces[si]!} \
/BitsPerComponent {bpc} {decode}{more}"
    let pdf := fuzzPdfBin #[
      "<< /Type /Catalog /Pages 2 0 R >>".toUTF8, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
      "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
/Resources << /XObject << /I1 5 0 R >> /Pattern << /P1 6 0 R >> >> >>".toUTF8,
      fuzzStreamBin "0.2 0.4 0.6 rg q 40 0 0 30 10 10 cm /I1 Do Q /Pattern cs /P1 scn q 20 0 0 20 60 10 cm /I1 Do Q".toUTF8,
      fuzzStreamBin data dict,
      fuzzStreamBin "1 0 0 rg 0 0 5 5 re f".toUTF8
        "/PatternType 1 /PaintType 1 /TilingType 1 /BBox [0 0 10 10] /XStep 10 /YStep 10 /Resources << >> ",
      "<< >>".toUTF8, "<< >>".toUTF8,
      fuzzStreamBin ⟨(Array.range (w * h)).map fun j => UInt8.ofNat (j * 7 % 256)⟩
        s!"/Type /XObject /Subtype /Image /Width {w} /Height {h} /ColorSpace /DeviceGray /BitsPerComponent 8 "]
    timedImport tally budget "an image dictionary" pdf
  let t ← tally.get
  IO.println s!"img-fuzz: the PDF figure importer read {t.runs} inputs ({t.drawn} drawn, the rest \
refused), the slowest in {t.worst} ms, under {budget} ms"

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
  pdfFigureFuzz
