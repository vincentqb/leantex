module

public import LeanTex.Core.Pdf
public import LeanTex.Core.Image
public import LeanTex.Core.FontSubset

public section

open LeanTex.Core
open LeanTex.Core.Dim

/-! Representation invariants (ISO 32000-2 §7.3.8, §7.5.7, §7.7.3.3):
an ordinary stream's length integer has the same meaning inline, at a
direct offset, or in an object stream. A page's content array has the same
ordered members inline, at a direct offset, or in an object stream.
Empty arrays stay empty and repeated stream references stay repeated.
These changes of representation preserve the imported drawing and the
actual PDF the writer ships, including copied resource stream bytes.

Object streams bootstrap from inline or directly stored length integers:
§7.5.7 excludes their length objects from object streams. A reference
chain, a cyclic bootstrap, or a non-integer cannot become a stream length.
All source PDFs here are invented and carry drawing operators only. -/

private def objectStream (raw : ByteArray) (length : String)
    (attrs : String := "") : ByteArray :=
  s!"<< /Length {length} {attrs} >>\nstream\n".toUTF8 ++ raw ++
    "\nendstream".toUTF8

/-- Fixed-width big-endian xref fields, `/W [1 4 2]` (§7.5.8.3). -/
private def objectXrefRow (tag target slot : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat tag, UInt8.ofNat (target >>> 24),
    UInt8.ofNat (target >>> 16), UInt8.ofNat (target >>> 8), UInt8.ofNat target,
    UInt8.ofNat (slot >>> 8), UInt8.ofNat slot]⟩

/-- Each pack gets a stream and an ordinary integer holding its length.
The optional overrides deliberately make malformed bootstrap/xref cases.
Packing order differs from object order so index zero is no special case. -/
private def objectPdf (bodies : Array ByteArray) (packs : Array (Array Nat) := #[])
    (streamXref : Bool := true) (indirectBootstrap : Bool := false)
    (bootstrap : Array (Option String) := #[])
    (rows : Array (Nat × (Nat × Nat × Nat)) := #[]) : ByteArray := Id.run do
  let mut all := bodies
  for (pack, i) in packs.zipIdx do
    let mut header := ""
    let mut data := ByteArray.empty
    for num in pack do
      header := header ++ s!"{num} {data.size} "
      data := data ++ bodies[num - 1]!.push 10
    let raw := Flate.deflateStored (header.toUTF8 ++ data)
    let stm := bodies.size + 2 * i + 1
    let length := ((bootstrap[i]?).join).getD
      (if indirectBootstrap then s!"{stm + 1} 0 R" else toString raw.size)
    all := all.push (objectStream raw length
      s!"/Type /ObjStm /N {pack.size} /First {header.utf8ByteSize} /Filter /FlateDecode")
    all := all.push (toString raw.size).toUTF8
  let mut out := "%PDF-1.7\n".toUTF8
  let mut offsets : Array Nat := #[0]
  for (body, i) in all.zipIdx do
    offsets := offsets.push out.size
    unless packs.any (·.contains (i + 1)) do
      out := out ++ s!"{i + 1} 0 obj\n".toUTF8 ++ body ++ "\nendobj\n".toUTF8
  let start := out.size
  if streamXref || !packs.isEmpty then
    let xref := all.size + 1
    offsets := offsets.push start
    let mut raw := ByteArray.empty
    for num in [0:xref + 1] do
      let (tag, target, slot) :=
        match rows.find? (·.1 == num) with
        | some (_, row) => row
        | none =>
          if num == 0 then (0, 0, 65535)
          else match packs.findIdx? (·.contains num) with
          | some i => (2, bodies.size + 2 * i + 1,
              (packs[i]!.findIdx? (· == num)).getD 0)
          | none => (1, offsets[num]!, 0)
      raw := raw ++ objectXrefRow tag target slot
    let encoded := Flate.deflateStored raw
    out := out ++ s!"{xref} 0 obj\n".toUTF8 ++
      objectStream encoded (toString encoded.size)
        s!"/Type /XRef /W [1 4 2] /Size {xref + 1} /Root 1 0 R /Filter /FlateDecode" ++
      "\nendobj\n".toUTF8
  else
    out := out ++ s!"xref\n0 {all.size + 1}\n0000000000 65535 f \n".toUTF8
    for offset in offsets.toList.drop 1 do
      let digits := toString offset
      let padded := String.ofList (List.replicate (10 - digits.length) '0') ++ digits
      out := out ++ s!"{padded} 00000 n \n".toUTF8
    out := out ++ s!"trailer\n<< /Size {all.size + 1} /Root 1 0 R >>\n".toUTF8
  return out ++ s!"startxref\n{start}\n%%EOF\n".toUTF8

private inductive LengthShape where
  | inline | indirect | compressed
  deriving BEq, Repr

private inductive ContentsShape where
  | stream | inlineArray | indirectArray | compressedArray
  deriving BEq, Repr

private def objectInkA :=
  "q 1 1 1 rg 0 0 128 96 re f /Alpha gs 1 0 0 rg 8 24 64 64 re f Q"
private def objectInkB :=
  "q 0 0 1 rg 48 8 40 40 re f /Tile Do Q"
private def objectTileInk := "q /Alpha gs 0 1 0 rg 2 2 8 8 re f Q"

private def objectArray (members : Array Nat) : String :=
  "[" ++ String.intercalate " " (members.toList.map (fun n => s!"{n} 0 R")) ++ "]"

private def objectBodies (length : LengthShape) (contents : ContentsShape)
    (filtered : Bool := false) (members : Array Nat := #[4, 8]) : Array ByteArray :=
  let stream (text : String) (num : Nat) (attrs : String := "") : ByteArray :=
    let raw := if filtered then Flate.deflateStored text.toUTF8 else text.toUTF8
    objectStream raw (if length == .inline then toString raw.size else s!"{num} 0 R")
      (attrs ++ if filtered then " /Filter /FlateDecode" else "")
  let lengthOf (text : String) : ByteArray :=
    (toString (if filtered then (Flate.deflateStored text.toUTF8).size
      else text.utf8ByteSize)).toUTF8
  let combined := objectInkA ++ "\n" ++ objectInkB
  let first := if contents == .stream then combined else objectInkA
  let entry := match contents with
    | .stream => "4 0 R"
    | .inlineArray => objectArray members
    | .indirectArray | .compressedArray => "7 0 R"
  #[
    "<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 128 96] \
      /Resources 6 0 R >>".toUTF8,
    s!"<< /Type /Page /Parent 2 0 R /Contents {entry} >>".toUTF8,
    stream first 5,
    lengthOf first,
    "<< /ExtGState << /Alpha 9 0 R >> /XObject << /Tile 10 0 R >> >>".toUTF8,
    (objectArray members).toUTF8,
    stream objectInkB 11,
    "<< /Type /ExtGState /CA 1 /ca 1 >>".toUTF8,
    stream objectTileInk 12
      "/Type /XObject /Subtype /Form /BBox [0 0 12 12] \
      /Resources << /ExtGState << /Alpha 9 0 R >> >>",
    lengthOf objectInkB,
    lengthOf objectTileInk]

private def objectPacks (length : LengthShape) (contents : ContentsShape)
    (metadata : Bool) : Array (Array Nat) := Id.run do
  let mut packs := #[]
  if length == .compressed then packs := packs.push #[12, 5, 11]
  let packedMetadata := if metadata then #[9, 6, 3, 2, 1] else #[]
  let packedMetadata :=
    if contents == .compressedArray then packedMetadata.push 7 else packedMetadata
  if !packedMetadata.isEmpty then packs := packs.push packedMetadata
  return packs

private def objectDrawing (members : Array Nat) : ByteArray :=
  members.foldl (fun out n =>
    out ++ (if n == 4 then objectInkA else objectInkB).toUTF8.push 10) ByteArray.empty

/-- Sources and expected decoded drawings for the optional external
renderer oracle as well as the hermetic check below. No host PDF tools
are needed to construct or judge these cases. -/
def pdfReadObjectFixtures : Array (String × ByteArray × ByteArray) := Id.run do
  let mut out := #[]
  for length in [LengthShape.inline, .indirect, .compressed] do
    for contents in [ContentsShape.stream, .inlineArray, .indirectArray, .compressedArray] do
      for metadata in [false, true] do
        for filtered in [false, true] do
          for indirect in [false, true] do
            let name := s!"{repr length}-{repr contents}-meta{metadata}-flate{filtered}-boot{indirect}"
            let bodies := objectBodies length contents filtered
            out := out.push (name, objectPdf bodies (objectPacks length contents metadata)
              true indirect, objectDrawing #[4, 8])
  for members in [#[], #[8, 4], #[4, 8, 4], #[8, 8]] do
    for contents in [ContentsShape.inlineArray, .indirectArray, .compressedArray] do
      let name := s!"array-{repr members}-{repr contents}"
      out := out.push (name,
        objectPdf (objectBodies .compressed contents true members)
          (objectPacks .compressed contents true) true true,
        objectDrawing members)
  for contents in [ContentsShape.stream, .inlineArray, .indirectArray] do
    out := out.push (s!"classic-{repr contents}",
      objectPdf (objectBodies .indirect contents) #[] false, objectDrawing #[4, 8])
  return out

private def objectWrapper (fonts : Font.FontSet) (programs : Array (ByteArray × Bool))
    (f : { f : PdfRead.Form // f.wf }) :
    ByteArray :=
  let plan : Image.Plan := { pxW := 0, pxH := 0, form := some f }
  let imgs : Image.Store := { entries := #[{ src := "drawing.pdf", info := some plan }] }
  let line : Layout.LineOut :=
    { x := 0, y := f.val.h, size := Dim.pt 12, setWidth := f.val.w,
      segs := #[.image (some 0) f.val.w f.val.h] }
  Pdf.write { pageW := f.val.w, pageH := f.val.h, hmargin := 0, vmargin := 0 }
    fonts #[{ lines := #[line] }] (imgs := imgs) (programs := programs)

private def objectResolve (es : Array PdfRead.Entry) (obj : PdfRead.Obj) :
    Option PdfRead.Obj :=
  match obj with
  | .ref n _ => (es.find? (·.num == n)).map (·.val)
  | other => some other

/-- Follow the emitted resource references; the nested form must retain
both its encoded payload and its decoded drawing, plus its graphics state. -/
private def objectResources (es : Array PdfRead.Entry) (obj : PdfRead.Obj)
    (tile : PdfRead.Entry) : Option Bool := do
  let res ← objectResolve es (← obj.get? "Resources")
  let states ← objectResolve es (← res.get? "ExtGState")
  let alpha ← objectResolve es (← states.get? "Alpha")
  let xobjs ← objectResolve es (← res.get? "XObject")
  let .ref num _ ← xobjs.get? "Tile" | none
  let copied ← es.find? (·.num == num)
  let tileRes ← objectResolve es (← copied.val.get? "Resources")
  let tileStates ← objectResolve es (← tileRes.get? "ExtGState")
  let tileAlpha ← objectResolve es (← tileStates.get? "Alpha")
  return alpha.get? "CA" == some (.int 1) && tileAlpha == alpha &&
    copied.stream == tile.stream &&
    copied.val.get? "Filter" == tile.val.get? "Filter" &&
    copied.decoded.toOption == some (some objectTileInk.toUTF8)

private def objectArtifactMatches (bytes : ByteArray)
    (ink : ByteArray) (tile : PdfRead.Entry) : Bool :=
  match PdfRead.objects bytes with
  | .error _ => false
  | .ok es =>
    let forms := es.val.filter fun e =>
      e.val.get? "Subtype" == some (.name "Form") &&
      e.val.get? "BBox" == some (.arr #[.int 0, .int 0, .int 128, .int 96])
    forms.size == 1 && forms.all (fun e =>
      e.decoded.toOption == some (some ink) &&
      (objectResources es.val e.val tile).getD false)

private def objectErrorIs {α : Type} (result : Except String α) (expected : String) : Bool :=
  match result with
  | .ok _ => false
  | .error message => message == expected

/-- Representation changes preserve actual shipped drawing/resource
streams; malformed chains and object-stream bootstrap cycles terminate
in a named refusal. Kept additive for independent suite registration. -/
def pdfReadObjectsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit := do
    unless ok do ref.modify (s!"PDF object forms: {name}" :: ·)
  let .ok font := Font.parse
      (← IO.FS.readBinFile "testdata/corpus/fonts/SourceSerifPro-Regular.otf") |
    t "bundled wrapper font parses" false
    return
  -- These pages contain only drawing operators. Reuse the empty glyph
  -- subset through the writer's existing font-program cache path.
  let program := FontSubset.program font #[]
  let fonts : Font.FontSet :=
    { fonts := #[font], zdata := #[some (Flate.deflate program.1)] }
  let wrap := objectWrapper fonts #[program]
  for (name, bytes, ink) in pdfReadObjectFixtures do
    let .ok es := PdfRead.objects bytes |
      t s!"{name}: all objects and stream boundaries read" false
      continue
    let some tile := es.val.find? (·.num == 10) |
      t s!"{name}: source resource stream exists" false
      continue
    match PdfRead.readForm bytes with
    | .error message => t s!"{name}: unexpected refusal: {message}" false
    | .ok f =>
      let artifact := wrap f
      t s!"{name}: imported drawing order and multiplicity" (f.val.content == ink)
      t s!"{name}: emitted drawing and resource graph" (objectArtifactMatches artifact ink tile)
      t s!"{name}: image decode retains the same PDF form"
        (match Image.decode bytes with
        | .ok p => p.form.any (fun g => wrap g == artifact)
        | .error _ => false)
  -- Byte-identical output across representation changes, separately for
  -- encoded and unencoded resources (their payloads must remain verbatim).
  for filtered in [false, true] do
    let .ok baseline := PdfRead.readForm
        (objectPdf (objectBodies .inline .stream filtered)) |
      t "inline baseline reads" false
      continue
    let expected := wrap baseline
    for length in [LengthShape.inline, .indirect, .compressed] do
      for contents in [ContentsShape.stream, .inlineArray, .indirectArray, .compressedArray] do
        let bytes := objectPdf (objectBodies length contents filtered)
          (objectPacks length contents true) true true
        t s!"identical emitted PDF: {repr length}, {repr contents}, filtered={filtered}"
          (match PdfRead.readForm bytes with
          | .ok f => wrap f == expected
          | .error _ => false)
  for length in [LengthShape.indirect, .compressed] do
    let bodies := objectBodies length .stream
    let packs := objectPacks length .stream false
    for value in ["true", "[1]", "<< >>", "(12)", "5 0 R", "11 0 R", "4 0 R"] do
      let bytes := objectPdf (bodies.set! 4 value.toUTF8) packs
      t s!"{repr length}: refuses non-integer or chained length {value}"
        (objectErrorIs (PdfRead.readForm bytes) "malformed PDF: an indirect /Length does not resolve" &&
         objectErrorIs (PdfRead.objects bytes) "malformed PDF: an indirect /Length does not resolve")
    for (value, error) in [("-1", "truncated PDF: a stream overruns the file"),
        ("1000000", "truncated PDF: a stream overruns the file"),
        ("1", "malformed PDF: a stream's /Length does not reach its endstream")] do
      let bytes := objectPdf (bodies.set! 4 value.toUTF8) packs
      t s!"{repr length}: refuses length {value}"
        (objectErrorIs (PdfRead.readForm bytes) error &&
         objectErrorIs (PdfRead.objects bytes) error)
  let bodies := objectBodies .compressed .stream
  let packs := objectPacks .compressed .stream false
  for (name, bytes) in [
      ("own compressed length", objectPdf bodies packs true false #[some "5 0 R"]),
      ("mutual compressed lengths", objectPdf bodies #[#[5], #[11]] true false
        #[some "11 0 R", some "5 0 R"]),
      ("length index out of range", objectPdf bodies packs true false #[]
        #[(5, (2, 13, 100))]),
      ("missing object stream", objectPdf bodies packs true false #[]
        #[(5, (2, 100, 0))]),
      ("object stream itself compressed", objectPdf bodies packs true false #[]
        #[(13, (2, 13, 0))]),
      ("missing length object", objectPdf bodies packs true false #[]
        #[(5, (0, 0, 0))])] do
    t s!"refuses {name}"
      (objectErrorIs (PdfRead.readForm bytes) "malformed PDF: an indirect /Length does not resolve" &&
       !(PdfRead.objects bytes).isOk)
  for compressed in [false, true] do
    let bodies := objectBodies .inline .indirectArray
    let packs := if compressed then #[#[5, 7]] else #[]
    for (value, error) in [
        ("7 0 R", "malformed PDF: a content stream has no data"),
        ("5 0 R", "malformed PDF: a content stream has no data"),
        ("[7 0 R]", "malformed PDF: a content stream has no data"),
        ("[100 0 R]", "malformed PDF: a content stream has no data"),
        ("[[4 0 R]]", "malformed PDF: page contents are not references"),
        ("[4 0 R null]", "malformed PDF: page contents are not references")] do
      let bytes := objectPdf ((bodies.set! 6 value.toUTF8).set! 4 "7 0 R".toUTF8) packs
      t s!"refuses malformed contents {value}, compressed={compressed}"
        (objectErrorIs (PdfRead.readForm bytes) error)
