import LeanTex.Core.Diag
import LeanTex.Core.Dim
import LeanTex.Core.Flate
import LeanTex.Core.PdfRead

namespace LeanTex.Core.Image

open LeanTex.Core.Dim

/-! # External images

Pure decoders for the two formats a first slice needs: PNG and JPEG. Reading
the file is the driver's effect; everything here is a total function over a
`ByteArray` — a truncated or foreign file yields an error value, never a
crash and never a wrong number. The decoders read only what placement and
embedding need: the pixel dimensions, the declared physical density, and
enough of the header to hand the compressed data to the PDF writer
(`/FlateDecode` with PNG prediction, `/DCTDecode`). Nothing inflates or
re-encodes; a PNG form whose samples cannot pass through untouched (alpha,
interlacing) is refused with a reason the driver can show. -/

/-- Both specs can leave the physical size undeclared — PNG's pHYs is
optional and "the physical size of each pixel is unknown" without it
(ISO/IEC 15948 §11.3.5.3), JFIF density unit 0 declares aspect ratio only
(ISO/IEC 10918-5 §5). The engine then adopts 72 pixels per inch, pdfTeX's
`\pdfimageresolution` default, so one pixel is one point. -/
def defaultDpi : Nat := 72

inductive Format where
  | png
  | jpeg
  /-- Page 1 of a PDF, embedded as a form XObject: vector stays vector. -/
  | pdf
  deriving Repr, BEq, Inhabited

/-- The colour interpretation the PDF image dictionary needs. -/
inductive Space where
  | gray
  | rgb
  /-- PNG colour type 3: samples index the PLTE palette. -/
  | indexed
  deriving Repr, BEq, Inhabited

/-- What placement and embedding read from a decoded file. `data` is the
stream the PDF writer embeds as-is: a PNG's concatenated IDAT zlib stream
(legal as `/FlateDecode` with the PNG predictor declared, ISO 32000-2
§7.4.4.4), a JPEG's whole file (`/DCTDecode`). -/
structure Info where
  format : Format
  pxW : Nat
  pxH : Nat
  dpiX : Nat := defaultDpi
  dpiY : Nat := defaultDpi
  bitDepth : Nat := 8
  space : Space := .rgb
  /-- PNG colour type 3: the PLTE payload, RGB triples. -/
  palette : ByteArray := ByteArray.empty
  data : ByteArray := ByteArray.empty
  /-- PNG only: `data` is PNG-predicted zlib — a pass-through IDAT
  stream, or a re-encoded plane the engine Up-filtered before deflating —
  and the PDF dictionary must declare the predictor. -/
  predictor : Bool := false
  /-- An alpha channel, as its own Up-filtered, zlib-compressed 8-bit
  gray plane: the PDF soft mask, Predictor 15 declared. Empty when the
  image is opaque. -/
  smask : ByteArray := ByteArray.empty
  /-- A PDF page read as a form XObject (`format == .pdf`): the box, the
  content, and the copied resource graph. The `wf` witness rides with it —
  `PdfRead.resources_closed` — so the writer never meets a dangling
  reference. -/
  form : Option { f : PdfRead.Form // f.wf } := none
  deriving Inhabited

/-- Samples per pixel, for `/DecodeParms /Colors`. -/
def Space.components : Space → Nat
  | .gray => 1
  | .rgb => 3
  | .indexed => 1

/-- Intrinsic physical width: pixels over density, in sp — and for a PDF
page, its box, exact to the sp (the `form_bbox_exact` half of the story:
the intrinsic size *is* the page box). -/
def Info.width (i : Info) : Sp :=
  match i.form with
  | some f => f.val.w
  | none => (i.pxW : Int) * 72 * spPerPt / max i.dpiX 1

def Info.height (i : Info) : Sp :=
  match i.form with
  | some f => f.val.h
  | none => (i.pxH : Int) * 72 * spPerPt / max i.dpiY 1

/-- At the default density one pixel is one point: the convention is not
just a comment, it is what `Info.width` computes. -/
theorem width_at_default_dpi (px : Nat) :
    Info.width { format := .png, pxW := px, pxH := px } = Dim.pt px := by
  show ((px : Int) * 72 * 65536) / (((72 : Nat) : Int)) = (px : Int) * 65536
  omega

-- Byte readers, all bounds-checked: the parsers below must be total over
-- arbitrary input.

private def u8? (b : ByteArray) (i : Nat) : Option Nat :=
  (b[i]?).map (·.toNat)

private def u16be? (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u8? b i) * 256 + (← u8? b (i + 1))

private def u32be? (b : ByteArray) (i : Nat) : Option Nat := do
  return (← u16be? b i) * 65536 + (← u16be? b (i + 2))

private def sliceEq (b : ByteArray) (i : Nat) (pat : List Nat) : Bool :=
  pat.zipIdx.all fun (v, k) => u8? b (i + k) == some v

/-- Pixels-per-metre to pixels-per-inch, rounded: 1 in = 25.4 mm exactly. -/
private def ppmToDpi (ppm : Nat) : Nat := (ppm * 254 + 5000) / 10000

/-! ## PNG

Signature, then chunks of `length type data crc`. IHDR carries the
dimensions and sample layout, pHYs the density, PLTE the palette, IDAT the
zlib stream (possibly split across chunks). Greyscale (0), truecolour (2),
and indexed (3) samples pass through to a PDF `/FlateDecode` image XObject
with the PNG predictor declared — their scanlines are pure sample runs after
the per-row filter byte, which is exactly what the predictor describes. An
alpha channel (types 4 and 6, 8-bit) interleaves samples PDF has no colour
space for, so those really decode: inflate, unfilter, split into a colour
plane and an SMask, re-encode. Adam7 interlacing and 16-bit alpha are
refused with the reason. -/

private def pngSig : List Nat := [137, 80, 78, 71, 13, 10, 26, 10]

/-- Split interleaved pixels into the colour plane and the alpha plane:
`channels` is 4 (RGBA) or 2 (grey + alpha), the alpha always last. -/
private def splitAlpha (px : ByteArray) (channels : Nat) :
    ByteArray × ByteArray := Id.run do
  let colorCh := channels - 1
  let n := px.size / channels
  let mut color := ByteArray.empty
  let mut alpha := ByteArray.empty
  for p in [0:n] do
    for c in [0:colorCh] do
      color := color.push (px[p * channels + c]?.getD 0)
    alpha := alpha.push (px[p * channels + colorCh]?.getD 0)
  return (color, alpha)

def decodePng (b : ByteArray) : Except String Info := do
  unless sliceEq b 0 pngSig do
    throw "not a PNG file (bad signature)"
  -- IHDR must be first (ISO/IEC 15948 §5.6).
  unless u32be? b 8 == some 13 && sliceEq b 12 [73, 72, 68, 82] do
    throw "corrupt PNG: IHDR is not the first chunk"
  let some pxW := u32be? b 16 | throw "truncated PNG: no IHDR width"
  let some pxH := u32be? b 20 | throw "truncated PNG: no IHDR height"
  let some bitDepth := u8? b 24 | throw "truncated PNG: no IHDR bit depth"
  let some colorType := u8? b 25 | throw "truncated PNG: no IHDR colour type"
  let some interlace := u8? b 28 | throw "truncated PNG: no IHDR interlace flag"
  if pxW == 0 || pxH == 0 then
    throw "corrupt PNG: zero width or height"
  if interlace != 0 then
    throw "interlaced (Adam7) PNG is not supported; re-export without interlacing"
  -- `alpha` is the channel count of a type that must really decode.
  let (space, alpha) ← match colorType with
    | 0 => pure (Space.gray, none)
    | 2 => pure (Space.rgb, none)
    | 3 => pure (Space.indexed, none)
    | 4 => pure (Space.gray, some 2)
    | 6 => pure (Space.rgb, some 4)
    | t => throw s!"corrupt PNG: colour type {t}"
  unless [1, 2, 4, 8, 16].contains bitDepth do
    throw s!"corrupt PNG: bit depth {bitDepth}"
  if space == .rgb && alpha.isNone && bitDepth < 8 then
    throw s!"corrupt PNG: truecolour at bit depth {bitDepth}"
  if alpha.isSome && bitDepth != 8 then
    throw s!"PNG with a {bitDepth}-bit alpha channel is not supported; \
re-export at 8 bits or flatten it"
  -- Walk the chunks. `i` advances by at least 12 per step, so the loop over
  -- `b.size` iterations covers every well-formed file; a lying length that
  -- points past the end is caught by the bounds-checked reads.
  let mut dpiX := defaultDpi
  let mut dpiY := defaultDpi
  let mut palette := ByteArray.empty
  let mut idat := ByteArray.empty
  let mut sawEnd := false
  let mut i := 8
  for _ in [0:b.size] do
    let some len := u32be? b i | break
    let some t0 := u8? b (i + 4) | break
    if i + 12 + len > b.size then
      throw "truncated PNG: a chunk overruns the file"
    -- Chunk types compared byte-wise; the reads are in bounds by the check.
    if t0 == 112 && sliceEq b (i + 4) [112, 72, 89, 115] then  -- pHYs
      if len == 9 then
        let some px := u32be? b (i + 8) | break
        let some py := u32be? b (i + 12) | break
        let some unit := u8? b (i + 16) | break
        -- Unit 1 is the metre; unit 0 declares aspect ratio only, and the
        -- physical size stays unknown (the default density).
        if unit == 1 && px > 0 && py > 0 then
          dpiX := max 1 (ppmToDpi px)
          dpiY := max 1 (ppmToDpi py)
    else if t0 == 80 && sliceEq b (i + 4) [80, 76, 84, 69] then  -- PLTE
      palette := b.extract (i + 8) (i + 8 + len)
    else if t0 == 73 && sliceEq b (i + 4) [73, 68, 65, 84] then  -- IDAT
      idat := idat ++ b.extract (i + 8) (i + 8 + len)
    else if t0 == 73 && sliceEq b (i + 4) [73, 69, 78, 68] then  -- IEND
      sawEnd := true
      break
    i := i + 12 + len
  unless sawEnd do
    throw "truncated PNG: no IEND chunk"
  if idat.isEmpty then
    throw "corrupt PNG: no image data (IDAT)"
  if space == .indexed && (palette.isEmpty || palette.size % 3 != 0) then
    throw "corrupt PNG: indexed colour without a usable PLTE"
  match alpha with
  | none =>
    return { format := .png, pxW, pxH, dpiX, dpiY, bitDepth, space, palette,
             data := idat, predictor := true }
  | some channels =>
    -- The samples cannot pass through: inflate against the size the
    -- geometry declares, unfilter, split — then each plane is Up-filtered
    -- and really compressed, so the embedded object costs on the order of
    -- what the source cost, never what the raw samples weigh.
    let rowBytes := pxW * channels
    let raw ← Flate.inflate idat (pxH * (1 + rowBytes))
    if raw.size != pxH * (1 + rowBytes) then
      throw "corrupt PNG: sample data does not match the declared size"
    let px ← Flate.pngUnfilter raw pxH rowBytes channels
    let (color, alphaPlane) := splitAlpha px channels
    return { format := .png, pxW, pxH, dpiX, dpiY, bitDepth := 8, space,
             data := Flate.deflate (Flate.upFilter color pxH (pxW * (channels - 1)))
             predictor := true
             smask := Flate.deflate (Flate.upFilter alphaPlane pxH pxW) }

/-! ## JPEG

A marker stream: `FF xx`, most segments carrying a big-endian length that
includes its own two bytes. `SOFn` carries the dimensions (ISO/IEC 10918-1
§B.2.2), the JFIF `APP0` the density. The entropy-coded data after `SOS`
never contains a bare `FF xx` marker except via `FF 00` stuffing and the
restart markers, so the header walk stops there — the dimensions must have
appeared first for the file to be an image at all. -/

/-- Is this marker byte an SOFn frame header? DHT (C4), JPG (C8) and DAC
(CC) share the Cx block and are not. -/
private def isSof (m : Nat) : Bool :=
  0xC0 ≤ m && m ≤ 0xCF && m != 0xC4 && m != 0xC8 && m != 0xCC

def decodeJpeg (b : ByteArray) : Except String Info := do
  unless sliceEq b 0 [0xFF, 0xD8] do
    throw "not a JPEG file (no SOI marker)"
  let mut i := 2
  let mut dpiX := defaultDpi
  let mut dpiY := defaultDpi
  let mut dims : Option (Nat × Nat × Nat × Nat) := none
  for _ in [0:b.size] do
    -- Fill bytes: any number of FFs may precede a marker.
    unless u8? b i == some 0xFF do
      throw "corrupt JPEG: expected a marker"
    let mut j := i + 1
    for _ in [0:b.size] do
      if u8? b j == some 0xFF then j := j + 1 else break
    let some m := u8? b j | throw "truncated JPEG: file ends inside a marker"
    if m == 0xD8 || (0xD0 ≤ m && m ≤ 0xD7) || m == 0x01 then
      -- Standalone markers carry no length.
      i := j + 1
      continue
    if m == 0xD9 || m == 0xDA then
      -- EOI, or the scan begins: the header is over.
      break
    let some len := u16be? b (j + 1) | throw "truncated JPEG: marker without a length"
    if len < 2 || j + 1 + len > b.size then
      throw "truncated JPEG: a segment overruns the file"
    if isSof m then
      let some precision := u8? b (j + 3) | throw "truncated JPEG: SOF too short"
      let some pxH := u16be? b (j + 4) | throw "truncated JPEG: SOF too short"
      let some pxW := u16be? b (j + 6) | throw "truncated JPEG: SOF too short"
      let some ncomp := u8? b (j + 8) | throw "truncated JPEG: SOF too short"
      dims := some (pxW, pxH, precision, ncomp)
    else if m == 0xE0 && sliceEq b (j + 3) [0x4A, 0x46, 0x49, 0x46, 0] then
      -- JFIF APP0: version(2) units(1) Xdensity(2) Ydensity(2).
      let some unit := u8? b (j + 10) | throw "truncated JPEG: APP0 too short"
      let some dx := u16be? b (j + 11) | throw "truncated JPEG: APP0 too short"
      let some dy := u16be? b (j + 13) | throw "truncated JPEG: APP0 too short"
      if dx > 0 && dy > 0 then
        if unit == 1 then
          dpiX := dx
          dpiY := dy
        else if unit == 2 then  -- dots per centimetre
          dpiX := max 1 ((dx * 254 + 50) / 100)
          dpiY := max 1 ((dy * 254 + 50) / 100)
    i := j + 1 + len
  let some (pxW, pxH, precision, ncomp) := dims
    | throw "corrupt JPEG: no frame header (SOFn) before the scan"
  if pxW == 0 || pxH == 0 then
    throw "corrupt JPEG: zero width or height"
  unless precision == 8 do
    throw s!"JPEG sample precision {precision} is not supported (8 expected)"
  let space ← match ncomp with
    | 1 => pure Space.gray
    | 3 => pure Space.rgb
    | 4 => throw "four-component (CMYK) JPEG is not supported; re-export as RGB"
    | n => throw s!"corrupt JPEG: {n} components"
  return { format := .jpeg, pxW, pxH, dpiX, dpiY, bitDepth := 8, space,
           data := b }

/-- Decode any embeddable asset, told apart by signature: PNG, JPEG, or a
PDF whose page 1 embeds as a form XObject. -/
def decode (b : ByteArray) : Except String Info :=
  if sliceEq b 0 pngSig then decodePng b
  else if sliceEq b 0 [0xFF, 0xD8] then decodeJpeg b
  else if sliceEq b 0 [0x25, 0x50, 0x44, 0x46] then do
    let f ← PdfRead.readForm b
    -- The pixel fields are the box rounded to whole points: only the dump
    -- and the placeholder read them; placement reads the box exactly.
    return { format := .pdf
             pxW := (max 0 f.val.w / spPerPt).toNat
             pxH := (max 0 f.val.h / spPerPt).toNat
             form := some f }
  else .error "not a PNG, JPEG, or PDF file (unrecognised signature)"

/-- Does decoding these bytes do real work — inflate, unfilter, split,
recompress? True exactly for the PNG colour types with an alpha channel
(4 and 6, ISO/IEC 15948 §11.2.2): what the driver's image cache keys on,
since a pass-through decode is cheaper than any cache read. -/
def decodeRecodes (b : ByteArray) : Bool :=
  sliceEq b 0 pngSig && (u8? b 25 == some 4 || u8? b 25 == some 6)

/-! ## The driver's image cache: serialization

A decoded image object as bytes: the value the driver files under the
source's content key, so the expensive decode (inflate, unfilter, split,
deflate) runs once per content. Only raster fields ride — a form XObject
never enters the cache; its decode is cheap and its `wf` witness cannot
be serialized. Transparency is `decodeBin_encodeBin_id` (staged in
`Obligations/`, exercised in `lake test`): a cache hit *is* the
recomputation's value, keeping the artifact a function of the document
and the font environment. The magic carries a format version: a change
here orphans old entries rather than misreading them. -/

private def pushU32 (b : ByteArray) (v : Nat) : ByteArray :=
  ((((b.push (UInt8.ofNat (v / 16777216 % 256))).push
    (UInt8.ofNat (v / 65536 % 256))).push
    (UInt8.ofNat (v / 256 % 256))).push (UInt8.ofNat (v % 256)))

/-- `LTIMG1`, the magic-and-format-version the decoder checks. -/
private def binMagic : List Nat := [76, 84, 73, 77, 71, 49]

/-- Serialize a raster `Info` (`form` is dropped; the cache never holds
one — `decodeRecodes` gates what is cached). -/
def encodeBin (i : Info) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (41 + i.palette.size + i.data.size + i.smask.size)
  for v in binMagic do
    out := out.push (UInt8.ofNat v)
  out := out.push (match i.format with | .png => 0 | .jpeg => 1 | .pdf => 2)
  out := out.push (match i.space with | .gray => 0 | .rgb => 1 | .indexed => 2)
  out := out.push (if i.predictor then 1 else 0)
  out := pushU32 out i.pxW
  out := pushU32 out i.pxH
  out := pushU32 out i.dpiX
  out := pushU32 out i.dpiY
  out := pushU32 out i.bitDepth
  out := pushU32 out i.palette.size
  out := pushU32 out i.data.size
  out := pushU32 out i.smask.size
  return out ++ i.palette ++ i.data ++ i.smask

/-- Read `encodeBin`'s bytes back; `none` for anything else — a foreign,
truncated, or older-format file is a cache miss, never a wrong image. -/
def decodeBin (b : ByteArray) : Option Info := do
  guard (sliceEq b 0 binMagic)
  let format ← match ← u8? b 6 with
    | 0 => some Format.png
    | 1 => some Format.jpeg
    | _ => none
  let space ← match ← u8? b 7 with
    | 0 => some Space.gray
    | 1 => some Space.rgb
    | 2 => some Space.indexed
    | _ => none
  let pr ← u8? b 8
  let pxW ← u32be? b 9
  let pxH ← u32be? b 13
  let dpiX ← u32be? b 17
  let dpiY ← u32be? b 21
  let bitDepth ← u32be? b 25
  let pLen ← u32be? b 29
  let dLen ← u32be? b 33
  let sLen ← u32be? b 37
  guard (b.size == 41 + pLen + dLen + sLen)
  return { format, pxW, pxH, dpiX, dpiY, bitDepth, space
           palette := b.extract 41 (41 + pLen)
           data := b.extract (41 + pLen) (41 + pLen + dLen)
           predictor := pr == 1
           smask := b.extract (41 + pLen + dLen) (41 + pLen + dLen + sLen) }

/-! ## The store: effects as data

An image is a file, so the elaborated document carries only the path it
wrote (`Ir.imageRefs` lists them); the CLI driver reads and decodes each,
and layout and the backends consume this value. An entry whose `info` is
`none` did not load — the driver has already said why — and every consumer
places its placeholder box instead. -/

structure Loaded where
  src : String
  /-- The relative path the driver resolved, when it differs from `src`: a
  bare graphicx name (`figures/plot`) gains the extension the file on disk
  has, and an HTML link must name it. -/
  href : String := ""
  info : Option Info := none
  deriving Inhabited

/-- graphicx resolves an extensionless name against its extension list; the
same convention here, over the formats that embed — `.pdf` first past the
name as written, graphicx's own order under pdfTeX. -/
def sourceCandidates (src : String) : List String :=
  [src, src ++ ".pdf", src ++ ".png", src ++ ".jpg", src ++ ".jpeg",
   src ++ ".PDF", src ++ ".PNG", src ++ ".JPG", src ++ ".JPEG"]

structure Store where
  entries : Array Loaded := #[]
  deriving Inhabited

def Store.find? (s : Store) (src : String) : Option Nat :=
  s.entries.findIdx? (·.src == src)

def Store.get? (s : Store) (i : Nat) : Option Loaded :=
  s.entries[i]?

/-- The decoded image behind a source, when the driver loaded one: the one
resolving question a consumer asks of the store — `none` is the placeholder
box, whatever the reason (`Ir.pending` counts exactly these). -/
def Store.info? (s : Store) (src : String) : Option Info :=
  (s.entries.find? (·.src == src)).bind (·.info)

/-! ## Fulfilment: the decision half of the image effect

The driver reads files; deciding what each read means — an entry with a
payload, or a placeholder box with the diagnostic that names it — is a
pure function here, so the naming is a theorem (`fulfil_named`) and the
store's coverage another (`fulfil_covers`), not a convention of the
driver's loop. -/

/-- W0601: the image file exists but reading it failed. -/
def imageUnreadable (src err : String) : Diag :=
  Diag.of .W0601 s!"cannot read image '{src}': {err}; a placeholder box holds its place"
    (subject := some src)

/-- W0601: no file answers the image source. -/
def imageMissing (src looked : String) : Diag :=
  Diag.of .W0601 s!"image file not found: '{src}'; a placeholder box holds its place"
    (help := s!"looked at: {looked}, also with .pdf/.png/.jpg/.jpeg added")
    (subject := some src)

/-- W0602: the image bytes are not a format the engine embeds. -/
def imageUndecodable (src err : String) : Diag :=
  Diag.of .W0602 s!"cannot use image '{src}': {err}; a placeholder box holds its place"
    (help := "PNG, JPEG, and PDF embed natively: re-export the image as one")
    (subject := some src)

/-- What the driver found for one image source, before the pure decision
names it: a file (or a boundary picture's drawn PDF) decoded — through the
driver's content cache, which equals the pure decode
(`decodeBin_encodeBin_id`) — with the relative path an HTML link needs; no
file; a file that would not read; or a boundary picture nothing drew,
carrying the boundary's own diagnostic (W0378, W0379), whose subject
`fulfil` sets so the refusal names the picture whatever words it chose. -/
inductive Fetch where
  | decoded (href : String) (res : Except String Info)
  | missing (looked : String)
  | unreadable (err : String)
  | refused (why : Diag)

/-- One source's decision: its store entry, and the diagnostic naming the
gap when there is one. Every arm that leaves `info := none` also returns
a diagnostic whose subject is the source — `fulfilOne_named`. -/
def fulfilOne (src : String) : Fetch → Loaded × Option Diag
  | .decoded href (.ok info) => ({ src, href, info := some info }, none)
  | .decoded href (.error e) => ({ src, href }, some (imageUndecodable src e))
  | .missing looked => ({ src }, some (imageMissing src looked))
  | .unreadable err => ({ src }, some (imageUnreadable src err))
  | .refused why => ({ src }, some { why with subject := some src })

def fulfilList (entries : Array Loaded) (diags : Array Diag) :
    List (String × Fetch) → Store × Array Diag
  | [] => ({ entries }, diags)
  | (src, f) :: rest =>
    fulfilList (entries.push (fulfilOne src f).1)
      (match (fulfilOne src f).2 with | some d => diags.push d | none => diags) rest

/-- The store and the diagnostics one run's reads decide, in the order the
document requested them (`Ir.imageRefs`, the driver's loop). -/
def fulfil (fetched : Array (String × Fetch)) : Store × Array Diag :=
  fulfilList #[] #[] fetched.toList

/-- A gap is named: whenever the decision leaves no payload, it also returns
a diagnostic whose subject is the source. -/
theorem fulfilOne_named (src : String) (f : Fetch) (h : (fulfilOne src f).1.info = none) :
    ∃ d, (fulfilOne src f).2 = some d ∧ d.subject = some src := by
  cases f with
  | decoded href res =>
    cases res with
    | ok info => simp [fulfilOne] at h
    | error e => exact ⟨_, rfl, rfl⟩
  | missing looked => exact ⟨_, rfl, rfl⟩
  | unreadable err => exact ⟨_, rfl, rfl⟩
  | refused why => exact ⟨_, rfl, rfl⟩

/-- Every entry the decision writes is the fetched source's, in order. -/
theorem fulfilOne_src (src : String) (f : Fetch) : (fulfilOne src f).1.src = src := by
  cases f with
  | decoded href res => cases res <;> rfl
  | missing _ | unreadable _ | refused _ => rfl

private theorem fulfilList_named (entries : Array Loaded) (diags : Array Diag)
    (hacc : ∀ en ∈ entries, en.info = none → ∃ d ∈ diags, d.subject = some en.src) :
    ∀ (fs : List (String × Fetch)) (en : Loaded),
      en ∈ (fulfilList entries diags fs).1.entries → en.info = none →
      ∃ d ∈ (fulfilList entries diags fs).2, d.subject = some en.src := by
  intro fs
  induction fs generalizing entries diags with
  | nil => intro en hmem hnone; exact hacc en hmem hnone
  | cons p rest ih =>
    intro en hmem hnone
    obtain ⟨src, f⟩ := p
    simp only [fulfilList] at hmem ⊢
    refine ih _ _ ?_ en hmem hnone
    intro en' hmem' hnone'
    rw [Array.mem_push] at hmem'
    rcases hmem' with hold | heq
    · obtain ⟨d, hd, hs⟩ := hacc en' hold hnone'
      refine ⟨d, ?_, hs⟩
      split <;> simp [hd]
    · subst heq
      obtain ⟨d, hd, hs⟩ := fulfilOne_named src f hnone'
      refine ⟨d, ?_, by rw [hs, fulfilOne_src]⟩
      rw [hd]
      simp

/-- **Every gap in the store is named.** An entry with no payload — the
placeholder box every consumer places — has a diagnostic in the same
run's output whose subject is its source. The image half of the
resolution gate (`pending_named`). -/
theorem fulfil_named (fetched : Array (String × Fetch)) :
    ∀ en ∈ (fulfil fetched).1.entries, en.info = none →
      ∃ d ∈ (fulfil fetched).2, d.subject = some en.src :=
  fulfilList_named #[] #[] (fun _ h => by simp at h) fetched.toList

private theorem fulfilList_covers (entries : Array Loaded) (diags : Array Diag) :
    ∀ fs : List (String × Fetch),
      ((fulfilList entries diags fs).1.entries.map (·.src)).toList =
        (entries.map (·.src)).toList ++ fs.map (·.1) := by
  intro fs
  induction fs generalizing entries diags with
  | nil => simp [fulfilList]
  | cons p rest ih =>
    obtain ⟨src, f⟩ := p
    simp only [fulfilList]
    rw [ih]
    simp [Array.toList_map, Array.toList_push, fulfilOne_src]

/-- **The store covers the request.** The entries are the fetched sources,
one each, in order: the driver fetches `Ir.imageRefs doc`, so every source
the document names has an entry to read. -/
theorem fulfil_covers (fetched : Array (String × Fetch)) :
    (fulfil fetched).1.entries.map (·.src) = fetched.map (·.1) := by
  rw [← Array.toList_inj, fulfil, fulfilList_covers]
  simp [Array.toList_map]

/-! ## Sizing

The request a document states (`width = 0.8\textwidth`, `height = 3cm`,
`scale = 0.5`, `keepaspectratio`) resolves against the intrinsic physical
size. The semantics are graphicx's: one declared dimension scales the other
to the intrinsic ratio; both declared set the box exactly, unless
`keepaspectratio` fits the image inside them; neither takes the intrinsic
size, times any `scale`. The theorems after the function are the contract:
declared size wins to the sp, and every derived dimension holds the
intrinsic ratio to within one sp of rounding. -/

/-- A requested dimension: an absolute part plus per-mille fractions of the
text width and text height, so `0.8\textwidth` rides symbolically to layout
where the measure is known. -/
structure Len where
  sp : Sp := 0
  tw : Int := 0
  th : Int := 0
  deriving Repr, BEq, Inhabited

def Len.resolve (l : Len) (textW textH : Sp) : Sp :=
  l.sp + l.tw * textW / 1000 + l.th * textH / 1000

/-- The sizing request from the source, unresolved. `scaleNum/scaleDen`
carry `scale = 0.6` exactly; 1/1 is unscaled. -/
structure SizeSpec where
  width : Option Len := none
  height : Option Len := none
  scaleNum : Int := 1
  scaleDen : Nat := 1
  keepAspect : Bool := false
  deriving Repr, BEq, Inhabited

/-- The placed box, in sp. `iW`/`iH` are the intrinsic physical size. -/
def resolveSize (spec : SizeSpec) (iW iH : Sp) (textW textH : Sp) : Sp × Sp :=
  match spec.width, spec.height with
  | none, none =>
    (iW * spec.scaleNum / spec.scaleDen, iH * spec.scaleNum / spec.scaleDen)
  | some w, none =>
    let w := w.resolve textW textH
    (w, w * iH / iW)
  | none, some h =>
    let h := h.resolve textW textH
    (h * iW / iH, h)
  | some w, some h =>
    let w := w.resolve textW textH
    let h := h.resolve textW textH
    if spec.keepAspect then
      if w * iH ≤ h * iW then (w, w * iH / iW) else (h * iW / iH, h)
    else
      (w, h)

/-- Division against a positive divisor loses less than one unit: the fact
every aspect statement below reduces to. -/
private theorem ediv_within_one (a d : Int) (hd : 0 < d) :
    a / d * d ≤ a ∧ a < (a / d + 1) * d := by
  have h : a % d + d * (a / d) = a :=
    (((Int.ediv_emod_unique (a := a) (b := d) (q := a / d) (r := a % d) hd).mp
      ⟨rfl, rfl⟩)).1
  have h0 := Int.emod_nonneg a (by omega : d ≠ 0)
  have h1 := Int.emod_lt_of_pos a hd
  have hm : a / d * d = d * (a / d) := Int.mul_comm _ _
  have hs : (a / d + 1) * d = d * (a / d) + d := by
    rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  constructor
  · rw [hm]
    calc d * (a / d) ≤ a % d + d * (a / d) := Int.le_add_of_nonneg_left h0
      _ = a := h
  · rw [hs]
    calc a = a % d + d * (a / d) := h.symm
      _ < d + d * (a / d) := Int.add_lt_add_right h1 _
      _ = d * (a / d) + d := Int.add_comm _ _

/-- Declared size wins: with both dimensions given and no `keepaspectratio`,
the box is exactly the declared size. -/
theorem resolveSize_both_exact (w h : Len) (n : Int) (d : Nat) (iW iH textW textH : Sp) :
    resolveSize { width := some w, height := some h, scaleNum := n, scaleDen := d }
      iW iH textW textH = (w.resolve textW textH, h.resolve textW textH) := by
  simp [resolveSize]

/-- With nothing declared the box is the intrinsic physical size. -/
theorem resolveSize_intrinsic (ka : Bool) (iW iH textW textH : Sp) :
    resolveSize { keepAspect := ka } iW iH textW textH = (iW, iH) := by
  simp [resolveSize]

/-- With `width` alone, the width is exact and the height holds the
intrinsic ratio to within one sp: `out.2 / out.1 = iH / iW` up to the
division's unit of rounding, stated multiplicatively so it is exact. -/
theorem resolveSize_width_keeps_aspect (w : Len) (n : Int) (d : Nat) (ka : Bool)
    (iW iH textW textH : Sp) (hW : 0 < iW) :
    (resolveSize { width := some w, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).1 = w.resolve textW textH ∧
    (resolveSize { width := some w, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).2 * iW ≤ w.resolve textW textH * iH ∧
    w.resolve textW textH * iH <
      ((resolveSize { width := some w, scaleNum := n, scaleDen := d, keepAspect := ka }
        iW iH textW textH).2 + 1) * iW := by
  have h := ediv_within_one (w.resolve textW textH * iH) iW hW
  exact ⟨rfl, h.1, h.2⟩

/-- The mirror statement for `height` alone. -/
theorem resolveSize_height_keeps_aspect (h : Len) (n : Int) (d : Nat) (ka : Bool)
    (iW iH textW textH : Sp) (hH : 0 < iH) :
    (resolveSize { height := some h, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).2 = h.resolve textW textH ∧
    (resolveSize { height := some h, scaleNum := n, scaleDen := d, keepAspect := ka }
      iW iH textW textH).1 * iH ≤ h.resolve textW textH * iW ∧
    h.resolve textW textH * iW <
      ((resolveSize { height := some h, scaleNum := n, scaleDen := d, keepAspect := ka }
        iW iH textW textH).1 + 1) * iH := by
  have hh := ediv_within_one (h.resolve textW textH * iW) iH hH
  exact ⟨rfl, hh.1, hh.2⟩

/-- With both given and `keepaspectratio`, the box fits inside the declared
rectangle: the binding dimension is exact and the other never exceeds its
declaration. -/
theorem resolveSize_keepAspect_fits (w h : Len) (iW iH textW textH : Sp)
    (hW : 0 < iW) (hH : 0 < iH) :
    (resolveSize { width := some w, height := some h, keepAspect := true }
      iW iH textW textH).1 ≤ w.resolve textW textH ∧
    (resolveSize { width := some w, height := some h, keepAspect := true }
      iW iH textW textH).2 ≤ h.resolve textW textH := by
  have hred : resolveSize { width := some w, height := some h, keepAspect := true }
      iW iH textW textH =
      (if w.resolve textW textH * iH ≤ h.resolve textW textH * iW then
        (w.resolve textW textH, w.resolve textW textH * iH / iW)
      else (h.resolve textW textH * iW / iH, h.resolve textW textH)) := rfl
  rw [hred]
  split
  · next hc =>
    -- Width binds: (w·iH/iW)·iW ≤ w·iH ≤ h·iW, and dividing out the
    -- positive iW keeps the order.
    have h1 := (ediv_within_one (w.resolve textW textH * iH) iW hW).1
    exact ⟨Int.le_refl _, Int.le_of_mul_le_mul_right (Int.le_trans h1 hc) hW⟩
  · next hc =>
    -- Height binds: (h·iW/iH)·iH ≤ h·iW < w·iH, same argument against iH.
    have h1 := (ediv_within_one (h.resolve textW textH * iW) iH hH).1
    have hlt : h.resolve textW textH * iW < w.resolve textW textH * iH :=
      Int.not_le.mp hc
    exact ⟨Int.le_of_mul_le_mul_right (Int.le_trans h1 (Int.le_of_lt hlt)) hH,
      Int.le_refl _⟩

end LeanTex.Core.Image
