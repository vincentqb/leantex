import LeanTex.Core.Dim
import LeanTex.Core.Font
import LeanTex.Core.Layout

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Layout

private def hexDigit (n : Nat) : Char := "0123456789ABCDEF".toList[n % 16]!

private def hex4 (n : Nat) : String :=
  String.ofList [hexDigit (n / 4096), hexDigit (n / 256), hexDigit (n / 16), hexDigit n]

private def utf16Hex (c : Char) : String :=
  let n := c.toNat
  if n < 0x10000 then
    hex4 n
  else
    let v := n - 0x10000
    hex4 (0xD800 + v / 1024) ++ hex4 (0xDC00 + v % 1024)

private def pdfName (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c.isAlphanum || c == '-' || c == '.' then
      out := out.push c
    else
      out := out ++ "#" ++ String.ofList [hexDigit (c.toNat / 16), hexDigit c.toNat]
  return if out == "" then "Embedded" else out

private def fnv64 (seed : UInt64) (b : ByteArray) : UInt64 := Id.run do
  let mut h := seed
  for byte in b do
    h := (h ^^^ byte.toUInt64) * 1099511628211
  return h

private def hex16 (x : UInt64) : String := Id.run do
  let mut s := ""
  let mut v := x
  for _ in [0:16] do
    s := String.ofList [hexDigit (v % 16).toNat] ++ s
    v := v / 16
  return s

/-- Used glyphs for one font: one char witness per gid, ascending gid. Mark
array — the glyph stream is large (every glyph on every page), so no sorting. -/
private def usedGlyphs (fontIdx numGlyphs : Nat) (pages : Array PageOut) :
    Array (Nat × Char) := Id.run do
  let mut seen : Array (Option Char) := Array.replicate numGlyphs none
  for p in pages do
    for l in p.lines do
      for s in l.segs do
        if let .run idx _ _ _ glyphs _ := s then
          if idx == fontIdx then
            for (g, c) in glyphs do
              if h : g < seen.size then
                if seen[g].isNone then
                  seen := seen.set! g (some c)
  let mut out : Array (Nat × Char) := #[]
  for (c?, g) in seen.zipIdx do
    if let some c := c? then
      out := out.push (g, c)
  return out

/-- One page's content stream. A `TJ` array cannot switch fonts mid-array, so
a run in a different face closes the array, emits `Tf`, and reopens it; the
text position carries over because `Tm` is only set per line. -/
private def contentStream (geom : Geom) (remap : Array Nat) (page : PageOut) :
    String := Id.run do
  let mut s := "BT\n"
  let mut curFont : Int := -1
  let mut curSize : Sp := -1
  let mut curColor : Ir.Color := Ir.Color.black
  for l in page.lines do
    if l.segs.isEmpty then
      continue
    let ypdf := geom.pageH - l.y
    s := s ++ s!"1 0 0 1 {l.x.toPtString} {ypdf.toPtString} Tm\n"
    let mut inArray := false
    for seg in l.segs do
      match seg with
      | .run idx color _ _ glyphs segSize =>
        let size := if segSize == 0 then l.size else segSize
        -- Neither Tf nor rg may appear inside a TJ array, so a change in
        -- either closes the array and reopens it after.
        if curFont != idx || curSize != size || curColor != color then
          if inArray then
            s := s ++ "] TJ\n"
            inArray := false
          if curFont != idx || curSize != size then
            s := s ++ s!"/F{(remap[idx]?.getD 0) + 1} {size.toPtString} Tf\n"
            curFont := idx
            curSize := size
          if curColor != color then
            s := s ++ s!"{color.pdfComponents} rg\n"
            curColor := color
        unless inArray do
          s := s.push '['
          inArray := true
        s := s.push '<'
        for (g, _) in glyphs do
          s := s.push (hexDigit (g / 4096))
          s := s.push (hexDigit (g / 256))
          s := s.push (hexDigit (g / 16))
          s := s.push (hexDigit g)
        s := s.push '>'
      | .gap w =>
        unless inArray do
          s := s.push '['
          inArray := true
        -- A TJ displacement is thousandths of the *live* font size, which is
        -- whatever the last Tf set, not the line's nominal size.
        let unit := if curSize == 0 then l.size else curSize
        let v : Int := -(w * 1000 / unit)
        s := s ++ s!"{v}"
    if inArray then
      s := s ++ "] TJ\n"
  s := s ++ "ET"
  return s

/-- Link rectangles for one page, in PDF user space. Adjacent runs with the
same destination merge, so a hyphenated or multi-font link is one annotation
per line rather than one per glyph run. -/
private def linkRects (geom : Geom) (page : PageOut) :
    Array (Sp × Sp × Sp × Sp × String) := Id.run do
  let mut out : Array (Sp × Sp × Sp × Sp × String) := #[]
  for l in page.lines do
    let mut x := l.x
    -- Merge tolerance of one em: a run separated only by an interword space
    -- joins the previous rectangle, so a multi-word link is one annotation.
    let pad := l.size
    for seg in l.segs do
      match seg with
      | .run _ _ link w _ segSize =>
        let size := if segSize == 0 then l.size else segSize
        let y0 := geom.pageH - l.y - size / 4
        let y1 := geom.pageH - l.y + size * 4 / 5
        if let some url := link then
          match out.back? with
          | some (bx0, by0, bx1, by1, burl) =>
            if burl == url && by0 == y0 && bx1 + pad ≥ x then
              out := out.pop.push (bx0, by0, x + w, by1, burl)
            else
              out := out.push (x, y0, x + w, y1, url)
          | none => out := out.push (x, y0, x + w, y1, url)
        x := x + w
      | .gap w => x := x + w
  return out

private def toUnicode (used : Array (Nat × Char)) : String := Id.run do
  let mut s := "/CIDInit /ProcSet findresource begin
12 dict begin
begincmap
/CIDSystemInfo << /Registry (Adobe) /Ordering (UCS) /Supplement 0 >> def
/CMapName /Adobe-Identity-UCS def
/CMapType 2 def
1 begincodespacerange
<0000> <FFFF>
endcodespacerange
"
  let mut remaining := used.toList
  for _ in [0:used.size + 1] do
    if remaining.isEmpty then
      break
    let chunk := remaining.take 100
    remaining := remaining.drop 100
    s := s ++ s!"{chunk.length} beginbfchar\n"
    for (g, c) in chunk do
      s := s ++ s!"<{hex4 g}> <{utf16Hex c}>\n"
    s := s ++ "endbfchar\n"
  s := s ++ "endcmap
CMapName currentdict /CMap defineresource pop
end
end"
  return s

private def wArray (font : Font) (used : Array (Nat × Char)) : String := Id.run do
  let mut s := "["
  for (g, _) in used do
    let w := (font.widths[g]?.getD 0) * 1000 / font.unitsPerEm
    s := s ++ s!" {g} [{w}]"
  return s ++ " ]"

/-- Escape a PDF literal string: balance-sensitive characters only. -/
private def pdfString (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c == '(' || c == ')' || c == '\\' then
      out := out.push '\\'
    out := out.push c
  return out

/-- Escape text for XML character data. -/
private def xmlEscape (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c == '&' then out := out ++ "&amp;"
    else if c == '<' then out := out ++ "&lt;"
    else if c == '>' then out := out ++ "&gt;"
    else out := out.push c
  return out

/-- XMP packet mirroring the Info dictionary; PDF 2.0 expects metadata here. -/
private def xmpPacket (info : Ir.Meta) : String :=
  let elem (tag : String) (v : Option String) : String :=
    match v with
    | some s =>
      s!"        <{tag}><rdf:Alt><rdf:li xml:lang=\"x-default\">{xmlEscape s}</rdf:li></rdf:Alt></{tag}>\n"
    | none => ""
  let seqElem (tag : String) (v : Option String) : String :=
    match v with
    | some s => s!"        <{tag}><rdf:Seq><rdf:li>{xmlEscape s}</rdf:li></rdf:Seq></{tag}>\n"
    | none => ""
  "<?xpacket begin=\"\" id=\"W5M0MpCehiHzreSzNTczkc9d\"?>\n" ++
  "<x:xmpmeta xmlns:x=\"adobe:ns:meta/\">\n" ++
  "  <rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">\n" ++
  "    <rdf:Description rdf:about=\"\"\n" ++
  "        xmlns:dc=\"http://purl.org/dc/elements/1.1/\"\n" ++
  "        xmlns:pdf=\"http://ns.adobe.com/pdf/1.3/\"\n" ++
  "        xmlns:xmp=\"http://ns.adobe.com/xap/1.0/\">\n" ++
  elem "dc:title" info.title ++
  seqElem "dc:creator" info.author ++
  elem "dc:description" info.subject ++
  (match info.keywords with
   | some k => s!"        <pdf:Keywords>{xmlEscape k}</pdf:Keywords>\n"
   | none => "") ++
  "        <pdf:Producer>leantex</pdf:Producer>\n" ++
  "    </rdf:Description>\n" ++
  "  </rdf:RDF>\n" ++
  "</x:xmpmeta>\n" ++
  "<?xpacket end=\"w\"?>"

private structure Wr where
  out : ByteArray := ByteArray.empty

private def Wr.put (w : Wr) (s : String) : Wr :=
  { out := w.out ++ s.toUTF8 }

private def Wr.putB (w : Wr) (b : ByteArray) : Wr :=
  { out := w.out ++ b }

/-- Serialize positioned pages into a PDF 2.0 file: cross-reference stream,
object streams, one Identity-H CID font per face actually used (fully
embedded, with its own ToUnicode), and the document information the source
declared (Info dictionary plus XMP). -/
def write (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta := {}) : ByteArray := Id.run do
  let np := pages.size
  -- Only faces that actually contribute glyphs are embedded; a declared but
  -- unused face would otherwise cost a megabyte of font file.
  let allUsed : Array (Array (Nat × Char)) :=
    (Array.range fs.fonts.size).map fun k => usedGlyphs k (fs.get k).numGlyphs pages
  let keep : Array Nat :=
    (Array.range fs.fonts.size).filter fun k => !(allUsed[k]!).isEmpty
  let keep := if keep.isEmpty then #[0] else keep
  let remap : Array Nat := Id.run do
    let mut r : Array Nat := Array.replicate fs.fonts.size 0
    for (old, new) in keep.zipIdx do
      r := r.set! old new
    return r
  let usedPerFont : Array (Array (Nat × Char)) := keep.map fun k => allUsed[k]!
  let nf := keep.size
  -- Object ids are laid out in fixed blocks so the xref can be built without
  -- a second pass: 1 catalog, 2 pages, then four ids per font, then two per
  -- page, then info, xmp, objstm, xref.
  let fontBase := 3
  let type0Id (k : Nat) := fontBase + 4 * k
  let cidId (k : Nat) := fontBase + 4 * k + 1
  let fdId (k : Nat) := fontBase + 4 * k + 2
  let toUniId (k : Nat) := fontBase + 4 * k + 3
  let fileBase := fontBase + 4 * nf
  let fileId (k : Nat) := fileBase + k
  let pageBase := fileBase + nf
  let pageId (i : Nat) := pageBase + 2 * i
  let contentId (i : Nat) := pageBase + 2 * i + 1
  let infoId := pageBase + 2 * np
  let xmpId := infoId + 1
  let objStmId := xmpId + 1
  let xrefId := objStmId + 1
  let size := xrefId + 1

  -- compressed (non-stream) objects, serialized bare
  let kids := String.intercalate " " ((List.range np).map fun i => s!"{pageId i} 0 R")
  let catalog := s!"<< /Type /Catalog /Pages 2 0 R /Metadata {xmpId} 0 R >>"
  let pagesObj := s!"<< /Type /Pages /Kids [{kids}] /Count {np} >>"
  let fontResources := String.intercalate " "
    ((List.range nf).map fun k => s!"/F{k + 1} {type0Id k} 0 R")
  let fontObjs : List (Nat × String) := (List.range nf).flatMap fun k =>
    let font := fs.get keep[k]!
    let used := usedPerFont[k]!
    let baseFont := pdfName font.psName
    let ascent1000 := font.ascent * 1000 / font.unitsPerEm
    let descent1000 := font.descent * 1000 / font.unitsPerEm
    let cidSubtype := if font.isCff then "CIDFontType0" else "CIDFontType2"
    let cidToGid := if font.isCff then "" else " /CIDToGIDMap /Identity"
    let fontFileKey := if font.isCff then "FontFile3" else "FontFile2"
    let italicAngle := if font.isItalic then -12 else 0
    -- Flags: bit 1 fixed pitch, bit 3 symbolic, bit 7 italic (1-based).
    let flags := 4 + (if font.isFixedPitch then 1 else 0) + (if font.isItalic then 64 else 0)
    let stemV := if font.isBold then 140 else 80
    [(type0Id k,
      s!"<< /Type /Font /Subtype /Type0 /BaseFont /{baseFont} /Encoding /Identity-H /DescendantFonts [{cidId k} 0 R] /ToUnicode {toUniId k} 0 R >>"),
     (cidId k,
      s!"<< /Type /Font /Subtype /{cidSubtype} /BaseFont /{baseFont} /CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >> /FontDescriptor {fdId k} 0 R /DW 1000 /W {wArray font used}{cidToGid} >>"),
     (fdId k,
      s!"<< /Type /FontDescriptor /FontName /{baseFont} /Flags {flags} /FontBBox [-1000 {descent1000} 2000 {ascent1000}] /ItalicAngle {italicAngle} /Ascent {ascent1000} /Descent {descent1000} /CapHeight {ascent1000} /StemV {stemV} /{fontFileKey} {fileId k} 0 R >>")]
  let annots (i : Nat) : String :=
    let rects := linkRects geom pages[i]!
    if rects.isEmpty then "" else
      let entries := rects.toList.map fun (x0, y0, x1, y1, url) =>
        s!"<< /Type /Annot /Subtype /Link /Rect [{x0.toPtString} {y0.toPtString} " ++
        s!"{x1.toPtString} {y1.toPtString}] /Border [0 0 0] /F 4 " ++
        s!"/A << /S /URI /URI ({pdfString url}) >> >>"
      " /Annots [" ++ String.intercalate " " entries ++ "]"
  let pageDict (i : Nat) :=
    s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {geom.pageW.toPtString} {geom.pageH.toPtString}] /Resources << /Font << {fontResources} >> >>{annots i} /Contents {contentId i} 0 R >>"
  -- PDF 2.0 text strings are UTF-8, so declared metadata needs no escaping
  -- beyond the literal-string delimiters.
  let infoEntry (key : String) (v : Option String) : String :=
    match v with
    | some s => s!" /{key} ({pdfString s})"
    | none => ""
  let infoDict :=
    "<<" ++ infoEntry "Title" info.title ++ infoEntry "Author" info.author ++
    infoEntry "Subject" info.subject ++ infoEntry "Keywords" info.keywords ++
    s!" /Producer (leantex) >>"

  let compressed : List (Nat × String) :=
    [(1, catalog), (2, pagesObj)] ++ fontObjs ++ [(infoId, infoDict)] ++
    (List.range np).map fun i => (pageId i, pageDict i)

  -- object stream payload
  let mut header := ""
  let mut payload := ""
  for (id, body) in compressed do
    header := header ++ s!"{id} {payload.utf8ByteSize} "
    payload := payload ++ body ++ "\n"
  let objStmData := header ++ payload
  let first := header.utf8ByteSize

  -- assemble the file
  let mut w : Wr := {}
  let mut locs : Array (Nat × Nat) := Array.replicate size (0, 0)  -- (kind, val): 1=direct
  w := w.put "%PDF-2.0\n%"
  w := w.putB ⟨#[0xE2, 0xE3, 0xCF, 0xD3]⟩
  w := w.put "\n"

  -- direct stream objects
  let putStream (w : Wr) (id : Nat) (dict : String) (data : ByteArray) : Wr × Nat :=
    let off := w.out.size
    let w := w.put s!"{id} 0 obj\n<< {dict} /Length {data.size} >>\nstream\n"
    let w := w.putB data
    let w := w.put "\nendstream\nendobj\n"
    (w, off)

  for i in [0:np] do
    let data := (contentStream geom remap pages[i]!).toUTF8
    let (w', off) := putStream w (contentId i) "" data
    w := w'
    locs := locs.set! (contentId i) (1, off)

  for k in [0:nf] do
    let font := fs.get keep[k]!
    let tuData := (toUnicode usedPerFont[k]!).toUTF8
    let (w', tuOff) := putStream w (toUniId k) "" tuData
    w := w'
    locs := locs.set! (toUniId k) (1, tuOff)
    let ffDict := if font.isCff then "/Subtype /OpenType" else s!"/Length1 {font.data.size}"
    let (w'', ffOff) := putStream w (fileId k) ffDict font.data
    w := w''
    locs := locs.set! (fileId k) (1, ffOff)

  let (wx, xmpOff) := putStream w xmpId "/Type /Metadata /Subtype /XML"
    (xmpPacket info).toUTF8
  w := wx
  locs := locs.set! xmpId (1, xmpOff)

  let (w3, osOff) := putStream w objStmId
    s!"/Type /ObjStm /N {compressed.length} /First {first}" objStmData.toUTF8
  w := w3
  locs := locs.set! objStmId (1, osOff)
  for (idx, (id, _)) in compressed.zipIdx.map (fun (p, i) => (i, p)) do
    locs := locs.set! id (2, idx)

  -- cross-reference stream: W [1 4 2]
  let xrefOff := w.out.size
  let mut rows : ByteArray := ByteArray.empty
  for id in [0:size] do
    if id == 0 then
      rows := rows ++ ⟨#[0, 0, 0, 0, 0, 0xFF, 0xFF]⟩
    else if id == xrefId then
      let off := xrefOff
      rows := rows.push 1
      rows := rows ++ ⟨#[UInt8.ofNat (off / 16777216), UInt8.ofNat (off / 65536 % 256),
        UInt8.ofNat (off / 256 % 256), UInt8.ofNat (off % 256)]⟩
      rows := rows ++ ⟨#[0, 0]⟩
    else
      let (kind, v) := locs[id]!
      if kind == 1 then
        rows := rows.push 1
        rows := rows ++ ⟨#[UInt8.ofNat (v / 16777216), UInt8.ofNat (v / 65536 % 256),
          UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)]⟩
        rows := rows ++ ⟨#[0, 0]⟩
      else
        rows := rows.push 2
        rows := rows ++ ⟨#[UInt8.ofNat (objStmId / 16777216), UInt8.ofNat (objStmId / 65536 % 256),
          UInt8.ofNat (objStmId / 256 % 256), UInt8.ofNat (objStmId % 256)]⟩
        rows := rows ++ ⟨#[UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)]⟩
  let idA := hex16 (fnv64 14695981039346656037 w.out)
  let idB := hex16 (fnv64 1099511628211 w.out)
  let xrefDict := s!"/Type /XRef /Size {size} /W [1 4 2] /Index [0 {size}] /Root 1 0 R /Info {infoId} 0 R /ID [<{idA}> <{idB}>]"
  let w4 := (putStream w xrefId xrefDict rows).1
  w := w4
  w := w.put s!"startxref\n{xrefOff}\n%%EOF\n"
  return w.out

end LeanTex.Core.Pdf
