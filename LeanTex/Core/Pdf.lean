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

/-- Used glyphs: one char witness per gid, ascending gid. Mark array — the
glyph stream is large (every glyph on every page), so no sorting. -/
private def usedGlyphs (numGlyphs : Nat) (pages : Array PageOut) :
    Array (Nat × Char) := Id.run do
  let mut seen : Array (Option Char) := Array.replicate numGlyphs none
  for p in pages do
    for l in p.lines do
      for s in l.segs do
        if let .run glyphs := s then
          for (g, c) in glyphs do
            if h : g < seen.size then
              if seen[g].isNone then
                seen := seen.set! g (some c)
  let mut out : Array (Nat × Char) := #[]
  for (c?, g) in seen.zipIdx do
    if let some c := c? then
      out := out.push (g, c)
  return out

private def contentStream (geom : Geom) (page : PageOut) : String := Id.run do
  let mut s := "BT\n"
  let mut curSize : Sp := -1
  for l in page.lines do
    if l.segs.isEmpty then
      continue
    if l.size != curSize then
      s := s ++ s!"/F1 {l.size.toPtString} Tf\n"
      curSize := l.size
    let ypdf := geom.pageH - l.y
    s := s ++ s!"1 0 0 1 {l.x.toPtString} {ypdf.toPtString} Tm\n["
    for seg in l.segs do
      match seg with
      | .run glyphs =>
        s := s.push '<'
        for (g, _) in glyphs do
          s := s.push (hexDigit (g / 4096))
          s := s.push (hexDigit (g / 256))
          s := s.push (hexDigit (g / 16))
          s := s.push (hexDigit g)
        s := s.push '>'
      | .gap w =>
        let v : Int := -(w * 1000 / l.size)
        s := s ++ s!"{v}"
    s := s ++ "] TJ\n"
  s := s ++ "ET"
  return s

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

private structure Wr where
  out : ByteArray := ByteArray.empty

private def Wr.put (w : Wr) (s : String) : Wr :=
  { out := w.out ++ s.toUTF8 }

private def Wr.putB (w : Wr) (b : ByteArray) : Wr :=
  { out := w.out ++ b }

/-- Serialize positioned pages into a PDF 2.0 file: cross-reference stream,
object streams, Identity-H CID font (full embed), ToUnicode. -/
def write (geom : Geom) (font : Font) (pages : Array PageOut) : ByteArray := Id.run do
  let used := usedGlyphs font.numGlyphs pages
  let np := pages.size
  -- ids: 1 catalog, 2 pages, 3 type0, 4 cid, 5 descriptor,
  -- 6 tounicode, 7 fontfile, 8+2i page dict, 9+2i content, objstm, xref
  let pageId (i : Nat) := 8 + 2 * i
  let contentId (i : Nat) := 9 + 2 * i
  let objStmId := 8 + 2 * np
  let xrefId := objStmId + 1
  let size := xrefId + 1
  let baseFont := pdfName font.psName
  let ascent1000 := font.ascent * 1000 / font.unitsPerEm
  let descent1000 := font.descent * 1000 / font.unitsPerEm

  -- compressed (non-stream) objects, serialized bare
  let kids := String.intercalate " " ((List.range np).map fun i => s!"{pageId i} 0 R")
  let catalog := "<< /Type /Catalog /Pages 2 0 R >>"
  let pagesObj := s!"<< /Type /Pages /Kids [{kids}] /Count {np} >>"
  let type0 := s!"<< /Type /Font /Subtype /Type0 /BaseFont /{baseFont} /Encoding /Identity-H /DescendantFonts [4 0 R] /ToUnicode 6 0 R >>"
  let cidSubtype := if font.isCff then "CIDFontType0" else "CIDFontType2"
  let cidToGid := if font.isCff then "" else " /CIDToGIDMap /Identity"
  let cid := s!"<< /Type /Font /Subtype /{cidSubtype} /BaseFont /{baseFont} /CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >> /FontDescriptor 5 0 R /DW 1000 /W {wArray font used}{cidToGid} >>"
  let fontFileKey := if font.isCff then "FontFile3" else "FontFile2"
  let fd := s!"<< /Type /FontDescriptor /FontName /{baseFont} /Flags 4 /FontBBox [-1000 {descent1000} 2000 {ascent1000}] /ItalicAngle 0 /Ascent {ascent1000} /Descent {descent1000} /CapHeight {ascent1000} /StemV 80 /{fontFileKey} 7 0 R >>"
  let pageDict (i : Nat) :=
    s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {geom.pageW.toPtString} {geom.pageH.toPtString}] /Resources << /Font << /F1 3 0 R >> >> /Contents {contentId i} 0 R >>"

  let compressed : List (Nat × String) :=
    [(1, catalog), (2, pagesObj), (3, type0), (4, cid), (5, fd)] ++
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
    let data := (contentStream geom pages[i]!).toUTF8
    let (w', off) := putStream w (contentId i) "" data
    w := w'
    locs := locs.set! (contentId i) (1, off)

  let tuData := (toUnicode used).toUTF8
  let (w', tuOff) := putStream w 6 "" tuData
  w := w'
  locs := locs.set! 6 (1, tuOff)

  let ffDict := if font.isCff then "/Subtype /OpenType" else s!"/Length1 {font.data.size}"
  let (w'', ffOff) := putStream w 7 ffDict font.data
  w := w''
  locs := locs.set! 7 (1, ffOff)

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
  let xrefDict := s!"/Type /XRef /Size {size} /W [1 4 2] /Index [0 {size}] /Root 1 0 R /ID [<{idA}> <{idB}>]"
  let w4 := (putStream w xrefId xrefDict rows).1
  w := w4
  w := w.put s!"startxref\n{xrefOff}\n%%EOF\n"
  return w.out

end LeanTex.Core.Pdf
