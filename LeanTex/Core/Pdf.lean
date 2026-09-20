import LeanTex.Core.Dim
import LeanTex.Core.Font
import LeanTex.Core.HtmlDoc
import LeanTex.Core.Layout

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Layout

private def hexDigit (n : Nat) : Char := "0123456789ABCDEF".toList[n % 16]!

/-- A rectangle in PDF user space: lower-left and upper-right corners.
Fields are spelled `Int` (the same type `Sp` names) because `omega`
reads the bare spelling only: the nesting proof below is the point of
the type. -/
structure Rect where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving Repr, BEq

/-- Containment, the relation ISO 32000-2 expects between the page boxes. -/
def Rect.within (inner outer : Rect) : Prop :=
  outer.x0 ≤ inner.x0 ∧ outer.y0 ≤ inner.y0 ∧
  inner.x1 ≤ outer.x1 ∧ inner.y1 ≤ outer.y1

def Rect.render (r : Rect) : String :=
  s!"[{Sp.toPtString r.x0} {Sp.toPtString r.y0} {Sp.toPtString r.x1} {Sp.toPtString r.y1}]"

/-- The page boxes, as consequences of the declared trim size and bleed —
never hand-rolled numbers. ISO 32000-2 §14.11.2 (Table 361) gives each its
meaning: **TrimBox** is "the intended dimensions of the finished page
after trimming" — the card at its trim size, offset by the bleed from the
medium's corner; **BleedBox** is "the region to which the contents of the
page shall be clipped when output in a production environment", trim plus
the declared bleed on every side, which is exactly the whole medium here;
**ArtBox** is "the extent of the page's meaningful content … as intended
by the page's creator" — for a finished artefact like a card, the trim;
**MediaBox** (§7.7.3.3) is "the boundaries of the physical medium",
containing them all. -/
def pageBoxes (pageW pageH bleed : Int) : Rect × Rect × Rect :=
  (⟨0, 0, pageW + 2 * bleed, pageH + 2 * bleed⟩,
   ⟨0, 0, pageW + 2 * bleed, pageH + 2 * bleed⟩,
   ⟨bleed, bleed, pageW + bleed, pageH + bleed⟩)

/-- The print guarantee a prepress proof checks: the boxes nest —
TrimBox ⊆ BleedBox ⊆ MediaBox — and the trim is exactly the declared page
size, whatever the bleed. The same shape as the `text.in_area` assertion:
what the file tells the finishing knife matches what the document
declared. -/
theorem pageBoxes_nest (W H b : Int) (hb : 0 ≤ b) :
    (pageBoxes W H b).2.2.within (pageBoxes W H b).2.1 ∧
    (pageBoxes W H b).2.1.within (pageBoxes W H b).1 ∧
    (pageBoxes W H b).2.2.x1 - (pageBoxes W H b).2.2.x0 = W ∧
    (pageBoxes W H b).2.2.y1 - (pageBoxes W H b).2.2.y0 = H := by
  dsimp only [pageBoxes, Rect.within]
  omega

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
        if let .run idx _ _ _ glyphs _ _ _ _ := s then
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

/-- The keep set over a per-face used-glyph census: the faces the file
embeds. Only faces that actually contribute glyphs are kept — a declared
but unused face would otherwise cost a megabyte of font file — and face 0
stands in when nothing set text: a PDF's page resources still name a font. -/
def keepOf (used : Array (Array (Nat × Char))) : Array Nat :=
  let keep := (Array.range used.size).filter fun k => !((used[k]?.getD #[]).isEmpty)
  if keep.isEmpty then #[0] else keep

/-- The faces `write` embeds for these pages, named so the cross-backend
contract below can quantify over the writer's own decision, not a copy. -/
def keepFaces (fs : FontSet) (pages : Array PageOut) : Array Nat :=
  keepOf ((Array.range fs.fonts.size).map fun k =>
    usedGlyphs k (fs.get k).numGlyphs pages)

theorem keepFaces_lt (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) : ∀ k ∈ keepFaces fs pages, k < fs.fonts.size := by
  intro k hk
  unfold keepFaces keepOf at hk
  dsimp only at hk
  rw [Array.size_map, Array.size_range] at hk
  split at hk
  · simp only [Array.mem_singleton] at hk
    omega
  · have := (Array.mem_filter.mp hk).1
    simpa using this

/-- **The HTML ships the faces the PDF embeds: one `FontSet`, two
projections.** Every face this writer would embed for these pages
(`keepFaces`) is declared by a `@font-face` in the HTML emission built
from the same set (`HtmlDoc.shipFaces`, which `fontFaceCss` renders one
rule per entry and whose files `fontAssets` requests of the driver,
`HtmlDoc.shipFaces_src_shipped`). Stated as the superset the HTML can
honestly promise: it never sees layout's used-glyph data, so it declares
every face of the set, and the embedded subset is covered a fortiori. The
convention is AGENTS': the artifact is a function of the document and the
font environment — a viewer without the document's faces installed must
not read it in a stand-in. -/
theorem html_fonts_cover_pdf (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) :
    ∀ k ∈ keepFaces fs pages, ∃ ff ∈ HtmlDoc.shipFaces fs, ff.index = k :=
  fun k hk => HtmlDoc.shipFaces_covers fs (keepFaces_lt fs pages h k hk)

/-- One page's content stream. Glyph runs are written as `TJ` arrays; the
pen's position is tracked against the layout's, and only a glyph run moves
it — a gap, a kern or a rule advances the layout position and nothing is
written until glyphs follow. Then the move is a `TJ` adjustment when it is
small and the array is open, and an absolute `Tm` otherwise: an adjustment
is thousandths of the live font size, and a viewer that keeps them in
sixteen bits (macOS Preview drops the whole array past ±32767) never sees
one that large. A rule-only line writes nothing here. A `TJ` array cannot
switch fonts or colours mid-array, so a run in a different face or colour
closes it, emits `Tf`/`rg`, and reopens it. -/
private def contentStream (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) : String := Id.run do
  let mut s := ""
  -- Fills paint first, in order: the page background, then any bars, then
  -- the text over them.
  for f in page.fills do
    s := s ++ s!"q {f.color.pdfFill} {f.x.toPtString} \
{(geom.pageH - f.y - f.h).toPtString} {f.w.toPtString} {f.h.toPtString} re f Q\n"
  -- Picture paths — node outlines, later edges — paint after the fills
  -- and before the text, so a node's own fill sits under its label. The
  -- painting operators are ISO 32000-2 §8.5.3 (S stroke, f fill, B fill
  -- then stroke); dash patterns §8.4.3.6 with pgf's rhythms (§15.3.2:
  -- dashed on 3pt off 3pt, dotted on the line width off 1pt).
  for p in page.paths do
    let mut g := "q "
    if let some fl := p.fill then
      g := g ++ s!"{fl.pdfFill} "
    if let some st := p.stroke then
      let dashOp := match st.dash with
        | .solid => ""
        | .dashed => "[3 3] 0 d "
        | .dotted => s!"[{st.width.toPtString} 1] 0 d "
      g := g ++ s!"{st.color.pdfStroke} {st.width.toPtString} w " ++ dashOp
    match p.path with
    | .circle cx cy r =>
      -- Four cubic Bézier arcs, the standard k = 4(√2−1)/3 ≈ 0.5523
      -- magic-number circle approximation; c is §8.5.2.2.
      let x := geom.bleed + cx
      let y := geom.bleed + geom.pageH - cy
      let k := r * 5523 / 10000
      let pt := Sp.toPtString
      g := g ++ s!"{pt (x + r)} {pt y} m " ++
        s!"{pt (x + r)} {pt (y + k)} {pt (x + k)} {pt (y + r)} {pt x} {pt (y + r)} c " ++
        s!"{pt (x - k)} {pt (y + r)} {pt (x - r)} {pt (y + k)} {pt (x - r)} {pt y} c " ++
        s!"{pt (x - r)} {pt (y - k)} {pt (x - k)} {pt (y - r)} {pt x} {pt (y - r)} c " ++
        s!"{pt (x + k)} {pt (y - r)} {pt (x + r)} {pt (y - k)} {pt (x + r)} {pt y} c h "
    | .rect rx ry rw rh =>
      let x := geom.bleed + rx
      let y := geom.bleed + geom.pageH - ry - rh
      g := g ++ s!"{x.toPtString} {y.toPtString} {rw.toPtString} {rh.toPtString} re "
    | .segs segs =>
      -- Segment endpoints are explicit, so each opens with its own move;
      -- a chain of touching segments still strokes as one visual path.
      let mut prev : Option (Sp × Sp) := none
      for sg in segs do
        match sg with
        | .line x1 y1 x2 y2 =>
          let a := (geom.bleed + x1, geom.bleed + geom.pageH - y1)
          let b := (geom.bleed + x2, geom.bleed + geom.pageH - y2)
          if prev != some a then
            g := g ++ s!"{a.1.toPtString} {a.2.toPtString} m "
          g := g ++ s!"{b.1.toPtString} {b.2.toPtString} l "
          prev := some b
        | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
          let a := (geom.bleed + x1, geom.bleed + geom.pageH - y1)
          let c1 := (geom.bleed + c1x, geom.bleed + geom.pageH - c1y)
          let c2 := (geom.bleed + c2x, geom.bleed + geom.pageH - c2y)
          let b := (geom.bleed + x2, geom.bleed + geom.pageH - y2)
          if prev != some a then
            g := g ++ s!"{a.1.toPtString} {a.2.toPtString} m "
          g := g ++ s!"{c1.1.toPtString} {c1.2.toPtString} {c2.1.toPtString} \
{c2.2.toPtString} {b.1.toPtString} {b.2.toPtString} c "
          prev := some b
    | .tri x1 y1 x2 y2 x3 y3 =>
      let p (x y : Sp) : String :=
        s!"{(geom.bleed + x).toPtString} {(geom.bleed + geom.pageH - y).toPtString}"
      g := g ++ s!"{p x1 y1} m {p x2 y2} l {p x3 y3} l h "
    let paint := match p.stroke, p.fill with
      | some _, some _ => "B"
      | some _, none => "S"
      | none, some _ => "f"
      | none, none => "n"
    s := s ++ g ++ paint ++ " Q\n"
  s := s ++ "BT\n"
  let mut curFont : Int := -1
  let mut curSize : Sp := -1
  let mut curColor : Ir.Color := Ir.Color.black
  -- The live horizontal text scale, per-mille delta from 100%: font
  -- expansion's per-line factor. `Tz` (ISO 32000-2 §9.3.4) scales glyph
  -- shapes and advances alike, which is exactly hz-style expansion — the
  -- run widths layout emitted are already rescaled by the same factor,
  -- so painted ink and measured metrics agree.
  let mut curTz : Int := 0
  -- Rules are path operators, which may not appear inside BT/ET, so they are
  -- gathered here and drawn after the text. Images gather with them: `Do`
  -- is likewise not a text-object operator.
  let mut rules : Array (Sp × Sp × Sp × Sp × Ir.Color) := #[]
  let mut images : Array (Sp × Sp × Sp × Sp × Option Nat) := #[]
  for l in page.lines do
    -- Bleed shifts everything: layout works in trim coordinates and the
    -- trim box sits `bleed` in from the medium's corner.
    let ypdf := geom.bleed + geom.pageH - l.y
    if l.expand != curTz then
      let tz := 1000 + l.expand
      s := s ++ s!"{tz / 10}.{tz % 10} Tz\n"
      curTz := l.expand
    let mut inArray := false
    let mut x := geom.bleed + l.x
    -- Where the pen is, when it is known: a fresh line has no position until
    -- its first glyph run sets one. A raised run (a math script) moves the
    -- baseline too, so the pen is a point: a `TJ` adjustment can only move
    -- x, and any vertical move is an absolute `Tm`.
    let mut pen : Option (Sp × Sp) := none
    for seg in l.segs do
      match seg with
      | .rule w thickness raise color =>
        rules := rules.push (x, ypdf + raise, w, thickness, color)
        x := x + w
      | .image idx w h =>
        -- Bottom on the baseline, `h` up: the `cm` maps the XObject's unit
        -- square onto exactly the box layout measured.
        images := images.push (x, ypdf, w, h, idx.bind fun k => imgMap[k]?.getD none)
        x := x + w
      | .gap w =>
        x := x + w
      | .run idx color _ w glyphs segSize _ raise _ =>
        if glyphs.isEmpty then
          -- A kern: width, no glyphs. It moves the layout position like a gap.
          x := x + w
        else
        let runY := ypdf + raise
        let size := if segSize == 0 then l.size else segSize
        let changes := curFont != idx || curSize != size || curColor != color
        -- Bring the pen to the run. Inside an open array with the face
        -- unchanged, a small horizontal move is an adjustment in the live
        -- size; any other move is absolute, and closes the array.
        match pen with
        | some (hx, hy) =>
          if hx != x || hy != runY then
            -- A TJ adjustment displaces by thousandths of the font size
            -- *times the horizontal scale*, so under expansion the number
            -- compensates by the inverse factor.
            let v0 : Int := (x - hx) * 1000 / curSize
            let v : Int := if curTz == 0 then v0 else v0 * 1000 / (1000 + curTz)
            if inArray && !changes && hy == runY && v.natAbs ≤ 32000 then
              s := s ++ s!"{-v}"
            else
              if inArray then
                s := s ++ "] TJ\n"
                inArray := false
              s := s ++ s!"1 0 0 1 {x.toPtString} {runY.toPtString} Tm\n"
        | none =>
          s := s ++ s!"1 0 0 1 {x.toPtString} {runY.toPtString} Tm\n"
        if changes then
          if inArray then
            s := s ++ "] TJ\n"
            inArray := false
          if curFont != idx || curSize != size then
            s := s ++ s!"/F{(remap[idx]?.getD 0) + 1} {size.toPtString} Tf\n"
            curFont := idx
            curSize := size
          if curColor != color then
            s := s ++ s!"{color.pdfFill}\n"
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
        x := x + w
        pen := some (x, runY)
    if inArray then
      s := s ++ "] TJ\n"
  s := s ++ "ET"
  for (ix, iy, iw, ih, res?) in images do
    match res? with
    | some n =>
      s := s ++ s!"\nq {iw.toPtString} 0 0 {ih.toPtString} {ix.toPtString} \
{iy.toPtString} cm /Im{n + 1} Do Q"
    | none =>
      -- The placeholder for an image that did not load: an outlined box of
      -- the requested size, so the failure is visible where the figure
      -- would stand and the diagnostic already said why.
      s := s ++ s!"\nq 0.62 0.62 0.66 RG 0.75 w {ix.toPtString} {iy.toPtString} \
{iw.toPtString} {ih.toPtString} re S Q"
  for (rx, ry, rw, rh, color) in rules do
    s := s ++ s!"\nq {color.pdfFill} {rx.toPtString} {ry.toPtString} \
{rw.toPtString} {rh.toPtString} re f Q"
  return s

/-- Link rectangles for one page, in PDF user space. Adjacent runs with the
same destination merge, so a hyphenated or multi-font link is one annotation
per line rather than one per glyph run. -/
private def linkRects (geom : Geom) (page : PageOut) :
    Array (Sp × Sp × Sp × Sp × String) := Id.run do
  let mut out : Array (Sp × Sp × Sp × Sp × String) := #[]
  for l in page.lines do
    let mut x := geom.bleed + l.x
    -- Merge tolerance of one em: a run separated only by an interword space
    -- joins the previous rectangle, so a multi-word link is one annotation.
    let pad := l.size
    for seg in l.segs do
      match seg with
      | .run _ _ link w _ segSize _ _ _ =>
        let size := if segSize == 0 then l.size else segSize
        let y0 := geom.bleed + geom.pageH - l.y - size / 4
        let y1 := geom.bleed + geom.pageH - l.y + size * 4 / 5
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
      | .rule w _ _ _ => x := x + w
      | .image _ w _ => x := x + w
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

/-- A PDF *text string*, delimiters included (ISO 32000-2 §7.9.2.2): ASCII
rides as a literal string; anything beyond it is written as a UTF-16BE
hex string opening with the byte-order mark (§7.9.2.2.1). Raw UTF-8 bytes
in an unmarked string read as PDFDocEncoding — 'é' displays as 'Ã©' in a
viewer's document panel — so the spelling is the spec's, never the
source's bytes. Byte strings (URIs) stay `pdfString`. -/
private def pdfTextString (s : String) : String :=
  if s.toList.all (fun c => c.toNat < 0x80) then s!"({pdfString s})"
  else s.toList.foldl (· ++ utf16Hex ·) "<FEFF" ++ ">"

/-- XMP packet mirroring the Info dictionary; PDF 2.0 expects metadata here. -/
private def xmpPacket (info : Ir.Meta) : String :=
  let elem (tag : String) (v : Option String) : String :=
    match v with
    | some s =>
      s!"        <{tag}><rdf:Alt><rdf:li xml:lang=\"x-default\">{Html.escapeText s}</rdf:li></rdf:Alt></{tag}>\n"
    | none => ""
  let seqElem (tag : String) (v : Option String) : String :=
    match v with
    | some s => s!"        <{tag}><rdf:Seq><rdf:li>{Html.escapeText s}</rdf:li></rdf:Seq></{tag}>\n"
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
  -- The canonical URL: dc:identifier, "an unambiguous reference to the
  -- resource within a given context" (XMP Specification Part 1 §8.3,
  -- ISO 16684-1, Dublin Core namespace; simple Text, not Alt/Seq).
  (match info.url with
   | some u => s!"        <dc:identifier>{Html.escapeText u}</dc:identifier>\n"
   | none => "") ++
  (match info.keywords with
   | some k => s!"        <pdf:Keywords>{Html.escapeText k}</pdf:Keywords>\n"
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

/-- The catalog's language entry: `/Lang` spelled from the declared tag —
the document's main language over every text run that carries no finer
mark (ISO 32000-2 §14.9.2.2; BCP 47) — and nothing when the document
declares none. The same `Ir.Meta` field the HTML root's `lang` attribute
reads (`HtmlDoc.emit_lang_declared`). -/
def langEntry : Option String → String
  | some tag => s!" /Lang ({pdfString tag})"
  | none => ""

/-- The document catalog (ISO 32000-2 §7.7.2): the page tree, an outline
when the layout carried one, the XMP metadata stream, the declared
language, and `/ViewerPreferences /DisplayDocTitle` — the reader's window
titles from the document's own metadata title rather than its file name
(§12.2; PDF/UA requires it). -/
def catalogDict (outlinesRef : String) (xmpId : Nat) (lang : Option String) : String :=
  s!"<< /Type /Catalog /Pages 2 0 R{outlinesRef} /Metadata {xmpId} 0 R\
{langEntry lang} /ViewerPreferences << /DisplayDocTitle true >> >>"

/-- The PDF twin of `emit_lang_declared`: the catalog is the language
entry of the document's declared tag between two fixed dictionary halves,
by construction — so `/Lang` appears exactly when the document declares a
language, reading the same `Ir.Meta` field as the HTML root's `lang`.
The webMetaChecks census in Tests/Backends is the wiring witness that
`write` ships this dictionary. -/
theorem pdf_lang_declared (outlinesRef : String) (xmpId : Nat) (lang : Option String) :
    ∃ pre post,
      catalogDict outlinesRef xmpId lang = pre ++ langEntry lang ++ post :=
  ⟨s!"<< /Type /Catalog /Pages 2 0 R{outlinesRef} /Metadata {xmpId} 0 R",
   " /ViewerPreferences << /DisplayDocTitle true >> >>", rfl⟩

/-- Serialize positioned pages into a PDF 2.0 file: cross-reference stream,
object streams, one Identity-H CID font per face actually used (fully
embedded, with its own ToUnicode), image XObjects for every image actually
placed, and the document information the source declared (Info dictionary
plus XMP). -/
def write (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta := {}) (imgs : Image.Store := {})
    (outline : Array OutlineEntry := #[]) : ByteArray := Id.run do
  let np := pages.size
  -- Only faces that actually contribute glyphs are embedded — `keepFaces`,
  -- the very function `html_fonts_cover_pdf` quantifies over, so the
  -- contract holds of the writer's own decision, not a copy. `allUsed`
  -- stays for the per-face glyph census the kept faces subset.
  let allUsed : Array (Array (Nat × Char)) :=
    (Array.range fs.fonts.size).map fun k => usedGlyphs k (fs.get k).numGlyphs pages
  let keep : Array Nat := keepFaces fs pages
  let remap : Array Nat := Id.run do
    let mut r : Array Nat := Array.replicate fs.fonts.size 0
    for (old, new) in keep.zipIdx do
      r := r.set! old new
    return r
  let usedPerFont : Array (Array (Nat × Char)) := keep.map fun k => allUsed[k]!
  let nf := keep.size
  -- Images actually placed and loaded become XObjects, one per file however
  -- often it is placed; a placeholder is drawn inline and needs no object.
  let usedImgs : Array Nat := Id.run do
    let mut out : Array Nat := #[]
    for p in pages do
      for l in p.lines do
        for s in l.segs do
          if let .image (some k) _ _ := s then
            if ((imgs.get? k).bind (·.info)).isSome && !out.contains k then
              out := out.push k
    return out
  let ni := usedImgs.size
  let imgMap : Array (Option Nat) := Id.run do
    let mut m : Array (Option Nat) := Array.replicate imgs.entries.size none
    for (k, n) in usedImgs.zipIdx do
      m := m.set! k (some n)
    return m
  -- Object ids are laid out in fixed blocks so the xref can be built without
  -- a second pass: 1 catalog, 2 pages, then four ids per font, one file per
  -- font, then per image an XObject plus an SMask when it has an alpha
  -- plane, then two per page, then info, xmp, objstm, xref.
  let fontBase := 3
  let type0Id (k : Nat) := fontBase + 4 * k
  let cidId (k : Nat) := fontBase + 4 * k + 1
  let fdId (k : Nat) := fontBase + 4 * k + 2
  let toUniId (k : Nat) := fontBase + 4 * k + 3
  let fileBase := fontBase + 4 * nf
  let fileId (k : Nat) := fileBase + k
  let imgBase := fileBase + nf
  let (imgIds, smaskIds, pageBase) : Array Nat × Array (Option Nat) × Nat := Id.run do
    let mut ids : Array Nat := #[]
    let mut masks : Array (Option Nat) := #[]
    let mut next := imgBase
    for k in usedImgs do
      ids := ids.push next
      next := next + 1
      match (imgs.get? k).bind (·.info) with
      | some inf =>
        if inf.smask.isEmpty then
          masks := masks.push none
        else
          masks := masks.push (some next)
          next := next + 1
      | none => masks := masks.push none
    return (ids, masks, next)
  let imgId (n : Nat) := imgIds[n]?.getD 0
  let pageId (i : Nat) := pageBase + 2 * i
  let contentId (i : Nat) := pageBase + 2 * i + 1
  let infoId := pageBase + 2 * np
  -- The document outline (ISO 32000-2 §12.3.3), when the layout carried
  -- one: a root plus one item per entry, flat, in document order. With no
  -- entries nothing is emitted and every object id below is unchanged —
  -- an outline-free document stays byte-identical.
  let nOut := outline.size
  let outlineRootId := infoId + 1
  let outlineItemId (k : Nat) := infoId + 2 + k
  let xmpId := if nOut == 0 then infoId + 1 else infoId + 2 + nOut
  let objStmId := xmpId + 1
  let xrefId := objStmId + 1
  let size := xrefId + 1

  -- compressed (non-stream) objects, serialized bare
  let kids := String.intercalate " " ((List.range np).map fun i => s!"{pageId i} 0 R")
  let outlinesRef := if nOut == 0 then "" else s!" /Outlines {outlineRootId} 0 R"
  -- The catalog: `catalogDict`, whose `/Lang` is `pdf_lang_declared`'s
  -- statement — present exactly when the document declares a language.
  let catalog := catalogDict outlinesRef xmpId info.language
  let pagesObj := s!"<< /Type /Pages /Kids [{kids}] /Count {np} >>"
  let fontResources := String.intercalate " "
    ((List.range nf).map fun k => s!"/F{k + 1} {type0Id k} 0 R")
  let fontObjs : List (Nat × String) := (List.range nf).flatMap fun k =>
    let font := fs.get keep[k]!
    let used := usedPerFont[k]!
    let baseFont := pdfName font.psName
    let ascent1000 := font.ascent * 1000 / font.unitsPerEm
    let descent1000 := font.descent * 1000 / font.unitsPerEm
    -- The descriptor states the parsed metrics, not stand-ins: CapHeight is
    -- the face's own (OS/2 sCapHeight through `Font.capHeight` — `ascent`
    -- once stood in for it), and ItalicAngle is the slant the face declares
    -- (post.italicAngle); only a face flagged italic that declares none
    -- keeps the conventional -12°.
    let capHeight1000 := font.capHeight * 1000 / font.unitsPerEm
    let cidSubtype := if font.isCff then "CIDFontType0" else "CIDFontType2"
    let cidToGid := if font.isCff then "" else " /CIDToGIDMap /Identity"
    let fontFileKey := if font.isCff then "FontFile3" else "FontFile2"
    let italicAngle := if font.italicAngle == 0 && font.isItalic then -12
      else font.italicAngle
    -- Flags: bit 1 fixed pitch, bit 3 symbolic, bit 7 italic (1-based).
    let flags := 4 + (if font.isFixedPitch then 1 else 0) + (if font.isItalic then 64 else 0)
    -- StemV and the FontBBox x-bounds are conventional stand-ins, said so:
    -- an unhinted OpenType face declares neither (a stem width lives in
    -- hinting data the parser does not keep), so these are the trade's
    -- usual values, not measurements.
    let stemV := if font.isBold then 140 else 80
    [(type0Id k,
      s!"<< /Type /Font /Subtype /Type0 /BaseFont /{baseFont} /Encoding /Identity-H /DescendantFonts [{cidId k} 0 R] /ToUnicode {toUniId k} 0 R >>"),
     (cidId k,
      s!"<< /Type /Font /Subtype /{cidSubtype} /BaseFont /{baseFont} /CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >> /FontDescriptor {fdId k} 0 R /DW 1000 /W {wArray font used}{cidToGid} >>"),
     (fdId k,
      s!"<< /Type /FontDescriptor /FontName /{baseFont} /Flags {flags} /FontBBox [-1000 {descent1000} 2000 {ascent1000}] /ItalicAngle {italicAngle} /Ascent {ascent1000} /Descent {descent1000} /CapHeight {capHeight1000} /StemV {stemV} /{fontFileKey} {fileId k} 0 R >>")]
  let annots (i : Nat) : String :=
    let rects := linkRects geom pages[i]!
    if rects.isEmpty then "" else
      let entries := rects.toList.map fun (x0, y0, x1, y1, url) =>
        s!"<< /Type /Annot /Subtype /Link /Rect [{x0.toPtString} {y0.toPtString} " ++
        s!"{x1.toPtString} {y1.toPtString}] /Border [0 0 0] /F 4 " ++
        s!"/A << /S /URI /URI ({pdfString url}) >> >>"
      " /Annots [" ++ String.intercalate " " entries ++ "]"
  let pageDict (i : Nat) :=
    -- With bleed the medium is larger than the finished page, and the
    -- boxes follow from the declared trim size and bleed (`pageBoxes`,
    -- nesting proved by `pageBoxes_nest`) — the file itself tells
    -- prepress where to cut, no hand-rolled \pdfvariable pageattr needed.
    -- With zero bleed nothing is written: CropBox defaults to MediaBox
    -- and BleedBox/TrimBox/ArtBox default to CropBox (ISO 32000-2
    -- §14.11.2), so an empty dictionary already declares all boxes equal
    -- — and the zero-bleed output stays byte-identical.
    let b := geom.bleed
    let (media, bleedBox, trim) := pageBoxes geom.pageW geom.pageH b
    let boxes := if b == 0 then "" else
      s!" /TrimBox {trim.render} /BleedBox {bleedBox.render} /ArtBox {trim.render}"
    let xobj := if ni == 0 then "" else
      " /XObject << " ++ String.intercalate " "
        ((List.range ni).map fun n => s!"/Im{n + 1} {imgId n} 0 R") ++ " >>"
    s!"<< /Type /Page /Parent 2 0 R /MediaBox {media.render}{boxes} /Resources << /Font << {fontResources} >>{xobj} >>{annots i} /Contents {contentId i} 0 R >>"
  -- Metadata is a *text string* (§7.9.2.2): ASCII literal, or UTF-16BE
  -- with the BOM past ASCII — never raw UTF-8 bytes, which a reader
  -- decodes as PDFDocEncoding.
  let infoEntry (key : String) (v : Option String) : String :=
    match v with
    | some s => s!" /{key} {pdfTextString s}"
    | none => ""
  let infoDict :=
    "<<" ++ infoEntry "Title" info.title ++ infoEntry "Author" info.author ++
    infoEntry "Subject" info.subject ++ infoEntry "Keywords" info.keywords ++
    s!" /Producer (leantex) >>"

  -- Outline items: /Title and /Parent always; a resolved in-document
  -- target is a /Dest to its page (/XYZ null null null keeps the reader's
  -- view), an external target a URI action, and a target that resolved to
  -- neither is a bare item — an outline item need carry no destination.
  let outlineObjs : List (Nat × String) :=
    if nOut == 0 then [] else
      (outlineRootId,
        s!"<< /Type /Outlines /First {outlineItemId 0} 0 R /Last {outlineItemId (nOut - 1)} 0 R /Count {nOut} >>") ::
      outline.toList.zipIdx.map fun (e, k) =>
        let prev := if k == 0 then "" else s!" /Prev {outlineItemId (k - 1)} 0 R"
        let next := if k + 1 == nOut then "" else s!" /Next {outlineItemId (k + 1)} 0 R"
        let target := match e.page, e.url with
          | some p, _ => s!" /Dest [{pageId p} 0 R /XYZ null null null]"
          | none, some u => s!" /A << /S /URI /URI ({pdfString u}) >>"
          | none, none => ""
        (outlineItemId k,
          s!"<< /Title {pdfTextString e.title} /Parent {outlineRootId} 0 R{prev}{next}{target} >>")
  let compressed : List (Nat × String) :=
    [(1, catalog), (2, pagesObj)] ++ fontObjs ++ [(infoId, infoDict)] ++ outlineObjs ++
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
    let data := (contentStream geom remap imgMap pages[i]!).toUTF8
    let (w', off) := putStream w (contentId i) "" data
    w := w'
    locs := locs.set! (contentId i) (1, off)

  -- Image XObjects. A PNG's raw IDAT stream passes through as
  -- `/FlateDecode` with the PNG predictor declared (ISO 32000-2 §7.4.4.4:
  -- Predictor 15, with Colors/BitsPerComponent/Columns describing the
  -- scanlines); a decoded-and-re-encoded plane needs no predictor; a JPEG
  -- embeds whole as `/DCTDecode`. An alpha plane rides as its own gray
  -- XObject named by `/SMask`.
  for (k, n) in usedImgs.zipIdx do
    if let some inf := (imgs.get? k).bind (·.info) then
      let colorSpace := match inf.space with
        | .gray => "/DeviceGray"
        | .rgb => "/DeviceRGB"
        | .indexed => Id.run do
          let mut hex := ""
          for byte in inf.palette do
            hex := hex.push (hexDigit (byte.toNat / 16))
            hex := hex.push (hexDigit byte.toNat)
          return s!"[/Indexed /DeviceRGB {inf.palette.size / 3 - 1} <{hex}>]"
      let filter := match inf.format with
        | .png =>
          if inf.predictor then
            s!"/Filter /FlateDecode /DecodeParms << /Predictor 15 \
/Colors {inf.space.components} /BitsPerComponent {inf.bitDepth} /Columns {inf.pxW} >>"
          else "/Filter /FlateDecode"
        | .jpeg => "/Filter /DCTDecode"
      let smaskRef := match smaskIds[n]?.getD none with
        | some mid => s!" /SMask {mid} 0 R"
        | none => ""
      let dict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace {colorSpace} /BitsPerComponent {inf.bitDepth}\
{smaskRef} {filter}"
      let (w', off) := putStream w (imgId n) dict inf.data
      w := w'
      locs := locs.set! (imgId n) (1, off)
      if let some mid := smaskIds[n]?.getD none then
        let mdict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace /DeviceGray /BitsPerComponent 8 /Filter /FlateDecode"
        let (w'', moff) := putStream w mid mdict inf.smask
        w := w''
        locs := locs.set! mid (1, moff)

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
