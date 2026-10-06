import LeanTex.Core.Dim
import LeanTex.Core.Flate
import LeanTex.Core.Font
import LeanTex.Core.FontSubset
import LeanTex.Core.HtmlDoc
import LeanTex.Core.Layout
import LeanTex.Core.PdfContent
import LeanTex.Core.PdfStruct
import LeanTex.Core.PdfXref

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Layout

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

/-- A length in points as an object: an integer when its rounded spelling
is one, a real otherwise. The distinction is the reader's — `parseVal`
answers `.int` for a dotless number — so a writer that spelled every
length `.real` would build a value its own reader never returns, and
`parseVal_render_id` would be false of it. -/
def ptObj (x : Sp) : PdfRead.Obj :=
  let milli := (x.natAbs * 1000 + 32768) / 65536
  if milli % 1000 == 0 then
    .int (if x < 0 then -(milli / 1000 : Int) else (milli / 1000 : Int))
  else .real x.toPtString

/-- The page box as an object — the four corners, each `ptObj`. -/
def Rect.obj (r : Rect) : PdfRead.Obj :=
  .arr #[ptObj r.x0, ptObj r.y0, ptObj r.x1, ptObj r.y1]

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

/-- The PDF 1.7 standard structure type a 2.0-only type is role-mapped
onto, in a file declared PDF 1.7 (ISO 32000-1 §14.8.4 is 1.7's standard
set; ISO 32000-2 §14.8.6 adds the others): a document title stands as a
paragraph, a footnote as a `Note`, an aside as a `Div`, and a heading past
the sixth level as `H6`. Every other type the engine writes is standard
in both. -/
def pdf17Role (s : String) : Option String :=
  if s == "Title" then some "P"
  else if s == "FENote" then some "Note"
  else if s == "Aside" then some "Div"
  else if s.startsWith "H" && ((s.drop 1).toString.toNat?.any (6 < ·)) then some "H6"
  else none

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

/-- A rational `p / q` (`q > 0`) as a decimal, rounded once at the ninth
digit: the precision a form's `/Matrix` needs — its scale entries are the
reciprocal of a page box in points, and one rounding at 1e-9 lands the
placed corner within a nanometre of `form_bbox_exact`'s rational. -/
private def ratString (p q : Int) : String :=
  let neg := p < 0
  let v := (p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs
  let ip := v / 1000000000
  let fr := v % 1000000000
  let sign := if neg && v != 0 then "-" else ""
  if fr == 0 then
    s!"{sign}{ip}"
  else
    let frs := toString fr
    let frs := ("".pushn '0' (9 - frs.length)) ++ frs
    let frs := (frs.dropEndWhile (· == '0')).toString
    s!"{sign}{ip}.{frs}"

/-- A PDF string object from a spelling that already carries its
delimiters (`(text)` or `<hex>`) — what `pdfTextString` and `pdfString`
produce, kept verbatim as `Obj.str` does. -/
private def litObj (s : String) : PdfRead.Obj := .str s.toUTF8

/-- Copied-graph chunks rendered against the writer's numbering: each hole
is `base + local`, and `resources_closed` is what makes every hole point
at an object this file writes. -/
private def renderChunks (base : Nat) (cs : Array PdfRead.Chunk) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for c in cs do
    match c with
    | .bytes bs => out := out ++ bs
    | .ref l => out := out ++ (s!"{base + l} 0 R").toUTF8
  return out

/-- Every face's used glyphs in one walk over the pages: per face, a mark
per glyph id holding the first char witness — the glyph stream is large
(every glyph on every page), so marks, never a sort, and one walk for all
the faces, never one walk a face. -/
private def markUsed (fs : FontSet) (pages : Array PageOut) : Array (Array (Option Char)) :=
  Id.run do
  let mut seen : Array (Array (Option Char)) :=
    fs.fonts.map fun f => Array.replicate f.numGlyphs none
  for p in pages do
    for l in p.lines do
      for s in l.segs do
        if let .run idx _ _ _ glyphs _ _ _ _ _ _ := s then
          seen := seen.modify idx fun marks => Id.run do
            let mut marks := marks
            for (g, c, _) in glyphs do
              if h : g < marks.size then
                if marks[g].isNone then
                  marks := marks.set g (some c)
            return marks
  return seen

/-- Used glyphs per face, one char witness per gid, ascending gid: the
census a PDF build's embedding decisions read — the faces the file keeps
(`keepFaces`, its `keepOf`), their subset programs (`facePrograms`), and
the writer's own tables. The driver takes it once for the programs, their
cache keys and the page operators; `write` takes its own. -/
def usedAll (fs : FontSet) (pages : Array PageOut) : Array (Array (Nat × Char)) :=
  let seen := markUsed fs pages
  (Array.range fs.fonts.size).map fun k =>
    ((seen[k]?.getD #[]).zipIdx.filterMap fun (c?, g) => c?.map (g, ·))

private theorem usedAll_size_exact (fs : FontSet) (pages : Array PageOut) :
    (usedAll fs pages).size = fs.fonts.size := by
  simp [usedAll]

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
  keepOf (usedAll fs pages)

/-- The font program `write` embeds for each face the census `used`
(`usedAll`) keeps, in `keepOf` order: the face's own file minus every glyph
its pages do not paint (`FontSubset.program`), and whether it is a subset.
The driver builds it once, deflates it through its cache (`FontSet.zdata`),
and hands it to `write`. -/
def facePrograms (fs : FontSet) (used : Array (Array (Nat × Char))) : Array (ByteArray × Bool) :=
  (keepOf used).map fun k =>
    let f := fs.get k
    FontSubset.program f ((used[k]?.getD #[]).map (·.1))

/-- A subset's tag (ISO 32000-2 §9.6.4): six capitals, the first two the
face's slot in the file, so no two subsets in one file share a tag, and the
rest a digest of the glyphs it keeps, so one subset is always spelled the
same. -/
def subsetTag (k : Nat) (used : Array Nat) : String :=
  let h := used.foldl (fun h g => (h * 31 + g + 1) % 456976) 7
  let v := k % 676 * 456976 + h
  String.ofList ((List.range 6).reverse.map fun i => Char.ofNat (65 + v / 26 ^ i % 26))

theorem keepFaces_lt (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) : ∀ k ∈ keepFaces fs pages, k < fs.fonts.size := by
  intro k hk
  unfold keepFaces keepOf at hk
  dsimp only at hk
  rw [usedAll_size_exact] at hk
  split at hk
  · simp only [Array.mem_singleton] at hk
    omega
  · have := (Array.mem_filter.mp hk).1
    simpa using this

/-- What this writer realizes of the output contract, as values the driver
holds against the document's declaration (`Ir.OutputContract.unmet`): no
alternative channel until the file is tagged, device colour with no output
intent, faces embedded (`keepFaces`), no script, mathematics as placed
glyphs. Nothing in `write` reads this record; it describes the bytes, it
does not shape them. -/
def profile : Ir.Realization :=
  { alternatives := .none
    color := .device
    fonts := .embeds
    scripting := .never
    math := .layout }

/-- The undeclared contract is met by this writer (`_exact`): a document
that declares no contract key gets no W0701 from its PDF. -/
theorem pdf_default_contract_exact : ({} : Ir.OutputContract).unmet profile = #[] := by
  decide

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

/-- **Both artifacts' kerning request is one record's two projections**
(`_agree`). `HtmlDoc.kernCssFor` emits the browser request and
`Layout.kernEnabled` gates every pair and space-pair lookup. The live
stylesheet and all three layout call sites pass `Ir.features` itself, so a
caller cannot substitute a detached literal at one backend. Quantifying the
record keeps the statement meaningful when a document-level feature switch
reaches the resolving site. -/
theorem features_agree (features : Ir.Features) :
    (!(HtmlDoc.kernCssFor features).isEmpty) = Layout.kernEnabled features := by
  cases features with
  | mk kern => cases kern <;> simp [HtmlDoc.kernCssFor, Layout.kernEnabled]

/-- **Both artifacts size a picture by one IR box** (`_agree`). The PDF
reserves and places a picture by `Layout.pictureBox`, and the SVG's
`viewBox` is `HtmlDoc.pictureBoxOf` (`HtmlDoc.pictureViewBox_projects`);
under the measurement the driver hands both — `Layout.labelMetric` over the
one face set, the x-height the layout resolves — the two are the one value
`Ir.Pic.Picture.box`: the declared box exactly (`box_declared_exact`), else
every mark's ink and every node's border (`box_covers`). Before, the SVG
read the hull of label *anchors* while the page read the ink, so one
picture had two sizes. -/
theorem picture_box_agree (geom : Layout.Geom) (fs : FontSet) (pic : Ir.Pic.Picture) :
    Layout.pictureBox geom fs {} (fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm) pic =
      HtmlDoc.pictureBoxOf { labelMetric := Layout.labelMetric geom fs } pic := rfl

/-- **The two artifacts carry one text for a non-text object** (`_agree`):
whatever text a `Figure` carries as `/Alt` (`altElem`, the PDF's projection
of the object's `Ir.Alt`), the HTML names the object by that same text — an
svg's `aria-label`, an img's `alt` — because both project the one value
(for a picture, `Ir.Pic.Picture.alternative`: the author's words, else its
labels'). -/
theorem alt_text_agree (floor : String) (a : Ir.Alt) (t : String)
    (ht : HtmlDoc.nonBlank t = true)
    (h : (altElem #[rootElem] 0 0 a).back?.bind (·.alt) = some t) :
    HtmlDoc.attrOf? (HtmlDoc.pictureAltAttrs floor a) "aria-label" = some t ∧
      HtmlDoc.attrOf? (HtmlDoc.imgAltAttrs a) "alt" = some t := by
  cases a with
  | described s =>
    simp [altElem, pushElem, figureElem] at h
    subst h
    simp [HtmlDoc.pictureAltAttrs, HtmlDoc.imgAltAttrs, HtmlDoc.attrOf?, HtmlDoc.firstNonBlank, ht]
  | undeclared => simp [altElem, pushElem, figureElem] at h
  | decorative => simp [altElem, rootElem] at h

/-- **The two artifacts hide the same objects** (`_agree`): the PDF adds no
element for a non-text object — its ink an artifact — exactly when the HTML
takes its svg out of the accessibility tree. -/
theorem alt_hidden_agree (floor : String) (a : Ir.Alt) :
    (altElem #[rootElem] 0 0 a).size = 1 ↔
      HtmlDoc.attrOf? (HtmlDoc.pictureAltAttrs floor a) "aria-hidden" = some "true" := by
  cases a <;> simp [altElem, pushElem, HtmlDoc.pictureAltAttrs, HtmlDoc.attrOf?]

/-- **Both artifacts' font decisions are projections of one policy value**
(`_projects`). `Doc.fontPolicy` is the one resolving site; the driver's
`shipFonts` is the spelling `doc.fontPolicy == .embedded`, and the HTML's
shipment is `shipFaces` under it and nothing otherwise — the `if` here is
that gate, written out. Under `.embedded` the shipment covers every face
this writer embeds (`html_fonts_cover_pdf` is the body); under `.none` the
document declared that its stylesheet owns the faces, and the PDF still
embeds its own, as `profile.fonts = .embeds` records. -/
theorem fontPolicy_projects (doc : Ir.Doc) (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) (hp : doc.fontPolicy == .embedded) :
    ∀ k ∈ keepFaces fs pages,
      ∃ ff ∈ (if doc.fontPolicy == .embedded then HtmlDoc.shipFaces fs else #[]),
        ff.index = k := by
  rw [ite_eq_left hp]
  exact html_fonts_cover_pdf fs pages h

/-- Link rectangles for one page, in PDF user space. Block links arrive
as one placed rectangle over their whole page segment; adjacent inline runs
with the same destination still merge per line. -/
private def linkRects (geom : Geom) (page : PageOut) :
    Array (Sp × Sp × Sp × Sp × String) := Id.run do
  let mut out : Array (Sp × Sp × Sp × Sp × String) := page.links.map fun r =>
    (geom.bleed + r.x, geom.bleed + geom.pageH - r.y - r.h,
      geom.bleed + r.x + r.w, geom.bleed + geom.pageH - r.y, r.target)
  for l in page.lines do
    let mut x := geom.bleed + l.x
    -- Merge tolerance of one em: a run separated only by an interword space
    -- joins the previous rectangle, so a multi-word link is one annotation.
    let pad := l.size
    for seg in l.segs do
      match seg with
      | .run _ _ link w _ segSize _ _ _ _ _ =>
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
      | .gap w _ | .decoratedGap w _ _ => x := x + w
      | .rule w _ _ _ | .decoration _ w _ _ _ => x := x + w
      | .image _ w _ => x := x + w
      | .poly _ _ => pure ()
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

/-- A `/W` width in millionths of the em as the number the file spells:
thousandths, with up to three decimals — an integer when it is one. -/
def widthObj (μ : Int) : PdfRead.Obj :=
  if μ % 1000 == 0 then .int (μ / 1000) else
    let frs := toString (μ.natAbs % 1000)
    let frs := (("".pushn '0' (3 - frs.length)) ++ frs).dropEndWhile (· == '0')
    .real s!"{μ / 1000}.{frs}"

/-- The `/W` array: each used glyph's advance (§9.7.4.3), `pdfWidthμ` as
`widthObj` spells it — the width the pen model advances by — as a typed
object; `Obj.render` decides its bytes. -/
private def wArray (font : Font) (used : Array (Nat × Char)) : PdfRead.Obj :=
  .arr (used.flatMap fun (g, _) => #[PdfRead.Obj.int g, .arr #[widthObj (pdfWidthμ font g)]])

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

/-- The catalog's language entry: `/Lang` from the declared tag — the
document's main language over every text run that carries no finer mark
(ISO 32000-2 §14.9.2.2; BCP 47) — and nothing when the document declares
none. The same `Ir.Meta` field the HTML root's `lang` attribute reads
(`HtmlDoc.emit_lang_declared`). -/
def langEntry : Option String → Array (String × PdfRead.Obj)
  | some tag => #[("Lang", .str s!"({pdfString tag})".toUTF8)]
  | none => #[]

/-- The catalog's tagging entries: `/MarkInfo << /Marked true >>` (§14.7.1
— the file's content is marked) and the structure tree root. Present
unconditionally: every PDF this writer ships is tagged, whatever the
document declares — tagging is a fact of the artifact, the profile claim
(`pdfuaid`) is a separate, withheld statement. -/
def markedEntry (structTreeRoot : Nat) : Array (String × PdfRead.Obj) :=
  #[("MarkInfo", .dict #[("Marked", .bool true)]), ("StructTreeRoot", .ref structTreeRoot 0)]

/-- `/ViewerPreferences /DisplayDocTitle`: the reader's window titles from
the document's own metadata title rather than its file name (§12.2;
PDF/UA requires it). -/
def viewerEntry : Array (String × PdfRead.Obj) :=
  #[("ViewerPreferences", .dict #[("DisplayDocTitle", .bool true)])]

/-- The document catalog (ISO 32000-2 §7.7.2): the page tree, an outline
when the layout carried one, the XMP metadata stream, the declared
language, the mark information and structure tree root, and the viewer
preference. A typed object, not a spelling: `Obj.render` is the only place
its bytes are decided. -/
def catalogDict (outlineRoot : Option Nat) (xmpId : Nat) (lang : Option String)
    (structTreeRoot : Nat) : PdfRead.Obj :=
  .dict (#[("Type", .name "Catalog"), ("Pages", .ref 2 0)]
    ++ (match outlineRoot with
        | some r => #[("Outlines", PdfRead.Obj.ref r 0)]
        | none => #[])
    ++ #[("Metadata", .ref xmpId 0)]
    ++ langEntry lang ++ markedEntry structTreeRoot ++ viewerEntry)

/-- The PDF twin of `emit_lang_declared`: the catalog's entries carry the
language entry of the document's declared tag between two fixed runs, by
construction — so `/Lang` appears exactly when the document declares a
language, reading the same `Ir.Meta` field as the HTML root's `lang`. A
statement over the typed entries rather than a substring of a spelling:
the value is what both the writer and a reader see. The webMetaChecks
census in Tests/Backends is the wiring witness that `write` ships this
dictionary. -/
theorem pdf_lang_declared (outlineRoot : Option Nat) (xmpId : Nat) (lang : Option String)
    (structTreeRoot : Nat) :
    ∃ pre post, catalogDict outlineRoot xmpId lang structTreeRoot
      = .dict (pre ++ langEntry lang ++ post) :=
  ⟨#[("Type", .name "Catalog"), ("Pages", .ref 2 0)]
    ++ (match outlineRoot with
        | some r => #[("Outlines", PdfRead.Obj.ref r 0)]
        | none => #[])
    ++ #[("Metadata", .ref xmpId 0)],
   markedEntry structTreeRoot ++ viewerEntry, by
    simp only [catalogDict, Array.append_assoc]⟩

/-- **`pdf_marked_declared`** (the `pdf_lang_declared` shape): the catalog
carries `/MarkInfo << /Marked true >>` and `/StructTreeRoot` between two
fixed runs, whatever the language, the outline, or the document declares
— tagging is unconditional. The structTreeChecks round trip in
Tests/Backends is the wiring witness that `write` ships this dictionary
with a tree behind the reference. -/
theorem pdf_marked_declared (outlineRoot : Option Nat) (xmpId : Nat) (lang : Option String)
    (structTreeRoot : Nat) :
    ∃ pre post, catalogDict outlineRoot xmpId lang structTreeRoot
      = .dict (pre ++ markedEntry structTreeRoot ++ post) :=
  ⟨#[("Type", .name "Catalog"), ("Pages", .ref 2 0)]
    ++ (match outlineRoot with
        | some r => #[("Outlines", PdfRead.Obj.ref r 0)]
        | none => #[])
    ++ #[("Metadata", .ref xmpId 0)] ++ langEntry lang,
   viewerEntry, by
    simp only [catalogDict, Array.append_assoc]⟩

/-- Face index → resource number, over the faces `keepFaces` embeds. -/
private def remapOf (fs : FontSet) (keep : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate fs.fonts.size 0
  for (old, new) in keep.zipIdx do
    r := r.set! old new
  return r

/-- Images actually placed and loaded become XObjects, one per file however
often it is placed; a placeholder is drawn inline and needs no object. -/
private def usedImagesOf (imgs : Image.Store) (pages : Array PageOut) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for p in pages do
    for l in p.lines do
      for s in l.segs do
        if let .image (some k) _ _ := s then
          if ((imgs.get? k).bind (·.info)).isSome && !out.contains k then
            out := out.push k
  return out

/-- Image index → XObject number, over `usedImagesOf`. -/
private def imgMapOf (imgs : Image.Store) (used : Array Nat) : Array (Option Nat) := Id.run do
  let mut m : Array (Option Nat) := Array.replicate imgs.entries.size none
  for (k, n) in used.zipIdx do
    m := m.set! k (some n)
  return m

/-- The structure type each leaf's marked content is tagged with, read off
the tree's skeleton (`leafTags`): the one answer both the content streams
and the structure elements are built from. -/
def tagsOf (tree : Struct.Tree) : Array (Option String) :=
  leafTags (skeleton tree) tree.leaves.size

/-- Each page's typed operators, resolved against the faces and images the
document actually uses and the structure tree's leaf tags: what
`pageStreams` renders, before spelling. `keep` is `keepFaces` over these
pages, read by the driver off the census it took once. -/
def pageOps (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store := {}) (tree : Struct.Tree := ⟨#[]⟩)
    (keep : Array Nat := keepFaces fs pages) : Array (Array ContentOp) :=
  let remap := remapOf fs keep
  let imgMap := imgMapOf imgs (usedImagesOf imgs pages)
  let tags := tagsOf tree
  let wt := widthTable fs.fonts keep
  pages.map (contentOps geom remap wt imgMap tags)

/-- The per-page content streams `write` embeds, uncompressed: the same
bytes `write` computes for itself, exposed so the driver can deflate them
through its content-hash cache (the font files' shape — a page whose
content is unchanged since the last build reads its stream instead of
compressing it) and hand them back as `write`'s `streams`. -/
def pageStreams (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store := {}) (tree : Struct.Tree := ⟨#[]⟩) : Array ByteArray :=
  (pageOps geom fs pages imgs tree).map fun ops => (render ops).toUTF8

-- ## The object table

/-- What the cross-reference row of one object id says (ISO 32000-2
§7.5.8.3, Table 18): the object is written at a byte offset (type 1), sits
at an index inside the object stream (type 2), or is the cross-reference
stream itself — type 1 too, at the offset the trailer's `startxref` names. -/
inductive ObjKind where
  | direct
  | inStream (idx : Nat)
  | xref
  deriving Repr, BEq

/-- What a placed image brings beyond its own XObject: nothing, an alpha
plane's SMask, or a copied page's resource graph — one id per object. -/
inductive ImgExtra where
  | plain
  | alpha
  | form (objects : Nat)
  deriving Repr

/-- How many ids an image's block spans: its XObject plus what it brings. -/
def ImgExtra.span : ImgExtra → Nat
  | .plain => 1
  | .alpha => 2
  | .form n => n + 1

/-- What image `k` of the store brings: a decoded page is a form, a raster
with an alpha plane brings its SMask, anything else (a placeholder too)
nothing. -/
def imgExtraOf (imgs : Image.Store) (k : Nat) : ImgExtra :=
  match (imgs.get? k).bind (·.info) with
  | some inf =>
    match inf.form with
    | some f => .form f.val.objects.size
    | none =>
      match inf.alpha with
      | .soft _ _ => .alpha
      | .opaque => .plain
      | .colorKey _ => .plain
  | none => .plain

/-- Where each of a run of consecutive blocks starts: `base`, then each
start plus its own block's span. -/
def blockStarts (base : Nat) : List Nat → List Nat
  | [] => []
  | n :: ns => base :: blockStarts (base + n) ns

/-- Every object id one file allocates, computed once from the counts that
decide it, in id order: 1 the catalog, 2 the page tree, four ids per kept
face and then one file per face, per placed image its XObject followed by
what it brings (`ImgExtra`), two per page, Info, the outline — root then
items — when the layout carried one, XMP, the object stream, and the
cross-reference stream last. `write` reads its ids here and nowhere else;
the conditional families are slots no document fills yet. -/
structure ObjTable where
  nf : Nat
  ni : Nat
  np : Nat
  nOut : Nat
  imgIds : Array Nat
  /-- Per image, the ids its block spans: its XObject plus what it brings. -/
  imgSpans : Array Nat
  smaskIds : Array (Option Nat)
  formBases : Array (Option Nat)
  /-- Objects a copied graph brings (0 when the image is not a form). -/
  formSizes : Array Nat
  pageBase : Nat
  infoId : Nat
  outlineRootId : Nat
  xmpId : Nat
  objStmId : Nat
  xrefId : Nat
  size : Nat
  /-- OutputIntent and its ICC stream: filled by the colour plan. -/
  outputIntent : Option Nat := none
  icc : Option Nat := none
  /-- The structure block, after the outline: the structure tree root, its
  parent tree, the one PDF 2.0 namespace dictionary, then one object per
  structure element from `structBase` — every PDF is tagged, so the block
  is unconditional (empty of elements only for a tree with no root, which
  `skeleton` never yields). -/
  nElems : Nat
  structTreeRoot : Nat
  parentTree : Nat
  namespaceId : Nat
  structBase : Nat
  deriving Repr

namespace ObjTable

def type0Id (k : Nat) : Nat := 3 + 4 * k
def cidId (k : Nat) : Nat := 3 + 4 * k + 1
def fdId (k : Nat) : Nat := 3 + 4 * k + 2
def toUniId (k : Nat) : Nat := 3 + 4 * k + 3
def fileId (t : ObjTable) (k : Nat) : Nat := 3 + 4 * t.nf + k
def pageId (t : ObjTable) (i : Nat) : Nat := t.pageBase + 2 * i
def contentId (t : ObjTable) (i : Nat) : Nat := t.pageBase + 2 * i + 1
def outlineItemId (t : ObjTable) (k : Nat) : Nat := t.infoId + 2 + k
def structElemId (t : ObjTable) (k : Nat) : Nat := t.structBase + k

/-- Every allocated id, in emission order — each block spelled from its
own slot function, so `objTable_inj` and `objTable_covers` are facts about
the allocation and not about a range. -/
def ids (t : ObjTable) : Array Nat :=
  #[1, 2]
  ++ (Array.range t.nf).flatMap (fun k => #[type0Id k, cidId k, fdId k, toUniId k])
  ++ (Array.range t.nf).map t.fileId
  ++ (t.imgIds.zip t.imgSpans).flatMap (fun (id, n) => Array.range' id n)
  ++ (Array.range t.np).flatMap (fun i => #[t.pageId i, t.contentId i])
  ++ #[t.infoId]
  ++ (if t.nOut == 0 then #[]
      else #[t.outlineRootId] ++ (Array.range t.nOut).map t.outlineItemId)
  ++ #[t.structTreeRoot, t.parentTree, t.namespaceId]
  ++ (Array.range t.nElems).map t.structElemId
  ++ #[t.xmpId, t.objStmId, t.xrefId]

/-- The cross-reference row kind of an id, given where the object stream
holds it (`compressedIdx`): a function of the table, so an id the table
never allocated is `none` — and `objTable_kindOf_some` says that never
happens on `ids`. -/
def kindOf (t : ObjTable) (compressedIdx : Nat → Option Nat) (id : Nat) : Option ObjKind :=
  if id == 0 || t.size ≤ id then none
  else if id == t.xrefId then some .xref
  else match compressedIdx id with
    | some idx => some (.inStream idx)
    | none => some .direct

end ObjTable

/-- The table for `keep` faces, the placed images `usedImgs` of `imgs`,
`np` pages, `nOut` outline entries and `nElems` structure elements. -/
def objTable (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems : Nat) : ObjTable :=
  let nf := keep.size
  let extras := usedImgs.map (imgExtraOf imgs)
  let spans := extras.map ImgExtra.span
  let imgIds := (blockStarts (3 + 5 * nf) spans.toList).toArray
  let pageBase := 3 + 5 * nf + spans.toList.sum
  let infoId := pageBase + 2 * np
  let structTreeRoot := if nOut == 0 then infoId + 1 else infoId + 2 + nOut
  let xmpId := structTreeRoot + 3 + nElems
  { nf, ni := usedImgs.size, np, nOut, imgIds, imgSpans := spans
    smaskIds := (imgIds.zip extras).map fun (id, e) => match e with
      | .alpha => some (id + 1)
      | .plain => none
      | .form _ => none
    formBases := (imgIds.zip extras).map fun (id, e) => match e with
      | .form _ => some (id + 1)
      | .plain => none
      | .alpha => none
    formSizes := extras.map fun e => match e with
      | .form n => n
      | .plain => 0
      | .alpha => 0
    pageBase, infoId, outlineRootId := infoId + 1, xmpId
    objStmId := xmpId + 1, xrefId := xmpId + 2, size := xmpId + 3
    nElems, structTreeRoot, parentTree := structTreeRoot + 1, namespaceId := structTreeRoot + 2
    structBase := structTreeRoot + 3 }

/-- The table `write` reads for these inputs: the faces it embeds
(`keepFaces`), the images it places (`usedImagesOf`), the page and outline
counts, and the structure tree's element count. -/
def tableOf (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store)
    (outline : Array OutlineEntry) (tree : Struct.Tree := ⟨#[]⟩) : ObjTable :=
  objTable (keepFaces fs pages) imgs (usedImagesOf imgs pages) pages.size outline.size
    (skeleton tree).size

/-- **`blockIds_exact`**: consecutive blocks laid out by `blockStarts` tile
the range from `base` of the spans' total, exactly. -/
theorem blockIds_exact (base : Nat) (spans : List Nat) :
    ((blockStarts base spans).zip spans).flatMap (fun p => List.range' p.1 p.2)
      = List.range' base spans.sum := by
  induction spans generalizing base with
  | nil => simp [blockStarts]
  | cons n ns ih =>
    rw [blockStarts, List.zip_cons_cons, List.flatMap_cons, ih, List.sum_cons]
    have := @List.range'_append base n ns.sum 1
    simp only [Nat.one_mul] at this
    rw [this]

/-- Constant-size blocks over `range n` tile `range' a (c * n)`. -/
theorem flatMap_range_exact (a c n : Nat) (f : Nat → List Nat)
    (hf : ∀ k, f k = List.range' (a + c * k) c) :
    (List.range n).flatMap f = List.range' a (c * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, hf]
    have := @List.range'_append a (c * n) c 1
    simp only [Nat.one_mul] at this
    rw [this, Nat.mul_succ]

/-- **`ObjTable.ids_exact`**: a table whose fields stand in the relations
`objTable` writes has ids that tile `[1, size)` — each block, spelled from
its slot function, is a range, and the ranges abut. Stated over the fields
so the proof never sees the structure literal. -/
theorem ObjTable.ids_exact (t : ObjTable) (spans : List Nat)
    (himg : t.imgIds.toList = blockStarts (3 + 5 * t.nf) spans)
    (hsp : t.imgSpans.toList = spans)
    (hpb : t.pageBase = 3 + 5 * t.nf + spans.sum)
    (hinfo : t.infoId = t.pageBase + 2 * t.np)
    (hroot : t.outlineRootId = t.infoId + 1)
    (hsr : t.structTreeRoot = if t.nOut == 0 then t.infoId + 1 else t.infoId + 2 + t.nOut)
    (hpt : t.parentTree = t.structTreeRoot + 1) (hns : t.namespaceId = t.structTreeRoot + 2)
    (hsb : t.structBase = t.structTreeRoot + 3) (hxmp : t.xmpId = t.structBase + t.nElems)
    (hstm : t.objStmId = t.xmpId + 1) (hxref : t.xrefId = t.xmpId + 2)
    (hsize : t.size = t.xmpId + 3) :
    t.ids.toList = List.range' 1 (t.size - 1) := by
  have hfont : ∀ k, [ObjTable.type0Id k, ObjTable.cidId k, ObjTable.fdId k, ObjTable.toUniId k]
      = List.range' (3 + 4 * k) 4 := fun _ => rfl
  have hpage : ∀ i, [t.pageId i, t.contentId i] = List.range' (t.pageBase + 2 * i) 2 :=
    fun _ => rfl
  have hfile : List.map t.fileId (List.range t.nf) = List.range' (3 + 4 * t.nf) t.nf := by
    rw [List.range'_eq_map_range]; rfl
  have hitems : List.map t.outlineItemId (List.range t.nOut)
      = List.range' (t.infoId + 2) t.nOut := by
    rw [List.range'_eq_map_range]; rfl
  have h12 : [1, 2] = List.range' 1 2 := rfl
  have hinfo1 : [t.infoId] = List.range' t.infoId 1 := rfl
  have htail : [t.xmpId, t.objStmId, t.xrefId] = List.range' t.xmpId 3 := by
    rw [hstm, hxref]; rfl
  have hstruct : [t.structTreeRoot, t.parentTree, t.namespaceId] = List.range' t.structTreeRoot 3 := by
    rw [hpt, hns]; rfl
  have helems : List.map t.structElemId (List.range t.nElems)
      = List.range' t.structBase t.nElems := by
    rw [List.range'_eq_map_range]; rfl
  simp only [ObjTable.ids, Array.toList_append, Array.toList_flatMap, Array.toList_map,
    Array.toList_range, Array.toList_zip, Array.toList_range', himg, hsp]
  rw [blockIds_exact, flatMap_range_exact 3 4 t.nf _ hfont,
    flatMap_range_exact t.pageBase 2 t.np _ hpage, hfile, h12, hinfo1, htail, hstruct, helems]
  by_cases h0 : t.nOut = 0
  · simp only [h0, beq_self_eq_true, ite_true, Array.toList_empty, List.append_nil] at hsr ⊢
    simp (disch := omega) only [range'_append_of]
    rw [hsize, hxmp, hsb, hsr, hinfo, hpb]
    congr 1
    omega
  · have hne : (t.nOut == 0) = false := by simpa using h0
    simp only [hne, Bool.false_eq_true, ite_false, Array.toList_append, Array.toList_map,
      Array.toList_range, hitems] at hsr ⊢
    have hout : [t.outlineRootId] ++ List.range' (t.infoId + 2) t.nOut
        = List.range' (t.infoId + 1) (1 + t.nOut) := by
      rw [hroot]; exact range'_append_of _ 1 _ _ rfl
    rw [hout]
    simp (disch := omega) only [range'_append_of]
    rw [hsize, hxmp, hsb, hsr, hinfo, hpb]
    congr 1
    omega

/-- **`objTable_ids_exact`** (the `_exact` statement the two theorems below
project): the table's ids, block by block from its slot functions, are the
range `[1, size)` — the allocation is a tiling. -/
theorem objTable_ids_exact (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems : Nat) :
    (objTable keep imgs usedImgs np nOut nElems).ids.toList
      = List.range' 1 ((objTable keep imgs usedImgs np nOut nElems).size - 1) :=
  ObjTable.ids_exact _ ((usedImgs.map (imgExtraOf imgs)).map ImgExtra.span).toList
    (List.toList_toArray) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- **`objTable_inj`** (the `_inj` statement): no two slots of the table
share an id — the allocation is injective. -/
theorem objTable_inj (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems : Nat) : (objTable keep imgs usedImgs np nOut nElems).ids.toList.Nodup := by
  rw [objTable_ids_exact]
  exact List.nodup_range' 1

/-- **`objTable_covers`** (the `_covers` statement): every id below the
trailer's `/Size`, other than the free-list head 0, is allocated — no row
of the cross-reference is left to a default. -/
theorem objTable_covers (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems : Nat) :
    ∀ id, 1 ≤ id → id < (objTable keep imgs usedImgs np nOut nElems).size →
      id ∈ (objTable keep imgs usedImgs np nOut nElems).ids := by
  intro id h1 h2
  rw [Array.mem_def, objTable_ids_exact, List.mem_range'_1]
  omega

/-- **`objTable_between`** (the `_between` statement): every allocated id
lies in `[1, size)` — the converse of `objTable_covers`, and what makes
`kindOf` answer on every id `write` iterates. -/
theorem objTable_between (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems : Nat) :
    ∀ id ∈ (objTable keep imgs usedImgs np nOut nElems).ids,
      1 ≤ id ∧ id < (objTable keep imgs usedImgs np nOut nElems).size := by
  intro id h
  rw [Array.mem_def, objTable_ids_exact, List.mem_range'_1] at h
  have : 3 ≤ (objTable keep imgs usedImgs np nOut nElems).size := by
    simp only [objTable]
    omega
  omega

/-- `kindOf` is defined on every id the table allocates: the `none` arm of
the match in `write` is dead by this theorem, not by a default. -/
theorem objTable_kindOf_some (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems : Nat) (compressedIdx : Nat → Option Nat) :
    ∀ id ∈ (objTable keep imgs usedImgs np nOut nElems).ids,
      ((objTable keep imgs usedImgs np nOut nElems).kindOf compressedIdx id).isSome = true := by
  intro id h
  have hb := objTable_between keep imgs usedImgs np nOut nElems id h
  unfold ObjTable.kindOf
  rw [ite_eq_right (by simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]; omega)]
  split
  · rfl
  · split <;> rfl

/-- A row of the writer's cross-reference. A missing direct object is
declared free; it is never redirected to an unrelated compressed object. -/
def xrefEntry (t : ObjTable) (compressedIdx offset : Nat → Option Nat)
    (xrefOff id : Nat) : Xref.Entry :=
  if id == t.xrefId then .direct xrefOff 0 else
    match compressedIdx id with
    | some idx => .compressed t.objStmId idx
    | none => match offset id with
      | some off => .direct off 0
      | none => .free 0 0

/-- The free-list head and one row per allocated id, in allocation order.
`write` encodes this array itself; it is not a reconstructed certificate. -/
def xrefEntries (t : ObjTable) (compressedIdx offset : Nat → Option Nat)
    (xrefOff : Nat) : Array Xref.Entry :=
  #[.free 0 65535] ++ t.ids.map (xrefEntry t compressedIdx offset xrefOff)

/-- The row selection is the allocation table's kind decision on every
allocated id, including its explicit missing-direct-object case. -/
theorem xrefEntry_kind_exact (t : ObjTable)
    (compressedIdx offset : Nat → Option Nat) (xrefOff id : Nat)
    (hlo : 0 < id) (hhi : id < t.size) :
    some (xrefEntry t compressedIdx offset xrefOff id) =
      (t.kindOf compressedIdx id).map (fun k => match k with
        | .xref => .direct xrefOff 0
        | .inStream idx => .compressed t.objStmId idx
        | .direct => match offset id with
          | some off => .direct off 0
          | none => .free 0 0) := by
  have hbad : (id == 0 || decide (t.size ≤ id)) ≠ true := by
    simp only [ne_eq, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    omega
  simp only [ObjTable.kindOf, ite_eq_right hbad]
  unfold xrefEntry
  split
  · rfl
  · cases compressedIdx id <;> rfl

/-- The actual xref payload has exactly the number of seven-byte rows
declared by `/Size` and `/Index`, including row zero. -/
theorem xrefEntries_size_exact (keep : Array Nat) (imgs : Image.Store)
    (usedImgs : Array Nat) (np nOut nElems : Nat)
    (compressedIdx offset : Nat → Option Nat) (xrefOff : Nat) :
    let t := objTable keep imgs usedImgs np nOut nElems
    (xrefEntries t compressedIdx offset xrefOff).size = t.size ∧
      (Xref.encode (xrefEntries t compressedIdx offset xrefOff)).size = 7 * t.size := by
  dsimp only
  have ht := objTable_ids_exact keep imgs usedImgs np nOut nElems
  have hn := congrArg List.length ht
  simp only [Array.length_toList, List.length_range'] at hn
  have hpos : 0 < (objTable keep imgs usedImgs np nOut nElems).size := by
    simp only [objTable]
    omega
  have hsize : (xrefEntries (objTable keep imgs usedImgs np nOut nElems)
      compressedIdx offset xrefOff).size =
      (objTable keep imgs usedImgs np nOut nElems).size := by
    simp only [xrefEntries, Array.size_append, Array.size_map, Array.size_singleton, hn]
    omega
  exact ⟨hsize, by rw [Xref.encode_size_exact, hsize]⟩

/-- Numeric field bounds suffice for every emitted xref entry. This
assumes no property of our writer, parser, or compressor. -/
theorem xrefEntry_fits (t : ObjTable) (compressedIdx offset : Nat → Option Nat)
    (xrefOff id : Nat) (hx : xrefOff < 256 ^ 4) (hs : t.objStmId < 256 ^ 4)
    (hc : ∀ n i, compressedIdx n = some i → i < 256 ^ 2)
    (ho : ∀ n i, offset n = some i → i < 256 ^ 4) :
    (xrefEntry t compressedIdx offset xrefOff id).Fits := by
  unfold xrefEntry
  split
  · exact ⟨hx, by change 0 < 256 ^ 2; omega⟩
  · split
    · exact ⟨hs, hc _ _ ‹_›⟩
    · split
      · exact ⟨ho _ _ ‹_›, by change 0 < 256 ^ 2; omega⟩
      · exact ⟨by decide, by decide⟩

-- ## The feature census

/-- What a written file asks of a reader, one constructor per thing a
reader must implement to show the file right: the rows of the reader
matrix (`tests/oracles/reader-matrix.txt`, spelled by `name`), whose
cells are what the readers on the `target:` line made of each. Every
constructor is parameter-free, so `all` is derived from the type and
`all_complete`/`all_nodup` close the census: a feature the writer starts
emitting is a row the matrix must carry, red until the readers pass it.
`copiedGraph` stands where a placed PDF page's own resource streams ride
verbatim: their filters are theirs, not this writer's, and the census
does not read them — the graph census will name them; until then the
whole graph is one feature the readers must pass. -/
inductive Feature where
  | xrefStream
  | objStm
  | flatePredictor15
  | dct
  | smask
  | formXObject
  | copiedGraph
  | cidFontType0
  | cidFontType2
  | linkURI
  | outlines
  | xmp
  | trimBox
  | outputIntent
  | iccBased
  | tabs
  | markedContent
  | structTree
  | transparencyGroup
  | brotli
  | jpx
  deriving DecidableEq, Repr, Inhabited

/-- How many features the census names: the one number a new constructor
bumps (`all_complete` fails on an undercount, `all_nodup` on an overcount,
`ofNat` clamping the excess onto the last constructor). -/
def Feature.count : Nat := 21

/-- Every feature, in declaration order — derived from the type through
the `ofNat` that `deriving DecidableEq` synthesises, never hand-kept. -/
def Feature.all : List Feature := (List.range Feature.count).map Feature.ofNat

theorem Feature.all_complete (f : Feature) : f ∈ Feature.all := by
  cases f <;> decide

theorem Feature.all_nodup : Feature.all.Nodup := by decide

/-- The matrix row a feature is spelled as. -/
def Feature.name : Feature → String
  | .xrefStream => "xref-stream"
  | .objStm => "objstm"
  | .flatePredictor15 => "flate-predictor15"
  | .dct => "dct"
  | .smask => "smask"
  | .formXObject => "form-xobject"
  | .copiedGraph => "copied-graph"
  | .cidFontType0 => "cidfonttype0"
  | .cidFontType2 => "cidfonttype2"
  | .linkURI => "link-uri"
  | .outlines => "outlines"
  | .xmp => "xmp"
  | .trimBox => "trimbox"
  | .outputIntent => "output-intent"
  | .iccBased => "icc-based"
  | .tabs => "tabs"
  | .markedContent => "marked-content"
  | .structTree => "struct-tree"
  | .transparencyGroup => "transparency-group"
  | .brotli => "brotli"
  | .jpx => "jpx"

/-- **`Feature.name_inj`** (the `_inj` statement): no two features share a
row name, so a matrix row names one feature. -/
theorem Feature.name_inj (a b : Feature) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Feature.name] at h)

def Feature.ofName? (s : String) : Option Feature := Feature.all.find? (·.name == s)

/-- Whether one run of `write` on these inputs reaches a feature: the
table's slots say what was allocated (a soft mask, a copied graph, an
outline, the colour and structure families); the kept faces say which CID
subtype; each placed image its declared filter; the pages their link
annotations and the outline its URI targets; the content operators whether
a marked sequence opens. The four the writer cannot emit yet (`tabs`,
`transparencyGroup`, `brotli`, `jpx`) are `false` here and rows the matrix
already carries, so the day one is emitted the census says so. -/
def reaches (geom : Geom) (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store)
    (outline : Array OutlineEntry) : Feature → Bool
  | .xrefStream => true
  | .objStm => true
  | .flatePredictor15 =>
    (placedImages imgs pages).any (fun i => i.form.isNone && i.filter == .flatePredictor)
      || (tableOf fs pages imgs outline).smaskIds.any Option.isSome
  | .dct => (placedImages imgs pages).any (fun i => i.form.isNone && i.filter == .dct)
  | .smask => (tableOf fs pages imgs outline).smaskIds.any Option.isSome
  | .formXObject => (tableOf fs pages imgs outline).formBases.any Option.isSome
  | .copiedGraph => (tableOf fs pages imgs outline).formSizes.any (· > 0)
  | .cidFontType0 => (keepFaces fs pages).any fun k => (fs.get k).isCff
  | .cidFontType2 => (keepFaces fs pages).any fun k => !(fs.get k).isCff
  | .linkURI =>
    pages.any (fun p => (linkRects geom p).any (fun r => !r.2.2.2.2.startsWith "#"))
      || outline.any (fun e => e.page.isNone && e.url.isSome)
  | .outlines => outline.size > 0
  | .xmp => true
  | .trimBox => geom.bleed != 0
  | .outputIntent => (tableOf fs pages imgs outline).outputIntent.isSome
  | .iccBased => (tableOf fs pages imgs outline).icc.isSome
  | .tabs => false
  | .markedContent => (pageOps geom fs pages imgs).any fun ops => (lines ops).any Line.isOpen
  -- every PDF is tagged: the structure block is unconditional (pdf-tag-skeleton)
  | .structTree => true
  | .transparencyGroup => false
  | .brotli => false
  | .jpx => false
where
  /-- The decoded images the pages place, in placement order: what `write`
  writes an XObject dictionary for. -/
  placedImages (imgs : Image.Store) (pages : Array PageOut) : Array Image.Plan :=
    (usedImagesOf imgs pages).filterMap fun k => (imgs.get? k).bind (·.info)

/-- The features `write` reaches on these inputs, in `Feature.all`'s order:
the closed census the reader matrix's rows are checked against, computed
by the test and the oracle script from the same inputs `write` reads,
never from the bytes. -/
def features (geom : Geom) (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store := {})
    (outline : Array OutlineEntry := #[]) : Array Feature :=
  (Feature.all.filter (reaches geom fs pages imgs outline)).toArray

/-- **`features_mem`** (the `_mem` statement): every feature the census
reports is drawn from `Feature.all` — the row set is closed, so a matrix
carrying a row per `Feature.all` has a row for whatever a fixture emits. -/
theorem features_mem (geom : Geom) (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store)
    (outline : Array OutlineEntry) (f : Feature) (h : f ∈ features geom fs pages imgs outline) :
    f ∈ Feature.all := by
  unfold features at h
  exact (List.mem_filter.1 (List.mem_toArray.1 h)).1

/-- **`features_smask_iff`** (the `_exact` statement): the census says
`smask` exactly when the table allocated a soft-mask id — the same slot
`write` reads to emit `/SMask`. -/
theorem features_smask_iff (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store) (outline : Array OutlineEntry) :
    .smask ∈ features geom fs pages imgs outline ↔
      ∃ k, ∃ h : k < (tableOf fs pages imgs outline).smaskIds.size,
        ((tableOf fs pages imgs outline).smaskIds[k]).isSome = true := by
  unfold features
  rw [List.mem_toArray, List.mem_filter]
  simp only [Feature.all_complete, true_and, reaches, Array.any_eq_true]

/-- One physical object as the bytes `serialize` writes for it: a
dictionary fragment and a stream payload whose filter is already chosen, a
form XObject whose `/Resources` is a copied graph's renumbered bytes, or a
copied object's own value bytes with its own stream. No offset rides here —
`serialize` decides where an object lands, and it decides it by having
written everything before it. -/
inductive Body where
  | stream (dict : String) (data : ByteArray)
  /-- The dictionary up to `/Resources`, the renumbered resource bytes, and
  the form's content. The resources are bytes with reference holes
  (`PdfRead.Chunk`), not an object, so this arm stays raw until a copied
  graph's dictionary is itself typed. -/
  | form (head : String) (resources : ByteArray) (content : ByteArray)
  /-- A copied object: its value verbatim and its stream when it has one.
  The filters are the source file's, never this writer's. -/
  | copied (value : ByteArray) (stream : Option ByteArray)

/-- An object with the id the table allocated it. -/
structure Row where
  id : Nat
  body : Body

/-- The bytes one object is written as, appended to the buffer it lands in:
the accumulator form, so a 60 MB font program is appended in place rather
than built beside the file and copied into it. -/
def rowInto (out : ByteArray) (id : Nat) : Body → ByteArray
  | .stream dict data =>
    ((out ++ (s!"{id} 0 obj\n<< {dict} /Length {data.size} >>\nstream\n").toUTF8) ++ data)
      ++ "\nendstream\nendobj\n".toUTF8
  | .form h res content =>
    ((((out ++ (s!"{id} 0 obj\n").toUTF8) ++ h.toUTF8) ++ res)
      ++ (s!" /Length {content.size} >>\nstream\n").toUTF8) ++ content
      ++ "\nendstream\nendobj\n".toUTF8
  | .copied value (some raw) =>
    (((out ++ (s!"{id} 0 obj\n").toUTF8) ++ value) ++ "\nstream\n".toUTF8) ++ raw
      ++ "\nendstream\nendobj\n".toUTF8
  | .copied value none =>
    ((out ++ (s!"{id} 0 obj\n").toUTF8) ++ value) ++ "\nendobj\n".toUTF8

/-- The `List` companion: the offset is bound before the append so the
buffer stays uniquely owned and the append is in place. -/
def serializeList (out : ByteArray) (locs : Array (Nat × Nat)) :
    List Row → ByteArray × Array (Nat × Nat)
  | [] => (out, locs)
  | r :: rest =>
    let off := out.size
    serializeList (rowInto out r.id r.body) (locs.push (r.id, off)) rest

/-- The file's objects and where each one landed. The offsets are this
fold's own — the size the buffer had when the object's bytes began — so
nothing can disagree with them: the cross-reference is built from this
result, not from a table filled beside the writing. `write_readXref_exact`
is the statement this shape exists for. -/
def serialize (head : ByteArray) (rows : Array Row) : ByteArray × Array (Nat × Nat) :=
  serializeList head #[] rows.toList

/-- A row appends its bytes independently of the preceding file. -/
theorem rowInto_bytes (pre : ByteArray) (id : Nat) (body : Body) :
    rowInto pre id body = pre ++ rowInto ByteArray.empty id body := by
  cases body with
  | stream dict data => simp [rowInto, ByteArray.append_assoc]
  | form head resources content => simp [rowInto, ByteArray.append_assoc]
  | copied value stream =>
    cases stream <;> simp [rowInto, ByteArray.append_assoc]

theorem serializeList_bytes (rows : List Row) (out : ByteArray)
    (locs : Array (Nat × Nat)) :
    (serializeList out locs rows).1 =
      out ++ (serializeList ByteArray.empty #[] rows).1 := by
  induction rows generalizing out locs with
  | nil => simp [serializeList]
  | cons r rest ih =>
    simp only [serializeList]
    rw [ih, ih (rowInto ByteArray.empty r.id r.body)]
    rw [rowInto_bytes out]
    exact ByteArray.append_assoc

theorem serializeList_offsets (rows : List Row) (out : ByteArray)
    (locs : Array (Nat × Nat)) :
    (serializeList out locs rows).2 =
      locs ++ (serializeList out #[] rows).2 := by
  induction rows generalizing out locs with
  | nil => simp [serializeList]
  | cons r rest ih =>
    simp only [serializeList]
    rw [ih (rowInto out r.id r.body) (locs.push (r.id, out.size)),
      ih (rowInto out r.id r.body) (#[].push (r.id, out.size))]
    simp only [Array.push_eq_append, Array.empty_append, Array.append_assoc]

theorem serializeList_offsetSize (rows : List Row) (out : ByteArray)
    (locs : Array (Nat × Nat)) :
    (serializeList out locs rows).2.size = locs.size + rows.length := by
  induction rows generalizing out locs with
  | nil => simp [serializeList]
  | cons r rest ih =>
    simp only [serializeList, ih, Array.size_push, List.length_cons]
    omega

theorem serializeList_append (before after : List Row) (out : ByteArray)
    (locs : Array (Nat × Nat)) :
    serializeList out locs (before ++ after) =
      serializeList (serializeList out locs before).1
        (serializeList out locs before).2 after := by
  induction before generalizing out locs with
  | nil => rfl
  | cons r rest ih =>
    simpa only [List.cons_append, serializeList] using
      (ih (rowInto out r.id r.body) (locs.push (r.id, out.size)))

/-- Every recorded offset selects exactly that row's bytes in the
serialized file. This artifact-specific law quantifies over all preceding
and following rows, including binary streams and copied objects. -/
theorem serialize_row_exact (head : ByteArray) (before after : Array Row) (r : Row) :
    let pre := (serialize head before).1
    let out := serialize head (before ++ #[r] ++ after)
    out.2[before.size]? = some (r.id, pre.size) ∧
      out.1.extract pre.size (pre.size + (rowInto ByteArray.empty r.id r.body).size) =
        rowInto ByteArray.empty r.id r.body := by
  dsimp only
  simp only [serialize, Array.toList_append, List.append_assoc,
    List.singleton_append, serializeList_append, serializeList]
  constructor
  · rw [serializeList_offsets]
    have hsize := serializeList_offsetSize before.toList head #[]
    simp only [Array.size_empty, Nat.zero_add, Array.length_toList] at hsize
    rw [Array.getElem?_append_left (by simp [hsize])]
    rw [← hsize]
    exact Array.getElem?_push_size
  · rw [serializeList_bytes, rowInto_bytes]
    rw [ByteArray.append_assoc]
    simpa only [Nat.add_zero] using
      (ByteArray.extract_append_size_add
        (a := (serializeList head #[] before.toList).1)
        (b := rowInto ByteArray.empty r.id r.body ++
          (serializeList ByteArray.empty #[] after.toList).1)
        (i := 0) (j := (rowInto ByteArray.empty r.id r.body).size)).trans
        (ByteArray.extract_append_eq_left rfl)

/-- **`serialize_locs_covers`** (the `_covers` statement): `serialize`
reports one offset per row, in the rows' own order — so a cross-reference
built from `locs` names every object the writer wrote and no other. -/
theorem serializeList_ids (l : List Row) (out : ByteArray) (locs : Array (Nat × Nat)) :
    (serializeList out locs l).2.toList.map (·.1) = locs.toList.map (·.1) ++ l.map (·.id) := by
  induction l generalizing out locs with
  | nil => simp [serializeList]
  | cons r rest ih => simp [serializeList, ih]

theorem serialize_locs_covers (head : ByteArray) (rows : Array Row) :
    (serialize head rows).2.toList.map (·.1) = rows.toList.map (·.id) := by
  simp [serialize, serializeList_ids]

/-- **`serialize_locs_id`** (the `_id` statement): the first object lands at
the head's own size — the offset a reader following `startxref` arrives at,
and the base case of the induction over the rows. -/
theorem serialize_locs_id (head : ByteArray) (r : Row) (rest : Array Row) :
    (serialize head (#[r] ++ rest)).2[0]? = some (r.id, head.size) := by
  simpa [serialize, serializeList] using (serialize_row_exact head #[] rest r).1

/-- The two buffers of an object stream (§7.5.7). Header offsets are
relative to `payload`, whose bytes are appended by the same step. -/
structure ObjectStream where
  header : String := ""
  payload : ByteArray := ByteArray.empty

def ObjectStream.push (s : ObjectStream) (id : Nat) (value : PdfRead.Obj) : ObjectStream :=
  { header := s.header ++ s!"{id} {s.payload.size} "
    payload := (s.payload ++ PdfRead.Obj.render value).push 10 }

/-- The actual writer's accumulator, shared by the emission and its
offset laws. No object offsets are supplied by a caller. -/
def objectStreamList (s : ObjectStream) : List (Nat × PdfRead.Obj) → ObjectStream
  | [] => s
  | (id, value) :: rest => objectStreamList (s.push id value) rest

def objectStream (objects : List (Nat × PdfRead.Obj)) : ObjectStream :=
  objectStreamList {} objects

def ObjectStream.bytes (s : ObjectStream) : ByteArray :=
  s.header.toUTF8 ++ s.payload

theorem objectStreamList_append (s : ObjectStream) (before after : List (Nat × PdfRead.Obj)) :
    objectStreamList s (before ++ after) =
      objectStreamList (objectStreamList s before) after := by
  induction before generalizing s with
  | nil => rfl
  | cons r rest ih => exact ih _

theorem objectStreamList_header (objects : List (Nat × PdfRead.Obj))
    (header : String) (payload : ByteArray) :
    (objectStreamList ⟨header, payload⟩ objects).header =
      header ++ (objectStreamList ⟨"", payload⟩ objects).header := by
  induction objects generalizing header payload with
  | nil => simp [objectStreamList]
  | cons r rest ih =>
    simp only [objectStreamList, ObjectStream.push, String.empty_append]
    rw [ih, ih s!"{r.1} {payload.size} "]
    simp [String.append_assoc]

theorem objectStreamList_payload (objects : List (Nat × PdfRead.Obj)) (s : ObjectStream) :
    (objectStreamList s objects).payload =
      s.payload ++ (objectStream objects).payload := by
  induction objects generalizing s with
  | nil => simp [objectStreamList, objectStream]
  | cons r rest ih =>
    change (objectStreamList (s.push r.1 r.2) rest).payload =
      s.payload ++ (objectStreamList (({} : ObjectStream).push r.1 r.2) rest).payload
    rw [ih, ih (({} : ObjectStream).push r.1 r.2)]
    simp only [ObjectStream.push, ByteArray.empty_append]
    apply ByteArray.ext
    simp only [ByteArray.data_push, ByteArray.data_append, Array.push_eq_append,
      Array.append_assoc]

/-- Every object's header entry spells the size of its actual preceding
payload, and that offset after `/First` selects exactly its rendered
bytes. This holds for arbitrary objects and surrounding objects; parser
grammar and xref field bounds are separate obligations. -/
theorem objectStream_entry_exact (before after : List (Nat × PdfRead.Obj))
    (id : Nat) (value : PdfRead.Obj) :
    let pre := objectStream before
    let out := objectStream (before ++ (id, value) :: after)
    (∃ suffix, out.header = pre.header ++ s!"{id} {pre.payload.size} " ++ suffix) ∧
      out.bytes.extract (out.header.utf8ByteSize + pre.payload.size)
        (out.header.utf8ByteSize + pre.payload.size + (PdfRead.Obj.render value).size) =
        PdfRead.Obj.render value := by
  dsimp only
  have hout : objectStream (before ++ (id, value) :: after) =
      objectStreamList ((objectStream before).push id value) after := by
    rw [objectStream, objectStreamList_append]
    rfl
  rw [hout]
  constructor
  · exact ⟨_, objectStreamList_header after _ _⟩
  · simp only [ObjectStream.bytes, String.toUTF8_eq_toByteArray, ← String.size_toByteArray]
    rw [Nat.add_assoc, ByteArray.extract_append_size_add]
    rw [objectStreamList_payload]
    simp only [ObjectStream.push]
    have hp (p v : ByteArray) :
        (p ++ v).push 10 = p ++ v ++ (ByteArray.empty.push 10) := by
      apply ByteArray.ext
      simp only [ByteArray.data_push, ByteArray.data_append, Array.push_eq_append,
        ByteArray.data_empty, Array.empty_append]
    rw [hp, ByteArray.append_assoc, ByteArray.append_assoc]
    simpa only [Nat.add_zero] using
      (ByteArray.extract_append_size_add (a := (objectStream before).payload)
        (b := PdfRead.Obj.render value ++ (ByteArray.empty.push 10 ++
          (objectStream after).payload)) (i := 0) (j := (PdfRead.Obj.render value).size)).trans
        (ByteArray.extract_append_eq_left rfl)

/-- The three dictionaries of one embedded face (ISO 32000-2 §§9.7, 9.8).
The stream rows hold its program and ToUnicode separately. -/
structure FontObjects where
  type0 : PdfRead.Obj
  cid : PdfRead.Obj
  descriptor : PdfRead.Obj

def FontObjects.rows (o : FontObjects) (k : Nat) : List (Nat × PdfRead.Obj) :=
  [(ObjTable.type0Id k, o.type0), (ObjTable.cidId k, o.cid),
    (ObjTable.fdId k, o.descriptor)]

/-- Font dictionaries from the face metrics and the allocated ids.
The name and widths have already been resolved for the selected glyphs. -/
def fontObjects (t : ObjTable) (k : Nat) (font : Font)
    (baseFont : String) (widths : PdfRead.Obj) : FontObjects :=
  let ascent1000 := font.ascent * 1000 / font.unitsPerEm
  let descent1000 := font.descent * 1000 / font.unitsPerEm
  -- The descriptor states the parsed metrics, not stand-ins: CapHeight is
  -- the face's own (OS/2 sCapHeight through `Font.capHeight` — `ascent`
  -- once stood in for it), and ItalicAngle is the slant the face declares
  -- (post.italicAngle); only a face flagged italic that declares none
  -- keeps the conventional -12°.
  let capHeight1000 := font.capHeight * 1000 / font.unitsPerEm
  let cidSubtype := if font.isCff then "CIDFontType0" else "CIDFontType2"
  let cidToGid : Array (String × PdfRead.Obj) :=
    if font.isCff then #[] else #[("CIDToGIDMap", .name "Identity")]
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
  {
    type0 := .dict
      #[("Type", .name "Font"), ("Subtype", .name "Type0"), ("BaseFont", .name baseFont),
        ("Encoding", .name "Identity-H"),
        ("DescendantFonts", .arr #[.ref (ObjTable.cidId k) 0]),
        ("ToUnicode", .ref (ObjTable.toUniId k) 0)]
    cid := .dict
      (#[("Type", .name "Font"), ("Subtype", .name cidSubtype),
         ("BaseFont", .name baseFont),
         ("CIDSystemInfo", .dict #[("Registry", litObj "(Adobe)"),
           ("Ordering", litObj "(Identity)"), ("Supplement", .int 0)]),
         ("FontDescriptor", .ref (ObjTable.fdId k) 0), ("DW", .int 1000),
         ("W", widths)] ++ cidToGid)
    descriptor := .dict
      #[("Type", .name "FontDescriptor"), ("FontName", .name baseFont), ("Flags", .int flags),
        ("FontBBox", .arr #[.int (-1000), .int descent1000, .int 2000, .int ascent1000]),
        ("ItalicAngle", .int italicAngle), ("Ascent", .int ascent1000),
        ("Descent", .int descent1000), ("CapHeight", .int capHeight1000),
        ("StemV", .int stemV), (fontFileKey, .ref (t.fileId k) 0)]
  }

/-- The composite font, its descendant, and its descriptor point to the
table's own slots, for every face and glyph-width table. This is a PDF
dictionary contract; it does not assume a reader or certify a font file. -/
theorem fontObjects_links_exact (t : ObjTable) (k : Nat) (font : Font)
    (baseFont : String) (widths : PdfRead.Obj) :
    let o := fontObjects t k font baseFont widths
    o.type0.get? "DescendantFonts" = some (.arr #[.ref (ObjTable.cidId k) 0]) ∧
    o.type0.get? "ToUnicode" = some (.ref (ObjTable.toUniId k) 0) ∧
    o.cid.get? "FontDescriptor" = some (.ref (ObjTable.fdId k) 0) ∧
    o.descriptor.get? (if font.isCff then "FontFile3" else "FontFile2") =
      some (.ref (t.fileId k) 0) := by
  cases hcff : font.isCff <;>
    simp [fontObjects, hcff, PdfRead.Obj.get?]

/-- Serialize positioned pages into a PDF 2.0 file: cross-reference stream,
object streams, one Identity-H CID font per face actually used (its program
the subset of the glyphs the pages paint, `FontSubset.program`, with its
own ToUnicode), image XObjects for every image actually
placed, the structure tree projected from `tree`, and the document
information the source declared (Info dictionary plus XMP). `streams`,
`ops` and `programs` are the driver's cache path: the page operators it
built through `pageOps` (one walk, not two), their rendered and deflated
bytes, and the face programs it built through `facePrograms`. -/
def write (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta := {}) (imgs : Image.Store := {})
    (outline : Array OutlineEntry := #[])
    (streams : Array (ByteArray × Option ByteArray) := #[])
    (tree : Struct.Tree := ⟨#[]⟩) (ops : Array (Array ContentOp) := #[])
    (programs : Array (ByteArray × Bool) := #[]) : ByteArray := Id.run do
  let np := pages.size
  let v17 := info.pdfVersion == some "1.7"
  -- Only faces that actually contribute glyphs are embedded — `keepFaces`,
  -- the very function `html_fonts_cover_pdf` quantifies over (`keepOf` of
  -- this census is `keepFaces fs pages` by definition), so the contract
  -- holds of the writer's own decision, not a copy. `allUsed` stays for the
  -- per-face glyph census the kept faces subset.
  let allUsed : Array (Array (Nat × Char)) := usedAll fs pages
  let keep : Array Nat := keepOf allUsed
  let remap := remapOf fs keep
  let usedPerFont : Array (Array (Nat × Char)) := keep.map fun k => allUsed[k]!
  let nf := keep.size
  -- The program each kept face embeds: its own file minus every glyph no
  -- page paints (`FontSubset.program`), named with a subset tag when it is
  -- one — the caller's when it built them (`facePrograms`), else built here.
  let programs : Array (ByteArray × Bool) := if programs.size == nf then programs
    else (keep.zip usedPerFont).map fun (fk, used) =>
      let font := fs.get fk
      FontSubset.program font (used.map (·.1))
  let usedImgs := usedImagesOf imgs pages
  let ni := usedImgs.size
  let imgMap := imgMapOf imgs usedImgs
  let nOut := outline.size
  -- The structure tree: the skeleton once, its leaf tags into every page's
  -- operators, the pages' marks back into the skeleton (`fill`), and the
  -- parent tree as the same map read from the page side. One walk decides
  -- the tag a sequence carries and the element that lists it.
  let sk := skeleton tree
  let nLeaves := tree.leaves.size
  let tags := leafTags sk nLeaves
  -- The typed operators: the caller's when it built them (`pageOps`, the
  -- same walk — `streams` are their render), else built here.
  let ops := if ops.size == np then ops
    else let wt := widthTable fs.fonts keep
      pages.map (contentOps geom remap wt imgMap tags)
  let marks := ops.map pageMarks
  let es := fill sk (leafPagesOf nLeaves marks)
  let parentTree := parentTreeOf marks (leafOwners sk nLeaves)
  -- Every object id, from the one table: `objTable_ids_exact` says its
  -- ids tile `[1, size)`, so the cross-reference can be built without a
  -- second pass and no row is left to a default.
  let t := objTable keep imgs usedImgs np nOut es.size

  -- compressed (non-stream) objects, as typed values: `Obj.render` is the
  -- only place their bytes are decided, so what the census reads back is
  -- the value this writer built (`parseVal_render_id`).
  let outlineRoot := if nOut == 0 then none else some t.outlineRootId
  -- The catalog: `catalogDict`, whose `/Lang` is `pdf_lang_declared`'s
  -- statement — present exactly when the document declares a language.
  let catalog := catalogDict outlineRoot t.xmpId info.language t.structTreeRoot
  let pagesObj : PdfRead.Obj := .dict
    #[("Type", .name "Pages"),
      ("Kids", .arr ((Array.range np).map fun i => .ref (t.pageId i) 0)),
      ("Count", .int np)]
  let fontResources : PdfRead.Obj :=
    .dict ((Array.range nf).map fun k => (s!"F{k + 1}", PdfRead.Obj.ref (ObjTable.type0Id k) 0))
  let fontObjs : List (Nat × PdfRead.Obj) := (List.range nf).flatMap fun k =>
    let font := fs.get keep[k]!
    let used := usedPerFont[k]!
    let baseFont := if (programs[k]?.map (·.2)).getD false
      then s!"{subsetTag k (used.map (·.1))}+{font.psName}" else font.psName
    (fontObjects t k font baseFont (wArray font used)).rows k
  -- Internal fragments name PDF destinations, never URI actions. Resolve
  -- from the final lines so columns, spills, and vertical glue cannot leave
  -- an annotation pointing at the page where collection first saw its name
  -- (ISO 32000-2 §§12.3.2, 12.6.4.2).
  let linkTarget (url : String) : String × PdfRead.Obj :=
    if url.startsWith "#" then
      let name := (url.drop 1).toString
      match Layout.destination? pages name with
      | some (page, line) =>
        let above := (Layout.segsInk fs line.segs).1
        ("Dest", .arr #[.ref (t.pageId page) 0, .name "XYZ",
          ptObj (line.x + geom.bleed),
          ptObj (geom.pageH + geom.bleed - (line.y - above)), .null])
      | none =>
        ("A", .dict #[("S", .name "GoTo"), ("D", litObj (pdfTextString name))])
    else
      ("A", .dict #[("S", .name "URI"), ("URI", litObj s!"({pdfString url})")])
  let annots (i : Nat) : Array (String × PdfRead.Obj) :=
    let rects := linkRects geom pages[i]!
    if rects.isEmpty then #[] else
      #[("Annots", .arr (rects.map fun (x0, y0, x1, y1, url) =>
        .dict #[("Type", .name "Annot"), ("Subtype", .name "Link"),
          ("Rect", .arr #[ptObj x0, ptObj y0, ptObj x1, ptObj y1]),
          ("Border", .arr #[.int 0, .int 0, .int 0]), ("F", .int 4),
          linkTarget url]))]
  let pageDict (i : Nat) : PdfRead.Obj :=
    -- With bleed the medium is larger than the finished page, and the
    -- boxes follow from the declared trim size and bleed (`pageBoxes`,
    -- nesting proved by `pageBoxes_nest`) — the file itself tells
    -- prepress where to cut, no hand-rolled \pdfvariable pageattr needed.
    -- With zero bleed nothing is written: CropBox defaults to MediaBox
    -- and BleedBox/TrimBox/ArtBox default to CropBox (ISO 32000-2
    -- §14.11.2), so an empty dictionary already declares all boxes equal
    -- — and the zero-bleed output stays byte-identical.
    let b := geom.bleed
    -- A trim the document's own drawn marks cut (`Geom.trimInset`) is the
    -- same arithmetic from the other side: the medium is the page, the trim
    -- lies the inset inside it.
    let inset := if b == 0 then geom.trimInset else 0
    let (media, bleedBox, trim) :=
      if 0 < inset then pageBoxes (geom.pageW - 2 * inset) (geom.pageH - 2 * inset) inset
      else pageBoxes geom.pageW geom.pageH b
    let boxes : Array (String × PdfRead.Obj) := if b == 0 && !(0 < inset) then #[] else
      #[("TrimBox", trim.obj), ("BleedBox", bleedBox.obj), ("ArtBox", trim.obj)]
    let xobj : Array (String × PdfRead.Obj) := if ni == 0 then #[] else
      #[("XObject", .dict (t.imgIds.zipIdx.map fun (id, n) =>
        (s!"Im{n + 1}", PdfRead.Obj.ref id 0)))]
    -- `/StructParents` (§14.7.5.4): the page's key in the parent tree,
    -- under which its marked-content identifiers map back to elements.
    let ann := annots i
    .dict (#[("Type", PdfRead.Obj.name "Page"), ("Parent", .ref 2 0), ("MediaBox", media.obj)]
      ++ boxes
      ++ #[("Resources", .dict (#[("Font", fontResources)] ++ xobj))]
      ++ ann
      ++ #[("Contents", .ref (t.contentId i) 0), ("StructParents", .int i)])
  -- Metadata is a *text string* (§7.9.2.2): ASCII literal, or UTF-16BE
  -- with the BOM past ASCII — never raw UTF-8 bytes, which a reader
  -- decodes as PDFDocEncoding.
  let infoEntry (key : String) (v : Option String) : Array (String × PdfRead.Obj) :=
    match v with
    | some s => #[(key, litObj (pdfTextString s))]
    | none => #[]
  let infoDict : PdfRead.Obj := .dict
    (infoEntry "Title" info.title ++ infoEntry "Author" info.author ++
      infoEntry "Subject" info.subject ++ infoEntry "Keywords" info.keywords ++
      #[("Producer", litObj "(leantex)")])

  -- Outline items: /Title and /Parent always; a resolved in-document
  -- target is a /Dest to its page (/XYZ null null null keeps the reader's
  -- view), an external target a URI action, and a target that resolved to
  -- neither is a bare item — an outline item need carry no destination.
  let outlineObjs : List (Nat × PdfRead.Obj) :=
    if nOut == 0 then [] else
      (t.outlineRootId, PdfRead.Obj.dict
        #[("Type", .name "Outlines"), ("First", .ref (t.outlineItemId 0) 0),
          ("Last", .ref (t.outlineItemId (nOut - 1)) 0), ("Count", .int nOut)]) ::
      outline.toList.zipIdx.map fun (e, k) =>
        let prev : Array (String × PdfRead.Obj) :=
          if k == 0 then #[] else #[("Prev", .ref (t.outlineItemId (k - 1)) 0)]
        let next : Array (String × PdfRead.Obj) :=
          if k + 1 == nOut then #[] else #[("Next", .ref (t.outlineItemId (k + 1)) 0)]
        let target : Array (String × PdfRead.Obj) := match e.page, e.url with
          | some p, _ =>
            #[("Dest", .arr #[.ref (t.pageId p) 0, .name "XYZ", .null, .null, .null])]
          | none, some u => #[("A", .dict #[("S", .name "URI"), ("URI", litObj s!"({pdfString u})")])]
          | none, none => #[]
        (t.outlineItemId k, PdfRead.Obj.dict
          (#[("Title", litObj (pdfTextString e.title)),
             ("Parent", PdfRead.Obj.ref t.outlineRootId 0)] ++ prev ++ next ++ target))
  -- The structure tree (§14.7): the root over the `Document` element, the
  -- parent tree as one number-tree node keyed by page (`/StructParents`),
  -- the PDF 2.0 namespace the elements name (§14.7.4 — `Title`, `FENote`,
  -- `Hn` past 6 are 2.0 types; a type 2.0 dropped stays in the default
  -- 1.7 namespace by naming none), and one dictionary per element:
  -- its type, parent, kids as marked-content references (`/MCR`, §14.7.5.3
  -- — the page travels with the identifier, so an element may span
  -- pages), and the alternative or language it carries.
  let elemRef (i : Nat) : PdfRead.Obj := .ref (t.structElemId i) 0
  -- A file declared PDF 1.7 has one standard namespace and no namespace
  -- objects: its 2.0-only types are role-mapped onto 1.7's (`pdf17Role`).
  let roleMap : Array (String × PdfRead.Obj) := es.foldl (fun acc e =>
    match pdf17Role e.s with
    | some r => if acc.any (·.1 == e.s) then acc else acc.push (e.s, .name r)
    | none => acc) #[]
  let structRoot : PdfRead.Obj := .dict
    (#[("Type", .name "StructTreeRoot"), ("K", .arr #[elemRef 0]),
      ("ParentTree", .ref t.parentTree 0), ("ParentTreeNextKey", .int np)] ++
     (if v17 then (if roleMap.isEmpty then #[] else #[("RoleMap", .dict roleMap)])
      else #[("Namespaces", .arr #[.ref t.namespaceId 0])]))
  let parentEntries : Array PdfRead.Obj := (Array.range np).flatMap fun (i : Nat) =>
    #[PdfRead.Obj.int (i : Int), .arr ((parentTree[i]?.getD #[]).map fun o => match o with
      | some e => elemRef e
      | none => .null)]
  let parentTreeObj : PdfRead.Obj := .dict #[("Nums", .arr parentEntries)]
  let namespaceObj : PdfRead.Obj := if v17 then .dict #[] else .dict
    #[("Type", .name "Namespace"), ("NS", litObj "(http://iso.org/pdf2/ssn)")]
  -- a placeholder `fill` did not replace: none remain after `fill`, and
  -- one would be a leaf with no marked content, which lists nothing
  let kidObj (k : StructKid) : Array PdfRead.Obj := match k with
    | .elem i => #[elemRef i]
    | .mcid p m => #[.dict #[("Type", .name "MCR"), ("Pg", .ref (t.pageId p) 0), ("MCID", .int m)]]
    | .leaf _ => #[]
  let optText (key : String) : Option String → Array (String × PdfRead.Obj)
    | some v => #[(key, litObj (pdfTextString v))]
    | none => #[]
  let structElemObj (e : StructElem) : PdfRead.Obj :=
    let parentRef : PdfRead.Obj := match e.parent with
      | some p => elemRef p
      | none => .ref t.structTreeRoot 0
    let kids := e.kids.flatMap kidObj
    let kidsEntry : Array (String × PdfRead.Obj) :=
      if kids.isEmpty then #[] else #[("K", .arr kids)]
    let attrsEntry : Array (String × PdfRead.Obj) := if e.attrs.isEmpty then #[] else
      #[("A", .dict e.attrs)]
    let nsEntry : Array (String × PdfRead.Obj) :=
      if e.ns20 && !v17 then #[("NS", .ref t.namespaceId 0)] else #[]
    .dict (#[("Type", PdfRead.Obj.name "StructElem"), ("S", .name e.s), ("P", parentRef)]
      ++ nsEntry ++ kidsEntry
      ++ optText "Alt" e.alt ++ optText "Lang" e.lang ++ optText "ActualText" e.actualText
      ++ attrsEntry)
  let structObjs : List (Nat × PdfRead.Obj) :=
    [(t.structTreeRoot, structRoot), (t.parentTree, parentTreeObj), (t.namespaceId, namespaceObj)]
    ++ es.toList.zipIdx.map fun (e, i) => (t.structElemId i, structElemObj e)
  let compressed : List (Nat × PdfRead.Obj) :=
    [(1, catalog), (2, pagesObj)] ++ fontObjs ++ [(t.infoId, infoDict)] ++ outlineObjs ++
    (List.range np).map (fun i => (t.pageId i, pageDict i)) ++ structObjs

  -- object stream payload
  let packed := objectStream compressed
  let objStmData := packed.bytes
  let first := packed.header.utf8ByteSize

  -- assemble the file: every object as a row first, then one `serialize`
  -- fold whose offsets are its own (`serialize_locs_covers`). Nothing
  -- records a position beside the writing any more.
  let fileHead : ByteArray := (if v17 then "%PDF-1.7\n%" else "%PDF-2.0\n%").toUTF8 ++
    ⟨#[0xE2, 0xE3, 0xCF, 0xD3]⟩ ++ "\n".toUTF8

  -- direct stream objects
  -- Every stream this writer owns (content, ToUnicode, font files, XMP, the
  -- object and cross-reference streams) rides as a real deflate whenever
  -- that is smaller, filter declared. Image payloads and copied form graphs
  -- carry their own filters and stay uncompressed here.
  let zRow (id : Nat) (dict : String) (data z : ByteArray) : Row :=
    if z.size < data.size then ⟨id, .stream (dict ++ " /Filter /FlateDecode") z⟩
    else ⟨id, .stream dict data⟩
  let flateRow (id : Nat) (dict : String) (data : ByteArray) : Row :=
    zRow id dict data (Flate.deflate data)
  let mut rows : Array Row := #[]

  -- A page's stream, and its deflate when the driver already holds one
  -- (`pageStreams`): the choice of spelling is `zRow`'s either way, so a
  -- cache hit and a recomputation write the same bytes.
  for i in [0:np] do
    let (data, z?) := match streams[i]?, ops[i]? with
      | some s, _ => s
      | none, some o => ((render o).toUTF8, none)
      | none, none => (ByteArray.empty, none)
    rows := rows.push (match z? with
      | some z => zRow (t.contentId i) "" data z
      | none => flateRow (t.contentId i) "" data)

  -- Image XObjects. A PNG's raw IDAT stream passes through as
  -- `/FlateDecode` with the PNG predictor declared (ISO 32000-2 §7.4.4.4:
  -- Predictor 15, with Colors/BitsPerComponent/Columns describing the
  -- scanlines); a decoded-and-re-encoded plane needs no predictor; a JPEG
  -- embeds whole as `/DCTDecode`. An alpha plane rides as its own gray
  -- XObject named by `/SMask`.
  for ((k, imgId), n) in (usedImgs.zip t.imgIds).zipIdx do
    if let some inf := (imgs.get? k).bind (·.info) then
      match inf.form, (t.formBases[n]?).join with
      | some f, some base =>
        -- A PDF page: a form XObject (ISO 32000-2 §8.10) whose /Matrix
        -- normalizes the page box to the unit square, so the same
        -- `cm w 0 0 h x y … Do` the raster path writes places it —
        -- `form_bbox_exact` is the statement. The copied resource graph
        -- follows, renumbered from `base`; `resources_closed` says no
        -- hole dangles.
        let fv := f.val
        let bw := fv.w
        let bh := fv.h
        let bbox := s!"[{Sp.toPtString fv.x0} {Sp.toPtString fv.y0} \
{Sp.toPtString fv.x1} {Sp.toPtString fv.y1}]"
        let matrix := s!"[{ratString spPerPt bw} 0 0 {ratString spPerPt bh} \
{ratString (-fv.x0) bw} {ratString (-fv.y0) bh}]"
        rows := rows.push ⟨imgId, .form s!"<< /Type /XObject /Subtype /Form \
/BBox {bbox} /Matrix {matrix} /Resources " (renderChunks base fv.resources) fv.content⟩
        for (o, l) in fv.objects.zipIdx do
          rows := rows.push ⟨base + l, .copied (renderChunks base o.chunks) o.stream⟩
      | _, _ =>
        -- The plan's three sums, spelled (ISO 32000-2 §8.9.5 Table 87).
        -- `iccBased` writes its alternate device space until the
        -- emission slice allocates the profile stream; the default
        -- parameters never plan it (`Image.plan_losses_accounts`).
        let deviceOf (n : Nat) : String :=
          if n == 1 then "/DeviceGray" else if n == 4 then "/DeviceCMYK" else "/DeviceRGB"
        let colorSpace := match inf.color with
          | .gray => "/DeviceGray"
          | .rgb => "/DeviceRGB"
          | .indexed palette => Id.run do
            let mut hex := ""
            for byte in palette do
              hex := hex.push (hexDigit (byte.toNat / 16))
              hex := hex.push (hexDigit byte.toNat)
            return s!"[/Indexed /DeviceRGB {palette.size / 3 - 1} <{hex}>]"
          | .iccBased n _ => deviceOf n
        let filter := match inf.filter with
          | .flatePredictor =>
            s!"/Filter /FlateDecode /DecodeParms << /Predictor 15 \
/Colors {inf.color.components} /BitsPerComponent {inf.bitDepth} /Columns {inf.pxW} >>"
          | .dct => "/Filter /DCTDecode"
        let smaskRef := match (t.smaskIds[n]?).join with
          | some mid => s!" /SMask {mid} 0 R"
          | none => ""
        -- Colour-key masking (ISO 32000-2 §8.9.6.4): the ranges in sample
        -- units, a PNG tRNS carried exactly (`Image.colorKeyRanges_between`
        -- keeps every value inside the bit depth).
        let maskRef := match inf.alpha with
          | .colorKey ranges => s!" /Mask [{" ".intercalate (ranges.toList.map toString)}]"
          | .opaque => ""
          | .soft _ _ => ""
        let dict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace {colorSpace} /BitsPerComponent {inf.bitDepth}\
{smaskRef}{maskRef} {filter}"
        rows := rows.push ⟨imgId, .stream dict inf.data⟩
        if let some mid := (t.smaskIds[n]?).join then
          if let .soft plane bpc := inf.alpha then
            -- The alpha plane is the source's own filtered rows, deinterleaved
            -- (`Image.splitPredictedAlpha`), so the mask declares the same PNG
            -- predictor its colour plane does (ISO 32000-2 §7.4.4.4).
            let mdict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace /DeviceGray /BitsPerComponent {bpc} /Filter /FlateDecode \
/DecodeParms << /Predictor 15 /Colors 1 /BitsPerComponent {bpc} /Columns {inf.pxW} >>"
            rows := rows.push ⟨mid, .stream mdict plane⟩

  for k in [0:nf] do
    let font := fs.get keep[k]!
    let prog := (programs[k]?.map (·.1)).getD font.data
    let tuData := (toUnicode usedPerFont[k]!).toUTF8
    rows := rows.push (flateRow (ObjTable.toUniId k) "" tuData)
    let ffDict := if font.isCff then "/Subtype /OpenType" else s!"/Length1 {prog.size}"
    -- The driver may have deflated this program already, through its
    -- content-hash cache; the writer then only picks the smaller spelling.
    rows := rows.push (match fs.zdata[keep[k]!]?.getD none with
      | some z => zRow (t.fileId k) ffDict prog z
      | none => flateRow (t.fileId k) ffDict prog)

  rows := rows.push (flateRow t.xmpId "/Type /Metadata /Subtype /XML" (xmpPacket info).toUTF8)
  rows := rows.push (flateRow t.objStmId
    s!"/Type /ObjStm /N {compressed.length} /First {first}" objStmData)

  -- One fold: the bytes and the offsets together, the offsets its own
  -- (`serialize_locs_covers`). The by-id table below is an index into that
  -- answer, not a second record of it.
  let (body, locs) := serialize fileHead rows
  let mut offs : Array (Option Nat) := Array.replicate t.size none
  for (id, off) in locs do
    if id < offs.size then
      offs := offs.set! id (some off)
  -- Where the object stream holds each compressed object, by id.
  let mut stmIdx : Array (Option Nat) := Array.replicate t.size none
  for ((id, _), idx) in compressed.zipIdx do
    stmIdx := stmIdx.set! id (some idx)
  let compressedIdx (id : Nat) : Option Nat := (stmIdx[id]?).join

  -- Cross-reference stream, W [1 4 2] (ISO 32000-2 §7.5.8.3): row 0 is the
  -- free-list head, written once; then one row per id the table allocates,
  -- in its order (`objTable_ids_exact`: exactly `[1, size)`), each row's
  -- kind the table's answer.
  let xrefOff := body.size
  let xrefRows := Xref.encode
    (xrefEntries t compressedIdx (fun id => (offs[id]?).join) xrefOff)
  let idA := Flate.hex16 (Flate.fnv64 14695981039346656037 body)
  let idB := Flate.hex16 (Flate.fnv64 1099511628211 body)
  let xrefDict := s!"/Type /XRef /Size {t.size} /W [1 4 2] /Index [0 {t.size}] /Root 1 0 R /Info {t.infoId} 0 R /ID [<{idA}> <{idB}>]"
  let (out, _) := serialize body #[flateRow t.xrefId xrefDict xrefRows]
  return out ++ (s!"startxref\n{xrefOff}\n%%EOF\n").toUTF8

end LeanTex.Core.Pdf
