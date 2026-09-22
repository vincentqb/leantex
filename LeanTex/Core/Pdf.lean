import LeanTex.Core.Dim
import LeanTex.Core.Flate
import LeanTex.Core.Font
import LeanTex.Core.HtmlDoc
import LeanTex.Core.Layout
import LeanTex.Core.PdfContent
import LeanTex.Core.PdfStruct

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

/-- Used glyphs for one font: one char witness per gid, ascending gid. Mark
array — the glyph stream is large (every glyph on every page), so no sorting. -/
private def usedGlyphs (fontIdx numGlyphs : Nat) (pages : Array PageOut) :
    Array (Nat × Char) := Id.run do
  let mut seen : Array (Option Char) := Array.replicate numGlyphs none
  for p in pages do
    for l in p.lines do
      for s in l.segs do
        if let .run idx _ _ _ glyphs _ _ _ _ _ := s then
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
      | .run _ _ link w _ segSize _ _ _ _ =>
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
      | .gap w _ => x := x + w
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

/-- The catalog's tagging entries: `/MarkInfo << /Marked true >>` (§14.7.1
— the file's content is marked) and the structure tree root. Spelled
unconditionally: every PDF this writer ships is tagged, whatever the
document declares — tagging is a fact of the artifact, the profile claim
(`pdfuaid`) is a separate, withheld statement. -/
def markedEntry (structTreeRoot : Nat) : String :=
  " /MarkInfo << /Marked true >> /StructTreeRoot " ++ toString structTreeRoot ++ " 0 R"

/-- The document catalog (ISO 32000-2 §7.7.2): the page tree, an outline
when the layout carried one, the XMP metadata stream, the declared
language, the mark information and structure tree root, and
`/ViewerPreferences /DisplayDocTitle` — the reader's window titles from
the document's own metadata title rather than its file name (§12.2;
PDF/UA requires it). -/
def viewerEntry : String := " /ViewerPreferences << /DisplayDocTitle true >> >>"

def catalogDict (outlinesRef : String) (xmpId : Nat) (lang : Option String)
    (structTreeRoot : Nat) : String :=
  s!"<< /Type /Catalog /Pages 2 0 R{outlinesRef} /Metadata {xmpId} 0 R"
    ++ langEntry lang ++ markedEntry structTreeRoot ++ viewerEntry

/-- The PDF twin of `emit_lang_declared`: the catalog is the language
entry of the document's declared tag between two fixed dictionary halves,
by construction — so `/Lang` appears exactly when the document declares a
language, reading the same `Ir.Meta` field as the HTML root's `lang`.
The webMetaChecks census in Tests/Backends is the wiring witness that
`write` ships this dictionary. -/
theorem pdf_lang_declared (outlinesRef : String) (xmpId : Nat) (lang : Option String)
    (structTreeRoot : Nat) :
    ∃ pre post,
      catalogDict outlinesRef xmpId lang structTreeRoot = pre ++ langEntry lang ++ post :=
  ⟨s!"<< /Type /Catalog /Pages 2 0 R{outlinesRef} /Metadata {xmpId} 0 R",
   markedEntry structTreeRoot ++ viewerEntry, by
    simp only [catalogDict, String.append_assoc]⟩

/-- **`pdf_marked_declared`** (the `pdf_lang_declared` shape): the catalog
carries `/MarkInfo << /Marked true >>` and `/StructTreeRoot` between two
fixed halves, whatever the language, the outline, or the document declares
— tagging is unconditional. The structTreeChecks round trip in
Tests/Backends is the wiring witness that `write` ships this dictionary
with a tree behind the reference. -/
theorem pdf_marked_declared (outlinesRef : String) (xmpId : Nat) (lang : Option String)
    (structTreeRoot : Nat) :
    ∃ pre post,
      catalogDict outlinesRef xmpId lang structTreeRoot
        = pre ++ " /MarkInfo << /Marked true >> /StructTreeRoot "
          ++ toString structTreeRoot ++ " 0 R" ++ post :=
  ⟨s!"<< /Type /Catalog /Pages 2 0 R{outlinesRef} /Metadata {xmpId} 0 R" ++ langEntry lang,
   viewerEntry, by
    simp only [catalogDict, markedEntry, String.append_assoc]⟩

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
`pageStreams` renders, before spelling. -/
def pageOps (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store := {}) (tree : Struct.Tree := ⟨#[]⟩) : Array (Array ContentOp) :=
  let remap := remapOf fs (keepFaces fs pages)
  let imgMap := imgMapOf imgs (usedImagesOf imgs pages)
  let tags := tagsOf tree
  pages.map (contentOps geom remap imgMap tags)

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
    | none => if inf.smask.isEmpty then .plain else .alpha
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
    (placedImages imgs pages).any (fun i => i.format == .png && i.predictor)
      || (tableOf fs pages imgs outline).smaskIds.any Option.isSome
  | .dct => (placedImages imgs pages).any (·.format == .jpeg)
  | .smask => (tableOf fs pages imgs outline).smaskIds.any Option.isSome
  | .formXObject => (tableOf fs pages imgs outline).formBases.any Option.isSome
  | .copiedGraph => (tableOf fs pages imgs outline).formSizes.any (· > 0)
  | .cidFontType0 => (keepFaces fs pages).any fun k => (fs.get k).isCff
  | .cidFontType2 => (keepFaces fs pages).any fun k => !(fs.get k).isCff
  | .linkURI =>
    pages.any (fun p => !(linkRects geom p).isEmpty)
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
  placedImages (imgs : Image.Store) (pages : Array PageOut) : Array Image.Info :=
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

/-- Serialize positioned pages into a PDF 2.0 file: cross-reference stream,
object streams, one Identity-H CID font per face actually used (fully
embedded, with its own ToUnicode), image XObjects for every image actually
placed, the structure tree projected from `tree`, and the document
information the source declared (Info dictionary plus XMP). `streams` and
`ops` are the driver's cache path: the page operators it built through
`pageOps` (one walk, not two) and their rendered and deflated bytes. -/
def write (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta := {}) (imgs : Image.Store := {})
    (outline : Array OutlineEntry := #[])
    (streams : Array (ByteArray × Option ByteArray) := #[])
    (tree : Struct.Tree := ⟨#[]⟩) (ops : Array (Array ContentOp) := #[]) : ByteArray := Id.run do
  let np := pages.size
  -- Only faces that actually contribute glyphs are embedded — `keepFaces`,
  -- the very function `html_fonts_cover_pdf` quantifies over, so the
  -- contract holds of the writer's own decision, not a copy. `allUsed`
  -- stays for the per-face glyph census the kept faces subset.
  let allUsed : Array (Array (Nat × Char)) :=
    (Array.range fs.fonts.size).map fun k => usedGlyphs k (fs.get k).numGlyphs pages
  let keep : Array Nat := keepFaces fs pages
  let remap := remapOf fs keep
  let usedPerFont : Array (Array (Nat × Char)) := keep.map fun k => allUsed[k]!
  let nf := keep.size
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
  let ops := if ops.size == np then ops else pages.map (contentOps geom remap imgMap tags)
  let marks := ops.map pageMarks
  let es := fill sk (leafPagesOf nLeaves marks)
  let parentTree := parentTreeOf marks (leafOwners sk nLeaves)
  -- Every object id, from the one table: `objTable_ids_exact` says its
  -- ids tile `[1, size)`, so the cross-reference can be built without a
  -- second pass and no row is left to a default.
  let t := objTable keep imgs usedImgs np nOut es.size

  -- compressed (non-stream) objects, serialized bare
  let kids := String.intercalate " " ((List.range np).map fun i => s!"{t.pageId i} 0 R")
  let outlinesRef := if nOut == 0 then "" else s!" /Outlines {t.outlineRootId} 0 R"
  -- The catalog: `catalogDict`, whose `/Lang` is `pdf_lang_declared`'s
  -- statement — present exactly when the document declares a language.
  let catalog := catalogDict outlinesRef t.xmpId info.language t.structTreeRoot
  let pagesObj := s!"<< /Type /Pages /Kids [{kids}] /Count {np} >>"
  let fontResources := String.intercalate " "
    ((List.range nf).map fun k => s!"/F{k + 1} {ObjTable.type0Id k} 0 R")
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
    [(ObjTable.type0Id k,
      s!"<< /Type /Font /Subtype /Type0 /BaseFont /{baseFont} /Encoding /Identity-H /DescendantFonts [{ObjTable.cidId k} 0 R] /ToUnicode {ObjTable.toUniId k} 0 R >>"),
     (ObjTable.cidId k,
      s!"<< /Type /Font /Subtype /{cidSubtype} /BaseFont /{baseFont} /CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >> /FontDescriptor {ObjTable.fdId k} 0 R /DW 1000 /W {wArray font used}{cidToGid} >>"),
     (ObjTable.fdId k,
      s!"<< /Type /FontDescriptor /FontName /{baseFont} /Flags {flags} /FontBBox [-1000 {descent1000} 2000 {ascent1000}] /ItalicAngle {italicAngle} /Ascent {ascent1000} /Descent {descent1000} /CapHeight {capHeight1000} /StemV {stemV} /{fontFileKey} {t.fileId k} 0 R >>")]
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
        (t.imgIds.toList.zipIdx.map fun (id, n) => s!"/Im{n + 1} {id} 0 R") ++ " >>"
    -- `/StructParents` (§14.7.5.4): the page's key in the parent tree,
    -- under which its marked-content identifiers map back to elements.
    s!"<< /Type /Page /Parent 2 0 R /MediaBox {media.render}{boxes} /Resources << /Font << {fontResources} >>{xobj} >>{annots i} /Contents {t.contentId i} 0 R /StructParents {i} >>"
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
      (t.outlineRootId,
        s!"<< /Type /Outlines /First {t.outlineItemId 0} 0 R /Last {t.outlineItemId (nOut - 1)} 0 R /Count {nOut} >>") ::
      outline.toList.zipIdx.map fun (e, k) =>
        let prev := if k == 0 then "" else s!" /Prev {t.outlineItemId (k - 1)} 0 R"
        let next := if k + 1 == nOut then "" else s!" /Next {t.outlineItemId (k + 1)} 0 R"
        let target := match e.page, e.url with
          | some p, _ => s!" /Dest [{t.pageId p} 0 R /XYZ null null null]"
          | none, some u => s!" /A << /S /URI /URI ({pdfString u}) >>"
          | none, none => ""
        (t.outlineItemId k,
          s!"<< /Title {pdfTextString e.title} /Parent {t.outlineRootId} 0 R{prev}{next}{target} >>")
  -- The structure tree (§14.7): the root over the `Document` element, the
  -- parent tree as one number-tree node keyed by page (`/StructParents`),
  -- the PDF 2.0 namespace the elements name (§14.7.4 — `Title`, `FENote`,
  -- `Hn` past 6 are 2.0 types; a type 2.0 dropped stays in the default
  -- 1.7 namespace by naming none), and one dictionary per element:
  -- its type, parent, kids as marked-content references (`/MCR`, §14.7.5.3
  -- — the page travels with the identifier, so an element may span
  -- pages), and the alternative or language it carries.
  let elemRef (i : Nat) : String := s!"{t.structElemId i} 0 R"
  let structRoot :=
    s!"<< /Type /StructTreeRoot /K [{elemRef 0}] /ParentTree {t.parentTree} 0 R \
/ParentTreeNextKey {np} /Namespaces [{t.namespaceId} 0 R] >>"
  let parentEntry (i : Nat) : String :=
    let refs := (parentTree[i]?.getD #[]).toList.map fun o => match o with
      | some e => elemRef e
      | none => "null"
    s!"{i} [{String.intercalate " " refs}]"
  let parentTreeObj :=
    "<< /Nums [" ++ String.intercalate " " ((List.range np).map parentEntry) ++ "] >>"
  let namespaceObj := "<< /Type /Namespace /NS (http://iso.org/pdf2/ssn) >>"
  let kidRef (k : StructKid) : String := match k with
    | .elem i => elemRef i
    | .mcid p m => s!"<< /Type /MCR /Pg {t.pageId p} 0 R /MCID {m} >>"
    -- a placeholder `fill` did not replace: none remain after `fill`, and
    -- one would be a leaf with no marked content, which lists nothing
    | .leaf _ => ""
  let optText (key : String) : Option String → String
    | some v => s!" /{key} {pdfTextString v}"
    | none => ""
  let structElemObj (e : StructElem) : String :=
    let parentRef := match e.parent with
      | some p => elemRef p
      | none => s!"{t.structTreeRoot} 0 R"
    let kids := (e.kids.toList.map kidRef).filter (· != "")
    let kidsEntry := if kids.isEmpty then "" else s!" /K [{String.intercalate " " kids}]"
    let attrsEntry := if e.attrs.isEmpty then "" else
      " /A << " ++ String.intercalate " " (e.attrs.toList.map fun (k, v) => s!"/{k} {v}") ++ " >>"
    let nsEntry := if e.ns20 then s!" /NS {t.namespaceId} 0 R" else ""
    s!"<< /Type /StructElem /S /{e.s} /P {parentRef}{nsEntry}{kidsEntry}\
{optText "Alt" e.alt}{optText "Lang" e.lang}{optText "ActualText" e.actualText}{attrsEntry} >>"
  let structObjs : List (Nat × String) :=
    [(t.structTreeRoot, structRoot), (t.parentTree, parentTreeObj), (t.namespaceId, namespaceObj)]
    ++ es.toList.zipIdx.map fun (e, i) => (t.structElemId i, structElemObj e)
  let compressed : List (Nat × String) :=
    [(1, catalog), (2, pagesObj)] ++ fontObjs ++ [(t.infoId, infoDict)] ++ outlineObjs ++
    (List.range np).map (fun i => (t.pageId i, pageDict i)) ++ structObjs

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
  -- The byte offset of every object written directly, by id. The kind of
  -- each row is `t.kindOf`'s, never read from here.
  let mut offs : Array (Option Nat) := Array.replicate t.size none
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
  -- The same, compressed: every stream this writer owns (content,
  -- ToUnicode, font files, XMP, the object and cross-reference streams)
  -- rides as a real deflate whenever that is smaller, filter declared.
  -- Image payloads and copied form graphs carry their own filters and
  -- stay on `putStream`.
  let putZ (w : Wr) (id : Nat) (dict : String) (data z : ByteArray) : Wr × Nat :=
    if z.size < data.size then
      putStream w id (dict ++ " /Filter /FlateDecode") z
    else
      putStream w id dict data
  let putFlate (w : Wr) (id : Nat) (dict : String) (data : ByteArray) : Wr × Nat :=
    putZ w id dict data (Flate.deflate data)

  -- A page's stream, and its deflate when the driver already holds one
  -- (`pageStreams`): the choice of spelling is `putZ`'s either way, so a
  -- cache hit and a recomputation write the same bytes.
  for i in [0:np] do
    let (data, z?) := match streams[i]?, ops[i]? with
      | some s, _ => s
      | none, some o => ((render o).toUTF8, none)
      | none, none => (ByteArray.empty, none)
    let (w', off) := match z? with
      | some z => putZ w (t.contentId i) "" data z
      | none => putFlate w (t.contentId i) "" data
    w := w'
    offs := offs.set! (t.contentId i) (some off)

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
        let off := w.out.size
        w := w.put s!"{imgId} 0 obj\n<< /Type /XObject /Subtype /Form \
/BBox {bbox} /Matrix {matrix} /Resources "
        w := w.putB (renderChunks base fv.resources)
        w := w.put s!" /Length {fv.content.size} >>\nstream\n"
        w := w.putB fv.content
        w := w.put "\nendstream\nendobj\n"
        offs := offs.set! imgId (some off)
        for (o, l) in fv.objects.zipIdx do
          let ooff := w.out.size
          w := w.put s!"{base + l} 0 obj\n"
          w := w.putB (renderChunks base o.chunks)
          match o.stream with
          | some raw =>
            w := w.put "\nstream\n"
            w := w.putB raw
            w := w.put "\nendstream\nendobj\n"
          | none =>
            w := w.put "\nendobj\n"
          offs := offs.set! (base + l) (some ooff)
      | _, _ =>
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
          -- Unreachable through `Image.decode`: a `.pdf` Info carries its
          -- form and takes the arm above. The raster dictionary it would
          -- describe does not exist.
          | .pdf => ""
        let smaskRef := match (t.smaskIds[n]?).join with
          | some mid => s!" /SMask {mid} 0 R"
          | none => ""
        -- Colour-key masking (ISO 32000-2 §8.9.6.4): the ranges in sample
        -- units, a PNG tRNS carried exactly (`Image.colorKeyRanges_between`
        -- keeps every value inside the bit depth).
        let maskRef := if inf.colorKey.isEmpty then ""
          else s!" /Mask [{" ".intercalate (inf.colorKey.toList.map toString)}]"
        let dict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace {colorSpace} /BitsPerComponent {inf.bitDepth}\
{smaskRef}{maskRef} {filter}"
        let (w', off) := putStream w imgId dict inf.data
        w := w'
        offs := offs.set! imgId (some off)
        if let some mid := (t.smaskIds[n]?).join then
          -- The alpha plane is the source's own filtered rows, deinterleaved
          -- (`Image.splitPredictedAlpha`), so the mask declares the same PNG
          -- predictor its colour plane does (ISO 32000-2 §7.4.4.4).
          let mdict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace /DeviceGray /BitsPerComponent 8 /Filter /FlateDecode \
/DecodeParms << /Predictor 15 /Colors 1 /BitsPerComponent 8 /Columns {inf.pxW} >>"
          let (w'', moff) := putStream w mid mdict inf.smask
          w := w''
          offs := offs.set! mid (some moff)

  for k in [0:nf] do
    let font := fs.get keep[k]!
    let tuData := (toUnicode usedPerFont[k]!).toUTF8
    let (w', tuOff) := putFlate w (ObjTable.toUniId k) "" tuData
    w := w'
    offs := offs.set! (ObjTable.toUniId k) (some tuOff)
    let ffDict := if font.isCff then "/Subtype /OpenType" else s!"/Length1 {font.data.size}"
    -- The driver may have deflated this face already, through its
    -- content-hash cache; the writer then only picks the smaller spelling.
    let (w'', ffOff) := match fs.zdata[keep[k]!]?.getD none with
      | some z => putZ w (t.fileId k) ffDict font.data z
      | none => putFlate w (t.fileId k) ffDict font.data
    w := w''
    offs := offs.set! (t.fileId k) (some ffOff)

  let (wx, xmpOff) := putFlate w t.xmpId "/Type /Metadata /Subtype /XML"
    (xmpPacket info).toUTF8
  w := wx
  offs := offs.set! t.xmpId (some xmpOff)

  let (w3, osOff) := putFlate w t.objStmId
    s!"/Type /ObjStm /N {compressed.length} /First {first}" objStmData.toUTF8
  w := w3
  offs := offs.set! t.objStmId (some osOff)
  -- Where the object stream holds each compressed object, by id.
  let mut stmIdx : Array (Option Nat) := Array.replicate t.size none
  for ((id, _), idx) in compressed.zipIdx do
    stmIdx := stmIdx.set! id (some idx)
  let compressedIdx (id : Nat) : Option Nat := (stmIdx[id]?).join

  -- Cross-reference stream, W [1 4 2] (ISO 32000-2 §7.5.8.3): row 0 is the
  -- free-list head, written once; then one row per id the table allocates,
  -- in its order (`objTable_ids_exact`: exactly `[1, size)`), each row's
  -- kind the table's answer.
  let xrefOff := w.out.size
  let be4 (v : Nat) : List UInt8 :=
    [UInt8.ofNat (v / 16777216), UInt8.ofNat (v / 65536 % 256),
     UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)]
  let directRow (off : Nat) : ByteArray := ⟨(1 :: be4 off ++ [0, 0]).toArray⟩
  let streamRow (idx : Nat) : ByteArray :=
    ⟨(2 :: be4 t.objStmId ++ [UInt8.ofNat (idx / 256 % 256), UInt8.ofNat (idx % 256)]).toArray⟩
  let mut rows : ByteArray := ⟨#[0, 0, 0, 0, 0, 0xFF, 0xFF]⟩
  for h : id in t.ids do
    match hk : t.kindOf compressedIdx id with
    | some .xref => rows := rows ++ directRow xrefOff
    | some (.inStream idx) => rows := rows ++ streamRow idx
    | some .direct =>
      match (offs[id]?).join with
      | some off => rows := rows ++ directRow off
      | none =>
        -- A direct id whose object was never recorded is written free: the
        -- file then says the object is absent, which the read-side census
        -- sees (its objects are the table's ids, per fixture), instead of a
        -- row pointing into the object stream at another object. Gone with
        -- the serialize split, where the offset arrives with the object.
        rows := rows ++ ⟨#[0, 0, 0, 0, 0, 0, 0]⟩
    | none =>
      have hs : (t.kindOf compressedIdx id).isSome = true :=
        objTable_kindOf_some keep imgs usedImgs np nOut es.size compressedIdx id h
      rows := absurd hs (by rw [hk]; exact Bool.false_ne_true)
  let idA := Flate.hex16 (Flate.fnv64 14695981039346656037 w.out)
  let idB := Flate.hex16 (Flate.fnv64 1099511628211 w.out)
  let xrefDict := s!"/Type /XRef /Size {t.size} /W [1 4 2] /Index [0 {t.size}] /Root 1 0 R /Info {t.infoId} 0 R /ID [<{idA}> <{idB}>]"
  let w4 := (putFlate w t.xrefId xrefDict rows).1
  w := w4
  w := w.put s!"startxref\n{xrefOff}\n%%EOF\n"
  return w.out

end LeanTex.Core.Pdf
