module

public import LeanTex.Core.Dim
import LeanTex.Core.Flate
import LeanTex.Core.FigureLoss
public import LeanTex.Core.Font
import LeanTex.Core.FontSubset
import LeanTex.Core.Html
public import LeanTex.Core.Layout
import LeanTex.Core.Loop
public import LeanTex.Core.PdfContent
public import LeanTex.Core.PdfFigures
public import LeanTex.Core.PdfStruct
public import LeanTex.Core.PdfXref

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Layout

/-- A rectangle in PDF user space: lower-left and upper-right corners. -/
public structure Rect where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving Repr, BEq

/-- Containment, the relation ISO 32000-2 expects between the page boxes. -/
public def Rect.within (inner outer : Rect) : Prop :=
  outer.x0 ≤ inner.x0 ∧ outer.y0 ≤ inner.y0 ∧
  inner.x1 ≤ outer.x1 ∧ inner.y1 ≤ outer.y1

/-- The rectangle's corners in points, spelled as a PDF array. -/
public def Rect.render (r : Rect) : String :=
  s!"[{Sp.toPtString r.x0} {Sp.toPtString r.y0} {Sp.toPtString r.x1} {Sp.toPtString r.y1}]"

private def ptObj (x : Sp) : PdfRead.Obj :=
  let milli := (x.natAbs * 1000 + 32768) / 65536
  if milli % 1000 == 0 then
    .int (if x < 0 then -(milli / 1000 : Int) else (milli / 1000 : Int))
  else .real x.toPtString

private def Rect.obj (r : Rect) : PdfRead.Obj :=
  .arr #[ptObj r.x0, ptObj r.y0, ptObj r.x1, ptObj r.y1]

/-- The MediaBox, BleedBox and TrimBox the declared trim size and bleed imply (ISO 32000-2 §14.11.2). -/
public def pageBoxes (pageW pageH bleed : Int) : Rect × Rect × Rect :=
  (⟨0, 0, pageW + 2 * bleed, pageH + 2 * bleed⟩,
   ⟨0, 0, pageW + 2 * bleed, pageH + 2 * bleed⟩,
   ⟨bleed, bleed, pageW + bleed, pageH + bleed⟩)

public theorem pageBoxes_nest (W H b : Int) (hb : 0 ≤ b) :
    (pageBoxes W H b).2.2.within (pageBoxes W H b).2.1 ∧
    (pageBoxes W H b).2.1.within (pageBoxes W H b).1 ∧
    (pageBoxes W H b).2.2.x1 - (pageBoxes W H b).2.2.x0 = W ∧
    (pageBoxes W H b).2.2.y1 - (pageBoxes W H b).2.2.y0 = H := by
  dsimp only [pageBoxes, Rect.within]
  omega

/-- The PDF 1.7 standard type a 2.0-only structure type is role-mapped onto in a PDF 1.7 file. -/
public def pdf17Role (s : String) : Option String :=
  if s == "Title" then some "P"
  else if s == "FENote" then some "Note"
  else if s == "Aside" then some "Div"
  else if s.startsWith "H" && ((s.drop 1).toString.toNat?.any (6 < ·)) then some "H6"
  else none

private def utf16Hex (c : Char) : String :=
  let n := c.toNat
  if n < 0x10000 then
    Hex.digits true 4 n
  else
    let v := n - 0x10000
    Hex.digits true 4 (0xD800 + v / 1024) ++ Hex.digits true 4 (0xDC00 + v % 1024)

private def litObj (s : String) : PdfRead.Obj := .str s.toUTF8

private def renderChunks (base : Nat) (cs : Array PdfRead.Chunk) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for c in cs do
    match c with
    | .bytes bs => out := out ++ bs
    | .ref l => out := out ++ (s!"{base + l} 0 R").toUTF8
  return out

private def markUsed (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) : Array (Array (Option Char)) :=
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
        -- A drawn figure's text sets in the document's faces, so its glyphs are the file's.
        if let .image (some k) _ _ _ := s then
          if let some fig := (shaped[k]?).join then
            -- A symbol's glyphs are the same however many uses paint it: bodies are read unexpanded.
            let runs := fig.symbols.foldl (fun acc b => Gfx.Node.labelsList Gfx.Affine.unit acc b.toList)
              (Gfx.Node.labelsList Gfx.Affine.unit #[] fig.nodes.toList)
            for (_, r) in runs do
              for (face, g, c, _) in r.glyphs do
                seen := seen.modify face fun marks =>
                  if h : g < marks.size then
                    if marks[g].isNone then marks.set g (some c) else marks
                  else marks
  return seen

/-- Used glyphs per face, one char witness per gid in ascending order: the census embedding reads. -/
public def usedAll (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped)) := #[]) : Array (Array (Nat × Char)) :=
  let seen := markUsed fs pages shaped
  (Array.range fs.fonts.size).map fun k =>
    ((seen[k]?.getD #[]).zipIdx.filterMap fun (c?, g) => c?.map (g, ·))

private theorem usedAll_size_exact (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) :
    (usedAll fs pages shaped).size = fs.fonts.size := by
  simp [usedAll]

/-- The faces the file embeds: those that contribute glyphs, or face 0 when nothing sets text. -/
public def keepOf (used : Array (Array (Nat × Char))) : Array Nat :=
  let keep := (Array.range used.size).filter fun k => !((used[k]?.getD #[]).isEmpty)
  if keep.isEmpty then #[0] else keep

/-- The faces `write` embeds for these pages. -/
public def keepFaces (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped)) := #[]) : Array Nat :=
  keepOf (usedAll fs pages shaped)

/-- The font program embedded for each kept face, subset to the glyphs its pages paint, and whether
it is a subset. -/
public def facePrograms (fs : FontSet) (used : Array (Array (Nat × Char))) : Array (ByteArray × Bool) :=
  (keepOf used).map fun k =>
    let f := fs.get k
    FontSubset.program f ((used[k]?.getD #[]).map (·.1))

private def subsetTag (k : Nat) (used : Array Nat) : String :=
  let h := used.foldl (fun h g => (h * 31 + g + 1) % 456976) 7
  let v := k % 676 * 456976 + h
  String.ofList ((List.range 6).reverse.map fun i => Char.ofNat (65 + v / 26 ^ i % 26))

public theorem keepFaces_lt (fs : FontSet) (pages : Array PageOut)
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

/-- What this writer realizes of the output contract, describing the bytes without shaping them. -/
public def profile : Ir.Realization :=
  { alternatives := .none
    color := .device
    fonts := .embeds
    scripting := .never
    math := .layout }

private def linkRects (geom : Geom) (page : PageOut) :
    Array (Sp × Sp × Sp × Sp × String) := Id.run do
  let mut out : Array (Sp × Sp × Sp × Sp × String) := page.links.map fun r =>
    (geom.bleed + r.x, geom.bleed + geom.pageH - r.y - r.h,
      geom.bleed + r.x + r.w, geom.bleed + geom.pageH - r.y, r.target)
  for l in page.lines do
    let mut x := geom.bleed + l.x
    -- One em of tolerance: runs split by an interword space join one link rectangle.
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
      | .image _ w _ _ => x := x + w
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
      s := s ++ s!"<{Hex.digits true 4 g}> <{utf16Hex c}>\n"
    s := s ++ "endbfchar\n"
  s := s ++ "endcmap
CMapName currentdict /CMap defineresource pop
end
end"
  return s

private def widthObj (μ : Int) : PdfRead.Obj :=
  if μ % 1000 == 0 then .int (μ / 1000) else
    let frs := toString (μ.natAbs % 1000)
    let frs := (("".pushn '0' (3 - frs.length)) ++ frs).dropEndWhile (· == '0')
    .real s!"{μ / 1000}.{frs}"

private def wArray (font : Font) (used : Array (Nat × Char)) : PdfRead.Obj :=
  .arr (used.flatMap fun (g, _) => #[PdfRead.Obj.int g, .arr #[widthObj (pdfWidthμ font g)]])

private def pdfString (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c == '(' || c == ')' || c == '\\' then
      out := out.push '\\'
    out := out.push c
  return out

private def pdfTextString (s : String) : String :=
  if s.toList.all (fun c => c.toNat < 0x80) then s!"({pdfString s})"
  else s.toList.foldl (· ++ utf16Hex ·) "<FEFF" ++ ">"

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
  -- The canonical URL as dc:identifier (XMP Specification Part 1 §8.3), simple Text.
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

/-- The catalog's `/Lang` from the declared language tag (ISO 32000-2 §14.9.2.2), none when undeclared. -/
public def langEntry : Option String → Array (String × PdfRead.Obj)
  | some tag => #[("Lang", .str s!"({pdfString tag})".toUTF8)]
  | none => #[]

/-- The catalog's tagging entries, `/MarkInfo << /Marked true >>` and the structure tree root,
present unconditionally. -/
public def markedEntry (structTreeRoot : Nat) : Array (String × PdfRead.Obj) :=
  #[("MarkInfo", .dict #[("Marked", .bool true)]), ("StructTreeRoot", .ref structTreeRoot 0)]

private def viewerEntry : Array (String × PdfRead.Obj) :=
  #[("ViewerPreferences", .dict #[("DisplayDocTitle", .bool true)])]

/-- The document catalog (ISO 32000-2 §7.7.2) as a typed object. -/
public def catalogDict (outlineRoot : Option Nat) (xmpId : Nat) (lang : Option String)
    (structTreeRoot : Nat) : PdfRead.Obj :=
  .dict (#[("Type", .name "Catalog"), ("Pages", .ref 2 0)]
    ++ (match outlineRoot with
        | some r => #[("Outlines", PdfRead.Obj.ref r 0)]
        | none => #[])
    ++ #[("Metadata", .ref xmpId 0)]
    ++ langEntry lang ++ markedEntry structTreeRoot ++ viewerEntry)

public theorem pdf_lang_declared (outlineRoot : Option Nat) (xmpId : Nat) (lang : Option String)
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

public theorem pdf_marked_declared (outlineRoot : Option Nat) (xmpId : Nat) (lang : Option String)
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

private def remapOf (fs : FontSet) (keep : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate fs.fonts.size 0
  for (old, new) in keep.zipIdx do
    r := r.set! old new
  return r

private def usedImagesOf (imgs : Image.Store) (pages : Array PageOut) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for p in pages do
    for l in p.lines do
      for s in l.segs do
        if let .image (some k) _ _ _ := s then
          if ((imgs.get? k).bind (·.info)).isSome && ((imgs.get? k).all (·.vector.isNone)) &&
              !out.contains k then
            out := out.push k
          for r in ((imgs.get? k).map (·.rasterSlots)).getD #[] do
            if ((imgs.get? r).bind (·.info)).isSome && !out.contains r then
              out := out.push r
  return out

private def imgMapOf (imgs : Image.Store) (used : Array Nat) : Array (Option Nat) := Id.run do
  let mut m : Array (Option Nat) := Array.replicate imgs.entries.size none
  for (k, n) in used.zipIdx do
    m := m.set! k (some n)
  return m

/-- The structure type each leaf's marked content is tagged with, read off the tree's skeleton. -/
public def tagsOf (tree : Struct.Tree) : Array (Option String) :=
  leafTags (skeleton tree) tree.leaves.size

/-- The resource names figure operators are first written with: every request 0, renamed onto the
figure table before spelling. -/
@[expose] public def figureNames : GfxPdf.Request → Nat := fun _ => 0

/-- A drawn figure's resource names: each raster by the store entry holding it, every other request 0. -/
@[expose] public def rasterNames (imgs : Image.Store) (k : Nat) : GfxPdf.Request → Nat
  | .raster r => ((imgs.get? k).bind fun en => en.rasterSlots[r]?).getD 0
  | .extG _ _ => 0
  | .pattern _ => 0
  | .form _ _ => 0

/-- Whether every raster of the figure at store entry `k` has an entry of its own. -/
@[expose] public def rastersSlotted (imgs : Image.Store) (k : Nat) (fig : Gfx.Figure Gfx.Shaped) : Bool :=
  ((imgs.get? k).map fun en => en.rasterSlots.size == fig.rasters.size &&
    en.rasterSlots.all fun r => ((imgs.get? r).bind (·.info)).isSome).getD fig.rasters.isEmpty

/-- The first page whose ink would paint a raster, which the writer refuses. -/
public def inkRasterPage? (pages : Array PageOut) : Option Nat :=
  pages.findIdx? fun p => p.inks.any fun k => !k.fig.imageFree

/-- The drawn figures the store holds as forms in the kept faces, each raster named by its store
entry and every other resource 0 until the writer names it onto the figure table. -/
public def docFigsWith (fs : FontSet) (keep : Array Nat) (imgs : Image.Store) : Array (Option FigForm) :=
  let remap := remapOf fs keep
  let wt := widthTable fs.fonts keep
  imgs.shaped.mapIdx fun k s => s.map fun fig =>
    -- One raster without an entry of its own drops every raster of the figure, none named without a resource.
    -- premise: Tests.svgRasterFigureChecks — the store slots each raster of a drawn figure
    let fig := if rastersSlotted imgs k fig then fig else FigureLoss.unrastered fig
    { body := figureBody remap wt (rasterNames imgs k) fig, box := fig.box }

/-- The drawn figures for these pages, in the faces `write` keeps. -/
public def docFigs (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store) : Array (Option FigForm) :=
  docFigsWith fs (keepFaces fs pages imgs.shaped) imgs

/-- The drawn figures a page places, by store index, in line order. -/
public def pageFigureForms (figs : Array (Option FigForm)) (p : PageOut) : Array FigForm :=
  p.lines.foldl (fun out l => l.segs.foldl (fun out s => match s with
    | .image (some k) _ _ _ => match (figs[k]?).join with
      | some f => out.push f
      | none => out
    | _ => out) out) #[]

/-- The figure resources a document's pages name, interned by content in page and paint order. -/
public def figureTable (geom : Geom) (pages : Array PageOut) (figs : Array (Option FigForm)) :
    Array FigRes :=
  pages.foldl (fun t p =>
    let t := p.inks.foldl
      (fun t k => collectList t (inkPaint geom figureNames (fun _ => none) k).toList) t
    (pageFigureForms figs p).foldl (fun t f => collectList t [.xobject none 0 .symbol f.body]) t) #[]

/-- Pages' operators with their figure resources named onto the document's
table; unchanged when no figure names one. -/
public def namedPageOps (geom : Geom) (pages : Array PageOut) (figs : Array (Option FigForm))
    (ops : Array (Array ContentOp)) : Array (Array ContentOp) :=
  let t := figureTable geom pages figs
  if t.isEmpty then ops else ops.map (nameOps t)

/-- Whether a table entry is spelled as a form XObject's stream; the others
are dictionaries in the object stream. -/
@[expose] public def FigRes.isForm : FigRes → Bool
  | .form _ _ => true
  | .extG _ _ => false
  | .pattern _ => false
  | .shading _ => false

/-- An entry's place among the table's entries of its own spelling kind:
its slot in the writer's dictionary or form block. -/
public def figRank (t : Array FigRes) (k : Nat) : Nat :=
  let form := (t[k]?.map FigRes.isForm).getD false
  ((t.extract 0 k).filter fun r => r.isForm == form).size

public def figDictCount (t : Array FigRes) : Nat := (t.filter fun r => !r.isForm).size

public def figFormCount (t : Array FigRes) : Nat := (t.filter FigRes.isForm).size

private def ratObj (p q : Int) : PdfRead.Obj :=
  let s := ratString p q
  if s.toList.contains '.' then .real s else .int (s.toInt?.getD 0)

private def rgbObj (c : Ir.Color) : PdfRead.Obj :=
  .arr #[ratObj c.r.toNat 255, ratObj c.g.toNat 255, ratObj c.b.toNat 255]

private def interpObj (c0 c1 : Ir.Color) : PdfRead.Obj :=
  .dict #[("FunctionType", .int 2), ("Domain", .arr #[.int 0, .int 1]), ("C0", rgbObj c0),
    ("C1", rgbObj c1), ("N", .int 1)]

/-- A stop list as a PDF function over [0, 1], padded at both ends: one interpolation per segment
between distinct offsets, stitched (§7.10.4) when there are several. -/
public def stopsFunctionObj (stops : Array Gfx.Stop) : PdfRead.Obj :=
  let black : Ir.Color := { r := 0, g := 0, b := 0 }
  match stops.toList with
  | [] => interpObj black black
  | [s] => interpObj s.color s.color
  | first :: _ =>
    let last := stops.back?.getD first
    let pts : List (Nat × Ir.Color) :=
      (if first.offset.val > 0 then [(0, first.color)] else []) ++
        stops.toList.map (fun s => (s.offset.val, s.color)) ++
        (if last.offset.val < 65536 then [(65536, last.color)] else [])
    let segs := (pts.zip (pts.drop 1)).filter fun (a, b) => a.1 < b.1
    match segs with
    | [] => interpObj first.color first.color
    | [(a, b)] => interpObj a.2 b.2
    | _ =>
      .dict #[("FunctionType", .int 3), ("Domain", .arr #[.int 0, .int 1]),
        ("Functions", .arr (segs.map fun (a, b) => interpObj a.2 b.2).toArray),
        ("Bounds", .arr ((segs.drop 1).map fun (a, _) => ratObj a.1 65536).toArray),
        ("Encode", .arr (segs.flatMap fun _ => [PdfRead.Obj.int 0, .int 1]).toArray)]

/-- A gradient as a shading dictionary in its own frame (§8.7.4.5.3–4),
padded at both ends as SVG pads. -/
public def shadingObj : Gfx.Gradient → PdfRead.Obj
  | .linear p0 p1 stops _ =>
    .dict #[("ShadingType", .int 2), ("ColorSpace", .name "DeviceRGB"),
      ("Coords", .arr #[ptObj p0.1, ptObj p0.2, ptObj p1.1, ptObj p1.2]),
      ("Function", stopsFunctionObj stops), ("Extend", .arr #[.bool true, .bool true])]
  | .radial c0 r0 c1 r1 stops _ =>
    .dict #[("ShadingType", .int 3), ("ColorSpace", .name "DeviceRGB"),
      ("Coords", .arr #[ptObj c0.1, ptObj c0.2, ptObj r0, ptObj c1.1, ptObj c1.2, ptObj r1]),
      ("Function", stopsFunctionObj stops), ("Extend", .arr #[.bool true, .bool true])]

/-- An exact matrix as a PDF array: the linear part as is, the translation
in points. -/
public def matrixObj (m : Gfx.Affine) : PdfRead.Obj :=
  .arr #[ratObj m.a.num m.a.den, ratObj m.b.num m.b.den, ratObj m.c.num m.c.den,
    ratObj m.d.num m.d.den, ratObj m.e.num ((m.e.den : Int) * spPerPt),
    ratObj m.f.num ((m.f.den : Int) * spPerPt)]

/-- A table entry spelled as a dictionary; a form is a stream and has none. -/
public def figDictObj : FigRes → Option PdfRead.Obj
  | .extG a b =>
    some (.dict #[("Type", .name "ExtGState"), ("ca", ratObj a.val 1000), ("CA", ratObj b.val 1000)])
  | .pattern g =>
    some (.dict #[("Type", .name "Pattern"), ("PatternType", .int 2), ("Shading", shadingObj g),
      ("Matrix", matrixObj g.xf)])
  | .shading g => some (shadingObj g)
  | .form _ _ => none

/-- Each kept glyph's `/W` width and outline hull in millionths of the em, by font resource. -/
public def glyphInkOf (fs : FontSet) (keep : Array Nat) : GfxPdf.GlyphInk :=
  { width := fun res g => match keep[res]? with
      | some f => pdfWidthμ (fs.get f) g
      | none => 0
    hull := fun res g => (keep[res]?).map fun f =>
        let font := fs.get f
        let lo (v : Int) : Int := Rat.floor (((v * 1000000 : Int) : Rat) / (font.unitsPerEm : Rat))
        let hi (v : Int) : Int := Rat.ceil (((v * 1000000 : Int) : Rat) / (font.unitsPerEm : Rat))
        match font.bounds g with
        | some b => ((lo b.left, lo b.bottom), (hi b.right, hi b.top))
        | none => ((0, lo font.descent), (hi (font.widths[g]?.getD 0), hi font.ascent)) }

/-- No face: what a reader of forms that set no text needs. -/
@[expose] public def noGlyphInk : GfxPdf.GlyphInk := { width := fun _ _ => 0, hull := fun _ _ => Option.none }

/-- A coordinate in whole points, rounded down. -/
@[expose] public def floorPt (x : Int) : Int :=
  if x ≥ 0 then x / spPerPt else -((-x + spPerPt - 1) / spPerPt)

/-- A form's bounding box in whole points outward, the hull of everything its body paints. -/
public def formBBox (gi : GfxPdf.GlyphInk) (kind : FormKind) (body : Array ContentOp) :
    Int × Int × Int × Int :=
  match GfxPdf.formBox gi kind body with
  | some ((x0, y0), (x1, y1)) => (floorPt x0, floorPt y0, -(floorPt (-x1)), -(floorPt (-y1)))
  | none => (0, 0, 0, 0)

public theorem formBBox_covers (gi : GfxPdf.GlyphInk) (kind : FormKind) (body : Array ContentOp)
    (b : Gfx.Box) (h : GfxPdf.formBox gi kind body = some b) :
    let r := formBBox gi kind body
    r.1 * spPerPt ≤ b.1.1 ∧ r.2.1 * spPerPt ≤ b.1.2 ∧ b.2.1 ≤ r.2.2.1 * spPerPt ∧
      b.2.2 ≤ r.2.2.2 * spPerPt := by
  obtain ⟨⟨x0, y0⟩, ⟨x1, y1⟩⟩ := b
  simp only [formBBox, h]
  have lo (x : Int) : floorPt x * spPerPt ≤ x := by
    unfold floorPt spPerPt
    split <;> omega
  have hi (x : Int) : x ≤ -floorPt (-x) * spPerPt := by
    have := lo (-x)
    unfold spPerPt at *
    omega
  exact ⟨lo x0, lo y0, hi x1, hi y1⟩

private def resourceGroup (key : String) (es : Array (String × PdfRead.Obj)) :
    Array (String × PdfRead.Obj) :=
  if es.isEmpty then #[] else #[(key, .dict es)]

/-- The one resources dictionary every page and figure form names (ISO 32000-2 §7.8.3). -/
public def resourcesDict (fonts : PdfRead.Obj)
    (xobjects extg patterns shadings : Array (String × PdfRead.Obj)) : PdfRead.Obj :=
  .dict (#[("Font", fonts)] ++ resourceGroup "XObject" xobjects ++ resourceGroup "ExtGState" extg ++
    resourceGroup "Pattern" patterns ++ resourceGroup "Shading" shadings)

private theorem resourceGroup_find_none (key k : String) (es : Array (String × PdfRead.Obj))
    (h : key ≠ k) : (resourceGroup key es).find? (·.1 == k) = none := by
  unfold resourceGroup
  split <;> simp [h]

public theorem resourcesDict_untyped_exact (fonts : PdfRead.Obj)
    (xobjects extg patterns shadings : Array (String × PdfRead.Obj)) :
    (resourcesDict fonts xobjects extg patterns shadings).get? "Type" = none ∧
      (resourcesDict fonts xobjects extg patterns shadings).get? "Subtype" = none := by
  simp [resourcesDict, PdfRead.Obj.get?, Array.find?_append,
    resourceGroup_find_none _ _ _ (by decide : "XObject" ≠ "Type"),
    resourceGroup_find_none _ _ _ (by decide : "ExtGState" ≠ "Type"),
    resourceGroup_find_none _ _ _ (by decide : "Pattern" ≠ "Type"),
    resourceGroup_find_none _ _ _ (by decide : "Shading" ≠ "Type"),
    resourceGroup_find_none _ _ _ (by decide : "XObject" ≠ "Subtype"),
    resourceGroup_find_none _ _ _ (by decide : "ExtGState" ≠ "Subtype"),
    resourceGroup_find_none _ _ _ (by decide : "Pattern" ≠ "Subtype"),
    resourceGroup_find_none _ _ _ (by decide : "Shading" ≠ "Subtype")]

public theorem figDictObj_untyped_exact (r : FigRes) :
    ((figDictObj r).getD .null).get? "Type" ≠ some (.name "Font") ∧
      ((figDictObj r).getD .null).get? "Subtype" = none := by
  cases r with
  | extG a b => simp [figDictObj, PdfRead.Obj.get?]
  | pattern g => simp [figDictObj, PdfRead.Obj.get?]
  | shading g => cases g <;> simp [figDictObj, shadingObj, PdfRead.Obj.get?]
  | form k b => simp [figDictObj, PdfRead.Obj.get?]

/-- The resource prefix a table entry's name is spelled with. -/
@[expose] public def FigRes.namePrefix : FigRes → String
  | .extG _ _ => "GS"
  | .pattern _ => "P"
  | .shading _ => "Sh"
  | .form _ _ => "Fm"

/-- Each page's typed operators, resolved against the used faces, images and leaf tags. -/
public def pageOps (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store := {}) (tree : Struct.Tree := ⟨#[]⟩)
    (keep : Array Nat := keepFaces fs pages imgs.shaped) : Array (Array ContentOp) :=
  let remap := remapOf fs keep
  let imgMap := imgMapOf imgs (usedImagesOf imgs pages)
  let tags := tagsOf tree
  let wt := widthTable fs.fonts keep
  let figs := docFigsWith fs keep imgs
  namedPageOps geom pages figs (pages.map (contentOps geom remap wt imgMap tags figureNames figs))

/-- The per-page content streams `write` embeds, uncompressed. -/
public def pageStreams (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store := {}) (tree : Struct.Tree := ⟨#[]⟩) : Array ByteArray :=
  (pageOps geom fs pages imgs tree).map fun ops => (render ops).toUTF8

/-- What one id's cross-reference row says (ISO 32000-2 §7.5.8.3): direct, compressed, or the
cross-reference stream itself. -/
public inductive ObjKind where
  | direct
  | inStream (idx : Nat)
  | xref
  deriving Repr, BEq

private inductive ImgExtra where
  | plain
  | alpha
  | form (objects : Nat)
  deriving Repr

private def ImgExtra.span : ImgExtra → Nat
  | .plain => 1
  | .alpha => 2
  | .form n => n + 1

private def imgExtraOf (imgs : Image.Store) (k : Nat) : ImgExtra :=
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

private def blockStarts (base : Nat) : List Nat → List Nat
  | [] => []
  | n :: ns => base :: blockStarts (base + n) ns

/-- The most objects one object stream holds, as many as a one-byte stream index addresses. -/
@[expose] public def objStmCapacity : Nat := 256

/-- How many object streams `n` compressed objects take. -/
@[expose] public def objStmCount (n : Nat) : Nat := (n + objStmCapacity - 1) / objStmCapacity

/-- How many objects the writer compresses for these counts. -/
@[expose] public def compressedCount (nf np nOut nElems nFigDict : Nat) : Nat :=
  3 * nf + np + (if nOut == 0 then 0 else nOut + 1) + nElems + 7 + nFigDict

/-- Every object id one file allocates, in id order, computed once from the counts that decide it. -/
public structure ObjTable where
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
  /-- The first of the `nStm` consecutive object-stream ids. -/
  objStmBase : Nat
  nStm : Nat
  xrefId : Nat
  size : Nat
  outputIntent : Option Nat := none
  icc : Option Nat := none
  nElems : Nat
  structTreeRoot : Nat
  parentTree : Nat
  namespaceId : Nat
  structBase : Nat
  /-- The resources dictionary's id, followed by the figure table's dictionaries and forms. -/
  resId : Nat
  nFigDict : Nat
  nFigForm : Nat
  deriving Repr

namespace ObjTable

public def type0Id (k : Nat) : Nat := 3 + 4 * k
public def cidId (k : Nat) : Nat := 3 + 4 * k + 1
public def fdId (k : Nat) : Nat := 3 + 4 * k + 2
public def toUniId (k : Nat) : Nat := 3 + 4 * k + 3
public def fileId (t : ObjTable) (k : Nat) : Nat := 3 + 4 * t.nf + k
public def pageId (t : ObjTable) (i : Nat) : Nat := t.pageBase + 2 * i
public def contentId (t : ObjTable) (i : Nat) : Nat := t.pageBase + 2 * i + 1
public def outlineItemId (t : ObjTable) (k : Nat) : Nat := t.infoId + 2 + k
public def structElemId (t : ObjTable) (k : Nat) : Nat := t.structBase + k
public def figDictId (t : ObjTable) (k : Nat) : Nat := t.resId + 1 + k
public def figFormId (t : ObjTable) (k : Nat) : Nat := t.resId + 1 + t.nFigDict + k
public def objStmId (t : ObjTable) (k : Nat) : Nat := t.objStmBase + k

/-- Every allocated id, in emission order. -/
public def ids (t : ObjTable) : Array Nat :=
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
  ++ #[t.resId]
  ++ (Array.range t.nFigDict).map t.figDictId
  ++ (Array.range t.nFigForm).map t.figFormId
  ++ (#[t.xmpId] ++ (Array.range t.nStm).map t.objStmId ++ #[t.xrefId])

/-- The cross-reference row kind of an id, `none` for an id the table never allocated. -/
public def kindOf (t : ObjTable) (compressedIdx : Nat → Option Nat) (id : Nat) : Option ObjKind :=
  if id == 0 || t.size ≤ id then none
  else if id == t.xrefId then some .xref
  else match compressedIdx id with
    | some idx => some (.inStream idx)
    | none => some .direct

end ObjTable

/-- The object table for these faces, placed images, pages, outline entries, structure elements and
figure resources. -/
public def objTable (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems nFigDict nFigForm : Nat) : ObjTable :=
  let nf := keep.size
  let extras := usedImgs.map (imgExtraOf imgs)
  let spans := extras.map ImgExtra.span
  let imgIds := (blockStarts (3 + 5 * nf) spans.toList).toArray
  let pageBase := 3 + 5 * nf + spans.toList.sum
  let infoId := pageBase + 2 * np
  let structTreeRoot := if nOut == 0 then infoId + 1 else infoId + 2 + nOut
  let resId := structTreeRoot + 3 + nElems
  let xmpId := resId + 1 + nFigDict + nFigForm
  let nStm := objStmCount (compressedCount nf np nOut nElems nFigDict)
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
    objStmBase := xmpId + 1, nStm, xrefId := xmpId + 1 + nStm, size := xmpId + 2 + nStm
    nElems, structTreeRoot, parentTree := structTreeRoot + 1, namespaceId := structTreeRoot + 2
    structBase := structTreeRoot + 3, resId, nFigDict, nFigForm }

/-- The table `write` reads for these inputs. -/
public def tableOf (geom : Geom) (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store)
    (outline : Array OutlineEntry) (tree : Struct.Tree := ⟨#[]⟩) : ObjTable :=
  let figs := figureTable geom pages (docFigs fs pages imgs)
  objTable (keepFaces fs pages imgs.shaped) imgs (usedImagesOf imgs pages) pages.size outline.size
    (skeleton tree).size (figDictCount figs) (figFormCount figs)

private theorem blockIds_exact (base : Nat) (spans : List Nat) :
    ((blockStarts base spans).zip spans).flatMap (fun p => List.range' p.1 p.2)
      = List.range' base spans.sum := by
  induction spans generalizing base with
  | nil => simp [blockStarts]
  | cons n ns ih =>
    rw [blockStarts, List.zip_cons_cons, List.flatMap_cons, ih, List.sum_cons]
    have := @List.range'_append base n ns.sum 1
    simp only [Nat.one_mul] at this
    rw [this]

private theorem flatMap_range_exact (a c n : Nat) (f : Nat → List Nat)
    (hf : ∀ k, f k = List.range' (a + c * k) c) :
    (List.range n).flatMap f = List.range' a (c * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, hf]
    have := @List.range'_append a (c * n) c 1
    simp only [Nat.one_mul] at this
    rw [this, Nat.mul_succ]

private theorem ObjTable.ids_exact (t : ObjTable) (spans : List Nat)
    (himg : t.imgIds.toList = blockStarts (3 + 5 * t.nf) spans)
    (hsp : t.imgSpans.toList = spans)
    (hpb : t.pageBase = 3 + 5 * t.nf + spans.sum)
    (hinfo : t.infoId = t.pageBase + 2 * t.np)
    (hroot : t.outlineRootId = t.infoId + 1)
    (hsr : t.structTreeRoot = if t.nOut == 0 then t.infoId + 1 else t.infoId + 2 + t.nOut)
    (hpt : t.parentTree = t.structTreeRoot + 1) (hns : t.namespaceId = t.structTreeRoot + 2)
    (hsb : t.structBase = t.structTreeRoot + 3) (hres : t.resId = t.structBase + t.nElems)
    (hxmp : t.xmpId = t.resId + 1 + t.nFigDict + t.nFigForm)
    (hstm : t.objStmBase = t.xmpId + 1) (hxref : t.xrefId = t.xmpId + 1 + t.nStm)
    (hsize : t.size = t.xmpId + 2 + t.nStm) :
    t.ids.toList = List.range' 1 (t.size - 1) := by
  have joinRanges (s m s' n : Nat) (h : s' = s + m) :
      List.range' s m ++ List.range' s' n = List.range' s (m + n) := by
    simpa only [h] using (List.range'_append_1 (s := s) (m := m) (n := n))
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
  have hstms : List.map t.objStmId (List.range t.nStm) = List.range' (t.xmpId + 1) t.nStm := by
    rw [List.range'_eq_map_range, ← hstm]; rfl
  have htail : [t.xmpId] ++ List.map t.objStmId (List.range t.nStm) ++ [t.xrefId] =
      List.range' t.xmpId (t.nStm + 2) := by
    rw [hstms, hxref]
    rw [show [t.xmpId] = List.range' t.xmpId 1 from rfl,
      show [t.xmpId + 1 + t.nStm] = List.range' (t.xmpId + 1 + t.nStm) 1 from rfl,
      joinRanges _ _ _ _ rfl, joinRanges _ _ _ _ (by omega)]
    congr 1
    omega
  have hstruct : [t.structTreeRoot, t.parentTree, t.namespaceId] = List.range' t.structTreeRoot 3 := by
    rw [hpt, hns]; rfl
  have helems : List.map t.structElemId (List.range t.nElems)
      = List.range' t.structBase t.nElems := by
    rw [List.range'_eq_map_range]; rfl
  have hres1 : [t.resId] = List.range' t.resId 1 := rfl
  have hfd : List.map t.figDictId (List.range t.nFigDict)
      = List.range' (t.resId + 1) t.nFigDict := by
    rw [List.range'_eq_map_range]; rfl
  have hff : List.map t.figFormId (List.range t.nFigForm)
      = List.range' (t.resId + 1 + t.nFigDict) t.nFigForm := by
    rw [List.range'_eq_map_range]; rfl
  simp only [ObjTable.ids, Array.toList_append, Array.toList_flatMap, Array.toList_map,
    Array.toList_range, Array.toList_zip, Array.toList_range', himg, hsp]
  rw [blockIds_exact, flatMap_range_exact 3 4 t.nf _ hfont,
    flatMap_range_exact t.pageBase 2 t.np _ hpage, hfile, h12, hinfo1, htail, hstruct, helems,
    hres1, hfd, hff]
  by_cases h0 : t.nOut = 0
  · simp only [h0, beq_self_eq_true, ite_true, Array.toList_empty, List.append_nil] at hsr ⊢
    simp (disch := omega) only [joinRanges]
    rw [hsize, hxmp, hres, hsb, hsr, hinfo, hpb]
    congr 1
    omega
  · have hne : (t.nOut == 0) = false := by simpa using h0
    simp only [hne, Bool.false_eq_true, ite_false, Array.toList_append, Array.toList_map,
      Array.toList_range, hitems] at hsr ⊢
    have hout : [t.outlineRootId] ++ List.range' (t.infoId + 2) t.nOut
        = List.range' (t.infoId + 1) (1 + t.nOut) := by
      rw [hroot]; exact joinRanges _ 1 _ _ rfl
    rw [hout]
    simp (disch := omega) only [joinRanges]
    rw [hsize, hxmp, hres, hsb, hsr, hinfo, hpb]
    congr 1
    omega

public theorem objTable_ids_exact (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems nFigDict nFigForm : Nat) :
    (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids.toList
      = List.range' 1 ((objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size - 1) :=
  ObjTable.ids_exact _ ((usedImgs.map (imgExtraOf imgs)).map ImgExtra.span).toList
    (List.toList_toArray) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

public theorem objTable_inj (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems nFigDict nFigForm : Nat) : (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids.toList.Nodup := by
  rw [objTable_ids_exact]
  exact List.nodup_range' 1

public theorem objTable_covers (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems nFigDict nFigForm : Nat) :
    ∀ id, 1 ≤ id → id < (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size →
      id ∈ (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids := by
  intro id h1 h2
  rw [Array.mem_def, objTable_ids_exact, List.mem_range'_1]
  omega

public theorem objTable_between (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems nFigDict nFigForm : Nat) :
    ∀ id ∈ (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids,
      1 ≤ id ∧ id < (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size := by
  intro id h
  rw [Array.mem_def, objTable_ids_exact, List.mem_range'_1] at h
  have : 3 ≤ (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size := by
    simp only [objTable]
    omega
  omega

public theorem objTable_kindOf_some (keep : Array Nat) (imgs : Image.Store) (usedImgs : Array Nat)
    (np nOut nElems nFigDict nFigForm : Nat) (compressedIdx : Nat → Option Nat) :
    ∀ id ∈ (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids,
      ((objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).kindOf compressedIdx id).isSome = true := by
  intro id h
  have hb := objTable_between keep imgs usedImgs np nOut nElems nFigDict nFigForm id h
  unfold ObjTable.kindOf
  rw [ite_eq_right (by simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]; omega)]
  split
  · rfl
  · split <;> rfl

/-- A row of the writer's cross-reference; a missing direct object is declared free, never redirected. -/
public def xrefEntry (t : ObjTable) (compressedIdx offset : Nat → Option Nat)
    (xrefOff id : Nat) : Xref.Entry :=
  if id == t.xrefId then .direct xrefOff 0 else
    match compressedIdx id with
    | some idx => .compressed (t.objStmId (idx / objStmCapacity)) (idx % objStmCapacity)
    | none => match offset id with
      | some off => .direct off 0
      | none => .free 0 0

/-- Row zero, the free list's head (§7.5.4), with generation 255 so the index field stays one byte. -/
public def freeHead : Xref.Entry := .free 0 255

/-- The free-list head and one row per allocated id, in allocation order. -/
public def xrefEntries (t : ObjTable) (compressedIdx offset : Nat → Option Nat)
    (xrefOff : Nat) : Array Xref.Entry :=
  #[freeHead] ++ t.ids.map (xrefEntry t compressedIdx offset xrefOff)

public theorem xrefEntry_kind_exact (t : ObjTable)
    (compressedIdx offset : Nat → Option Nat) (xrefOff id : Nat)
    (hlo : 0 < id) (hhi : id < t.size) :
    some (xrefEntry t compressedIdx offset xrefOff id) =
      (t.kindOf compressedIdx id).map (fun k => match k with
        | .xref => .direct xrefOff 0
        | .inStream idx =>
          .compressed (t.objStmId (idx / objStmCapacity)) (idx % objStmCapacity)
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

public theorem xrefEntries_size_exact (keep : Array Nat) (imgs : Image.Store)
    (usedImgs : Array Nat) (np nOut nElems nFigDict nFigForm : Nat)
    (compressedIdx offset : Nat → Option Nat) (xrefOff : Nat) (w : Xref.Widths) :
    let t := objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm
    (xrefEntries t compressedIdx offset xrefOff).size = t.size ∧
      (Xref.encode w (xrefEntries t compressedIdx offset xrefOff)).size = w.row * t.size := by
  dsimp only
  have ht := objTable_ids_exact keep imgs usedImgs np nOut nElems nFigDict nFigForm
  have hn := congrArg List.length ht
  simp only [Array.length_toList, List.length_range'] at hn
  have hpos : 0 < (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size := by
    simp only [objTable]
    omega
  have hsize : (xrefEntries (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm)
      compressedIdx offset xrefOff).size =
      (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size := by
    simp only [xrefEntries, Array.size_append, Array.size_map, Array.size_singleton, hn]
    omega
  exact ⟨hsize, by rw [Xref.encode_size_exact, hsize]⟩

public theorem xrefEntries_index_exact (keep : Array Nat) (imgs : Image.Store)
    (usedImgs : Array Nat) (np nOut nElems nFigDict nFigForm : Nat)
    (compressedIdx offset : Nat → Option Nat) (xrefOff id : Nat)
    (hid : id < (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size) :
    let t := objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm
    (xrefEntries t compressedIdx offset xrefOff)[id]? =
      some (if id = 0 then freeHead else xrefEntry t compressedIdx offset xrefOff id) := by
  dsimp only
  have ht := objTable_ids_exact keep imgs usedImgs np nOut nElems nFigDict nFigForm
  have hta : (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).ids =
      (List.range' 1 ((objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size - 1)).toArray := by
    rw [← ht, Array.toArray_toList]
  cases id with
  | zero => simp [xrefEntries, Array.getElem?_append]
  | succ id =>
    simp only [xrefEntries, hta, Array.getElem?_append, Array.size_singleton,
      Nat.succ_lt_succ_iff, Nat.not_lt_zero, ↓reduceIte, Nat.add_one_sub_one,
      Array.getElem?_map, List.getElem?_toArray]
    simp [show id < (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size - 1 by omega,
      Nat.add_comm]

public theorem xrefEntries_second_between (t : ObjTable) (compressedIdx offset : Nat → Option Nat)
    (xrefOff : Nat) : ∀ e ∈ xrefEntries t compressedIdx offset xrefOff, e.fields.2.2 < 256 := by
  intro e he
  simp only [xrefEntries, Array.mem_append, Array.mem_singleton, Array.mem_map] at he
  obtain he | ⟨id, _, rfl⟩ := he
  · subst e
    decide
  · unfold xrefEntry
    split
    · simp [Xref.Entry.fields]
    · split
      · simp only [Xref.Entry.fields, objStmCapacity]
        omega
      · split <;> simp [Xref.Entry.fields]

/-- What a written file asks of a reader, one parameter-free constructor per row of the reader matrix. -/
public inductive Feature where
  | xrefStream
  | objStm
  | objStmMulti
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

/-- How many features the census names. -/
public def Feature.count : Nat := 22

/-- Every feature in declaration order, derived from the type. -/
public def Feature.all : List Feature := (List.range Feature.count).map Feature.ofNat

public theorem Feature.all_complete (f : Feature) : f ∈ Feature.all := by
  cases f <;> decide

public theorem Feature.all_nodup : Feature.all.Nodup := by decide

/-- The matrix row a feature is spelled as. -/
public def Feature.name : Feature → String
  | .xrefStream => "xref-stream"
  | .objStm => "objstm"
  | .objStmMulti => "objstm-multi"
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

public theorem Feature.name_inj (a b : Feature) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Feature.name] at h)

public def Feature.ofName? (s : String) : Option Feature := Feature.all.find? (·.name == s)

private def reaches (geom : Geom) (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store)
    (outline : Array OutlineEntry) (tree : Struct.Tree) : Feature → Bool
  | .xrefStream => true
  | .objStm => true
  | .objStmMulti => 1 < (tableOf geom fs pages imgs outline tree).nStm
  | .flatePredictor15 =>
    (placedImages imgs pages).any (fun i => i.form.isNone && i.filter == .flatePredictor)
      || (tableOf geom fs pages imgs outline).smaskIds.any Option.isSome
  | .dct => (placedImages imgs pages).any (fun i => i.form.isNone && i.filter == .dct)
  | .smask => (tableOf geom fs pages imgs outline).smaskIds.any Option.isSome
  | .formXObject => (tableOf geom fs pages imgs outline).formBases.any Option.isSome ||
    0 < (tableOf geom fs pages imgs outline).nFigForm
  | .copiedGraph => (tableOf geom fs pages imgs outline).formSizes.any (· > 0)
  | .cidFontType0 => (keepFaces fs pages imgs.shaped).any fun k => (fs.get k).isCff
  | .cidFontType2 => (keepFaces fs pages imgs.shaped).any fun k => !(fs.get k).isCff
  | .linkURI =>
    pages.any (fun p => (linkRects geom p).any (fun r => !r.2.2.2.2.startsWith "#"))
      || outline.any (fun e => e.page.isNone && e.url.isSome)
  | .outlines => outline.size > 0
  | .xmp => true
  | .trimBox => geom.bleed != 0
  | .outputIntent => (tableOf geom fs pages imgs outline).outputIntent.isSome
  | .iccBased => (tableOf geom fs pages imgs outline).icc.isSome
  | .tabs => false
  | .markedContent => (pageOps geom fs pages imgs).any fun ops => (lines ops).any Line.isOpen
  | .structTree => true
  | .transparencyGroup => (figureTable geom pages (docFigs fs pages imgs)).any fun r => match r with
    | .form .group _ => true
    | .form .symbol _ => false
    | .form (.stamp _) _ => false
    | .extG _ _ => false
    | .pattern _ => false
    | .shading _ => false
  | .brotli => false
  | .jpx => false
where
  /-- The decoded images the pages place, in placement order. -/
  placedImages (imgs : Image.Store) (pages : Array PageOut) : Array Image.Plan :=
    (usedImagesOf imgs pages).filterMap fun k => (imgs.get? k).bind (·.info)

/-- The features `write` reaches on these inputs, in `Feature.all`'s order, computed from its
inputs rather than its bytes. -/
public def features (geom : Geom) (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store := {})
    (outline : Array OutlineEntry := #[]) (tree : Struct.Tree := ⟨#[]⟩) : Array Feature :=
  (Feature.all.filter (reaches geom fs pages imgs outline tree)).toArray

public theorem features_mem (geom : Geom) (fs : FontSet) (pages : Array PageOut) (imgs : Image.Store)
    (outline : Array OutlineEntry) (tree : Struct.Tree) (f : Feature)
    (h : f ∈ features geom fs pages imgs outline tree) :
    f ∈ Feature.all := by
  unfold features at h
  exact (List.mem_filter.1 (List.mem_toArray.1 h)).1

public theorem features_smask_iff (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store) (outline : Array OutlineEntry) (tree : Struct.Tree) :
    .smask ∈ features geom fs pages imgs outline tree ↔
      ∃ k, ∃ h : k < (tableOf geom fs pages imgs outline).smaskIds.size,
        ((tableOf geom fs pages imgs outline).smaskIds[k]).isSome = true := by
  unfold features
  rw [List.mem_toArray, List.mem_filter]
  simp only [Feature.all_complete, true_and, reaches, Array.any_eq_true]

public theorem features_formXObject_exact (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (imgs : Image.Store) (outline : Array OutlineEntry) (tree : Struct.Tree) :
    .formXObject ∈ features geom fs pages imgs outline tree ↔
      (tableOf geom fs pages imgs outline).formBases.any Option.isSome = true ∨
        0 < (tableOf geom fs pages imgs outline).nFigForm := by
  unfold features
  rw [List.mem_toArray, List.mem_filter]
  simp only [Feature.all_complete, true_and, reaches, Bool.or_eq_true, decide_eq_true_eq]

/-- The native stream prefixes owned by the writer. -/
public inductive StreamPrefix where
  | content
  | openType
  | trueType (length : Nat)
  | metadata
  /-- A figure form: its box in whole points, the shared resources it
  names, and whether it is an isolated transparency group. -/
  | figForm (x0 y0 x1 y1 : Int) (res : Nat) (group : Bool)
  deriving Repr

public def StreamPrefix.text : StreamPrefix → String
  | .content => ""
  | .openType => "/Subtype /OpenType"
  | .trueType n => s!"/Length1 {n}"
  | .metadata => "/Type /Metadata /Subtype /XML"
  | .figForm x0 y0 x1 y1 res group =>
    "/Type /XObject" ++ " /Subtype /Form" ++ s!" /BBox [{x0} {y0} {x1} {y1}]" ++
      s!" /Resources {res} {(0 : Nat)} R" ++
      (if group then " /Group << /Type /Group" ++ " /S /Transparency" ++ " /I true >>" else "")

public def StreamPrefix.fragment (p : StreamPrefix) (filtered : Bool) : String :=
  p.text ++ if filtered then " /Filter /FlateDecode" else ""

/-- One physical object as `serialize` writes it: a stream, a form over a copied graph's
renumbered resources, or a copied object. -/
public inductive Body where
  | stream (dict : String) (data : ByteArray)
  /-- The dictionary up to `/Resources`, the renumbered resource bytes, and the form's content. -/
  | form (head : String) (resources : ByteArray) (content : ByteArray)
  /-- A copied object's value and stream, verbatim under the source file's filters. -/
  | copied (value : ByteArray) (stream : Option ByteArray)

/-- A native stream: a writer-owned dictionary prefix and its retained payload. -/
public def Body.Native (body : Body) : Prop :=
  ∃ p : StreamPrefix, ∃ filtered : Bool, ∃ raw : ByteArray,
    body = .stream (p.fragment filtered) raw

/-- An object with the id the table allocated it. -/
public structure Row where
  id : Nat
  body : Body

/-- The bytes one object is written as, appended in place to the buffer it lands in. -/
public def rowInto (out : ByteArray) (id : Nat) : Body → ByteArray
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

private def serializeList (out : ByteArray) (locs : Array (Nat × Nat)) :
    List Row → ByteArray × Array (Nat × Nat)
  | [] => (out, locs)
  | r :: rest =>
    let off := out.size
    serializeList (rowInto out r.id r.body) (locs.push (r.id, off)) rest

/-- The file's objects and the offset each landed at, as this fold wrote them. -/
public def serialize (head : ByteArray) (rows : Array Row) : ByteArray × Array (Nat × Nat) :=
  serializeList head #[] rows.toList

public theorem rowInto_bytes (pre : ByteArray) (id : Nat) (body : Body) :
    rowInto pre id body = pre ++ rowInto ByteArray.empty id body := by
  cases body with
  | stream dict data => simp [rowInto, ByteArray.append_assoc]
  | form head resources content => simp [rowInto, ByteArray.append_assoc]
  | copied value stream =>
    cases stream <;> simp [rowInto, ByteArray.append_assoc]

private theorem serializeList_bytes (rows : List Row) (out : ByteArray)
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

private theorem serializeList_offsets (rows : List Row) (out : ByteArray)
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

private theorem serializeList_offsetSize (rows : List Row) (out : ByteArray)
    (locs : Array (Nat × Nat)) :
    (serializeList out locs rows).2.size = locs.size + rows.length := by
  induction rows generalizing out locs with
  | nil => simp [serializeList]
  | cons r rest ih =>
    simp only [serializeList, ih, Array.size_push, List.length_cons]
    omega

private theorem serializeList_append (before after : List Row) (out : ByteArray)
    (locs : Array (Nat × Nat)) :
    serializeList out locs (before ++ after) =
      serializeList (serializeList out locs before).1
        (serializeList out locs before).2 after := by
  induction before generalizing out locs with
  | nil => rfl
  | cons r rest ih =>
    simpa only [List.cons_append, serializeList] using
      (ih (rowInto out r.id r.body) (locs.push (r.id, out.size)))

public theorem serialize_row_exact (head : ByteArray) (before after : Array Row) (r : Row) :
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

private theorem serializeList_ids (l : List Row) (out : ByteArray) (locs : Array (Nat × Nat)) :
    (serializeList out locs l).2.toList.map (·.1) = locs.toList.map (·.1) ++ l.map (·.id) := by
  induction l generalizing out locs with
  | nil => simp [serializeList]
  | cons r rest ih => simp [serializeList, ih]

public theorem serialize_locs_covers (head : ByteArray) (rows : Array Row) :
    (serialize head rows).2.toList.map (·.1) = rows.toList.map (·.id) := by
  simp [serialize, serializeList_ids]

public theorem serialize_locs_id (head : ByteArray) (r : Row) (rest : Array Row) :
    (serialize head (#[r] ++ rest)).2[0]? = some (r.id, head.size) := by
  simpa [serialize, serializeList] using (serialize_row_exact head #[] rest r).1

private def indexObjectsList {α : Type} (out : Array (Option α)) :
    List (Nat × α) → Array (Option α)
  | [] => out
  | (id, value) :: rest => indexObjectsList (out.setIfInBounds id (some value)) rest

public def indexObjects {α : Type} (size : Nat) (rows : List (Nat × α)) : Array (Option α) :=
  indexObjectsList (Array.replicate size none) rows

@[simp] private theorem indexObjectsList_size {α : Type} (rows : List (Nat × α))
    (out : Array (Option α)) :
    (indexObjectsList out rows).size = out.size := by
  induction rows generalizing out with
  | nil => rfl
  | cons r rest ih => simp [indexObjectsList, ih]

private theorem indexObjectsList_append {α : Type} (before after : List (Nat × α))
    (out : Array (Option α)) :
    indexObjectsList out (before ++ after) =
      indexObjectsList (indexObjectsList out before) after := by
  induction before generalizing out with
  | nil => rfl
  | cons r rest ih => exact ih _

private theorem indexObjectsList_absent {α : Type} (rows : List (Nat × α))
    (out : Array (Option α)) (id : Nat)
    (habsent : ∀ r ∈ rows, r.1 ≠ id) :
    (indexObjectsList out rows)[id]? = out[id]? := by
  induction rows generalizing out with
  | nil => rfl
  | cons r rest ih =>
    simp only [indexObjectsList]
    rw [ih _ (fun s hs => habsent s (List.mem_cons_of_mem _ hs))]
    simp [habsent r (List.mem_cons_self)]

private theorem indexObjectsList_source {α : Type} (rows : List (Nat × α))
    (out : Array (Option α)) (id : Nat) (value : α)
    (h : ((indexObjectsList out rows)[id]?).join = some value) :
    (out[id]?).join = some value ∨ (id, value) ∈ rows := by
  induction rows generalizing out with
  | nil => exact Or.inl h
  | cons r rest ih =>
    obtain h | h := ih _ h
    · by_cases hi : r.1 = id
      · simp only [hi, Array.getElem?_setIfInBounds_self] at h
        split at h
        · have hv : r.2 = value := by simpa using h
          exact Or.inr (List.mem_cons.mpr (Or.inl (Prod.ext hi.symm hv.symm)))
        · simp at h
      · exact Or.inl (by simpa [hi] using h)
    · exact Or.inr (List.mem_cons_of_mem _ h)

public theorem indexObjects_mem {α : Type} (size : Nat) (rows : List (Nat × α))
    (id : Nat) (value : α)
    (h : ((indexObjects size rows)[id]?).join = some value) :
    (id, value) ∈ rows := by
  obtain h | h := indexObjectsList_source rows _ id value h
  · simp only [Array.getElem?_replicate] at h
    split at h <;> simp_all
  · exact h

public theorem indexObjects_entry_exact {α : Type} (size : Nat)
    (before after : List (Nat × α)) (id : Nat) (value : α)
    (hid : id < size) (hlast : ∀ r ∈ after, r.1 ≠ id) :
    ((indexObjects size (before ++ (id, value) :: after))[id]?).join =
      some value := by
  simp only [indexObjects, indexObjectsList_append, indexObjectsList]
  rw [indexObjectsList_absent _ _ id hlast]
  rw [Array.getElem?_setIfInBounds_self_of_lt]
  · rfl
  · simpa using hid

/-- Each compressed id's position in the list the object streams pack. -/
public def compressedIndex (size : Nat) (objects : List (Nat × PdfRead.Obj)) :
    Array (Option Nat) :=
  indexObjects size (objects.zipIdx.map (fun (row, i) => (row.1, i)))

public theorem compressedIndex_mem (size : Nat) (objects : List (Nat × PdfRead.Obj))
    (id i : Nat) (h : ((compressedIndex size objects)[id]?).join = some i) :
    ∃ value, objects[i]? = some (id, value) := by
  have hm := indexObjects_mem size _ id i h
  obtain ⟨⟨row, j⟩, hj, heq⟩ := List.mem_map.mp hm
  have hr : row.1 = id := congrArg Prod.fst heq
  have hi : j = i := congrArg Prod.snd heq
  refine ⟨row.2, ?_⟩
  have := List.mem_zipIdx_iff_getElem?.mp hj
  simpa [hi, ← hr] using this

public theorem compressedIndex_between (size : Nat) (objects : List (Nat × PdfRead.Obj))
    (id i : Nat) (h : ((compressedIndex size objects)[id]?).join = some i) :
    i < objects.length := by
  have hm := indexObjects_mem size _ id i h
  obtain ⟨⟨row, j⟩, hj, heq⟩ := List.mem_map.mp hm
  have hi : j = i := congrArg Prod.snd heq
  have := List.snd_lt_of_mem_zipIdx hj
  simpa [hi] using this

private theorem serializeList_offsetBound (rows : List Row) (out : ByteArray)
    (locs : Array (Nat × Nat)) (h : ∀ r ∈ locs, r.2 ≤ out.size) :
    ∀ r ∈ (serializeList out locs rows).2,
      r.2 ≤ (serializeList out locs rows).1.size := by
  induction rows generalizing out locs with
  | nil => exact h
  | cons row rest ih =>
    apply ih
    have hsize : out.size ≤ (rowInto out row.id row.body).size := by
      rw [rowInto_bytes, ByteArray.size_append]
      omega
    intro r hr
    obtain hr | hr := Array.mem_push.mp hr
    · exact Nat.le_trans (h r hr) hsize
    · simpa [hr] using hsize

public theorem serialize_offsets_between (head : ByteArray) (rows : Array Row)
    (id off : Nat) (h : (id, off) ∈ (serialize head rows).2) :
    off ≤ (serialize head rows).1.size :=
  serializeList_offsetBound rows.toList head #[] (by simp) (id, off) h

/-- The xref payload from the serializer's locations and the object-stream position list. -/
public def writerXrefEntries (t : ObjTable) (locs : Array (Nat × Nat))
    (objects : List (Nat × PdfRead.Obj)) (xrefOff : Nat) : Array Xref.Entry :=
  let offsets := indexObjects t.size locs.toList
  let compressed := compressedIndex t.size objects
  xrefEntries t (fun id => (compressed[id]?).join)
    (fun id => (offsets[id]?).join) xrefOff

public theorem writerXrefEntries_fits (t : ObjTable) (locs : Array (Nat × Nat))
    (objects : List (Nat × PdfRead.Obj)) (xrefOff : Nat) :
    ∀ e ∈ writerXrefEntries t locs objects xrefOff,
      e.Fits (Xref.widthsOf (writerXrefEntries t locs objects xrefOff)) :=
  Xref.widthsOf_fits _

public theorem writerXrefWidths_second_exact (t : ObjTable) (locs : Array (Nat × Nat))
    (objects : List (Nat × PdfRead.Obj)) (xrefOff : Nat) :
    (Xref.widthsOf (writerXrefEntries t locs objects xrefOff)).second = 1 := by
  obtain ⟨hlo, hhi⟩ := (Xref.widthsOf_between (writerXrefEntries t locs objects xrefOff) ⟨_, 1⟩
    (Xref.width_between (Xref.maxFirst (writerXrefEntries t locs objects xrefOff))).1
    (Nat.le_refl 1) (fun e he => ⟨(Xref.widthsOf_fits _ e he).1,
      by simpa using xrefEntries_second_between _ _ _ _ e he⟩)).2
  change _ ≤ 1 at hhi
  omega

public theorem writerXref_fields_exact (keep : Array Nat) (imgs : Image.Store)
    (usedImgs : Array Nat) (np nOut nElems nFigDict nFigForm : Nat) (head : ByteArray)
    (rows : Array Row) (objects : List (Nat × PdfRead.Obj)) (id : Nat)
    (hid : id < (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size) :
    let t := objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm
    let out := serialize head rows
    let es := writerXrefEntries t out.2 objects out.1.size
    let w := Xref.widthsOf es
    let e := if id = 0 then freeHead else
      xrefEntry t (fun n => ((compressedIndex t.size objects)[n]?).join)
        (fun n => ((indexObjects t.size out.2.toList)[n]?).join) out.1.size id
    let data := Xref.encode w es
    Binary.readNatBE 1 data (w.row * id) = some e.fields.1.toNat ∧
      Binary.readNatBE w.first data (w.row * id + 1) = some e.fields.2.1 ∧
      Binary.readNatBE w.second data (w.row * id + 1 + w.first) = some e.fields.2.2 := by
  dsimp only
  have hi := xrefEntries_index_exact keep imgs usedImgs np nOut nElems nFigDict nFigForm
    (fun n => ((compressedIndex (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size objects)[n]?).join)
    (fun n => ((indexObjects (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm).size
      (serialize head rows).2.toList)[n]?).join) (serialize head rows).1.size id hid
  have he := writerXrefEntries_fits (objTable keep imgs usedImgs np nOut nElems nFigDict nFigForm)
    (serialize head rows).2 objects (serialize head rows).1.size _ (Array.mem_of_getElem? hi)
  simpa only [writerXrefEntries, ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] using
    Xref.encode_index_fields_exact _ _ id _ hi he ByteArray.empty ByteArray.empty

/-- The two buffers of an object stream (§7.5.7); header offsets are relative to `payload`. -/
public structure ObjectStream where
  header : String := ""
  payload : ByteArray := ByteArray.empty

private def ObjectStream.push (s : ObjectStream) (id : Nat) (value : PdfRead.Obj) : ObjectStream :=
  { header := s.header ++ s!"{id} {s.payload.size} "
    payload := (s.payload ++ PdfRead.Obj.render value).push 10 }

private def objectStreamList (s : ObjectStream) : List (Nat × PdfRead.Obj) → ObjectStream
  | [] => s
  | (id, value) :: rest => objectStreamList (s.push id value) rest

public def objectStream (objects : List (Nat × PdfRead.Obj)) : ObjectStream :=
  objectStreamList {} objects

public def ObjectStream.bytes (s : ObjectStream) : ByteArray :=
  s.header.toUTF8 ++ s.payload

private theorem objectStreamList_append (s : ObjectStream) (before after : List (Nat × PdfRead.Obj)) :
    objectStreamList s (before ++ after) =
      objectStreamList (objectStreamList s before) after := by
  induction before generalizing s with
  | nil => rfl
  | cons r rest ih => exact ih _

private theorem objectStreamList_header (objects : List (Nat × PdfRead.Obj))
    (header : String) (payload : ByteArray) :
    (objectStreamList ⟨header, payload⟩ objects).header =
      header ++ (objectStreamList ⟨"", payload⟩ objects).header := by
  induction objects generalizing header payload with
  | nil => simp [objectStreamList]
  | cons r rest ih =>
    simp only [objectStreamList, ObjectStream.push, String.empty_append]
    rw [ih, ih s!"{r.1} {payload.size} "]
    simp [String.append_assoc]

private theorem objectStreamList_payload (objects : List (Nat × PdfRead.Obj)) (s : ObjectStream) :
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

public theorem objectStream_entry_exact (before after : List (Nat × PdfRead.Obj))
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

/-- The three dictionaries of one embedded face (ISO 32000-2 §9.7, §9.8). -/
public structure FontObjects where
  type0 : PdfRead.Obj
  cid : PdfRead.Obj
  descriptor : PdfRead.Obj

public def FontObjects.rows (o : FontObjects) (k : Nat) : List (Nat × PdfRead.Obj) :=
  [(ObjTable.type0Id k, o.type0), (ObjTable.cidId k, o.cid),
    (ObjTable.fdId k, o.descriptor)]

/-- Font dictionaries from the face metrics and the allocated ids. -/
public def fontObjects (t : ObjTable) (k : Nat) (font : Font)
    (baseFont : String) (widths : PdfRead.Obj) : FontObjects :=
  let ascent1000 := font.ascent * 1000 / font.unitsPerEm
  let descent1000 := font.descent * 1000 / font.unitsPerEm
  let capHeight1000 := font.capHeight * 1000 / font.unitsPerEm
  let cidSubtype := if font.isCff then "CIDFontType0" else "CIDFontType2"
  let cidToGid : Array (String × PdfRead.Obj) :=
    if font.isCff then #[] else #[("CIDToGIDMap", .name "Identity")]
  let fontFileKey := if font.isCff then "FontFile3" else "FontFile2"
  let italicAngle := if font.italicAngle == 0 && font.isItalic then -12
    else font.italicAngle
  -- Flags: bit 1 fixed pitch, bit 3 symbolic, bit 7 italic (1-based).
  let flags := 4 + (if font.isFixedPitch then 1 else 0) + (if font.isItalic then 64 else 0)
  -- StemV and the FontBBox x-bounds are conventional stand-ins: an unhinted face declares neither.
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

public theorem fontObjects_links_exact (t : ObjTable) (k : Nat) (font : Font)
    (baseFont : String) (widths : PdfRead.Obj) :
    let o := fontObjects t k font baseFont widths
    o.type0.get? "DescendantFonts" = some (.arr #[.ref (ObjTable.cidId k) 0]) ∧
    o.type0.get? "ToUnicode" = some (.ref (ObjTable.toUniId k) 0) ∧
    o.cid.get? "FontDescriptor" = some (.ref (ObjTable.fdId k) 0) ∧
    o.descriptor.get? (if font.isCff then "FontFile3" else "FontFile2") =
      some (.ref (t.fileId k) 0) := by
  cases hcff : font.isCff <;>
    simp [fontObjects, hcff, PdfRead.Obj.get?]

/-- A stream row in the smaller of its original and deflated spellings. -/
public def zRow (id : Nat) (dict : String) (data z : ByteArray) : Row :=
  if z.size < data.size then ⟨id, .stream (dict ++ " /Filter /FlateDecode") z⟩
  else ⟨id, .stream dict data⟩

public def flateRow (id : Nat) (dict : String) (data : ByteArray) : Row :=
  zRow id dict data (Flate.deflate data)

/-- A figure form's stream prefix: its box, the shared resources, and whether it is an isolated
transparency group (§11.6.6). -/
public def formPrefix (b : Int × Int × Int × Int) (resId : Nat) (kind : FormKind) : StreamPrefix :=
  .figForm b.1 b.2.1 b.2.2.1 b.2.2.2 resId (match kind with
    | .group => true
    | .symbol => false
    | .stamp _ => false)

/-- A figure form's row; an entry that is no form writes an empty content stream. -/
public def formRow (gi : GfxPdf.GlyphInk) (id resId : Nat) : FigRes → Row
  | .form kind body =>
    flateRow id (formPrefix (formBBox gi kind body) resId kind).text (render body).toUTF8
  | .extG _ _ => flateRow id StreamPrefix.content.text ByteArray.empty
  | .pattern _ => flateRow id StreamPrefix.content.text ByteArray.empty
  | .shading _ => flateRow id StreamPrefix.content.text ByteArray.empty

/-- A copied page's decoded content as stored: deflated with the filter declared when smaller,
else unfiltered. -/
@[expose] public def copiedFormStream (content : ByteArray) (z? : Option ByteArray) :
    ByteArray × Bool :=
  let z := z?.getD (Flate.deflate content)
  if z.size < content.size then (z, true) else (content, false)

/-- The content of each copied page the pages place, by store entry. -/
public def copiedFormContents (imgs : Image.Store) (pages : Array PageOut) :
    Array (Option ByteArray) :=
  let used := usedImagesOf imgs pages
  (Array.range imgs.entries.size).map fun k =>
    if used.contains k then
      ((((imgs.get? k).bind (·.info)).bind (·.form)).map (·.val.content))
    else none

public theorem zRow_native_exact (id : Nat) (p : StreamPrefix) (data z : ByteArray) :
    (zRow id p.text data z).body.Native := by
  unfold zRow
  split
  · exact ⟨p, true, z, rfl⟩
  · exact ⟨p, false, data, by simp [StreamPrefix.fragment]⟩

public theorem flateRow_native_exact (id : Nat) (p : StreamPrefix) (data : ByteArray) :
    (flateRow id p.text data).body.Native :=
  zRow_native_exact id p data _

public theorem formRow_native_exact (gi : GfxPdf.GlyphInk) (id resId : Nat) (r : FigRes) :
    (formRow gi id resId r).body.Native := by
  cases r <;> exact flateRow_native_exact _ _ _

/-- `n` consecutive slices of at most `objStmCapacity` items each, in order. -/
public def chunksN {α : Type} : Nat → List α → List (List α)
  | 0, _ => []
  | n + 1, xs => xs.take objStmCapacity :: chunksN n (xs.drop objStmCapacity)

/-- The compressed objects cut into object streams: consecutive slices of
`objStmCapacity`, the last one shorter. -/
public def objStmChunks {α : Type} (xs : List α) : List (List α) :=
  chunksN (objStmCount xs.length) xs

public theorem chunksN_getElem?_exact {α : Type} (n : Nat) (xs : List α) (k : Nat) :
    (chunksN n xs)[k]? =
      if k < n then some ((xs.drop (k * objStmCapacity)).take objStmCapacity) else none := by
  induction n generalizing xs k with
  | zero => simp [chunksN]
  | succ n ih =>
    cases k with
    | zero => simp [chunksN]
    | succ k =>
      simp only [chunksN, List.getElem?_cons_succ, ih, List.drop_drop, Nat.succ_mul,
        Nat.add_comm objStmCapacity, Nat.add_lt_add_iff_right]

@[simp] public theorem chunksN_length {α : Type} (n : Nat) (xs : List α) :
    (chunksN n xs).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [chunksN, ih]

public theorem objStmChunks_length {α : Type} (xs : List α) :
    (objStmChunks xs).length = objStmCount xs.length := chunksN_length _ _

private theorem objStmCount_mul_le (n : Nat) : n ≤ objStmCount n * objStmCapacity := by
  simp only [objStmCount, objStmCapacity]
  omega

private theorem lt_of_lt_objStmCount (n k : Nat) (hk : k < objStmCount n) :
    k * objStmCapacity < n := by
  simp only [objStmCount, objStmCapacity] at hk ⊢
  omega

public theorem objStmChunks_flatten_id {α : Type} (xs : List α) :
    (objStmChunks xs).flatten = xs := by
  have h (n : Nat) (ys : List α) : (chunksN n ys).flatten = ys.take (n * objStmCapacity) := by
    induction n generalizing ys with
    | zero => simp [chunksN]
    | succ n ih =>
      rw [chunksN, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm, List.take_add]
  rw [objStmChunks, h, List.take_of_length_le (objStmCount_mul_le _)]

public theorem objStmChunks_between {α : Type} (xs : List α) :
    ∀ c ∈ objStmChunks xs, 0 < c.length ∧ c.length ≤ objStmCapacity := by
  intro c hc
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
  rw [objStmChunks, chunksN_getElem?_exact] at hk
  split at hk
  · rename_i hlt
    cases hk
    have := lt_of_lt_objStmCount xs.length k hlt
    simp only [List.length_take, List.length_drop]
    simp only [objStmCapacity] at this ⊢
    omega
  · cases hk

public theorem objStmChunks_entry_exact {α : Type} (before after : List α) (x : α) :
    ∃ cb ca, (objStmChunks (before ++ x :: after))[before.length / objStmCapacity]? =
        some (cb ++ x :: ca) ∧
      cb.length = before.length % objStmCapacity ∧ ∀ y ∈ ca, y ∈ after := by
  refine ⟨before.drop (before.length / objStmCapacity * objStmCapacity),
    after.take (objStmCapacity - 1 - before.length % objStmCapacity), ?_, ?_, ?_⟩
  · have hk : before.length / objStmCapacity < objStmCount (before ++ x :: after).length := by
      simp only [objStmCount, List.length_append, List.length_cons, objStmCapacity]
      omega
    rw [objStmChunks, chunksN_getElem?_exact]
    simp only [hk, ↓reduceIte, Option.some.injEq]
    rw [List.drop_append_of_le_length (by simp only [objStmCapacity]; omega), List.take_append,
      List.take_of_length_le (by simp only [List.length_drop, objStmCapacity]; omega)]
    congr 1
    simp only [List.length_drop]
    rw [show objStmCapacity - (before.length - before.length / objStmCapacity * objStmCapacity) =
      (objStmCapacity - 1 - before.length % objStmCapacity) + 1 by simp only [objStmCapacity]; omega,
      List.take_succ_cons]
  · simp only [List.length_drop, objStmCapacity]
    omega
  · intro y hy
    exact List.mem_of_mem_take hy

/-- The writer's allocation and emissions before serialization. -/
public structure WritePlan where
  table : ObjTable
  head : ByteArray
  direct : Array Row
  compressed : List (Nat × PdfRead.Obj)

/-- The object streams' contents, `objStmCapacity` objects at most each. -/
public def WritePlan.chunks (p : WritePlan) : List (List (Nat × PdfRead.Obj)) :=
  objStmChunks p.compressed

/-- One object stream's row, deflated when that is smaller. -/
public def objStmRow (id count : Nat) (packed : ObjectStream) : Row :=
  flateRow id s!"/Type /ObjStm /N {count} /First {packed.header.utf8ByteSize}" packed.bytes

/-- Each chunk packed once with its object count. -/
public def WritePlan.packed (p : WritePlan) : List (Nat × ObjectStream) :=
  p.chunks.map fun c => (c.length, objectStream c)

/-- The object-stream rows, stream `k` under the table's `k`-th id. -/
public def stmRowsOf (t : ObjTable) (packed : List (Nat × ObjectStream)) : Array Row :=
  (packed.zipIdx.map fun ((count, s), k) => objStmRow (t.objStmId k) count s).toArray

/-- The object streams are appended to the direct rows they accompany. -/
public def WritePlan.rows (p : WritePlan) : Array Row :=
  p.direct ++ stmRowsOf p.table p.packed

public def WritePlan.serialized (p : WritePlan) : ByteArray × Array (Nat × Nat) :=
  serialize p.head p.rows

public def WritePlan.entries (p : WritePlan) : Array Xref.Entry :=
  let (body, locs) := p.serialized
  writerXrefEntries p.table locs p.compressed body.size

/-- The row layout the writer declares: the widths the rows need. -/
public def WritePlan.widths (p : WritePlan) : Xref.Widths :=
  Xref.widthsOf p.entries

/-- The largest decoded object stream, as the size check reads it. -/
public def packedMax (packed : List (Nat × ObjectStream)) : Nat :=
  packed.foldl (fun m x => max m (x.2.header.utf8ByteSize + x.2.payload.size)) 0

/-- The measured bytes retained for final emission. -/
public structure WriteMeasurement where
  body : ByteArray
  widths : Xref.Widths
  xrefPayload : ByteArray
  objectPayloadSize : Nat

public def WritePlan.measure (p : WritePlan) : WriteMeasurement :=
  let packed := p.packed
  let (body, locs) := serialize p.head (p.direct ++ stmRowsOf p.table packed)
  let entries := writerXrefEntries p.table locs p.compressed body.size
  let widths := Xref.widthsOf entries
  { body, widths, xrefPayload := Xref.encode widths entries,
    objectPayloadSize := packedMax packed }

/-- The xref stream's own dictionary, as `bytes` spells it. -/
public def WriteMeasurement.xrefDictText (m : WriteMeasurement) (t : ObjTable) : String :=
  let idA := Flate.hex16 (Flate.fnv64 Flate.fnvOffset m.body)
  let idB := Flate.hex16 (Flate.fnv64 Flate.secondSeed m.body)
  s!"/Type /XRef /Size {t.size} /W [1 {m.widths.first} {m.widths.second}] /Index [0 {t.size}] /Root 1 0 R /Info {t.infoId} 0 R /ID [<{idA}> <{idB}>]"

/-- Finishes a measurement: its xref, and `startxref` naming the byte after its body. -/
public def WriteMeasurement.bytes (m : WriteMeasurement) (t : ObjTable) : ByteArray :=
  let (out, _) := serialize m.body #[flateRow t.xrefId (m.xrefDictText t) m.xrefPayload]
  out ++ (s!"startxref\n{m.body.size}\n%%EOF\n").toUTF8

public def WritePlan.bytes (p : WritePlan) : ByteArray :=
  p.measure.bytes p.table

public theorem WritePlan.measure_body_exact (p : WritePlan) :
    p.measure.body = p.serialized.1 := by rfl

public theorem WritePlan.measure_xref_exact (p : WritePlan) :
    p.measure.xrefPayload = Xref.encode p.widths p.entries := by rfl

private theorem foldl_packedMax_le (B : Nat) (xs : List (Nat × ObjectStream)) (acc : Nat) :
    xs.foldl (fun m x => max m (x.2.header.utf8ByteSize + x.2.payload.size)) acc ≤ B ↔
      acc ≤ B ∧ ∀ x ∈ xs, x.2.header.utf8ByteSize + x.2.payload.size ≤ B := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, forall_eq_or_imp, Nat.max_le, and_assoc]

public theorem WritePlan.measure_object_size_exact (p : WritePlan) (B : Nat) :
    p.measure.objectPayloadSize ≤ B ↔ ∀ c ∈ p.chunks, (objectStream c).bytes.size ≤ B := by
  change packedMax p.packed ≤ B ↔ _
  rw [packedMax, foldl_packedMax_le]
  simp only [Nat.zero_le, true_and, WritePlan.packed, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, ObjectStream.bytes, ByteArray.size_append,
    String.toUTF8_eq_toByteArray, String.size_toByteArray]

public theorem WritePlan.bytes_serialized_exact (p : WritePlan) :
    p.bytes =
      let (body, locs) := p.serialized
      let entries := writerXrefEntries p.table locs p.compressed body.size
      let w := Xref.widthsOf entries
      let xrefRows := Xref.encode w entries
      let idA := Flate.hex16 (Flate.fnv64 Flate.fnvOffset body)
      let idB := Flate.hex16 (Flate.fnv64 Flate.secondSeed body)
      let dict := s!"/Type /XRef /Size {p.table.size} /W [1 {w.first} {w.second}] /Index [0 {p.table.size}] /Root 1 0 R /Info {p.table.infoId} 0 R /ID [<{idA}> <{idB}>]"
      let (out, _) := serialize body #[flateRow p.table.xrefId dict xrefRows]
      out ++ (s!"startxref\n{body.size}\n%%EOF\n").toUTF8 := by rfl

/-- Prepares positioned pages for a PDF 2.0 file, or 1.7 where the document declares it; `ops`,
`streams` and `programs` are the driver's cached page operators, their rendered and deflated bytes,
and its face programs. -/
public def prepare (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta := {}) (imgs : Image.Store := {})
    (outline : Array OutlineEntry := #[])
    (streams : Array (ByteArray × Option ByteArray) := #[])
    (tree : Struct.Tree := ⟨#[]⟩) (ops : Array (Array ContentOp) := #[])
    (programs : Array (ByteArray × Bool) := #[]) : WritePlan := Id.run do
  let np := pages.size
  let v17 := info.pdfVersion == some "1.7"
  let allUsed : Array (Array (Nat × Char)) := usedAll fs pages imgs.shaped
  let keep : Array Nat := keepOf allUsed
  let remap := remapOf fs keep
  let gi := glyphInkOf fs keep
  let usedPerFont : Array (Array (Nat × Char)) := keep.map fun k => allUsed[k]!
  let nf := keep.size
  let programs : Array (ByteArray × Bool) := if programs.size == nf then programs
    else (keep.zip usedPerFont).map fun (fk, used) =>
      let font := fs.get fk
      FontSubset.program font (used.map (·.1))
  let usedImgs := usedImagesOf imgs pages
  let imgMap := imgMapOf imgs usedImgs
  let nOut := outline.size
  let sk := skeleton tree
  let nLeaves := tree.leaves.size
  let tags := leafTags sk nLeaves
  let docFigs := docFigsWith fs keep imgs
  let ops := if ops.size == np then ops
    else let wt := widthTable fs.fonts keep
      namedPageOps geom pages docFigs
        (pages.map (contentOps geom remap wt imgMap tags figureNames docFigs))
  let marks := ops.map pageMarks
  let es := fill sk (leafPagesOf nLeaves marks)
  let parentTree := parentTreeOf marks (leafOwners sk nLeaves)
  let figs := figureTable geom pages docFigs
  let figDicts := figs.filter fun r => !r.isForm
  let figForms := figs.filter FigRes.isForm
  let t := objTable keep imgs usedImgs np nOut es.size (figDictCount figs) (figFormCount figs)

  let outlineRoot := if nOut == 0 then none else some t.outlineRootId
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
  -- Internal fragments are destinations resolved from the final lines, never URI actions (§12.3.2).
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
  let figId (k : Nat) : Nat :=
    if (figs[k]?.map FigRes.isForm).getD false then t.figFormId (figRank figs k)
    else t.figDictId (figRank figs k)
  let figEntries (pick : FigRes → Bool) : Array (String × PdfRead.Obj) :=
    figs.zipIdx.filterMap fun (r, k) =>
      if pick r then some (s!"{r.namePrefix}{k + 1}", PdfRead.Obj.ref (figId k) 0) else none
  -- A drawn figure's raster is also named by the store entry its form paints it with.
  let imgEntries : Array (String × PdfRead.Obj) :=
    t.imgIds.zipIdx.map (fun (id, n) => (s!"Im{n + 1}", PdfRead.Obj.ref id 0)) ++
    (usedImgs.zip t.imgIds).filterMap fun (k, id) =>
      ((imgs.get? k).bind (·.rasterOf)).map fun _ => (s!"Ri{k + 1}", PdfRead.Obj.ref id 0)
  let resources : PdfRead.Obj := resourcesDict fontResources
    (imgEntries ++ figEntries FigRes.isForm) (figEntries fun r => r.namePrefix == "GS")
    (figEntries fun r => r.namePrefix == "P") (figEntries fun r => r.namePrefix == "Sh")
  let figDictObjs : List (Nat × PdfRead.Obj) := figDicts.toList.zipIdx.map fun (r, j) =>
    (t.figDictId j, (figDictObj (nameRes figs r)).getD .null)
  let pageDict (i : Nat) : PdfRead.Obj :=
    let b := geom.bleed
    -- A trim the document's own marks cut lies the inset inside the page.
    let inset := if b == 0 then geom.trimInset else 0
    let (media, bleedBox, trim) :=
      if 0 < inset then pageBoxes (geom.pageW - 2 * inset) (geom.pageH - 2 * inset) inset
      else pageBoxes geom.pageW geom.pageH b
    let boxes : Array (String × PdfRead.Obj) := if b == 0 && !(0 < inset) then #[] else
      #[("TrimBox", trim.obj), ("BleedBox", bleedBox.obj), ("ArtBox", trim.obj)]
    -- `/StructParents` (§14.7.5.4): the page's key in the parent tree.
    let ann := annots i
    .dict (#[("Type", PdfRead.Obj.name "Page"), ("Parent", .ref 2 0), ("MediaBox", media.obj)]
      ++ boxes
      ++ #[("Resources", .ref t.resId 0)]
      ++ ann
      ++ #[("Contents", .ref (t.contentId i) 0), ("StructParents", .int i)])
  -- Metadata is a text string (§7.9.2.2), never raw UTF-8, which a reader decodes as PDFDocEncoding.
  let infoEntry (key : String) (v : Option String) : Array (String × PdfRead.Obj) :=
    match v with
    | some s => #[(key, litObj (pdfTextString s))]
    | none => #[]
  let infoDict : PdfRead.Obj := .dict
    (infoEntry "Title" info.title ++ infoEntry "Author" info.author ++
      infoEntry "Subject" info.subject ++ infoEntry "Keywords" info.keywords ++
      #[("Producer", litObj "(leantex)")])

  -- A resolved outline target is a /Dest to its page; /XYZ null null null keeps the reader's view.
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
  let elemRef (i : Nat) : PdfRead.Obj := .ref (t.structElemId i) 0
  -- A PDF 1.7 file role-maps its 2.0-only types onto 1.7's and has no namespace objects.
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
    (List.range np).map (fun i => (t.pageId i, pageDict i)) ++ structObjs ++
    [(t.resId, resources)] ++ figDictObjs

  let fileHead : ByteArray := (if v17 then "%PDF-1.7\n%" else "%PDF-2.0\n%").toUTF8 ++
    ⟨#[0xE2, 0xE3, 0xCF, 0xD3]⟩ ++ "\n".toUTF8

  let mut rows : Array Row := #[]

  for i in [0:np] do
    let (data, z?) := match streams[i]?, ops[i]? with
      | some s, _ => s
      | none, some o => ((render o).toUTF8, none)
      | none, none => (ByteArray.empty, none)
    rows := rows.push (match z? with
      | some z => zRow (t.contentId i) "" data z
      | none => flateRow (t.contentId i) "" data)

  -- PNG rows embed as /FlateDecode with the predictor declared (§7.4.4.4), re-deflated when alpha splits off.
  for ((k, imgId), n) in (usedImgs.zip t.imgIds).zipIdx do
    if let some inf := (imgs.get? k).bind (·.info) then
      match inf.form, (t.formBases[n]?).join with
      | some f, some base =>
        -- A PDF page is a form XObject (§8.10) whose /Matrix normalizes its box to the unit square.
        let fv := f.val
        let bw := fv.w
        let bh := fv.h
        let bbox := s!"[{Sp.toPtString fv.x0} {Sp.toPtString fv.y0} \
{Sp.toPtString fv.x1} {Sp.toPtString fv.y1}]"
        let matrix := s!"[{ratString spPerPt bw} 0 0 {ratString spPerPt bh} \
{ratString (-fv.x0) bw} {ratString (-fv.y0) bh}]"
        let stored := copiedFormStream fv.content (imgs.formZ[k]?).join
        let filter := if stored.2 then " /Filter /FlateDecode" else ""
        rows := rows.push ⟨imgId, .form s!"<< /Type /XObject /Subtype /Form \
/BBox {bbox} /Matrix {matrix}{filter} /Resources " (renderChunks base fv.resources) stored.1⟩
        for (o, l) in fv.objects.zipIdx do
          rows := rows.push ⟨base + l, .copied (renderChunks base o.chunks) o.stream⟩
      | _, _ =>
        let deviceOf (n : Nat) : String :=
          if n == 1 then "/DeviceGray" else if n == 4 then "/DeviceCMYK" else "/DeviceRGB"
        let colorSpace := match inf.color with
          | .gray => "/DeviceGray"
          | .rgb => "/DeviceRGB"
          | .indexed palette => Id.run do
            let mut hex := ""
            for byte in palette do
              hex := hex ++ Hex.byte true byte
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
        -- Colour-key masking (ISO 32000-2 §8.9.6.4), its ranges in sample units.
        let maskRef := match inf.alpha with
          | .colorKey ranges => s!" /Mask [{" ".intercalate (ranges.toList.map toString)}]"
          | .opaque => ""
          | .soft _ _ => ""
        -- A drawn figure's raster a reader may smooth says so (§8.9.5.3).
        let interp := if ((imgs.get? k).map (·.interpolate)).getD false then " /Interpolate true" else ""
        let dict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace {colorSpace} /BitsPerComponent {inf.bitDepth}\
{smaskRef}{maskRef}{interp} {filter}"
        rows := rows.push ⟨imgId, .stream dict inf.data⟩
        if let some mid := (t.smaskIds[n]?).join then
          if let .soft plane bpc := inf.alpha then
            -- The alpha plane is the source's filtered rows, so the mask declares its colour plane's predictor.
            let mdict := s!"/Type /XObject /Subtype /Image /Width {inf.pxW} \
/Height {inf.pxH} /ColorSpace /DeviceGray /BitsPerComponent {bpc} /Filter /FlateDecode \
/DecodeParms << /Predictor 15 /Colors 1 /BitsPerComponent {bpc} /Columns {inf.pxW} >>"
            rows := rows.push ⟨mid, .stream mdict plane⟩

  for (r, j) in figForms.zipIdx do
    rows := rows.push (formRow gi (t.figFormId j) t.resId (nameRes figs r))

  for k in [0:nf] do
    let font := fs.get keep[k]!
    let prog := (programs[k]?.map (·.1)).getD font.data
    let tuData := (toUnicode usedPerFont[k]!).toUTF8
    rows := rows.push (flateRow (ObjTable.toUniId k) "" tuData)
    let ffDict := if font.isCff then "/Subtype /OpenType" else s!"/Length1 {prog.size}"
    rows := rows.push (match fs.zdata[keep[k]!]?.getD none with
      | some z => zRow (t.fileId k) ffDict prog z
      | none => flateRow (t.fileId k) ffDict prog)

  rows := rows.push (flateRow t.xmpId "/Type /Metadata /Subtype /XML" (xmpPacket info).toUTF8)
  return ⟨t, fileHead, rows, compressed⟩

/-- Serializes the prepared emissions. -/
public def write (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta := {}) (imgs : Image.Store := {})
    (outline : Array OutlineEntry := #[])
    (streams : Array (ByteArray × Option ByteArray) := #[])
    (tree : Struct.Tree := ⟨#[]⟩) (ops : Array (Array ContentOp) := #[])
    (programs : Array (ByteArray × Bool) := #[]) : ByteArray :=
  (prepare geom fs pages info imgs outline streams tree ops programs).bytes

private theorem usedImagesOf_loaded (imgs : Image.Store) (pages : Array PageOut) :
    ∀ k ∈ usedImagesOf imgs pages, ((imgs.get? k).bind (·.info)).isSome = true := by
  let P := fun out : Array Nat =>
    ∀ k ∈ out, ((imgs.get? k).bind (·.info)).isSome = true
  change P (usedImagesOf imgs pages)
  unfold usedImagesOf
  simp only [Id.run, bind, pure]
  apply Loop.forIn_array_inv P
  · simp [P]
  · intro p _ out h
    change P (forIn p.lines out _ : Id (Array Nat))
    apply Loop.forIn_array_inv P
    · exact h
    · intro l _ out h
      change P (forIn l.segs out _ : Id (Array Nat))
      apply Loop.forIn_array_inv P
      · exact h
      · intro s _ out h
        dsimp only [Id.run, bind, pure]
        have slots (init : Array Nat) (hi : P init) (xs : Array Nat) :
            P (forIn xs init (fun r (acc : Array Nat) =>
              if (((imgs.get? r).bind fun x => x.info).isSome && !acc.contains r) = true then
                ForInStep.yield (acc.push r) else ForInStep.yield acc) : Id (Array Nat)).run := by
          apply Loop.forIn_array_inv P
          · exact hi
          · intro r _ acc ha
            dsimp only [Id.run]
            split
            · next hc =>
              intro j hj
              rcases Array.mem_push.mp hj with hj | rfl
              · exact ha j hj
              · exact (Bool.and_eq_true_iff.mp hc).1
            · exact ha
        split
        · split
          · rename_i k _ _ _ hk
            apply slots
            intro j hj
            rcases Array.mem_push.mp hj with hj | rfl
            · exact h j hj
            · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hk).1).1
          · exact slots _ h _
        · exact h

private theorem usedImagesOf_empty (pages : Array PageOut) :
    usedImagesOf {} pages = #[] := by
  apply Array.eq_empty_iff_forall_not_mem.mpr
  intro k hk
  have h := usedImagesOf_loaded {} pages k hk
  simp [Image.Store.get?] at h

public theorem prepare_native_exact (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta) (outline : Array OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    ∀ r ∈ (prepare geom fs pages info {} outline streams tree ops programs).direct,
      r.body.Native := by
  let P := fun rows : Array Row => ∀ r ∈ rows, r.body.Native
  have push (rows : Array Row) (r : Row) (h : P rows) (hr : r.body.Native) :
      P (rows.push r) := by
    intro s hs
    rcases Array.mem_push.mp hs with hs | rfl
    · exact h s hs
    · exact hr
  have zfont (id : Nat) (cff : Bool) (data z : ByteArray) :
      (zRow id (if cff then "/Subtype /OpenType" else s!"/Length1 {data.size}")
        data z).body.Native := by
    cases cff
    · exact zRow_native_exact id (.trueType data.size) data z
    · exact zRow_native_exact id .openType data z
  have ffont (id : Nat) (cff : Bool) (data : ByteArray) :
      (flateRow id (if cff then "/Subtype /OpenType" else s!"/Length1 {data.size}")
        data).body.Native := zfont id cff data _
  change P (prepare geom fs pages info {} outline streams tree ops programs).direct
  unfold prepare
  simp only [Id.run, bind, pure, usedImagesOf_empty]
  apply push
  · apply Loop.forIn_range_inv P
    · apply Loop.forIn_array_inv P
      · apply Loop.forIn_array_inv P
        · apply Loop.forIn_range_inv P
          · simp [P]
          · intro i _ _ rows h
            dsimp only [Id.run, bind, pure]
            apply push _ _ h
            split
            · exact zRow_native_exact _ .content _ _
            · exact flateRow_native_exact _ .content _
        · intro x _ rows h
          dsimp only [Id.run, bind, pure]
          simpa only [Image.Store.get?, Array.getElem?_empty, Option.bind_none,
            ForInStep.value] using h
      · intro x _ rows h
        dsimp only [Id.run, bind, pure]
        exact push _ _ h (formRow_native_exact _ _ _ _)
    · intro k _ _ rows h
      dsimp only [Id.run, bind, pure]
      apply push
      · exact push _ _ h (flateRow_native_exact _ .content _)
      · split
        · exact zfont _ _ _ _
        · exact ffont _ _ _
  · exact flateRow_native_exact _ .metadata _

private theorem map_zipIdx_snd {α β : Type} (l : List α) (f : Nat → β) :
    l.zipIdx.map (fun p => f p.2) = (List.range l.length).map f := by
  have h := congrArg (List.map f) (List.zipIdx_map_snd 0 l)
  simpa only [List.map_map, List.range_eq_range', Function.comp_def] using h
public theorem prepare_table_exact (geom : Geom) (fs : FontSet) (pages : Array PageOut) (info : Ir.Meta)
    (imgs : Image.Store) (outline : Array OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    (prepare geom fs pages info imgs outline streams tree ops programs).table =
      tableOf geom fs pages imgs outline tree := by
  unfold prepare tableOf
  simp only [Id.run, pure, bind, keepFaces, docFigs, fill_size_exact]

public theorem prepare_compressed_ids_exact (geom : Geom) (fs : FontSet) (pages : Array PageOut) (info : Ir.Meta)
    (imgs : Image.Store) (outline : Array OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    let t := p.table
    p.compressed.map Prod.fst =
      [1, 2] ++ (List.range t.nf).flatMap (fun k =>
        [ObjTable.type0Id k, ObjTable.cidId k, ObjTable.fdId k]) ++
      [t.infoId] ++
      (if t.nOut == 0 then [] else t.outlineRootId ::
        (List.range t.nOut).map t.outlineItemId) ++
      (List.range t.np).map t.pageId ++
      [t.structTreeRoot, t.parentTree, t.namespaceId] ++
      (List.range t.nElems).map t.structElemId ++
      [t.resId] ++ (List.range t.nFigDict).map t.figDictId := by
  dsimp only
  simp only [prepare, Id.run, pure, bind, List.map_append, List.map_cons,
    List.map_nil, List.map_flatMap, FontObjects.rows, List.map_map, Function.comp_def,
    List.append_assoc, fill_size_exact]
  simp only [apply_ite, List.map_nil, List.map_cons, List.map_map, Function.comp_def]
  simp only [map_zipIdx_snd, apply_ite, Array.length_toList, fill_size_exact, ite_self]
  rfl
private theorem forIn_ids {α β : Type} (ids : β → List Nat)
    (f : α → β → Id (ForInStep β)) (emits : α → List Nat)
    (xs : List α) (initial : β)
    (hf : ∀ a ∈ xs, ∀ state, ∃ next,
      f a state = .yield next ∧ ids next = ids state ++ emits a) :
    ids (forIn xs initial f : Id β).run = ids initial ++ xs.flatMap emits := by
  induction xs generalizing initial with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨next, hn, he⟩ := hf a (by simp) initial
    rw [List.forIn_cons, hn]
    change ids (forIn xs next f : Id β).run =
      ids initial ++ (a :: xs).flatMap emits
    rw [ih next (fun b hb => hf b (by simp [hb])), he]
    simp only [List.flatMap_cons, List.append_assoc]

private theorem forIn_range_ids {β : Type} (ids : β → List Nat)
    (f : Nat → β → Id (ForInStep β)) (emits : Nat → List Nat)
    (hi : Nat) (initial : β)
    (hf : ∀ i, i < hi → ∀ state, ∃ next,
      f i state = .yield next ∧ ids next = ids state ++ emits i) :
    ids (forIn [0:hi] initial f : Id β) =
      ids initial ++ (List.range hi).flatMap emits := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, ← List.range_eq_range']
  exact forIn_ids ids f emits _ initial (fun i hi => hf i (List.mem_range.mp hi))

private theorem forIn_array_ids {α β : Type} (ids : β → List Nat)
    (f : α → β → Id (ForInStep β)) (emits : α → List Nat)
    (xs : Array α) (initial : β)
    (hf : ∀ a ∈ xs, ∀ state, ∃ next,
      f a state = .yield next ∧ ids next = ids state ++ emits a) :
    ids (forIn xs initial f : Id β) = ids initial ++ xs.toList.flatMap emits := by
  rw [← Array.forIn_toList]
  exact forIn_ids ids f emits _ initial (fun a ha => hf a (by simpa using ha))

private theorem zRow_id (n : Nat) (d : String) (data z : ByteArray) :
    (zRow n d data z).id = n := by
  unfold zRow
  split <;> rfl

private theorem flateRow_id (n : Nat) (d : String) (data : ByteArray) :
    (flateRow n d data).id = n := zRow_id ..

private theorem formRow_id (gi : GfxPdf.GlyphInk) (n resId : Nat) (r : FigRes) :
    (formRow gi n resId r).id = n := by
  cases r <;> exact flateRow_id ..

private theorem image_slots (keep : Array Nat) (imgs : Image.Store) (used : Array Nat)
    (np nOut nElems nFigDict nFigForm k id n : Nat) (hk : used[n]? = some k)
    (hi : (objTable keep imgs used np nOut nElems nFigDict nFigForm).imgIds[n]? = some id) :
    let t := objTable keep imgs used np nOut nElems nFigDict nFigForm
    t.formBases[n]?.join =
      (match imgExtraOf imgs k with | .form _ => some (id + 1) | _ => none) ∧
    t.smaskIds[n]?.join =
      (match imgExtraOf imgs k with | .alpha => some (id + 1) | _ => none) := by
  dsimp only
  simp only [objTable, Array.getElem?_map, Array.zip_eq_zipWith, Array.getElem?_zipWith',
    show (blockStarts (3 + 5 * keep.size)
      ((used.map (imgExtraOf imgs)).map ImgExtra.span).toList).toArray[n]? = some id
      from hi, hk, Option.map_some, Option.bind_some, Option.join_some]
  cases imgExtraOf imgs k <;> exact ⟨rfl, rfl⟩

private theorem zip_flatMap_swap {α β γ : Type} (xs : List α) (ys : List β)
    (f : α → β → List γ) :
    (xs.zip ys).flatMap (fun p => f p.1 p.2) =
      (ys.zip xs).flatMap (fun p => f p.2 p.1) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp [ih]

private theorem flatMap_zipIdx_fst {α β : Type} (xs : List α)
    (f : α → List β) :
    xs.zipIdx.flatMap (fun p => f p.1) = xs.flatMap f := by
  simpa only [List.flatMap_map] using
    congrArg (List.flatMap f) (List.zipIdx_map_fst 0 xs)

private theorem image_transcript (used ids : Array Nat) (imgs : Image.Store) :
    (used.zip ids).zipIdx.toList.flatMap
      (fun x => List.range' x.1.2 (imgExtraOf imgs x.1.1).span) =
    (ids.zip ((used.map (imgExtraOf imgs)).map ImgExtra.span)).toList.flatMap
      (fun p => List.range' p.1 p.2) := by
  simp only [Array.toList_zipIdx]
  rw [flatMap_zipIdx_fst (f := fun p : Nat × Nat =>
    List.range' p.2 (imgExtraOf imgs p.1).span)]
  simp only [Array.toList_zip, Array.toList_map, List.zip_map_right, List.flatMap_map]
  exact zip_flatMap_swap used.toList ids.toList
    (fun k id => List.range' id (imgExtraOf imgs k).span)


public theorem prepare_direct_ids_exact (geom : Layout.Geom) (fs : Font.FontSet) (pages : Array Layout.PageOut)
    (info : Ir.Meta) (imgs : Image.Store) (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    p.direct.toList.map Row.id =
      (List.range p.table.np).map p.table.contentId ++
      ((p.table.imgIds.zip p.table.imgSpans).toList.flatMap fun p => List.range' p.1 p.2) ++
      (List.range p.table.nFigForm).map p.table.figFormId ++
      (List.range p.table.nf).flatMap (fun k => [ObjTable.toUniId k, p.table.fileId k]) ++
      [p.table.xmpId] := by
  let t := tableOf geom fs pages imgs outline tree
  dsimp only
  simp only [prepare, Id.run, bind, pure, fill_size_exact]
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, flateRow_id]
  rw [forIn_range_ids (ids := fun rs : Array Row => rs.toList.map Row.id)
    (emits := fun k => [ObjTable.toUniId k, t.fileId k])]
  case hf =>
    intro k _ rs
    refine ⟨_, rfl, ?_⟩
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, flateRow_id]
    split <;> simp only [zRow_id, flateRow_id, List.append_assoc, List.cons_append,
      List.nil_append]
    all_goals rfl
  rw [forIn_array_ids (ids := fun rs : Array Row => rs.toList.map Row.id)
    (emits := fun x : FigRes × Nat => [t.figFormId x.2])]
  case hf =>
    rintro ⟨r, j⟩ _ rs
    refine ⟨_, rfl, ?_⟩
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, formRow_id]
    rfl
  rw [forIn_array_ids (ids := fun rs : Array Row => rs.toList.map Row.id)
    (emits := fun x : (Nat × Nat) × Nat => List.range' x.1.2 (imgExtraOf imgs x.1.1).span)]
  case hf =>
    rintro ⟨⟨k, imgId⟩, n⟩ hm rs
    have hs := Array.getElem?_zip_eq_some.mp (Array.mem_zipIdx_iff_getElem?.mp hm)
    obtain ⟨inf, hinf⟩ := Option.isSome_iff_exists.mp
      (usedImagesOf_loaded imgs pages k (Array.mem_of_getElem? hs.1))
    have slots := image_slots _ imgs _ pages.size outline.size (skeleton tree).size
      (figDictCount (figureTable geom pages (docFigsWith fs (keepOf (usedAll fs pages imgs.shaped)) imgs)))
      (figFormCount (figureTable geom pages (docFigsWith fs (keepOf (usedAll fs pages imgs.shaped)) imgs)))
      k imgId n hs.1 hs.2
    simp only [hinf]
    cases hf : inf.form with
    | some f =>
      simp only [imgExtraOf, hinf, hf] at slots ⊢
      rw [slots.1]
      refine ⟨_, rfl, ?_⟩
      rw [forIn_array_ids (ids := fun rows : Array Row => rows.toList.map Row.id)
        (emits := fun p : PdfRead.XObjOut × Nat => [imgId + 1 + p.2])]
      case hf =>
        intro p _ rows
        exact ⟨_, rfl, by simp only [Array.toList_push, List.map_append,
          List.map_cons, List.map_nil]⟩
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
        ← List.map_eq_flatMap, Array.toList_zipIdx, map_zipIdx_snd, Array.length_toList,
        ImgExtra.span, ← List.range'_eq_map_range, List.range'_succ, List.append_assoc,
        List.cons_append, List.nil_append]
    | none =>
      simp only [imgExtraOf, hinf, hf] at slots ⊢
      rw [slots.2]
      cases inf.alpha <;> refine ⟨_, rfl, ?_⟩ <;>
        simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
          ImgExtra.span, List.range'_succ, List.range'_zero, List.append_assoc,
          List.cons_append, List.nil_append]
  rw [forIn_range_ids (ids := fun rs : Array Row => rs.toList.map Row.id)
    (emits := fun k => [t.contentId k])]
  case hf =>
    intro k _ rows
    refine ⟨_, rfl, ?_⟩
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    split <;> simp only [zRow_id, flateRow_id] <;> rfl
  rw [image_transcript]
  simp only [List.map_nil, List.nil_append, ← List.map_eq_flatMap, Array.toList_zipIdx,
    map_zipIdx_snd, Array.length_toList]
  rfl

public theorem stmRowsOf_ids_exact (t : ObjTable) (packed : List (Nat × ObjectStream)) :
    (stmRowsOf t packed).toList.map Row.id = (List.range packed.length).map t.objStmId := by
  simp only [stmRowsOf, List.toList_toArray, List.map_map, Function.comp_def,
    objStmRow, flateRow_id]
  exact map_zipIdx_snd packed t.objStmId

public theorem WritePlan.rows_ids_exact (p : WritePlan) :
    p.rows.toList.map Row.id =
      p.direct.toList.map Row.id ++ (List.range p.chunks.length).map p.table.objStmId := by
  simp only [WritePlan.rows, Array.toList_append, List.map_append, stmRowsOf_ids_exact,
    WritePlan.packed, List.length_map]

private theorem emission_covers (p : WritePlan)
    (hd : p.direct.toList.map Row.id =
      (List.range p.table.np).map p.table.contentId ++
      ((p.table.imgIds.zip p.table.imgSpans).toList.flatMap fun q => List.range' q.1 q.2) ++
      (List.range p.table.nFigForm).map p.table.figFormId ++
      (List.range p.table.nf).flatMap (fun k => [ObjTable.toUniId k, p.table.fileId k]) ++
      [p.table.xmpId])
    (hc : p.compressed.map Prod.fst =
      [1, 2] ++ (List.range p.table.nf).flatMap (fun k =>
        [ObjTable.type0Id k, ObjTable.cidId k, ObjTable.fdId k]) ++
      [p.table.infoId] ++
      (if p.table.nOut == 0 then [] else p.table.outlineRootId ::
        (List.range p.table.nOut).map p.table.outlineItemId) ++
      (List.range p.table.np).map p.table.pageId ++
      [p.table.structTreeRoot, p.table.parentTree, p.table.namespaceId] ++
      (List.range p.table.nElems).map p.table.structElemId ++
      [p.table.resId] ++ (List.range p.table.nFigDict).map p.table.figDictId)
    (hs : p.chunks.length = p.table.nStm) :
    ∀ id ∈ p.table.ids, id = p.table.xrefId ∨
      id ∈ p.rows.toList.map Row.id ∨ id ∈ p.compressed.map Prod.fst := by
  intro id hid
  rw [p.rows_ids_exact, hs, hd, hc]
  simp only [Array.mem_def, ObjTable.ids, Array.toList_append, Array.toList_flatMap,
    Array.toList_map, Array.toList_range, Array.toList_range'] at hid
  clear hd hc hs
  cases hout : p.table.nOut == 0
  all_goals
    simp only [hout, Bool.false_eq_true, ↓reduceIte,
      Array.toList_append, Array.toList_map,
      Array.toList_range, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false,
      Array.toList_empty] at hid ⊢
    grind only

private theorem chunks_count_exact (p : WritePlan)
    (hc : p.compressed.map Prod.fst =
      [1, 2] ++ (List.range p.table.nf).flatMap (fun k =>
        [ObjTable.type0Id k, ObjTable.cidId k, ObjTable.fdId k]) ++
      [p.table.infoId] ++
      (if p.table.nOut == 0 then [] else p.table.outlineRootId ::
        (List.range p.table.nOut).map p.table.outlineItemId) ++
      (List.range p.table.np).map p.table.pageId ++
      [p.table.structTreeRoot, p.table.parentTree, p.table.namespaceId] ++
      (List.range p.table.nElems).map p.table.structElemId ++
      [p.table.resId] ++ (List.range p.table.nFigDict).map p.table.figDictId)
    (hstm : p.table.nStm = objStmCount
      (compressedCount p.table.nf p.table.np p.table.nOut p.table.nElems p.table.nFigDict)) :
    p.chunks.length = p.table.nStm := by
  have hl := congrArg List.length hc
  rw [List.length_map] at hl
  rw [WritePlan.chunks, objStmChunks_length, hstm, hl]
  congr 1
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_flatMap,
    List.length_map, List.length_range, List.map_const', List.sum_replicate_nat,
    compressedCount]
  cases p.table.nOut == 0 <;> simp <;> omega

public theorem prepare_chunks_exact (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta) (imgs : Image.Store) (outline : Array OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    p.chunks.length = p.table.nStm :=
  chunks_count_exact _
    (prepare_compressed_ids_exact geom fs pages info imgs outline streams tree ops programs)
    (by rw [prepare_table_exact]; rfl)

public theorem features_objStmMulti_exact (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta) (imgs : Image.Store) (outline : Array OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    .objStmMulti ∈ features geom fs pages imgs outline tree ↔
      1 < (prepare geom fs pages info imgs outline streams tree ops programs).chunks.length := by
  rw [prepare_chunks_exact, prepare_table_exact]
  unfold features
  rw [List.mem_toArray, List.mem_filter]
  simp only [Feature.all_complete, true_and, reaches, decide_eq_true_eq]

public theorem prepare_emission_covers (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta) (imgs : Image.Store) (outline : Array OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    ∀ id ∈ p.table.ids, id = p.table.xrefId ∨
      id ∈ p.rows.toList.map Row.id ∨ id ∈ p.compressed.map Prod.fst :=
  emission_covers _
    (prepare_direct_ids_exact geom fs pages info imgs outline streams tree ops programs)
    (prepare_compressed_ids_exact geom fs pages info imgs outline streams tree ops programs)
    (prepare_chunks_exact geom fs pages info imgs outline streams tree ops programs)

private theorem indexObjectsList_live {α : Type} (rows : List (Nat × α))
    (out : Array (Option α)) (id : Nat) (hid : id < out.size)
    (h : ((out[id]?).join).isSome = true ∨ id ∈ rows.map Prod.fst) :
    (((indexObjectsList out rows)[id]?).join).isSome = true := by
  induction rows generalizing out with
  | nil => simpa [indexObjectsList] using h
  | cons r rest ih =>
    apply ih (out.setIfInBounds r.1 (some r.2)) (by simpa using hid)
    by_cases hr : r.1 = id
    · left
      simp [hr, hid]
    · rcases h with h | h
      · left
        simpa [hr] using h
      · right
        simpa only [List.map_cons, List.mem_cons, Ne.symm hr, false_or] using h

public theorem indexObjects_covers {α : Type} (size : Nat) (rows : List (Nat × α))
    (id : Nat) (hid : id < size) (hm : id ∈ rows.map Prod.fst) :
    (((indexObjects size rows)[id]?).join).isSome = true :=
  indexObjectsList_live rows _ id (by simpa using hid) (Or.inr hm)

public theorem compressedIndex_covers (size : Nat) (objects : List (Nat × PdfRead.Obj))
    (id : Nat) (hid : id < size) (hm : id ∈ objects.map Prod.fst) :
    (((compressedIndex size objects)[id]?).join).isSome = true := by
  apply indexObjects_covers size _ id hid
  have h := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 objects)
  simp only [List.map_map, Function.comp_def] at h ⊢
  rw [h]
  exact hm

private theorem writerEntry_live (t : ObjTable) (locs : Array (Nat × Nat))
    (objects : List (Nat × PdfRead.Obj)) (off id : Nat) (hid : id < t.size)
    (hc : id = t.xrefId ∨ id ∈ locs.toList.map Prod.fst ∨
      id ∈ objects.map Prod.fst) :
    (PdfRead.xrefEntryLocation (xrefEntry t
      (fun n => ((compressedIndex t.size objects)[n]?).join)
      (fun n => ((indexObjects t.size locs.toList)[n]?).join) off id)).isSome = true := by
  unfold xrefEntry
  split
  · rfl
  · rename_i hx
    cases hcomp : ((compressedIndex t.size objects)[id]?).join with
    | some idx => simp only [hcomp, PdfRead.xrefEntryLocation, Option.isSome_some]
    | none =>
      cases hdir : ((indexObjects t.size locs.toList)[id]?).join with
      | some pos => simp only [hcomp, hdir, PdfRead.xrefEntryLocation, Option.isSome_some]
      | none =>
        exfalso
        rcases hc with hc | hc | hc
        · exact hx (by simpa using hc)
        · have := indexObjects_covers t.size locs.toList id hid hc
          simp [hdir] at this
        · have := compressedIndex_covers t.size objects id hid hc
          simp [hcomp] at this

private theorem plan_entries_contract (p : WritePlan)
    (keep : Array Nat) (imgs : Image.Store) (used : Array Nat) (np no ne nd nfm : Nat)
    (ht : p.table = objTable keep imgs used np no ne nd nfm)
    (hc : ∀ id ∈ p.table.ids, id = p.table.xrefId ∨
      id ∈ p.rows.toList.map Row.id ∨ id ∈ p.compressed.map Prod.fst) :
    p.entries.size = p.table.size ∧
    p.entries[0]?.bind PdfRead.xrefEntryLocation = none ∧
    ∀ i, 0 < i → i < p.entries.size →
      (p.entries[i]?.bind PdfRead.xrefEntryLocation).isSome = true := by
  have hs : p.entries.size = p.table.size := by
    simpa only [WritePlan.entries, writerXrefEntries, ht] using
      (xrefEntries_size_exact keep imgs used np no ne nd nfm
        (fun n => ((compressedIndex p.table.size p.compressed)[n]?).join)
        (fun n => ((indexObjects p.table.size p.serialized.2.toList)[n]?).join)
        p.serialized.1.size default).1
  have hi (i : Nat) (hib : i < p.table.size) :
      p.entries[i]? = some (if i = 0 then freeHead else
        xrefEntry p.table
          (fun n => ((compressedIndex p.table.size p.compressed)[n]?).join)
          (fun n => ((indexObjects p.table.size p.serialized.2.toList)[n]?).join)
          p.serialized.1.size i) := by
    simpa only [WritePlan.entries, writerXrefEntries, ht] using
      xrefEntries_index_exact keep imgs used np no ne nd nfm
        (fun n => ((compressedIndex p.table.size p.compressed)[n]?).join)
        (fun n => ((indexObjects p.table.size p.serialized.2.toList)[n]?).join)
        p.serialized.1.size i (by simpa only [ht] using hib)
  have hpos : 0 < p.table.size := by
    rw [ht]
    simp only [objTable]
    omega
  refine ⟨hs, ?_, ?_⟩
  · rw [hi 0 hpos]
    rfl
  · intro i hip hib
    rw [hs] at hib
    rw [hi i hib]
    simp only [show i ≠ 0 by omega, ↓reduceIte, Option.bind_some]
    apply writerEntry_live _ _ _ _ i hib
    have hm : i ∈ p.table.ids := by
      rw [ht]
      exact objTable_covers keep imgs used np no ne nd nfm i (by omega) (by simpa only [ht] using hib)
    rcases hc i hm with hx | hd | hcomp
    · exact Or.inl hx
    · right
      left
      simpa only [WritePlan.serialized, serialize_locs_covers] using hd
    · exact Or.inr (Or.inr hcomp)

public theorem prepare_entries_contract (geom : Geom) (fs : FontSet) (pages : Array PageOut)
    (info : Ir.Meta) (imgs : Image.Store) (outline : Array OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    p.entries.size = p.table.size ∧
    p.entries[0]?.bind PdfRead.xrefEntryLocation = none ∧
    ∀ i, 0 < i → i < p.entries.size →
      (p.entries[i]?.bind PdfRead.xrefEntryLocation).isSome = true :=
  plan_entries_contract _ (keepFaces fs pages imgs.shaped) imgs (usedImagesOf imgs pages)
    pages.size outline.size (skeleton tree).size
    (figDictCount (figureTable geom pages (docFigs fs pages imgs)))
    (figFormCount (figureTable geom pages (docFigs fs pages imgs)))
    (prepare_table_exact geom fs pages info imgs outline streams tree ops programs)
    (prepare_emission_covers geom fs pages info imgs outline streams tree ops programs)

end LeanTex.Core.Pdf
