module

public import Tests.Support
public import LeanTex.Core.PdfFontContract

public section

open LeanTex.Core

private def fieldFile (w : Pdf.Xref.Widths) (row : ByteArray) : ByteArray :=
  let head := "%PDF-2.0\n".toUTF8
  let data := Pdf.Xref.row w 0 0 255 ++ row
  let out := Pdf.rowInto head 2
    (.stream s!"/Type /XRef /Size 2 /W [1 {w.first} {w.second}] /Index [0 2] /Root 1 0 R" data)
  out ++ s!"startxref\n{head.size}\n%%EOF\n".toUTF8

/-- The reader consumes the fields at the widths the PDF writer declares,
including offsets past 4 GiB and stream indices past one byte once a
width holds them. The out-of-domain case witnesses why the universal
field law requires each value to fit its declared width. -/
def pdfWriterChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let w142 : Pdf.Xref.Widths := ⟨4, 2⟩
  t "PDF xref: persisted direct-row bytes"
    (Pdf.Xref.row w142 1 16909060 0 == bytes [1, 1, 2, 3, 4, 0, 0])
  t "PDF xref: persisted compressed-row bytes"
    (Pdf.Xref.row w142 2 16909060 1286 == bytes [2, 1, 2, 3, 4, 5, 6])
  t "PDF xref: a five-byte offset field spells past 4 GiB"
    (Pdf.Xref.row ⟨5, 1⟩ 1 (256 ^ 4 + 2) 0 == bytes [1, 1, 0, 0, 0, 2, 0])
  let entries : Array Pdf.Xref.Entry :=
    #[.free 0 255, .direct 4294967295 0, .compressed 16909060 99,
      .direct 256 0, .compressed 1 0]
  let w := Pdf.Xref.widthsOf entries
  t "PDF xref: widths are the maxima's, a four-byte offset and a one-byte index"
    (w == ⟨4, 1⟩)
  t "PDF xref: one more byte of offset widens only the offset field"
    (Pdf.Xref.widthsOf (entries.push (.direct (256 ^ 4) 0)) == ⟨5, 1⟩)
  t "PDF xref: an index past 255 widens only the index field"
    (Pdf.Xref.widthsOf (entries.push (.compressed 1 256)) == ⟨4, 2⟩)
  t "PDF xref: a file of zeros still declares one byte per field"
    (Pdf.Xref.widthsOf #[.free 0 0] == ⟨1, 1⟩)
  let encoded := Pdf.Xref.encode w entries
  t "PDF xref: every payload row has the declared width" (encoded.size == w.row * entries.size)
  for (e, i) in entries.zipIdx do
    t "PDF xref: fields at their actual row position"
      (Binary.readNatBE 1 encoded (w.row * i) == some e.fields.1.toNat &&
        Binary.readNatBE w.first encoded (w.row * i + 1) == some e.fields.2.1 &&
        Binary.readNatBE w.second encoded (w.row * i + 1 + w.first) == some e.fields.2.2)
  t "PDF xref: the free-list head is the one-byte all-ones generation"
    (Pdf.freeHead == .free 0 255)
  let table := Pdf.objTable #[] {} #[] 0 0 0 0 0
  let select := Pdf.xrefEntry table (fun _ => some 23) (fun _ => some 99) 177
  t "PDF xref: its own direct row takes priority over the compressed index"
    (select table.xrefId == .direct 177 0 && select 1 == .compressed (table.objStmId 0) 23)
  t "PDF xref: one capacity past index 23 is index 23 of the second object stream"
    (Pdf.xrefEntry table (fun _ => some (Pdf.objStmCapacity + 23)) (fun _ => none) 177 1 ==
      .compressed (table.objStmId 1) 23)
  t "PDF xref: absent direct objects are free"
    (Pdf.xrefEntry table (fun _ => none) (fun _ => none) 177 1 == .free 0 0)
  t "PDF xref: allocation count includes the free-list head"
    ((Pdf.xrefEntries table (fun _ => none) (fun _ => some 99) 177).size == table.size)
  t "PDF index: the last in-range source row wins"
    (Pdf.indexObjects 4 [(1, 3), (2, 7), (1, 9), (4, 13)] ==
      #[none, some 9, some 7, none])
  t "PDF index: absent and out-of-range ids have no answer"
    (((Pdf.indexObjects 4 [(1, 3), (4, 13)])[0]?).join == none &&
      ((Pdf.indexObjects 4 [(1, 3), (4, 13)])[4]?).join == none)
  t "PDF index: compressed positions retain the actual packed-list index"
    (Pdf.compressedIndex 4 [(1, .int 3), (3, .int 7), (1, .int 9), (9, .int 13)] ==
      #[none, some 2, none, some 1])
  let objects : List (Nat × PdfRead.Obj) :=
    [(11, .int 7), (31, .str "(A\\(B\\))".toUTF8),
      (43, .dict #[("Type", .name "Example"), ("N", .int 99)])]
  let packed := Pdf.objectStream objects
  t "PDF object stream: first offset follows the encoded header"
    (packed.bytes.extract 0 packed.header.utf8ByteSize == packed.header.toUTF8)
  for ((_, value), i) in objects.zipIdx do
    let off := (Pdf.objectStream (objects.take i)).payload.size
    t "PDF object stream: every declared offset selects its object"
      ((PdfRead.parseVal packed.bytes (packed.header.utf8ByteSize + off)).toOption.any
        fun (actual, _) => actual == value)
  t "PDF object stream: omitting First changes the parsed object"
    ((PdfRead.parseVal packed.bytes 0).toOption.any fun (actual, _) => actual != .int 7)
  for off in [0, 255, 256, 65535, 65536, 4294967295, 4294967296, 256 ^ 6 - 1] do
    let wf : Pdf.Xref.Widths := ⟨Pdf.Xref.width off, 2⟩
    match PdfRead.readXref (fieldFile wf (Pdf.Xref.row wf 1 off 0)) with
    | .error _ => t "PDF xref: a representable direct row reads" false
    | .ok x =>
      t "PDF xref: declared trailer and count"
        (x.root == some 1 && x.locs.size == 1 &&
          (x.trailer.bind (·.get? "Size")).bind PdfRead.Obj.int? == some 2)
      t "PDF xref: direct byte offset reads exactly" (match x.locs.get? 1 with
        | some (.direct actual) => actual == off
        | _ => false)
    for idx in [0, 255, 256, 65535] do
      match PdfRead.readXref (fieldFile wf (Pdf.Xref.row wf 2 off idx)) with
      | .error _ => t "PDF xref: a representable compressed row reads" false
      | .ok x =>
        t "PDF xref: stream id and index read exactly" (match x.locs.get? 1 with
          | some (.inStm actual index) => actual == off && index == idx
          | _ => false)
  match PdfRead.readXref (fieldFile ⟨4, 1⟩ (Pdf.Xref.row ⟨4, 1⟩ 2 1 256)) with
  | .error _ => t "PDF xref: index width bound is necessary" false
  | .ok x =>
    t "PDF xref: index width bound is necessary" (match x.locs.get? 1 with
      | some (.inStm 1 0) => true
      | _ => false)
  -- The complete writer, not just individual field encoders.
  let (doc, _) := Elab.run "synthetic.tex" "A small file."
  let pages := (layoutOf fs doc).pages
  for pages in [#[], pages] do
    let pdf := Pdf.write {} fs pages
    match PdfRead.readXref pdf with
    | .error _ => t "PDF writer: xref reads" false
    | .ok x =>
      t "PDF writer: root and allocated count read exactly"
        (x.root == some 1 &&
          (x.trailer.bind (·.get? "Size")).bind PdfRead.Obj.int? ==
            some (Int.ofNat (x.locs.size + 1)))
    t "PDF writer: font census reads program references"
      ((PdfCensus.census pdf).toOption.any (·.fontsEmbedded))
    match PdfRead.objects pdf with
    | .error _ => t "PDF writer: font objects read" false
    | .ok objects =>
      let es := objects.val
      let entry? n := es.find? (·.num == n)
      let obj n := ((entry? n).map (·.val)).getD .null
      let table := Pdf.tableOf {} fs pages {} #[]
      let programs := Pdf.facePrograms fs (Pdf.usedAll fs pages)
      for (face, k) in (Pdf.keepFaces fs pages).zipIdx do
        let key := if (fs.get face).isCff then "FontFile3" else "FontFile2"
        t "PDF writer: composite font names its descendant and Unicode map"
          ((obj (Pdf.ObjTable.type0Id k)).get? "DescendantFonts" ==
              some (.arr #[.ref (Pdf.ObjTable.cidId k) 0]) &&
            (obj (Pdf.ObjTable.type0Id k)).get? "ToUnicode" ==
              some (.ref (Pdf.ObjTable.toUniId k) 0))
        t "PDF writer: descendant names its descriptor"
          ((obj (Pdf.ObjTable.cidId k)).get? "FontDescriptor" ==
            some (.ref (Pdf.ObjTable.fdId k) 0))
        t "PDF writer: descriptor names its font program"
          ((obj (Pdf.ObjTable.fdId k)).get? key == some (.ref (table.fileId k) 0))
        t "PDF writer: decoded program equals the selected face program"
          ((entry? (table.fileId k)).any fun e =>
            e.decoded.toOption == some (some programs[k]!.1))
        let missingProgram := es.map fun e =>
          if e.num == Pdf.ObjTable.fdId k then
            { e with val := .dict #[("Type", .name "FontDescriptor")] }
          else e
        t "PDF writer: a descriptor without a program reference fails the census"
          (!(PdfCensus.ofEntries .null missingProgram).fontsEmbedded)
