import Tests.Support
import LeanTex.Core.PdfFontContract

open LeanTex.Core

private def fieldFile (row : ByteArray) : ByteArray :=
  let head := "%PDF-2.0\n".toUTF8
  let data := Pdf.Xref.row 0 0 65535 ++ row
  let out := Pdf.rowInto head 2
    (.stream "/Type /XRef /Size 2 /W [1 4 2] /Index [0 2] /Root 1 0 R" data)
  out ++ s!"startxref\n{head.size}\n%%EOF\n".toUTF8

/-- The reader consumes the fields the PDF writer declares, including the
last representable byte offset and object-stream index. The out-of-domain
case witnesses why the universal field law requires a width bound. -/
def pdfWriterChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  t "PDF xref: persisted direct-row bytes"
    (Pdf.Xref.row 1 16909060 0 == bytes [1, 1, 2, 3, 4, 0, 0])
  t "PDF xref: persisted compressed-row bytes"
    (Pdf.Xref.row 2 16909060 1286 == bytes [2, 1, 2, 3, 4, 5, 6])
  let entries : Array Pdf.Xref.Entry :=
    #[.free 0 65535, .direct 4294967295 0, .compressed 16909060 65535,
      .direct 256 0, .compressed 1 0]
  let encoded := Pdf.Xref.encode entries
  t "PDF xref: every payload row has seven bytes" (encoded.size == 7 * entries.size)
  for (e, i) in entries.zipIdx do
    t "PDF xref: fields at their actual row position"
      (Binary.readNatBE 1 encoded (7 * i) == some e.fields.1.toNat &&
        Binary.readNatBE 4 encoded (7 * i + 1) == some e.fields.2.1 &&
        Binary.readNatBE 2 encoded (7 * i + 5) == some e.fields.2.2)
  let table := Pdf.objTable #[] {} #[] 0 0 0
  let select := Pdf.xrefEntry table (fun _ => some 23) (fun _ => some 99) 177
  t "PDF xref: its own direct row takes priority over the compressed index"
    (select table.xrefId == .direct 177 0 && select 1 == .compressed table.objStmId 23)
  t "PDF xref: absent direct objects are free"
    (Pdf.xrefEntry table (fun _ => none) (fun _ => none) 177 1 == .free 0 0)
  t "PDF xref: allocation count includes the free-list head"
    ((Pdf.xrefEntries table (fun _ => none) (fun _ => some 99) 177).size == table.size)
  for off in [0, 255, 256, 65535, 65536, 4294967295] do
    match PdfRead.readXref (fieldFile (Pdf.Xref.row 1 off 0)) with
    | .error _ => t "PDF xref: a representable direct row reads" false
    | .ok x =>
      t "PDF xref: declared trailer and count"
        (x.root == some 1 && x.locs.size == 1 &&
          (x.trailer.bind (·.get? "Size")).bind PdfRead.Obj.int? == some 2)
      t "PDF xref: direct byte offset reads exactly" (match x.locs.get? 1 with
        | some (.direct actual) => actual == off
        | _ => false)
    for idx in [0, 255, 256, 65535] do
      match PdfRead.readXref (fieldFile (Pdf.Xref.row 2 off idx)) with
      | .error _ => t "PDF xref: a representable compressed row reads" false
      | .ok x =>
        t "PDF xref: stream id and index read exactly" (match x.locs.get? 1 with
          | some (.inStm actual index) => actual == off && index == idx
          | _ => false)
  match PdfRead.readXref (fieldFile (Pdf.Xref.row 2 1 65536)) with
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
      let table := Pdf.tableOf fs pages {} #[]
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
