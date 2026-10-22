module

public import LeanTex.Core.PdfWriteContract
public import LeanTex.Core.PdfCensus
public import LeanTex.Cli.DriverDiag
import Tests.Support.Check

public section

open LeanTex.Core

/-- The writer's object-stream storage beyond 65536 compressed objects, and its refusal outside its
domain. -/
def pdfBoundsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let fs : Font.FontSet :=
    { fonts := #[{ (default : Font) with psName := "Synthetic" }] }
  let small := Pdf.prepare {} fs #[]
  check ref "PDF bounds: ordinary writer plan accepted" (decide small.WithinBounds)
  check ref "PDF bounds: checked bytes are the actual writer bytes"
    (match small.checked with
      | .ok b => b == Pdf.write {} fs #[]
      | .error _ => false)
  check ref "PDF bounds: positioned-page producer returns checked bytes"
    (match Pdf.writeChecked {} fs #[], small.checked with
      | .ok a, .ok b => a == b
      | _, _ => false)
  check ref "PDF bounds: a small file writes one object stream"
    (small.chunks.length == 1 && small.table.nStm == 1)
  -- Read through a ref, so no loop closure copies the plan as a closed term.
  let count ← IO.mkRef 65536
  let outline := Array.replicate (← count.get) ({ title := "Synthetic" } : Layout.OutlineEntry)
  let large := Pdf.prepare {} fs #[] {} {} outline
  let lastItem := large.table.outlineItemId (outline.size - 1)
  check ref "PDF bounds: outline entries share the compressed index space"
    (large.compressed.length > 65536)
  check ref "PDF bounds: one object stream per capacity of compressed objects"
    (large.chunks.length == Pdf.objStmCount large.compressed.length &&
      large.chunks.length == large.table.nStm &&
      large.chunks.all (fun c => 0 < c.length && c.length ≤ Pdf.objStmCapacity))
  let largeChecked := large.checked
  match largeChecked with
  | .error _ => check ref "PDF bounds: a file past 65536 compressed objects builds" false
  | .ok bytes =>
    check ref "PDF bounds: the large file is the actual writer's bytes" (bytes == large.bytes)
    check ref "PDF bounds: the index field stays one byte past 65536 objects"
      (large.widths.second == 1 && large.widths.first == Pdf.Xref.width large.measure.body.size)
    match PdfRead.objects bytes with
    | .error _ => check ref "PDF bounds: the reader enumerates the large file" false
    | .ok es =>
      check ref "PDF bounds: every allocated object reads back"
        (es.val.size + 1 == large.table.size)
      let streams := es.val.filter fun e => PdfCensus.kindOf e.val == .objStm
      check ref "PDF bounds: every object stream the reader finds holds at most the capacity"
        (streams.size == large.table.nStm &&
          streams.all fun e => match e.val.get? "N" with
            | some (.int n) => 0 < n && n ≤ Pdf.objStmCapacity
            | _ => false)
      check ref "PDF bounds: every compressed object is read from one of those streams"
        (es.val.all fun e => match e.loc with
          | .inStm stm idx => idx < Pdf.objStmCapacity && streams.any (·.num == stm)
          | .direct _ => true)
      check ref "PDF bounds: the last outline item reads back with its title"
        ((es.val.find? (·.num == lastItem)).any fun e =>
          e.val.get? "Title" == some (.str "(Synthetic)".toUTF8))
    check ref "PDF bounds: the font census reads the large file"
      ((PdfCensus.census bytes).toOption.any (·.fontsEmbedded))
  check ref "PDF bounds: positioned-page producer builds the large outline"
    (match Pdf.writeChecked {} fs #[] {} {} outline, largeChecked with
      | .ok a, .ok b => a == b
      | _, _ => false)
  let bad : Font.FontSet := { fonts := #[{ (default : Font) with
    psName := "λ", unitsPerEm := 1000, numGlyphs := 2, widths := #[500, 500] }] }
  match Pdf.writeChecked {} bad #[] {} {} #[] #[] ⟨#[]⟩ #[] #[("invented program".toUTF8, false)] with
  | .ok _ => check ref "PDF bounds: the producer refuses an unspellable face name" false
  | .error e =>
    check ref "PDF bounds: the producer's refusal names the face's first object"
      (match e with
        | .objectSpelling id => id == Pdf.ObjTable.type0Id 0
        | _ => false)
    check ref "PDF bounds: the producer's refusal reaches the registry as E0006"
      ((LeanTex.Cli.DriverDiag.pdfWriteRefused e).code == DiagCode.E0006.code)
  check ref "PDF bounds: a storage refusal reaches the registry as E0006"
    ((LeanTex.Cli.DriverDiag.pdfWriteRefused (.objectStreamSize (PdfRead.maxDecoded + 1))).code ==
      DiagCode.E0006.code)
  check ref "PDF bounds: a one-byte index field wraps at 256, so its width is computed"
    (Binary.readNatBE 1 (Pdf.Xref.row ⟨4, 1⟩ 2 1 256) 5 == some 0)
