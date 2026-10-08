module

public import LeanTex.Core.PdfWriteContract
public import LeanTex.Core.PdfCensus
public import LeanTex.Cli.DriverDiag

public section

open LeanTex.Core

/-- The writer's storage domain past the ceiling the fixed `/W [1 4 2]`
layout once imposed: one object stream indexed by two bytes refused a
file needing more than 65536 compressed objects. The large input uses
only invented outline titles and no external fonts or resources; the
refusal the CLI reports as E0607 is the producer's own, on an invented
face name. These executable witnesses supplement the universal field
theorems; they are not proof premises. Parent registration calls this
block. -/
def pdfBoundsChecks (failures : IO.Ref (List String)) : IO Unit := do
  let check (name : String) (ok : Bool) : IO Unit := do
    unless ok do failures.modify (name :: ·)
  let fs : Font.FontSet :=
    { fonts := #[{ (default : Font.Font) with psName := "Synthetic" }] }
  let small := Pdf.prepare {} fs #[]
  check "PDF bounds: ordinary writer plan accepted" (decide small.WithinBounds)
  check "PDF bounds: checked bytes are the actual writer bytes"
    (match small.checked with
      | .ok b => b == Pdf.write {} fs #[]
      | .error _ => false)
  check "PDF bounds: positioned-page producer returns checked bytes"
    (match Pdf.writeChecked {} fs #[], small.checked with
      | .ok a, .ok b => a == b
      | _, _ => false)
  check "PDF bounds: a small file writes one object stream"
    (small.chunks.length == 1 && small.table.nStm == 1)
  -- The count is read through a ref: as a closed term, the plan could be
  -- copied into a loop's specialized body and rebuilt once per element.
  let count ← IO.mkRef 65536
  let outline := Array.replicate (← count.get) ({ title := "Synthetic" } : Layout.OutlineEntry)
  let large := Pdf.prepare {} fs #[] {} {} outline
  let lastItem := large.table.outlineItemId (outline.size - 1)
  check "PDF bounds: outline entries share the compressed index space"
    (large.compressed.length > 65536)
  check "PDF bounds: one object stream per capacity of compressed objects"
    (large.chunks.length == Pdf.objStmCount large.compressed.length &&
      large.chunks.length == large.table.nStm &&
      large.chunks.all (fun c => 0 < c.length && c.length ≤ Pdf.objStmCapacity))
  let largeChecked := large.checked
  match largeChecked with
  | .error _ => check "PDF bounds: a file past 65536 compressed objects builds" false
  | .ok bytes =>
    check "PDF bounds: the large file is the actual writer's bytes" (bytes == large.bytes)
    check "PDF bounds: the index field stays one byte past 65536 objects"
      (large.widths.second == 1 && large.widths.first == Pdf.Xref.width large.measure.body.size)
    match PdfRead.objects bytes with
    | .error _ => check "PDF bounds: the reader enumerates the large file" false
    | .ok es =>
      check "PDF bounds: every allocated object reads back"
        (es.val.size + 1 == large.table.size)
      let streams := es.val.filter fun e => PdfCensus.kindOf e.val == .objStm
      check "PDF bounds: every object stream the reader finds holds at most the capacity"
        (streams.size == large.table.nStm &&
          streams.all fun e => match e.val.get? "N" with
            | some (.int n) => 0 < n && n ≤ Pdf.objStmCapacity
            | _ => false)
      check "PDF bounds: every compressed object is read from one of those streams"
        (es.val.all fun e => match e.loc with
          | .inStm stm idx => idx < Pdf.objStmCapacity && streams.any (·.num == stm)
          | .direct _ => true)
      check "PDF bounds: the last outline item reads back with its title"
        ((es.val.find? (·.num == lastItem)).any fun e =>
          e.val.get? "Title" == some (.str "(Synthetic)".toUTF8))
    check "PDF bounds: the font census reads the large file"
      ((PdfCensus.census bytes).toOption.any (·.fontsEmbedded))
  check "PDF bounds: positioned-page producer builds the large outline"
    (match Pdf.writeChecked {} fs #[] {} {} outline, largeChecked with
      | .ok a, .ok b => a == b
      | _, _ => false)
  -- A real refusal, through the producer and the registry: a face whose
  -- name no PDF name spells is outside the writer's domain, and the CLI
  -- reports the producer's own error as E0607.
  let bad : Font.FontSet := { fonts := #[{ (default : Font.Font) with
    psName := "λ", unitsPerEm := 1000, numGlyphs := 2, widths := #[500, 500] }] }
  match Pdf.writeChecked {} bad #[] {} {} #[] #[] ⟨#[]⟩ #[] #[("invented program".toUTF8, false)] with
  | .ok _ => check "PDF bounds: the producer refuses an unspellable face name" false
  | .error e =>
    check "PDF bounds: the producer's refusal names the face's first object"
      (match e with
        | .objectSpelling id => id == Pdf.ObjTable.type0Id 0
        | _ => false)
    check "PDF bounds: the producer's refusal reaches the registry as E0607"
      ((LeanTex.Cli.DriverDiag.pdfWriteRefused e).code == DiagCode.E0607.code)
  check "PDF bounds: a storage refusal reaches the registry as E0607"
    ((LeanTex.Cli.DriverDiag.pdfWriteRefused (.objectStreamSize (PdfRead.maxDecoded + 1))).code ==
      DiagCode.E0607.code)
  check "PDF bounds: a one-byte index field wraps at 256, so its width is computed"
    (Binary.readNatBE 1 (Pdf.Xref.row ⟨4, 1⟩ 2 1 256) 5 == some 0)
