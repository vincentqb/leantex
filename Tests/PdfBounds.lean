import LeanTex.Core.PdfWriteContract
import LeanTex.Core.PdfCensus

open LeanTex.Core

/-- Regression for the false unbounded writer claim. The large input
uses only invented outline titles and no external fonts or resources.
These executable witnesses supplement the universal field theorems;
they are not proof premises. Parent registration calls this block. -/
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
  let outline := Array.replicate 65536 ({ title := "Synthetic" } : Layout.OutlineEntry)
  let large := Pdf.prepare {} fs #[] {} {} outline
  check "PDF bounds: outline entries share the compressed index space"
    (large.compressed.length > 65536)
  check "PDF bounds: oversized object index is refused"
    (match large.checked with | .error _ => true | .ok _ => false)
  check "PDF bounds: the old unbounded font census claim is false"
    (match PdfCensus.census large.bytes with
      | .error _ => true
      | .ok c => !c.fontsEmbedded)
  check "PDF bounds: the first unrepresentable index wraps to zero"
    (Binary.readNatBE 2 (Pdf.Xref.row 2 1 65536) 5 == some 0)
