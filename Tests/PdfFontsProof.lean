module

public import LeanTex.Core.PdfFontsProof

public section

open LeanTex.Core

private def syntheticFace (name : String) (cff : Bool) : Font.Font :=
  { (default : Font.Font) with
    psName := name, isCff := cff, unitsPerEm := 1000,
    numGlyphs := 2, widths := #[500, 500] }

private def twoFacePage : Layout.PageOut :=
  { lines := #[{ (default : Layout.LineOut) with
      segs := #[
        .run 0 .black none 0 #[(1, 'A', 0)] 0 {} {} 0 none default,
        .run 1 .black none 0 #[(1, 'B', 0)] 0 {} {} 0 none default] }] }

/-- Exercise the actual checked producer and its structural census with
both font-program dictionary shapes, both PDF versions, and full/subset
names. Invented program bytes witness transport and reference recovery;
they make no claim about sfnt validity or viewer rendering.

Malformed source names are refused by the producer itself. The separate
`pdfBoundsChecks` block reads the census of a 65536-entry outline, past
the compressed-object ceiling the fixed-width xref once imposed. -/
def pdfFontsProofChecks (failures : IO.Ref (List String)) : IO Unit := do
  let check (name : String) (ok : Bool) : IO Unit := do
    unless ok do failures.modify (name :: ·)
  let fs : Font.FontSet :=
    { fonts := #[syntheticFace "SyntheticTrueType" false, syntheticFace "SyntheticCff" true] }
  let pages := #[twoFacePage]
  check "PDF fonts: both synthetic faces contribute glyphs"
    (Pdf.keepFaces fs pages == #[0, 1])
  for version in ["1.7", "2.0"] do
    for subset in [false, true] do
      let info : Ir.Meta :=
        { pdfVersion := some version, title := some "Invented (font) \\ census λ" }
      let outline : Array Layout.OutlineEntry := #[{ title := "Invented λ outline" }]
      let programs : Array (ByteArray × Bool) :=
        #[("short program".toUTF8, subset), (⟨Array.replicate 4096 17⟩, subset)]
      let plan := Pdf.prepare {} fs pages info {} outline #[] ⟨#[]⟩ #[] programs
      check "PDF fonts: ordinary source belongs to the complete checked domain"
        (decide plan.WithinDomain)
      match Pdf.writeChecked {} fs pages info {} outline #[] ⟨#[]⟩ #[] programs with
      | .error _ => check "PDF fonts: checked native producer succeeds" false
      | .ok bytes =>
        check "PDF fonts: successful production keeps the actual writer bytes"
          (bytes == Pdf.write {} fs pages info {} outline #[] ⟨#[]⟩ #[] programs)
        check "PDF fonts: actual reader counts both embedded font families"
          ((PdfCensus.census bytes).toOption.any fun c =>
            c.fontsEmbedded && c.fonts == 4 && c.type0Fonts == 2)
        match PdfRead.objects bytes with
        | .error _ => check "PDF fonts: complete object recovery succeeds" false
        | .ok objects =>
          for k in [0:2] do
            let program := objects.val.find? (·.num == plan.table.fileId k)
            check "PDF fonts: actual decoded program equals its selected source"
              (program.any fun e => e.decoded.toOption == some (some programs[k]!.1))
            check "PDF fonts: compressed and uncompressed transport both exercised"
              (program.any fun e =>
                (e.val.get? "Filter").isSome == (k == 1))
  for name in ["", "λ"] do
    let bad : Font.FontSet := { fonts := #[syntheticFace name false] }
    let programs := #[("invented program".toUTF8, false)]
    let plan := Pdf.prepare {} bad #[] {} {} #[] #[] ⟨#[]⟩ #[] programs
    check "PDF fonts: spelling counterexample still fits all numeric bounds"
      (decide plan.WithinBounds && !decide plan.Encodable)
    check "PDF fonts: source spelling refusal names the first offending font object"
      (match Pdf.writeChecked {} bad #[] {} {} #[] #[] ⟨#[]⟩ #[] programs with
        | .error (.objectSpelling id) => id == Pdf.ObjTable.type0Id 0
        | _ => false)
