module

import LeanTex.Core.PdfCensus
import LeanTex.Core.PdfFlateProof

/-! Consumers can classify the bytes a PDF carries and apply stream
round-trip contracts without importing scanner or proof implementation. -/

open LeanTex.Core
open PdfRead

namespace Tests.PdfCensusInterface

example : Obj → PdfCensus.Kind := PdfCensus.kindOf
example : Array Entry → Obj → Obj := PdfCensus.deref
example : Array Entry → Array Entry := PdfCensus.fontEntries
example : Array Entry → Entry → Bool := PdfCensus.fontEmbedded
example : Obj → Array String := PdfCensus.filtersOf
example : Obj → Option String := PdfCensus.colorSpaceOf
example : Array Entry → Obj → Obj := PdfCensus.catalogOf
example : Obj → Array Entry → PdfCensus.Census := PdfCensus.ofEntries
example : PdfCensus.Census → Array Entry → Bool := PdfCensus.xrefCovers
example : ByteArray → Except String PdfCensus.Census := PdfCensus.census

example (o : Obj) (h : o.get? "Type" = some (.name "Page")) :
    PdfCensus.kindOf o = .page :=
  PdfCensus.kindOf_page_exact o h

example (trailer : Obj) (es : Array Entry) :
    (PdfCensus.ofEntries trailer es).fontsEmbedded = true ↔
      ∀ e ∈ PdfCensus.fontEntries es, PdfCensus.fontEmbedded es e = true :=
  PdfCensus.census_fontsEmbedded_exact trailer es

example (dict : Obj) (data : ByteArray)
    (hsize : data.size ≤ maxDecoded)
    (hf : dict.get? "Filter" = some (.name "FlateDecode"))
    (hd : dict.get? "DL" = none) (hp : dict.get? "DecodeParms" = none) :
    decodeStream dict (Flate.deflate data) = .ok data :=
  decodeStream_deflate_exact dict data hsize hf hd hp

example (dict : Obj) (raw : ByteArray) (hf : dict.get? "Filter" = none) :
    decodeStream dict raw = .ok raw :=
  decodeStream_unfiltered_exact dict raw hf

example : True := by
  fail_if_success have := PdfCensus.fontSubtypes
  fail_if_success have := PdfCensus.nameOf
  fail_if_success have := PdfCensus.sortedUnique
  fail_if_success have := PdfCensus.strOf
  fail_if_success have := decodeStream_flate
  trivial

end Tests.PdfCensusInterface
