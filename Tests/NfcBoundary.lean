module

import all LeanTex.Core.Nfc
import LeanTex.Core.NfcData

/-! The normalization implementation stays private. These tests inspect its
generated tables through a same-package import and export only runnable checks. -/

namespace Tests.NfcBoundary

open LeanTex.Core

/-- UAX #15 idempotence over every decomposition key and table-loader byte
accounting, supplementing the universal ASCII normalization theorem. -/
public def tableChecks (t : String → Bool → IO Unit) : IO Unit := do
  let acute := String.ofList ['\u0301']
  let notIdempotent := Nfc.tables.get.decomp.fold (init := #[]) fun bad k _ =>
    let c := String.ofList [Char.ofNat k.toNat]
    [c, c ++ c, c ++ acute, acute ++ c].foldl (init := bad) fun bad s =>
      let once := Nfc.normalize s
      if Nfc.normalize once == once then bad else bad.push s
  t s!"nfc is idempotent over the decomposition keys ({notIdempotent.size} broke it)"
    notIdempotent.isEmpty

  -- The loader reads past a table's end as zero. The decomposition records
  -- have variable width, so their census accounts for bytes, not just entries.
  let tb := Nfc.load ()
  t "nfc: every fixed-width table is a whole number of entries"
    (NfcData.ccc.toUTF8.size % 8 == 0 && NfcData.comp.toUTF8.size % 18 == 0 &&
     NfcData.letters.toUTF8.size % 12 == 0 && NfcData.lower.toUTF8.size % 12 == 0)
  t "nfc: the loader keeps one entry per fixed-width entry the generator wrote"
    (tb.ccc.size == NfcData.ccc.toUTF8.size / 8 &&
     tb.comp.size == NfcData.comp.toUTF8.size / 18 &&
     tb.letters.size == NfcData.letters.toUTF8.size / 12 &&
     tb.lower.size == NfcData.lower.toUTF8.size / 12)
  t "nfc: the decomposition records account for every byte of their table"
    (tb.decomp.fold (init := 0) (fun n _ parts => n + 7 + 6 * parts.size) ==
      NfcData.decomp.toUTF8.size)

/-- Backslash separates normalization slices. Exercise the caller's source
attribution predicate on every scalar and expanded decomposition in the tables. -/
public def escapeChecks (t : String → Bool → IO Unit)
    (prefixAgrees : String → Bool) : IO Unit := do
  let nfc := Nfc.tables.get
  let escape := '\\'
  let decompositions := nfc.decomp.toList
  t "image origin: NFC tables preserve the escape-boundary premise"
    (nfc.ccc.getD escape.val 0 == 0 && !nfc.decomp.contains escape.val &&
      decompositions.all (fun (_, parts) => !parts.contains escape) &&
      nfc.comp.toList.all fun (pair, result) =>
        pair.toNat / 0x100000000 != escape.toNat &&
        pair.toNat % 0x100000000 != escape.toNat && result != escape)
  t "image origin: every decomposition scalar preserves authored sites and raw triggers"
    (!decompositions.isEmpty && decompositions.all fun (scalar, _) =>
      prefixAgrees (String.ofList [Char.ofNat scalar.toNat]))
  t "image origin: every expanded decomposition preserves authored sites and raw triggers"
    (!decompositions.isEmpty && decompositions.all fun (_, parts) =>
      prefixAgrees (String.ofList parts.toList))

end Tests.NfcBoundary
