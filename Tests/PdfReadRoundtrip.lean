module

public import LeanTex.Core.PdfRead
public import LeanTex.Core.PdfNameProof
public import LeanTex.Core.PdfStringProof
import Tests.Support

public section

open LeanTex.Core

/-! Counterexamples to `formerPrimitivePremise`: a decimal point, an opening delimiter or a nonempty
name alone does not make a spelling reversible. -/

private def formerPrimitivePremise : PdfRead.Obj → Bool
  | .real raw => raw.contains '.'
  | .str raw => 2 ≤ raw.size && (raw[0]? == some 40 || raw[0]? == some 60)
  | .name n => n != ""
  | _ => false

def pdfReadRoundtripChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) := check ref s!"PDF object round trip: {name}"
  let witnesses : Array (String × PdfRead.Obj) := #[
    ("non-numeric real prefix", .real "a."),
    ("trailing real bytes", .real "1.x"),
    ("unclosed literal", .str "(x".toUTF8),
    ("dictionary masquerading as a string", .str "<<>>".toUTF8),
    ("trailing literal bytes", .str "(a) trailing".toUTF8),
    ("trailing hex bytes", .str "<a>tail".toUTF8),
    ("name outside the byte alphabet", .name "λ")]
  for (name, o) in witnesses do
    let bytes := o.render
    t s!"former premise accepts {name}" (formerPrimitivePremise o)
    t s!"former contract fails for {name}"
      ((PdfRead.parseVal bytes 0).toOption != some (o, bytes.size))
  t "real consumes only its numeric prefix"
    ((PdfRead.parseVal "1.x".toUTF8 0).toOption == some (.real "1.", 2))
  t "a string tag does not alter dictionary syntax"
    ((PdfRead.parseVal (PdfRead.Obj.str "<<>>".toUTF8).render 0).toOption
      == some (.dict #[], 4))
  t "non-byte names lose their high bits"
    ((PdfRead.parseVal (PdfRead.Obj.name "λ").render 0).toOption == some (.name "»", 4))
  t "byte-valued names remain reversible"
    ((PdfRead.parseVal (PdfRead.Obj.name "é").render 0).toOption == some (.name "é", 4))
  let values : Array PdfRead.Obj := #[
    .int (10^80), .int (-(10^80)), .real "-.25",
    .str "(outer(inner)\\)tail)".toUTF8, .str "<0a ff 1>".toUTF8,
    .arr #[.int 12, .ref 7 0, .str "(x)".toUTF8],
    .dict #[("a/b", .arr #[.bool true, .null, .name "é"])]]
  for o in values do
    let bytes := o.render
    t "primitive or compound object retains its bytes"
      ((PdfRead.parseVal bytes 0).toOption == some (o, bytes.size))
  for c in [0:256] do
    let o := PdfRead.Obj.name (String.singleton (Char.ofNat c))
    let bytes := o.render
    t s!"name byte {c} remains reversible"
      ((PdfRead.parseVal bytes 0).toOption == some (o, bytes.size))

/-- Arrays and dictionaries of many entries parse whole, each within a hang guard. -/
def pdfWideContainerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let count ← IO.mkRef 300000
  let n ← count.get
  let arr := ("[" ++ String.join (List.replicate n "1 ") ++ "2]").toUTF8
  let dict := ("<<" ++ String.join ((List.range n).map fun i => s!"/K{i} {i} ") ++ ">>").toUTF8
  let arrValue : PdfRead.Obj := .arr ((Array.replicate n (.int 1)).push (.int 2))
  let dictValue : PdfRead.Obj :=
    .dict ((Array.range n).map fun (i : Nat) => (s!"K{i}", .int (i : Int)))
  for (what, bytes, value) in [("an array", arr, arrValue), ("a dictionary", dict, dictValue)] do
    let t0 ← IO.monoMsNow
    let read ← IO.lazyPure fun _ => PdfRead.parseVal bytes 0
    let ms := (← IO.monoMsNow) - t0
    check ref s!"PDF object reader: {what} of {n} entries reads exactly ({ms} ms)"
      (read.toOption == some (value, bytes.size))
    check ref s!"hang guard: {what} of {n} entries within {hangGuardMs 400} ms ({ms} ms)"
      (ms < hangGuardMs 400)
