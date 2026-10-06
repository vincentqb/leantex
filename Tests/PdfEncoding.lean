import LeanTex.Core.PdfEncoding

open LeanTex.Core.PdfRead

/-- Mutations of the raw spellings accepted by the object encoder.
The round-trip guarantee itself is `Obj.encodable_render_exact`; these
checks hold the executable boundary to its intended accepted domain. -/
def pdfEncodingChecks (failures : IO.Ref (List String)) : IO Unit := do
  let check (name : String) (ok : Bool) : IO Unit := do
    unless ok do failures.modify (name :: ·)
  let accepted : List Obj :=
    [.null, .bool true, .int (-123), .ref 65537 0, .real "-0.125",
     .name "a b/#", .str "(a\\(b\\)\\\\c)".toUTF8, .str "<ab 12 F>".toUTF8,
     .dict #[("Name", .arr #[.name "Synthetic", .int 0])]]
  check "PDF encoding: native source spellings accepted" (accepted.all Obj.encodable)
  let refused : List Obj :=
    [.name "", .name "λ", .real "12", .real "1.2 rest",
     .str "(missing".toUTF8, .str "(a)tail".toUTF8, .str "(a\\)".toUTF8,
     .str "<zz>".toUTF8, .str "<12".toUTF8, .str "<12>tail".toUTF8,
     .dict #[("", .int 0)], .dict #[("Child", .arr #[.name "λ"])]]
  check "PDF encoding: malformed and lossy spellings refused"
    (refused.all (fun o => !o.encodable))
