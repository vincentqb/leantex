import LeanTex.Core.ControlContract

open LeanTex.Core

/-- Consuming registry rows are checked at the actual compatibility
checkpoint and at the source frontend. The source-level counterexample
keeps execution outside the declarative erasure contract: definitions in
consumed groups can already have changed later text. -/
def frontendControlContractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let file := "controls.tex"
  let executed := Compat.execute file #[]
  let cursor := Compat.beginRewrite executed
  let finish (body : Array Parse.Raw) :=
    Elab.runRewriteFinal file {} #[] executed.sourceTriggers #[] #[]
      (fun _ _ => {}) (cursor.withDocument body {})
  let body (name : String) (arity : Nat) (payload : Array Parse.Raw) :=
    #[Parse.Raw.word "alpha" {}, .space, .ctrl name {}] ++
      Array.replicate arity (.group payload {}) ++
      #[.space, .word "omega" {}, .par {}, .word "tail" {}]
  let left : Array Parse.Raw :=
    #[.word "zzkeyword" {}, .group #[.word "nested" {}] {},
      .ctrl "unknownInside" {}, .group #[.word "unread" {}] {}]
  let right : Array Parse.Raw :=
    #[.env "center" #[.word "different" {}] {}, .ctrl "ref" {},
      .group #[.word "neverRequested" {}] {}]
  let source (name : String) (arity : Nat) (deferred : Bool) :=
    let call := "\\" ++ name ++ String.join (List.replicate arity "{zzkeyword}")
    "\\documentclass{article}" ++
      (if deferred then "\\AtBeginDocument{" ++ call ++ "}" else "") ++
      "\\begin{document}alpha " ++ (if deferred then "" else call) ++
      " omega\\end{document}"
  for row in Compat.meaningFree do
    let l ← pure (finish (body row.1 row.2.1 left))
    let r ← pure (finish (body row.1 row.2.1 right))
    t s!"control completion: {row.1} consumes arbitrary nested operands"
      (l == r)
    for deferred in #[false, true] do
      let result ← pure (Elab.run file (source row.1 row.2.1 deferred))
      t s!"control source: {row.1} consumes its groups, deferred={deferred}"
        (((Ir.blocksText result.1.body).splitOn "zzkeyword").length == 1)
      if row.2.2.isSome then
        t s!"control source: {row.1} retains its report, deferred={deferred}"
          (result.2.any (·.kind == .N0100))
  for row in Compat.configSkip do
    let l ← pure (finish (body row.1 row.2.1 left))
    let r ← pure (finish (body row.1 row.2.1 right))
    t s!"configuration completion: {row.1} preserves the complete result"
      (l == r && l.2.any (·.kind == .W0104))
    let result ← pure (Elab.run file (source row.1 row.2.1 false))
    t s!"configuration source: {row.1} retains its report"
      (result.2.any (·.kind == .W0104))
  let unknown ← pure (Elab.run file (source "zzNotAControl" 1 false))
  t "unknown controls retain group text and attribution"
    (((Ir.blocksText unknown.1.body).splitOn "zzkeyword").length == 2 &&
      unknown.1.salvage.any (·.command == "zzNotAControl") &&
      unknown.1.salvage.all (fun s =>
        unknown.2.any (·.subject == some s.subject)))
  let executeFirst (value : String) :=
    Elab.run file ("\\documentclass{article}\\begin{document}" ++
      "\\PackageWarning{\\gdef\\probe{" ++ value ++ "}}{message}" ++
      "\\probe\\end{document}")
  let executedLeft ← pure (executeFirst "left")
  let executedRight ← pure (executeFirst "right")
  t "counterexample: consumed groups can have earlier execution effects"
    (Ir.blocksText executedLeft.1.body == "left" &&
      Ir.blocksText executedRight.1.body == "right" &&
      executedLeft.2.any (·.kind == .N0100) &&
      executedRight.2.any (·.kind == .N0100))
