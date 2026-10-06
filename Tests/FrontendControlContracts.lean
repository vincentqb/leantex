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
  for preamble in #["", "\\documentclass{article}",
      "\\documentclass{article}\\title{\\ref{missing}}",
      "\\documentclass{article}\\theme{daylight}"] do
    for word in #["kept", "naïve", "sample123"] do
      let input := preamble ++ "\\begin{document}\\zzRecovered{" ++ word ++ "}\\end{document}"
      let (tokens, _) := Lex.lex file input
      let (raws, _) := Parse.parse file tokens
      let prepared := Elab.prepare file raws
      let (entry, initial) := Elab.preparedBody file prepared
      let bodyRun := (Elab.runDocBody entry).run initial
      let preparedRun := Elab.runPrepared file prepared
      let final := Elab.run file input
      t s!"unknown argument survives actual body preparation and finalization: {preamble}/{word}"
        (Ir.blocksText bodyRun.1.1.body == word &&
          Ir.blocksText preparedRun.1.body == word &&
          Ir.blocksText final.1.body == word &&
          final.1.salvage.all (fun item => final.2.any
            (fun d => d.kind == item.code && d.subject == some item.subject)))
  let recovered : Ir.Recovered :=
    { code := .W0301, command := "zzUnaccounted", text := "kept" }
  let recoveryDoc : Ir.Doc :=
    { body := #[.para #[.text "kept"]], salvage := #[recovered] }
  let completion := Elab.completePrepared file (Elab.prepare file #[]) #[]
    recoveryDoc #[] { ctx := { file }, offset := 0 } {}
  t "completion accounts for the recovery records in its returned document"
    (completion.1.salvage.all (fun s =>
      completion.2.1.any (·.subject == some s.subject)) &&
      Ir.blocksText completion.1.body == "kept")
  let pending := { recovered with code := .W0370 }
  t "a recovery fallback preserves the code supplied by the producer"
    ((Elab.recoveryDiagnostic pending).kind == pending.code)
  t "synthetic recovery without option evidence makes no shape claim"
    ((Elab.recoveryDiagnostic recovered).help == none)
  let unrelated := Diag.of .W0346 "a separate declaration" none
    (subject := some recovered.subject)
  t "a different diagnostic code cannot account for recovered content"
    ((Elab.accountRecoveredItem #[unrelated] recovered).any
      (fun d => d.kind == recovered.code && d.subject == some recovered.subject))
  let footnote ← pure (Elab.run file
    "\\begin{document}\\footnotetext{kept}\\end{document}")
  t "pending footnote recovery records carry their emitted code"
    (!footnote.1.salvage.isEmpty && footnote.1.salvage.all (fun item =>
      footnote.2.any (fun d => d.subject == some item.subject && d.kind == item.code)))
  for (label, input) in #[
      ("plain", "\\begin{document}\n\\zzRecovered{kept}\n\\end{document}"),
      ("options", "\\begin{document}\n\\zzRecovered[option]{kept}\n\\end{document}"),
      ("mixed", "\\begin{document}\n\\zzRecovered{kept} " ++
        "\\zzRecovered[option]{also kept}\n\\end{document}"),
      ("mixed reversed", "\\begin{document}\n\\zzRecovered[option]{kept} " ++
        "\\zzRecovered{also kept}\n\\end{document}"),
      ("nested", "\\begin{document}\n\\zzRecovered{\\zzRecovered{kept}}\n\\end{document}"),
      ("replacement", "\\newcommand{\\recoverMe}{\\zzRecovered{kept}}\n" ++
        "\\begin{document}\n\\recoverMe\n\\end{document}"),
      ("replacement options", "\\newcommand{\\recoverMe}{\\zzRecovered[option]{kept}}\n" ++
        "\\begin{document}\n\\recoverMe\n\\end{document}")] do
    let (tokens, lexDiags) := Lex.lex file input
    let (raws, parseDiags) := Parse.parse file tokens
    let prepared := Elab.prepare file raws
    let (preamble, initial) := Elab.preparedPreamble file prepared
    let ((doc, table, report), st) := (Elab.finishPreamble file preamble).run initial
    let expectedReports := (Diag.tallySites
      (st.diags.map prepared.sourceTriggers.attribute)).filter
        (·.subject == some "ctrl:zzRecovered")
    let expected := expectedReports[0]?
    let resumed := Elab.completePrepared file prepared (lexDiags ++ parseDiags)
      doc table report { st with diags := #[] }
    let actual := resumed.2.1.find? (·.subject == some "ctrl:zzRecovered")
    t s!"recovery completion replays every complete producer record: {label}"
      (expectedReports == resumed.2.1.filter
        (·.subject == some "ctrl:zzRecovered"))
    t s!"recovery completion retains source and trigger: {label}"
      (match expected, actual with
      | some a, some b => a.span.isSome && a.span == b.span && a.trigger == b.trigger
      | _, _ => false)
    t s!"recovery completion retains the producer's code and option wording: {label}"
      (match expected, actual with
      | some a, some b => a.kind == b.kind && a.message == b.message && a.help == b.help
      | _, _ => false)
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
