module

public import LeanTex.Core.ControlContract
import Tests.Support.Check

public section

open LeanTex.Core

/-- Consuming registry rows hold at the compatibility checkpoint and the source frontend, where
execution stays outside the declarative erasure contract. -/
def frontendControlContractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let file := "controls.tex"
  let executed := Compat.execute file #[]
  let cursor := Compat.beginRewrite executed
  let finish (body : Array Parse.Raw) :=
    Elab.runRewriteFinal file {} #[] executed.sourceTriggers #[] #[]
      (fun _ _ => {}) (cursor.withDocument body {})
  let operands (sig : List Compat.ArgKind) (payload : Array Parse.Raw) : Array Parse.Raw :=
    sig.foldl (init := #[]) fun acc k => match k with
      | .star => acc.push (.word "*" {})
      | .opt => acc ++ #[.sym '[' {}] ++ payload ++ #[.sym ']' {}]
      | .group | .needed => acc.push (.group payload {})
      | .kept => acc.push (.group #[.word "kept" {}] {})
  let body (row : Compat.CtrlRow) (payload : Array Parse.Raw) :=
    #[Parse.Raw.word "alpha" {}, .space, .ctrl row.name {}] ++ operands row.sig payload ++
      #[.space, .word "omega" {}, .par {}, .word "tail" {}]
  let left : Array Parse.Raw :=
    #[.word "zzkeyword" {}, .group #[.word "nested" {}] {},
      .ctrl "unknownInside" {}, .group #[.word "unread" {}] {}]
  let right : Array Parse.Raw :=
    #[.env "center" #[.word "different" {}] {}, .ctrl "ref" {},
      .group #[.word "neverRequested" {}] {}]
  let written (sig : List Compat.ArgKind) : String :=
    String.join (sig.map fun k => match k with
      | .star => "*"
      | .opt => "[zzkeyword]"
      | .group | .needed => "{zzkeyword}"
      | .kept => "{kept}")
  let source (row : Compat.CtrlRow) (deferred : Bool) :=
    let call := "\\" ++ row.name ++ written row.sig
    "\\documentclass{article}" ++
      (if deferred then "\\AtBeginDocument{" ++ call ++ "}" else "") ++
      "\\begin{document}alpha " ++ (if deferred then "" else call) ++
      " omega\\end{document}"
  let reported (row : Compat.CtrlRow) (ds : Array Diag) : Bool :=
    let noted := ds.any fun d => d.kind == .N0100 &&
      d.message.startsWith (Diag.translated s!"\\{row.name}")
    match row.action with
    | .tokens _ none => true
    | .tokens _ (some _) | .native .. | .skip _ => noted
    | .refuse code .ctrl _ _ =>
      ds.any fun d => d.kind == code && d.subject == some ("ctrl:" ++ row.name)
    | .refuse code .beamer _ _ =>
      ds.any fun d => d.kind == code && d.subject == some ("beamer:" ++ row.name)
    | .refuse code .each msg _ => ds.any fun d => d.kind == code && d.message == msg
    | .discard _ key =>
      ds.any fun d => d.kind == .N0100 && d.subject == some ("ctrl:nothing:" ++ key)
    | .inert => ds.any fun d => d.kind == .W0387 && d.subject == some ("ctrl:" ++ row.name)
    | .lower .. => true
  t "control table: every skip row names a kernel skip amount"
    (Compat.ctrlRows.all fun row => match row.action with
      | .skip amount => (Compat.kernelSkip amount).isSome
      | .tokens .. | .native _ | .refuse .. | .discard .. | .inert | .lower .. => true)
  -- A row answers its control after the \cite guard and before a document's list settings.
  let listed (preamble use after : String) : Array Diag :=
    (Elab.run file ("\\documentclass{article}" ++ preamble ++
      "\\begin{document}\\begin{itemize}\\item Alpha " ++ use ++ " more\\end{itemize}" ++ after ++
      "End.\\end{document}")).2
  let settled (ds : Array Diag) : Bool :=
    ds.any fun d => d.kind == .W0104 && (d.message.splitOn "itemsep").length > 1
  let cited := listed ("\\usepackage[style=authoryear]{biblatex}" ++
    "\\renewcommand{\\cite}{\\setlength{\\itemsep}{9pt}}") "\\cite" ""
  t "dispatch order: a renewed \\cite inside a list still takes the citation path"
    (cited.any (·.kind == .E0304) && !settled cited)
  let hooked := listed "\\renewcommand{\\AtBeginDocument}{\\setlength{\\itemsep}{9pt}}"
    "\\AtBeginDocument" ""
  t "dispatch order: a renewed hook inside a list is its row's refusal"
    (hooked.any (·.kind == .W0340) && !settled hooked)
  let later := listed "" "\\newpage" "\\gdef\\newpage{\\setlength{\\itemsep}{9pt}}"
  t "dispatch order: a use before a later definition keeps the row's meaning"
    (later.any (fun d => d.kind == .N0100 && d.message == Diag.translated "\\newpage") &&
      !settled later)
  let lowered := listed "" "\\pagestyle{zzstyle}" "\\gdef\\pagestyle{\\setlength{\\itemsep}{9pt}}"
  t "dispatch order: a lowered control used before a later definition keeps its meaning"
    (lowered.any (fun d => d.kind == .W0104 &&
        d.message == "ignored page style zzstyle") &&
      !settled lowered)
  let earlier := listed "\\renewcommand{\\ensuremath}{\\setlength{\\itemsep}{9pt}}"
    "\\ensuremath{x^2}" ""
  t "dispatch order: a lowered control after a redefinition the built-in overrides keeps meaning"
    (earlier.any (·.kind == .W0361) && !settled earlier && earlier.all (·.severity != .error))
  let missing := Elab.run file ("\\documentclass{article}\\usepackage{natbib}\\begin{document}" ++
    "alpha \\bibpunct{(}{)} \\section{Zzsec} omega\\end{document}")
  t "body declaration: one missing a group is left to elaboration with what follows it"
    (((Ir.blocksText missing.1.body).splitOn "(").length == 2 &&
      ((Ir.blocksText missing.1.body).splitOn "Zzsec").length == 2 &&
      !missing.2.any (·.kind == .W0340))
  let bare := Elab.run file ("\\documentclass{article}\\begin{document}alpha \\usepackage omega" ++
    "\\end{document}")
  t "body declaration: a body \\usepackage naming no package is left to elaboration"
    (bare.2.any (fun d => d.kind == .W0301 && (d.message.splitOn "'\\usepackage'").length > 1) &&
      !bare.2.any (·.kind == .W0340))
  let deferred := Elab.run file ("\\documentclass{article}\\usepackage{natbib}\\begin{document}" ++
    "\\newcommand{\\zzmac}{\\bibpunct{(}{)}}alpha \\zzmac{;} omega\\end{document}")
  t "body declaration: in a definition body one missing groups waits for its uses"
    (!deferred.2.any (·.kind == .W0340) &&
      ((Ir.blocksText deferred.1.body).splitOn "(").length == 2)
  for row in Compat.ctrlRows.filter (!·.action.reads) do
    let l ← pure (finish (body row left))
    let r ← pure (finish (body row right))
    t s!"control completion: {row.name} consumes arbitrary nested operands"
      (l == r && reported row l.2)
    let deferrable := row.action matches .discard .. | .inert
    for deferred in (if deferrable then #[false, true] else #[false]) do
      let result ← pure (Elab.run file (source row deferred))
      t s!"control source: {row.name} consumes its arguments, deferred={deferred}"
        (((Ir.blocksText result.1.body).splitOn "zzkeyword").length == 1)
      t s!"control source: {row.name} retains its report, deferred={deferred}"
        (reported row result.2)
  let unknown ← pure (Elab.run file ("\\documentclass{article}\\begin{document}alpha " ++
    "\\zzNotAControl{zzkeyword} omega\\end{document}"))
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
  for content in #[
      "first \\textbf{second} third",
      "naïve \\emph{café} $x+1$",
      "\\href{https://example.invalid}{a link}",
      "  nested {ordinary \\textit{groups}}  ",
      "\\zzNested{kept} and more",
      "\\label{kept-label}text \\ref{kept-label}"] do
    let opening := "\\documentclass{article}\\begin{document}"
    let ending := "\\end{document}"
    let refused := Elab.run file (opening ++ "\\zzRecovered{" ++ content ++ "}" ++ ending)
    let braced := Elab.run file (opening ++ "{" ++ content ++ "}" ++ ending)
    t s!"unknown grouped content follows its braced interpreter: {content}"
      (refused.1.body == braced.1.body &&
        refused.1.salvage.any (·.command == "zzRecovered") &&
        refused.1.salvage.all (fun item => refused.2.any
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

/-- A lowered control's gates read from its row: a declaration the body ignores is named in one
wording and leaves no ink, and a setting whose value is a macro parameter waits for its uses. -/
def ctrlGateChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let file := "gates.tex"
  let operandText (sig : List Compat.ArgKind) : String :=
    String.join (sig.map fun k => match k with
      | .star => ""
      | .opt => "[zzkeyword]"
      | .group | .needed | .kept => "{zzkeyword}")
  for row in Compat.ctrlRows do
    let .lower _ gates := row.action | continue
    let loads := String.join (gates.leaves.filterMap fun leave => match leave with
      | .without pkg => some s!"\\usepackage\{{pkg}}"
      | .inDef | .inBody | .inSeam | .outsidePreamble | .notCtrl _ => none)
    if let some help := gates.bodyHelp then
      let (doc, ds) := Elab.run file ("\\documentclass{article}" ++ loads ++
        "\\begin{document}alpha \\" ++ row.name ++ operandText row.sig ++ " omega\\end{document}")
      t s!"control gate: a body \\{row.name} leaves no ink, its neighbours kept"
        (((Ir.blocksText doc.body).splitOn "zzkeyword").length == 1 &&
          ((Ir.blocksText doc.body).splitOn "alpha").length == 2 &&
          ((Ir.blocksText doc.body).splitOn "omega").length == 2)
      t s!"control gate: a body \\{row.name} is named in the one wording"
        (ds.any fun d => d.kind == .W0340 && d.subject == some ("ctrl:" ++ row.name) &&
          d.message == Diag.bodyDeclaration row.name &&
          d.help == some help)
      let (_, early) := Elab.run file ("\\documentclass{article}" ++ loads ++ "\\" ++ row.name ++
        operandText row.sig ++ "\\begin{document}alpha omega\\end{document}")
      t s!"control gate: a preamble \\{row.name} is not named as a body declaration"
        (!early.any fun d => d.kind == .W0340 && d.subject == some ("ctrl:" ++ row.name))
    if gates.paramStands.isSome then
      let groups := row.sig.filter fun k => k != .opt && k != .star
      let params := String.join (groups.map fun _ => "{#1}")
      let waits (ds : Array Diag) : Bool := ds.any fun d => d.kind == .N0100 &&
        d.message == Diag.translated s!"\\{row.name}" &&
          d.detail == some "a rewrite at each use, where its parameters hold their values"
      let (_, ds) := Elab.run file ("\\documentclass{article}\\newcommand{\\zzwrap}[1]{\\" ++
        row.name ++ params ++ "}\\begin{document}omega\\end{document}")
      t s!"control gate: \\{row.name} holding a parameter waits for its uses"
        (waits ds && ds.all (·.severity == .note))
      let (_, written) := Elab.run file ("\\documentclass{article}\\newcommand{\\zzwrap}[1]{\\" ++
        row.name ++ operandText row.sig ++ "}\\begin{document}omega\\end{document}")
      t s!"control gate: \\{row.name} holding written values does not wait"
        (!waits written)

/-- Every lowering the table uses and `Lowering.emitsNothing` does not list emits raws on its
witness call under some row naming it, so the list of lowerings proved silent is complete. -/
def lowerEmitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let rows := Compat.ctrlRows.filterMap fun row => match row.action with
    | .lower l _ => some (row.name, l)
    | _ => none
  let mut seen : Array Compat.Lowering := #[]
  for (_, l) in rows do
    if seen.contains l then continue
    seen := seen.push l
    match l.emitWitness with
    | some w =>
      let names := rows.filterMap fun (n, l') => if l' == l then some n else none
      t s!"lowering completeness: {repr l} emits raws on its witness under one of {names}"
        (names.any fun n => l.emitsOn n w)
    | none => pure ()

/-- Each leave a lowered row names keeps its control as written exactly where its condition holds,
checked by two builds differing by the condition. -/
def ctrlLeaveChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let run (pre body : String) : Array Diag :=
    (Elab.run "leaves.tex" ("\\documentclass{article}" ++ pre ++ "\\begin{document}" ++ body ++
      "\\end{document}")).2
  let noted (ds : Array Diag) (s : String) : Bool :=
    ds.any fun d => d.kind == .N0100 && ((d.message ++ "\n" ++ (d.detail.getD "")).splitOn s).length > 1
  let unknown (ds : Array Diag) (n : String) : Bool :=
    ds.any fun d => d.kind == .W0301 && (d.message.splitOn s!"'\\{n}'").length > 1
  let defined := "\\newcommand{\\zzmac}{\\usepackage{xcolor}}"
  t "control leave: a load in a definition body waits for the definition's use"
    (!noted (run defined "Alpha.") "package xcolor" &&
      noted (run (defined ++ "\\zzmac") "Alpha.") "package xcolor")
  t "control leave: a blueprint declaration without the package is left to elaboration"
    (unknown (run "\\graphcolor{a}{b}{c}" "Alpha.") "graphcolor" &&
      !unknown (run "\\usepackage{blueprint}\\graphcolor{a}{b}{c}" "Alpha.") "graphcolor")
  t "control leave: an allocation naming no control word is left to elaboration"
    (unknown (run "\\newlength{zz}" "Alpha.") "newlength" &&
      noted (run "\\newlength{\\zz}" "Alpha.") "newlength")
  t "control leave: a biblatex resource in the body is left to elaboration"
    (noted (run "\\usepackage{biblatex}\\bibliography{refs}" "Alpha.") "addbibresource" &&
      !noted (run "\\usepackage{biblatex}" "Alpha.\\bibliography{refs}") "addbibresource")
  t "control leave: a style in a hook's seam is left to elaboration"
    (noted (run "\\usepackage{natbib}\\bibliographystyle{plainnat}" "Alpha.") "as natbib reads" &&
      !noted (run "\\usepackage{natbib}\\AtBeginDocument{\\bibliographystyle{plainnat}}" "Alpha.")
        "as natbib reads")
