import Tests.Support

open LeanTex.Core LeanTex.Cli

namespace Tests

private def triggerParse (file text : String) : Array Parse.Raw :=
  (Parse.parse file (Lex.lex file text).1).1

private def triggerDiags (file text : String) : Array Diag :=
  (Compat.rewrite file (triggerParse file text)).2.1

private def triggerAt (ds : Array Diag) (kind : DiagCode) (file : String)
    (line col : Nat) (trigger : String) : Bool :=
  let found := ds.filter fun d =>
    d.kind == kind && d.span.any fun s => s.file == file &&
      s.pos.line == line && s.pos.col == col
  found.size == 1 && found.all (·.trigger == some trigger)

/-- Replacement text crossing from execution into compatibility rewriting
names its actual macro use, even when definition coordinates collide with
an unrelated command in the caller. Written arguments and newly read files
keep their own sites; a selected default belongs to the macro use. -/
def diagnosticTriggerExpansionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let child := "child.tex"
  let root := "root.tex"
  let definition := "\\newcommand{\\run}{\n\n\\iftrue\n\\directlua{}\n\\fi}"
  let included (definitions source : String) :=
    let parent := triggerParse root source
    #[Parse.Raw.env (Parse.inputEnv child) (triggerParse child definitions) {}] ++
      parent.extract 2 parent.size
  for (label, extra, call) in [
      ("direct", "", "\\run"),
      ("nested", "\n\\newcommand{\\outer}[1]{#1\\run}", "\\outer{X}"),
      ("alias", "\n\\let\\alias\\run", "\\alias")] do
    let trigger := if label == "nested" then "\\outer" else call
    let source := "\\input{child}\n\\begin{document}\n" ++ call ++
      "\n\\RequirePackage{triggerunknown}\n\\end{document}"
    let (_, ds, _) := Compat.rewrite root (included (definition ++ extra) source)
    t s!"diagnostic trigger expansion: {label} later rewrite names the use"
      (triggerAt ds .W0104 root 3 1 trigger)
    t s!"diagnostic trigger expansion: {label} never borrows the colliding command"
      (!(ds.any fun d => d.kind == .W0104 && d.span.any
        (fun s => s.file == root && s.pos.line == 4)))
    t s!"diagnostic trigger expansion: {label} preserves definition and loss count"
      (triggerAt ds .W0104 child 4 1 "\\directlua" &&
        (ds.filter (·.kind == .W0104)).size == 2)
  let (_, hookDs, _) := Compat.rewrite root (included definition
    "\\input{child}\n\\AtBeginDocument{\\run}\n\\begin{document}\n\
      \\RequirePackage{triggerunknown}\n\\end{document}")
  t "diagnostic trigger expansion: deferred macro rewrite names the hook's call"
    (triggerAt hookDs .W0104 root 2 18 "\\run")
  let (_, argDs, _) := Compat.rewrite root (included
    "\\newcommand{\\pass}[1]{#1}\n\\newcommand{\\default}[1][\\directlua{}]{#1}"
    "\\input{child}\n\\begin{document}\n\\pass{\n  \\directlua{}}\n\
      \\default[\n  \\directlua{}]\n\\default\n\\end{document}")
  t "diagnostic trigger expansion: a written required argument keeps its source"
    (triggerAt argDs .W0104 root 4 3 "\\directlua")
  t "diagnostic trigger expansion: a written optional argument keeps its source"
    (triggerAt argDs .W0104 root 6 3 "\\directlua")
  t "diagnostic trigger expansion: an omitted default names its use"
    (triggerAt argDs .W0104 root 7 1 "\\default")
  let (definitions, definitionDs, _) := Compat.rewrite root (triggerParse root
    "\\newcommand{\\setup}[1]{\\newcommand{\\first}{\\iftrue First\\else BadFirst\\fi}\
      \\newcommand{\\second}{\\iftrue Second\\else BadSecond\\fi}}\n\
      \\setup{}\n\\begin{document}\\first{} \\second{}\\end{document}")
  t "diagnostic trigger expansion: relocation preserves distinct stored definitions"
    ((Parse.rawSrc definitions).contains
      "\\define \\first (){First}\\define \\second (){Second}" &&
      (definitionDs.filter (·.kind == .N0100)).size == 3)
  IO.FS.withTempDir fun dir => do
    let root := (dir / "root.tex").toString
    let child := (dir / "child.tex").toString
    let deep := (dir / "deep.tex").toString
    IO.FS.writeFile child "\\newcommand{\\load}[1]{\\input{deep}#1}"
    IO.FS.writeFile deep
      "\n\\iftrue\n\\directlua{}\n\\fi\n\\AtBeginDocument{\\directlua{}}"
    let source := "\\input{child}\n\n\n\n\n\\load{\\directlua{}}\n\
      \\begin{document}x\\end{document}"
    let (executed, readDs, _) ← Input.expandInputs root (triggerParse root source)
    let (_, ds, _) := Compat.rewriteExecuted executed
    t "diagnostic trigger expansion: macro includes have no read failures" readDs.isEmpty
    t "diagnostic trigger expansion: an included conditional owns its site"
      (triggerAt ds .N0114 deep 2 1 "\\iftrue")
    t "diagnostic trigger expansion: an included later rewrite keeps its site"
      (triggerAt ds .W0104 deep 3 1 "\\directlua")
    t "diagnostic trigger expansion: returning from a macro include restores the argument"
      (triggerAt ds .W0104 root 6 7 "\\directlua")
    t "diagnostic trigger expansion: an included deferred body keeps its site"
      (triggerAt ds .W0104 deep 5 18 "\\directlua")

/-- Ordinary command expansion and compatibility execution share source
ownership: replacement code belongs to the outer written call, while a
written argument retains its own site and command. -/
def diagnosticElabMacroChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let animation := "\\animategraphics{12}{poster.pdf}{}{}"
  let run (file source : String) :=
    (Elab.runRawsSpanned file (triggerParse file source)).2.1
  let owns (ds : Array Diag) (file : String) (line col : Nat) (trigger : String) :=
    let ds := ds.filter (·.kind == .W0110)
    ds.size == 2 && ds.all fun d =>
      d.span == some ⟨file, { line, col }⟩ && d.trigger == some trigger
  for (label, body, extra, call, col) in [
      ("inline", animation, "", "before \\movie", 8),
      ("block", "\\block{" ++ animation ++ "}", "", "\\movie", 1),
      ("nested", animation, "\\newcommand{\\outer}{\\movie}", "\\outer", 1)] do
    let trigger := if label == "nested" then "\\outer" else "\\movie"
    let ds := run "macro.tex"
      ("\\newcommand{\\movie}{" ++ body ++ "}" ++ extra ++
        "\n\\begin{document}\n" ++ call ++ "\n\\end{document}")
    t s!"diagnostic macro origin: {label} replacement names its written call"
      (owns ds "macro.tex" 3 col trigger)
  let child := triggerParse "definitions.tex" ("\\newcommand{\\movie}{" ++ animation ++ "}")
  let (_, included, _) := Elab.runRawsSpanned "caller.tex"
    (#[.env (Parse.inputEnv "definitions.tex") child {}] ++
      triggerParse "caller.tex" "\n\\begin{document}\n\\movie\n\\end{document}")
  t "diagnostic macro origin: an included definition reports the caller's file and line"
    (owns included "caller.tex" 3 1 "\\movie")
  let argument := run "argument.tex"
    ("\\newcommand{\\pass}[1]{#1}\n\\begin{document}\n\\pass{\n  " ++
      animation ++ "}\n\\end{document}")
  t "diagnostic macro origin: written arguments keep their own command and position"
    (owns argument "argument.tex" 4 3 "\\animategraphics")
  IO.FS.withTempDir fun dir => do
    let root := (dir / "caller.tex").toString
    IO.FS.writeFile (dir / "definitions.tex")
      ("\\newcommand{\\movie}{" ++ animation ++ "}")
    let source := "\\input{definitions}\n\\begin{document}\n\\movie\n\\end{document}"
    let (executed, readDs, _) ← Input.expandInputs root (triggerParse root source)
    let (_, ds, _) := Elab.runPrepared root (Elab.prepareExecuted root executed)
    t "diagnostic macro origin: fulfilled inputs retain the written macro trigger"
      (readDs.isEmpty && owns ds root 3 1 "\\movie")

/-- Compatibility diagnostics name the construct at their source site.
The spelling is independent of the message, subject and refused name; file
scope, nested commands and deferred replay must retain that ownership.
Adding it changes no other diagnostic field or compatibility behaviour. -/
def diagnosticTriggerChecks (ref : IO.Ref (List String)) : IO Unit := do
  diagnosticTriggerExpansionChecks ref
  diagnosticElabMacroChecks ref
  let t := check ref
  let file := "trigger.tex"
  let lua := triggerDiags file "\n  \\directlua{unread Lua}"
  let original := Diag.of .W0104
    "'\\directlua' is Lua code for luatex; the engine does not run Lua, so it is skipped"
    (some ⟨file, { line := 2, col := 3 }⟩)
    (help := "\\allow{W0104} accepts the skip") (subject := "ctrl:directlua")
  t "diagnostic trigger: directlua names the source command"
    (triggerAt lua .W0104 file 2 3 "\\directlua")
  t "diagnostic trigger: directlua preserves the entire existing record"
    (lua.map (fun d => { d with trigger := none }) == #[original])
  let (out, _, _) := Compat.rewrite file (triggerParse file "\\directlua{\\nested{unread}}")
  t "diagnostic trigger: skipped command operands remain unread" out.isEmpty
  for name in ["usepackage", "RequirePackage"] do
    let ds := triggerDiags file ("\\" ++ name ++ "{triggerunknown}")
    let refused := ds.filter (·.kind == .W0103)
    t s!"diagnostic trigger: {name} is the trigger, not the refused package"
      (triggerAt ds .W0103 file 1 1 ("\\" ++ name))
    t s!"diagnostic trigger: {name} preserves its name refusal"
      (refused.map (fun d => { d with trigger := none }) ==
        #[Diag.of .W0103 "package 'triggerunknown' is not supported; skipped"
          (some ⟨file, { line := 1, col := 1 }⟩) (refused := "triggerunknown")])
  let nested := triggerDiags file
    "\n{\\directlua{}}\n\\RequirePackage{triggeroutside}"
  t "diagnostic trigger: a nested command owns its diagnostic"
    (triggerAt nested .W0104 file 2 2 "\\directlua")
  t "diagnostic trigger: the next sibling owns its own diagnostic"
    (triggerAt nested .W0103 file 3 1 "\\RequirePackage")
  let env := triggerDiags file
    "\\begin{otherlanguage}{triggerunknown}\\directlua{}\\end{otherlanguage}"
  t "diagnostic trigger: a parent emission after descent keeps the parent's source"
    (triggerAt env .W0368 file 1 1 "\\begin{otherlanguage}")
  let silent := triggerDiags file
    "\\thispagestyle{plain}\n\\begin{document}x\\end{document}"
  t "diagnostic trigger: attribution does not count as an effect for the silence guard"
    (triggerAt silent .W0387 file 1 1 "\\thispagestyle")
  let cond := triggerDiags file "\\newif\\iftrigger\n\\triggertrue\n\\iftrigger x\\fi"
  for (line, trigger) in [(1, "\\newif"), (2, "\\triggertrue"), (3, "\\iftrigger")] do
    t s!"diagnostic trigger: conditional execution attributes {trigger}"
      (triggerAt cond .N0114 file line 1 trigger)
  let macroDs := triggerDiags file
    "\\newif\\iftrigger\n\\newcommand{\\turnon}{\\triggertrue}\n\
      \\begin{document}\n\\turnon\n\\end{document}"
  t "diagnostic trigger: a diagnostic relocated to a macro use names that use"
    (triggerAt macroDs .N0114 file 4 1 "\\turnon")
  let text := "\\qty[round-mode=places]{2}{\\triggerunit}"
  let (_, textDs, _) := Compat.rewriteText file (triggerParse file text)
  for kind in [DiagCode.N0100, .W0110, .W0381] do
    t s!"diagnostic trigger: text compatibility attributes {kind.code} to qty"
      (triggerAt textDs kind file 1 1 "\\qty")
  let textChild := "trigger-child.tex"
  let textDeep := "trigger-deep.tex"
  let textRaws := #[Parse.Raw.env (Parse.inputEnv textChild)
    (#[Parse.Raw.env (Parse.inputEnv textDeep)
      (triggerParse textDeep "\n\\ang[round-mode=places]{30}") { line := 1, col := 1 }] ++
      triggerParse textChild "\n\\qty[round-mode=places]{2}{m}") { line := 1, col := 1 }] ++
      triggerParse file "\n\\num[round-mode=places]{2}"
  let (_, textIncludeDs, _) := Compat.rewriteText file textRaws
  for (sourceFile, trigger) in [(textDeep, "\\ang"), (textChild, "\\qty"), (file, "\\num")] do
    t s!"diagnostic trigger: text include scope restores {trigger}"
      (triggerAt textIncludeDs .W0110 sourceFile 2 1 trigger)
  let repeated := triggerDiags file "\\directlua{}\n\\directlua{}"
  let tally := Diag.tallySites repeated
  t "diagnostic trigger: repeat accounting preserves both source sites"
    (tally.size == 2 &&
      triggerAt tally .W0104 file 1 1 "\\directlua" &&
      triggerAt tally .W0104 file 2 1 "\\directlua")
  t "diagnostic trigger: repeat counts, help and demotion are unchanged"
    (tally.map (fun d => (d.sites, d.demoted, d.help)) ==
      #[(2, false, some "\\allow{W0104} accepts the skip"), (0, true, none)])
  for d in lua do
    let (accepted, didAccept) := Diag.accept #["W0104"] false d
    t "diagnostic trigger: acceptance retains the trigger and its existing policy"
      (didAccept && accepted.demoted && accepted.trigger == some "\\directlua" &&
        { accepted with trigger := none } == original.demote)
    for outputs in [#[], #[Diag.Output.pdf], #[.html], #[.pdf, .html]] do
      t "diagnostic trigger: unscoped diagnostics retain their output selection"
        (Diag.forOutputs outputs #[d] == #[d] && d.output.isNone)
  IO.FS.withTempDir fun dir => do
    let root := (dir / "root.tex").toString
    let child := (dir / "child.tex").toString
    let deep := (dir / "deep.tex").toString
    IO.FS.writeFile child
      "\n  \\directlua{}\n\\input{deep}\n  \\AtBeginDocument{\\directlua{}}\n\
        \\usepackage{triggerchild}"
    IO.FS.writeFile deep "\n  \\usepackage{triggerdeep}"
    let source := " \\input{child}\n\\RequirePackage{triggerroot}\n\
      \\begin{document}x\\end{document}"
    let (executed, readDs, _) ← Input.expandInputs root (triggerParse root source)
    let (_, ds, _) := Compat.rewriteExecuted executed
    t "diagnostic trigger: synthetic includes have no read failures" readDs.isEmpty
    t "diagnostic trigger: an included command keeps its own source"
      (triggerAt ds .W0104 child 2 3 "\\directlua")
    t "diagnostic trigger: a deeper file with the same position keeps its own command"
      (triggerAt ds .W0103 deep 2 3 "\\usepackage")
    t "diagnostic trigger: returning from an include restores the parent source"
      (triggerAt ds .W0103 child 5 1 "\\usepackage" &&
        triggerAt ds .W0103 root 2 1 "\\RequirePackage")
    t "diagnostic trigger: deferred hooks use the body command in the declaring file"
      (triggerAt ds .W0104 child 4 20 "\\directlua")

end Tests
