import LeanTex.Core.Elab

open LeanTex.Core

private abbrev InputObservation := String × String × String × Array String

private def inputObservations (source : String) : Array InputObservation :=
  let file := "requests.tex"
  let raws := (Parse.parse file (Lex.lex file source).1).1
  let reader : Compat.InputReader (StateM (Array InputObservation)) :=
    fun request context => do
      modify fun seen => seen.push
        (request.command, request.name, request.options, Compat.localStyCandidates request.call)
      return (none, context)
  (Elab.executeInputs reader file raws).run #[] |>.2

/-- Inspect the production evaluator's actual callback arguments. Dormant
definitions and skipped branches cannot pay for an executed loading call;
native options and native themes remain counterexamples to inferring a
file request from a refusal code. -/
def frontendInputRequestChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) := unless ok do ref.modify (name :: ·)
  let calls ← pure (inputObservations
    ("\\def\\probeLoad#1{\\usepackage[wide]{#1}}" ++
     "\\def\\probeDormant{\\usepackage{dormant}}" ++
     "\\iffalse\\usepackage{skipped}\\fi" ++
     "\\probeLoad{alphastyle, betaother,alphastyle}" ++
     "\\RequirePackage[small]{gammastyle}" ++
     "\\usetheme[compact]{Delta}" ++
     "\\usecolortheme{Epsilon}" ++
     "\\input{chapters/first}\\include{chapters/second}" ++
     "\\markdownInput[unknown=kept]{chapters/third}"))
  t "executed requests retain expanded operands and options"
    (calls == #[
      ("usepackage", "alphastyle, betaother,alphastyle", "wide",
        #["alphastyle", "betaother"]),
      ("RequirePackage", "gammastyle", "small", #["gammastyle"]),
      ("usetheme", "Delta", "compact", #["beamerthemeDelta"]),
      ("usecolortheme", "Epsilon", "", #["beamercolorthemeEpsilon"]),
      ("input", "chapters/first", "", #[]),
      ("include", "chapters/second", "", #[]),
      ("markdownInput", "chapters/third", "unknown=kept", #[])])
  let native ← pure (inputObservations
    "\\usepackage[unsupportedoption]{ulem}\\theme{inventedtheme}")
  t "native options do not introduce a local style candidate"
    (native == #[("usepackage", "ulem", "unsupportedoption", #[])])
  let nativeRun := Elab.run "requests.tex"
    "\\usepackage[unsupportedoption]{ulem}\\theme{inventedtheme}\\begin{document}body\\end{document}"
  t "refusal codes alone do not establish a file-loading request"
    (nativeRun.2.any (·.kind == .W0103) && nativeRun.2.any (·.kind == .W0319))
  let generated := "\\def\\probeLoad#1{\\usepackage{#1}}\\probeLoad{Expanded}"
  let original := (Parse.parse "requests.tex" (Lex.lex "requests.tex" generated).1).1
  t "expanded requests need not occur in the raw-source candidate census"
    (!(Compat.localStyCandidates original).contains "Expanded" &&
      inputObservations generated == #[("usepackage", "Expanded", "", #["Expanded"])])
  for row in Compat.themeAsking do
    let actual ← pure (inputObservations ("\\" ++ row.1 ++ "[choice]{Invented}"))
    t s!"expanded {row.1} asks for its registry prefix"
      (actual == #[(row.1, "Invented", "choice", #[row.2 ++ "Invented"])])
  let file := "input-evidence.tex"
  let source :=
    "\\def\\loadProbe#1{\\RequirePackage[choice]{#1}}\n" ++
    "\\loadProbe{MissingProbe}\n\\input{provided}\n" ++
    "\\begin{document}body\\end{document}"
  let raws := (Parse.parse file (Lex.lex file source).1).1
  let reader : Compat.InputReader (StateM (Array Compat.InputRequest)) :=
    fun request context => do
      modify (·.push request)
      return (if request.command == "input" then some #[] else none, context)
  let (executed, requests) := (Elab.executeInputs reader file raws).run #[]
  t "execution retains the reader's exact requests and answers"
    (executed.inputAttempts.map (·.request) == requests &&
      executed.inputAttempts.map (·.answered) == #[false, true])
  let prepared := Elab.prepareExecuted file executed
  t "preparation retains executed input evidence"
    (prepared.inputAttempts == executed.inputAttempts)
  for withdrawn in [#[], #["unrelated-picture"]] do
    let result := Elab.runPrepared file prepared (picWithdrawn := withdrawn)
    t "prepared runs retain input evidence across withdrawal"
      (result.2.2.inputAttempts == executed.inputAttempts)
  let final := Elab.runExecuted file executed
  let refused := final.2.filter fun d =>
    d.kind == .W0103 && d.refused == some "MissingProbe"
  t "a refused expanded package retains its source site"
    (refused.size == 1 && refused.all fun d =>
      d.span == requests[0]?.map (fun request => ⟨request.file, request.pos⟩))
