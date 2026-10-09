module

public import LeanTex.Core.Diag
public import LeanTex.Core.Parse
public import LeanTex.Core.Compat
public import LeanTex.Core.Ir
import LeanTex.Core.Elab
import LeanTex.Core.Surface
import LeanTex.Core.Utf8
import LeanTex.Core.Bib
import LeanTex.Core.BibStyle
import LeanTex.Core.Data
import LeanTex.Cli.DriverDiag

/-! The driver's file frontend fulfils `\input`/`\include`,
`\markdownInput` and local `.sty` requests at their executed use. The pure
macro evaluator returns requests; this driver reads the file, parses its
surface once and resumes the same execution context with that answer.
Unused definitions and unselected branches have no file effects. Local
styles reserve their first load before execution; repeats and cycle back
edges read nothing. Distinct nested styles and ordinary inputs share the
existing eight-file nesting bound.

Every other file the *document* names is read here for the same reason:
the document's own bytes (`readSource`), the `.bib` its `\bibliography`
requests (`resolveBibliography`), the `.bib` its `\data` requests
(`resolveData`). Each is one decision — the file is there, or its absence
is a named loss — and each **returns** its diagnostics rather than
printing them, which is what lets a test run the decision instead of
restating it. A decision reachable only from the entry path in Main.lean
is a decision no test can witness: its code's witness then has to be a
hand-built value, and a value cannot tell you the driver stopped emitting
it. -/

namespace LeanTex.Cli.Input

open LeanTex.Core

/-- The first line of an `IO.Error`'s rendering. `IO.Error`'s own
`toString` appends a second `  file: <path>` line, and the path it repeats
is the one the message already names — so the second line says nothing new
and costs a newline inside a `Diag.message`, where one line per diagnostic
is what every reader, `Render.human`, and the registry golden's block
parse all assume. -/
private def reasonLine (s : String) : String :=
  (s.splitOn "\n").headD s

/-- The document's own bytes, or the diagnostic naming why they could not
be read (E0001). The read is the driver's first effect and its refusal is
the driver's first decision, so it is returned rather than printed. -/
public def readSource (file : String) : IO (Except Diag ByteArray) := do
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .ok bytes => return .ok bytes
  | .error e => return .error (DriverDiag.unreadableInput file (reasonLine (toString e)))

/-- Every included surface uses the document reader's UTF-8 and IO error
contract, and its one door (`Surface.fragment`): the file's reading is a
fragment of the same AST, wrapped as the file it came from; its bytes are
never converted to TeX source and parsed again. The wrapper carries the
file's name and nothing else: an include standing as a whole block sequence
— a document body, a frame's content — elaborates as the file alone does
(`Elab.elabBlocks_input_exact`, `Elab.elabBlockScope_input_exact`; for a
markdown file with any content, `Elab.markdownInput_blocks_exact`).
Mid-sequence the included blocks are the same and only the inner
frame-source offsets shift, which no statement here claims. Filename normalization
precedes the surface's extension policy: LaTeX's file-name sanitizer removes
paired quotes and trims both ends when the name contains a dot, only the
start otherwise (expl3-code.tex; quotedInputFilenameChecks). -/
private def readFragment (dir : System.FilePath) (file name : String) (pos : Pos)
    (prefer : String → String) (command : String) (surface : Surface) :
    IO (Array Parse.Raw × Array Diag) := do
  -- Do not turn an unmatched quote into an accepted, unquoted filename.
  let name := if name.toList.count '"' % 2 == 0 then
      let unquoted := name.replace "\"" ""
      if unquoted.contains '.' then unquoted.trimAscii.toString
      else unquoted.trimAsciiStart.toString
    else name
  let preferred := prefer name
  let candidate := dir / preferred
  let path ← if ← candidate.pathExists then pure candidate else pure (dir / name)
  if ← path.pathExists then
    match ← readSource path.toString with
    | .error d => return (#[], #[{ d with span := some ⟨file, pos⟩ }])
    | .ok bytes =>
      if let some err := Utf8.validate bytes then
        return (#[], #[err.toDiag path.toString])
      return surface.fragment path.toString (String.fromUTF8! bytes) pos
  else
    -- The span names `file`, the file the `\input` sits in — the reader
    -- goes to that line to fix it, and a directory has no line 5.
    let d := DriverDiag.inputMissing preferred (some ⟨file, pos⟩) command
    return (#[], #[d])

public def readInput (dir : System.FilePath) (file name : String) (pos : Pos) :
    IO (Array Parse.Raw × Array Diag) :=
  -- TeX's input scanner tries the default `.tex` suffix before the literal
  -- spelling, unless that spelling already ends in `.tex` (inputFileChecks).
  readFragment dir file name pos (fun name =>
    if name.endsWith ".tex" then name else name ++ ".tex") "input" .tex

/-- `\usepackage{p}` where `p.sty` exists beside the document is LaTeX's
own rule (ltfiles.dtx `\@onefilewithoptions`: find `p.sty` on the input
path and read it as TeX). Reading the file is this driver's effect, the
same door `\input` uses; the splice and the option machinery are the pure
core's (`Compat.applyLocalSty`), which wraps the file's text as its own
input fragment so every diagnostic names the `.sty` and its line. Where
no such file exists, the CTAN dispatch (W0103) applies unchanged. The
style file's own lexer and parser diagnostics are dropped: the file is
not the engine's to lint, and the splice carries its own positions. -/
public def expandLocalSty (dir : System.FilePath) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array (String × Option String × Pos)) := do
  let candidates := Compat.localStyCandidates raws
  if candidates.isEmpty then return (raws, #[])
  let mut stys : Array (String × Array Parse.Raw) := #[]
  for name in candidates do
    let path := dir / (name ++ ".sty")
    if ← path.pathExists then
      let text ← IO.FS.readFile path
      let (sraws, _) := Surface.read .tex (name ++ ".sty") text
      stys := stys.push (name, sraws)
  if stys.isEmpty then return (raws, #[])
  return Compat.applyLocalSty raws stys

private structure InputLog where
  diags : Array Diag := #[]
  spliced : Array (String × Option String × Pos) := #[]

private abbrev ReadM := StateT InputLog IO

/-- Fulfil one executed request. A local style is admitted before reading
its body; a compatible repeat or cycle back edge consumes no input depth.
Distinct nested files retain the existing eight-file input-stack bound.
An absent local style is left for normal package dispatch. Answers stay
parsed AST and execute before the requesting token stream continues. -/
private def readAt (dir : System.FilePath) (root : String) (depth : Nat) :
    Compat.InputReader ReadM := fun request context => do
  let input := ["input", "include", "markdownInput"].contains request.command
  if input then
    match depth with
    | 0 =>
      let d := { DriverDiag.inputTooDeep with span := some ⟨request.file, request.pos⟩ }
      modify fun log => { log with diags := log.diags.push d }
      return (none, context)
    | depth + 1 =>
      let (sub, diags) ← if request.command == "markdownInput" then do
          let prefer := fun name : String =>
            if (System.FilePath.mk name).extension.isSome then name else name ++ ".tex"
          let (sub, ds) ← readFragment dir request.file request.name request.pos prefer
            "markdownInput" .md
          let ds := if request.options.isEmpty then ds else ds.push <|
            Diag.of .W0110 s!"'\\markdownInput' options '{request.options}' are not applied; \
the file uses the Markdown document dialect" (some ⟨request.file, request.pos⟩)
              (subject := some "markdownInput:options")
          pure (sub, ds)
        else readInput dir request.file request.name request.pos
      modify fun log => { log with diags := log.diags ++ diags }
      let (answer, context) ←
        Elab.resumeInput (readAt dir root depth) context request.file sub
      return (some answer, context)
  else
    let mut out : Array Parse.Raw := #[]
    let mut current := context
    let mut handled := false
    -- Admit and execute each member before the next one. A dependency of
    -- the first member may already have loaded a later sibling.
    for (name, call) in request.packageCalls do
      if name.isEmpty || Compat.nativePackages.contains name then
        out := out ++ call
        continue
      let (options, reserved) := current.admitLocalPackage name request.options request.pos
      match options with
      | none =>
        -- The gate also diagnoses new options. Neither a compatible repeat
        -- nor a clash reads the file or spends another input-stack level.
        current := reserved
        handled := true
      | some passed =>
        let path := dir / (name ++ ".sty")
        unless ← path.pathExists do
          out := out ++ call
          continue
        match depth with
        | 0 =>
          let d := { DriverDiag.inputTooDeep with span := some ⟨request.file, request.pos⟩ }
          modify fun log => { log with diags := log.diags.push d }
          out := out ++ call
        | depth + 1 =>
          let text ← IO.FS.readFile path
          let (raws, _) := Surface.read .tex (name ++ ".sty") text
          let source := if request.file == root then none else some request.file
          modify fun log => { log with
            spliced := log.spliced.push (name ++ ".sty", source, request.pos) }
          let sub := Compat.spliceLocalPackage name passed raws request.pos
          let (answer, next) ←
            Elab.resumeInput (readAt dir root depth) reserved request.file sub
          out := out ++ answer
          current := next
          handled := true
    return if handled then (some out, current) else (none, context)

/-- Execute macros and fulfil input requests in source order. A definition
or unselected branch never reads a file; an actual use binds its filename
before the driver reads it, and the answer's definitions and flags are in
force at the caller's next token. The returned execution must continue
through `Elab.prepareExecuted` or `Elab.runExecuted`, without a second macro
pass. The other results are read diagnostics and the local-style records
whose N0020 counts become available after elaboration. Requests resolve
beside the document unless `dir` says where it stands. -/
public def expandInputs (file : String) (raws : Array Parse.Raw)
    (dir : System.FilePath := (System.FilePath.mk file).parent.getD ".") :
    IO (Compat.Executed × Array Diag × Array (String × Option String × Pos)) := do
  let (executed, log) ← (Elab.executeInputs (readAt dir file 8) file raws).run {}
  return (executed, log.diags, log.spliced)

/-- The bibliography request an elaborated document states (`Ir.bibRefs`),
fulfilled: each named `.bib` resolves beside the document, like `\input`,
and its text goes to the pure core (`Bib.apply`) — parsing, ordering,
formatting, and the citation rewrite all happen there, on every document
(`Bib.apply_no_cite`: no `.cite` node reaches a backend). A missing file is
E0503 naming the path; the marker stays empty and the citations' `?`
marks say so on the page. -/
public def resolveBibliography (file : String) (doc : Ir.Doc)
    (bibSpans : Array (String × Span) := #[]) :
    IO (Ir.Doc × Array Diag) := do
  let requested := Ir.bibRefs doc
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  for src in requested do
    let name := Bib.sourceName src
    let path := if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
      else dir / name
    if ← path.pathExists then
      sources := sources.push (src, ← IO.FS.readFile path)
    else
      diags := diags.push (DriverDiag.bibMissing src path.toString
        ((bibSpans.find? (·.1 == src)).map (·.2)))
  let (doc, applyDiags) := Bib.apply sources doc
  return (doc, diags ++ applyDiags)

/-- The data request a parsed document states (`Data.fileRefsAt`), fulfilled
before elaboration — the expansion needs the records where
`\begin{foreach}` stands, so this is the `resolveBibliography` shape moved
ahead of `Elab.runRaws`. Each named `.bib` resolves beside the document,
like `\input`; a missing file is E0365 naming the path, and the reads that
wanted its records say what stayed unresolved. -/
public def resolveData (file : String) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array Diag) := do
  unless Data.hasData raws do return (raws, #[])
  let requested := Data.fileRefsAt file raws
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  for (src, span) in requested do
    let name := Data.sourceName src
    let path := if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
      else dir / name
    if ← path.pathExists then
      sources := sources.push (src, ← IO.FS.readFile path)
    else
      diags := diags.push (DriverDiag.dataMissing src path.toString (some span))
  let (raws, expandDiags) := Data.expandData file sources raws
  return (raws, diags ++ expandDiags)

end LeanTex.Cli.Input
