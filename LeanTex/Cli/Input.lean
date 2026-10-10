module

public import LeanTex.Core.Diag
public import LeanTex.Core.Parse
public import LeanTex.Core.Compat
public import LeanTex.Core.Ir
public import LeanTex.Core.Encoding
import LeanTex.Core.Elab
import LeanTex.Core.Surface
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
restating it. Every file's bytes become text through one door
(`Encoding.readTex`, `Encoding.readMarkdown`), once per run, in the encoding
the document declares wherever its declaration runs: the declaration
governs every file the document reads, so a file read under another is
read again under it. Bytes never refuse a file, and never escape as an
exception. A decision reachable only from the entry path in Main.lean
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

/-- What a run knows of the files it reads: the reads' diagnostics, the
local styles spliced, and the input encoding — the declaration each file is
read under and the ledger of what each file read as. -/
private structure InputLog where
  diags : Array Diag := #[]
  spliced : Array (String × Option String × Pos) := #[]
  /-- Where every file is read under one declaration the run already knows
  (`none` inside for UTF-8): a second pass, under the declaration the first
  settled on, since that declaration governs every file of the document. -/
  fixed : Option (Option Encoding.Declared) := none
  /-- The declaration the document's own preamble makes, which a file read
  before any `inputenc` load runs is read under. -/
  guess : Option Encoding.Declared := none
  /-- The first `inputenc` load executed, and each file read. -/
  ledger : Encoding.Ledger := {}
  /-- Whether `inputenc` has loaded: the first load's options are the ones
  applied, as a later load's new options are not (W0110). -/
  inputenc : Bool := false
  /-- Each file decoded in this run, so a file read twice is decoded once and
  its losses named once. -/
  decoded : Array (String × Encoding.FileText) := #[]

private abbrev ReadM := StateT InputLog IO

/-- A file's bytes through the decoding door, once per run: the losses are
named the first time, and a repeat read is the first reading. -/
private def decodeOnce (path : String) (fresh : Unit → Encoding.FileText) :
    ReadM (Encoding.FileText × Bool) := do
  if let some (_, read) := (← get).decoded.find? (·.1 == path) then return (read, false)
  let read := fresh ()
  modify fun log => { log with
    diags := log.diags ++ read.diags
    decoded := log.decoded.push (path, read) }
  return (read, true)

/-- A tex file the document reads, through the decoding door: under the
declaration the run fixed, else the one in force, else the document's own
preamble's, else the one the file makes for itself — pdfLaTeX applies a
declaration to every file of the document, the file that makes it
included. -/
private def readTexOnce (path : String) (bytes : ByteArray) : ReadM Encoding.FileText := do
  let log ← get
  let under := match log.fixed with
    | some d => d
    | none => log.ledger.declared <|> log.guess <|> Encoding.declaredIn path bytes
  let (read, fresh) ← decodeOnce path fun _ => Encoding.readTex under path bytes
  if fresh then
    modify fun log => { log with ledger := log.ledger.record (read.read path under) }
  return read

/-- Every included surface uses the document reader's decoding door and IO
error contract, and its one door (`Surface.fragment`): the file's reading is
a fragment of the same AST, wrapped as the file it came from; its bytes are
never converted to TeX source and parsed again. The wrapper carries the
file's name and nothing else: an include standing as a whole block sequence
— a document body, a frame's content — with only blank source around the
call elaborates as the file alone does (`Elab.elabBlocks_input_exact`, and
at a frame's content by a lemma private to `InputContract`; for a markdown
file whose desugaring is not empty, `Elab.markdownInput_blocks_exact`).
Beside other content the included blocks are the same and the inner
frame-source offsets shift, which no statement here claims. Filename normalization
precedes the surface's extension policy: LaTeX's file-name sanitizer removes
paired quotes and trims both ends when the name contains a dot, only the
start otherwise (expl3-code.tex; quotedInputFilenameChecks). -/
private def readFragment (dir : System.FilePath) (file name : String) (pos : Pos)
    (prefer : String → String) (command : String)
    (decode : String → ByteArray → ReadM Encoding.FileText) (surface : Ir.Surface) :
    ReadM (Array Parse.Raw × Array Diag) := do
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
      let read ← decode path.toString bytes
      return Surface.fragment surface path.toString read.text pos
  else
    -- The span names `file`, the file the `\input` sits in — the reader
    -- goes to that line to fix it, and a directory has no line 5.
    let d := DriverDiag.inputMissing preferred (some ⟨file, pos⟩) command
    return (#[], #[d])

/-- An `\input` read through the door. TeX's input scanner tries the default
`.tex` suffix before the literal spelling, unless that spelling already ends
in `.tex` (inputFileChecks). -/
private def readInputAt (dir : System.FilePath) (file name : String) (pos : Pos) :
    ReadM (Array Parse.Raw × Array Diag) :=
  readFragment dir file name pos (fun name =>
    if name.endsWith ".tex" then name else name ++ ".tex") "input" readTexOnce .tex

public def readInput (dir : System.FilePath) (file name : String) (pos : Pos) :
    IO (Array Parse.Raw × Array Diag) := do
  let ((raws, ds), log) ← (readInputAt dir file name pos).run {}
  return (raws, log.diags ++ ds)

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
            "markdownInput" (fun path bytes => do
              return (← decodeOnce path fun _ => Encoding.readMarkdown path bytes).1) .markdown
          let ds := if request.options.isEmpty then ds else ds.push <|
            Diag.of .W0110 s!"'\\markdownInput' options '{request.options}' are not applied; \
the file uses the Markdown document dialect" (some ⟨request.file, request.pos⟩)
              (subject := some "markdownInput:options")
          pure (sub, ds)
        else readInputAt dir request.file request.name request.pos
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
      if name == "inputenc" && !(← get).inputenc then
        modify fun log => { log with
          inputenc := true
          ledger := { log.ledger with
            declared := Encoding.ofCall request.command request.file request.pos
              request.options } }
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
          let text ← match ← readSource path.toString with
            | .ok bytes => pure (← readTexOnce (name ++ ".sty") bytes).text
            | .error d =>
              modify fun log => { log with
                diags := log.diags.push { d with span := some ⟨request.file, request.pos⟩ } }
              pure ""
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

/-- Execute macros and fulfil input requests in source order, from what the
run already knows of its files. -/
private def executeWith (file : String) (raws : Array Parse.Raw) (log : InputLog)
    (dir : System.FilePath := (System.FilePath.mk file).parent.getD ".") :
    IO (Compat.Executed × InputLog) :=
  (Elab.executeInputs (readAt dir file 8) file raws).run log

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
  let (executed, log) ← executeWith file raws {} dir
  return (executed, log.diags, log.spliced)

/-- The bibliography request an elaborated document states (`Ir.bibRefs`),
fulfilled: each named `.bib` resolves beside the document, like `\input`,
and its text goes to the pure core (`Bib.apply`) — parsing, ordering,
formatting, and the citation rewrite all happen there, on every document
(`Bib.apply_no_cite`: no `.cite` node reaches a backend). A missing file is
E0503 naming the path; the marker stays empty and the citations' `?`
marks say so on the page. Each `.bib` is read under the declaration the
ledger holds, and joins its reads. -/
public def resolveBibliography (file : String) (doc : Ir.Doc)
    (bibSpans : Array (String × Span) := #[]) (ledger : Encoding.Ledger := {}) :
    IO (Ir.Doc × Array Diag × Encoding.Ledger) := do
  let requested := Ir.bibRefs doc
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  let mut ledger := ledger
  for src in requested do
    let name := Bib.sourceName src
    let path := if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
      else dir / name
    let span := (bibSpans.find? (·.1 == src)).map (·.2)
    if ← path.pathExists then
      match ← readSource path.toString with
      | .ok bytes =>
        let read := Encoding.readTex ledger.declared path.toString bytes
        sources := sources.push (src, read.text)
        diags := diags ++ read.diags
        ledger := ledger.record (read.read path.toString ledger.declared)
      | .error d => diags := diags.push { d with span := span }
    else
      diags := diags.push (DriverDiag.bibMissing src path.toString span)
  let (doc, applyDiags) := Bib.apply sources doc
  return (doc, diags ++ applyDiags, ledger)

/-- The data request a parsed document states (`Data.fileRefsAt`), fulfilled
before elaboration — the expansion needs the records where
`\begin{foreach}` stands, so this is the `resolveBibliography` shape moved
ahead of `Elab.runRaws`. Each named `.bib` resolves beside the document,
like `\input`, and is read under the declaration the ledger holds; a
missing file is E0365 naming the path, and the reads that wanted its
records say what stayed unresolved. -/
private def resolveDataIn (file : String) (raws : Array Parse.Raw) (ledger : Encoding.Ledger) :
    IO (Array Parse.Raw × Array Diag × Encoding.Ledger) := do
  unless Data.hasData raws do return (raws, #[], ledger)
  let requested := Data.fileRefsAt file raws
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  let mut ledger := ledger
  for (src, span) in requested do
    let name := Data.sourceName src
    let path := if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
      else dir / name
    if ← path.pathExists then
      match ← readSource path.toString with
      | .ok bytes =>
        let read := Encoding.readTex ledger.declared path.toString bytes
        sources := sources.push (src, read.text)
        diags := diags ++ read.diags
        ledger := ledger.record (read.read path.toString ledger.declared)
      | .error d => diags := diags.push { d with span := some span }
    else
      diags := diags.push (DriverDiag.dataMissing src path.toString (some span))
  let (raws, expandDiags) := Data.expandData file sources raws
  return (raws, diags ++ expandDiags, ledger)

/-- `resolveDataIn` for a document that declares no input encoding. -/
public def resolveData (file : String) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array Diag) := do
  let (raws, diags, _) ← resolveDataIn file raws {}
  return (raws, diags)

/-- A document's sources as the driver reads them: its own text as the door
read it, executed, with its data resolved, the diagnostics of every read,
the local styles spliced, and the ledger of the input encoding. -/
public structure Source where
  text : String
  executed : Compat.Executed
  diags : Array Diag
  spliced : Array (String × Option String × Pos)
  ledger : Encoding.Ledger

/-- **The front door**: a document's bytes to its executed source, as the
driver reads every document and as every harness that claims to read one
like the driver must. The bytes become text through the decoding door
(`Encoding.readDocument`) under the declaration the preamble makes; the surface
its extension selects is parsed and the inputs executed. The declaration
execution settles on governs every file the document read — the one that
makes it, and those read before it ran — so where a file was read under
another, the document is read again under it, once, every file with it.
`phase` hears each stage's name, detail and milliseconds. -/
public def readDocument (file : String) (bytes : ByteArray)
    (phase : String → String → Nat → IO Unit := fun _ _ _ => pure ()) : IO Source := do
  let since (t : Nat) : IO Nat := do return (← IO.monoMsNow) - t
  let markdown := Ir.Surface.ofPath file == .markdown
  let t ← IO.monoMsNow
  let (first, guess) := if markdown then (Encoding.readMarkdown file bytes, none)
    else Encoding.readDocument file bytes
  phase "decode" s!"{first.text.utf8ByteSize} bytes of text" (← since t)
  -- Which surface a path's extension selects, read through its one door.
  -- The markdown door hands back the same surface AST the tex door does —
  -- one elaborator, one place where meaning lives — so everything past
  -- this point reads raws, never the surface that wrote them; the
  -- elaborator records the same decision in the document, where only the
  -- surface's own defaults read it (`Ir.Surface.textBlock`, `Ir.Surface.listing`).
  -- The tex door's two stages report apart (`Surface.read_tex_exact`).
  let surface (text : String) (phases : Bool) : IO (Array Parse.Raw × Array Diag) := do
    let t ← IO.monoMsNow
    match Ir.Surface.ofPath file with
    | .tex =>
      let (toks, lexDiags) := Surface.texLex file text
      if phases then phase "lex" s!"{toks.size} tokens" (← since t)
      let t ← IO.monoMsNow
      let (raws, parseDiags) := Surface.texParse file toks
      if phases then phase "parse" s!"{raws.size} top-level nodes" (← since t)
      return (raws, lexDiags ++ parseDiags)
    | .markdown =>
      let (raws, ds) := Surface.read .markdown file text
      if phases then phase "md" s!"{raws.size} top-level nodes" (← since t)
      return (raws, ds)
  let (raws, frontDiags) ← surface first.text true
  let t ← IO.monoMsNow
  let seeded (read : Encoding.FileText) (under : Option Encoding.Declared) : Encoding.Ledger :=
    if markdown then {} else { reads := #[read.read file under] }
  let (executed, log) ← executeWith file raws { guess, ledger := seeded first guess }
  let settled := log.ledger.declared
  let (read, frontDiags, executed, log) ← if !log.ledger.stale then
      pure (first, frontDiags, executed, log)
    else
      let again := Encoding.readTex settled file bytes
      let (raws, frontDiags) ← if again.text == first.text then pure (raws, frontDiags)
        else surface again.text false
      let (executed, log) ← executeWith file raws
        { fixed := some settled, ledger := seeded again settled }
      let ledger := { log.ledger with declared := settled }
      pure (again, frontDiags, executed, { log with ledger })
  let (raws, dataDiags, ledger) ← resolveDataIn file executed.raws log.ledger
  phase "input" s!"{raws.size} top-level nodes" (← since t)
  return { text := read.text
           executed := executed.withRaws raws
           diags := read.diags ++ frontDiags ++ log.diags ++ dataDiags
           spliced := log.spliced, ledger }

end LeanTex.Cli.Input
