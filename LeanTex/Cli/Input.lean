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
public import LeanTex.Core.BibText
import LeanTex.Core.Data
import LeanTex.Core.KeyVal
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.LeanFactsFile
import LeanTex.Cli.LeanLinks
import LeanTex.Cli.Host

/-! The driver's file frontend: the document's own bytes and the `\input`/`\include`,
`\markdownInput`, local `.sty`, `.bib` and `\data` files it names, each read through one
decoding door and returning its diagnostics. -/

namespace LeanTex.Cli.Input

open LeanTex.Core

/-- The first line of an `IO.Error`'s rendering, since a diagnostic message is one
line. -/
private def reasonLine (s : String) : String :=
  (s.splitOn "\n").headD s

/-- The document's own bytes, or the E0001 naming why they could not be read. -/
public def readSource (file : String) : IO (Except Diag ByteArray) := do
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .ok bytes => return .ok bytes
  | .error e => return .error (DriverDiag.unreadableInput file (reasonLine (toString e)))

/-- What a run knows of the files it reads: the reads' diagnostics, the local styles
spliced, and the input encoding. -/
private structure InputLog where
  diags : Array Diag := #[]
  spliced : Array (String × Option String × Pos) := #[]
  /-- The declaration every file is read under on a second pass (`none` inside for
  UTF-8). -/
  fixed : Option (Option Encoding.Declared) := none
  /-- The declaration the document's own preamble makes, for a file read before any
  `inputenc` load runs. -/
  guess : Option Encoding.Declared := none
  /-- The first `inputenc` load executed, and each file read. -/
  ledger : Encoding.Ledger := {}
  /-- Whether `inputenc` has loaded; the first load's options apply, and a later load's
  new options are W0110. -/
  inputenc : Bool := false
  /-- Each file decoded in this run, so a file read twice is decoded once and
  its losses named once. -/
  decoded : Array (String × Encoding.FileText) := #[]
  /-- Each file read, by the path it was read at, which publication must never
  overwrite. -/
  reads : Array String := #[]
  /-- The bibliography files the document's inclusions cite into, by the names the document gives
  them, which its reference list joins. -/
  joins : Array String := #[]
  /-- Each bibliography file's keys by its path, parsed once a run. -/
  bibKeys : Array (String × Std.HashSet String) := #[]

private abbrev ReadM := StateT InputLog IO

/-- A file's bytes through the decoding door once per run; a repeat read returns the first
reading. -/
private def decodeOnce (path : String) (fresh : Unit → Encoding.FileText) :
    ReadM (Encoding.FileText × Bool) := do
  if let some (_, read) := (← get).decoded.find? (·.1 == path) then return (read, false)
  let read := fresh ()
  modify fun log => { log with
    diags := log.diags ++ read.diags
    decoded := log.decoded.push (path, read) }
  return (read, true)

/-- A tex file read through the decoding door under the declaration the run fixed, else
the one in force, else the preamble's, else its own. -/
private def readTexOnce (path : String) (bytes : ByteArray) : ReadM Encoding.FileText := do
  let log ← get
  let under := match log.fixed with
    | some d => d
    | none => log.ledger.declared <|> log.guess <|> Encoding.declaredIn path bytes
  let (read, fresh) ← decodeOnce path fun _ => Encoding.readTex under path bytes
  if fresh then
    modify fun log => { log with ledger := log.ledger.record (read.read path under) }
  return read

/-- An included surface read through the document reader's decoding door into one
`Surface.fragment` of the same AST, after LaTeX's file-name sanitizing. -/
private def readFragment (dir : System.FilePath) (file name : String) (pos : Pos)
    (prefer : String → String) (command : String)
    (decode : String → ByteArray → ReadM Encoding.FileText) (surface : Ir.Surface)
    (cites : Bool := false) (native : Bool := false) (hybrid : Bool := false) :
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
      modify fun log => { log with reads := log.reads.push path.toString }
      let read ← decode path.toString bytes
      return Surface.fragment surface path.toString read.text pos cites native hybrid
  else
    -- The span names the file the `\input` sits in, where the reader fixes it.
    let d := DriverDiag.inputMissing preferred (some ⟨file, pos⟩) command
    return (#[], #[d])

/-- An `\input` read through the door, trying the `.tex` suffix before the literal
spelling unless it already ends in `.tex`. -/
private def readInputAt (dir : System.FilePath) (file name : String) (pos : Pos) :
    ReadM (Array Parse.Raw × Array Diag) :=
  readFragment dir file name pos (fun name =>
    if name.endsWith ".tex" then name else name ++ ".tex") "input" readTexOnce .tex

public def readInput (dir : System.FilePath) (file name : String) (pos : Pos) :
    IO (Array Parse.Raw × Array Diag) := do
  let ((raws, ds), log) ← (readInputAt dir file name pos).run {}
  return (raws, log.diags ++ ds)

/-- minted's `\inputminted[options]{lang}{file}`: the file's text as the listing a `minted`
environment of that language and those options sets. -/
private def readMinted (dir : System.FilePath) (request : Compat.InputRequest) :
    ReadM (Array Parse.Raw × Array Diag) := do
  let name := request.second.trimAscii.toString
  let path := dir / name
  unless ← path.pathExists do
    return (#[], #[DriverDiag.inputMissing name (some ⟨request.file, request.pos⟩) "inputminted"])
  match ← readSource path.toString with
  | .error d => return (#[], #[{ d with span := some ⟨request.file, request.pos⟩ }])
  | .ok bytes =>
    modify fun log => { log with reads := log.reads.push path.toString }
    let text := (← decodeOnce path.toString fun _ => Encoding.readMarkdown path.toString bytes).1.text
    let head := if request.options.isEmpty then "" else "[" ++ request.options ++ "]"
    let lang := request.name.trimAscii.toString
    return (#[.verb "minted" (head ++ "{" ++ lang ++ "}\n" ++ text) request.pos], #[])

/-- The bibliography a Lean page or inclusion cites into: its files as the document names them, and
their entries' keys. -/
private def codeRefs (found : Array LeanFactsFile.BibFile) (keys : Std.HashSet String) :
    Option Code.Refs :=
  if found.isEmpty then none else some { path := ",".intercalate (found.map (·.name)).toList, keys }

/-- The bibliography files a reference list can name, and W0110 at `span` for each whose name holds
a comma, which a list's names cannot. -/
private def listable (found : Array LeanFactsFile.BibFile) (span : Span) :
    Array LeanFactsFile.BibFile × Array Diag :=
  let (bad, good) := found.partition (·.name.contains ',')
  (good, bad.map fun f => Diag.of .W0110 s!"`bibliography` names '{f.name}', whose comma a \
reference list's file names cannot hold; its entries are not read" (some span)
    (help := "rename the file or its folder without a comma") (subject := some "code:bibliography"))

/-- A bibliography file's keys, parsed once a run. -/
private def keysOnce (f : LeanFactsFile.BibFile) : ReadM (Std.HashSet String) := do
  if let some (_, ks) := (← get).bibKeys.find? (·.1 == f.path) then return ks
  let ks := (Bib.keysOf f.text).foldl (·.insert ·) {}
  modify fun log => { log with bibKeys := log.bibKeys.push (f.path, ks) }
  return ks

/-- A Lean file an inclusion names, what it asks to show, where it is asked, and whether markdown's
division asks it. -/
private structure LeanAsk where
  name : String
  showing : Code.Showing
  site : Span
  division : Bool

/-- A Lean file included with the views its inclusion asks for, its facts read where they need them
and git asked where its link names the file's commit or path. -/
private def readLean (dir : System.FilePath) (ask : LeanAsk) : ReadM (Array Parse.Raw × Array Diag) := do
  let path := dir / ask.name
  unless ← path.pathExists do
    return (#[], #[DriverDiag.inputMissing ask.name (some ask.site) "inputlean"
      (if ask.division then some "the Lean division's file" else none)])
  match ← readSource path.toString with
  | .error d => return (#[], #[{ d with span := some ask.site }])
  | .ok bytes =>
    modify fun log => { log with reads := log.reads.push path.toString }
    let text := (← decodeOnce path.toString fun _ => Encoding.readMarkdown path.toString bytes).1.text
    let showing := ask.showing
    let lost := showing.lostIncluded
    let declared := showing.facts.map fun p => (dir / p).toString
    let (facts, factDiags, factsRead) ← if showing.asks || showing.decls.isSome then
        Host.runIO (LeanFactsFile.factsFor path.toString text declared lost)
      else pure (none, #[], none)
    if let some p := factsRead then modify fun log => { log with reads := log.reads.push p }
    let place ← match showing.link with
      | some l => if showing.statements then
          Host.runIO (LeanLinks.placeOf path.toString (Code.linkTemplate l)) else pure {}
      | none => pure {}
    let entry := if ask.division then "the Lean division" else "`\\inputlean`"
    -- A documentation view cites by its bibliography's keys, declared beside the document, else the
    -- Lean file's project's, and the document's reference list joins the files it cites from.
    let (found, bibDiags) ← if showing.docs then
        Host.runIO (LeanFactsFile.bibFor path.toString showing.bibliography ask.site
          (base := some dir.toString) (entry := some entry))
      else pure (#[], #[])
    let (found, commaDiags) := listable found ask.site
    let keyed ← found.mapM fun f => return (f, ← keysOnce f)
    let keys := keyed.foldl (init := {}) fun ks (_, k) => k.fold (init := ks) fun acc x => acc.insert x
    let (raws, ds) := Code.includeLean path.toString text showing facts place ask.site entry
      (codeRefs found keys)
    let cited := Code.citedKeys raws
    let citing := keyed.filter fun (_, ks) => cited.any ks.contains
    modify fun log => { log with
      joins := citing.foldl (fun js (f, _) => if js.contains f.name then js else js.push f.name)
        log.joins
      reads := log.reads ++ found.map (·.path) }
    return (raws, ds ++ factDiags ++ bibDiags ++ commaDiags)

/-- `\inputlean[options]{file}`, its options read as TeX spells them. -/
private def inputleanAsk (request : Compat.InputRequest) : LeanAsk :=
  { name := request.name.trimAscii.toString, site := ⟨request.file, request.pos⟩, division := false
    showing := Code.showingOfEntries .lean (Decl.splitEntries request.options) (alone := true) }

/-- What a Lean division asks the reader for. -/
private def divisionAsk (d : Md.LeanDivision) (site : Span) : LeanAsk :=
  { name := d.file.trimAscii.toString, site, division := true, showing := Code.showingOfDivision d }

/-- Each Lean division markdown raws read from `file` hold, replaced by the file it includes, with
the inclusions' diagnostics in order. -/
private def includeDivisions (dir : System.FilePath) (file : String) (raws : Array Parse.Raw) :
    ReadM (Array Parse.Raw × Array Diag) := do
  if !Md.requestsDivisions raws.toList then return (raws, #[])
  (Md.includeDivisions (m := StateT (Array Diag) ReadM) (fun d site => do
    let (raws, ds) ← readLean dir (divisionAsk d site)
    modify (· ++ ds)
    return raws) file #[] raws.toList).run #[]

/-- The same in a file the walk reads as TeX: each inclusion's raws kept off the walk, at their
place, in the context. -/
private def keptDivisions (dir : System.FilePath) (file : String) (raws : Array Parse.Raw)
    (context : Compat.InputContext) :
    ReadM ((Array Parse.Raw × Array Diag) × Compat.InputContext) := do
  if !Md.requestsDivisions raws.toList then return ((raws, #[]), context)
  ((Md.includeDivisions (m := StateT (Array Diag) (StateT Compat.InputContext ReadM)) (fun d site => do
    let (raws, ds) ← readLean dir (divisionAsk d site)
    modify (· ++ ds)
    let (place, kept) := (← getThe Compat.InputContext).native raws site.pos
    set kept
    return place) file #[] raws.toList).run #[]).run context

/-- The markdown package's `citations` and `hybrid` an inclusion reads under, its own options over
those in force, and a note naming every other option it writes. -/
private def markdownSet (opts setup : Compat.MarkdownOptions) (site : Span) :
    Bool × Bool × Array Diag :=
  let note := if opts.others.isEmpty then #[] else #[Diag.of .W0110 s!"'\\markdownInput' options \
'{", ".intercalate opts.others.toList}' are not applied; the Markdown document dialect reads only \
'citations' and 'hybrid'" (some site) (subject := some "markdownInput:options")]
  (opts.citations.getD (setup.citations.getD false), opts.hybrid.getD (setup.hybrid.getD false), note)

/-- Fulfil one executed request; a compatible repeat or a cycle back edge of a local style
reads nothing, and nesting stays within eight files. -/
private def readAt (dir : System.FilePath) (root : String) (depth : Nat) :
    Compat.InputReader ReadM := fun request context => do
  let site : Span := ⟨request.file, request.pos⟩
  if Compat.inputCommands.contains request.command then
    match depth with
    | 0 =>
      let d := { DriverDiag.inputTooDeep with span := some site }
      modify fun log => { log with diags := log.diags.push d }
      return (none, context)
    | depth + 1 =>
      if request.command == "markdownInput" then
        let prefer := fun name : String =>
          if (System.FilePath.mk name).extension.isSome then name else name ++ ".tex"
        let (cites, hybrid, note) :=
          markdownSet (Compat.MarkdownOptions.read request.options) context.markdown site
        let (sub, ds) ← readFragment dir request.file request.name request.pos prefer
          "markdownInput" (fun path bytes => do
            return (← decodeOnce path fun _ => Encoding.readMarkdown path bytes).1) .markdown
          cites (native := !hybrid) (hybrid := hybrid)
        modify fun (log : InputLog) => { log with diags := log.diags ++ ds ++ note }
        if hybrid then
          let ((sub, divisionDs), context) ← keptDivisions dir request.file sub context
          modify fun (log : InputLog) => { log with diags := log.diags ++ divisionDs }
          let (answer, context) ← Elab.resumeInput (readAt dir root depth) context request.file sub
          return (some answer, context)
        let (sub, divisionDs) ← includeDivisions dir request.file sub
        modify fun (log : InputLog) => { log with diags := log.diags ++ divisionDs }
        let (answer, context) := context.native sub request.pos
        return (some answer, context)
      let (sub, diags) ← if request.command == "inputminted" then readMinted dir request
        else if request.command == "inputlean" then readLean dir (inputleanAsk request)
        else readInputAt dir request.file request.name request.pos
      modify fun log => { log with diags := log.diags ++ diags }
      if request.command == "inputlean" then
        let (answer, context) := context.native sub request.pos
        return (some answer, context)
      let (answer, context) ←
        Elab.resumeInput (readAt dir root depth) context request.file sub
      return (some answer, context)
  else
    let mut out : Array Parse.Raw := #[]
    let mut current := context
    let mut handled := false
    -- Each member executes before the next, since an earlier member may load a later sibling.
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
            | .ok bytes =>
              modify fun log => { log with reads := log.reads.push path.toString }
              pure (← readTexOnce (name ++ ".sty") bytes).text
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

/-- Execute macros and fulfil input requests in source order, from what the run already knows of
its files; markdown and a code file execute nothing. -/
private def executeWith (file : String) (raws : Array Parse.Raw) (log : InputLog)
    (dir : System.FilePath := (System.FilePath.mk file).parent.getD ".") :
    IO (Compat.Executed × InputLog) :=
  (match Ir.Surface.ofPath file with
    | .markdown => do
      let (raws, ds) ← includeDivisions dir file raws
      modify fun (l : InputLog) => { l with diags := l.diags ++ ds }
      return Compat.native file (Code.joinBibliography raws (← get).joins)
    | .code _ => return Compat.native file raws
    | .tex => Elab.executeInputs (readAt dir file 8) file raws).run log

/-- Execute macros and fulfil input requests in source order, resolving beside the
document unless `dir` says otherwise; the execution continues through
`Elab.prepareExecuted` or `Elab.runExecuted`, with no second macro pass. -/
public def expandInputs (file : String) (raws : Array Parse.Raw)
    (dir : System.FilePath := (System.FilePath.mk file).parent.getD ".") :
    IO (Compat.Executed × Array Diag × Array (String × Option String × Pos)) := do
  let (executed, log) ← executeWith file raws {} dir
  let executed := if log.joins.isEmpty then executed
    else executed.withRaws (Code.joinBibliography executed.raws log.joins)
  return (executed, log.diags, log.spliced)

/-- Where a file a document names by `name` is read: beside the document,
like `\input`, unless the name is absolute. -/
public def besideDocument (file name : String) : System.FilePath :=
  if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
  else (System.FilePath.mk file).parent.getD "." / name

/-- The files the document's bibliography request names (`Ir.bibRefs`), at
the paths `resolveBibliography` reads them from. -/
public def bibPaths (file : String) (doc : Ir.Doc) : Array System.FilePath :=
  (Ir.bibRefs doc).map fun src => besideDocument file (Bib.sourceName src)

/-- The document's bibliography request fulfilled: each named `.bib` read beside the
document and applied by `Bib.apply`; a list with no file read is E0503, a partly read one
W0424. -/
public def resolveBibliography (file : String) (doc : Ir.Doc) (cv : Bib.FieldReading)
    (labels : Ir.RefTable) (bibSpans : Array (String × Span) := #[])
    (ledger : Encoding.Ledger := {}) :
    IO (Ir.Doc × Array Diag × Encoding.Ledger) := do
  let requested := Ir.bibRefs doc
  let spanOf (src : String) : Option Span :=
    (bibSpans.find? fun (r, _) => (Ir.bibSourceNames r).contains src).map (·.2)
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  let mut missing : Array (String × String) := #[]
  let mut ledger := ledger
  for src in requested do
    let path := besideDocument file (Bib.sourceName src)
    if ← path.pathExists then
      match ← readSource path.toString with
      | .ok bytes =>
        let read := Encoding.readTex ledger.declared path.toString bytes
        sources := sources.push (src, read.text)
        diags := diags ++ read.diags
        ledger := ledger.record (read.read path.toString ledger.declared)
      | .error d => diags := diags.push { d with span := spanOf src }
    else
      missing := missing.push (src, path.toString)
  let missingDiags := missing.map fun (src, looked) =>
    if doc.surface == .markdown then
      DriverDiag.bibMissingMarkdown (!sources.isEmpty) src looked (spanOf src)
    else if sources.isEmpty then DriverDiag.bibMissing src looked (spanOf src)
    else DriverDiag.bibMissingAmong src looked (spanOf src)
  let (doc, applyDiags) := Bib.apply sources doc cv
  return (Bib.resolveListRefs labels doc, diags ++ missingDiags ++ applyDiags, ledger)

/-- The document's data requests fulfilled before elaboration: each named `.bib` read
beside the document under the ledger's declaration; a missing file is E0365. -/
private def resolveDataIn (file : String) (raws : Array Parse.Raw) (ledger : Encoding.Ledger) :
    IO (Array Parse.Raw × Array Diag × Encoding.Ledger × Array String) := do
  unless Data.hasData raws do return (raws, #[], ledger, #[])
  let requested := Data.fileRefsAt file raws
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  let mut ledger := ledger
  let mut reads : Array String := #[]
  for (src, span) in requested do
    let path := besideDocument file (Data.sourceName src)
    if ← path.pathExists then
      match ← readSource path.toString with
      | .ok bytes =>
        reads := reads.push path.toString
        let read := Encoding.readTex ledger.declared path.toString bytes
        sources := sources.push (src, read.text)
        diags := diags ++ read.diags
        ledger := ledger.record (read.read path.toString ledger.declared)
      | .error d => diags := diags.push { d with span := some span }
    else
      diags := diags.push (DriverDiag.dataMissing src path.toString (some span))
  let (raws, expandDiags) := Data.expandData file sources raws
  return (raws, diags ++ expandDiags, ledger, reads)

/-- `resolveDataIn` for a document that declares no input encoding. -/
public def resolveData (file : String) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array Diag) := do
  let (raws, diags, _, _) ← resolveDataIn file raws {}
  return (raws, diags)

/-- A document's sources as the driver reads them: its executed text and data, every
read's diagnostics, the local styles spliced, the encoding ledger, and every other file
read. -/
public structure Source where
  text : String
  executed : Compat.Executed
  diags : Array Diag
  spliced : Array (String × Option String × Pos)
  ledger : Encoding.Ledger
  reads : Array String

/-- The front door: a document's bytes to its executed source, decoded under the
declaration its preamble makes and read again under the one execution settles on; `phase`
hears each stage's name, detail and milliseconds. -/
public def readDocument (file : String) (bytes : ByteArray)
    (phase : String → String → Nat → IO Unit := fun _ _ _ => pure ()) : IO Source := do
  let since (t : Nat) : IO Nat := do return (← IO.monoMsNow) - t
  let tex := Ir.Surface.ofPath file == .tex
  let t ← IO.monoMsNow
  let (first, guess) := if tex then Encoding.readDocument file bytes
    else (Encoding.readMarkdown file bytes, none)
  phase "decode" s!"{first.text.utf8ByteSize} bytes of text" (← since t)
  let surface (text : String) (phases : Bool) : IO (Array Parse.Raw × Array Diag × Array String) := do
    let t ← IO.monoMsNow
    match Ir.Surface.ofPath file with
    | .tex =>
      let (toks, lexDiags) := Surface.texLex file text
      if phases then phase "lex" s!"{toks.size} tokens" (← since t)
      let t ← IO.monoMsNow
      let (raws, parseDiags) := Surface.texParse file toks
      if phases then phase "parse" s!"{raws.size} top-level nodes" (← since t)
      return (raws, lexDiags ++ parseDiags, #[])
    | .markdown =>
      let (raws, ds) := Surface.read .markdown file text
      if phases then phase "md" s!"{raws.size} top-level nodes" (← since t)
      return (raws, ds, #[])
    | .code lang =>
      let showing := Code.showingOf lang text.toList.toArray
      let asks := lang == .lean && showing.asks
      let (facts, factDiags, factsRead) ← if asks then
          Host.runIO (LeanFactsFile.factsFor file text (showing.facts.map fun p =>
            ((System.FilePath.mk file).parent.getD "." / p).toString) showing.lost)
        else pure (none, #[], none)
      if phases && asks then
        phase "lean" s!"{(facts.map (·.decls.size)).getD 0} declarations" (← since t)
      let place ← match showing.link with
        | some l => if lang == .lean && showing.statements then
            Host.runIO (LeanLinks.placeOf file (Code.linkTemplate l)) else pure {}
        | none => pure {}
      -- A Lean page's documentation cites into its declared bibliography, else its project's.
      let (found, bibDiags) ← if lang == .lean then
          Host.runIO (LeanFactsFile.bibFor file showing.bibliography ⟨file, {}⟩)
        else pure (#[], #[])
      let (found, commaDiags) := listable found ⟨file, {}⟩
      let refs := codeRefs found (found.foldl (init := {}) fun ks f =>
        (Bib.keysOf f.text).foldl (·.insert ·) ks)
      let bibRead := found.map (·.path)
      let t ← IO.monoMsNow
      let (raws, ds) := Surface.readCode lang file text facts place refs
      if phases then phase "code" s!"{raws.size} top-level nodes" (← since t)
      return (raws, ds ++ factDiags ++ bibDiags ++ commaDiags, factsRead.toArray ++ bibRead)
  let (raws, frontDiags, surfaceReads) ← surface first.text true
  let t ← IO.monoMsNow
  let seeded (read : Encoding.FileText) (under : Option Encoding.Declared) : Encoding.Ledger :=
    if tex then { reads := #[read.read file under] } else {}
  let (executed, log) ← executeWith file raws { guess, ledger := seeded first guess }
  let settled := log.ledger.declared
  let firstReads := log.reads
  let (read, frontDiags, executed, log) ← if !log.ledger.stale then
      pure (first, frontDiags, executed, log)
    else
      let again := Encoding.readTex settled file bytes
      let (raws, frontDiags) ← if again.text == first.text then pure (raws, frontDiags)
        else (fun (r, d, _) => (r, d)) <$> surface again.text false
      let (executed, log) ← executeWith file raws
        { fixed := some settled, ledger := seeded again settled }
      let ledger := { log.ledger with declared := settled }
      pure (again, frontDiags, executed, { log with ledger })
  let (raws, dataDiags, ledger, dataReads) ← resolveDataIn file executed.raws log.ledger
  let raws := Code.joinBibliography raws log.joins
  phase "input" s!"{raws.size} top-level nodes" (← since t)
  return { text := read.text
           executed := executed.withRaws raws
           diags := read.diags ++ frontDiags ++ log.diags ++ dataDiags
           spliced := log.spliced, ledger,
           reads := (surfaceReads ++ firstReads ++ log.reads ++ dataReads).toList.eraseDups.toArray }

end LeanTex.Cli.Input
