import LeanTex

open LeanTex.Core LeanTex.Cli

structure Ui where
  cfg : Config
  color : Bool
  errStream : IO.FS.Stream
  outStream : IO.FS.Stream

def Ui.mk' (cfg : Config) : IO Ui := do
  let errStream ← IO.getStderr
  let color ← match cfg.color with
    | .always => pure true
    | .never => pure false
    | .auto => do
      let noColor := (← IO.getEnv "NO_COLOR").isSome
      let tty ← errStream.isTty
      pure (!noColor && tty)
  return ⟨cfg, color, errStream, ← IO.getStdout⟩

def Ui.diag (ui : Ui) (d : Diag) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDiag d)
  else if d.severity != .note || ui.cfg.verbosity ≥ 1 then
    ui.errStream.putStrLn (Render.human ui.color d)

/-- One phase's diagnostics resolved against the document's acceptance
(`\allow` and `--best-effort`) and printed. -/
def Ui.resolve (ui : Ui) (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) : IO Resolution := do
  let r := Diag.resolveAll allowed allowAll ds
  for d in r.diags do
    ui.diag d
  return r

/-- Codes with their multiplicities, first appearance first. -/
def tally (xs : Array String) : List (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  for x in xs do
    match out.findIdx? (·.1 == x) with
    | some i => out := out.set! i (x, out[i]!.2 + 1)
    | none => out := out.push (x, 1)
  return out.toList

/-- Acceptance is visible, never ambient: whenever any loss was accepted,
the line prints — under `-q` too, because an accepted error is exactly the
thing quiet mode must not hide. -/
def Ui.accepted (ui : Ui) (accepted : Array String) : IO Unit := do
  if accepted.isEmpty then return
  let counts := tally accepted
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainAccepted counts)
  else
    ui.errStream.putStrLn (Render.humanAccepted ui.color counts)

def Ui.phase (ui : Ui) (name detail : String) (ms : Nat) : IO Unit := do
  if ui.cfg.verbosity ≥ 1 then
    if ui.cfg.porcelain then
      ui.outStream.putStrLn (Render.porcelainPhase name detail ms)
    else
      ui.errStream.putStrLn s!"{name}: {detail} ({ms} ms)"

def Ui.summary (ui : Ui) (file : String) (errors ms : Nat) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainSummary file (errors == 0) errors ms)
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanSummary ui.color file errors ms)

def Ui.done (ui : Ui) (file output : String) (pages ms : Nat) (notes : Nat := 0) :
    IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDone file output pages ms)
  else if !ui.cfg.quiet then
    let shown := if ui.cfg.verbosity ≥ 1 then 0 else notes
    ui.errStream.putStrLn (Render.humanDone ui.color file output pages ms shown)

/-- Every slot and variant mapped to one face: the shape of a single-font set. -/
def singleFaceIndex : Array ((Nat × Nat × Bool) × Nat) :=
  ((List.range 3).flatMap fun slot =>
    [((slot, 400, false), 0), ((slot, 700, false), 0),
     ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray

/-- `LEANTEX_FONT` (a path) overrides the default face for a document that
declares no `\fonts`: one face serves every slot and variant, no scan. -/
def loadOverride (path : String) : IO (Except Diag (Font.Font × String)) := do
  if ← System.FilePath.pathExists path then
    let data ← IO.FS.readBinFile path
    match Font.parse data with
    | .ok f => return .ok (f, path)
    | .error e => return .error (DriverDiag.envFontUnusable path e)
  else
    return .error (DriverDiag.envFontMissing path)

/-- TeX Live's font roots, asked of kpsewhich when it is installed, so
`--font-dir` is almost never needed. `--show-path` returns the expanded list.
Two process spawns cost ~120 ms -- measured, not the ~10 ms first assumed --
so the answer is remembered beside the font cache, keyed by the kpsewhich
binary's own mtime: a TeX Live upgrade replaces it and the roots are asked
again. -/
def texFontDirs : IO (List String) := do
  let query (ext : String) : IO (List String) := do
    try
      let out ← IO.Process.output { cmd := "kpsewhich", args := #["--show-path=" ++ ext] }
      if out.exitCode != 0 then return []
      return (out.stdout.trimAscii.toString.splitOn ":").filterMap fun p =>
        let p := if p.startsWith "!!" then (p.drop 2).toString else p
        let p := String.ofList (p.toList.reverse.dropWhile (· == '/')).reverse
        if p.startsWith "/" then some p else none
    catch _ => return []
  let cache ← FontDb.cacheDir
  let stamp ← do
    let which ← try IO.Process.output { cmd := "sh", args := #["-c", "command -v kpsewhich"] }
      catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
    if which.exitCode != 0 then return []
    let bin := which.stdout.trimAscii.toString
    match ← (System.FilePath.mk bin).metadata.toBaseIO with
    | .ok md => pure s!"{bin} {md.modified.sec}"
    | .error _ => pure bin
  let memo := cache.map (· / "texroots.txt")
  if let some m := memo then
    if let .ok text ← IO.FS.readFile m |>.toBaseIO then
      match text.splitOn "\n" with
      | first :: roots => if first == stamp then return roots.filter (!·.isEmpty)
      | _ => pure ()
  let roots := ((← query ".otf") ++ (← query ".ttf")).eraseDups
  if let some m := memo then
    try
      if let some parent := m.parent then IO.FS.createDirAll parent
      IO.FS.writeFile m (String.intercalate "\n" (stamp :: roots) ++ "\n")
    catch _ => pure ()
  return roots

/-- The scan produced nothing usable at all. -/
def noFontDiag : Diag := DriverDiag.noFont

/-- Every face a document can reach: the three family slots crossed with the
four bold/italic variants, loaded once and deduplicated by path. Faces the
document never uses are still loaded but not embedded — `usedGlyphs` decides
what reaches the file. A document with no `\fonts` is served by the same
mechanism: `FontDb.defaultFamily` picks a family from the scan and it fills
the body slot, so the default exists wherever any font does, by construction.
A `\fonts{ dir = ... }` is searched first, resolved against the document's own
directory like `\input`: a document that ships its fonts renders the same on
every host, whatever else is installed.

Per-glyph fallback is precomputed here, against the document's own scalars
(`Layout.docScalars`): a scalar some declared face covers maps to the first
covering face in declaration order, and one no declared face covers goes to
`FontDb.fallbackPicks`, whose face is loaded at the end of the set. Layout
consults the map only on a missing glyph. The `LEANTEX_FONT` override is a
single face with no scan behind it, so it gets no fallback. -/
def buildFontSet (ui : Ui) (file : String) (doc : Ir.Doc) :
    IO (Except Diag (Font.FontSet × Array Diag × String)) := do
  let spec := doc.fonts
  let bare := spec.body.isNone && spec.sans.isNone && spec.mono.isNone
    && spec.math.isNone
  if bare then
    if let some path ← IO.getEnv "LEANTEX_FONT" then
      match ← loadOverride path with
      | .error d => return .error d
      | .ok (f, path) =>
        return .ok ({ fonts := #[f], index := singleFaceIndex }, #[], path)
  let mut diags : Array Diag := #[]
  let mut docDirs : List String := []
  for d in spec.dirs do
    let d := if d.endsWith "/" && d.length > 1 then (d.dropEnd 1).toString else d
    let p := System.FilePath.mk d
    let p := if p.isAbsolute then p else ((System.FilePath.mk file).parent.getD ".") / p
    if ← p.isDir then
      docDirs := docDirs ++ [p.toString]
    else
      diags := diags.push (DriverDiag.fontsDirMissing d p.toString)
  let t ← IO.monoMsNow
  let faces ← FontDb.scanRoots
    (docDirs ++ (← FontDb.systemRoots (ui.cfg.fontDirs.toList ++ (← texFontDirs))))
  ui.phase "fontdb" s!"{faces.size} faces" ((← IO.monoMsNow) - t)
  let spec ← if bare then
      match FontDb.defaultFamily faces with
      | some fam => pure { spec with body := some fam }
      | none => return .error noFontDiag
    else pure spec
  let mut fonts : Array Font.Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Nat × Bool) × Nat) := #[]
  let mut missing : Array String := #[]
  let slots : List (Nat × Option String) :=
    [(0, spec.body), (1, spec.sans), (2, spec.mono)]
  -- A slot the document did not name falls back to the body family, and the
  -- body's declared per-variant faces come with it.
  -- beamer sets a presentation in its sans family: the class's default
  -- font theme is sans serif (beamer user guide §18, "the default font
  -- theme uses sans serif fonts"), so in the slides class the default
  -- text slot is the declared sans family, and its declared per-variant
  -- faces come with it. The engine's three slots carry no separate serif
  -- default for decks: \rmfamily follows the deck's face.
  let slides := doc.docClass == Ir.DocClass.slides
  let resolveName (slot : Nat) : Option String :=
    match slot with
    -- A document that names a sans family and no body family reads its
    -- text in that face. This was already the shipped behaviour — with no
    -- slot-0 entry every text lookup fell through to font 0, the sans
    -- regular — but as an accident of load order that no weight or
    -- variant could refine; naming it makes the sans's declared faces
    -- (its Medium upright, its Light) reach the text the card sets.
    | 0 => if slides then spec.sans.orElse fun _ => spec.body
      else spec.body.orElse fun _ => spec.sans
    | 1 => spec.sans.orElse fun _ => spec.body
    | _ => spec.mono.orElse fun _ => spec.body
  -- A slot's declared faces live under its *effective* slot: the one its
  -- family resolution reads (a deck's body — or a sans-only document's —
  -- follows the sans declaration).
  let effectiveOf (slot : Nat) : Nat := match slot with
    | 1 => if spec.sans.isSome then 1 else 0
    | 2 => if spec.mono.isSome then 2 else 0
    | _ => if (slides || spec.body.isNone) && spec.sans.isSome then 1 else 0
  let declaredFace (slot : Nat) (weight : Nat) (italic : Bool) : Option String :=
    spec.faceFor (effectiveOf slot) weight italic
  -- The off-corner keys this document can ask the index for: the weights
  -- its styles really use (`docWeightKeys`, exact so W0366 never fires
  -- for a weight nobody asked), plus every declared face's own key — a
  -- declaration is a request to load, as fontspec's is, so a declared
  -- Light ships in the HTML set even before a run selects it.
  let standard : List (Nat × Bool) :=
    [(400, false), (700, false), (400, true), (700, true)]
  let extraKeysFor (slot : Nat) : List (Nat × Bool) :=
    ((Layout.docWeightKeys doc).toList.filterMap fun (s, w, i) =>
      if s == slot then some (w, i) else none) ++
    (spec.faces.toList.filterMap fun ((s, w, i), _) =>
      if s == effectiveOf slot && !(standard.contains (w, i)) then some (w, i)
      else none)
  for (slot, _) in slots do
    let some family := resolveName slot | continue
    for (weight, italic) in standard ++ (extraKeysFor slot).eraseDups do
      match FontDb.resolveWeight faces family (declaredFace slot weight italic)
          weight italic with
      | none =>
        unless missing.contains family do
          missing := missing.push family
          -- A host with TeX Live installed has a thousand families; listing
          -- them all is not help. Name the ones that look like what was asked
          -- for, and how to see the rest.
          let all := FontDb.families faces
          diags := diags.push (DriverDiag.familyMissing family
            (FontDb.nearest all family).toList all.size)
      | some (face, sub) =>
        if let some s := sub then
          let d := DriverDiag.substituted s
          -- Slots share families, so the same substitution surfaces repeatedly.
          unless diags.any (·.message == d.message) do
            diags := diags.push d
        match paths.findIdx? (· == face.path) with
        | some i => index := index.push ((slot, weight, italic), i)
        | none =>
          let data ← IO.FS.readBinFile face.path
          match Font.parse data with
          | .error e =>
            diags := diags.push (DriverDiag.fontFileUnusable face.path e)
          | .ok f =>
            index := index.push ((slot, weight, italic), fonts.size)
            fonts := fonts.push f
            paths := paths.push face.path
  -- The math face: resolved like any named family, and installed only when
  -- it carries an OpenType MATH table — constants are never invented, so a
  -- face without the table earns a diagnostic naming it and math is set as
  -- source text (PLAN, M6 design decision 1).
  let mut mathIdx : Option Nat := none
  let loadFace (fonts : Array Font.Font) (paths : Array String) (path : String) :
      IO (Option Nat × Array Font.Font × Array String × Option Diag) := do
    match paths.findIdx? (· == path) with
    | some i => return (some i, fonts, paths, none)
    | none =>
      let data ← IO.FS.readBinFile path
      match Font.parse data with
      | .error e =>
        return (none, fonts, paths, some (DriverDiag.fontFileUnusable path e))
      | .ok f =>
        return (some fonts.size, fonts.push f, paths.push path, none)
  if let some family := spec.math then
    match FontDb.resolveVariant faces family none {} with
    | none =>
      unless missing.contains family do
        missing := missing.push family
        let all := FontDb.families faces
        diags := diags.push (DriverDiag.familyMissing family
          (FontDb.nearest all family).toList all.size)
    | some (face, _) =>
      let (loaded, fonts', paths', diag?) ← loadFace fonts paths face.path
      fonts := fonts'
      paths := paths'
      if let some d := diag? then
        diags := diags.push d
      if let some i := loaded then
        if (fonts[i]!).math.isSome then
          mathIdx := some i
        else
          diags := diags.push (DriverDiag.mathFaceNoTable (fonts[i]!).family face.path)
  else if !(Layout.docMathScalars doc).isEmpty then
    -- The document has formulas and no declared math face: the body
    -- family's designed companion when the host has it, else the first
    -- installed MATH-table face — either way named once, so a face the
    -- document did not choose is never silent (the `\fonts{ math = ... }`
    -- override always wins, above).
    let bodyFam := spec.body.getD ""
    let choice : Option (FontDb.Face × Option String) ←
      (← FontDb.pickMathFace faces bodyFam).mapM fun (face, row?) =>
        pure (face, row?.map fun _ => bodyFam)
    if let some (face, companionOf) := choice then
      let (loaded, fonts', paths', diag?) ← loadFace fonts paths face.path
      fonts := fonts'
      paths := paths'
      if let some d := diag? then
        diags := diags.push d
      if let some i := loaded then
        if (fonts[i]!).math.isSome then
          mathIdx := some i
          diags := diags.push (match companionOf with
            | some body => DriverDiag.mathFaceCompanion (fonts[i]!).family body
            | none => DriverDiag.mathFaceFirst (fonts[i]!).family)
  if fonts.isEmpty then
    -- Every named family failed and `diags` carries the errors; the caller
    -- stops on them, but nothing downstream may ever see an empty set.
    match FontDb.defaultFamily faces |>.bind (FontDb.resolve faces · {}) with
    | none => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
    | some (face, _) =>
      let data ← IO.FS.readBinFile face.path
      match Font.parse data with
      | .error _ => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
      | .ok f =>
        return .ok ({ fonts := #[f], index := singleFaceIndex }, diags, face.path)
  -- Per-glyph fallback: map every scalar the document uses to the first
  -- declared face covering it; scalars none covers go to the scan.
  let mut fallback : Array (Char × Nat) := #[]
  let mut uncovered : Array Char := #[]
  for c in Layout.docScalars doc do
    match (Array.range fonts.size).find? (fun i => ((fonts[i]!).gid c).isSome) with
    | some i => fallback := fallback.push (c, i)
    | none => uncovered := uncovered.push c
  unless uncovered.isEmpty do
    -- The document's own directories outrank the host: a shipped face
    -- answers first for every scalar it covers.
    let inDocDir (path : String) : Bool :=
      docDirs.any fun d => path.startsWith (d ++ "/") || path.startsWith d
    for (c, path) in ← FontDb.fallbackPicksPreferring inDocDir faces uncovered do
      match paths.findIdx? (· == path) with
      | some i => fallback := fallback.push (c, i)
      | none =>
        let data ← IO.FS.readBinFile path
        match Font.parse data with
        | .error _ => pure ()  -- undecodable candidate; the scalar stays dropped
        | .ok f =>
          fallback := fallback.push (c, fonts.size)
          fonts := fonts.push f
          paths := paths.push path
  let set : Font.FontSet := {
    fonts := fonts
    index := index
    fallback := fallback
    math := mathIdx }
  return .ok (set, diags, String.intercalate ", " paths.toList)

/-- The bibliography request an elaborated document states (`Ir.bibRefs`),
fulfilled: each named `.bib` resolves beside the document, like `\input`,
and its text goes to the pure core (`Bib.apply`) — parsing, ordering,
formatting, and the citation rewrite all happen there. A missing file is
E0503 naming the path; the marker stays empty and the citations' `?`
marks say so on the page. -/
def resolveBibliography (file : String) (doc : Ir.Doc)
    (bibSpans : Array (String × Span) := #[]) :
    IO (Ir.Doc × Array Diag) := do
  let requested := Ir.bibRefs doc
  if requested.isEmpty then return (doc, #[])
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

/-- The data request a parsed document states (`Data.fileRefs`), fulfilled
before elaboration — the expansion needs the records where
`\begin{foreach}` stands, so this is the `resolveBibliography` shape moved
ahead of `Elab.runRaws`. Each named `.bib` resolves beside the document,
like `\input`; a missing file is E0365 naming the path, and the reads that
wanted its records say what stayed unresolved. -/
def resolveData (file : String) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array Diag) := do
  unless Data.hasData raws do return (raws, #[])
  let requested := Data.fileRefs raws
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  for (src, pos) in requested do
    let name := Data.sourceName src
    let path := if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
      else dir / name
    if ← path.pathExists then
      sources := sources.push (src, ← IO.FS.readFile path)
    else
      diags := diags.push (DriverDiag.dataMissing src path.toString (some ⟨file, pos⟩))
  let (raws, expandDiags) := Data.expandData file sources raws
  return (raws, diags ++ expandDiags)

def since (t0 : Nat) : IO Nat := do
  return (← IO.monoMsNow) - t0

/-- Where the markdown twin is written: `outPath`, unless the document
declared its served name (`\output{ md = "llms.txt" }`) — the declared
name replaces the stem-derived one in the same directory, so the HTML
head's alternate link and the file on disk cannot drift apart. An explicit
`-o twin.md` file still wins: the command line outranks the document. -/
def mdOutPath (output : Option String) (outputIsDir : Bool) (source : String)
    (declared : Option String) : String :=
  let base := outPath output outputIsDir source .md
  match declared with
  | some name =>
    if (output.bind emitOfPath) == some Emit.md then base
    else ((System.FilePath.mk base).parent.getD "." / name).toString
  | none => base


/-- One fulfilled boundary picture: its image-source spelling, the drawn
PDF's bytes, and where the cache holds it (the HTML branch converts from
that file). -/
structure PicResult where
  src : String
  bytes : ByteArray
  cached : System.FilePath

/-- Run one process with a wall-clock budget: poll-and-sleep, kill on
overrun. The boundary tool is external and a runaway TeX must not hang the
build. -/
def runBounded (cmd : String) (args : Array String) (cwd : System.FilePath)
    (budgetMs : Nat) : IO (Except String Unit) := do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := args
    cwd := cwd
    stdout := .null
    stderr := .null
    stdin := .null }
  let mut waited := 0
  for _ in [0:budgetMs / 50 + 1] do
    match ← child.tryWait with
    | some 0 => return .ok ()
    | some code => return .error s!"exit code {code}"
    | none =>
      IO.sleep 50
      waited := waited + 50
  child.kill
  let _ ← child.wait
  return .error s!"no result within {budgetMs / 1000} s; killed"

/-- The last words of a batchmode log: the `!` error lines, else the last
line — what W0378's help shows so the failure is diagnosable without
opening the temp directory. -/
def logTail (log : String) : String :=
  let lines := (log.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)
  let bangs := lines.filter (·.startsWith "!")
  let picked := if bangs.isEmpty then lines.reverse.take 1 else bangs.take 3
  String.intercalate " · " (picked.map (·.trimAscii.toString))

/-- The boundary requests an elaborated document states (`Ir.pictureRefs`),
fulfilled: each wrapped standalone runs under the pinned tool — or the
default, the boundary being open by default (`boundary_request_env_free`:
only fulfilment reads the environment) — in a scratch directory, and the
drawn PDF lands in the cache beside the font cache, keyed by the content
hash *and the tool's version string* — an upgraded TeX re-renders, an
unchanged picture never re-runs, and a warm cache needs no TeX installed:
with no tool at all, any earlier render of the same content serves. A
request nothing can fulfil is W0379, once; each such picture then ships as
the placeholder box the diagnostic names. Failures of a tool that ran are
W0378 with the tool's own last words. The inventory (`-v` and the
porcelain phases) says per picture what came through the boundary: tool,
version, hash, size. -/
def resolvePictures (ui : Ui) (doc : Ir.Doc)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Array PicResult × Array Diag) := do
  let refs := Ir.pictureRefs doc
  if refs.isEmpty then return (#[], #[])
  let spanFor (hash : String) : Option Span :=
    (imageSpans.find? (·.1 == Ir.picSrcPrefix ++ hash)).map (·.2)
  let tool := doc.pictureTool.getD "lualatex"
  let t0 ← IO.monoMsNow
  -- The tool's identity: first line of `--version`, part of the cache key.
  let version? ← try
    let out ← IO.Process.output { cmd := tool, args := #["--version"] }
    pure (some (((out.stdout.splitOn "\n").headD "").trimAscii.toString))
  catch _ =>
    pure (none : Option String)
  let cacheRoot ← FontDb.cacheDir
  let picDir := (cacheRoot.getD "/tmp") / "pics"
  IO.FS.createDirAll picDir
  let mut results : Array PicResult := #[]
  let mut diags : Array Diag := #[]
  let mut saidUnavailable := false
  for (hash, wrapped) in refs do
    let src := Ir.picSrcPrefix ++ hash
    -- The cache: exact hash+version with a tool present; with none, any
    -- earlier render of this content serves — the content hash is the
    -- request's meaning, and the version in the key only forces a
    -- re-render on upgrade.
    let cached? ← do
      match version? with
      | some version =>
        let c := picDir / (hash ++ "-" ++ Ir.picHash version ++ ".pdf")
        if ← c.pathExists then pure (some c) else pure (none : Option System.FilePath)
      | none =>
        let entries ← picDir.readDir
        pure <| entries.findSome? fun e =>
          if e.fileName.startsWith (hash ++ "-") && e.fileName.endsWith ".pdf" then
            some e.path
          else none
    if let some cached := cached? then
      let bytes ← IO.FS.readBinFile cached
      results := results.push { src, bytes, cached }
      ui.phase "boundary"
        s!"{tool} ({version?.getD "?"}), {hash.take 16}, {bytes.size} bytes (cached)"
        (← since t0)
      continue
    match version? with
    | none =>
      unless saidUnavailable do
        diags := diags.push (DriverDiag.boundaryToolUnavailable tool)
        saidUnavailable := true
    | some version =>
      let cached := picDir / (hash ++ "-" ++ Ir.picHash version ++ ".pdf")
      let work := picDir / s!"work-{hash}"
      IO.FS.createDirAll work
      IO.FS.writeFile (work / "pic.tex") wrapped
      let r ← try
        runBounded tool #["-interaction=batchmode", "-halt-on-error", "pic.tex"]
          work 120000
      catch e =>
        pure (.error (toString e))
      let produced := work / "pic.pdf"
      match r with
      | .ok _ =>
        if ← produced.pathExists then
          let bytes ← IO.FS.readBinFile produced
          IO.FS.writeBinFile cached bytes
          results := results.push { src, bytes, cached }
          ui.phase "boundary"
            s!"{tool} ({version}), {hash.take 16}, {bytes.size} bytes" (← since t0)
        else
          diags := diags.push (DriverDiag.boundaryFailed tool "no PDF was produced"
            (spanFor hash))
      | .error err =>
        let log ← try IO.FS.readFile (work / "pic.log") catch _ => pure ""
        let tail := logTail log
        diags := diags.push (DriverDiag.boundaryFailed tool
          (if tail.isEmpty then err else tail) (spanFor hash))
      -- The scratch directory is per-content and spent either way.
      try IO.FS.removeDirAll work catch _ => pure ()
  return (results, diags)

/-- The image request an elaborated document states (`Ir.imageRefs`),
fulfilled: each path resolves against the document's own directory, like
`\input`, and decodes in the pure core. A boundary picture's source
(`Ir.picSrcPrefix`) is fulfilled from the resolved boundary results
instead of the filesystem. A file that is missing or refuses
to decode keeps its entry with no payload — layout places a placeholder box
of the requested size, so the document still compiles and the diagnostic
here says why the figure is a box. -/
def loadImages (file : String) (doc : Ir.Doc) (pics : Array PicResult := #[]) :
    IO (Image.Store × Array Diag) := do
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut entries : Array Image.Loaded := #[]
  let mut diags : Array Diag := #[]
  for src in Ir.imageRefs doc do
    if src.startsWith Ir.picSrcPrefix then
      -- A boundary picture: the driver has already run (or refused) the
      -- tool, and W0378 has spoken for any failure — an empty entry here
      -- is the placeholder box that diagnostic named.
      match pics.find? (·.src == src) with
      | some r =>
        match Image.decode r.bytes with
        | .ok info => entries := entries.push { src, info := some info }
        | .error e =>
          entries := entries.push { src }
          diags := diags.push (DriverDiag.imageUndecodable src (toString e))
      | none => entries := entries.push { src }
      continue
    -- The name as written, then graphicx's extension resolution: a deck
    -- says `figures/plot` and means the `figures/plot.png` beside it.
    let mut hit : Option (String × System.FilePath) := none
    for cand in Image.sourceCandidates src do
      let p := if (System.FilePath.mk cand).isAbsolute then System.FilePath.mk cand
        else dir / cand
      if ← p.pathExists then
        hit := some (cand, p)
        break
    let bytes? ← do
      match hit with
      | some (_, p) =>
        try pure (some (← IO.FS.readBinFile p))
        catch e =>
          diags := diags.push (DriverDiag.imageUnreadable src (toString e))
          pure none
      | none =>
        let p := if (System.FilePath.mk src).isAbsolute then System.FilePath.mk src
          else dir / src
        diags := diags.push (DriverDiag.imageMissing src p.toString)
        pure none
    let href := match hit with
      | some (cand, _) => if cand == src then "" else cand
      | none => ""
    match bytes? with
    | none => entries := entries.push { src, href }
    | some bytes =>
      match Image.decode bytes with
      | .ok info => entries := entries.push { src, href, info := some info }
      | .error e =>
        entries := entries.push { src, href }
        diags := diags.push (DriverDiag.imageUndecodable src (toString e))
  return ({ entries := entries }, diags)

def countErrors (diags : Array Diag) : Nat :=
  diags.foldl (fun n d => if d.severity == .error then n + 1 else n) 0

/-- The HTML face of the boundary: each drawn picture converts once, at the
boundary too, by pinned `pdftocairo -svg` into an asset beside the page
(the font-shipping shape), and the store's `href` points the `<img>` at
it. `pdftocairo` missing or failing is W0378 for this artifact only — the
PDF is unaffected — and the page then shows the picture's text
alternative. -/
def picsToSvg (ui : Ui) (htmlPath : String) (pics : Array PicResult)
    (imgs : Image.Store) : IO (Image.Store × Array Diag) := do
  if pics.isEmpty then return (imgs, #[])
  let t0 ← IO.monoMsNow
  let assetsDir := ((System.FilePath.mk htmlPath).fileStem.getD "out") ++ ".assets"
  let dir := ((System.FilePath.mk htmlPath).parent.getD ".") / assetsDir
  IO.FS.createDirAll dir
  let mut entries := imgs.entries
  let mut diags : Array Diag := #[]
  let mut converted := 0
  for r in pics do
    let hash := (r.src.drop Ir.picSrcPrefix.length).toString
    let svgName := hash ++ ".svg"
    let svgPath := dir / svgName
    let ok ← do
      if ← svgPath.pathExists then pure true
      else
        try
          let out ← IO.Process.output { cmd := "pdftocairo"
                                        args := #["-svg", r.cached.toString,
                                          svgPath.toString] }
          if out.exitCode == 0 then pure true
          else do
            diags := diags.push (DriverDiag.boundarySvgMissing
              s!"exit code {out.exitCode}")
            pure false
        catch e =>
          diags := diags.push (DriverDiag.boundarySvgMissing (toString e))
          pure false
    if ok then
      converted := converted + 1
      entries := entries.map fun en =>
        if en.src == r.src then { en with href := assetsDir ++ "/" ++ svgName }
        else en
  if converted > 0 then
    ui.phase "boundary-svg" s!"{converted} pictures ({assetsDir})" (← since t0)
  return ({ entries }, diags)

/-- Read and decode the file, then run the front end, reporting phases.
Returns the document, all diagnostics, and whether reading itself failed. -/
def frontend (ui : Ui) (file : String) : IO (Option (Ir.Doc × Array Diag × Elab.ReqSpans)) := do
  let t0 ← IO.monoMsNow
  let bytes ← try
    pure (some (← IO.FS.readBinFile file))
  catch e =>
    ui.diag (DriverDiag.unreadableInput file (toString e))
    pure none
  let some bytes := bytes | return none
  ui.phase "read" s!"{bytes.size} bytes" (← since t0)
  let t ← IO.monoMsNow
  match LeanTex.Core.Utf8.validate bytes with
  | some err =>
    ui.diag (err.toDiag file)
    return none
  | none =>
    ui.phase "utf8" "valid" (← since t)
    let input := String.fromUTF8! bytes
    let t ← IO.monoMsNow
    let (toks, lexDiags) := Lex.lex file input
    ui.phase "lex" s!"{toks.size} tokens" (← since t)
    let t ← IO.monoMsNow
    let (raws, parseDiags) := Parse.parse file toks
    ui.phase "parse" s!"{raws.size} top-level nodes" (← since t)
    let t ← IO.monoMsNow
    let (raws, inputDiags, spliced) ← Input.expandInputs file raws
    let (raws, dataDiags) ← resolveData file raws
    let (doc, elabDiags, reqSpans) := Elab.runRawsSpanned file raws
      (lexDiags ++ parseDiags ++ inputDiags ++ dataDiags)
    -- N0020 says a `.sty` was read and how much of it took; its counts
    -- are read off the elaborated diagnostics, so it is built after them.
    -- A record from inside an `\input` wrapper names that file, not the
    -- document: the `\RequirePackage` lives there.
    let elabDiags := elabDiags ++
      spliced.map fun (sty, src, pos) =>
        Compat.styRead (src.getD file) sty pos elabDiags
    ui.phase "elab" s!"{doc.body.size} blocks" (← since t)
    let t ← IO.monoMsNow
    let (doc, bibDiags) ← resolveBibliography file doc reqSpans.bib
    unless bibDiags.isEmpty && (Ir.bibRefs doc).isEmpty do
      ui.phase "bib" s!"{(Ir.bibRefs doc).size} sources" (← since t)
    return some (doc, elabDiags ++ bibDiags, reqSpans)

def build (ui : Ui) (file : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  match ← frontend ui file with
  | none =>
    ui.summary file 1 (← since t0)
    return 1
  | some (doc, diags, reqSpans) =>
    let allowAll := ui.cfg.bestEffort
    let mut fired : Array String := #[]
    let mut accepted : Array String := #[]
    let mut warnings : Nat := 0
    let r0 ← ui.resolve doc.allow allowAll diags
    fired := fired ++ r0.fired
    accepted := accepted ++ r0.accepted
    warnings := warnings + r0.warnings
    if r0.errors > 0 then
      ui.accepted accepted
      ui.summary file r0.errors (← since t0)
      return 1
    let t ← IO.monoMsNow
    match ← buildFontSet ui file doc with
    | .error d =>
      -- No usable font set exists at all: nothing downstream can run, so
      -- this stays fatal whatever the document accepts.
      ui.diag d
      ui.summary file 1 (← since t0)
      return 1
    | .ok (fs, fontDiags, paths) =>
      let r1 ← ui.resolve doc.allow allowAll fontDiags
      fired := fired ++ r1.fired
      accepted := accepted ++ r1.accepted
      warnings := warnings + r1.warnings
      if r1.errors > 0 then
        ui.accepted accepted
        ui.summary file r1.errors (← since t0)
        return 1
      let names := ", ".intercalate (fs.fonts.toList.map (·.psName))
      ui.phase "font" s!"{names} ({paths})" (← since t)
      let t ← IO.monoMsNow
      let (pics, picDiags) ← resolvePictures ui doc reqSpans.images
      let rB ← ui.resolve doc.allow allowAll picDiags
      fired := fired ++ rB.fired
      accepted := accepted ++ rB.accepted
      warnings := warnings + rB.warnings
      let (imgs, imgDiags) ← loadImages file doc pics
      -- The alt judge's picture face, after fulfilment: a picture the
      -- tool failed on ships a placeholder box, not an image, and W0378
      -- has named that loss — one loss, named once.
      let imgDiags := imgDiags ++ Ir.picAltDiags doc
        (fun src => (reqSpans.images.find? (·.1 == src)).map (·.2))
        (fun src => imgs.entries.any fun en => en.src == src && en.info.isSome)
      let r2 ← ui.resolve doc.allow allowAll imgDiags
      fired := fired ++ r2.fired
      accepted := accepted ++ r2.accepted
      warnings := warnings + r2.warnings
      unless imgs.entries.isEmpty do
        ui.phase "images" s!"{imgs.entries.size} files" (← since t)
      let t ← IO.monoMsNow
      -- The main language's patterns; a language whose table has not
      -- landed is honestly unhyphenated (W0368 already named it).
      let pats := Hyphen.forTag doc.info.locale.tag
      ui.phase "hyphen" (match pats with
        | some p => s!"{p.map.size} patterns ({doc.info.locale.tag})"
        | none => s!"no patterns for '{doc.info.locale.tag}'") (← since t)
      let t ← IO.monoMsNow
      let geom := Layout.Geom.ofPage doc.page
      let out := Layout.run geom fs pats doc imgs
      let r3 ← ui.resolve doc.allow allowAll out.diags
      fired := fired ++ r3.fired
      accepted := accepted ++ r3.accepted
      warnings := warnings + r3.warnings
      ui.phase "layout" s!"{out.pages.size} pages" (← since t)
      -- An unaccepted error anywhere before the writers means no output: a
      -- failing document must not produce one (the assertion contract, held
      -- for every dropped loss).
      if r2.errors + r3.errors > 0 then
        ui.accepted accepted
        ui.summary file (r2.errors + r3.errors) (← since t0)
        return 1
      -- Assertions judge what shipped, so they run after layout and before
      -- the file is written: a failing document must not produce output.
      -- The page walk is skipped when nothing asserts: measuring ink on
      -- every build would tax the common path for the rare check.
      let shipped := if doc.asserts.isEmpty then
          { pages := out.pages.size, fontsEmbedded := true : Check.Shipped }
        else Check.Shipped.ofOut geom fs out (fontsEmbedded := true)
      -- The AA rows read the document and its judged diagnostics — the
      -- picture face speaks after fulfilment, so the driver reads the
      -- pre-\allow stream through that batch: accepting a warning quiets
      -- the report, never the fact.
      let shipped := if doc.asserts.any (·.kind == .accessibilityAA) then
          { shipped with a11y := Check.a11ySummary doc (diags ++ picDiags ++ imgDiags) }
        else shipped
      let failures := Check.all shipped doc.asserts
      unless doc.asserts.isEmpty do
        ui.phase "assert"
          s!"{doc.asserts.size - failures.size}/{doc.asserts.size} held" (← since t)
      if !failures.isEmpty then
        for d in failures do
          ui.diag d
        ui.accepted accepted
        ui.summary file failures.size (← since t0)
        return exitFor 0 failures.size warnings ui.cfg.werror
      let mut written : Array String := #[]
      let emit := ui.cfg.effectiveEmit doc.output.formats
      let css := cssFor doc.output.css
      let outIsDir ← match ui.cfg.output with
        | some o => (System.FilePath.mk o).isDir
        | none => pure false
      if let some o := ui.cfg.output then
        if o.endsWith "/" && !outIsDir then
          IO.FS.createDirAll o
      if emit.contains .html then
        let t ← IO.monoMsNow
        let cssMode := match css with
          | .own => HtmlDoc.CssMode.own
          | .bulma => HtmlDoc.CssMode.bulma
          | .none => HtmlDoc.CssMode.none
        let htmlPath := outPath ui.cfg.output outIsDir file .html
        -- The boundary pictures' HTML face: the cached PDFs convert to
        -- SVG assets beside the page, and the store's hrefs point at
        -- them (`picsToSvg`; W0378 names a converter this host lacks).
        let (imgs, svgDiags) ← picsToSvg ui htmlPath pics imgs
        let rS ← ui.resolve doc.allow allowAll svgDiags
        fired := fired ++ rS.fired
        accepted := accepted ++ rS.accepted
        warnings := warnings + rS.warnings
        -- The artifact ships the faces the document resolved, as the PDF
        -- embeds them — unless the document declared its `css =` story
        -- (the site port's `css = own`): then its stylesheet owns fonts
        -- and nothing ships.
        let shipFonts := doc.output.css.isNone
        let fontsDir := ((System.FilePath.mk htmlPath).fileStem.getD "out") ++ ".fonts"
        let hcfg : HtmlDoc.Config := {
          css := cssMode
          mathBoundary := ui.cfg.mathBoundary
          imgs := imgs
          fonts := if shipFonts then some fs else none
          fontsDir := fontsDir
          -- The markdown twin, when one is being written beside the page,
          -- is linked from the head as the alternate representation.
          mdHref := if emit.contains .md then
              (System.FilePath.mk (mdOutPath ui.cfg.output outIsDir file
                doc.output.md)).fileName
            else none
        }
        let (html, hdiags) := HtmlDoc.emit hcfg doc
        let r4 ← ui.resolve doc.allow allowAll hdiags
        fired := fired ++ r4.fired
        accepted := accepted ++ r4.accepted
        warnings := warnings + r4.warnings
        IO.FS.writeFile htmlPath html
        written := written.push htmlPath
        ui.phase "html" s!"{html.utf8ByteSize} bytes" (← since t)
        -- The emission's font-file requests, fulfilled beside the page:
        -- the faces the styling references, byte for byte the ones the
        -- PDF embeds.
        if shipFonts then
          let t ← IO.monoMsNow
          let assets := HtmlDoc.fontAssets fs
          let dir := ((System.FilePath.mk htmlPath).parent.getD ".") / fontsDir
          IO.FS.createDirAll dir
          let mut bytes := 0
          for a in assets do
            IO.FS.writeBinFile (dir / a.file) a.data
            bytes := bytes + a.data.size
          ui.phase "fonts" s!"{assets.size} faces, {bytes} bytes ({fontsDir})" (← since t)
      if emit.contains .md then
        let t ← IO.monoMsNow
        let md := MarkdownDoc.emit doc
        let mdPath := mdOutPath ui.cfg.output outIsDir file doc.output.md
        IO.FS.writeFile mdPath md
        written := written.push mdPath
        ui.phase "markdown" s!"{md.utf8ByteSize} bytes" (← since t)
      if emit.contains .pdf then
        let t ← IO.monoMsNow
        let pdf := Pdf.write geom fs out.pages doc.info imgs out.outline
        let pdfPath := outPath ui.cfg.output outIsDir file .pdf
        IO.FS.writeBinFile pdfPath pdf
        written := written.push pdfPath
        ui.phase "pdf" s!"{pdf.size} bytes" (← since t)
      -- The hatch's other teeth: an `\allow` that never fired is stale
      -- acceptance and warns; what was accepted always prints.
      let r5 ← ui.resolve doc.allow allowAll
        ((Diag.unfired doc.allow fired).map DriverDiag.allowUnfired)
      accepted := accepted ++ r5.accepted
      warnings := warnings + r5.warnings
      ui.accepted accepted
      let notes := diags.foldl (fun n d => if d.severity == .note then n + 1 else n) 0
      ui.done file (String.intercalate ", " written.toList) out.pages.size (← since t0) notes
      -- `--werror`: the outputs above were written — the flag turns the
      -- exit code, never the rendering — and the verdict line says why the
      -- build failed anyway.
      if ui.cfg.werror && warnings > 0 then
        if ui.cfg.porcelain then
          ui.outStream.putStrLn (Render.porcelainWerror file warnings (← since t0))
        else if !ui.cfg.quiet then
          ui.errStream.putStrLn (Render.humanWerror ui.color file warnings (← since t0))
      return exitFor 0 0 warnings ui.cfg.werror

def dump (ui : Ui) (file : String) : IO UInt32 := do
  match ← frontend ui file with
  | none => return 1
  | some (doc, diags, _) =>
    IO.print (Ir.dump doc diags)
    return (if countErrors diags > 0 then 1 else 0)

/-- Insert `-` at each hyphenation point: the `hyphenate` command's output
format, and what the lualatex differential harness compares. -/
def showHyphens (pats : Hyphen.Patterns) (word : String) : String := Id.run do
  let breaks := Hyphen.hyphenate pats word
  let mut out := ""
  for (c, i) in word.toList.zipIdx do
    if i > 0 && breaks.contains i then
      out := out.push '-'
    out := out.push c
  return out

def hyphenate (ui : Ui) (words : List String) (file : Option String) : IO UInt32 := do
  let mut all := words
  if let some path := file then
    let contents ← try
      pure (some (← IO.FS.readFile path))
    catch e =>
      ui.diag (Diag.of .E0001 s!"cannot read '{path}': {e}")
      pure none
    let some contents := contents | return 1
    all := all ++ (contents.splitOn "\n").filterMap fun line =>
      let w := line.trimAscii.toString
      if w.isEmpty then none else some w
  let pats := Hyphen.english.get
  for w in all do
    IO.println (showHyphens pats w)
  return 0

/-- Rebuild whenever the source changes, by polling its mtime every 200 ms —
no inotify dependency. Each rebuild prints the usual summary line. -/
def watch (cfg : Config) (file : String) : IO UInt32 := do
  let mtime : IO (Option IO.FS.SystemTime) := do
    try
      pure (some (← (System.FilePath.mk file).metadata).modified)
    catch _ =>
      pure none
  let mut last ← mtime
  discard <| build (← Ui.mk' cfg) file
  repeat
    IO.sleep 200
    let m ← mtime
    if m != last && m.isSome then
      last := m
      discard <| build (← Ui.mk' cfg) file
  return 0

def main (argv : List String) : IO UInt32 := do
  match parse argv with
  | .error msg =>
    let stderr ← IO.getStderr
    stderr.putStrLn s!"leantex: {msg}"
    stderr.putStrLn "try 'leantex --help'"
    return 3
  | .ok cfg =>
    match cfg.cmd with
    | .help =>
      IO.println helpText
      return 0
    | .version =>
      IO.println s!"leantex {LeanTex.version}"
      return 0
    | .build file =>
      if file.endsWith ".md" then
        let stderr ← IO.getStderr
        stderr.putStrLn
          "leantex: markdown input is not implemented yet; write the document as .tex"
        return 3
      if let some o := cfg.output then
        unless o.endsWith "/" || (← (System.FilePath.mk o).isDir) ||
            (emitOfPath o).isSome do
          let stderr ← IO.getStderr
          stderr.putStrLn
            s!"leantex: cannot tell the output format of '{o}'; name it *.pdf or *.html, or pass a directory"
          return 3
      if cfg.watch then
        watch cfg file
      else
        build (← Ui.mk' cfg) file
    | .dump file =>
      dump (← Ui.mk' cfg) file
    | .hyphenate words file =>
      hyphenate (← Ui.mk' cfg) words file
    | .fonts =>
      -- The answer to "what may \\fonts name here": one family per line on
      -- stdout, so it pipes into grep. A family whose designed math
      -- companion is installed says so on an indented line, with the
      -- x-heights the optical match reads and the measured stems — stem
      -- width is measurable but no authority publishes a mismatch
      -- threshold, so it is reported here and never gates anything.
      let faces ← FontDb.scan (cfg.fontDirs.toList ++ (← texFontDirs))
      let load (path : String) : IO (Option Font.Font) := do
        try
          match Font.parse (← IO.FS.readBinFile path) with
          | .ok f => pure (some f)
          | .error _ => pure none
        catch _ => pure none
      for fam in FontDb.families faces do
        IO.println fam
        if let some (row, cFace) := FontDb.pickCompanion faces fam then
          let metrics ← do
            let bodyPath := (FontDb.resolve faces fam {}).map (·.1.path)
            match ← bodyPath.mapM load, ← load cFace.path with
            | some (some b), some c =>
              let perMille (f : Font.Font) (v : Nat) : Nat := v * 1000 / f.unitsPerEm
              let xh := s!"x-height {perMille b b.xHeightOptical} vs \
{perMille c c.xHeightOptical}"
              let stem (f : Font.Font) : Option Nat := do
                let g ← f.gid 'l'
                let src := Ink.Src.make f.data f.isCff f.numGlyphs
                let y := (f.xHeightOptical : Int) / 2
                let ivs ← src.inkAt g y y
                let (a, e) ← ivs[0]?
                pure (perMille f (e - a).toNat)
              match stem b, stem c with
              | some sb, some sc => pure s!" — {xh}, stem {sb} vs {sc} (per 1000 of each em)"
              | _, _ => pure s!" — {xh} (per 1000 of each em)"
            | _, _ => pure ""
          IO.println s!"  math companion: {cFace.family} [{row.license}] \
({row.source}){metrics}"
      return 0
    | .themes =>
      -- The answer to "what may \\theme name here": one bundle per line.
      for th in Theme.builtin do
        IO.println th.name
      return 0
