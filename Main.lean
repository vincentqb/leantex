import LeanTex.Version
import LeanTex.Core.Diag
import LeanTex.Core.Utf8
import LeanTex.Core.Flate
import LeanTex.Core.PdfCensus
import LeanTex.Core.PdfContract
import LeanTex.Core.Image
import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.MdDesugar
import LeanTex.Core.Ir
import LeanTex.Core.Struct
import LeanTex.Core.Theme
import LeanTex.Core.Compat
import LeanTex.Core.Elab
import LeanTex.Core.Font
import LeanTex.Core.FontDb
import LeanTex.Core.Hyphen
import LeanTex.Core.HtmlDoc
import LeanTex.Core.MarkdownDoc
import LeanTex.Core.Layout
import LeanTex.Core.Check
import LeanTex.Core.Pdf
import LeanTex.Core.Ink
import LeanTex.Cli.Args
import LeanTex.Cli.Render
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.Input
import LeanTex.Cli.FontEnv
import LeanTex.Cli.FontFix
import LeanTex.Cli.SlotLoss
import LeanTex.Cli.Boundary
import LeanTex.Cli.PicCache
import LeanTex.Cli.ToolProbe
import LeanTex.Cli.ImageAssets
import LeanTex.Cli.BrowserFaces
import LeanTex.Cli.ListingHighlight
import LeanTex.Cli.PublicationPaths
import LeanTex.Cli.Publication

open LeanTex.Core LeanTex.Cli LeanTex.Cli.Publication

structure Ui where
  cfg : Config
  color : Bool
  errStream : IO.FS.Stream
  outStream : IO.FS.Stream
  showOutput : Bool := false

def Ui.mk' (cfg : Config) : IO Ui := do
  let errStream ← IO.getStderr
  let color ← match cfg.color with
    | .always => pure true
    | .never => pure false
    | .auto => do
      let noColor := (← IO.getEnv "NO_COLOR").isSome
      let tty ← errStream.isTty
      pure (!noColor && tty)
  return ⟨cfg, color, errStream, ← IO.getStdout, false⟩

/-- The sole terminal sink for document diagnostics: keep Diag values from
DriverDiag and other producers structured through resolution, and render only
when writing the chosen stream. The pre-commit rule rejects print bypasses. -/
def Ui.diag (ui : Ui) (d : Diag) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDiag d)
  else if d.severity != .note || ui.cfg.verbosity ≥ 1 then
    ui.errStream.putStrLn (Render.human ui.color d (showOutput := ui.showOutput))

/-- Resolve and print one phase against the document's acceptance
(`\allow` and `--best-effort`). Return its accounting without retaining
already-emitted messages. -/
def Ui.resolve (ui : Ui) (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) (outputs : Array Diag.Output := #[.pdf, .html]) : IO Resolution := do
  let r := Diag.resolveAll allowed allowAll (Diag.forOutputs outputs ds)
  for d in r.diags do
    ui.diag d
  return { r with diags := #[] }

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

/-- The --werror run verdict follows the written output. Keep its stream
choice and quiet policy alongside the other UI writers. -/
def Ui.werror (ui : Ui) (file : String) (warnings ms : Nat) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainWerror file warnings ms)
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanWerror ui.color file warnings ms)

/-- Every slot and variant mapped to one face: the shape of a single-font set. -/
def singleFaceIndex : Array ((Nat × Nat × Bool) × Nat) :=
  ((List.range 3).flatMap fun slot =>
    [((slot, 400, false), 0), ((slot, 700, false), 0),
     ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray

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

/-- Deflate through the content-hash cache: the compressed stream the PDF
embeds for these bytes, computed once per content and engine version. A
font file's deflate costs ~300 ms/MB and its bytes never change between
builds, so every build after the first reads a file instead. The cached
value is `Flate.deflate`'s own output byte for byte — a hit equals a
recomputation — and a file that does not open with the zlib header the
compressor writes is a miss, never a corrupt embed. -/
def deflateCached (bytes : ByteArray) : IO ByteArray := do
  let some root ← FontDb.cacheDir | return Flate.deflate bytes
  let path := root / "flate" / s!"{Flate.contentKey bytes}-{LeanTex.version}.z"
  if let .ok z ← IO.FS.readBinFile path |>.toBaseIO then
    if z[0]? == some 0x78 && z[1]? == some 0x9C then
      return z
  let z := Flate.deflate bytes
  try
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path z
  catch _ => pure ()
  return z

/-- The per-face deflated programs `Pdf.write` embeds (`Pdf.facePrograms`,
in `Pdf.keepFaces` order), through the cache — for the faces it will embed
and no other: hashing a face the file never carries is the whole cost of a
one-page build. -/
def fontZdata (fs : Font.FontSet) (keep : Array Nat) (programs : Array (ByteArray × Bool)) :
    IO (Array (Option ByteArray)) := do
  let mut zdata : Array (Option ByteArray) := Array.replicate fs.fonts.size none
  for (k, prog, _) in keep.zip programs do
    if k < fs.fonts.size then
      zdata := zdata.set! k (some (← deflateCached prog))
  return zdata

/-- The scan is the host's answer and the parses are the filesystem's, so
both are taken once and handed to every assembly that needs them. Two
assemblies do need them: the provisional font environment a picture's
labels are measured against, resolved from the preamble, and the final one
the document settles. -/
structure FaceScan where
  faces : Array FontDb.Face
  docDirs : List String
  dirs : Array String
  diags : Array Diag

/-- Which directories to look in, and what is there. The document's own
`\fonts{ dir = ... }` outranks the host; both are preamble facts, so this
answer serves the provisional assembly and the final one alike — and the
driver re-scans only where the two disagree about the directories. -/
def scanFaces (ui : Ui) (file : String) (spec : Ir.FontSpec)
    (announce : Bool := true) : IO FaceScan := do
  let (docDirs, dirDiags) ← FontEnv.resolveDocDirs file spec.dirs
  let t ← IO.monoMsNow
  let faces ← FontDb.scanRoots
    (docDirs ++ (← FontDb.systemRoots (ui.cfg.fontDirs.toList ++ (← texFontDirs))))
  if announce then ui.phase "fontdb" s!"{faces.size} faces" ((← IO.monoMsNow) - t)
  return { faces := faces, docDirs := docDirs, dirs := spec.dirs, diags := dirDiags }

/-- Which assembly a font set is: the one the document settles on, or the
provisional one a picture's labels are measured against before the body has
been read. A value rather than a flag — it says what the caller is doing,
and the assembly reads its own consequences off it. -/
inductive Purpose where
  /-- The environment the artifact is a function of. -/
  | settled
  /-- The face resolved from the preamble alone, with a math slot where the
  source's pictures set a formula. -/
  | provisional (math : Bool)
  deriving Repr, BEq, Inhabited

/-- Every face a document can reach: the three family slots crossed with the
four bold/italic variants, loaded once and deduplicated by path. Faces the
document never uses are still loaded but not embedded — `Pdf.keepFaces` decides
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
single face with no scan behind it, so it gets no fallback.

Whether a math face loads is the document's own answer — whether a formula
stands anywhere — except for the provisional assembly, which has no body to
ask and takes the answer from what its pictures set (`Elab.picWants`): a
node label setting `$x$` is the commonest reason a preamble-resolved face
would measure differently from the final one, and a math face is also the
most expensive parse a document makes, so it is resolved early exactly when
a picture would use it.

Neither `ui` nor `file` is an argument any more: the host's answer and the
document's own directories were the only reasons to hold them, and both are
now the scan's (`scanFaces`). Assembly is a function of the document, the
faces in hand, the parses already made, and which assembly this is. -/
def buildFontSet (doc : Ir.Doc) (scan : FaceScan)
    (cache : FontEnv.Cache) (purpose : Purpose) :
    IO (Except Diag (Font.FontSet × Ir.Doc × Array Diag × String)) := do
  let spec := doc.fonts
  let bare := spec.body.isNone && spec.sans.isNone && spec.mono.isNone
    && spec.math.isNone
  if bare then
    if let some path ← IO.getEnv "LEANTEX_FONT" then
      match ← FontEnv.loadOverride path with
      | .error d => return .error d
      | .ok (f, path) =>
        -- The override is one real face: read its own alphabet coverage so a
        -- math override face is not falsely told it lacks every alphabet, and
        -- carry the resolver's N0018 diagnostics out instead of dropping them.
        let coverage := f.mathAlphabetCoverage spec.mathSources
        let (doc, alphaDiags) := Ir.resolveMathAlphas coverage f.family doc
        let set : Font.FontSet := {
          fonts := #[f]
          index := singleFaceIndex
          mathAlphabets := coverage }
        return .ok (set, doc, alphaDiags, path)
  let mut diags : Array Diag := scan.diags
  let docDirs := scan.docDirs
  let faces := scan.faces
  let spec ← if bare then
      match FontDb.defaultFamily faces with
      | some fam => pure { spec with body := some fam }
      | none => return .error noFontDiag
    else pure spec
  let mut fonts : Array Font.Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Nat × Bool) × Nat) := #[]
  let mut missing : Array String := #[]
  -- A provisional assembly resolves the *text* slot and nothing else: a
  -- node label sets in the document's text face, and the sans and mono
  -- slots cost a search of the whole scan per key for a face no label is
  -- going to ask for. A label that does ask — `\texttt` inside a node —
  -- measures against font 0 here, the settled face disagrees, and the
  -- driver elaborates again; the cost of being wrong is bounded and the
  -- cost of being thorough was not.
  let slots : List (Nat × Option String) :=
    match purpose with
    | .provisional _ => [(0, spec.body)]
    | .settled => [(0, spec.body), (1, spec.sans), (2, spec.mono)]
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
      match ← cache.resolveWeight faces family (declaredFace slot weight italic)
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
          match ← cache.parse face.path with
          | .error e =>
            diags := diags.push (DriverDiag.fontFileUnusable face.path e)
          | .ok f =>
            index := index.push ((slot, weight, italic), fonts.size)
            fonts := fonts.push f
            paths := paths.push face.path
  -- The math face: resolved like any named family, and installed only when
  -- it carries an OpenType MATH table (`FontEnv.resolveMath`, which is
  -- handed this scan rather than performing one).
  let wantsMath : Bool := match purpose with
    | .provisional math => math
    | .settled => !(Layout.docMathScalars doc).isEmpty
  let math ← FontEnv.resolveMath faces spec.math spec.body
    wantsMath fonts paths missing (some cache)
  fonts := math.fonts
  paths := math.paths
  missing := math.missing
  diags := diags ++ math.diags
  let mathIdx := math.index
  if fonts.isEmpty then
    -- Every named family failed and `diags` carries the errors; the caller
    -- stops on them, but nothing downstream may ever see an empty set.
    match FontDb.defaultFamily faces |>.bind (FontDb.resolve faces · {}) with
    | none => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
    | some (face, _) =>
      match ← cache.parse face.path with
      | .error _ => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
      | .ok f =>
        -- The single fallback face answers its own coverage, and its N0018
        -- diagnostics join the errors already collected rather than being
        -- dropped.
        let coverage := f.mathAlphabetCoverage spec.mathSources
        let (doc, alphaDiags) := Ir.resolveMathAlphas coverage f.family doc
        let set : Font.FontSet := {
          fonts := #[f]
          index := singleFaceIndex
          mathAlphabets := coverage }
        return .ok (set, doc, diags ++ alphaDiags, face.path)
  -- The math face answers its alphabet ranges once. Resolve the shared IR
  -- before `docScalars`, so a wholly unavailable alphabet never becomes a
  -- request the host fallback scan can answer by accident.
  let (doc, mathAlphabets, alphaDiags) :=
    match mathIdx.bind (fonts[·]?) with
    | some f =>
      let coverage := f.mathAlphabetCoverage spec.mathSources
      let (resolved, ds) := Ir.resolveMathAlphas coverage f.family doc
      (resolved, coverage, ds)
    | none =>
      -- No math face resolved: the coverage carries no range, so the resolver
      -- names every used alphabet as lost (N0018). Keep those diagnostics —
      -- they are appended once below, so the normal path is not doubled.
      let coverage : Math.MathAlphabetCoverage := { sources := spec.mathSources }
      let (resolved, ds) := Ir.resolveMathAlphas coverage "math face" doc
      (resolved, coverage, ds)
  diags := diags ++ alphaDiags
  -- Per-glyph fallback: map every scalar the resolved document uses to the first
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
        match ← cache.parse path with
        | .error _ => pure ()  -- undecodable candidate; the scalar stays dropped
        | .ok f =>
          fallback := fallback.push (c, fonts.size)
          fonts := fonts.push f
          paths := paths.push path
  let set : Font.FontSet := {
    fonts := fonts
    index := index
    fallback := fallback
    math := mathIdx
    mathAlphabets := mathAlphabets }
  return .ok (set, doc, diags, String.intercalate ", " paths.toList)

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
PDF's captured bytes, and where the boundary cache holds it. Both artifacts
read the captured bytes. -/
structure PicResult where
  src : String
  bytes : ByteArray
  cached : System.FilePath

/-- Run one process with a wall-clock budget: poll-and-sleep, kill on
overrun. The boundary tool is external and a runaway TeX must not hang the
build. The ending is returned as a value (`PicCache.Ran`), because whether
the tool reached a decision is what decides whether its answer is worth
remembering. -/
def runBounded (cmd : String) (args : Array String) (cwd : System.FilePath)
    (budgetMs : Nat) : IO PicCache.Ran := do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := args
    cwd := cwd
    stdout := .null
    stderr := .null
    stdin := .null }
  for _ in [0:budgetMs / 50 + 1] do
    match ← child.tryWait with
    | some code => return .exited code.toNat
    | none => IO.sleep 50
  child.kill
  let _ ← child.wait
  return .overran (budgetMs / 1000)

/-- The last words of a batchmode log: the `!` error lines, else the last
line — what E0382's help shows so the failure is diagnosable without
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
drawn PDF lands in the cache beside the font cache, keyed by the request's
content hash *and the tool's version string* — an upgraded TeX re-renders,
an unchanged request never re-runs, and a warm cache needs no TeX
installed: with no tool at all, any earlier render of the same request
serves. The version string stays the key; what is memoized is the *asking*,
against a stat-only witness of the tool binary (`ToolProbe.identify`,
`PicCache.versionStep`), so a build whose pictures all replay starts no
process at all. A request nothing can fulfil is W0379, per picture; each
such
picture then ships as the placeholder box the diagnostic names — unless the
rendered subset draws it in part, when `Boundary.withdraw` withdraws the
request and the subset's drawing ships instead (N0419). A tool that
is not installed lands there and not on E0382: only a clean exit names a
version (`PicCache.probed_present_exact`), so a picture no tool ever looked
at is never reported as one the tool drew nothing for. Failures of
a tool that ran are E0382 with the tool's own last words — and are
remembered in the same slot the drawn PDF would take, so the tool is asked
about one request at most once per version (`PicCache.step_cold_exact`) and
a replay carries the words the tool gave (`PicCache.replay_says_exact`),
never a stand-in.
An attempt the tool did not finish — a budget kill, a spawn that raised, or
a nonzero exit that left no log at all — is not an answer: it is not
remembered (`PicCache.remembers_verdict_exact`,
`PicCache.unlogged_retried_exact`) and not withdrawn to the rendered
subset's drawing (`Boundary.withdrawStep_unfinished_exact`), so neither a
busy machine nor one without the tool installed can make a picture that
renders look like one that cannot, or change the artifact while the run
reads as clean. Refusals are returned keyed
by the picture's image source, for `Image.fulfil` to name (the subject is
set there, so the gate's match cannot depend on the words chosen here).
The inventory (`-v` and the porcelain phases) says per picture what came
through the boundary: tool, version, the picture's id and its request
key, size. -/
def resolvePictures (ui : Ui) (doc : Ir.Doc)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Array PicResult × Array (String × Boundary.Undrawn)) := do
  let refs := Ir.pictureRefs doc
  if refs.isEmpty then return (#[], #[])
  let spanFor (hash : String) : Option Span :=
    (imageSpans.find? (·.1 == Ir.picSrcPrefix ++ hash)).map (·.2)
  let tool := doc.pictureTool.getD "lualatex"
  let t0 ← IO.monoMsNow
  let cacheRoot ← FontDb.cacheDir
  let picDir := (cacheRoot.getD "/tmp") / "pics"
  IO.FS.createDirAll picDir
  -- The tool's identity: first line of `--version`, part of the cache key —
  -- asked once per tool binary, not once per build, and only its exit code
  -- decides whether it answered at all.
  let stamp ← ToolProbe.witness tool
  let found ← ToolProbe.identify (picDir / PicCache.versionName (Ir.picHash tool))
    stamp (ToolProbe.probeVersion tool)
  let mut results : Array PicResult := #[]
  -- Each request no drawing came back for, with how its attempt ended —
  -- an answer the withdrawal may act on, in the tool's own words where it
  -- ran, or an attempt that never finished (`Boundary.withdraw`).
  let mut undrawn : Array (String × Boundary.Undrawn) := #[]
  for (id, wrapped) in refs do
    let src := Ir.picSrcPrefix ++ id
    -- The cache key is the *request* — the body wrapped with the design it
    -- reads — so a palette or font edit a picture mentions re-renders it
    -- and one it does not mention leaves it warm
    -- (`Ir.paletteDecls_local_exact`); the id stays the author's bytes.
    let key := Ir.picHash wrapped
    match found with
    | .absent why =>
      -- No tool: the cold decision is `Boundary.coldPicture`'s — an earlier
      -- render of this request serves, and where none exists W0379 names
      -- the loss it returns.
      match ← Boundary.coldPicture picDir tool key (spanFor id) with
      | .ok cached =>
        let bytes ← IO.FS.readBinFile cached
        results := results.push { src, bytes, cached }
        ui.phase "boundary"
          s!"{tool} (?), {id.take 16} as {key.take 16}, {bytes.size} bytes (cached)"
          (← since t0)
      | .error d =>
        undrawn := undrawn.push (src, .answered d none)
        ui.phase "boundary"
          s!"{tool} unavailable ({why}), {id.take 16} as {key.take 16}, placeholder"
          (← since t0)
    | .present version =>
      -- One slot per request and tool version, holding whichever way the
      -- tool answered: the drawn PDF, or its own refusal in the tool's own
      -- words. Either is an answer, so neither is asked for twice.
      let cached := picDir / PicCache.pdfName key (Ir.picHash version)
      let slot := picDir / PicCache.failName key (Ir.picHash version)
      let drawn ← cached.pathExists
      let remembered? ← if drawn then pure (none : Option String)
        else if ← slot.pathExists then pure (some (← IO.FS.readFile slot))
        else pure (none : Option String)
      match PicCache.step drawn remembered? with
      | .serve =>
        let bytes ← IO.FS.readBinFile cached
        results := results.push { src, bytes, cached }
        ui.phase "boundary"
          s!"{tool} ({version}), {id.take 16} as {key.take 16}, {bytes.size} bytes (cached)"
          (← since t0)
      | .replay says =>
        -- The tool already answered no for exactly these bytes under
        -- exactly this version: its own words, the same code, the same
        -- dropped loss — one attempt per request, not one per build.
        if let some u := Boundary.undrawnOf tool (.refused says) (spanFor id) then
          undrawn := undrawn.push (src, u)
        ui.phase "boundary"
          s!"{tool} ({version}), {id.take 16} as {key.take 16}, drew nothing (cached)"
          (← since t0)
      | .run =>
        let work := picDir / s!"work-{key}"
        IO.FS.createDirAll work
        IO.FS.writeFile (work / "pic.tex") wrapped
        let ran ← try
          runBounded tool #["-interaction=batchmode", "-halt-on-error", "pic.tex"]
            work 120000
        catch e =>
          pure (.unstarted (toString e))
        let produced := work / "pic.pdf"
        let drew ← produced.pathExists
        let logPath := work / "pic.log"
        let log ← if ← logPath.pathExists then
            pure (PicCache.Log.says (logTail (← IO.FS.readFile logPath)))
          else pure PicCache.Log.absent
        let outcome := PicCache.outcome ran drew log
        match outcome with
        | .drawn =>
          let bytes ← IO.FS.readBinFile produced
          IO.FS.writeBinFile cached bytes
          results := results.push { src, bytes, cached }
          ui.phase "boundary"
            s!"{tool} ({version}), {id.take 16} as {key.take 16}, {bytes.size} bytes"
            (← since t0)
        | .refused words =>
          IO.FS.writeFile slot words
          ui.phase "boundary"
            s!"{tool} ({version}), {id.take 16} as {key.take 16}, drew nothing"
            (← since t0)
        | .inconclusive words =>
          -- Nothing the machine did is written: the next build retries.
          ui.phase "boundary"
            s!"{tool} ({version}), {id.take 16} as {key.take 16}, did not finish ({words})"
            (← since t0)
        if let some u := Boundary.undrawnOf tool outcome (spanFor id) then
          undrawn := undrawn.push (src, u)
        -- The scratch directory is per-content and spent either way.
        try IO.FS.removeDirAll work catch _ => pure ()
  return (results, undrawn)

/-- Where the image cache files a plan: beside the font and boundary
caches, keyed by the *content* (so a re-exported file under the same name
re-plans and an unchanged one never does), by the plan parameters (every
non-source input to `Image.plan`, so two plans that could differ never
share an entry — `planParams_serialize_inj`), and by the engine version
(an upgraded planner re-plans; `Image.decodeBin`'s magic already orphans a
format change). No document or output path enters the key. -/
def imageCachePath (params : Image.PlanParams) (bytes : ByteArray) :
    IO (Option System.FilePath) := do
  let some root ← FontDb.cacheDir | return none
  return some (root / "imgs" / s!"{Flate.contentKey bytes}-{params.key}-{LeanTex.version}.img")

/-- Plan through the image cache. The header is probed first; only a plan
the planner itself says does real work — an alpha PNG's inflate, split,
deflate (`Image.Plan.recodes`, `recodes_iff`) — is worth a disk read, and
everything else plans directly from the probe. The cached value is the
pure plan's own output (`Image.encodeBin`), so a hit equals a
recomputation — `decodeBin_encodeBin_id`, the transparency statement.
Returns whether this was a hit, for the phase line. -/
def decodeImageCached (params : Image.PlanParams) (bytes : ByteArray) :
    IO (Except String Image.Plan × Bool) := do
  let src ← match Image.probe bytes with
    | .error e => return (.error e, false)
    | .ok src => pure src
  unless Image.Plan.recodes params src do return (Image.plan params src, false)
  let path? ← imageCachePath params bytes
  if let some path := path? then
    if let .ok blob ← IO.FS.readBinFile path |>.toBaseIO then
      if let some pl := Image.decodeBin blob then
        return (.ok pl, true)
  let res := Image.plan params src
  if let some path := path? then
    if let .ok pl := res then
      try
        if let some parent := path.parent then IO.FS.createDirAll parent
        IO.FS.writeBinFile path (Image.encodeBin pl)
      catch _ => pure ()
  return (res, false)

/-- One image source's read — the effect half of `Image.fulfil`: a boundary
picture's source (`Ir.picSrcPrefix`) is answered from the resolved
boundary results, a path resolves against the document's own directory,
like `\input`, then through graphicx's extension resolution (a deck says
`figures/plot` and means the `figures/plot.png` beside it), and decodes in
the pure core through the content-hash cache when the decode is the
expensive kind. Returns whether the cache answered, for the phase line. -/
def fetchImage (dir : System.FilePath) (pics : Array PicResult)
    (refused : Array (String × Diag)) (params : Image.PlanParams) (req : Image.Request) :
    IO (Image.Fetch × Bool) := do
  let src := req.src
  if src.startsWith Ir.picSrcPrefix then
    match pics.find? (·.src == src) with
    | some r => return (.decoded "" (Image.probe r.bytes >>= Image.plan params) none none none none, false)
    | none =>
      match refused.find? (·.1 == src) with
      | some (_, why) => return (.refused why, false)
      | none => return (.missing "the boundary cache (no picture declares this source)", false)
  let mut hit : Option (String × System.FilePath) := none
  for cand in Image.sourceCandidates src do
    let p := if (System.FilePath.mk cand).isAbsolute then System.FilePath.mk cand
      else dir / cand
    if ← p.pathExists then
      hit := some (cand, p)
      break
  match hit with
  | none =>
    let p := if (System.FilePath.mk src).isAbsolute then System.FilePath.mk src
      else dir / src
    return (.missing p.toString, false)
  | some (cand, p) =>
    let bytes : Except String ByteArray ← try pure (.ok (← IO.FS.readBinFile p))
      catch e => pure (.error (toString e))
    match bytes with
    | .error e => return (.unreadable e, false)
    | .ok bytes =>
      let href := if cand == src then "" else cand
      if Image.isSvg cand then
        let res ← ImageAssets.svgPlan params bytes req.page
        return (.decoded href res (some bytes) none (some bytes) none, false)
      else if req.page != .first || req.animated then
        let res := Image.decodeRequest params bytes req
        -- An animation's companion SVG is read once, here, beside the PDF,
        -- so preserving movement never rereads the file (`fulfilOne_bytes`).
        let companion ← if req.animated then do
            match ← (IO.FS.readBinFile (p.withExtension "svg")).toBaseIO with
            | .ok svg => pure (some svg)
            | .error _ =>
              Except.toOption <$> (IO.FS.readBinFile (p.withExtension "SVG")).toBaseIO
          else pure none
        return (.decoded href (res.map (·.1)) none (res.toOption.bind (·.2))
          (some bytes) companion, false)
      else
        let (res, fromCache) ← decodeImageCached params bytes
        return (.decoded href res none none (some bytes) none, fromCache)

/-- The image request an elaborated document states (`Ir.imageRequests`),
fulfilled: the driver reads each source (`fetchImage`) and the pure core
decides what each read means (`Image.fulfil`) — an entry with a payload,
or a placeholder box with the diagnostic that names it (`fulfil_named`),
one entry per requested source (`fulfil_covers`) — and every fact a plan
did not carry is named after it (`Image.lossDiags`, W0603/W0604;
`plan_losses_accounts` says the ledger is complete). The plan parameters
are the defaults until a declaration projects them (the profile slices'
one line). The `Nat` returned is the cache-hit count, for the phase line.
Image diagnostics inherit the executed request span; located boundary
refusals keep their own span. -/
def loadImages (file : String) (doc : Ir.Doc) (pics : Array PicResult := #[])
    (refused : Array (String × Diag) := #[])
    (imageSpans : Array (String × Span) := #[]) :
    IO (Image.Store × Array Diag × Nat) := do
  let dir := (System.FilePath.mk file).parent.getD "."
  let params := Image.PlanParams.default
  let mut fetched : Array (Image.Request × Image.Fetch) := #[]
  let mut hits := 0
  for req in Ir.imageRequests doc do
    let (f, fromCache) ← fetchImage dir pics refused params req
    if fromCache then hits := hits + 1
    fetched := fetched.push (req, f)
  let (store, diags) := Image.fulfilRequests fetched
  let mut diags := diags
  for en in store.entries do
    if let some pl := en.info then
      diags := diags ++ Image.lossDiags en.src pl
  diags := diags.map fun d =>
    match d.subject with
    | some src => DriverDiag.atImageRequest imageSpans src d
    | none => d
  return (store, diags, hits)

/-- PDF sources receive a browser image of their selected page, converted
from the bytes `fetchImage` already read — never a reread. A declared
animation also looks for a readable, self-contained SVG beside that PDF:
its SMIL stays intact in an image context, while print and reduced motion
select the static poster. An absent or unusable companion leaves the PDF
poster as the browser face. No generated script or inline XML is needed. -/
def imageBrowserFaces (imgs : Image.Store) : IO Image.Store := do
  return { entries := ← imgs.entries.mapM BrowserFaces.prepare }

def countErrors (diags : Array Diag) : Nat :=
  diags.foldl (fun n d => if d.severity == .error then n + 1 else n) 0

/-- Convert the captured boundary PDF to captured browser SVG. Conversion
failure retains the existing named fallback; no output path is consulted. -/
def picsToSvg (pics : Array PicResult) (imgs : Image.Store)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Image.Store × Array Diag × Array String) := do
  let mut entries := imgs.entries
  let mut diags : Array Diag := #[]
  let mut unconverted : Array String := #[]
  for r in pics do
    match ← ImageAssets.picFace r.bytes with
    | .ok bytes =>
      entries := entries.map fun en =>
        if en.src == r.src then { en with webSvg := some bytes } else en
    | .error why =>
      diags := diags.push (DriverDiag.atImageRequest imageSpans r.src (DriverDiag.boundarySvgMissing why))
      unconverted := unconverted.push r.src
  return ({ entries }, diags, unconverted)

/-- **Elaborate, against whatever face the caller has.** Everything from the
elaborator on is a function of the prepared source and one measurement
(`Ir.Pic.LabelMetric`), which is why the driver can resolve a face *before*
elaborating and still re-run this if that face turns out not to be the
document's own. The measurement is a parameter, never a flag and never read
from a config: the artifact stays a function of the document and the font
environment (`artifact_flag_free`). -/
def elaborate (ui : Ui) (file : String) (prepared : Elab.Prepared)
    (earlier : Array Diag) (spliced : Array (String × Option String × Pos))
    (metric : Ir.Pic.LabelMetric) (phases : Bool := true)
    (withdrawn : Array String := #[]) :
    IO (Ir.Doc × Array Diag × Elab.ReqSpans) := do
  let t ← IO.monoMsNow
  let (doc, elabDiags, reqSpans) := Elab.runPrepared file prepared earlier metric withdrawn
  -- N0020 says a `.sty` was read and how much of it took; its counts
  -- are read off the elaborated diagnostics, so it is built after them.
  -- A record from inside an `\input` wrapper names that file, not the
  -- document: the `\RequirePackage` lives there.
  let elabDiags := elabDiags ++
    spliced.map fun (sty, src, pos) =>
      Compat.styRead (src.getD file) sty pos elabDiags
  if phases then ui.phase "elab" s!"{doc.body.size} blocks" (← since t)
  let t ← IO.monoMsNow
  let (doc, bibDiags) ← Input.resolveBibliography file doc reqSpans.bib
  unless bibDiags.isEmpty && (Ir.bibRefs doc).isEmpty || !phases do
    ui.phase "bib" s!"{(Ir.bibRefs doc).size} sources" (← since t)
  -- The unresolved-reference judge, over the document the backends read
  -- (`Ir.refDiags`): with the images fulfilled below, this is the tail
  -- `pending_named` quantifies over.
  let refDiags := Ir.refDiags reqSpans.labels (Elab.ReqSpans.spanOf reqSpans.refs) doc
  return (doc, elabDiags ++ bibDiags ++ refDiags, reqSpans)

/-- What the front end hands the driver: the document, and everything a
second elaboration would need if the face this one was measured against
turns out not to be the one the document settles on. -/
structure Front where
  doc : Ir.Doc
  diags : Array Diag
  spans : Elab.ReqSpans
  prepared : Elab.Prepared
  earlier : Array Diag
  spliced : Array (String × Option String × Pos)
  /-- Parsed faces, shared by the provisional assembly and the final one. -/
  cache : FontEnv.Cache
  /-- The host's answer, taken once — absent where no face was needed yet. -/
  scan : Option FaceScan
  /-- The measurement this document was elaborated against, where one was
  resolved from the preamble. `none` means the source could draw no picture
  the engine measures, so nothing was asked of a face. -/
  provisional : Option Ir.Pic.LabelMetric

/-- Read and decode the file, then run the front end, reporting phases.

**The font environment is resolved before elaboration where it can be.** A
node's extent is a font question that the picture walk must answer while it
places, so the measurement has to exist before the body is elaborated — and
the environment that answers it is a function of the elaborated body, which
is the circle. It is cut, not straightened: the *preamble* settles which
families, sizes and page a face resolves from (`Elab.preambleDoc`), so a
provisional environment exists before any body runs, and the driver checks
afterwards whether the document's own environment would have measured any
label differently (`Cli.FontFix.agree`). Where it would not — the common
case, and the only case for a document whose picture labels set in the text
face — one elaboration is the whole answer, and what licenses stopping there
is `Cli.FontFix.extent_agree`: metrics that agree on a label's ink give that
node the same extent, so the placement the walk computed is the placement
this face determines. Where they differ, `build` elaborates again against the
settled face, so the artifact is never the provisional one's. That the
environment itself cannot depend on the metric — the whole-document fixed
point — is owed, not proved; the gate that keeps it sound meanwhile is the
check, not the claim. -/
def frontend (ui : Ui) (file : String) : IO (Option Front) := do
  let t0 ← IO.monoMsNow
  let bytes ← match ← Input.readSource file with
    | .error d =>
      ui.diag d
      pure none
    | .ok bytes => pure (some bytes)
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
    -- Which reader a path's extension selects. The markdown reader hands
    -- back the same surface AST the tex reader does — one elaborator, one
    -- place where meaning lives — so everything past this point is blind
    -- to which surface the document was written in.
    let (raws, frontDiags) ← do
      if file.endsWith ".md" then
        let (raws, ds) := Md.read file input
        ui.phase "md" s!"{raws.size} top-level nodes" (← since t)
        pure (raws, ds)
      else
        let (toks, lexDiags) := Lex.lex file input
        ui.phase "lex" s!"{toks.size} tokens" (← since t)
        let t ← IO.monoMsNow
        let (raws, parseDiags) := Parse.parse file toks
        ui.phase "parse" s!"{raws.size} top-level nodes" (← since t)
        pure (raws, lexDiags ++ parseDiags)
    let (executed, inputDiags, spliced) ← Input.expandInputs file raws
    let (raws, dataDiags) ← Input.resolveData file executed.raws
    let earlier := frontDiags ++ inputDiags ++ dataDiags
    -- One rewrite, one boundary scan, one macro scan: two elaborations of
    -- one document must read one source, or their agreement would be about
    -- two (`Elab.prepareExecuted`).
    let prepared := Elab.prepareExecuted file { executed with raws := raws }
    let cache ← FontEnv.Cache.mk'
    -- Nothing is asked of a face until something might measure against it,
    -- and a math slot only where a picture body sets a formula
    -- (`Elab.picWants`): resolving one eagerly costs a MATH-table parse,
    -- which is the most expensive face a document can load.
    let wants := Elab.picWants prepared.raws
    let (scan, provisional) ← if !wants.draws then
        pure (none, none)
      else do
        let pre := Elab.preambleDoc file prepared
        let scan ← scanFaces ui file pre.fonts
        let t ← IO.monoMsNow
        match ← buildFontSet pre scan cache (.provisional wants.math) with
        | .error _ =>
          -- A provisional face that will not resolve is not an error here:
          -- the final assembly reports it, at the document's own spec.
          pure (some scan, none)
        | .ok (fsPre, _, _, _) =>
          let m := Layout.labelMetric (Layout.Geom.ofPage pre.page) fsPre
          ui.phase "provisional" s!"{fsPre.fonts.size} faces" (← since t)
          pure (some scan, some m)
    let (doc, diags, reqSpans) ←
      elaborate ui file prepared earlier spliced (provisional.getD (fun _ _ => {}))
    -- Discover through the elaborated document: package options, markdown,
    -- macros and includes have already settled the language and source. The
    -- provider returns data only; every later elaboration reuses this exact
    -- snapshot, including font remeasurement and picture withdrawal.
    let requests := LeanTex.Core.ListingReply.requests doc
    let (doc, diags, reqSpans, prepared, earlier) ← if requests.isEmpty then
        pure (doc, diags, reqSpans, prepared, earlier)
      else do
        let t ← IO.monoMsNow
        let (replies, listingDiags) ← LeanTex.Cli.ListingHighlight.fulfil file requests
        ui.phase "highlight" s!"{replies.size} of {requests.size} listings" (← since t)
        let prepared := { prepared with listingReplies := replies }
        let earlier := earlier ++ listingDiags
        let (doc, diags, reqSpans) ← elaborate ui file prepared earlier spliced
          (provisional.getD (fun _ _ => {})) (phases := false)
        pure (doc, diags, reqSpans, prepared, earlier)
    return some { doc := doc, diags := diags, spans := reqSpans
                  prepared := prepared, earlier := earlier, spliced := spliced
                  cache := cache, scan := scan, provisional := provisional }

/-- The reporting scope is the output plan's projection. Markdown has no
backend-specific diagnostic scope; common source diagnostics still apply. -/
def diagnosticOutputs (emit : Array Emit) : Array Diag.Output :=
  emit.filterMap fun e => match e with
    | .pdf => some .pdf
    | .html => some .html
    | .md => none

def build (ui : Ui) (file : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  match ← frontend ui file with
  | none =>
    ui.summary file 1 (← since t0)
    return 1
  | some front =>
    let allowAll := ui.cfg.bestEffort
    let emit := ui.cfg.effectiveEmit front.doc.output.formats
    let outputs := diagnosticOutputs emit
    let ui := { ui with showOutput := emit.toList.eraseDups.length > 1 }
    -- **The boundary answers before the document's diagnostics are read.**
    -- A request no tool drew, for a picture the rendered subset draws in
    -- part, is withdrawn (`Boundary.withdraw`) and the document elaborated
    -- again with it, so what is resolved below is the page that ships: the
    -- subset's drawing with its refusals named, never a placeholder the
    -- subset could have filled. A document already failing asks nothing of
    -- the tool — its build stops at the first resolution either way.
    let failing := (Diag.resolveAll front.doc.allow allowAll (Diag.forOutputs outputs front.diags)).errors > 0
    let (pics, undrawn) ← if failing then pure (#[], #[])
      else resolvePictures ui front.doc front.spans.images
    let w := Boundary.withdraw (front.doc.pictureTool.getD "lualatex")
      front.spans.fallbacks undrawn front.spans.images
    let front ← if w.ids.isEmpty then pure front else do
      let t ← IO.monoMsNow
      let (doc, diags, spans) ← elaborate ui file front.prepared front.earlier front.spliced
        (front.provisional.getD (fun _ _ => {})) (phases := false) (withdrawn := w.ids)
      ui.phase "withdraw" s!"{w.ids.size} pictures drawn by the rendered subset" (← since t)
      pure { front with doc := doc, diags := diags ++ w.notes, spans := spans }
    let refused := w.standing
    let doc := front.doc
    let diags := front.diags
    let reqSpans := front.spans
    let mut resolved ← ui.resolve doc.allow allowAll (outputs := outputs) diags
    if resolved.errors > 0 then
      ui.accepted resolved.accepted
      ui.summary file resolved.errors (← since t0)
      return 1
    let t ← IO.monoMsNow
    -- The host's answer is taken once. The directories to look in are the
    -- document's `\fonts{ dir = ... }`, a preamble fact — so a scan taken
    -- for the provisional face serves the settled one, and only a document
    -- that names a directory in its *body* pays for a second scan.
    let reuse : Option FaceScan := front.scan.filter (·.dirs == doc.fonts.dirs)
    let scan ← match reuse with
      | some s => pure s
      | none => scanFaces ui file doc.fonts
    match ← buildFontSet doc scan front.cache .settled with
    | .error d =>
      -- No usable font set exists at all: nothing downstream can run, so
      -- this stays fatal whatever the document accepts.
      ui.diag d
      ui.summary file 1 (← since t0)
      return 1
    | .ok (fs, doc, fontDiags, paths) =>
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) fontDiags)
      if resolved.errors > 0 then
        ui.accepted resolved.accepted
        ui.summary file resolved.errors (← since t0)
        return 1
      let names := ", ".intercalate (fs.fonts.toList.map (·.psName))
      ui.phase "font" s!"{names} ({paths})" (← since t)
      -- **Is the document already the fixed point?** It was elaborated
      -- against a face resolved from its preamble; the face it settles on
      -- is `fs`. Where the two measure every label the pictures carry
      -- alike (`Cli.FontFix.agree`, over `probes`), the extents the
      -- placement used are the extents this face gives — `extent_agree` is
      -- the step — so the document in hand *is* the one this environment
      -- determines and no second elaboration can change it. Where they
      -- differ, or where no provisional face was resolved at all and the
      -- body drew a picture anyway, elaborate again against the settled
      -- face: the artifact is a function of the document and the font
      -- environment, never of whichever face happened to be resolved first.
      let metric := Layout.labelMetric (Layout.Geom.ofPage doc.page) fs
      let t ← IO.monoMsNow
      let ps := FontFix.probes doc.body
      let settled : Bool := match front.provisional with
        | some pre => FontFix.agree pre metric ps
        | none => Elab.enginePictures doc.body == 0
      if let some pre := front.provisional then
        ui.phase "settle" (if settled then s!"provisional face holds ({ps.size} labels)"
          else s!"provisional face superseded \
({FontFix.disagreements pre metric ps} of {ps.size} labels)") (← since t)
      let doc ← if settled then pure doc else do
        let t ← IO.monoMsNow
        let (doc2, _, _) ←
          elaborate ui file front.prepared front.earlier front.spliced metric
            (phases := false) (withdrawn := w.ids)
        ui.phase "remeasure" s!"{Elab.enginePictures doc.body} pictures" (← since t)
        let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
        pure (Ir.resolveMathAlphas fs.mathAlphabets family doc2).1
      let t ← IO.monoMsNow
      let (imgs, imgDiags, imgHits) ← loadImages file doc pics refused reqSpans.images
      -- The alt judge's picture face, after fulfilment: a picture the
      -- tool failed on ships a placeholder box, not an image, and E0382
      -- has named that loss — one loss, named once.
      let picAlts := Ir.picAltDiags doc
        (fun src => (reqSpans.images.find? (·.1 == src)).map (·.2))
        (fun src => imgs.entries.any fun en => en.src == src && en.info.isSome)
      let imgDiags := (imgDiags ++ picAlts).map front.prepared.sourceTriggers.attribute
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) imgDiags)
      unless imgs.entries.isEmpty do
        let cached := if imgHits == 0 then "" else s!", {imgHits} cached"
        ui.phase "images" s!"{imgs.entries.size} files{cached}" (← since t)
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
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) out.diags)
      ui.phase "layout" s!"{out.pages.size} pages" (← since t)
      -- An unaccepted error anywhere before the writers means no output: a
      -- failing document must not produce one (the assertion contract, held
      -- for every dropped loss).
      if resolved.errors > 0 then
        ui.accepted resolved.accepted
        ui.summary file resolved.errors (← since t0)
        return 1
      -- Phase 1, the plan: what to build and where it would land, as pure
      -- computation over the flags and the document — the one read is
      -- whether `-o` names an existing directory. No directory is created
      -- here, and none is until `publish`.
      let css := cssFor doc.output.css
      let outIsDir ← match ui.cfg.output with
        | some o => (System.FilePath.mk o).isDir
        | none => pure false
      let outDir := ui.cfg.output.bind fun o =>
        if o.endsWith "/" && !outIsDir then some o else none
      let htmlPath := outPath ui.cfg.output outIsDir file .html
      let mdPath := mdOutPath ui.cfg.output outIsDir file doc.output.md
      let pdfPath := outPath ui.cfg.output outIsDir file .pdf
      let destinations := (if emit.contains .html then #[ ("HTML", htmlPath) ] else #[]) ++
        (if emit.contains .md then #[ ("Markdown", mdPath) ] else #[]) ++
        (if emit.contains .pdf then #[ ("PDF", pdfPath) ] else #[])
      -- premise: publicationPathChecks — distinct formats publish, while
      -- colliding names and filesystem aliases leave all outputs untouched.
      if let some detail ← PublicationPaths.conflict destinations then
        ui.diag (DriverDiag.outputPathsConflict detail)
        ui.summary file 1 (← since t0)
        return 1
      -- Phase 2, the build, in memory: every artifact's bytes exist before
      -- any is judged, so the assertion gate reads the file that would
      -- ship (the PDF census) and a failing document leaves nothing
      -- behind — the HTML page included, which once beat the gate to
      -- disk. Between here and `Check.all` nothing names an output
      -- location: no write, no directory under `-o`, no such path handed
      -- to a tool; the boundary conversion targets the picture cache.
      -- The artifact ships the faces the document resolved, as the PDF
      -- embeds them — unless the document declared its `css =` story
      -- (the site port's `css = own`): then its stylesheet owns fonts
      -- and nothing ships. `Doc.fontPolicy` is that rule as a value, and
      -- a declared `fonts =` overrides it (`Pdf.fontPolicy_projects`).
      let shipFonts := doc.fontPolicy == .embedded
      -- **A slot that fell to the body face is named here**, and not in the
      -- assembly: the loss is about a face a reader receives, so the
      -- decision has to see what this run emits. The PDF embeds the
      -- resolved set; an HTML page does so only under `fontPolicy =
      -- embedded`. A page declaring `css = own` ships no face and styles
      -- code from its own monospace stack, and a report there names a file
      -- nobody receives (`Cli.SlotLoss.carries`). The set here is the
      -- settled one — `build` holds no other — so no assembly gate is
      -- needed on top.
      -- premise: slotLossChecks — one document, one index, two values of
      -- the gate's own condition: carrying a face reports the lost slot,
      -- carrying none reports nothing. The gate is load-bearing rather
      -- than decorative.
      let slotDiags := SlotLoss.diags doc.fonts fs doc
        (SlotLoss.carries emit doc.fontPolicy)
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) slotDiags)
      -- The declared contract, held against each emitted artifact's
      -- realization record: a fact the artifact cannot yet realize is one
      -- W0701 per artifact, per fact — warnings, resolved before the gate
      -- and never gating (`Ir.contract_accounts`).
      let mut contractWarnings : Array Diag := #[]
      if emit.contains .pdf then
        contractWarnings := contractWarnings ++
          Ir.contractDiags (doc.output.contract.unmet Pdf.profile)
      if emit.contains .html then
        contractWarnings := contractWarnings ++
          Ir.contractDiags (doc.output.contract.unmet HtmlDoc.profile)
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) contractWarnings)
      let mut htmlBuilt : Option HtmlDoc.ClosedPage := none
      if emit.contains .html then
        let t ← IO.monoMsNow
        let cssMode := match css with
          | .own => HtmlDoc.CssMode.own
          | .bulma => HtmlDoc.CssMode.bulma
          | .none => HtmlDoc.CssMode.none
        -- The boundary pictures' HTML face: captured PDFs convert to
        -- captured SVG bytes (`picsToSvg`; W0378 names a converter
        -- this host lacks). A picture the conversion failed on, and that
        -- the rendered subset draws in part, is drawn by the subset on
        -- this face alone (`Boundary.htmlWithdraw`): the document is
        -- elaborated again for the page with it withdrawn, and the PDF
        -- keeps the boundary's drawing.
        let (imgs, svgDiags, unconverted) ← picsToSvg pics imgs reqSpans.images
        let imgs ← imageBrowserFaces imgs
        resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
          (svgDiags.map front.prepared.sourceTriggers.attribute))
        let htmlOnly := Boundary.htmlWithdraw reqSpans.fallbacks unconverted
        let htmlDoc ← if htmlOnly.isEmpty then pure doc else do
          let t ← IO.monoMsNow
          let (d, _, _) ← elaborate ui file front.prepared front.earlier front.spliced metric
            (phases := false) (withdrawn := w.ids ++ htmlOnly)
          ui.phase "withdraw" s!"{htmlOnly.size} pictures drawn by the rendered subset \
in the HTML" (← since t)
          let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
          pure (Ir.resolveMathAlphas fs.mathAlphabets family d).1
        let hcfg : HtmlDoc.Config := {
          css := cssMode
          mathBoundary := ui.cfg.mathBoundary
          imgs := imgs
          fonts := if shipFonts then some fs else none
          -- The markdown twin, when one is being written beside the page,
          -- is linked from the head as the alternate representation.
          mdHref := if emit.contains .md then (System.FilePath.mk mdPath).fileName
            else none
          -- A picture's `viewBox` is the box the PDF reserves: the same
          -- label measurement layout places with, over the one face set.
          labelMetric := Layout.labelMetric (Layout.Geom.ofPage doc.page) fs
          cancelMetric := Layout.cancelMetric (Layout.Geom.ofPage doc.page) fs
          mathEm := Layout.mathEm (Layout.Geom.ofPage doc.page) fs
        }
        let (result, hdiags) ← prepareHtml file hcfg htmlDoc
        resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) hdiags)
        match result with
        | .error detail =>
          ui.diag (DriverDiag.htmlResourceUnavailable detail)
          ui.accepted resolved.accepted
          ui.summary file 1 (← since t0)
          return 1
        | .ok page =>
          ui.phase "html" s!"{page.render.utf8ByteSize} bytes" (← since t)
          htmlBuilt := some page
      let mut mdBuilt : Option String := none
      if emit.contains .md then
        let t ← IO.monoMsNow
        let md := MarkdownDoc.emit doc
        ui.phase "markdown" s!"{md.utf8ByteSize} bytes" (← since t)
        mdBuilt := some md
      let mut pdfBuilt : Option ByteArray := none
      if emit.contains .pdf then
        let t ← IO.monoMsNow
        -- Font programs and content streams deflate through the
        -- content-hash cache: a subset, or a page unchanged since the last
        -- build, reads its stream back instead of compressing it. The glyph
        -- census is taken once for the kept faces, their programs and the
        -- page operators; the writer takes its own.
        let used := Pdf.usedAll fs out.pages
        let keep := Pdf.keepOf used
        let programs := Pdf.facePrograms fs used
        let fs := { fs with zdata := ← fontZdata fs keep programs }
        -- The structure tree the pages' `leaf` indices name: the one the
        -- layout attributed against (`Layout.pdfView`), projected once.
        let tree := Struct.ofDoc (Layout.pdfView doc)
        let ops := Pdf.pageOps geom fs out.pages imgs tree keep
        let mut streams : Array (ByteArray × Option ByteArray) := #[]
        for o in ops do
          let data := (Pdf.render o).toUTF8
          streams := streams.push (data, some (← deflateCached data))
        let pdf := Pdf.write geom fs out.pages doc.info imgs out.outline streams tree ops programs
        ui.phase "pdf" s!"{pdf.size} bytes" (← since t)
        pdfBuilt := some pdf
      -- Phase 3: census, gate, publish. Assertions judge what shipped, so
      -- they read the built bytes and run before anything is written: a
      -- failing document must not produce output. The page walk is
      -- skipped when nothing asserts: measuring ink on every build would
      -- tax the common path for the rare check — and so is the PDF
      -- census, which runs only when an assertion reads it.
      let t ← IO.monoMsNow
      -- Every artifact the plan emits must carry its fonts: the PDF by the
      -- census of its bytes (a copied page can bring a face the writer
      -- never embedded), the HTML by the faces it embeds in the page;
      -- the markdown twin carries none and contributes nothing.
      let readsPdf := doc.asserts.any fun a => match a.kind with
        | .fontsAllEmbedded | .pdfProfile _ => true
        | .pages _ _ | .textInArea | .minXHeight _ | .accessibilityAA => false
      let pdfCensus : Option (Except String PdfCensus.Census) :=
        if readsPdf then pdfBuilt.map PdfCensus.census else none
      let fontsEmbedded : Bool :=
        if doc.asserts.any (·.kind == .fontsAllEmbedded) then
          (pdfCensus.all fun c => match c with
            | .ok c => c.fontsEmbedded
            | .error _ => false) &&
          htmlBuilt.all fun _ => shipFonts
        else true
      -- The declared profile set, held against the census of the PDF just
      -- built: the meet's rules the file breaks, rendered. A run that
      -- emits no PDF leaves the list empty and fails loud below instead.
      let pdfViolations : Array String :=
        match pdfCensus with
        | none => #[]
        | some (.error e) => #[s!"the PDF census refused the file: {e}"]
        | some (.ok c) =>
          if doc.output.profiles.isEmpty then #[]
          else match PdfContract.Contract.ofProfiles doc.output.profiles with
            | .ok k => (PdfContract.violations k c doc.info.title).map (·.render)
            | .error v => #[v.render]
      let shipped := if doc.asserts.isEmpty then
          { pages := out.pages.size, fontsEmbedded := true : Check.Shipped }
        else Check.Shipped.ofOut geom fs out (fontsEmbedded := fontsEmbedded)
      let shipped := { shipped with pdfViolations }
      -- The AA rows read the document and its judged diagnostics — the
      -- picture face speaks after fulfilment, so the driver reads the
      -- pre-\allow stream through that batch: accepting a warning quiets
      -- the report, never the fact.
      let shipped := if doc.asserts.any (·.kind == .accessibilityAA) then
          { shipped with a11y := Check.a11ySummary doc (diags ++ imgDiags) }
        else shipped
      let failures := Check.all shipped doc.asserts
      -- An assertion whose subject is bytes is judged on the bytes this run
      -- emits (`AssertKind.reads`); a run emitting none of them cannot
      -- judge it, and says so instead of passing vacuously — the
      -- `formats = md` document that asserts embedded fonts fails here.
      -- Layout assertions read no artifact and never reach this.
      let failures := failures ++ doc.asserts.filterMap fun a =>
        if a.kind.reads.isEmpty || emit.any (fun e => a.kind.reads.contains e.ext) then none
        else some (Diag.of .E0330
          s!"assertion failed: {a.kind.source} (actual: no emitted artifact carries this measurement)"
          a.span (help := some (a.help.getD "add pdf or html to '\\output{ formats = ... }'")))
      unless doc.asserts.isEmpty do
        ui.phase "assert"
          s!"{doc.asserts.size - failures.size}/{doc.asserts.size} held" (← since t)
      if !failures.isEmpty then
        for d in failures do
          ui.diag d
        ui.accepted resolved.accepted
        ui.summary file failures.size (← since t0)
        return exitFor 0 failures.size resolved.warnings ui.cfg.werror
      let written ← publish outDir (htmlBuilt.map (htmlPath, ·))
        (mdBuilt.map (mdPath, ·)) (pdfBuilt.map (pdfPath, ·))
      -- The hatch's other teeth: an `\allow` that never fired is stale
      -- acceptance and warns; what was accepted always prints.
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
        ((Diag.unfired doc.allow resolved.fired).map DriverDiag.allowUnfired))
      ui.accepted resolved.accepted
      let notes := (Diag.forOutputs outputs diags).foldl
        (fun n d => if d.severity == .note then n + 1 else n) 0
      ui.done file (String.intercalate ", " written.toList) out.pages.size (← since t0) notes
      -- `--werror`: the outputs above were written — the flag turns the
      -- exit code, never the rendering — and the verdict line says why the
      -- build failed anyway.
      if ui.cfg.werror && resolved.warnings > 0 then
        ui.werror file resolved.warnings (← since t0)
      return exitFor 0 0 resolved.warnings ui.cfg.werror

def dump (ui : Ui) (file : String) : IO UInt32 := do
  match ← frontend ui file with
  | none => return 1
  | some front =>
    IO.print (Ir.dump front.doc front.diags)
    return (if countErrors front.diags > 0 then 1 else 0)

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
