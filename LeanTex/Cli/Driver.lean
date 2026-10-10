module

import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.TexFontTrees
import LeanTex.Version
import LeanTex.Core.Diag
import LeanTex.Core.Encoding
import LeanTex.Core.Flate
import LeanTex.Core.PdfCensus
import LeanTex.Core.PdfContract
import LeanTex.Core.Image
import LeanTex.Core.Parse
import LeanTex.Core.Ir
import LeanTex.Core.Struct
import LeanTex.Core.Theme
import LeanTex.Core.Compat
import LeanTex.Core.Elab
import LeanTex.Core.BibStyle
import LeanTex.Core.PictureCensus
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
import LeanTex.Cli.FontAssembly
import LeanTex.Cli.FontFix
import LeanTex.Cli.PlanLoss
import LeanTex.Cli.Boundary
import LeanTex.Cli.Batch
import LeanTex.Cli.Compression
import LeanTex.Cli.PictureAssets
import LeanTex.Cli.PicCache
import LeanTex.Cli.ToolProbe
import LeanTex.Cli.ImageAssets
import LeanTex.Cli.BrowserFaces
import LeanTex.Cli.ListingHighlight
import LeanTex.Cli.PublicationPaths
import LeanTex.Cli.Publication

namespace LeanTex.Cli.Driver

open LeanTex.Core LeanTex.Cli LeanTex.Cli.Publication LeanTex.Cli.FontAssembly

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
already-emitted messages. Each wording of a loss repeated in the phase prints
once, its first warning carrying the wording's count and every later one a
note (`Diag.foldRepeats`); porcelain keeps every site. -/
def Ui.resolve (ui : Ui) (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) (outputs : Array Diag.Output := #[.pdf, .html]) : IO Resolution := do
  let r := Diag.resolveAll allowed allowAll (Diag.foldRepeats (Diag.forOutputs outputs ds))
  for d in r.diags do
    ui.diag d
  return { r with diags := #[] }

/-- Codes with their multiplicities, first appearance first. -/
def tally (xs : Array String) : List (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  for x in xs do
    match out.findFinIdx? (·.1 == x) with
    | some i => out := out.set i.val (x, out[i].2 + 1) i.isLt
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
      ui.errStream.putStrLn (Render.humanPhase name detail ms)

def Ui.summary (ui : Ui) (file : String) (errors ms : Nat) (written : Array String := #[]) :
    IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainSummary file (errors == 0) errors ms written)
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanSummary ui.color file errors ms written)

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

/-- The font directories of the TeX distribution on `PATH`
(`TexFontTrees.roots`), so a font TeX has rarely needs `--font-dir`; finding
them starts no process (`TexFontTrees.roots_runless_exact`). -/
def texFontDirs : IO (List String) := TexFontTrees.hostRoots

/-- Which directories to look in, and what is there. The document's own
`\fonts{ dir = ... }` outranks the host; both are preamble facts, so this
answer serves the provisional assembly and the final one alike — and the
driver re-scans only where the two disagree about the directories. -/
def scanFaces (ui : Ui) (file : String) (spec : Ir.FontSpec)
    (announce : Bool := true) : IO FaceScan := do
  let (docDirs, dirDiags) ← FontEnv.resolveDocDirs file spec.dirs
  let t ← IO.monoMsNow
  let faces ← FontDiscovery.scanRoots
    (docDirs ++ (← FontDiscovery.systemRoots (ui.cfg.fontDirs.toList ++ (← texFontDirs))))
  if announce then ui.phase "fontdb" s!"{faces.size} faces" ((← IO.monoMsNow) - t)
  return { faces := faces, docDirs := docDirs, dirs := spec.dirs, diags := dirDiags }

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


/-- One fulfilled boundary picture. Both artifacts read these captured
bytes, independently of subsequent cache writes or scratch cleanup. -/
structure PicResult where
  src : String
  bytes : ByteArray

private structure PicAttempt where
  result : Option PicResult := none
  undrawn : Option (String × Boundary.Undrawn) := none
  detail : String
  elapsed : Nat

/-- Fulfil elaborated requests through `PictureAssets`, keeping captured
results and diagnostics in source order (`Batch.plan_exact`). The scheduler
excludes repeated keys within a batch (`Batch.plan_keys_nodup`); owned
scratch and atomic cache publication also protect independent compiler runs.
Unfinished attempts remain distinct from refusals, so machine failures
cannot silently select the native subset's drawing. -/
def resolvePictures (ui : Ui) (doc : Ir.Doc)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Array PicResult × Array (String × Boundary.Undrawn)) := do
  let refs := Ir.pictureRefs doc
  if refs.isEmpty then return (#[], #[])
  let spanFor (hash : String) : Option Span :=
    (imageSpans.find? (·.1 == Ir.picSrcPrefix ++ hash)).map (·.2)
  let tool := doc.pictureTool.getD "lualatex"
  let t0 ← IO.monoMsNow
  let picDir ← PictureAssets.cacheDir
  let stamp ← ToolProbe.witness tool
  let found ← match picDir with
    | some dir =>
      ToolProbe.identify (dir / PicCache.versionName (Ir.picHash tool))
        stamp (ToolProbe.probeVersion tool)
    | none => ToolProbe.probeVersion tool
  let fulfil (request : String × String) : IO PicAttempt := do
    let (id, wrapped) := request
    let src := Ir.picSrcPrefix ++ id
    -- The cache key is the *request* — the body wrapped with the design it
    -- reads — so a palette or font edit a picture mentions re-renders it
    -- and one it does not mention leaves it warm
    -- (`Ir.paletteDecls_local_exact`); the id stays the author's bytes.
    let key := PictureAssets.key wrapped
    match found with
    | .absent why =>
      -- No tool: the cold decision is `Boundary.coldPicture`'s — an earlier
      -- render of this request serves, and where none exists W0379 names
      -- the loss it returns.
      let earlier ← match picDir with
        | some dir => Boundary.coldPicture dir tool key (spanFor id) why
        | none => pure (.error (DriverDiag.boundaryToolUnavailable tool (spanFor id) why))
      match earlier with
      | .ok bytes =>
        return {
          result := some { src, bytes }
          detail := s!"{tool} (?), {id.take 16} as {key.take 16}, {bytes.size} bytes (cached)"
          elapsed := ← since t0 }
      | .error d =>
        return {
          undrawn := some (src, .answered d none)
          detail := s!"{tool} unavailable ({why}), {id.take 16} as {key.take 16}, placeholder"
          elapsed := ← since t0 }
    | .present version =>
      let answer ← PictureAssets.fulfil picDir tool stamp version wrapped
      let outcome := answer.result.outcome
      let bytes := answer.result.bytes
      let result := match outcome with
        | .drawn => some { src, bytes : PicResult }
        | .refused _ | .inconclusive _ => none
      let status := match outcome with
        | .drawn => s!"{bytes.size} bytes"
        | .refused _ => "drew nothing"
        | .inconclusive words => s!"did not finish ({words})"
      return {
        result
        detail := s!"{tool} ({version}), {id.take 16} as {key.take 16}, {status}" ++
          (if answer.cached then " (cached)" else "")
        elapsed := ← since t0
        undrawn := (Boundary.undrawnOf tool outcome (spanFor id) src).map (src, ·) }
  -- Four TeX processes bound peak memory on a laptop; this changes
  -- scheduling alone, never the request or its cache key.
  let attempts ← Batch.map 4 (fun (_, wrapped) => PictureAssets.key wrapped) fulfil refs
  let mut results := #[]
  let mut undrawn := #[]
  for attempt in attempts do
    if let some result := attempt.result then results := results.push result
    if let some loss := attempt.undrawn then undrawn := undrawn.push loss
    ui.phase "boundary" attempt.detail attempt.elapsed
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
  let some root ← FontDiscovery.cacheDir | return none
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
expensive kind. Returns whether the cache answered, for the phase line, and
whether a fact about the machine stopped an included SVG's plan, for the
page's placeholder (`Boundary.markUnplanned`). -/
def fetchImage (dir : System.FilePath) (pics : Array PicResult)
    (refused : Array (String × Diag)) (params : Image.PlanParams) (req : Image.Request) :
    IO (Image.Fetch × Bool × Bool) := do
  let src := req.src
  if src.startsWith Ir.picSrcPrefix then
    match pics.find? (·.src == src) with
    | some r =>
      return (.decoded "" (Image.probe r.bytes >>= Image.plan params) none none none none,
        false, false)
    | none =>
      match refused.find? (·.1 == src) with
      | some (_, why) => return (.refused why, false, false)
      | none =>
        return (.missing "the boundary cache (no picture declares this source)", false, false)
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
    return (.missing p.toString, false, false)
  | some (cand, p) =>
    let bytes : Except String ByteArray ← try pure (.ok (← IO.FS.readBinFile p))
      catch e => pure (.error (toString e))
    match bytes with
    | .error e => return (.unreadable e, false, false)
    | .ok bytes =>
      let href := if cand == src then "" else cand
      if Image.isSvg cand then
        let (res, stopped) ← ImageAssets.svgPlanResult params bytes req.page
        return (.decoded href res (some bytes) none (some bytes) none, false, stopped)
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
          (some bytes) companion, false, false)
      else
        let (res, fromCache) ← decodeImageCached params bytes
        return (.decoded href res none none (some bytes) none, fromCache, false)

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
refusals keep their own span. An include whose plan a fact about the
machine stopped carries the page's placeholder (`Boundary.markUnplanned`). -/
def loadImages (file : String) (doc : Ir.Doc) (pics : Array PicResult := #[])
    (refused : Array (String × Diag) := #[])
    (imageSpans : Array (String × Span) := #[]) :
    IO (Image.Store × Array Diag × Nat) := do
  let dir := (System.FilePath.mk file).parent.getD "."
  let params := Image.PlanParams.default
  let mut fetched : Array (Image.Request × Image.Fetch) := #[]
  let mut stopped : Array Image.Request := #[]
  let mut hits := 0
  for req in Ir.imageRequests doc do
    let (f, fromCache, machine) ← fetchImage dir pics refused params req
    if fromCache then hits := hits + 1
    if machine then stopped := stopped.push req
    fetched := fetched.push (req, f)
  let (store, diags) := Image.fulfilRequests fetched
  let store := Boundary.markUnplanned stopped store
  let diags := (diags ++ PlanLoss.ledger store).map fun d =>
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
  return { entries := ← BrowserFaces.prepareAll imgs.entries }

def countErrors (diags : Array Diag) : Nat :=
  diags.foldl (fun n d => if d.severity == .error then n + 1 else n) 0

/-- Convert the captured boundary PDF to captured browser SVG, checked as
publication checks it (`Boundary.htmlFace`). A conversion that failed, or a
check that did not finish, retains the existing named fallback — W0378 at the
picture's span, and the rendered subset's drawing where it draws the picture
in part; no output path is consulted. -/
def picsToSvg (pics : Array PicResult) (imgs : Image.Store)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Image.Store × Array Diag × Array String) := do
  let mut entries := imgs.entries
  let mut diags : Array Diag := #[]
  let mut unconverted : Array String := #[]
  for r in pics do
    match ← Boundary.htmlFace r.bytes with
    | .ok bytes =>
      entries := entries.map fun en =>
        if en.src == r.src then { en with webSvg := some bytes } else en
    | .error why =>
      diags := diags.push (DriverDiag.atImageRequest imageSpans r.src (DriverDiag.boundarySvgMissing r.src why))
      unconverted := unconverted.push r.src
  return (Boundary.markFaceless { entries }, diags, unconverted)

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
    (withdrawn : Array String := #[]) (ledger : Encoding.Ledger := {}) :
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
  let reqSpans := { reqSpans with frames := Bib.remapSources doc reqSpans.frames }
  let (doc, bibDiags, ledger) ← Input.resolveBibliography file doc reqSpans.bib ledger
  unless bibDiags.isEmpty && (Ir.bibRefs doc).isEmpty || !phases do
    ui.phase "bib" s!"{(Ir.bibRefs doc).size} sources" (← since t)
  -- The bibliography is the last file a document reads, so the input
  -- encoding's one note can name every file now.
  let bibDiags := bibDiags ++ ledger.notes
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
  /-- The input encoding the document declares and the files read under
  it, which the bibliography joins. -/
  ledger : Encoding.Ledger
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
  let src ← Input.readDocument file bytes ui.phase
  let earlier := src.diags
  let spliced := src.spliced
  -- One rewrite, one boundary scan, one macro scan: two elaborations of
  -- one document must read one source, or their agreement would be about
  -- two (`Elab.prepareExecuted`).
  let t ← IO.monoMsNow
  let prepared := Elab.prepareExecuted file src.executed
  ui.phase "prepare" s!"{prepared.raws.size} top-level nodes" (← since t)
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
      (ledger := src.ledger)
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
        (provisional.getD (fun _ _ => {})) (phases := false) (ledger := src.ledger)
      pure (doc, diags, reqSpans, prepared, earlier)
  return some { doc := doc, diags := diags, spans := reqSpans
                prepared := prepared, earlier := earlier, spliced := spliced
                ledger := src.ledger
                cache := cache, scan := scan, provisional := provisional }

/-- The reporting scope is the output plan's projection. Markdown has no
backend-specific diagnostic scope; common source diagnostics still apply. -/
def diagnosticOutputs (emit : Array Emit) : Array Diag.Output :=
  emit.filterMap fun e => match e with
    | .pdf => some .pdf
    | .html => some .html
    | .md => none

/-- **Is the document elaboration returned already the fixed point?** It
was elaborated against `front.provisional`; font assembly settled on `fs`
and returned `resolved`, the same document with its alphabets resolved
against `fs`'s coverage. Where the two faces measure every label alike
(`Cli.FontFix.agree`, over `probes`), the extents the placement used are
the extents `fs` gives — `extent_agree` is the step — so no second
elaboration can change the document; where they differ, or where no
provisional face was resolved and the body drew a picture anyway, it is
elaborated again against `fs`'s measure, which this returns beside the
probes and the verdict. The probes are `front.doc`'s labels, the calls
elaboration made, never `resolved`'s: those carry `fs`'s alphabets, and
where the faces' coverage differ they measure alike where the labels
elaboration measured do not. -/
def settlement (front : Front) (fs : Font.FontSet) (resolved : Ir.Doc) :
    Ir.Pic.LabelMetric × Array FontFix.Probe × Bool :=
  let metric := Layout.labelMetric (Layout.Geom.ofPage resolved.page) fs
  let ps := FontFix.probes front.doc.body
  (metric, ps, match front.provisional with
    | some pre => FontFix.agree pre metric ps
    | none => Elab.enginePictures resolved.body == 0)

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
    -- subset's drawing with its loss named once (`Boundary.foldLines`), never
    -- a placeholder the subset could have filled — as a picture the document
    -- keeps to the subset (`\pictures{ tool = none }`) ships its drawing with
    -- its loss named once. A document already failing asks nothing of the
    -- tool — its build stops at the first resolution either way.
    let tool := front.doc.pictureTool.getD "lualatex"
    let declined := Boundary.linesOf tool {} front.spans.declined
    let front := { front with diags := Boundary.foldLines front.doc.allow allowAll declined front.diags }
    let failing := (Diag.resolveAll front.doc.allow allowAll (Diag.forOutputs outputs front.diags)).errors > 0
    let (pics, undrawn) ← if failing then pure (#[], #[])
      else resolvePictures ui front.doc front.spans.images
    let w := Boundary.withdraw front.spans.fallbacks undrawn
    let front ← if w.ids.isEmpty then pure front else do
      let t ← IO.monoMsNow
      let (doc, diags, spans) ← elaborate ui file front.prepared front.earlier front.spliced
        (front.provisional.getD (fun _ _ => {})) (phases := false) (withdrawn := w.ids)
        (ledger := front.ledger)
      ui.phase "withdraw" s!"{w.ids.size} pictures drawn by the rendered subset" (← since t)
      pure { front with doc := doc, spans := spans
                        diags := Boundary.foldLines doc.allow allowAll
                          (Boundary.linesOf tool w spans.declined) diags }
    let refused := w.standing
    let doc := front.doc
    let sourceDiag := front.prepared.sourceTriggers.attribute
    let diags := front.diags.map sourceDiag
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
      ui.diag (sourceDiag d)
      ui.summary file 1 (← since t0)
      return 1
    | .ok (fs, doc, fontDiags, paths) =>
      resolved := resolved.append
        (← ui.resolve doc.allow allowAll (outputs := outputs) (fontDiags.map sourceDiag))
      if resolved.errors > 0 then
        ui.accepted resolved.accepted
        ui.summary file resolved.errors (← since t0)
        return 1
      let names := ", ".intercalate (fs.fonts.toList.map (·.psName))
      ui.phase "font" s!"{names} ({paths})" (← since t)
      -- The artifact is a function of the document and the font
      -- environment, never of whichever face happened to be resolved first
      -- (`settlement`).
      let t ← IO.monoMsNow
      let (metric, ps, settled) := settlement front fs doc
      if let some pre := front.provisional then
        ui.phase "settle" (if settled then s!"provisional face holds ({ps.size} labels)"
          else s!"provisional face superseded \
({FontFix.disagreements pre metric ps} of {ps.size} labels)") (← since t)
      let (doc, reqSpans) ← if settled then pure (doc, reqSpans) else do
        let t ← IO.monoMsNow
        let (doc2, _, spans2) ←
          elaborate ui file front.prepared front.earlier front.spliced metric
            (phases := false) (withdrawn := w.ids) (ledger := front.ledger)
        ui.phase "remeasure" s!"{Elab.enginePictures doc.body} pictures" (← since t)
        let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
        pure ((Ir.resolveMathAlphas fs.mathAlphabets family doc2).1, spans2)
      let t ← IO.monoMsNow
      let (imgs, imgDiags, imgHits) ← loadImages file doc pics refused reqSpans.images
      let imgDiags := (imgDiags ++ PlanLoss.pictureAlts doc reqSpans.images imgs).map sourceDiag
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
        (frameSpans := Layout.frameSpansForPdf doc reqSpans.frames)
        (pictureSpans := Layout.pictureSpansForPdf doc reqSpans.images)
      let layoutDiags := out.diags.map sourceDiag
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) layoutDiags)
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
      -- decision has to see what this run emits. The set here is the
      -- settled one — `build` holds no other — so no assembly gate is
      -- needed on top. The declared contract is held against each emitted
      -- artifact's realization record beside it: warnings, resolved before
      -- the gate and never gating (`PlanLoss.ofPlan`).
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
        ((PlanLoss.ofPlan emit fs doc).map sourceDiag))
      let mut htmlBuilt : Option HtmlArtifact := none
      if emit.contains .html then
        let t ← IO.monoMsNow
        let cssMode := match css with
          | .own => HtmlDoc.CssMode.own
          | .bulma => HtmlDoc.CssMode.bulma
          | .none => HtmlDoc.CssMode.none
        -- The boundary pictures' HTML face: captured PDFs convert to
        -- checked SVG bytes (`picsToSvg`; W0378 names a face this host
        -- could not convert or check). A picture left without one, and that
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
            (phases := false) (withdrawn := w.ids ++ htmlOnly) (ledger := front.ledger)
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
          -- The footline's box is the page's band box, over the same faces.
          footBox := fun n band => some (Layout.footBandBox (Layout.Geom.ofPage doc.page) fs imgs n band)
          cancelMetric := fun measures ss st spec body value =>
            Layout.cancelMetric (Layout.Geom.ofPage doc.page) fs ss st spec body value (some measures)
          mathEm := fun measures ss st =>
            Layout.mathEm (Layout.Geom.ofPage doc.page) fs ss st (some measures)
          mathTextEm := fun measures ss st =>
            Layout.mathTextEm (Layout.Geom.ofPage doc.page) fs ss st (some measures)
          -- A markdown table's size and overhang: the page's own decision,
          -- over the one face set.
          tableFit := fun avail cols padL padR rows spans =>
            let fit := Layout.tableFit (Layout.Geom.ofPage htmlDoc.page) fs imgs
              (Layout.tableLength none htmlDoc.preambleFace "tabcolsep") avail cols padL padR rows
              spans
            (fit.step, fit.overhang > 0)
        }
        let (result, hdiags) ← prepareHtml file hcfg htmlDoc
        resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
          (hdiags.map front.prepared.sourceTriggers.attribute))
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
        let cache ← FontDiscovery.cacheDir
        let fs := { fs with zdata := ← Compression.fontZdata cache fs.fonts.size keep programs }
        -- The structure tree the pages' `leaf` indices name: the one the
        -- layout attributed against (`Layout.pdfView`), projected once.
        let tree := Struct.ofDoc (Layout.pdfView doc)
        let ops := Pdf.pageOps geom fs out.pages imgs tree keep
        let streams ← Compression.pageStreams cache (ops.map fun o => (Pdf.render o).toUTF8)
        match Pdf.writeChecked geom fs out.pages doc.info imgs out.outline streams tree ops programs with
        | .error error =>
          ui.diag (DriverDiag.pdfWriteRefused error)
          ui.accepted resolved.accepted
          ui.summary file 1 (← since t0)
          return 1
        | .ok pdf =>
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
      -- Accepting a warning quiets the report, never the fact. A PDF also
      -- judges placed paint; a source-only plan cannot see every run.
      let shipped := if doc.asserts.any (·.kind == .accessibilityAA) then
          let a11y := if pdfBuilt.isSome then
              Check.pdfA11ySummary doc (diags ++ imgDiags) geom fs out
            else Check.a11ySummary doc (diags ++ imgDiags)
          { shipped with a11y }
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
      let (written, unwritten) ← publish outDir (htmlBuilt.map (htmlPath, ·))
        (mdBuilt.map (mdPath, ·)) (pdfBuilt.map (pdfPath, ·))
      unless unwritten.isEmpty do
        for d in unwritten do
          ui.diag d
        ui.accepted resolved.accepted
        ui.summary file unwritten.size (← since t0) written
        return exitFor unwritten.size 0 resolved.warnings ui.cfg.werror
      -- The hatch's other teeth: an `\allow` that never fired is stale
      -- acceptance and warns; what was accepted always prints.
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
        ((Diag.unfired doc.allow resolved.fired).map DriverDiag.allowUnfired))
      ui.accepted resolved.accepted
      ui.done file (String.intercalate ", " written.toList) out.pages.size (← since t0)
        resolved.notes
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

public def main (argv : List String) : IO UInt32 := do
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
      let faces ← FontDiscovery.scan (cfg.fontDirs.toList ++ (← texFontDirs))
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

end LeanTex.Cli.Driver
