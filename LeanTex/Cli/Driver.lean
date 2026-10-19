module

import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.TexFontTrees
import LeanTex.Version
public import LeanTex.Core.Diag
import LeanTex.Core.Encoding
import LeanTex.Core.Flate
import LeanTex.Core.PdfCensus
import LeanTex.Core.PdfContract
import LeanTex.Core.PdfX
public import LeanTex.Core.Image
public import LeanTex.Core.Gfx
public import LeanTex.Core.PdfRead
import LeanTex.Core.Parse
import LeanTex.Core.Ir
import LeanTex.Core.Struct
import LeanTex.Core.Theme
import LeanTex.Core.Compat
import LeanTex.Core.Elab
import LeanTex.Core.Contrast
import LeanTex.Core.BibStyle
import LeanTex.Core.BibElab
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
import LeanTex.Core.Xml
import LeanTex.Core.SvgImport
import LeanTex.Core.SvgPoster
import LeanTex.Core.LayoutFigure
import LeanTex.Core.FigureLoss
import LeanTex.Core.FigureAlt
import LeanTex.Core.FigureSvg
public import LeanTex.Core.FigureStore
import LeanTex.Cli.Args
import LeanTex.Cli.Render
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.Input
import LeanTex.Cli.FontEnv
import LeanTex.Cli.FontAssembly
import LeanTex.Cli.FontFix
import LeanTex.Cli.PlanLoss
import LeanTex.Cli.Boundary
import LeanTex.Cli.Host
import LeanTex.Cli.Batch
import LeanTex.Cli.Compression
import LeanTex.Cli.Engine
import LeanTex.Cli.PlanCache
import LeanTex.Cli.PictureAssets
public import LeanTex.Cli.PicCache
import LeanTex.Cli.ToolProbe
import LeanTex.Cli.ImageAssets
import LeanTex.Cli.BrowserFaces
import LeanTex.Cli.PdfFaces
import LeanTex.Cli.ListingHighlight
import LeanTex.Cli.PublicationPaths
import LeanTex.Cli.Publication
import LeanTex.Cli.RunCost

namespace LeanTex.Cli.Driver

open LeanTex.Core LeanTex.Cli LeanTex.Cli.Publication LeanTex.Cli.FontAssembly

structure Ui where
  cfg : Config
  color : Bool
  errStream : IO.FS.Stream
  outStream : IO.FS.Stream
  showOutput : Bool := false
  /-- Whether the summary states the process's peak, which a watcher's rebuild has only
  where its start reset it. -/
  statesPeak : Bool := true

def Ui.mk' (cfg : Config) : IO Ui := do
  let errStream ← IO.getStderr
  let color ← match cfg.color with
    | .always => pure true
    | .never => pure false
    | .auto => do
      let noColor := (← IO.getEnv "NO_COLOR").isSome
      let tty ← errStream.isTty
      pure (!noColor && tty)
  return ⟨cfg, color, errStream, ← IO.getStdout, false, true⟩

/-- The sole terminal sink for document diagnostics, rendering a `Diag` only as it writes
the chosen stream. -/
def Ui.diag (ui : Ui) (d : Diag) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDiag d)
  else if d.severity != .note || ui.cfg.verbosity ≥ 1 then
    ui.errStream.putStrLn (Render.human ui.color d (showOutput := ui.showOutput))

/-- Resolve and print one phase against the document's acceptance (`\allow`,
`--best-effort`): a repeated warning prints once with its count, its repeats as notes
shown under `-v`; porcelain keeps every site. -/
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

/-- The accepted-loss line, printed whenever a loss was accepted, under `-q` too, counting
each census loss once. -/
def Ui.accepted (ui : Ui) (accepted : Array Diag.Accepted) : IO Unit := do
  if accepted.isEmpty then return
  let counts := tally (Diag.acceptedLosses accepted)
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

/-- The `font` phase; its porcelain record also names the loaded face files and how many
faces the scan found. -/
def Ui.fontPhase (ui : Ui) (names : String) (paths : Array String) (scanned ms : Nat) :
    IO Unit := do
  let detail := s!"{names} ({", ".intercalate paths.toList})"
  if ui.cfg.porcelain && ui.cfg.verbosity ≥ 1 then
    ui.outStream.putStrLn (Render.porcelainFontPhase detail ms paths scanned)
  else ui.phase "font" detail ms

/-- The most memory the process held resident while this build ran, a watcher's earlier
builds included. -/
def Ui.peak (ui : Ui) : IO (Option Nat) :=
  if ui.statesPeak then RunCost.peakKiB else pure none

/-- A run's summary record, flushed as written, since under `--watch` the process never
exits. -/
def Ui.summary (ui : Ui) (file : String) (errors ms : Nat) (written : Array String := #[]) :
    IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn
      (Render.porcelainSummary file (errors == 0) errors ms written (← ui.peak))
    ui.outStream.flush
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanSummary ui.color file errors ms written)

def Ui.done (ui : Ui) (file output : String) (pages : Option Nat) (ms : Nat) (notes : Nat := 0) :
    IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDone file output pages ms (← ui.peak))
    ui.outStream.flush
  else if !ui.cfg.quiet then
    let shown := if ui.cfg.verbosity ≥ 1 then 0 else notes
    ui.errStream.putStrLn (Render.humanDone ui.color file output pages ms shown)

/-- The `--werror` verdict, after the written outputs. -/
def Ui.werror (ui : Ui) (file : String) (warnings ms : Nat) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainWerror file warnings ms (← ui.peak))
    ui.outStream.flush
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanWerror ui.color file warnings ms)

/-- The font directories of the TeX distribution on `PATH`, found without starting a
process. -/
def texFontDirs : IO (List String) := TexFontTrees.hostRoots

/-- Which directories to look in and what is there, the document's `\fonts{ dir = ... }`
before the host's. -/
def scanFaces (ui : Ui) (file : String) (spec : Ir.FontSpec)
    (announce : Bool := true) : IO FaceScan := do
  let (docDirs, dirDiags) ← FontEnv.resolveDocDirs file spec.dirs
  let t ← IO.monoMsNow
  let faces ← FontDiscovery.scanRoots
    (docDirs ++ (← FontDiscovery.systemRoots (ui.cfg.fontDirs.toList ++ (← texFontDirs))))
  if announce then ui.phase "fontdb" s!"{faces.size} faces" ((← IO.monoMsNow) - t)
  return { faces := faces, docDirs := docDirs, dirs := spec.dirs, diags := dirDiags
           privateDirs := ui.cfg.fontDirs.toList ++ (← FontDiscovery.envDirs) }

def since (t0 : Nat) : IO Nat := do
  return (← IO.monoMsNow) - t0

/-- Where the markdown twin is written: `outPath`, or the name the document declares
(`\output{ md = ... }`) read from the same directory; an explicit `-o` file still wins. -/
def mdOutPath (output : Option String) (outputIsDir : Bool) (source : String)
    (declared : Option String) : String :=
  let base := outPath output outputIsDir source .md
  match declared with
  | some name =>
    if (output.bind emitOfPath) == some Emit.md then base
    else PublicationPaths.placed ((System.FilePath.mk base).parent.getD ".").toString name
  | none => base

/-- The bibliography names a twin written at `mdPath` gives the files its document's bibliography
reads, by the names the document gives them. -/
def twinBibNames (file mdPath : String) (doc : Ir.Doc) : Array (String × String) :=
  let dir := ((System.FilePath.mk mdPath).parent.getD ".").toString
  (Ir.bibRefs doc).filterMap fun src =>
    let name := Bib.sourceName src
    (World.ToolPath.relative dir (Input.besideDocument file name).toString).map (name, ·)

/-- The markdown twin's link from the page: the declared name, else the derived file's own
name; none where the page cannot link that name. -/
def twinHref (mdPath : String) (declared : Option String) : Option String :=
  match declared with
  | some name => PublicationPaths.nameHref name
  | none => (System.FilePath.mk mdPath).fileName.bind PublicationPaths.nameHref


/-- One fulfilled boundary picture, whose captured bytes both artifacts read. -/
structure PicResult where
  src : String
  bytes : ByteArray

private structure PicAttempt where
  result : Option PicResult := none
  undrawn : Option (String × Boundary.Undrawn) := none
  detail : String
  elapsed : Nat

/-- Fulfil elaborated picture requests through `PictureAssets`, results and diagnostics in
source order and unfinished attempts kept apart from refusals; also returns every file a
request staged. -/
def resolvePictures (ui : Ui) (file : String) (doc : Ir.Doc)
    (imageSpans : Array (String × Span) := #[]) (faces : Ir.FontSpec := doc.fonts) :
    IO (Array PicResult × Array (String × Boundary.Undrawn) × Array String) := do
  let refs := Ir.pictureRefs doc faces
  if refs.isEmpty then return (#[], #[], #[])
  -- The document's own request stands behind a faced one the tool refused (`Boundary.ownRequest?`).
  -- premise: boundaryFaceRetryChecks — a refused faced request draws the document's own
  let own := Ir.pictureRefs doc
  let dir := ((System.FilePath.mk file).parent.getD ".").toString
  let keyedRefs ← refs.mapM fun (id, wrapped) => do
    let ownWrapped := ((own.find? (·.1 == id)).map (·.2)).getD wrapped
    return (id, wrapped, ownWrapped,
      ← Host.runIO (Boundary.requestInputs dir doc.graphicsPath wrapped))
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
  let fulfil (request : String × String × String × Array (String × ByteArray)) :
      IO PicAttempt := do
    let (id, wrapped, ownWrapped, inputs) := request
    let src := Ir.picSrcPrefix ++ id
    -- Keyed by the request, its design and its inputs' bytes: only an edit it reads re-renders.
    let key := PictureAssets.key (PictureAssets.keyed wrapped inputs)
    match found with
    | .absent why =>
      let ownKey := PictureAssets.key (PictureAssets.keyed ownWrapped inputs)
      let earlier ← match picDir with
        | some dir => do
          match ← Boundary.coldPicture dir tool key (spanFor id) why with
          | .error d =>
            if ownKey == key then pure (.error d)
            else Boundary.coldPicture dir tool ownKey (spanFor id) why
          | drawn => pure drawn
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
      let first ← PictureAssets.fulfil picDir tool stamp version wrapped inputs
      let (answer, owned) ← match Boundary.ownRequest? wrapped ownWrapped first.result.outcome with
        | some r => pure ((← PictureAssets.fulfil picDir tool stamp version r inputs), true)
        | none => pure (first, false)
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
          (if owned then ", asked again without the page's faces" else "") ++
          (if answer.cached then " (cached)" else "")
        elapsed := ← since t0
        undrawn := (Boundary.undrawnOf tool outcome (spanFor id) src).map (src, ·) }
  -- Four TeX processes at once bound peak memory; scheduling never changes a request or its key.
  let attempts ← Batch.map 4 (fun (_, wrapped, _, inputs) =>
    PictureAssets.key (PictureAssets.keyed wrapped inputs)) fulfil keyedRefs
  let mut results := #[]
  let mut undrawn := #[]
  for attempt in attempts do
    if let some result := attempt.result then results := results.push result
    if let some loss := attempt.undrawn then undrawn := undrawn.push loss
    ui.phase "boundary" attempt.detail attempt.elapsed
  let staged := keyedRefs.flatMap fun (_, _, _, inputs) =>
    inputs.map fun (cand, _) => Boundary.inputPath dir cand
  return (results, undrawn, staged)

/-- A converter a lossy SVG may ask: given the canonical spelling and whether the drawing
is font-independent, a plan or the attempt that drew nothing, or none without a tool. -/
public abbrev Converter := ByteArray → Bool → IO (Option (Except PicCache.Outcome Image.Plan))

/-- A tool that is always there, answering as `run` answers. -/
public def Converter.always (run : ByteArray → Bool → IO (Except PicCache.Outcome Image.Plan)) :
    Converter :=
  fun b i => some <$> run b i

/-- What the native SVG path decided for one source: the plan layout reads, the figure the
engine draws, whether the source animates, and the diagnostics owed. -/
public structure SvgFetch where
  res : Except String Image.Plan
  vector : Option (Gfx.Figure Gfx.Run) := none
  /-- The drawn figure's raster plans, one per raster in order, which the PDF writer
  embeds. -/
  plans : Array Image.Plan := #[]
  moving : Bool := false
  diags : Array Diag := #[]
  /-- The figure's own `<title>`, whichever route drew it. -/
  title : Option String := none
  /-- The source bytes the native judge accepted, which the page need not judge again. -/
  judged : Option ByteArray := none

/-- What the store keeps of a route's answer: the drawn figure, whether it moves, and its
rasters' plans. -/
public def SvgFetch.drawn (f : SvgFetch) : FigureStore.Drawn :=
  { vector := f.vector, moving := f.moving, plans := f.plans }

/-- The plan a drawn figure stands under in the store: its box in CSS pixels at their own
density, with no payload. -/
public def vectorPlan (fig : Gfx.Figure Gfx.Run) : Image.Plan :=
  let w := fig.box.2.1 - fig.box.1.1
  let h := fig.box.2.2 - fig.box.1.2
  { pxW := HtmlDoc.cssPxOfSp w, pxH := HtmlDoc.cssPxOfSp h, dpiX := 96, dpiY := 96 }

/-- The SVG route (`Boundary.route`): judged, posed and imported natively; a lossy figure
goes to `convert` as its canonical spelling, never the authored bytes, and `convert` is
none where the document refused the converter. -/
public def svgFetch (src : String) (bytes : ByteArray) (page : PdfRead.PageSelection) (lang : String)
    (convert : Option Converter) (params : Image.PlanParams := .default) : IO SvgFetch := do
  let terminal ← match ImageAssets.svgPosterAtEnd page with
    | .error e => return { res := .error e }
    | .ok t => pure t
  let (tree, sheets) ← match Svg.judged bytes with
    | .error r => return { res := .error r.message }
    | .ok j => pure j
  let pose ← match SvgPoster.poseOf tree terminal with
    | .error why => return { res := .error why }
    | .ok t => pure t
  -- Whether the figure moves is the authored tree's answer; a final pose holds no animation.
  let moving := Svg.moves tree
  let i := Svg.importTree pose lang (sheets := if terminal then Svg.sheetsOf pose else sheets)
  let (fig, plans) := FigureStore.rasterPlans params i.fig
  let losses := fig.losses
  -- An inkless import note, such as a dropped link, is named once on any route.
  let notes := i.notes.map (FigureLoss.svgNoteDiag src)
  -- premise: Tests.svgRouteChecks — the page skips judging only the bytes this judge accepted
  let native : SvgFetch :=
    { res := .ok (vectorPlan fig), vector := some fig, plans, moving, title := fig.title, diags := notes
      judged := some bytes }
  let verdict : Boundary.Verdict := if losses.isEmpty then .exact else .lossy losses
  let decl : Boundary.Refusal := if convert.isSome then .none else .declared
  if !verdict.asksTool decl then
    let owed := Boundary.svgRouteDiags moving src .refused losses (Boundary.route verdict .notAsked decl)
    let diags := notes ++ owed
    return { native with diags }
  -- premise: Tests.svgRouteChecks — converter presence never changes a lossless figure
  let answer ← match convert with
    | some run => run (Xml.renderItem pose) (!Svg.fontDependent pose)
    | none => pure none
  let (tool, why) : Boundary.ToolState × FigureLoss.Unconverted := match answer with
    | some (.ok _) => (.drew, .absent)
    | some (.error o) => (.failed (Boundary.undrawnWords o), Boundary.undrawn o)
    | none => (.failed "rsvg-convert is not on PATH", .absent)
  let route := Boundary.route verdict tool decl
  let owed := Boundary.svgRouteDiags moving src why losses route
  let diags := notes ++ owed
  match route, answer with
  | .tool, some (.ok plan) =>
    return { res := .ok plan, moving, title := fig.title, diags, judged := some bytes }
  | _, _ => return { native with diags }

/-- The converter a lossy SVG may ask when the document allows it: `run`, once a build per
canonical spelling, while `probe`, asked once on first need, says the host has it. -/
public def svgConverterWith (probe : IO Bool)
    (run : ByteArray → Bool → IO (Except PicCache.Outcome Image.Plan))
    (allowed : Bool) : IO (Option Converter) := do
  if !allowed then return none
  let present ← ToolProbe.once probe
  -- A later asker takes the attempt it met, unless that attempt reached no verdict.
  let ask ← Batch.shared (· matches .error (.inconclusive _))
    fun ((canonical, independent) : ByteArray × Bool) => run canonical independent
  return some fun canonical independent => do
    if ← present then some <$> ask (canonical, independent) else pure none

/-- librsvg's `rsvg-convert` as that converter (`\figures{ convert = none }`
refuses it). -/
public def svgConverter (params : Image.PlanParams) (allowed : Bool) : IO (Option Converter) :=
  svgConverterWith (do return (← ToolProbe.onPath "rsvg-convert").isSome)
    (ImageAssets.canonicalPlan params) allowed

/-- A request's source as found: its answer already, a boundary picture's bytes, or bytes read at
a path, the last two still to plan. -/
inductive Located where
  | done (answer : Image.Fetch × Bool × SvgFetch × Array String)
  | picture (bytes : ByteArray)
  | read (cand : String) (path : System.FilePath) (bytes : ByteArray)

/-- One image source found and read, the effect half of `Image.fulfil`: a boundary picture from
its results, else a path beside the document through graphicx's extensions. -/
def locateImage (dir : System.FilePath) (pics : Array PicResult)
    (refused : Array (String × Diag)) (req : Image.Request) (paths : Array String := #[]) :
    IO Located := do
  let src := req.src
  let none' : SvgFetch := { res := .error "" }
  if src.startsWith Ir.picSrcPrefix then
    match pics.find? (·.src == src) with
    | some r => return .picture r.bytes
    | none =>
      match refused.find? (·.1 == src) with
      | some (_, why) => return .done (.refused why, false, none', #[])
      | none =>
        return .done (.missing "the boundary cache (no picture declares this source)", false, none',
          #[])
  let mut hit : Option (String × System.FilePath) := none
  for cand in Image.searchCandidates paths src do
    let p := if (System.FilePath.mk cand).isAbsolute then System.FilePath.mk cand
      else dir / cand
    if ← p.pathExists then
      hit := some (cand, p)
      break
  match hit with
  | none =>
    let p := if (System.FilePath.mk src).isAbsolute then System.FilePath.mk src
      else dir / src
    return .done (.missing p.toString, false, none', #[])
  | some (cand, p) =>
    let bytes : Except String ByteArray ← try pure (.ok (← IO.FS.readBinFile p))
      catch e => pure (.error (toString e))
    match bytes with
    | .error e => return .done (.unreadable e, false, none', #[p.toString])
    | .ok bytes => return .read cand p bytes

/-- A source's batch key: a read file's size, so two files of one content never plan at once and
each plan cache slot has one writer, or its position for a source no plan cache slot holds. -/
def Located.key (l : Located) (index : Nat) : Sum Nat Nat :=
  match l with
  | .done _ => .inl index
  | .picture _ => .inl index
  | .read _ _ bytes => .inr bytes.size

/-- A found source planned: a boundary picture as it stands, an SVG through `svgFetch`, a page or
animation through `Image.decodeRequest`, else through the plan cache; also whether the cache
answered, and the files read. -/
def planLocated (params : Image.PlanParams) (lang : String) (convert : Option Converter)
    (req : Image.Request) (cache : Option Engine.Cache) : Located →
    IO (Image.Fetch × Bool × SvgFetch × Array String)
  | .done answer => return answer
  | .picture bytes =>
    return (.decoded "" (Image.probe bytes >>= Image.plan params) none none none none, false,
      { res := .error "" }, #[])
  | .read cand p bytes => do
    let src := req.src
    let none' : SvgFetch := { res := .error "" }
    let href := if cand == src then "" else cand
    if Image.isSvg cand then
      let f ← svgFetch src bytes req.page lang convert params
      return (.decoded href f.res (some bytes) none (some bytes) none, false, f, #[p.toString])
    else if req.page != .first || req.animated then
      let res := Image.decodeRequest params bytes req
      -- An animation's companion SVG is read once, here, beside its PDF.
      let companion ← if req.animated then do
          match ← (IO.FS.readBinFile (p.withExtension "svg")).toBaseIO with
          | .ok svg => pure (some (svg, p.withExtension "svg"))
          | .error _ =>
            let upper := p.withExtension "SVG"
            pure ((← (IO.FS.readBinFile upper).toBaseIO).toOption.map (·, upper))
        else pure none
      return (.decoded href (res.map (·.1)) none (res.toOption.bind (·.2))
        (some bytes) (companion.map (·.1)), false, none',
        #[p.toString] ++ (companion.map (·.2.toString)).toArray)
    else
      let (res, fromCache) ← PlanCache.decodeCached cache params bytes
      return (.decoded href res none none (some bytes) none, fromCache, none', #[p.toString])

/-- The document's image requests fulfilled in request order (`locateImage`, `planLocated`,
`Image.fulfil`), every unplanned fact named, with the cache-hit count, drawn SVGs' titles, the files
read and the SVG bytes the native judge accepted. -/
def loadImages (file : String) (doc : Ir.Doc) (pics : Array PicResult := #[])
    (refused : Array (String × Diag) := #[])
    (imageSpans : Array (String × Span) := #[]) (cache : Option Engine.Cache := none)
    (convert : Option Converter) :
    IO (Image.Store × Array Diag × Nat × Array (String × String) × Array String ×
      Array ByteArray) := do
  let dir := (System.FilePath.mk file).parent.getD "."
  let params := Image.PlanParams.default
  let mut fetched : Array (Image.Request × Image.Fetch) := #[]
  let mut svgs : Array SvgFetch := #[]
  let mut hits := 0
  let mut reads : Array String := #[]
  let reqs := Ir.imageRequests doc
  let located ← reqs.mapM fun req => locateImage dir pics refused req doc.graphicsPath
  -- Four at a time bounds peak memory; answers stand in request order.
  let answers ← Batch.map 4 (fun (k, _, l) => Located.key l k)
    (fun (_, req, l) => planLocated params doc.info.locale.tag convert req cache l)
    ((reqs.zip located).mapIdx fun k (req, l) => (k, req, l))
  for (req, (f, fromCache, svg, read)) in reqs.zip answers do
    if fromCache then hits := hits + 1
    fetched := fetched.push (req, f)
    reads := reads ++ read
    svgs := svgs.push svg
  let (store, diags) := Image.fulfilRequests fetched
  let store := FigureStore.attach store (svgs.map fun f => some f.drawn)
  -- A figure's route diagnostics stand at the span the document names its source at.
  let diags := diags ++ (fetched.zip svgs).flatMap fun ((req, _), f) =>
    f.diags.map (DriverDiag.atImageRequest imageSpans req.src)
  let diags := (diags ++ PlanLoss.ledger store).map fun d =>
    match d.subject with
    | some src => DriverDiag.atImageRequest imageSpans src d
    | none => d
  let titles := (store.entries.zip svgs).filterMap fun (en, f) =>
    if en.info.isSome then f.title.map (en.src, ·) else none
  return (store, diags, hits, titles, reads, svgs.filterMap (·.judged))

/-- The output intent's ICC profile and the path it was read at: beside the document, else, for a
profile l3pdfmeta describes, in the TeX distribution's colorprofiles package where LaTeX finds it;
W0446 where it is neither or no output profile. -/
def loadProfile (file : String) (info : Ir.Meta) : IO (Option (String × ByteArray) × Array Diag) := do
  let some oi := info.intent | return (none, #[])
  let some p := Publication.localPath? file oi.profile
    | return (none, #[PdfX.profileRefused oi.profile "names no local file" oi.span])
  let reply : Except World.Failure ByteArray ← Host.answer (.readFile p.toString)
  let builtin := (Ir.OutputIntent.builtin? oi.profile).isSome
  let (path, reply) ← match reply with
    | .error .absent =>
      if !builtin then pure (p.toString, reply) else do
      let found ← ((TexFontTrees.colorProfile oi.profile).runM Host.answer : BaseIO (Option String))
      match found with
      | some q => pure (q, ← (Host.answer (.readFile q) : IO (Except World.Failure ByteArray)))
      | none => pure (p.toString, reply)
    | _ => pure (p.toString, reply)
  match reply with
  | .error f =>
    let why := match f with
      | .absent => if builtin then "is neither beside the document nor in the TeX distribution's \
colorprofiles package" else "is not there"
      | .denied => "cannot be read, its permission denied"
      | .notRegular => "is no regular file"
      | .other w => s!"cannot be read: {w}"
    return (none, #[PdfX.profileRefused oi.profile why oi.span])
  | .ok b =>
    match PdfX.profileFault b oi.components with
    | some why => return (none, #[PdfX.profileRefused oi.profile why oi.span])
    | none => return (some (path, b), #[])

/-- The claim's losses less the missing output intent a refused profile already names (W0446). -/
def claimLosses (profileDiags claimDiags : Array Diag) : Array Diag :=
  if profileDiags.isEmpty then claimDiags
  else claimDiags.filter (·.subject != some "pdfx:output-intent")

/-- W0447 for each declaration a standing PDF/X claim replaces: a PDF version other than the 1.6
the standard is written on, and an unknown trapping, stated False as the engine traps nothing. -/
def pdfxDeclLosses (x : String) (info : Ir.Meta) : Array Diag :=
  let version := match info.pdfVersion with
    | some v =>
      if v == "1.6" then #[] else #[Diag.of .W0447
        "the declared PDF version is one the declared PDF standard does not admit; the standard's \
version is written" info.versionSpan
        (help := some "declare the version the standard is written on: \\DocumentMetadata{ pdfversion = 1.6 } or \\pdfmeta{ version = \"1.6\" }")
        (subject := some "pdfx:version") (output := some .pdf)
        (detail := some s!"the PDF/{x} standard is written on PDF 1.6; PDF {v} is declared, and 1.6 written")]
    | none => #[]
  let trapped := match info.trappedUnknownAt with
    | some site =>
      #[Diag.of .W0447 "the declared trapping is unknown, which the declared PDF standard does not \
admit; the file states False, as it is untrapped" (some site)
        (help := some "state the trapping: \\hypersetup{ pdftrapped = False }")
        (subject := some "pdfx:trapped") (output := some .pdf)
        (detail := some s!"PDF/{x} asks the trapping True or False")]
    | none => #[]
  version ++ trapped

/-- A file claiming a PDF/X standard kept only where its own bytes meet it, what it leaves out of
its `links` and only a preflight judges named; else the file `rewrite` writes without the claim,
and each requirement it breaks named (W0445). -/
def pdfxClaim (info : Ir.Meta) (pdf : ByteArray) (links : Nat)
    (rewrite : Ir.Meta → Except Pdf.WriteError ByteArray) :
    Except Pdf.WriteError (ByteArray × Array Diag) :=
  match info.pdfx with
  | none => .ok (pdf, #[])
  | some x =>
    let (facts, bs) := match PdfX.read pdf with
      | .ok f => (some f, PdfX.breaches f)
      | .error e => (none, #[⟨"census", s!"the engine's reader refuses the file: {e}"⟩])
    match facts, bs.isEmpty with
    | some f, true => .ok (pdf, pdfxDeclLosses x info ++ PdfX.claimDiags x f links)
    | _, _ => (rewrite { info with pdfx := none }).map (·, PdfX.breachDiags x bs)

/-- PDF sources' browser images of their selected page, converted from the bytes already
read; a declared animation's self-contained companion SVG serves where usable. -/
def imageBrowserFaces (imgs : Image.Store) : IO Image.Store := do
  return { imgs with entries := ← BrowserFaces.prepareAll imgs.entries }

/-- `imageBrowserFaces` with each face's route diagnostics and the faces the engine drew
itself, under the document's refusal `decl`. -/
def imageBrowserFacesNative (imgs : Image.Store) (decl : Boundary.Refusal := .none)
    (door : Option PdfFaces.Door := none) :
    IO (Image.Store × Array (String × Diag) × Array ByteArray × PdfFaces.Tally) := do
  let (entries, diags, natives, tally) ←
    BrowserFaces.prepareAllFaces imgs.entries (decl := decl) (door := door)
  return ({ imgs with entries }, diags, natives, tally)

def countErrors (diags : Array Diag) : Nat :=
  diags.foldl (fun n d => if d.severity == .error then n + 1 else n) 0

/-- Boundary pictures' browser faces, native first (`PdfFaces.face`): a picture nothing
drew keeps W0378 and the rendered subset's drawing where it draws it in part; also the
faces publication need not check, and how each was decided. -/
def picsToSvgNative (pics : Array PicResult) (imgs : Image.Store)
    (imageSpans : Array (String × Span) := #[]) (fallbacks : Array String := #[])
    (decl : Boundary.Refusal := .none) (door : Option PdfFaces.Door := none) :
    IO (Image.Store × Array Diag × Array String × Array ByteArray × PdfFaces.Tally) := do
  let mut entries := imgs.entries
  let mut diags : Array Diag := #[]
  let mut unconverted : Array String := #[]
  let mut natives : Array ByteArray := #[]
  let mut tally : PdfFaces.Tally := {}
  let cache ← PdfFaces.cacheDir
  let door ← match door with
    | some d => pure d
    | none => PdfFaces.door
  -- Four at a time, never two of one content, so each cache slot has one writer.
  let faces ← Batch.map 4 (fun (r : PicResult) => Flate.contentKey r.bytes) (fun r =>
    PdfFaces.face r.src r.bytes .first (door (ImageAssets.picFaceAnswer r.bytes))
      ImageAssets.validateSvgResult (decl := decl) (cache := cache)) pics
  for (r, f) in pics.zip faces do
    -- premise: nativeFigureBuildChecks — a textless face falls back to the subset's drawing
    let textless := f.route == .nativeWithLoss &&
      f.diags.any (fun d => d.subject.any (·.startsWith "figure:pdf:font:")) &&
      fallbacks.any (fun id => Ir.picSrcPrefix ++ id == r.src)
    if textless then
      diags := diags.push (DriverDiag.atImageRequest imageSpans r.src (DriverDiag.boundarySvgMissing r.src
        (if decl == .declared then .textlessDeclined else .textless)))
      unconverted := unconverted.push r.src
      continue
    tally := tally.add f.route
    diags := diags ++ f.diags.map (DriverDiag.atImageRequest imageSpans r.src)
    match f.bytes with
    | .ok bytes =>
      entries := entries.map fun en =>
        if en.src == r.src then { en with webSvg := some bytes, webWords := f.words } else en
      if f.checked then natives := natives.push bytes
    | .error why =>
      diags := diags.push (DriverDiag.atImageRequest imageSpans r.src
        (DriverDiag.boundarySvgMissing r.src (.unconverted why)))
      unconverted := unconverted.push r.src
  return (Boundary.markFaceless { imgs with entries }, diags, unconverted, natives, tally)

/-- `picsToSvgNative`'s store, diagnostics and unconverted pictures. -/
def picsToSvg (pics : Array PicResult) (imgs : Image.Store)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Image.Store × Array Diag × Array String) := do
  let (store, diags, unconverted, _, _) ← picsToSvgNative pics imgs imageSpans
  return (store, diags, unconverted)

/-- Elaborate against whatever label measurement the caller has, so the driver can
elaborate again where it is not the document's own. -/
def elaborate (ui : Ui) (file : String) (prepared : Elab.Prepared)
    (earlier : Array Diag) (spliced : Array (String × Option String × Pos))
    (metric : Ir.Pic.LabelMetric) (phases : Bool := true)
    (withdrawn : Array String := #[]) (ledger : Encoding.Ledger := {}) :
    IO (Ir.Doc × Array Diag × Elab.ReqSpans) := do
  let pass (prepared : Elab.Prepared) (phases : Bool) :
      IO (Ir.Doc × Array Diag × Elab.ReqSpans) := do
    let t ← IO.monoMsNow
    let (doc, elabDiags, reqSpans) := Elab.runPrepared file prepared earlier metric withdrawn
    -- N0020's counts are read off the elaborated diagnostics, so it is built after them.
    let elabDiags := elabDiags ++
      spliced.map fun (sty, src, pos) =>
        Compat.styRead (src.getD file) sty pos elabDiags
    if phases then ui.phase "elab" s!"{doc.body.size} blocks" (← since t)
    if phases then
      let t := ← IO.monoMsNow
      let summary := if (ui.cfg.effectiveEmit doc.output.formats).contains .html then
          Contrast.pageSummary doc
        else Contrast.paletteSummary doc.palette [.print]
      ui.phase "palette" summary.detail (← since t)
    let t ← IO.monoMsNow
    let reqSpans := { reqSpans with frames := Bib.remapSources doc reqSpans.frames }
    let (doc, bibDiags, ledger) ← Input.resolveBibliography file doc
      (Bib.FieldDoor.of file prepared).read reqSpans.labels reqSpans.bib ledger reqSpans.cites
    unless bibDiags.isEmpty && (Ir.bibRefs doc).isEmpty || !phases do
      ui.phase "bib" s!"{(Ir.bibRefs doc).size} sources" (← since t)
    let refDiags := Bib.refJudge reqSpans doc
    return (doc, Bib.accountFront elabDiags bibDiags ledger.notes refDiags, reqSpans)
  let first ← pass prepared phases
  -- A reference list's notes step the footnote counter where it stands, as a `.bbl` does.
  let counts := first.1.listNotes.map (·.2)
  if !prepared.listNotes.isEmpty || counts.all (· == 0) then return first
  let t ← IO.monoMsNow
  let second ← pass { prepared with listNotes := counts } false
  if phases then ui.phase "notes" s!"{counts.foldl (· + ·) 0} list notes" (← since t)
  return second

/-- What the front end hands the driver: the document, and what a second elaboration needs
if the measured face is not the settled one. -/
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
  /-- Every file the document's execution read, by the path it read it at
  (`Input.Source.reads`). -/
  reads : Array String
  /-- Parsed faces, shared by the provisional assembly and the final one. -/
  cache : FontEnv.Cache
  /-- The host's answer, taken once — absent where no face was needed yet. -/
  scan : Option FaceScan
  /-- The measurement the document was elaborated against; `none` when the source draws no
  measured picture. -/
  provisional : Option Ir.Pic.LabelMetric
  /-- The declared output profile as the host read it and where, and why it was refused where it
  was. -/
  profile : Option (String × ByteArray) × Array Diag

/-- Read and decode the file and run the front end, elaborating against a face resolved
from the preamble alone; `build` elaborates again where the settled face would measure a
label differently (`Cli.FontFix.agree`). -/
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
  -- Two elaborations of one document read one prepared source.
  let t ← IO.monoMsNow
  let prepared := Elab.prepareExecuted file src.executed
  ui.phase "prepare" s!"{prepared.raws.size} top-level nodes" (← since t)
  let cache ← FontEnv.Cache.mk'
  -- A face resolves only once something may measure against it; a math slot only for a formula.
  let wants := Elab.picWants prepared.raws
  let (scan, provisional) ← if !wants.draws then
      pure (none, none)
    else do
      let pre := Elab.preambleDoc file prepared
      let scan ← scanFaces ui file pre.fonts
      let t ← IO.monoMsNow
      match ← buildFontSet pre scan cache (.provisional wants.math) with
      | .error _ =>
        -- An unresolvable provisional face is the final assembly's to report.
        pure (some scan, none)
      | .ok (fsPre, _, _, _) =>
        let m := Layout.labelMetric (Layout.Geom.ofPage pre.page) fsPre
        ui.phase "provisional" s!"{fsPre.fonts.size} faces" (← since t)
        pure (some scan, some m)
  -- The output intent is the preamble's to declare, so its profile is read once, before the first
  -- elaboration, and a CMYK one shows every elaboration's CMYK.
  let profile ← if Elab.preambleNamesMeta prepared then
      loadProfile file (Elab.preambleDoc file prepared).info
    else pure (none, #[])
  let screen := (profile.1.bind (Icc.Transform.of? ·.2)).filter (·.space == "CMYK")
  let prepared := { prepared with profile := screen }
  let (doc, diags, reqSpans) ←
    elaborate ui file prepared earlier spliced (provisional.getD (fun _ _ => {}))
      (ledger := src.ledger)
  -- Highlighting is discovered once; every later elaboration reuses this snapshot.
  let requests := LeanTex.Core.ListingReply.requests doc reqSpans.code
  let (doc, diags, reqSpans, prepared, earlier) ← if requests.isEmpty then
      pure (doc, diags, reqSpans, prepared, earlier)
    else do
      let t ← IO.monoMsNow
      let (replies, listingDiags) ← LeanTex.Cli.ListingHighlight.fulfil requests
      ui.phase "highlight" s!"{replies.size} of {requests.size} listings" (← since t)
      let prepared := { prepared with listingReplies := replies }
      let earlier := earlier ++ listingDiags
      let (doc, diags, reqSpans) ← elaborate ui file prepared earlier spliced
        (provisional.getD (fun _ _ => {})) (phases := false) (ledger := src.ledger)
      pure (doc, diags, reqSpans, prepared, earlier)
  return some { doc := doc, diags := diags, spans := reqSpans
                prepared := prepared, earlier := earlier, spliced := spliced
                ledger := src.ledger, reads := src.reads
                cache := cache, scan := scan, provisional := provisional, profile }

/-- The reporting scope: each artifact the run writes, so a loss scoped to an artifact is
named exactly when it is written. -/
def diagnosticOutputs (emit : Array Emit) : Array Diag.Output :=
  emit.map fun e => match e with
    | .pdf => .pdf
    | .html => .html
    | .md => .md

/-- Whether the elaboration is already the fixed point: where the provisional and settled
faces measure every probed label alike (`Cli.FontFix.agree`) it is, else the settled
measure is returned for a second elaboration, with the probes and the verdict. -/
def settlement (front : Front) (fs : Font.FontSet) (resolved : Ir.Doc) :
    Ir.Pic.LabelMetric × Array FontFix.Probe × Bool :=
  let metric := Layout.labelMetric (Layout.Geom.ofPage resolved.page) fs
  let ps := FontFix.probes front.doc.body
  (metric, ps, match front.provisional with
    | some pre => FontFix.agree pre metric ps
    | none => Elab.enginePictures resolved.body == 0)

/-- The font roles a boundary request sets in, resolved before any request is wrapped: the
text slot and math face as the provisional assembly resolves them, and the typewriter
default. -/
def boundaryFaces (ui : Ui) (file : String) (front : Front) : IO (Ir.FontSpec × Front) := do
  let doc := front.doc
  if (Ir.pictureRefs doc).isEmpty then return (doc.fonts, front)
  let scan ← match front.scan.filter (·.dirs == doc.fonts.dirs) with
    | some s => pure s
    | none => scanFaces ui file doc.fonts
  let front := { front with scan := some scan }
  match ← buildFontSet doc scan front.cache (.provisional true) with
  | .ok (fs, _, _, _) => return (FontAssembly.boundaryFonts doc fs scan, front)
  | .error _ => return (doc.fonts, front)

/-- Every file a build reads, by the path it reads it at: the document, its execution's reads,
bibliography, images, staged picture inputs, every face read or found under the document's and the
run's own font directories, and its declared stylesheet, icon and output profile. -/
def buildInputs (file : String) (front : Front) (doc : Ir.Doc) (scan : FaceScan)
    (parsed imgReads staged faces : Array String) : Array String :=
  let owned := scan.docDirs ++ scan.privateDirs
  -- A collection's face is read from its collection, so the file read is the collection.
  let scanned := (scan.faces.filter fun face =>
    owned.any fun dir => face.path.startsWith (if dir.endsWith "/" then dir else dir ++ "/")).map
      (FontDb.faceFile ·.path)
  let declared := (doc.output.stylesheet.toArray ++ doc.info.favicon.toArray).filterMap fun name =>
    (Publication.localPath? file name).map (·.toString)
  -- The profile where it was read; one not read is the file it names beside the document.
  let profile := match front.profile.1, doc.info.intent with
    | some (path, _), _ => #[path]
    | none, some oi => ((Publication.localPath? file oi.profile).map (·.toString)).toArray
    | none, none => #[]
  #[file] ++ front.reads ++ (Input.bibPaths file doc).map (·.toString) ++ imgReads ++ staged ++
    faces.map FontDb.faceFile ++ parsed ++ scanned ++ declared ++ profile

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
    -- Withdrawn pictures re-elaborate first, so what is resolved below is the page that ships.
    let tool := front.doc.pictureTool.getD "lualatex"
    let declined := Boundary.linesOf tool {} front.spans.declined
    let front := { front with diags := Boundary.foldLines front.doc.allow allowAll declined front.diags }
    let failing := (Diag.resolveAll front.doc.allow allowAll (Diag.forOutputs outputs front.diags)).errors > 0
    let (faces, front) ← boundaryFaces ui file front
    let (pics, undrawn, staged) ← if failing then pure (#[], #[], #[])
      else resolvePictures ui file front.doc front.spans.images faces
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
    -- Images load before the faces settle (SVG scalars join the fallback) and before diagnostics.
    let failingNow := (Diag.resolveAll doc.allow allowAll (Diag.forOutputs outputs diags)).errors > 0
    let cache ← Engine.cache (← FontDiscovery.cacheDir)
    let convert ← svgConverter Image.PlanParams.default doc.figureConvert
    let tImg ← IO.monoMsNow
    let (imgs0, imgDiags0, imgHits, titles, imgReads0, judged0) ←
      if failingNow then pure ({}, #[], 0, #[], #[], #[])
      else loadImages file doc pics refused reqSpans.images cache convert
    let imgMs ← since tImg
    let doc := FigureAlt.titled titles doc
    -- premise: svgTitleAltChecks — a figure's title answers N0376
    let diags := FigureAlt.unanswered titles doc diags
    let mut resolved ← ui.resolve doc.allow allowAll (outputs := outputs) diags
    if resolved.errors > 0 then
      ui.accepted resolved.accepted
      ui.summary file resolved.errors (← since t0)
      return 1
    let t ← IO.monoMsNow
    -- A provisional scan serves unless the body names another font directory.
    let reuse : Option FaceScan := front.scan.filter (·.dirs == doc.fonts.dirs)
    let scan ← match reuse with
      | some s => pure s
      | none => scanFaces ui file doc.fonts
    match ← buildFontSet doc scan front.cache .settled (Layout.storeScalars imgs0) reqSpans.faces with
    | .error d =>
      -- No usable font set: fatal whatever the document accepts.
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
      ui.fontPhase names paths scan.faces.size (← since t)
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
        pure (FigureAlt.titled titles (Ir.resolveMathAlphas fs.mathAlphabets family doc2).1, spans2)
      let t ← IO.monoMsNow
      let (imgs, imgDiags, imgHits, _, imgReads, judged) ←
        if Ir.imageRequests doc == Ir.imageRequests front.doc then
          pure (imgs0, imgDiags0, imgHits, titles, imgReads0, judged0)
        else loadImages file doc pics refused reqSpans.images cache convert
      let (imgs, shapeNotes) := FigureStore.settle fs imgs
      let imgDiags := imgDiags ++ shapeNotes.map fun (src, d) =>
        DriverDiag.atImageRequest reqSpans.images src d
      let imgDiags := (imgDiags ++ PlanLoss.pictureAlts doc reqSpans.images imgs).map sourceDiag
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) imgDiags)
      unless imgs.entries.isEmpty do
        let cached := if imgHits == 0 then "" else s!", {imgHits} cached"
        let drawn := imgs.entries.filter (·.vector.isSome) |>.size
        let svgs := imgs.entries.filter (fun en => Image.isSvg (HtmlDoc.resolvedSrc en)) |>.size
        let figs := if svgs == 0 then "" else s!", {drawn} of {svgs} SVG figures drawn natively"
        ui.phase "images" s!"{imgs.entries.size} files{cached}{figs}" (imgMs + (← since t))
      let t ← IO.monoMsNow
      -- A language without patterns is unhyphenated; W0368 already named it.
      let pats := Hyphen.forTag doc.info.locale.tag
      ui.phase "hyphen" (match pats with
        | some p => s!"{p.map.size} patterns ({doc.info.locale.tag})"
        | none => s!"no patterns for '{doc.info.locale.tag}'") (← since t)
      let t ← IO.monoMsNow
      let geom := Layout.Geom.ofPage doc.page
      -- Pages are set only where something reads them: the PDF, a deck's squeeze, a page assertion.
      let readsPages := doc.asserts.any fun a => match a.kind with
        | .pages _ _ | .textInArea | .minXHeight _ => true
        | .fontsAllEmbedded | .accessibilityAA | .pdfProfile _ => false
      -- premise: paperLossChecks — an unset flow loses only its paper's losses
      let setsPages := emit.contains .pdf || readsPages || !Layout.paperLossesOnly doc
      let (out, squeezed) : Layout.Out × Array Nat := if setsPages then
          let fitted := Layout.runFitted geom fs pats doc imgs
            (frameSpans := Layout.frameSpansForPdf doc reqSpans.frames)
            (pictureSpans := Layout.pictureSpansForPdf doc reqSpans.images)
          (fitted.out, fitted.webSqueeze)
        else ({ pages := #[], diags := #[] }, #[])
      let layoutDiags := out.diags.map sourceDiag
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs) layoutDiags)
      if setsPages then ui.phase "layout" s!"{out.pages.size} pages" (← since t)
      -- An unaccepted error before the writers means no output.
      if resolved.errors > 0 then
        ui.accepted resolved.accepted
        ui.summary file resolved.errors (← since t0)
        return 1
      -- Phase 1, the plan: what to build and where, with no directory created until `publish`.
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
      -- premise: publicationInputChecks — a destination naming an input is refused
      if let some clash ← Host.runIO (PublicationPaths.overwrite destinations
          (buildInputs file front doc scan (← front.cache.readPaths) imgReads staged paths)) then
        ui.diag (DriverDiag.outputOverwritesInput clash)
        ui.summary file 1 (← since t0)
        return 1
      -- premise: publicationPathChecks — colliding destinations leave all outputs untouched
      if let some detail ← PublicationPaths.conflict destinations then
        ui.diag (DriverDiag.outputPathsConflict detail)
        ui.summary file 1 (← since t0)
        return 1
      -- Phase 2, the build in memory: every artifact's bytes exist before any is judged.
      let shipFonts := doc.fontPolicy == .embedded
      -- A slot fallen to the body face is named here, where the emitted formats are known.
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
        ((PlanLoss.ofPlan emit fs doc reqSpans.faces).map sourceDiag))
      let mut htmlBuilt : Option HtmlArtifact := none
      if emit.contains .html then
        let t ← IO.monoMsNow
        let cssMode := match css with
          | .own => HtmlDoc.CssMode.own
          | .bulma => HtmlDoc.CssMode.bulma
          | .none => HtmlDoc.CssMode.none
        -- Boundary pictures' HTML faces, native first; a faceless one the subset draws withdraws.
        let tf ← IO.monoMsNow
        -- premise: nativeFigureBuildChecks — a refused converter never runs; each loss is named
        let decl : Boundary.Refusal := if doc.figureConvert then .none else .declared
        let door ← PdfFaces.door
        let (imgs, svgDiags, unconverted, picNatives, picTally) ←
          picsToSvgNative pics imgs reqSpans.images reqSpans.fallbacks (decl := decl) (door := door)
        let (imgs, faceDiags, faceNatives, faceTally) ← imageBrowserFacesNative imgs decl door
        let tally := picTally.merge faceTally
        if tally.native + tally.lossy + tally.tool + tally.refused > 0 then
          ui.phase "faces" tally.words (← since tf)
        let faceDiags := faceDiags.map fun (src, d) => DriverDiag.atImageRequest reqSpans.images src d
        resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
          ((svgDiags ++ faceDiags).map front.prepared.sourceTriggers.attribute))
        let htmlOnly := Boundary.htmlWithdraw reqSpans.fallbacks unconverted
        let htmlDoc ← if htmlOnly.isEmpty then pure doc else do
          let t ← IO.monoMsNow
          let (d, _, _) ← elaborate ui file front.prepared front.earlier front.spliced metric
            (phases := false) (withdrawn := w.ids ++ htmlOnly) (ledger := front.ledger)
          ui.phase "withdraw" s!"{htmlOnly.size} pictures drawn by the rendered subset \
in the HTML" (← since t)
          let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
          pure (FigureAlt.titled titles (Ir.resolveMathAlphas fs.mathAlphabets family d).1)
        let hcfg : HtmlDoc.Config := {
          css := cssMode
          imgs := imgs
          fonts := if shipFonts then some fs else none
          requiredFaces := Layout.docFaceIndices fs htmlDoc
          mdHref := if emit.contains .md then twinHref mdPath doc.output.md else none
          labelMetric := Layout.labelMetric (Layout.Geom.ofPage doc.page) fs
          footBox := fun n band => some (Layout.footBandBox (Layout.Geom.ofPage doc.page) fs imgs n band)
          blockTitleRule := Layout.blockTitleRule (Layout.Geom.ofPage doc.page) fs doc.styles
          blockLastBelow := Layout.blockLastBelow (Layout.Geom.ofPage doc.page) fs
          cancelMetric := fun measures ss st spec body value =>
            Layout.cancelMetric (Layout.Geom.ofPage doc.page) fs ss st spec body value (some measures)
          mathEm := fun measures ss st =>
            Layout.mathEm (Layout.Geom.ofPage doc.page) fs ss st (some measures)
          mathTextEm := fun measures ss st =>
            Layout.mathTextEm (Layout.Geom.ofPage doc.page) fs ss st (some measures)
          tableFit := fun avail cols padL padR rows spans =>
            let fit := Layout.tableFit (Layout.Geom.ofPage htmlDoc.page) fs imgs
              (Layout.tableLength none htmlDoc.preambleFace "tabcolsep") avail cols padL padR rows
              spans
            (fit.step, fit.overhang > 0)
        }
        let htmlDoc := { htmlDoc with body := Ir.squeezeFrames htmlDoc.body squeezed }
        let (result, hdiags) ← prepareHtml file hcfg htmlDoc (picNatives ++ faceNatives ++ judged)
          (mathBoundary := ui.cfg.mathBoundary)
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
        let names := twinBibNames file mdPath doc
        let md := MarkdownDoc.emit doc fun n => ((names.find? (·.1 == n)).map (·.2)).getD n
        ui.phase "markdown" s!"{md.utf8ByteSize} bytes" (← since t)
        mdBuilt := some md
      let mut pdfBuilt : Option ByteArray := none
      if emit.contains .pdf then
        let t ← IO.monoMsNow
        -- Font programs and content streams deflate through the content-hash cache.
        let used := Pdf.usedAll fs out.pages imgs.shaped
        let keep := Pdf.keepOf used
        let programs := Pdf.facePrograms fs used
        let fs := { fs with zdata := ← Compression.fontZdata cache fs.fonts.size keep programs }
        let tree := Struct.ofDoc (Layout.pdfView doc)
        -- The output profile's press prints the engine's own colours in every operator.
        let (profile, profileDiags) := front.profile
        let imgs := { imgs with profile := profile.map (·.2) }
        let ops := Pdf.pageOps geom fs out.pages imgs tree keep
        let streams ← Compression.pageStreams cache (ops.map fun o => (Pdf.render o).toUTF8)
        let imgs := { imgs with
          formZ := ← Compression.formZdata cache (Pdf.copiedFormContents imgs out.pages) }
        -- A claimed file's outline carries no link out of the file, PDF/X admitting no action.
        let claimOutline := if doc.info.pdfx.isSome then out.outline.filter (·.url.isNone)
          else out.outline
        let links := Pdf.linkCount geom out.pages + (out.outline.size - claimOutline.size)
        let written := (Pdf.writeChecked geom fs out.pages doc.info imgs claimOutline streams tree ops
          programs).bind fun pdf =>
            pdfxClaim doc.info pdf links fun info =>
            Pdf.writeChecked geom fs out.pages info imgs out.outline streams tree ops programs
        match written with
        | .error error =>
          ui.diag (DriverDiag.pdfWriteRefused error)
          ui.accepted resolved.accepted
          ui.summary file 1 (← since t0)
          return 1
        | .ok (pdf, claimDiags) =>
          resolved := resolved.append
            (← ui.resolve doc.allow allowAll (outputs := outputs)
              (profileDiags ++ claimLosses profileDiags claimDiags))
          ui.phase "pdf" s!"{pdf.size} bytes" (← since t)
          pdfBuilt := some pdf
      -- Phase 3: census, gate, publish; assertions judge the built bytes before any write.
      let t ← IO.monoMsNow
      -- Every emitted artifact carries its fonts: the PDF by its census, the HTML by its faces.
      let readsPdf := doc.asserts.any fun a => match a.kind with
        | .fontsAllEmbedded | .pdfProfile _ => true
        | .pages _ _ | .textInArea | .minXHeight _ | .accessibilityAA => false
      let pdfCensus : Option (Except String PdfCensus.Census) :=
        if readsPdf then pdfBuilt.map PdfCensus.census else none
      let fontsEmbedded : Bool :=
        if doc.asserts.any (·.kind == .fontsAllEmbedded) then
          (pdfCensus.all fun c => match c with
            | .ok c => c.allEmbedded
            | .error _ => false) &&
          htmlBuilt.all fun _ => shipFonts
        else true
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
      -- Accepting a warning quiets the report, never the fact.
      let shipped := if doc.asserts.any (·.kind == .accessibilityAA) then
          let a11y := if pdfBuilt.isSome then
              Check.pdfA11ySummary doc (diags ++ imgDiags) geom fs out
            else Check.a11ySummary doc (diags ++ imgDiags)
          { shipped with a11y }
        else shipped
      let failures := Check.all shipped doc.asserts
      -- An assertion about bytes this run does not emit fails rather than passing vacuously.
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
      -- An `\allow` that never fired warns.
      resolved := resolved.append (← ui.resolve doc.allow allowAll (outputs := outputs)
        ((Diag.unfired doc.allow resolved.fired).map DriverDiag.allowUnfired))
      ui.accepted resolved.accepted
      ui.done file (String.intercalate ", " written.toList)
        (if setsPages then some out.pages.size else none) (← since t0)
        resolved.notes
      if ui.cfg.werror && resolved.warnings > 0 then
        ui.werror file resolved.warnings (← since t0)
      return exitFor 0 0 resolved.warnings ui.cfg.werror

def dump (ui : Ui) (file : String) : IO UInt32 := do
  match ← frontend ui file with
  | none => return 1
  | some front =>
    IO.print (Ir.dump front.doc front.diags)
    return (if countErrors front.diags > 0 then 1 else 0)

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
    IO.println (Hyphen.marked pats w)
  return 0

/-- Rebuild whenever the source's mtime changes, polled every 200 ms, each rebuild
printing its summary with the peak reset at its start. -/
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
      let statesPeak ← RunCost.resetPeak
      discard <| build { (← Ui.mk' cfg) with statesPeak } file
  return 0

public def main (argv : List String) : IO UInt32 := do
  -- The engine's identity is the image this process started as.
  discard Engine.engineId
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
      -- premise: outputNameChecks — an output name no extension ends is one E0006, exit 3
      if let some o := cfg.output then
        unless o.endsWith "/" || (← (System.FilePath.mk o).isDir) ||
            (emitOfPath o).isSome do
          let ui ← Ui.mk' cfg
          ui.diag (DriverDiag.outputFormatUnknown o)
          ui.summary file 1 0
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
      -- `fonts`: one family per line, its installed math companion indented beneath.
      let faces ← FontDiscovery.scan (cfg.fontDirs.toList ++ (← texFontDirs))
      let load (path : String) : IO (Option Font) := do
        return ((← FontDiscovery.faceBytes path) >>= Font.parse).toOption
      for fam in FontDb.families faces do
        IO.println fam
        if let some (row, cFace) := FontDb.pickCompanion faces fam then
          let metrics ← do
            let bodyPath := (FontDb.resolve faces fam {}).map (·.1.path)
            match ← bodyPath.mapM load, ← load cFace.path with
            | some (some b), some c =>
              let perMille (f : Font) (v : Nat) : Nat := v * 1000 / f.unitsPerEm
              let xh := s!"x-height {perMille b b.xHeightOptical} vs \
{perMille c c.xHeightOptical}"
              let stem (f : Font) : Option Nat := do
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
      for th in Theme.builtin do
        IO.println th.name
      return 0

end LeanTex.Cli.Driver
