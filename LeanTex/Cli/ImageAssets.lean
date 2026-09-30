import LeanTex.Core.Image
import LeanTex.Core.FontDb
import LeanTex.Version
import LeanTex.Cli.ConvCache
import LeanTex.Cli.ToolProbe

/-! Vector image IO. Captured SVG bytes remain the browser source. Fresh
conversions return bytes; only the driver decides when to publish them.

Every host conversion — `xmllint`'s support boundary, `rsvg-convert`'s
static reading, `pdftocairo`'s page — runs under a wall-clock budget and its
own process group, so a runaway tool cannot hang the build (`runBounded`
kills the group with `SIGTERM`, then `SIGKILL` after a grace window). Each
*completed* answer is cached beside the font and picture caches, keyed by
the source's content, the operation's recipe, the tool's version and the
engine version (`ConvCache`): a converted output serves, the tool's own
refusal replays word for word, and an attempt the tool never finished — a
budget kill, a failed spawn, a nonzero exit with no log, an empty or
unreadable output — is not remembered, so the next build retries it. Writes
are staged under a `.part` name and renamed into place, so a killed writer
never leaves a valid-looking slot. The policy is all values in `ConvCache`;
here is the spawn, the stat, the temp directory and the atomic rename. -/

namespace LeanTex.Cli.ImageAssets

open LeanTex.Core

/-- Host conversions are quick — a well-formed figure renders in
milliseconds — so a ceiling well above that catches only a hang, never a
slow success. -/
def convBudgetMs : Nat := 60000

/-- After the budget, the group gets `SIGTERM`; this long to exit cleanly,
then `SIGKILL`. -/
def convGraceMs : Nat := 2000

/-- The normalized host-tool recipe behind browser vector faces, built from
the same `ConvCache.Op` recipes the cache keys on — so a recipe change moves
this record and every cached slot together, and the browser oracle can never
record a command the runtime does not run. The trailing page conversion is
shown with a `<page>` placeholder (the browser oracle records the template,
not one page's slot). -/
def browserFaceContract : String :=
  let input := System.FilePath.mk "<input>"
  let output := System.FilePath.mk "<output>"
  String.intercalate "\n" [
    ConvCache.Op.recipe .validate,
    ConvCache.Op.recipe .svgPdf,
    ConvCache.Op.recipe .svgPoster,
    ConvCache.commandText "pdftocairo" (ConvCache.pdfSvgArgs "<page>" input output)]

/-! ## The bounded process group

Every tool runs here. The child is its own session and process group
(`setsid`), so the budget kill reaches whatever it spawned, not just the
child; `stdout`/`stderr` are drained on dedicated tasks so a chatty tool
cannot fill a pipe buffer and deadlock the poll loop. The ending is a
`PicCache.Ran`, and what the tool wrote comes back beside it. -/

/-- One tool run's result: how it ended, and what it wrote to each stream. -/
structure Ended where
  ran : PicCache.Ran
  out : String
  err : String

/-- The last words of a tool's stderr: the trailing non-empty lines, so a
refusal is diagnosable and a cached refusal replays the tool's own words. -/
def errTail (s : String) : String :=
  let lines := (s.splitOn "\n").filterMap fun l =>
    let t := l.trimAscii.toString
    if t.isEmpty then none else some t
  String.intercalate " · " (lines.reverse.take 3).reverse

/-- The stderr as a `PicCache.Log`: absent when the tool wrote nothing, so a
nonzero exit that left no log at all reads as a machine fact, not a verdict. -/
def logOf (err : String) : PicCache.Log :=
  let t := errTail err
  if t.isEmpty then .absent else .says t

/-- The most of a tool's stream the build holds in memory. Conversions say
little — a version banner, a short error — so this ceiling is never reached
by a well-behaved tool; a tool spewing past it is still drained (so it never
blocks on a full pipe) but only this many bytes are kept, bounding the
build's footprint against a runaway. -/
def maxCaptureBytes : Nat := 1 <<< 20

/-- The read chunk, and the finite chunk ceiling that makes the drain
loop total: `maxDrainChunks` 64 KiB reads bound one drain, after which the
stream is left for the budget kill to close rather than read forever. -/
def captureChunk : Nat := 65536
def maxDrainChunks : Nat := 1 <<< 20

/-- Decode captured bytes, trimming up to three trailing bytes so a cap that
fell mid-codepoint still yields valid text rather than raising. -/
private def decodeCapped (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => match String.fromUTF8? (b.extract 0 (b.size - 1)) with
    | some s => s
    | none => match String.fromUTF8? (b.extract 0 (b.size - 2)) with
      | some s => s
      | none => (String.fromUTF8? (b.extract 0 (b.size - 3))).getD ""

/-- Read a child stream to EOF, keeping at most `maxCaptureBytes` and
draining the rest. The loop is bounded by `maxDrainChunks`, so it is total
and a stream longer than the ceiling is abandoned to the budget kill rather
than read without end; the captured prefix is decoded losslessly. -/
def captureCapped (h : IO.FS.Handle) : IO String := do
  let mut acc : ByteArray := .empty
  let mut capped := false
  for _ in [0:maxDrainChunks] do
    let chunk ← h.read captureChunk.toUSize
    if chunk.isEmpty then break
    unless capped do
      acc := acc ++ chunk
      if acc.size ≥ maxCaptureBytes then
        acc := acc.extract 0 maxCaptureBytes
        capped := true
  return decodeCapped acc

/-- Send `signal` to the whole process group led by `pid` (its own group
under `setsid`, so the negative-pid target reaches every descendant). A
failure to spawn or reap `kill` is swallowed: an unkillable group is a
machine fact the bounded drains still survive, never a crash. -/
private def signalGroup (signal : String) (pid : UInt32) : IO Unit := do
  try
    let args : IO.Process.SpawnArgs :=
      { cmd := "kill", args := #["-" ++ signal, "-" ++ toString pid],
        stdout := .null, stderr := .null, stdin := .null }
    let child ← IO.Process.spawn args
    let _ ← (child.wait).toBaseIO
  catch _ => pure ()

/-- Run one tool under a wall-clock budget in its own process group. On
overrun the whole group gets `SIGTERM`, then — after the grace window, and
always, even if the leader has since exited — `SIGKILL`, so no descendant
that inherited the pipes outlives the budget. Both streams are drained on
dedicated tasks, each capped in memory (`captureCapped`) and each awaited
under a bounded wait, so a descendant holding a pipe open can neither fill
it nor hang the build. A spawn that raised is `.unstarted`; a kill or wait
that raised is swallowed and leaves the ending inconclusive. -/
def runBounded (tool : String) (args : Array String) (cwd : System.FilePath)
    (budgetMs : Nat := convBudgetMs) (graceMs : Nat := convGraceMs) : IO Ended := do
  let spawned ← (do
    let args : IO.Process.SpawnArgs :=
      { cmd := tool, args := args, cwd := cwd, setsid := true,
        stdout := .piped, stderr := .piped, stdin := .null }
    IO.Process.spawn args).toBaseIO
  match spawned with
  | .error e => return { ran := .unstarted (toString e), out := "", err := "" }
  | .ok child =>
    let outT ← IO.asTask (captureCapped child.stdout) Task.Priority.dedicated
    let errT ← IO.asTask (captureCapped child.stderr) Task.Priority.dedicated
    let mut ran : PicCache.Ran := .overran (budgetMs / 1000)
    let mut done := false
    for _ in [0:budgetMs / 50 + 1] do
      unless done do
        match ← (child.tryWait).toBaseIO with
        | .ok (some code) => ran := .exited code.toNat; done := true
        | _ => IO.sleep 50
    unless done do
      -- Overran: TERM the whole group, wait the grace window, then always
      -- KILL the whole group — even if the leader has since exited — so a
      -- descendant that inherited the pipes cannot outlive the budget.
      signalGroup "TERM" child.pid
      for _ in [0:graceMs / 50 + 1] do
        unless done do
          match ← (child.tryWait).toBaseIO with
          | .ok (some _) => done := true
          | _ => IO.sleep 50
      signalGroup "KILL" child.pid
      let _ ← (child.wait).toBaseIO
    -- Bound the drains: once the group is dead its pipe write-ends close and
    -- each `captureCapped` returns, but a descendant the kill could not reach
    -- must not hang the build, so each task is awaited under a bounded wait
    -- and abandoned to "" if it does not settle in time.
    let drain (t : Task (Except IO.Error String)) : IO String := do
      for _ in [0:budgetMs / 50 + graceMs / 50 + 2] do
        unless (← IO.hasFinished t) do IO.sleep 50
      if ← IO.hasFinished t then return (t.get).toOption.getD "" else return ""
    let out ← drain outT
    let err ← drain errT
    return { ran, out, err }

/-! ## The cache

Beside the font and picture caches, one directory of slots. A conversion's
tool version is asked at most once per tool binary (`ToolProbe.identify`),
and its slot is named by the source's content, the operation's recipe, the
tool version and the engine version. A converted output serves; a remembered
refusal replays; otherwise the tool runs and its completed answer is
recorded. -/

/-- The conversion cache directory, beside the others; `none` when no cache
root is available, in which case conversions run uncached but still
bounded. -/
def convDir : IO (Option System.FilePath) := do
  let some root ← FontDb.cacheDir | return none
  let d := root / "convs"
  IO.FS.createDirAll d
  return some d

/-- The version flag each conversion tool answers to. `pdftocairo` has no
`--version`; `-v` prints its banner. -/
def versionArgs (tool : String) : Array String :=
  if tool == "pdftocairo" then #["-v"] else #["--version"]

/-- Ask a conversion tool who it is. Unlike the TeX boundary, these tools
print their banner to whichever stream they please — `rsvg-convert` to
stdout, `xmllint` and `pdftocairo` to stderr — so the first non-empty line
of stdout is taken, else stderr. Only a clean exit names a version
(`PicCache.probed`); a missing tool still reaches `exec` and comes back
nonzero. -/
def probeConvVersion (tool : String) : IO PicCache.Tool := do
  let (ran, said) ← try
      let out ← IO.Process.output { cmd := tool, args := versionArgs tool }
      let pick := fun (s : String) => ((s.splitOn "\n").headD "").trimAscii.toString
      let o := pick out.stdout
      pure (PicCache.Ran.exited out.exitCode.toNat, if o.isEmpty then pick out.stderr else o)
    catch e => pure (PicCache.Ran.unstarted (toString e), "")
  return PicCache.probed ran said

/-- The tool's identity, asked once per tool binary against a stat-only
witness and remembered beside the slots (`ToolProbe`). -/
def toolVersion (dir : System.FilePath) (tool : String) : IO PicCache.Tool := do
  let stamp ← ToolProbe.witness tool
  ToolProbe.identify (dir / PicCache.versionName tool) stamp (probeConvVersion tool)

/-- A fresh temp-name nonce: the monotonic clock and a random draw. Two
writers to one slot — the output writer and the refusal writer, or two
concurrent builds converting the same figure — draw different nonces, so
they never share a `.part`, and a writer killed mid-write leaves a temp
named after nobody that no other writer renames into place. -/
private def freshNonce : IO String := do
  return s!"{← IO.monoNanosNow}-{← IO.rand 0 (2 ^ 31)}"

/-- Read a warmed byte slot only when it holds usable bytes — a readable,
non-empty file. An empty or unreadable slot (a truncated file, or a half-written
byte left by a writer that died before atomic staging) is refused as `none`,
so the caller re-runs the tool rather than serving garbage. -/
private def readGoodOutput (p : System.FilePath) : IO (Option ByteArray) := do
  if ← p.pathExists then
    match ← (IO.FS.readBinFile p).toBaseIO with
    | .ok b => return if b.isEmpty then none else some b
    | .error _ => return none
  else return none

/-- Read a warmed text slot (a remembered refusal, or the validation
sentinel) only when it holds non-empty, readable text; an empty or
unreadable slot is refused as `none` and re-run. -/
private def readGoodText (p : System.FilePath) : IO (Option String) := do
  if ← p.pathExists then
    match ← (IO.FS.readFile p).toBaseIO with
    | .ok t => return if t.isEmpty then none else some t
    | .error _ => return none
  else return none

/-- Write bytes to their slot atomically: build a per-writer `.part`, then
rename it into place. A killed writer leaves only its uniquely-named
`.part`, never a slot that serves; the rename is the only step that makes
bytes visible at the served name. -/
private def atomicWriteBin (dir : System.FilePath) (srcKey variant : String)
    (final : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let part := dir / ConvCache.partName srcKey variant (← freshNonce)
  IO.FS.writeBinFile part bytes
  IO.FS.rename part final

/-- Write a remembered refusal atomically, the same way, under a per-writer
`.part`. -/
private def atomicWriteText (dir : System.FilePath) (srcKey variant : String)
    (final : System.FilePath) (text : String) : IO Unit := do
  let part := dir / ConvCache.partName srcKey variant (← freshNonce)
  IO.FS.writeFile part text
  IO.FS.rename part final

/-- The bytes one byte-producing conversion writes: run it in a temp
directory under the budget, read back the output, and read the ending as a
`ConvCache.convOutcome` — a clean exit with a non-empty readable output is
the conversion, a nonzero exit with a log is the tool's own refusal, and
anything else is inconclusive. Returns the outcome and, on success, the
bytes. -/
private def runByteConv (bytes : ByteArray)
    (inExt outExt tool : String)
    (args : System.FilePath → System.FilePath → Array String) :
    IO (PicCache.Outcome × Option ByteArray) := do
  IO.FS.withTempDir fun tdir => do
    let input := tdir / ("source." ++ inExt)
    let output := tdir / ("face." ++ outExt)
    IO.FS.writeBinFile input bytes
    let e ← runBounded tool (args input output) tdir
    let bytes? ← if ← output.pathExists then
        pure (← (IO.FS.readBinFile output).toBaseIO).toOption
      else pure none
    let readable := match bytes? with | some b => !b.isEmpty | none => false
    let outcome := ConvCache.convOutcome e.ran readable (logOf e.err)
    return (outcome, if readable then bytes? else none)

/-- One byte-producing host conversion, through the cache and the budget.
The op alone determines the tool, the extensions and the arguments through
`ConvCache.Op.byteSpec`, so the runtime cannot key one op and run another.
The tool's version keys the slot; if the tool cannot say who it is, the
conversion is an error and nothing is cached. A converted output serves, a
remembered refusal replays word for word, and an attempt that never finished
leaves the slot untouched so the next build retries. -/
def byteConv (op : ConvCache.Op) (bytes : ByteArray) : IO (Except String ByteArray) := do
  match op.byteSpec with
  | none => return .error "internal: a validation op has no byte conversion"
  | some (tool, inExt, outExt, args) =>
  -- The typed precondition, before any cache lookup or tool run: a PDF handed
  -- to a host renderer must embed every font, or the host would substitute
  -- glyphs from its own fonts and the face would depend on the machine. The
  -- refusal is deterministic in the bytes, so it needs no tool and is never
  -- cached, and it is what keeps the slot key free of a host-font fingerprint.
  -- premise: LeanTex.Cli.ConvCache.pdfSelfContained_ok_exact — the verdict is
  -- exactly the read-side census's font-embedding fact, a function of the bytes.
  match (if op.readsPdf then ConvCache.pdfSelfContained bytes else .ok ()) with
  | .error e => return .error e
  | .ok () =>
  match ← convDir with
  | none =>
    -- No cache root: run uncached, still bounded.
    let (outcome, bytes?) ← runByteConv bytes inExt outExt tool args
    match outcome with
    | .drawn => match bytes? with
        | some b => return .ok b
        | none => return .error s!"{tool} produced no usable output"
    | .refused says => return .error says
    | .inconclusive says => return .error says
  | some dir =>
    match ← toolVersion dir tool with
    | .absent why => return .error s!"{tool} is unavailable: {why}"
    | .present version =>
      let srcKey := Flate.contentKey bytes
      let variant := ConvCache.variant op version LeanTex.version
      let outP := dir / ConvCache.outName srcKey variant
      let failP := dir / ConvCache.failName srcKey variant
      -- The serve/replay/run decision is the shared `PicCache.step`, read
      -- over usable slots only: an empty or unreadable warmed output is not
      -- a hit, so a truncated slot re-runs rather than serving garbage.
      let good? ← readGoodOutput outP
      let refusal? ← readGoodText failP
      match PicCache.step good?.isSome refusal?, good? with
      | .serve, some b => return .ok b
      | .replay says, _ => return .error says
      | _, _ =>
      let (outcome, bytes?) ← runByteConv bytes inExt outExt tool args
      match outcome with
      | .drawn => match bytes? with
          | some b =>
            try atomicWriteBin dir srcKey variant outP b catch _ => pure ()
            return .ok b
          | none => return .error s!"{tool} produced no usable output"
      | .refused says =>
        -- `remembers` governs what is persisted: only the tool's own refusal.
        match PicCache.remembers outcome with
        | some _ => try atomicWriteText dir srcKey variant failP says catch _ => pure ()
        | none => pure ()
        return .error says
      | .inconclusive says => return .error says

/-! ## The support boundary

`xmllint` guards which SVGs `rsvg-convert` may read. Its "no" is a verdict —
the boundary's own refusal, whose descriptive words are cached and replayed —
so it is a completed answer like any other, but its refusal lives in the
tool's stdout, not its exit code, so it is read here rather than through
`convOutcome`. The boundary is evaluated over libxml's parsed XML; the
support subset is `ConvCache.supportedSvg`. -/

private def dtdEvent (raw : String) : Bool :=
  let event := raw.trimAscii.toString
  ["internalSubset(", "externalSubset(", "entityDecl("].any fun marker =>
    (event.splitOn marker).length > 1

/-- The SAX pass read as an outcome: a clean parse with no DTD continues; a
DTD or entity declaration is the boundary's refusal; an incomplete parse or
a nonzero exit that left a log is the tool's own no; everything else is
inconclusive. -/
def saxStage (e : Ended) : PicCache.Outcome :=
  match e.ran with
  | .exited 0 =>
    let lines := e.out.splitOn "\n"
    if lines.any dtdEvent then
      .refused "SVG resource boundary refuses DTDs and entity declarations"
    else if lines.any (·.trimAscii.toString == "SAX.startDocument()") &&
        lines.any (·.trimAscii.toString == "SAX.endDocument()") then .drawn
    else .inconclusive "SVG validation received no complete XML parse"
  | .exited c =>
    match logOf e.err with
    | .absent => .inconclusive s!"exit code {c}"
    | .says t => .refused t
  | .overran s => .inconclusive s!"no result within {s} s; killed"
  | .unstarted er => .inconclusive er

/-- The XPath boundary read as an outcome: `true` is support; `false` is the
boundary's refusal, carrying the message that names what it requires; a
nonzero exit with a log is the tool's own no; everything else is
inconclusive. -/
def xpathStage (e : Ended) : PicCache.Outcome :=
  match e.ran with
  | .exited 0 =>
    if e.out.trimAscii.toString == "true" then .drawn
    else .refused "SVG resource boundary requires fragment-only references and plain CSS; paint servers must be exactly url(#id), without fallback syntax; DTDs, scripts, foreign objects, base URIs, CSS functions/escapes/at-rules and animated resource/style assignments are unsupported"
  | .exited c =>
    match logOf e.err with
    | .absent => .inconclusive s!"exit code {c}"
    | .says t => .refused t
  | .overran s => .inconclusive s!"no result within {s} s; killed"
  | .unstarted er => .inconclusive er

/-- Run the two-pass boundary in a temp directory under the budget, and
compose the stages: the SAX pass, then — only if it passed — the XPath
boundary (`ConvCache.seq`). -/
private def runValidate (bytes : ByteArray) : IO PicCache.Outcome := do
  IO.FS.withTempDir fun tdir => do
    let input := tdir / "source.svg"
    IO.FS.writeBinFile input bytes
    let sax ← runBounded "xmllint" (ConvCache.saxArgs input) tdir
    match saxStage sax with
    | .drawn =>
      let xp ← runBounded "xmllint" (ConvCache.xpathArgs input) tdir
      return ConvCache.seq .drawn (xpathStage xp)
    | other => return other

/-- Validate captured SVG bytes through the cache. Success writes a sentinel
slot so the next build serves without a tool; the boundary's refusal is
remembered and replayed with its own words; an inconclusive attempt is not
cached. -/
def checkSvg (bytes : ByteArray) : IO (Except String Unit) := do
  match ← convDir with
  | none =>
    match ← runValidate bytes with
    | .drawn => return .ok ()
    | .refused says => return .error says
    | .inconclusive says => return .error says
  | some dir =>
    match ← toolVersion dir "xmllint" with
    | .absent why => return .error s!"xmllint is unavailable: {why}"
    | .present version =>
      let srcKey := Flate.contentKey bytes
      let variant := ConvCache.variant .validate version LeanTex.version
      let outP := dir / ConvCache.outName srcKey variant
      let failP := dir / ConvCache.failName srcKey variant
      let ok? ← readGoodText outP
      let refusal? ← readGoodText failP
      match PicCache.step ok?.isSome refusal? with
      | .serve => return .ok ()
      | .replay says => return .error says
      | .run =>
      match ← runValidate bytes with
      | .drawn =>
        try atomicWriteText dir srcKey variant outP "ok" catch _ => pure ()
        return .ok ()
      | .refused says =>
        match PicCache.remembers (.refused says) with
        | some _ => try atomicWriteText dir srcKey variant failP says catch _ => pure ()
        | none => pure ()
        return .error says
      | .inconclusive says => return .error says

/-- Validate captured SVG bytes before accepting a browser companion, then
read their static PDF plan. An error lets the caller fall back to converting
its selected PDF page. Requires the installed xmllint and librsvg; either
failing is an error value. -/
def validateSvg (bytes : ByteArray) (params : Image.PlanParams := .default) :
    IO (Except String Image.Plan) := do
  match ← checkSvg bytes with
  | .error e => return .error e
  | .ok () =>
    let pdf ← byteConv .svgPdf bytes
    return pdf >>= fun b => Image.probe b >>= Image.plan params

/-- librsvg's static vector reading of a self-contained SVG. The caller
keeps the captured SVG bytes for the browser, including SMIL animation. -/
def svgPlan (params : Image.PlanParams) (bytes : ByteArray)
    (page : PdfRead.PageSelection := .first) :
    IO (Except String Image.Plan) := do
  if page != .first && page != .number 1 then
    return .error "SVG conversion supplies a static first frame; the selected poster requires a PDF frame sequence"
  validateSvg bytes params

/-- Cairo's static SVG face for print and reduced motion. Use `pdfSvg` on
the selected page instead when a companion PDF supplies a chosen frame. -/
def svgPoster (bytes : ByteArray) : IO (Except String ByteArray) := do
  match ← checkSvg bytes with
  | .error e => return .error e
  | .ok () => byteConv .svgPoster bytes

/-- Poppler reads the physical page selected by the same page-tree
traversal as the native importer, including `last`; `/Count` is never a
substitute for that traversal. -/
def pdfSvg (bytes : ByteArray) (page : PdfRead.PageSelection) :
    IO (Except String ByteArray) := do
  match PdfRead.pageNumber bytes page with
  | .error e => return .error e
  | .ok n =>
    byteConv (.pdfPage n) bytes

/-- The static vector face of a boundary picture's own single-page PDF: one
`pdftocairo` conversion of its first page, through the same cache and budget
as every other. -/
def picFace (bytes : ByteArray) : IO (Except String ByteArray) :=
  byteConv .picFace bytes

end LeanTex.Cli.ImageAssets
