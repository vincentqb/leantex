import LeanTex.Cli.BrowserFaces
import Tests.Support

namespace Tests.BrowserFaceBatch

open LeanTex.Core LeanTex.Cli

private def capturedPdf (tag : String) : ByteArray :=
  svgCanvasPdf ++ ("\n% batch-id:" ++ tag ++ "\n").toUTF8

private def capturedSvg (tag : String) : ByteArray :=
  svgDocument ("<!--batch-id:" ++ tag ++ " --><path d=\"M0 0L20 20\"/>")

private def pdfEntry (src tag : String) (page : PdfRead.PageSelection := .first)
    (companion : Option ByteArray := none) : IO Image.Loaded := do
  let source := capturedPdf tag
  let req : Image.Request := { src, page, animated := companion.isSome }
  let .ok (info, canvas) := Image.decodeRequest .default source req |
    throw <| IO.userError "the browser batch fixture did not decode"
  return {
    toRequest := req, info := some info, canvasSize := canvas
    source := some source, companion }

private def entries : IO (Array Image.Loaded) := do
  let a ← pdfEntry "a.pdf" "a"
  let b ← pdfEntry "b.pdf" "b" .last (some (capturedSvg "shared"))
  let c ← pdfEntry "c.pdf" "c" .first (some (capturedSvg "shared"))
  let svg : Image.Loaded := { a with
    src := "moving.svg", source := some (capturedSvg "moving")
    webSvg := some (capturedSvg "moving") }
  let fallback ← pdfEntry "fallback.pdf" "fallback" .first (some (capturedSvg "bad"))
  let failed ← pdfEntry "failed.pdf" "failed" .first (some (capturedSvg "unused"))
  let fallbackAgain ← pdfEntry "fallback-again.pdf" "fallback-again" .first
    (some (capturedSvg "bad"))
  return #[a, b, c, svg,
    { a with src := "alias-a.pdf", page := .number 1 },
    { b with src := "alias-b.pdf", page := .number 2 },
    { svg with src := "alias-moving.svg", page := .number 1 },
    { svg with page := .last }, fallback, failed,
    { a with src := "unloaded.pdf", info := none },
    { a with src := "raster.png", info := some { pxW := 4, pxH := 5 } },
    { a with src := Ir.picSrcPrefix ++ "batch-owned-picture" },
    { svg with src := "missing.svg", source := none, webSvg := none },
    { a with
      src := "broken.pdf", source := some "broken PDF".toUTF8
      webSvg := some (capturedSvg "stale"), posterSvg := some (capturedSvg "stale") },
    { svg with
      src := "captured-web.svg", source := none
      webSvg := some (capturedSvg "web-only") }, fallbackAgain]

private def sameFaces (a b : Image.Loaded) : Bool :=
  a.toRequest == b.toRequest && a.href == b.href &&
    a.source == b.source && a.companion == b.companion &&
    a.webSvg == b.webSvg && a.posterSvg == b.posterSvg && a.webError == b.webError &&
    a.canvasSize == b.canvasSize && a.size? == b.size?

private def readLines (path : System.FilePath) : IO (List String) := do
  return ((← (IO.FS.readFile path).toBaseIO).toOption.getD "").splitOn "\n"
    |>.filter (!·.isEmpty)

private def answerCount (dir : System.FilePath) : IO Nat := do
  let cache ← (dir / "cache" / "leantex" / "convs").readDir.toBaseIO
  return ((cache.toOption.getD #[]).filter (·.fileName.endsWith ".answer")).size

/-- The exit of a run the host denied a tool identity: its census is not
judged, and the suite runs it again. -/
private def deniedExit : UInt32 := 2

/-- The limit whose first run's xmllint answers its first version probe
past the probe's budget. -/
private def slowProbeLimit : Nat := 4

/-- Called in a child with its own PATH and cache, so the suite never mutates
process-global environment while other IO tests may be running.

Tool identity rests on spawns held to wall-clock budgets (the PATH lookup,
the version probe); one answered past its budget identifies no tool, so that
conversion runs uncached by design and the census would count the host's
speed as a sharing failure. The census is judged only when every cold call
recorded its answer and no warm pass converted without adding a slot: every
other contract is judged on every run. -/
def runChild (args : List String) : IO UInt32 := do
  let limit := (args.headD "4").toNat?.getD 4
  let some root ← IO.getEnv "LEANTEX_FACE_BATCH_ROOT" |
    throw <| IO.userError "missing isolated browser batch root"
  let dir : System.FilePath := root
  let ref ← IO.mkRef ([] : List String)
  let t := check ref
  let input ← entries
  let actual ← BrowserFaces.prepareAll input limit
  let calls ← readLines (dir / "calls")
  let recorded ← answerCount dir
  let identified := calls.length == recorded
  let events ← readLines (dir / "events")
  let mut active := 0
  let mut peak := 0
  let mut balanced := true
  for event in events do
    if event.startsWith "+ " then
      active := active + 1
      peak := max peak active
    else if event.startsWith "- " then
      balanced := balanced && active > 0
      active := active - 1
  t "browser batch: bounded converters all finish before returning"
    (balanced && active == 0 && peak ≤ max 1 limit &&
      (← (dir / "active").readDir).isEmpty)
  if limit > 1 then
    t "browser batch: independent converters overlap and finish out of order"
      (peak ≥ 2 && !(← (dir / "timeout").pathExists) &&
        events.idxOf "- pdf-page-2:b" < events.idxOf "- pdf-page-1:a")
  t "browser batch: equal bytes never convert concurrently"
    (!(← (dir / "collision").pathExists))
  t "browser batch: all primary work finishes before companion validation"
    (!(← (dir / "early-companion").pathExists))
  if identified then
    for key in ["pdf-page-1:a", "pdf-page-2:b", "pdf-page-1:c",
        "pdf-page-1:fallback", "pdf-page-1:failed", "pdf-page-1:fallback-again",
        "svg-poster:web-only", "validate:shared", "validate:bad"] do
      t s!"browser batch: one cold attempt for {key}" (calls.count key == 1)
    t "browser batch: equivalent SVG page spellings share their answer"
      (calls.count "svg-poster:moving" == 2)
    t "browser batch: only eligible primary/companion conversions run" (calls.length == 11)
  t "browser batch: a valid companion keeps the captured animation and poster"
    (actual[1]!.webSvg == some (capturedSvg "shared") && actual[1]!.posterSvg.isSome)
  t "browser batch: a refused companion falls back to the selected static face"
    (actual[8]!.webSvg.isSome && actual[8]!.posterSvg.isNone && actual[8]!.webError.isNone)
  t "browser batch: primary failure clears payloads and skips the companion"
    (actual[9]!.webError.isSome && actual[9]!.webSvg.isNone &&
      actual[9]!.posterSvg.isNone && !calls.contains "validate:unused")
  t "browser batch: missing captured SVG retains its existing refusal"
    (actual[13]!.webError == some "the SVG source has no captured bytes")
  t "browser batch: a failed new source cannot publish old converted bytes"
    (actual[14]!.webError.isSome && actual[14]!.webSvg.isNone && actual[14]!.posterSvg.isNone)
  for i in [10, 11, 12] do
    t s!"browser batch: keep entry {i} is unchanged" (sameFaces actual[i]! input[i]!)
  let serial ← input.mapM BrowserFaces.prepare
  t "browser batch: result order, captured sources, native sizes and faces match serial preparation"
    (actual.size == serial.size && (actual.zip serial).all (fun (a, b) => sameFaces a b))
  let again ← BrowserFaces.prepareAll actual limit
  t "browser batch: repeated preparation preserves published assets"
    (HtmlDoc.imageAssets { entries := again } == HtmlDoc.imageAssets { entries := actual })
  let warm := (← readLines (dir / "calls")).drop calls.length
  let judged := identified && (warm.isEmpty || (← answerCount dir) > recorded)
  if judged then
    t "browser batch: warm successes and refusals perform no conversion" warm.isEmpty
  t "browser batch: an empty input starts no work" ((← BrowserFaces.prepareAll #[] limit).isEmpty)
  let cache ← (dir / "cache" / "leantex" / "convs").readDir
  t "browser batch: no staging residue" (cache.all (fun e => !e.fileName.endsWith ".part"))
  if judged then
    t "browser batch: one whole answer per cold conversion"
      ((cache.filter (·.fileName.endsWith ".answer")).size == 11)
  for entry in cache do
    if entry.fileName.endsWith ".answer" then
      t "browser batch: persisted answer checksum is valid"
        ((ConvCache.decode (← IO.FS.readBinFile entry.path)).isSome)
    if entry.fileName.endsWith ".ver" then
      t "browser batch: concurrent cold identity memos remain complete"
        ((PicCache.readVersionMemo (← IO.FS.readFile entry.path)).any fun (stamp, version) =>
          !stamp.isEmpty && version == "browser-face test 1")
  let failed ← ref.get
  for message in failed.reverse do IO.eprintln message
  unless judged do
    IO.println s!"browser batch limit={limit}: the host denied a tool identity \
({calls.length} cold calls, {recorded} answers recorded, {warm.length} warm calls); \
census not judged"
  IO.println s!"browser batch limit={limit}: {failed.length} failures"
  return if !failed.isEmpty then 1 else if judged then 0 else deniedExit

-- A slow stub sleeps through its first version answer; a probe that kills
-- it at its budget leaves no answered marker.
private def versionStub (slow : Bool := false) : String :=
  "#!/bin/sh\n\
case \"$1\" in -v|--version)\n" ++
  (if slow then
    "  if /bin/mkdir \"$LEANTEX_FACE_BATCH_ROOT/slow-probe\" 2>/dev/null; then\n\
    /bin/sleep 10; : > \"$LEANTEX_FACE_BATCH_ROOT/slow-probe-answered\"\n\
  fi\n" else "") ++
  "  printf '%s\\n' 'browser-face test 1'; exit 0;; esac\n"

-- The converter witnesses real overlap via a handshake, not an elapsed-time
-- assertion. Its source lock and event log cover the actual process boundary.
private def converterStub (pdf : Bool) : String :=
  versionStub ++
  (if pdf then
    "kind=pdf-page-$3\ninput=$6\noutput=$7\n"
   else
    "input=$4\noutput=$3\n\
case \"$1\" in --format=pdf) kind=validate;; *) kind=svg-poster;; esac\n") ++
  "root=$LEANTEX_FACE_BATCH_ROOT\n\
id=$(/bin/sed -n 's/.*batch-id:\\([a-z-]*\\).*/\\1/p' \"$input\")\n\
case \"$id\" in ''|*[!a-z-]*) echo 'missing synthetic source marker' >&2; exit 3;; esac\n\
key=$kind:$id\n\
if ! /bin/mkdir \"$root/active/$id\" 2>/dev/null; then\n\
  : > \"$root/collision\"\n\
  echo 'concurrent conversion of the same captured source' >&2; exit 3\n\
fi\n\
if [ \"$kind\" != validate ]; then : > \"$root/primaries/$id\"; fi\n\
printf '%s\\n' \"$key\" >> \"$root/calls\"\n\
printf '+ %s\\n' \"$key\" >> \"$root/events\"\n\
trap '/bin/rmdir \"$root/active/$id\"; /bin/rm -f \"$root/primaries/$id\"; printf \"%s %s\\n\" - \"$key\" >> \"$root/events\"; : > \"$root/done/$key\"' EXIT\n\
if [ \"$kind\" = validate ]; then\n\
  for busy in \"$root/primaries/\"*; do\n\
    [ ! -f \"$busy\" ] || : > \"$root/early-companion\"\n\
  done\n\
fi\n\
: > \"$root/started/$id\"\n\
if [ \"$LEANTEX_FACE_BATCH_LIMIT\" -gt 1 ]; then\n\
  waitfor=''\n\
  case \"$id\" in a) waitfor=$root/done/pdf-page-2:b;; b) waitfor=$root/started/a;; esac\n\
  if [ -n \"$waitfor\" ]; then\n\
    n=0\n\
    while [ ! -f \"$waitfor\" ] && [ \"$n\" -lt 500 ]; do /bin/sleep 0.01; n=$((n + 1)); done\n\
    [ -f \"$waitfor\" ] || : > \"$root/timeout\"\n\
  fi\n\
fi\n\
case \"$id\" in bad|failed) echo 'synthetic conversion refusal' >&2; exit 3;; esac\n\
if [ \"$kind\" = validate ]; then /bin/cat \"$root/canvas.pdf\" > \"$output\"\n\
else printf '<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"20\" height=\"20\"><desc>%s</desc><path d=\"M0 0L20 20\"/></svg>' \"$key\" > \"$output\"\n\
fi\n"

private def writeTool (path : System.FilePath) (body : String) : IO Unit := do
  IO.FS.writeFile path body
  IO.setAccessRights path { user := ⟨true, true, true⟩ }

end Tests.BrowserFaceBatch

namespace Tests

open LeanTex.Cli

/-- Real preparation, cache reads/writes and child processes under isolated
synthetic tools. No installed vector converter or shared user cache is used.
A run the host denied a tool identity runs again, three runs per limit at
most; the first run at `slowProbeLimit` is denied on purpose. -/
def browserFaceBatchChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some lean ← ToolProbe.onPath "lean" |
    throw <| IO.userError "browser batch checks require the Lean interpreter"
  let cwd ← IO.currentDir
  let libraries ← IO.FS.realPath ".lake/build/lib/lean"
  let leanPath := libraries.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD ""
  let denied := PicCache.Ran.exited BrowserFaceBatch.deniedExit.toNat
  for limit in #[0, 1, 2, 4] do
    let mut runs : Array (RunBounded.Ended × Bool) := #[]
    for attempt in [:3] do
      let slow := limit == BrowserFaceBatch.slowProbeLimit && attempt == 0
      let run ← IO.FS.withTempDir fun dir => do
        for name in ["bin", "active", "primaries", "started", "done"] do
          IO.FS.createDir (dir / name)
        IO.FS.writeBinFile (dir / "canvas.pdf") svgCanvasPdf
        BrowserFaceBatch.writeTool (dir / "bin" / "pdftocairo")
          (BrowserFaceBatch.converterStub true)
        BrowserFaceBatch.writeTool (dir / "bin" / "rsvg-convert")
          (BrowserFaceBatch.converterStub false)
        BrowserFaceBatch.writeTool (dir / "bin" / "xsltproc")
          (BrowserFaceBatch.versionStub ++
            "for input in \"$@\"; do :; done\n/bin/cat \"$input\"\n")
        BrowserFaceBatch.writeTool (dir / "bin" / "xmllint")
          (BrowserFaceBatch.versionStub slow ++
            "case \"$3\" in --sax) printf 'SAX.startDocument()\\nSAX.endDocument()\\n';;\n\
             --xpath) printf 'true\\n';; *) exit 3;; esac\n")
        let probe := dir / "probe.lean"
        IO.FS.writeFile probe
          "import Tests.BrowserFaceBatch\n\
           def main (args : List String) : IO UInt32 := Tests.BrowserFaceBatch.runChild args\n"
        let result ← RunBounded.runBounded lean.toString
          #["--run", probe.toString, toString limit] cwd 30000 100 (env := #[
            ("PATH", some (dir / "bin").toString), ("LEAN_PATH", some leanPath),
            ("XDG_CACHE_HOME", some (dir / "cache").toString),
            ("LEANTEX_FACE_BATCH_ROOT", some dir.toString),
            ("LEANTEX_FACE_BATCH_LIMIT", some (toString limit))])
        let killed := (← (dir / "slow-probe").pathExists) &&
          !(← (dir / "slow-probe-answered").pathExists)
        return (result, killed)
      runs := runs.push run
      unless run.1.complete && run.1.ran == denied do break
    let some (result, _) := runs.back? | continue
    check ref s!"browser batch limit={limit}: isolated IO contracts\n{result.out}{result.err}"
      (result.complete && result.ran == .exited 0)
    if limit == BrowserFaceBatch.slowProbeLimit then
      check ref "browser batch: a run denied a tool identity runs again, unjudged"
        (runs[0]?.any fun (first, killed) => killed && first.ran == denied)

end Tests
