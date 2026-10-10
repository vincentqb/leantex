/-
The PDF reader and validator oracle. Run from the repository root:

  lake build TestsModules leantex && lake env lean --run scripts/pdf-oracles.lean

The engine's own reader judges every written file inside `lake test`
(Tests/PdfConformance.lean: the reference walk, the mutants, determinism).
This script is the external half: it builds every corpus fixture that
declares a PDF output (or declares none) with the shipped binary, then asks
the readers on this host what they make of the bytes — Poppler (`pdfinfo`,
`pdffonts`, `pdftotext`, and `pdftoppm` as the raster reference),
Ghostscript, pypdf, PDFium through the host Chrome's own viewer, pdf.js
lifted out of the host Firefox's `omni.ja` and run under the same Chrome —
and the validator (veraPDF, PDF/A-4 and PDF/UA-2 on the four reference
fixtures), and writes what they said as data: `testdata/oracles/reader-
matrix.txt`, whose `[feature]` rows are the writer's typed census
(`Pdf.features`, computed here from the same inputs `write` reads, one row
per `Feature.all`), whose cells are (feature, reader) verdicts, and whose
`[profile]` cells are the validator's measured failures per fixture. This
script is the file's only writer; `lake test` reads it like a golden and
never asks what is installed. A tool not on PATH writes `untested`, never
`pass`.

A browser column passes a feature when every fixture reaching it opened,
reported the page count, contained the shipped text (pdf.js
`getTextContent`, PDFium's select-all), and every page's raster lay within
`dssimTolerance` of Poppler's at 100 dpi — a tolerance, never identity:
renderers anti-alias differently, and the calibration table in the run
record is where the number comes from. Per-renderer raster hashes go to
the run record, never to the repo; movement between runs is explained
there.

The `target:` line names five readers. A host without Chrome or Firefox's
`omni.ja` writes `untested` in the browser columns and this run exits
non-zero: that matrix must not be committed — the header is widened only
in a commit whose run filled the cells.

Exit is non-zero when any cell a reached feature has in a `target:` column
is not `pass`. The run record (tool versions, per-fixture verdicts, the
DSSIM calibration, the raster hashes, the matrix diff, the validator's raw
summaries) lands under /tmp/leantex-agents/modern-output/pdf-oracles-<date>.md.
-/
import LeanTex.Cli.FontDiscovery
import Lean.Data.Json
import Tests.PdfConformance

open LeanTex.Core LeanTex.Cli Lean

def die (msg : String) : IO Unit := do
  IO.eprintln s!"pdf-oracles: FAIL {msg}"
  IO.Process.exit 1

def runTool (cmd : String) (args : Array String) : IO (Option IO.Process.Output) := do
  try
    pure (some (← IO.Process.output { cmd, args }))
  catch _ => pure none

/-- The version a tool prints, or `none` when it is not on PATH. -/
def versionOf (cmd : String) (args : Array String) (pick : String → Option String) :
    IO (Option String) := do
  match ← runTool cmd args with
  | none => pure none
  | some out =>
    if out.exitCode != 0 then pure none else pure (pick (out.stdout ++ out.stderr))

def firstWordAfter (text key : String) : Option String :=
  ((text.splitOn key).drop 1).head?.bind fun rest =>
    ((rest.trimAscii.toString.splitOn "\n").head?.bind fun l => (l.splitOn " ").head?)

/-- The readers exercised: every column the matrix carries, in order. -/
def readerColumns : Array String :=
  #["poppler", "ghostscript", "pypdf", "verapdf", "pdfium", "pdfjs", "qpdf", "arlington"]

/-- The columns this run exercises and the gate demands `pass` on. -/
def targetColumns : Array String := #["poppler", "ghostscript", "pypdf", "pdfium", "pdfjs"]

/-- The fixtures the `[profile]` section is keyed by: synthetic, four
shapes (deck, one-page résumé, two-face card, image page). -/
def profileFixtures : List String := ["deck", "resume", "trio-card", "images"]

/-- The raster judgement's resolution, for Poppler, PDFium and pdf.js alike. -/
def rasterDpi : Nat := 100

/-- The DSSIM (ImageMagick `compare -metric DSSIM`, alpha dropped, both
rasters brought to `dssimScale`) a browser's page may stand from Poppler's
and still pass. Calibrated on the 2026-09-22 run over the 142 corpus pages
(the run record carries every cell): PDFium at most 0.026 (a dense text
page, `valign` p5) and pdf.js at most 0.030 (`deck` p8) against Poppler;
the negative cases the same record keeps lie above — a page against a
different page of the same deck 0.085, a text page against itself rolled
down one 12 pt line 0.043. The window is narrow, `[0.030, 0.043]`, and the
number sits in its middle; a wider one needs a metric that reads ink
positions, not pixels. Not identity: Ghostscript's fast-colour raster
against Poppler measures 0.002 on the image page and is meant to. -/
def dssimTolerance : Float := 0.035

/-- One fixture's verdicts from the host readers: a reason per failed
check, empty when every check passed. -/
structure Fixture where
  name : String
  pages : Nat
  features : List String
  /-- The body text the layout shipped, whose ink every extractor must contain. -/
  shipped : String := ""
  poppler : Array String := #[]
  ghostscript : Array String := #[]
  pypdf : Array String := #[]
  pdfium : Array String := #[]
  pdfjs : Array String := #[]
  tagged : String := ""
  /-- Per page: PDFium's and pdf.js's DSSIM against Poppler, when measured. -/
  dssim : Array (Option Float × Option Float) := #[]
  /-- Per page: the FNV-64 of each renderer's PNG (poppler, pdfium, pdfjs). -/
  hashes : Array (String × String × String) := #[]
  deriving Repr

/-- A font set from the faces this host and the corpus directory carry:
the body (or sans) family the document names, at the four standard
weights, else the default family; the math face the driver would pick
(declared, or the body's companion, or the first MATH-table face); the
scan's per-glyph fallback — enough for the shipped text the containment
check reads. The driver's declared per-variant faces are not reproduced
here: they move line breaks, never the characters shipped. -/
def fontSetFor (faces : Array FontDb.Face) (doc : Ir.Doc) : IO (Option Font.FontSet) := do
  let spec := doc.fonts
  let named := spec.body.orElse fun _ => spec.sans.orElse fun _ => spec.mono
  let some family := named.orElse fun _ => FontDb.defaultFamily faces | return none
  let mut fonts : Array Font.Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Nat × Bool) × Nat) := #[]
  let famOf (slot : Nat) : String := match slot with
    | 1 => spec.sans.getD family
    | 2 => spec.mono.getD family
    | _ => family
  for slot in [0:3] do
    for (w, i) in [(400, false), (700, false), (400, true), (700, true)] do
      if let some (face, _) := FontDb.resolveWeight faces (famOf slot) none w i then
        match paths.findIdx? (· == face.path) with
        | some k => index := index.push ((slot, w, i), k)
        | none =>
          if let .ok f := Font.parse (← IO.FS.readBinFile face.path) then
            index := index.push ((slot, w, i), fonts.size)
            fonts := fonts.push f
            paths := paths.push face.path
  if fonts.isEmpty then return none
  let mut mathIdx : Option Nat := none
  let mathPick : Option FontDb.Face ← match spec.math with
    | some fam => pure ((FontDb.resolveVariant faces fam none {}).map (·.1))
    | none =>
      if (Layout.docMathScalars doc).isEmpty then pure none
      else pure ((← FontDiscovery.pickMathFace faces (spec.body.getD "")).map (·.1))
  if let some face := mathPick then
    match paths.findIdx? (· == face.path) with
    | some k => if (fonts[k]!).math.isSome then mathIdx := some k
    | none =>
      if let .ok f := Font.parse (← IO.FS.readBinFile face.path) then
        if f.math.isSome then
          mathIdx := some fonts.size
          fonts := fonts.push f
          paths := paths.push face.path
  let mathAlphabets := match mathIdx.bind (fonts[·]?) with
    | some f => f.mathAlphabetCoverage spec.mathSources
    | none => { sources := spec.mathSources }
  let familyName := mathIdx.bind (fonts[·]?) |>.map (·.family) |>.getD "math face"
  let resolved := (Ir.resolveMathAlphas mathAlphabets familyName doc).1
  let mut fallback : Array (Char × Nat) := #[]
  let mut uncovered : Array Char := #[]
  for c in Layout.docScalars resolved do
    match (Array.range fonts.size).find? (fun k => ((fonts[k]!).gid c).isSome) with
    | some k => fallback := fallback.push (c, k)
    | none => uncovered := uncovered.push c
  for (c, path) in ← FontDiscovery.fallbackPicksPreferring (·.startsWith "testdata/corpus") faces uncovered do
    match paths.findIdx? (· == path) with
    | some k => fallback := fallback.push (c, k)
    | none =>
      if let .ok f := Font.parse (← IO.FS.readBinFile path) then
        fallback := fallback.push (c, fonts.size)
        fonts := fonts.push f
        paths := paths.push path
  return some { fonts, index, fallback, math := mathIdx, mathAlphabets }

/-- The ink a text carries, as a character multiset: what containment
compares. Whitespace is layout, the hyphen is line breaking's (a word
hyphenated at a line end gains one), so neither counts. -/
def inkOf (s : String) : Std.HashMap Char Nat :=
  s.toList.foldl (fun m c =>
    if c.isWhitespace || c == '-' || c == '\u00ad' then m
    else m.insert c (m.getD c 0 + 1)) {}

/-- The characters of `need` (with multiplicity) that `have` lacks. -/
def missingInk (need have_ : Std.HashMap Char Nat) : Array Char :=
  need.fold (fun acc c k =>
    let short := k - have_.getD c 0
    acc ++ Array.replicate short c) #[]

/-- The containment reason for one extractor's text, or none. -/
def containment (tag shipped extracted : String) : Option String :=
  let missing := missingInk (inkOf shipped) (inkOf extracted)
  if missing.isEmpty then none
  else some s!"{tag}-missing:{missing.size}:{String.ofList (missing.toList.take 12)}"

/-- The failed rule ids in a veraPDF XML report, `clause-testNumber`,
sorted, once each; and the report's own summary line. -/
def veraFailures (xml : String) : Array String × String := Id.run do
  let mut ids : Array String := #[]
  let mut summary := ""
  for l in xml.splitOn "\n" do
    let t := l.trimAscii.toString
    if t.startsWith "<details " then summary := t
    if t.startsWith "<rule " && hasStr t "status=\"failed\"" then
      let attr (k : String) : String :=
        (((t.splitOn (k ++ "=\"")).drop 1).head?.bind fun r => (r.splitOn "\"").head?).getD "?"
      let id := s!"{attr "clause"}-{attr "testNumber"}"
      unless ids.contains id do ids := ids.push id
  return (ids.qsort (· < ·), summary)

-- ## The browser judges

/-- The Chrome binaries to try: `LEANTEX_CHROME` first, then every
`~/.cache/ms-playwright/chromium-*/chrome-linux64/chrome`, newest revision
first — the full browser, whose viewer is PDFium; the `headless_shell`
beside it downloads a PDF instead of showing it. Nothing is installed. -/
def chromeCandidates : IO (Array String) := do
  let mut out : Array String := #[]
  if let some p ← IO.getEnv "LEANTEX_CHROME" then out := out.push p
  if let some home ← IO.getEnv "HOME" then
    let pw : System.FilePath := home / ".cache" / "ms-playwright"
    if ← pw.isDir then
      let revs := ((← pw.readDir).filter (·.fileName.startsWith "chromium-")).qsort
        (·.fileName > ·.fileName)
      for e in revs do
        let c := e.path / "chrome-linux64" / "chrome"
        if ← c.pathExists then out := out.push c.toString
  return out

/-- The first Chrome that reports a version, with it. -/
def findChrome : IO (Option (String × String)) := do
  for c in ← chromeCandidates do
    if let some out ← runTool c #["--version"] then
      if out.exitCode == 0 then
        return some (c, ((out.stdout.trimAscii.toString.splitOn "\n").headD "").trimAscii.toString)
  return none

/-- pdf.js, as the host Firefox ships it: `pdf.mjs` and `pdf.worker.mjs`
unzipped from `omni.ja` (`LEANTEX_OMNI_JA`, else `/usr/lib64/firefox/omni.ja`)
into `dir`; the library's own version string comes back. -/
def extractPdfjs (dir : System.FilePath) : IO (Option String) := do
  let omni := (← IO.getEnv "LEANTEX_OMNI_JA").getD "/usr/lib64/firefox/omni.ja"
  unless ← System.FilePath.pathExists omni do return none
  let some out ← runTool "unzip" #["-o", "-j", "-q", omni,
    "chrome/pdfjs/content/build/pdf.mjs", "chrome/pdfjs/content/build/pdf.worker.mjs",
    "-d", dir.toString] | return none
  if out.exitCode != 0 then return none
  let src ← IO.FS.readFile (dir / "pdf.mjs")
  return (firstWordAfter src "const pdfjsVersion = \"").map fun w => (w.splitOn "\"").headD w

/-- The pdf.js harness page: one document per `judge` call — bytes fetched
from the file URL, every page rendered to a canvas at the scale asked
(points to pixels) and read back as PNG, its text content, the metadata. -/
def harnessHtml : String := r#"<!doctype html><meta charset="utf-8"><title>pdf.js judge</title>
<script type="module">
import * as pdfjs from './pdf.mjs';
pdfjs.GlobalWorkerOptions.workerSrc = './pdf.worker.mjs';
window.judge = async (url, scale) => {
  const data = new Uint8Array(await (await fetch(url)).arrayBuffer());
  const doc = await pdfjs.getDocument({ data }).promise;
  const text = [], pngs = [];
  for (let i = 1; i <= doc.numPages; i++) {
    const page = await doc.getPage(i);
    const vp = page.getViewport({ scale });
    const c = document.createElement('canvas');
    c.width = Math.round(vp.width); c.height = Math.round(vp.height);
    const ctx = c.getContext('2d');
    ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, c.width, c.height);
    await page.render({ canvasContext: ctx, viewport: vp }).promise;
    pngs.push(c.toDataURL('image/png').split(',')[1]);
    const tc = await page.getTextContent();
    text.push(tc.items.map(it => it.str + (it.hasEOL ? '\n' : '')).join(' '));
  }
  const meta = (await doc.getMetadata()).info;
  return { version: pdfjs.version, pages: doc.numPages, text, meta, pngs };
};
// The page inside a viewer capture: the bounding box of every pixel that
// is not the background the viewer was told to paint (magenta), less the
// viewer's page-shadow insets (3 top, 7 bottom, 5 left and right CSS px
// at zoom 1), cut out and returned as PNG.
window.cropPage = async (b64, zoom, cx, cy) => {
  const img = await createImageBitmap(await (await fetch('data:image/png;base64,' + b64)).blob());
  const c = document.createElement('canvas'); c.width = img.width; c.height = img.height;
  const ctx = c.getContext('2d'); ctx.drawImage(img, 0, 0);
  const d = ctx.getImageData(0, 0, c.width, c.height).data;
  const bg = (x, y) => { const i = (y * c.width + x) * 4; return d[i] > 235 && d[i + 1] < 20 && d[i + 2] > 235; };
  const rowBg = y => { for (let x = 0; x < c.width; x++) if (!bg(x, y)) return false; return true; };
  const colBg = (x, y0, y1) => { for (let y = y0; y <= y1; y++) if (!bg(x, y)) return false; return true; };
  cx = Math.min(c.width - 1, Math.max(0, Math.round(cx))); cy = Math.min(c.height - 1, Math.max(0, Math.round(cy)));
  if (rowBg(cy)) throw new Error('no-page-at-centre');
  let y0 = cy, y1 = cy;
  while (y0 > 0 && !rowBg(y0 - 1)) y0--;
  while (y1 < c.height - 1 && !rowBg(y1 + 1)) y1++;
  let x0 = cx, x1 = cx;
  while (x0 > 0 && !colBg(x0 - 1, y0, y1)) x0--;
  while (x1 < c.width - 1 && !colBg(x1 + 1, y0, y1)) x1++;
  const x = x0 + Math.round(5 * zoom), y = y0 + Math.round(3 * zoom);
  const w = x1 + 1 - Math.round(5 * zoom) - x, h = y1 + 1 - Math.round(7 * zoom) - y;
  if (w < 8 || h < 8) throw new Error(`page-too-small:${w}x${h}`);
  const o = document.createElement('canvas'); o.width = w; o.height = h;
  o.getContext('2d').drawImage(c, x, y, w, h, 0, 0, w, h);
  return { x, y, w, h, png: o.toDataURL('image/png').split(',')[1] };
};
</script>
"#

/-- The browser driver, run by node: one headless Chrome over its debugging
pipe (no module, no port), a viewer tab for PDFium and a harness tab for
pdf.js. argv: chrome, the work directory (pdf.mjs, pdf.worker.mjs,
harness.html), then PDF paths. One JSON line per PDF on stdout.

PDFium is Chrome's own viewer: the file is navigated to, the extension
frame attaches as its own target, and the `pdf-viewer` element there
reports the load state (`failed` on a broken file) and the page boxes. The
viewport is zoomed so a point is `dpi/72` pixels, the plugin is told to
paint its background magenta, and each page is captured whole-viewport
once three consecutive captures agree; the harness then cuts the page out
as the block of non-magenta pixels around the viewer's idea of the page
centre, less the viewer's shadow insets — the viewer's own rectangle was
off by pixels on some pages, and a pixel is the truth here. PDFium's text
is the select-all selection. -/
def judgeJs : String := r#"
import { spawn } from 'node:child_process';
import { writeFileSync } from 'node:fs';
import { basename, join } from 'node:path';

const [chrome, workDir, dpiArg, ...pdfs] = process.argv.slice(2);
const DPI = +dpiArg;
const child = spawn(chrome, ['--headless=new', '--no-sandbox', '--disable-gpu', '--hide-scrollbars',
  '--remote-debugging-pipe', `--user-data-dir=${join(workDir, 'profile')}`,
  '--allow-file-access-from-files', '--no-first-run', '--force-device-scale-factor=1', 'about:blank'],
  { stdio: ['ignore', 'ignore', 'pipe', 'pipe', 'pipe'] });
const wr = child.stdio[3], rd = child.stdio[4];
let buf = '', nextId = 0;
const pending = new Map(), listeners = new Set();
rd.on('data', d => {
  buf += d.toString();
  let k;
  while ((k = buf.indexOf('\0')) >= 0) {
    const msg = JSON.parse(buf.slice(0, k)); buf = buf.slice(k + 1);
    if (msg.id && pending.has(msg.id)) {
      const p = pending.get(msg.id); pending.delete(msg.id);
      msg.error ? p.rej(new Error(msg.error.message)) : p.res(msg.result);
    } else for (const l of listeners) l(msg);
  }
});
const send = (method, params = {}, sessionId, ms = 30000) => new Promise((res, rej) => {
  const m = { id: ++nextId, method, params }; if (sessionId) m.sessionId = sessionId;
  const t = setTimeout(() => { pending.delete(m.id); rej(new Error(`${method}: no reply in ${ms} ms`)); }, ms);
  pending.set(m.id, { res: v => { clearTimeout(t); res(v); }, rej: e => { clearTimeout(t); rej(e); } });
  wr.write(JSON.stringify(m) + '\0');
});
const sleep = ms => new Promise(r => setTimeout(r, ms));
const evalIn = async (sessionId, expression) => {
  const r = await send('Runtime.evaluate', { expression, returnByValue: true, awaitPromise: true }, sessionId);
  if (r.exceptionDetails) throw new Error(r.exceptionDetails.exception?.description || r.exceptionDetails.text);
  return r.result.value;
};
const savePng = (b64, path) => { writeFileSync(path, Buffer.from(b64, 'base64')); return path; };

// A page target: created once, navigated per document.
const newPage = async () => {
  const { targetId } = await send('Target.createTarget', { url: 'about:blank' });
  const { sessionId } = await send('Target.attachToTarget', { targetId, flatten: true });
  await send('Page.enable', {}, sessionId);
  await send('Runtime.enable', {}, sessionId);
  return { targetId, sessionId };
};
const setViewport = (sessionId, width, height) =>
  send('Emulation.setDeviceMetricsOverride', { width, height, deviceScaleFactor: 1, mobile: false }, sessionId);

// Wait until a probe expression yields a truthy value, or time runs out.
const waitFor = async (sessionId, expression, ms) => {
  const t0 = Date.now();
  while (Date.now() - t0 < ms) {
    const v = await evalIn(sessionId, expression).catch(() => null);
    if (v) return v;
    await sleep(100);
  }
  return null;
};

// ---- PDFium: Chrome's viewer. The extension frame attaches as its own
// target; the `pdf-viewer` element there reports load state and page
// boxes, and its plugin paints on the background it is told to.
const tick = `(() => { let k = document.getElementById('leantex-tick'); if (!k) { k = document.createElement('div'); k.id = 'leantex-tick'; k.style.cssText = 'position:fixed;left:0;top:0;width:2px;height:2px;z-index:-1'; document.body.appendChild(k); } k.style.background = k.style.background === 'rgb(1, 1, 1)' ? 'rgb(2, 2, 2)' : 'rgb(1, 1, 1)'; })()`;

async function pdfium(page, harness, viewerFrames, pdfPath, outPrefix) {
  const out = { ok: false, pages: 0, text: '', rasters: [], error: '' };
  viewerFrames.length = 0;
  let download = false;
  const dl = m => { if (m.method === 'Page.downloadWillBegin') download = true; };
  listeners.add(dl);
  try {
    await setViewport(page.sessionId, 1000, 1000);
    await send('Page.navigate', { url: `file://${pdfPath}#toolbar=0` }, page.sessionId);
    const t0 = Date.now();
    let fs = null, state = null;
    while (Date.now() - t0 < 20000 && !download) {
      for (const f of viewerFrames) {
        state = await evalIn(f, `(() => { const v = document.querySelector('pdf-viewer'); return v ? v.loadState_ : null; })()`).catch(() => null);
        if (state === 'success' || state === 'failed') { fs = f; break; }
      }
      if (fs) break;
      await sleep(100);
    }
    if (download) throw new Error('download-instead-of-view');
    if (!fs) throw new Error(`viewer-not-loaded:${state}`);
    if (state !== 'success') throw new Error(`load-state:${state}`);
    const pageDims = JSON.parse(await evalIn(fs, `JSON.stringify(document.querySelector('pdf-viewer').documentDimensions.pageDimensions)`));
    out.pages = pageDims.length;
    // Magenta behind the pages: the harness finds each page as the block of
    // pixels that are not it.
    await evalIn(fs, `document.querySelector('pdf-viewer').currentController.setBackgroundColor(0xFFFF00FF)`);
    // Zoom so one point is DPI/72 pixels; a viewport that holds one page.
    const zoom = DPI / 96;
    const maxW = Math.max(...pageDims.map(p => p.width)), maxH = Math.max(...pageDims.map(p => p.height));
    await setViewport(page.sessionId, Math.ceil(maxW * zoom) + 60, Math.ceil(maxH * zoom) + 60);
    await evalIn(fs, `document.querySelector('pdf-viewer').viewport_.setZoom(${zoom})`);
    await sleep(100);
    for (let i = 0; i < pageDims.length; i++) {
      await evalIn(fs, `document.querySelector('pdf-viewer').viewport_.goToPage(${i})`);
      const rect = JSON.parse(await evalIn(fs, `JSON.stringify(document.querySelector('pdf-viewer').viewport_.getPageScreenRect(${i}))`));
      // Paint is asynchronous: hold until three consecutive captures agree.
      // `fromSurface: false` reads the renderer's own compositor — the
      // surface path waits for a frame the viewer may never produce once
      // a page is painted, and hung for good on later pages — and honours
      // no clip, so the whole viewport is captured. A capture still needs
      // a frame, so the tick is toggled behind the embed in both frames
      // while one is pending.
      await sleep(250);
      let prev = null, stable = 0, data = null;
      const t1 = Date.now();
      while (Date.now() - t1 < 15000) {
        let capturing = true;
        const ticker = (async () => { while (capturing) { for (const sid of [page.sessionId, fs]) await evalIn(sid, tick).catch(() => {}); await sleep(100); } })();
        const shot = await send('Page.captureScreenshot', { format: 'png', fromSurface: false }, page.sessionId, 15000).catch(() => null);
        capturing = false; await ticker;
        if (!shot) continue;
        data = shot.data;
        if (data === prev && ++stable >= 3) break;
        if (data !== prev) stable = 0;
        prev = data; await sleep(200);
      }
      if (!data) throw new Error(`no-capture:page${i + 1}`);
      // The page's pixels, found from the viewer's own idea of its centre.
      const cut = await evalIn(harness.sessionId, `window.cropPage(${JSON.stringify(data)}, ${zoom}, ${rect.x + rect.width / 2}, ${rect.y + rect.height / 2})`);
      out.rasters.push(savePng(cut.png, `${outPrefix}-pdfium-${i + 1}.png`));
    }
    // PDFium's own text: select all, read the selection.
    out.text = await evalIn(fs, `(async () => { const v = document.querySelector('pdf-viewer'); const c = v.currentController; c.selectAll(); const r = await c.getSelectedText(); return r && r.selectedText !== undefined ? r.selectedText : JSON.stringify(r); })()`);
    out.ok = true;
  } catch (e) { out.error = String(e.message || e); }
  listeners.delete(dl);
  return out;
}

// ---- pdf.js: the harness page loads the library from the work dir and
// judges one document per call.
async function pdfjs(page, pdfPath, outPrefix) {
  const out = { ok: false, version: '', pages: 0, text: [], meta: null, rasters: [], error: '' };
  try {
    const r = await evalIn(page.sessionId, `window.judge(${JSON.stringify(`file://${pdfPath}`)}, ${DPI / 72})`);
    out.version = r.version; out.pages = r.pages; out.text = r.text; out.meta = r.meta;
    r.pngs.forEach((b64, i) => out.rasters.push(savePng(b64, `${outPrefix}-pdfjs-${i + 1}.png`)));
    out.ok = true;
  } catch (e) { out.error = String(e.message || e); }
  return out;
}

const main = async () => {
  const version = (await send('Browser.getVersion')).product;
  const viewer = await newPage();
  const viewerFrames = [];
  listeners.add(m => {
    if (m.method === 'Target.attachedToTarget' && m.params.targetInfo.type === 'iframe') viewerFrames.push(m.params.sessionId);
  });
  await send('Target.setAutoAttach', { autoAttach: true, waitForDebuggerOnStart: false, flatten: true }, viewer.sessionId);
  const harness = await newPage();
  await setViewport(harness.sessionId, 800, 600);
  await send('Page.navigate', { url: `file://${join(workDir, 'harness.html')}` }, harness.sessionId);
  const ready = await waitFor(harness.sessionId, 'typeof window.judge === "function"', 15000);
  if (!ready) { console.log(JSON.stringify({ fatal: 'harness did not load' })); process.exit(2); }
  console.log(JSON.stringify({ chrome: version }));
  for (const pdfPath of pdfs) {
    const stem = basename(pdfPath).replace(/\.pdf$/, '');
    const outPrefix = join(workDir, stem);
    const a = await pdfium(viewer, harness, viewerFrames, pdfPath, outPrefix);
    const b = await pdfjs(harness, pdfPath, outPrefix);
    console.log(JSON.stringify({ name: stem, pdfium: a, pdfjs: b }));
  }
  await send('Browser.close').catch(() => {});
  child.kill();
};
main().catch(e => { console.log(JSON.stringify({ fatal: String(e.message || e) })); child.kill(); process.exit(2); });
"#

/-- What the driver said of one file, per engine. -/
structure Browser where
  ok : Bool := false
  pages : Nat := 0
  text : String := ""
  error : String := ""
  /-- Per page: the PNG of the page as the engine painted it. -/
  rasters : Array String := #[]
  formatVersion : String := ""
  deriving Repr, Inhabited

def jStr (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok (.str s) => s
  | _ => ""

def jNat (j : Json) (k : String) : Nat :=
  match (j.getObjVal? k).bind (·.getNat?) with
  | .ok n => n
  | _ => 0

def jArr (j : Json) (k : String) : Array Json :=
  match j.getObjVal? k with
  | .ok (.arr xs) => xs
  | _ => #[]

def browserOf (j : Json) (isPdfium : Bool) : Browser := Id.run do
  let ok := match j.getObjVal? "ok" with
    | .ok (.bool v) => v
    | _ => false
  let mut b : Browser := { ok, pages := jNat j "pages", error := jStr j "error" }
  b := { b with rasters := (jArr j "rasters").map fun r =>
    match r with | .str s => s | _ => "" }
  if isPdfium then
    b := { b with text := jStr j "text" }
  else
    b := { b with text := String.intercalate "\n" ((jArr j "text").toList.map fun t =>
      match t with | .str s => s | _ => "") }
    if let .ok metaJ := j.getObjVal? "meta" then
      b := { b with formatVersion := jStr metaJ "PDFFormatVersion" }
  return b

/-- A decimal as ImageMagick prints it (`0.0197563`, `1.2e-05`), or none. -/
def parseFloat (s : String) : Option Float := do
  let s := s.trimAscii.toString
  let (mant, exp) := match s.splitOn "e" with
    | [m, e] => (m, e.toInt?.getD 0)
    | _ => (s, 0)
  let neg := mant.startsWith "-"
  let mant := if neg then (mant.drop 1).toString else mant
  let (ip, fp) := match mant.splitOn "." with
    | [i, f] => (i, f)
    | [i] => (i, "")
    | _ => ("", "")
  let i ← if ip.isEmpty then some 0 else ip.toNat?
  let f ← if fp.isEmpty then some 0 else fp.toNat?
  let v : Float := Float.ofNat i + Float.ofNat f / Float.ofNat (10 ^ fp.length)
  let v := if exp ≥ 0 then v * Float.ofNat (10 ^ exp.toNat) else v / Float.ofNat (10 ^ (-exp).toNat)
  return if neg then -v else v

/-- `WxH` of a PNG, by `magick identify`. -/
def pngGeometry (png : String) : IO (Option String) := do
  let some out ← runTool "magick" #["identify", "-format", "%wx%h", png] | return none
  if out.exitCode != 0 then return none
  return some out.stdout.trimAscii.toString

/-- The scale both rasters are brought to before they are compared: a
quarter of `rasterDpi`, 25 dpi. At full resolution the distance between
two conforming renderers of one dense text page (glyph anti-aliasing, a
one-pixel registration offset) exceeds the distance between two different
pages; at a quarter the glyphs are the grey they set, and what remains is
where ink lies. -/
def dssimScale : String := "25%"

/-- The candidate with alpha dropped, resampled to the reference's geometry
and then to `dssimScale`; the reference the same way; then `compare -metric
DSSIM`, whose parenthesised number is the normalised distance. -/
def dssimAgainst (dir : System.FilePath) (tag : String) (candidate reference : String) :
    IO (Option Float) := do
  let some geom ← pngGeometry reference | return none
  let a := (dir / s!"{tag}-a.png").toString
  let b := (dir / s!"{tag}-b.png").toString
  let some ca ← runTool "magick"
    #[candidate, "-alpha", "off", "-resize", geom ++ "!", "-resize", dssimScale, a] | return none
  if ca.exitCode != 0 then return none
  let some cb ← runTool "magick" #[reference, "-alpha", "off", "-resize", dssimScale, b] | return none
  if cb.exitCode != 0 then return none
  let some cmp ← runTool "magick" #["compare", "-metric", "DSSIM", a, b, "null:"] | return none
  let text := cmp.stderr ++ cmp.stdout
  match (text.splitOn "(").drop 1 with
  | inner :: _ => return parseFloat ((inner.splitOn ")").headD "")
  | [] => return parseFloat text

/-- The FNV-64 of a file's bytes, as the run record spells a raster. -/
def fileHash (path : String) : IO String := do
  let b ← IO.FS.readBinFile path
  return Flate.hex16 (Flate.fnv64 14695981039346656037 b)

/-- Poppler's rasters of a file at `rasterDpi`, one PNG per page in page
order (`pdftoppm` pads the page number to the count's width). -/
def popplerRasters (dir : System.FilePath) (pdf : String) (stem : String) : IO (Array String) := do
  let pre := (dir / s!"{stem}-poppler").toString
  let some out ← runTool "pdftoppm" #["-r", toString rasterDpi, "-png", pdf, pre] | return #[]
  if out.exitCode != 0 then return #[]
  let mut found : Array (Nat × String) := #[]
  for e in ← dir.readDir do
    if e.fileName.startsWith s!"{stem}-poppler-" && e.fileName.endsWith ".png" then
      let num := ((e.fileName.dropEnd 4).toString.splitOn "-").getLast?.bind (·.toNat?)
      if let some n := num then found := found.push (n, e.path.toString)
  return (found.qsort (·.1 < ·.1)).map (·.2)

def fmtF (f : Float) : String :=
  let s := toString f
  (s.take 8).toString

def main : IO Unit := do
  let bin := ".lake/build/bin/leantex"
  unless ← System.FilePath.pathExists bin do
    let b ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
    if b.exitCode != 0 then die s!"lake build leantex: {b.stderr}"
  let date := ((← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d"] }).stdout).trimAscii.toString
  -- Tool versions; a missing tool is `none`, and its column stays untested.
  let popplerV ← versionOf "pdfinfo" #["-v"] (firstWordAfter · "pdfinfo version ")
  let gsV ← versionOf "gs" #["--version"] fun s => (s.trimAscii.toString.splitOn "\n").head?
  let pypdfV ← versionOf "python3" #["-c", "import pypdf; print(pypdf.__version__)"]
    fun s => (s.trimAscii.toString.splitOn "\n").head?
  let veraPath := "/home/linuxbrew/.linuxbrew/bin/verapdf"
  let veraV ← versionOf veraPath #["--version"] (firstWordAfter · "veraPDF ")
  let magickV ← versionOf "magick" #["-version"] (firstWordAfter · "ImageMagick ")
  let nodeV ← versionOf "node" #["--version"] fun s => (s.trimAscii.toString.splitOn "\n").head?
  let chrome ← findChrome
  let dir ← IO.FS.createTempDir
  let pdfjsV ← extractPdfjs dir
  -- The browsers run when Chrome, node, pdf.js, pdftoppm and magick are
  -- all here; else both browser columns are untested and the run fails.
  let browsers := chrome.isSome && nodeV.isSome && pdfjsV.isSome && popplerV.isSome && magickV.isSome
  let chromeV := chrome.map fun (_, v) => (v.splitOn " ").getLast?.getD v
  let toolsLine (vera : Option String) : String := String.intercalate "  " [
    s!"poppler {popplerV.getD "absent"}", s!"ghostscript {gsV.getD "absent"}",
    s!"pypdf {pypdfV.getD "absent"}", s!"verapdf {vera.getD "absent"}",
    s!"chrome {chromeV.getD "absent"}", s!"pdfjs {pdfjsV.getD "absent"}"]
  IO.println s!"pdf-oracles: {toolsLine veraV}"
  IO.println s!"pdf-oracles: node {nodeV.getD "absent"}  magick {magickV.getD "absent"}  browsers {if browsers then "on" else "off"}"
  let faces ← FontDiscovery.scanRoots (["testdata/corpus/fonts"] ++ (← FontDiscovery.systemRoots []))
  let pats := Hyphen.english.get
  -- The fixtures: every golden document that declares a PDF output or
  -- declares none, each read through its own surface (`goldenDoc`), built
  -- by the shipped binary.
  let names := goldenNames.toArray.qsort (· < ·)
  let mut fixtures : Array Fixture := #[]
  let mut notBuilt : Array String := #[]
  let mut record : Array String := #[]
  let mut censusDisagree : Array String := #[]
  for n in names do
    let (doc, _) ← goldenDoc n
    let formats := doc.output.formats
    unless formats.isEmpty || formats.contains "pdf" do continue
    let pdfPath := dir / s!"{n}.pdf"
    let built ← IO.Process.output { cmd := bin, args :=
      #[goldenFile n, "-o", pdfPath.toString, "--porcelain", "-q"] }
    if built.exitCode != 0 then
      notBuilt := notBuilt.push s!"{n} (exit {built.exitCode})"
      continue
    let pages := (((built.stdout.splitOn "\"pages\":").drop 1).head?.bind fun r =>
      ((r.splitOn ",").head?.bind (·.toNat?))).getD 0
    let pdf ← IO.FS.readBinFile pdfPath
    -- The layout this script computes, for the typed census and the
    -- shipped text; the driver's faces are approximated by `fontSetFor`.
    let some fs ← fontSetFor faces doc | die s!"{n}: no face resolves for the census"; continue
    let store ← corpusStore doc
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf fs doc geom (some pats) store
    -- The structure tree the driver writes, so the census counts its
    -- elements among the compressed objects (`objstm-multi`).
    let tree := Struct.ofDoc (Layout.pdfView doc)
    let features := (Pdf.features geom fs out.pages store out.outline tree).toList.map
      Pdf.Feature.name
    -- The census against the built bytes: the same rows, or the run says
    -- where they part. One parting is expected: a boundary picture the
    -- driver had TeX render arrives as a copied page, where this harness
    -- (no TeX) laid a placeholder — the readers judged the driver's bytes,
    -- so those two rows join the fixture's reach.
    let features ← match parsedFeatureNames pdf with
      | .ok parsed =>
        let extra := parsed.filter (!features.contains ·)
        let lost := features.filter (!parsed.contains ·)
        if extra.isEmpty && lost.isEmpty then pure features
        else if lost.isEmpty && extra.all ["form-xobject", "copied-graph"].contains then
          censusDisagree := censusDisagree.push s!"{n}: the driver's bytes add {extra} (a boundary render); rows joined"
          pure (features ++ extra)
        else
          die s!"{n}: typed census {features} and built bytes {parsed} disagree"
          pure features
      | .error e => die s!"{n}: the engine's reader refuses the built file: {e}"; pure features
    -- Body lines only: furniture (line numbers, running feet) follows
    -- this font set's line breaks, which the driver's may not share. And
    -- only lines on the medium: what a page sets past its edge is the
    -- artifact tier's offence (`artKnownOffences`), and a reader that
    -- extracts only what the page box shows is right not to read it.
    let onMedium (l : Layout.LineOut) : Bool :=
      geom.onMedium l.x (l.segs.foldl (fun w s => w + s.advance) 0)
    let shipped := String.intercalate " " (((bodyLines out).filter onMedium).toList.map (lineText ·))
    let mut fx : Fixture := { name := n, pages, features, shipped }
    -- Poppler: pdfinfo, pdffonts, pdftotext.
    if popplerV.isSome then
      let info ← IO.Process.output { cmd := "pdfinfo", args := #[pdfPath.toString] }
      let field (k : String) : String :=
        ((((info.stdout.splitOn (k ++ ":")).drop 1).head?.bind fun r =>
          (r.splitOn "\n").head?).getD "").trimAscii.toString
      unless field "PDF version" == "2.0" do
        fx := { fx with poppler := fx.poppler.push s!"pdfinfo-version:{field "PDF version"}" }
      unless field "Pages" == toString pages do
        fx := { fx with poppler := fx.poppler.push s!"pdfinfo-pages:{field "Pages"}/{pages}" }
      fx := { fx with tagged := field "Tagged" }
      let fonts ← IO.Process.output { cmd := "pdffonts", args := #[pdfPath.toString] }
      let rows := ((fonts.stdout.splitOn "\n").drop 2).filter (!·.trimAscii.toString.isEmpty)
      let cols (l : String) : Array String :=
        ((l.splitOn " ").filter (!·.isEmpty)).toArray
      let embAll := rows.all fun l => let c := cols l; c[c.size - 5]? == some "yes"
      let uniAll := rows.all fun l => let c := cols l; c[c.size - 3]? == some "yes"
      unless embAll do fx := { fx with poppler := fx.poppler.push "pdffonts-emb" }
      unless uniAll do fx := { fx with poppler := fx.poppler.push "pdffonts-uni" }
      -- pdffonts' `emb` column and the engine's census agree: pdf-objects'
      -- oracle, reasserted here.
      match PdfCensus.census pdf with
      | .ok c =>
        unless c.fontsEmbedded == embAll do
          fx := { fx with poppler := fx.poppler.push "pdffonts-census-disagree" }
      | .error e => fx := { fx with poppler := fx.poppler.push s!"census:{e}" }
      let text ← IO.Process.output { cmd := "pdftotext", args := #["-layout", pdfPath.toString, "-"] }
      if let some why := containment "pdftotext" shipped text.stdout then
        fx := { fx with poppler := fx.poppler.push why }
    -- Ghostscript: a full interpretation with errors fatal, no device.
    if gsV.isSome then
      let gs ← IO.Process.output { cmd := "gs", args :=
        #["-q", "-dNOPAUSE", "-dBATCH", "-dPDFSTOPONERROR", "-sDEVICE=nullpage", pdfPath.toString] }
      unless gs.exitCode == 0 && gs.stderr.isEmpty && gs.stdout.isEmpty do
        let why := (gs.stderr ++ gs.stdout).trimAscii.toString.take 60
        fx := { fx with ghostscript := fx.ghostscript.push s!"gs-exit{gs.exitCode}:{why}" }
    -- pypdf, strict: every page's text and the metadata read.
    if pypdfV.isSome then
      let py ← IO.Process.output { cmd := "python3", args := #["-c",
        "import sys\nfrom pypdf import PdfReader\nr = PdfReader(sys.argv[1], strict=True)\n\
for p in r.pages:\n    p.extract_text()\nr.metadata\nprint(len(r.pages))", pdfPath.toString] }
      unless py.exitCode == 0 && py.stdout.trimAscii.toString == toString pages do
        let why := ((py.stderr.trimAscii.toString.splitOn "\n").getLast?.getD "").take 60
        fx := { fx with pypdf := fx.pypdf.push s!"pypdf-exit{py.exitCode}:{why}" }
    fixtures := fixtures.push fx
    IO.println s!"  {n}: {pages} pages; poppler {fx.poppler}; gs {fx.ghostscript}; pypdf {fx.pypdf}; features {features}"
  if fixtures.size < 40 then die s!"only {fixtures.size} fixtures built"
  -- The browsers, one Chrome for every file; then each fixture's verdicts
  -- from what the driver said and the rasters it left.
  let mut hashLines : Array String := #[]
  let mut calib : Array String := #[]
  let mut negatives : Array String := #[]
  let mut driverNote := "browsers not run"
  if browsers then
    let some (chromePath, _) := chrome | pure ()
    IO.FS.writeFile (dir / "harness.html") harnessHtml
    IO.FS.writeFile (dir / "judge.mjs") judgeJs
    -- The negative case first: S3's first mutant, the file cut at 60 %,
    -- must be refused by both engines.
    let truncName := "zz-truncated"
    if let some img := fixtures.find? (·.name == "images") then
      let whole ← IO.FS.readBinFile (dir / s!"{img.name}.pdf")
      IO.FS.writeBinFile (dir / s!"{truncName}.pdf") (whole.extract 0 (whole.size * 3 / 5))
    let pdfPaths := (fixtures.map fun fx => (dir / s!"{fx.name}.pdf").toString).push
      (dir / s!"{truncName}.pdf").toString
    IO.println s!"pdf-oracles: driving {chromePath} over {pdfPaths.size} files"
    let run ← IO.Process.output { cmd := "node", args :=
      #[(dir / "judge.mjs").toString, chromePath, dir.toString, toString rasterDpi] ++ pdfPaths }
    let mut said : Std.HashMap String (Browser × Browser) := {}
    let mut chromeSaid := ""
    for l in run.stdout.splitOn "\n" do
      if l.trimAscii.toString.isEmpty then continue
      match Json.parse l with
      | .error e => driverNote := s!"driver line unreadable: {e}"
      | .ok j =>
        if let .ok (.str v) := j.getObjVal? "chrome" then chromeSaid := v
        if let .ok (.str f) := j.getObjVal? "fatal" then driverNote := s!"driver fatal: {f}"
        if let .ok (.str name) := j.getObjVal? "name" then
          let a := match j.getObjVal? "pdfium" with | .ok x => browserOf x true | _ => {}
          let b := match j.getObjVal? "pdfjs" with | .ok x => browserOf x false | _ => {}
          said := said.insert name (a, b)
    driverNote := if run.exitCode == 0 then s!"driver ok ({chromeSaid}); {said.size} files judged"
      else s!"driver exit {run.exitCode}: {run.stderr.trimAscii.toString.take 200}; {driverNote}"
    match said.get? truncName with
    | some (a, b) =>
      negatives := negatives.push s!"- truncated at 60 %: PDFium {if a.ok then "ACCEPTED" else s!"fail:{a.error}"}; pdf.js {if b.ok then "ACCEPTED" else s!"fail:{b.error}"}"
      if a.ok || b.ok then die "the truncated mutant was accepted by a browser judge"
    | none => negatives := negatives.push "- truncated at 60 %: the driver said nothing"
    let mut judged : Array Fixture := #[]
    for fx in fixtures do
      let mut fx := fx
      let stem := fx.name
      let pdfFile := (dir / s!"{stem}.pdf").toString
      let ref ← popplerRasters dir pdfFile stem
      match said.get? stem with
      | none =>
        fx := { fx with pdfium := #["pdfium-nojudgement"], pdfjs := #["pdfjs-nojudgement"] }
      | some (a, b) =>
        -- PDFium: open, page count, text, rasters.
        if !a.ok then fx := { fx with pdfium := fx.pdfium.push s!"pdfium-open:{a.error}" }
        else
          unless a.pages == fx.pages do
            fx := { fx with pdfium := fx.pdfium.push s!"pdfium-pages:{a.pages}/{fx.pages}" }
          if let some why := containment "pdfium-text" fx.shipped a.text then
            fx := { fx with pdfium := fx.pdfium.push why }
        if !b.ok then fx := { fx with pdfjs := fx.pdfjs.push s!"pdfjs-open:{b.error}" }
        else
          unless b.pages == fx.pages do
            fx := { fx with pdfjs := fx.pdfjs.push s!"pdfjs-pages:{b.pages}/{fx.pages}" }
          unless b.formatVersion == "2.0" do
            fx := { fx with pdfjs := fx.pdfjs.push s!"pdfjs-version:{b.formatVersion}" }
          if let some why := containment "pdfjs-text" fx.shipped b.text then
            fx := { fx with pdfjs := fx.pdfjs.push why }
        if ref.size != fx.pages then
          fx := { fx with pdfium := fx.pdfium.push s!"poppler-rasters:{ref.size}/{fx.pages}",
                          pdfjs := fx.pdfjs.push s!"poppler-rasters:{ref.size}/{fx.pages}" }
        for i in [0:ref.size] do
          let popH ← fileHash ref[i]!
          let mut dA : Option Float := none
          let mut dB : Option Float := none
          let mut hA := "-"
          let mut hB := "-"
          if a.ok then
            match a.rasters[i]? with
            | some png =>
              hA ← fileHash png
              dA ← dssimAgainst dir s!"{stem}-{i}-pdfium" png ref[i]!
              match dA with
              | some d => if d > dssimTolerance then
                  fx := { fx with pdfium := fx.pdfium.push s!"pdfium-dssim:p{i + 1}={fmtF d}" }
              | none => fx := { fx with pdfium := fx.pdfium.push s!"pdfium-dssim:p{i + 1}=unmeasured" }
            | none => fx := { fx with pdfium := fx.pdfium.push s!"pdfium-raster:p{i + 1}=missing" }
          if b.ok then
            match b.rasters[i]? with
            | some png =>
              hB ← fileHash png
              dB ← dssimAgainst dir s!"{stem}-{i}-pdfjs" png ref[i]!
              match dB with
              | some d => if d > dssimTolerance then
                  fx := { fx with pdfjs := fx.pdfjs.push s!"pdfjs-dssim:p{i + 1}={fmtF d}" }
              | none => fx := { fx with pdfjs := fx.pdfjs.push s!"pdfjs-dssim:p{i + 1}=unmeasured" }
            | none => fx := { fx with pdfjs := fx.pdfjs.push s!"pdfjs-raster:p{i + 1}=missing" }
          fx := { fx with dssim := fx.dssim.push (dA, dB), hashes := fx.hashes.push (popH, hA, hB) }
          hashLines := hashLines.push s!"| {stem} | {i + 1} | {popH} | {hA} | {hB} |"
          calib := calib.push s!"| {stem} | {i + 1} | {(dA.map fmtF).getD "-"} | {(dB.map fmtF).getD "-"} |"
      judged := judged.push fx
      IO.println s!"  {stem}: pdfium {if fx.pdfium.isEmpty then "pass" else String.intercalate " " fx.pdfium.toList}; pdfjs {if fx.pdfjs.isEmpty then "pass" else String.intercalate " " fx.pdfjs.toList}"
    fixtures := judged
    -- The tolerance is not vacuous: a page against another page of the
    -- same file, and a page against itself shifted down one line, must lie
    -- above it; Poppler against Ghostscript's fast-colour raster on the
    -- image page is recorded for what it measures.
    if let some fx := fixtures.find? fun f => f.name == "deck" && f.pages ≥ 3 then
      let ref ← popplerRasters dir (dir / s!"{fx.name}.pdf").toString fx.name
      if let (some p1, some p3) := (ref[0]?, ref[2]?) then
        let d ← dssimAgainst dir "neg-pages" p1 p3
        negatives := negatives.push s!"- Poppler {fx.name} page 1 against page 3: DSSIM {(d.map fmtF).getD "unmeasured"} ({if d.any (· > dssimTolerance) then "above" else "WITHIN"} the tolerance {dssimTolerance})"
    if let some fx := fixtures.find? (·.name == "paragraphs") then
      let ref ← popplerRasters dir (dir / s!"{fx.name}.pdf").toString fx.name
      if let some p1 := ref[0]? then
        let shifted := (dir / "neg-shifted.png").toString
        let px := 12 * rasterDpi / 72
        let _ ← runTool "magick" #[p1, "-roll", s!"+0+{px}", shifted]
        let d ← dssimAgainst dir "neg-shift" shifted p1
        negatives := negatives.push s!"- Poppler {fx.name} page 1 against itself rolled down one 12 pt line: DSSIM {(d.map fmtF).getD "unmeasured"} ({if d.any (· > dssimTolerance) then "above" else "WITHIN"} the tolerance)"
    if gsV.isSome then
      if let some fx := fixtures.find? (·.name == "images") then
        let ref ← popplerRasters dir (dir / s!"{fx.name}.pdf").toString fx.name
        if let some p1 := ref[0]? then
          let gsPng := (dir / "neg-gs.png").toString
          let _ ← runTool "gs" #["-q", "-dNOPAUSE", "-dBATCH", "-sDEVICE=png16m", s!"-r{rasterDpi}",
            "-dUseFastColor", "-dTextAlphaBits=1", "-dGraphicsAlphaBits=1", s!"-sOutputFile={gsPng}",
            (dir / s!"{fx.name}.pdf").toString]
          let d ← dssimAgainst dir "neg-gs" gsPng p1
          negatives := negatives.push s!"- Ghostscript -dUseFastColor, no anti-aliasing, against Poppler on {fx.name} page 1: DSSIM {(d.map fmtF).getD "unmeasured"} ({if d.any (· > dssimTolerance) then "above" else "within"} the tolerance — two conforming renderers, so within is the expected reading)"
  else
    fixtures := fixtures.map fun fx => { fx with pdfium := #["untested"], pdfjs := #["untested"] }
  for fx in fixtures do
    let verdict (xs : Array String) : String := if xs.isEmpty then "pass" else String.intercalate " " xs.toList
    record := record.push s!"| {fx.name} | {fx.pages} | {fx.tagged} | {verdict fx.poppler} | {verdict fx.ghostscript} | {verdict fx.pypdf} | {verdict fx.pdfium} | {verdict fx.pdfjs} | {String.intercalate " " fx.features} |"
  -- veraPDF over the four reference fixtures, both profiles: measured
  -- failures, recorded as cells and in the run record.
  let mut profiles : Array (String × String × String) := #[]
  let mut veraRaw : Array String := #[]
  let mut veraCore : Option String := none
  for n in profileFixtures do
    unless fixtures.any (·.name == n) do die s!"profile fixture {n} was not built"
    for (profile, flavour) in [("pdf/a-4", "4"), ("pdf/ua-2", "ua2")] do
      let cell ← if veraV.isNone then pure "untested" else do
        let v ← IO.Process.output { cmd := veraPath, args := #["-df", flavour, (dir / s!"{n}.pdf").toString] }
        let (ids, summary) := veraFailures v.stdout
        veraCore := veraCore.orElse fun _ =>
          firstWordAfter v.stdout "<releaseDetails id=\"core\" version=\"" |>.map fun w =>
            ((w.splitOn "\"").headD w)
        veraRaw := veraRaw.push s!"- {profile} {n}: {summary}"
        pure (if ids.isEmpty then (if hasStr v.stdout "isCompliant=\"true\"" then "pass" else "fail:unparsed")
          else s!"fail:{String.intercalate "," ids.toList}")
      profiles := profiles.push (profile, n, cell)
      IO.println s!"  {profile} {n}: {cell}"
  -- The feature cells: a reader passes a feature when it passed every
  -- fixture that reaches it; a feature no built fixture reaches is untested.
  let cellFor (reader : String) (feature : String) : String :=
    let reaching := fixtures.filter (·.features.contains feature)
    if reaching.isEmpty then "untested" else
    let verdictOf (fx : Fixture) : Array String := match reader with
      | "poppler" => if popplerV.isNone then #["untested"] else fx.poppler
      | "ghostscript" => if gsV.isNone then #["untested"] else fx.ghostscript
      | "pypdf" => if pypdfV.isNone then #["untested"] else fx.pypdf
      | "pdfium" => fx.pdfium
      | "pdfjs" => fx.pdfjs
      | _ => #["untested"]
    let fails := reaching.filterMap fun fx =>
      let v := verdictOf fx
      if v.isEmpty then none else some (fx.name, v)
    if fails.any (·.2 == #["untested"]) then "untested"
    else if fails.isEmpty then "pass"
    else "fail:" ++ String.intercalate "," (fails.toList.map fun (n, v) =>
      s!"{n}={String.intercalate "+" ((v.map fun s => (s.splitOn ":").headD s).toList)}")
  -- The CLI's version and the validation core's, as veraPDF reports both.
  let tools := toolsLine (veraV.map fun v => match veraCore with
    | some c => if c == v then v else s!"{v}/{c}"
    | none => v)
  let pad (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - min w s.length) ' ')
  let mut lines : Array String := #[
    "# generated by scripts/pdf-oracles.lean — do not hand-edit",
    s!"target: {String.intercalate " " targetColumns.toList}",
    s!"tools: {tools}",
    s!"date: {date}",
    "",
    "[feature]",
    pad "# feature" 20 ++ String.intercalate "  " (readerColumns.toList.map (pad · 12))]
  for f in writerFeatures do
    lines := lines.push (pad f 20 ++ String.intercalate "  " (readerColumns.toList.map fun r => pad (cellFor r f) 12))
  lines := lines.push ""
  lines := lines.push "[profile]"
  lines := lines.push (pad "# profile" 10 ++ pad "fixture" 11 ++ "verdict")
  for (p, n, cell) in profiles do
    lines := lines.push (pad p 10 ++ pad n 11 ++ cell)
  let text := String.intercalate "\n" lines.toList ++ "\n"
  let matrixPath := "testdata/oracles/reader-matrix.txt"
  let previous ← try IO.FS.readFile matrixPath catch _ => pure ""
  IO.FS.createDirAll "testdata/oracles"
  IO.FS.writeFile matrixPath text
  -- The file reads back through the gate's own parser, and the gate judges
  -- it over every feature some built fixture reaches.
  let reached := fixtures.foldl (fun acc fx => fx.features.foldl (fun acc f =>
    if acc.contains f then acc else acc.push f) acc) (#[] : Array String)
  let gaps ← match readMatrix text with
    | .error e => die s!"the written matrix does not parse: {e}"; pure #[]
    | .ok m => pure (featureGate m reached.toList)
  -- The run record.
  let diff := if previous == text then "unchanged" else if previous.isEmpty then "new file" else Id.run do
    let a := (previous.splitOn "\n").toArray
    let b := (text.splitOn "\n").toArray
    let mut out : Array String := #[]
    for i in [0:max a.size b.size] do
      let la := a[i]?.getD ""
      let lb := b[i]?.getD ""
      if la != lb then out := out.push s!"  - {la}\n  + {lb}"
    return String.intercalate "\n" out.toList
  -- The calibration summary: per renderer, the largest DSSIM and its page.
  let summarise (pick : Option Float × Option Float → Option Float) : String := Id.run do
    let mut best : Option (Float × String) := none
    let mut n := 0
    for fx in fixtures do
      for (d, i) in fx.dssim.zipIdx do
        if let some v := pick d then
          n := n + 1
          if best.all (·.1 < v) then best := some (v, s!"{fx.name} p{i + 1}")
    match best with
    | some (v, at_) => return s!"{n} pages measured, max {fmtF v} at {at_}"
    | none => return "nothing measured"
  let recordDir := "/tmp/leantex-agents/modern-output"
  IO.FS.createDirAll recordDir
  let recordPath := s!"{recordDir}/pdf-oracles-{date}.md"
  IO.FS.writeFile recordPath (String.intercalate "\n" ([
    s!"# pdf-oracles run — {date}", "",
    s!"tools: {tools}", s!"node {nodeV.getD "absent"}; magick {magickV.getD "absent"}; chrome binary {(chrome.map (·.1)).getD "absent"}; {driverNote}", "",
    s!"veraPDF --version: {(((← runTool veraPath #["--version"]).map (·.stdout)).getD "absent").trimAscii}",
    "", s!"fixtures built: {fixtures.size}; not built: {if notBuilt.isEmpty then "none" else String.intercalate ", " notBuilt.toList}",
    "", s!"typed census against the built bytes: {if censusDisagree.isEmpty then "agree on every fixture" else String.intercalate "; " censusDisagree.toList}",
    "", "| fixture | pages | Tagged | poppler | ghostscript | pypdf | pdfium | pdfjs | features |",
    "|---|---:|---|---|---|---|---|---|---|"] ++ record.toList ++ [
    "", s!"## DSSIM calibration against Poppler at {rasterDpi} dpi (tolerance {dssimTolerance})", "",
    s!"- PDFium: {summarise (·.1)}", s!"- pdf.js: {summarise (·.2)}", "",
    "### negative cases", ""] ++ negatives.toList ++ [
    "", "| fixture | page | pdfium | pdfjs |", "|---|---:|---:|---:|"] ++ calib.toList ++ [
    "", "## raster hashes (FNV-64 of the PNG; movement between runs is explained here, never committed)", "",
    "| fixture | page | poppler | pdfium | pdfjs |", "|---|---:|---|---|---|"] ++ hashLines.toList ++ [
    "", "## veraPDF raw summaries", ""] ++ veraRaw.toList ++ [
    "", "## profile cells", ""] ++ (profiles.toList.map fun (p, n, c) => s!"- {p} {n}: {c}") ++ [
    "", "## matrix diff against the checked-in file", "", diff,
    "", s!"## gate over target columns: {if gaps.isEmpty then "pass" else String.intercalate "; " gaps.toList}", ""]))
  IO.println s!"pdf-oracles: wrote {matrixPath} and {recordPath}"
  IO.FS.removeDirAll dir
  unless gaps.isEmpty do die s!"target cells not pass: {gaps}"
  IO.println "pdf-oracles: all target cells pass"
