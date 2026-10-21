/-
The cancellation oracle: lualatex against leantex's PDF and page in Chromium and Firefox on the
invented probe, read off colour-coded rasters into testdata/oracles/cancel-anchors.txt.
Usage: lake build leantex ScriptsModules && lake env lean --run scripts/cancel-diff.lean [--report | --selftest | --leantex <binary>]
-/
import scripts.CancelProbe
import scripts.Playwright
import scripts.ToolDump

open CancelProbe

/-- The raster resolution the PDFs are read at. -/
def dpi : Nat := 600

/-- A pixel's colour class: the strike's red, the value's blue, or dark operand ink. -/
inductive Paint where
  | mark
  | value
  | operand
  | none
  deriving BEq

def classify (r g b : Nat) : Paint :=
  if r ≥ 150 && g + 80 ≤ r && b + 80 ≤ r then .mark
  else if b ≥ 150 && r + 60 ≤ b && g + 60 ≤ b then .value
  else if r < 120 && g < 120 && b < 120 && max r (max g b) ≤ min r (min g b) + 40 then .operand
  else .none

def grow (box : Option Ink) (x y : Int) : Option Ink :=
  match box with
  | none => some ⟨x, y, x, y⟩
  | some b => some ⟨min b.left x, min b.top y, max b.right x, max b.bottom y⟩

/-- The three ink boxes of a binary PPM (P6, maxval 255). -/
def ppmBoxes (bytes : ByteArray) : Except String (Option Ink × Option Ink × Option Ink) := do
  -- The header is four whitespace-separated tokens.
  let mut i := 0
  let mut toks : Array String := #[]
  let mut cur := ""
  while toks.size < 4 && i < bytes.size do
    let c := Char.ofNat (bytes[i]?.getD 0).toNat
    i := i + 1
    if c.isWhitespace then
      if !cur.isEmpty then
        toks := toks.push cur
        cur := ""
    else cur := cur.push c
  let #["P6", ws, hs, "255"] := toks | throw "not a P6 PPM with maxval 255"
  let some w := ws.toNat? | throw "bad width"
  let some h := hs.toNat? | throw "bad height"
  if bytes.size < i + 3 * w * h then throw "truncated PPM"
  let mut mark : Option Ink := none
  let mut value : Option Ink := none
  let mut operand : Option Ink := none
  for y in [0:h] do
    for x in [0:w] do
      let o := i + 3 * (y * w + x)
      let at_ (k : Nat) := (bytes[k]?.getD 0).toNat
      match classify (at_ o) (at_ (o + 1)) (at_ (o + 2)) with
      | .mark => mark := grow mark x y
      | .value => value := grow value x y
      | .operand => operand := grow operand x y
      | .none => pure ()
  return (mark, value, operand)

/-- The browser side, run by node with Playwright in `PW_MODULE`: each formula of the page shot
at four device pixels per CSS pixel with the others hidden, its colour classes' ink boxes read off
the shot. -/
def probeJs : String := r#"
const pw = require(process.env.PW_MODULE);
(async () => {
  const b = await pw.chromium.launch({ headless: true, args: ['--no-sandbox', '--disable-gpu'] });
  const p = await b.newPage({ viewport: { width: 1200, height: 900 }, deviceScaleFactor: 4 });
  await p.goto('file://' + process.argv[2], { waitUntil: 'domcontentloaded' });
  await p.evaluate(() => document.fonts.ready);
  const maths = await p.$$('math');
  for (const [i, m] of maths.entries()) {
    // Only this formula paints, shot with three ems around its box for what overhangs it.
    const fs = await m.evaluate(e => parseFloat(getComputedStyle(e).fontSize));
    await p.evaluate((i) => document.querySelectorAll('math').forEach((e, k) =>
      e.style.visibility = k === i ? 'visible' : 'hidden'), i);
    await m.scrollIntoViewIfNeeded();
    const r = await m.boundingBox();
    const pad = 3 * fs;
    const shot = await p.screenshot({ type: 'png', clip: { x: Math.max(0, r.x - pad),
      y: Math.max(0, r.y - pad), width: r.width + 2 * pad, height: r.height + 2 * pad } });
    const boxes = await p.evaluate(async (src) => {
      const img = new Image(); img.src = 'data:image/png;base64,' + src; await img.decode();
      const c = document.createElement('canvas'); c.width = img.width; c.height = img.height;
      const g = c.getContext('2d'); g.drawImage(img, 0, 0);
      const d = g.getImageData(0, 0, c.width, c.height).data;
      const box = { mark: null, value: null, operand: null };
      const grow = (k, x, y) => { const q = box[k];
        box[k] = q ? [Math.min(q[0], x), Math.min(q[1], y), Math.max(q[2], x), Math.max(q[3], y)] : [x, y, x, y]; };
      for (let y = 0; y < c.height; y++) for (let x = 0; x < c.width; x++) {
        const o = 4 * (y * c.width + x), r = d[o], gr = d[o + 1], bl = d[o + 2];
        if (r >= 150 && gr + 80 <= r && bl + 80 <= r) grow('mark', x, y);
        else if (bl >= 150 && r + 60 <= bl && gr + 60 <= bl) grow('value', x, y);
        else if (r < 120 && gr < 120 && bl < 120 && Math.max(r, gr, bl) <= Math.min(r, gr, bl) + 40) grow('operand', x, y);
      }
      return box;
    }, shot.toString('base64'));
    const f = (q) => q ? q.join(' ') : '-';
    console.log(['math', Math.round(fs * 4), f(boxes.mark), f(boxes.value), f(boxes.operand)].join('\t'));
  }
  await b.close();
})().catch(e => { console.error(String(e.message).split('\n')[0]); process.exit(1); });
"#

def inkOf (s : String) : Option Ink := do
  let [l, t, r, b] := (s.splitOn " ").filterMap String.toInt? | none
  return ⟨l, t, r, b⟩

/-- One `math` line of the browser probe: em, mark, value, operand. -/
def parseMathLine (line : String) : Option Boxes := do
  let ["math", em, m, v, o] := line.splitOn "\t" | none
  return { em := ← em.toInt?, mark := ← inkOf m, value := inkOf v, operand := ← inkOf o }

def run (cmd : String) (args : Array String) (cwd : System.FilePath := ".")
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd, env }

/-- Each page's boxes in a PDF of `pages` pages, the em being 10 pt at `dpi`. -/
def pdfBoxes (pdf : System.FilePath) (pages : Nat) (work : System.FilePath) :
    IO (Except String (Array Boxes)) := do
  let em : Int := (10 * dpi * 100 / 7227 : Nat)
  let mut out : Array Boxes := #[]
  for n in [1:pages+1] do
    let stem := work / s!"page{n}"
    let r ← run "pdftoppm" #["-r", toString dpi, "-f", toString n, "-l", toString n,
      "-singlefile", pdf.toString, stem.toString]
    if r.exitCode != 0 then return .error s!"pdftoppm exited {r.exitCode} on {pdf} page {n}"
    let ppm := stem.addExtension "ppm"
    let t ← run "magick" #[ppm.toString, "-trim", "+repage", ppm.toString]
    if t.exitCode != 0 then return .error s!"magick exited {t.exitCode} on {ppm}"
    let bytes ← IO.FS.readBinFile ppm
    IO.FS.removeFile ppm
    match ppmBoxes bytes with
    | .error e => return .error s!"{pdf} page {n}: {e}"
    | .ok (some mark, value, some operand) => out := out.push { em, mark, value, operand }
    | .ok _ => return .error s!"{pdf} page {n}: no strike or no operand ink"
  return .ok out

/-- A page showing only its `k`th paragraph, its root size four times the default, since Firefox's
headless shot takes no device scale and clips an SVG inside MathML under CSS zoom. -/
def soloPage (html : String) (k : Nat) : String :=
  let css := s!"<style>:root \{ font-size: 400% } main > p \{ display: none } \
main > p:nth-of-type({k + 1}) \{ display: block }</style></head>"
  match html.splitOn "</head>" with
  | head :: rest => head ++ css ++ "</head>".intercalate rest
  | [] => html

/-- One Firefox shot of `page`, its own profile under `work`, trimmed to its ink and read as a PPM. -/
def firefoxShot (page : System.FilePath) (work : System.FilePath) (stem : String) :
    IO (Except String (Option Ink × Option Ink × Option Ink)) := do
  let png := work / s!"{stem}.png"
  let ppm := work / s!"{stem}.ppm"
  let url := s!"file://{(← IO.FS.realPath page).toString}"
  let shot := (← IO.FS.realPath work) / s!"{stem}.png"
  -- A headless start now and then hangs, so each try is bounded and retried on a fresh profile.
  let mut code : UInt32 := 0
  for attempt in [0:3] do
    let profile := work / s!"ff-profile-{stem}-{attempt}"
    IO.FS.createDirAll profile
    let r ← run "timeout" #["60", "firefox", "--headless", "--no-remote", "--profile",
      (← IO.FS.realPath profile).toString, "--screenshot", shot.toString,
      "--window-size=2400,1600", url]
    IO.FS.removeDirAll profile
    code := r.exitCode
    if code == 0 && (← png.pathExists) then break
  unless ← png.pathExists do
    return .error s!"firefox exited {code} on {page}"
  let c ← run "magick" #[png.toString, "-trim", "+repage", "-depth", "8", ppm.toString]
  IO.FS.removeFile png
  if c.exitCode != 0 then return .error s!"magick exited {c.exitCode} on {png}"
  let bytes ← IO.FS.readBinFile ppm
  IO.FS.removeFile ppm
  return ppmBoxes bytes

/-- Each case of a page in Firefox, one start at a time since simultaneous headless starts wedge
one another, at the em Chromium measured for it. -/
def firefoxBoxes (html : System.FilePath) (ems : Array Int) (work : System.FilePath)
    (tag : String) : IO (Except String (Array Boxes)) := do
  let text ← IO.FS.readFile html
  let mut out : Array Boxes := #[]
  for k in [0:ems.size] do
    let page := work / s!"ff-{tag}-{k}.html"
    IO.FS.writeFile page (soloPage text k)
    let shot ← firefoxShot page work s!"ff-{tag}-{k}"
    IO.FS.removeFile page
    match shot with
    | .error e => return .error e
    | .ok (some mark, value, some operand) =>
      out := out.push { em := ems[k]?.getD 0, mark, value, operand }
    | .ok _ => return .error s!"firefox {tag} case {k}: no strike or no operand ink"
  return .ok out

def selftest : IO UInt32 := Scoreboard.tierSelftest "cancel-diff" fun no => do
  no "classify: pure red, blue and black" (classify 255 0 0 == .mark &&
    classify 0 0 255 == .value && classify 20 20 20 == .operand && classify 250 250 245 == .none)
  no "classify: a grey antialiased edge is neither colour" (classify 180 160 160 == .none)
  let ppm := "P6\n3 2\n255\n".toUTF8 ++ ByteArray.mk #[255,255,255, 255,0,0, 255,255,255,
    0,0,255, 255,255,255, 10,10,10]
  no "ppm: boxes of each class"
    (match ppmBoxes ppm with
     | .ok (some m, some v, some o) => m == ⟨1, 0, 1, 0⟩ && v == ⟨0, 1, 0, 1⟩ && o == ⟨2, 1, 2, 1⟩
     | _ => false)
  no "ppm: a truncated raster is refused" ((ppmBoxes ("P6\n3 2\n255\n".toUTF8)).toOption.isNone)
  no "browser line: read back"
    ((parseMathLine "math\t64\t1 2 30 40\t-\t5 6 25 35").any fun b =>
      b.em == 64 && b.value.isNone && b.mark == ⟨1, 2, 30, 40⟩)
  let a : Anchors :=
    { left := -10, bottom := 5, right := 20, top := 0, valueX := some 30, valueY := some 40 }
  no "row: renders and parses back" (parseRow (renderRow "x-mk" "pdf" a) == some ("x-mk", "pdf", a))
  no "gap: the largest anchor difference"
    (a.gap { a with right := 70 } == some 50 && (a.gap { a with valueX := none }).isNone)
  no "judge: a case passes within tolerance and fails past it"
    (judge #[("x", "pdf", a), ("x", "lualatex", { a with top := 100 })] "pdf" "lualatex" 100
        == (1, 1) &&
      judge #[("x", "pdf", a), ("x", "lualatex", { a with top := 101 })] "pdf" "lualatex" 100
        == (0, 1))

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return (← selftest)
  let own : System.FilePath := ".lake" / "build" / "bin" / "leantex"
  let other := match args.dropWhile (· != "--leantex") with
    | _ :: p :: _ => some (System.FilePath.mk p)
    | _ => none
  let reportOnly := args.contains "--report" || other.isSome
  unless ← (other.getD own).pathExists do
    IO.eprintln "cancel-diff: build leantex first (lake build leantex)"
    return 2
  let leantex ← IO.FS.realPath (other.getD own)
  for (cmd, probe) in [("lualatex", #["--version"]), ("pdftoppm", #["-v"]), ("node", #["--version"]),
      ("firefox", #["--version"]), ("magick", #["-version"])] do
    if (← toolVersion cmd probe ".") == "unavailable" then
      IO.eprintln s!"cancel-diff: {cmd} not available — untested"
      return 2
  let some (module, chromium) ← findChromium "node"
    | IO.eprintln "cancel-diff: no Playwright module launches Chromium — untested"; return 2
  let work : System.FilePath := ".lake" / "cancel-diff"
  if ← work.pathExists then IO.FS.removeDirAll work
  IO.FS.createDirAll work
  let fontDir := (← IO.FS.realPath ("testdata" / "corpus" / "fonts")).toString
  let key ← match ← buildKey leantex with
    | .ok k => pure k
    | .error e => IO.eprintln s!"cancel-diff: {e}"; return 1
  let js := work / "probe.js"
  IO.FS.writeFile js probeJs
  let mut rows : Array String := #[]
  let pages := cases.length
  for (tag, opt) in rooms do
    let tex := work / s!"lua-{tag}.tex"
    IO.FS.writeFile tex (luaSource fontDir opt)
    let r ← run "lualatex" #["-interaction=nonstopmode", "-halt-on-error",
      s!"-output-directory={work}", tex.toString]
    if r.exitCode != 0 then
      IO.eprintln s!"cancel-diff: lualatex failed on {tex}"; return 1
    let lua ← pdfBoxes (work / s!"lua-{tag}.pdf") pages work
    let pdf ← pdfBoxes (probeDir / s!"lean-{tag}.pdf") pages work
    let html ← run "node" #[js.toString, (← IO.FS.realPath (probeDir / s!"lean-{tag}.html")).toString]
      (env := #[("PW_MODULE", some module)])
    if html.exitCode != 0 then
      IO.eprintln s!"cancel-diff: the browser probe failed: {html.stderr.trimAscii}"; return 1
    let web := ((html.stdout.splitOn "\n").filterMap parseMathLine).toArray
    let ff ← firefoxBoxes (probeDir / s!"lean-{tag}.html") (web.map (·.em)) work tag
    match lua, pdf, ff with
    | .ok lua, .ok pdf, .ok ff =>
      if lua.size != pages || pdf.size != pages || web.size != pages || ff.size != pages then
        IO.eprintln s!"cancel-diff: {tag}: {lua.size}, {pdf.size}, {web.size} and {ff.size} cases \
measured, {pages} expected"
        return 1
      for (((c, l), (p, h)), f) in ((cases.toArray.zip lua).zip (pdf.zip web)).zip ff do
        let label := s!"{c.label}-{tag}"
        for (engine, b) in [("lualatex", l), ("pdf", p), ("chromium", h), ("firefox", f)] do
          rows := rows.push (renderRow label engine b.anchors)
    | .error e, _, _ | _, .error e, _ | _, _, .error e => IO.eprintln s!"cancel-diff: {e}"; return 1
  let parsed := rows.filterMap parseRow
  for r in rows do IO.println s!"  {r}"
  for (engine, against, tol) in judgements do
    let (n, d) := judge parsed engine against tol
    IO.println s!"cancel-diff: {engine} within {tol}‰ em of {against}: {n}/{d}"
  if reportOnly then return 0
  let lv ← toolVersion "lualatex" #["--version"] "."
  let pv ← toolVersion "pdftoppm" #["-v"] "."
  let text := "# generated by scripts/cancel-diff.lean — do not hand-edit; regenerate: \
lake env lean --run scripts/cancel-diff.lean\n" ++
    s!"tools: {lv.trimAscii}; {pv.trimAscii}; chromium {chromium} (playwright {← moduleVersion module}); \
{(← toolVersion "firefox" #["--version"] ".").trimAscii}\n" ++
    s!"src-key: {key}\n" ++
    "# <case>-<room> <engine> <left> <bottom> <right> <top> <valueX> <valueY>, thousandths of an em: \
the strike's ink edges past the operand's, the value's left past its right and bottom above its bottom\n" ++
    String.intercalate "\n" rows.toList ++ "\n"
  IO.FS.writeFile oraclePath text
  IO.println s!"cancel-diff: wrote {oraclePath}"
  return 0
