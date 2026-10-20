/-
HTML artifact oracle: every corpus page probed in the host's cached Playwright Chromium, one
cell per feature and fixture × reader in testdata/oracles/html-reader-matrix.txt.
Usage: lake build && lake env lean --run scripts/html-oracle.lean [--check [path] | --selftest | --load-check [probe.cjs]]
-/
import LeanTex
import scripts.Board
import scripts.Playwright

open LeanTex.Core

def matrixPath : String := "testdata/oracles/html-reader-matrix.txt"
def shapesPath : String := "testdata/oracles/stage-shapes.txt"
def mystPath : String := "testdata/oracles/myst-themes.tsv"
def leantexBin : String := ".lake/build/bin/leantex"

/-- The readers the matrix declares as targets, declared by the file, not by what a host
has installed. -/
def targetReaders : List String := ["chromium"]

/-- Every reader the probe knows how to drive, in column order. -/
def readers : List String := ["chromium", "firefox"]

/-- The feature rows, in the order the probe emits them. -/
def features : List String :=
  ["load", "images", "fonts", "mathml", "mathAlpha", "math-line", "lang", "landmarks", "snaps",
   "box-side",
   "affine-screen", "affine-print", "color-scheme", "reduced-motion", "print", "print-spill",
   "print-sheets", "no-script", "code-height", "stage-fit", "stage-focus", "deck-links",
   "disclosure",
   "print-disclosure", "code-wrap", "print-code", "web-layout"]

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

def padRight (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

def hasCmd (cmd : String) : IO Bool := do
  try
    return (← IO.Process.output { cmd, args := #["--version"] }).exitCode == 0
  catch _ => return false

/-- The reader the print judgements read paper with: `pdftotext -v`'s first line, or
`pdftotext absent`. -/
def pdftotextVersion : IO String := do
  try
    let out ← IO.Process.output { cmd := "pdftotext", args := #["-v"] }
    let line := (((out.stderr ++ out.stdout).splitOn "\n").headD "").trimAscii.toString
    return if line.isEmpty then "pdftotext absent" else line
  catch _ => return "pdftotext absent"

/-- First version line of a host-only converter, or an explicit absence. -/
def toolVersion (tool : String) (args : Array String) : IO String := do
  try
    let out ← IO.Process.output { cmd := tool, args }
    let line := (((out.stdout ++ out.stderr).splitOn "\n").find? (!·.trimAscii.isEmpty)).getD ""
      |>.trimAscii.toString
    return if out.exitCode == 0 && !line.isEmpty then line else tool ++ " absent"
  catch _ => return tool ++ " absent"

/-- One section of the matrix: its name, its reader columns, and its rows
(key, then one cell per column; trailing columns are data). -/
structure Section where
  name : String
  columns : Array String
  rows : Array (String × Array String)

structure Matrix where
  target : Array String
  sections : Array Section

/-- Parse the matrix text: `#` lines are comments, except that the first one after a
`[section]` header names the columns. -/
def parseMatrix (text : String) : Except String Matrix := do
  let mut target : Array String := #[]
  let mut sections : Array Section := #[]
  let mut cur : Option Section := none
  let mut sawTarget := false
  for raw in text.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty then continue
    if l.startsWith "target:" then
      target := ((l.drop "target:".length).toString.splitOn " ").filter (!·.isEmpty) |>.toArray
      sawTarget := true
    else if l.startsWith "[" && l.endsWith "]" then
      if let some s := cur then sections := sections.push s
      cur := some { name := ((l.drop 1).toString.dropEnd 1).toString, columns := #[], rows := #[] }
    else if l.startsWith "#" then
      if let some s := cur then
        if s.columns.isEmpty then
          let toks := ((l.drop 1).toString.splitOn " ").filter (!·.isEmpty)
          cur := some { s with columns := (toks.drop 1).toArray }
    else if let some s := cur then
      let toks := (l.splitOn " ").filter (!·.isEmpty) |>.toArray
      if toks.isEmpty then continue
      if s.columns.isEmpty then throw s!"[{s.name}]: a row before the column header"
      if toks.size < s.columns.size + 1 then
        throw s!"[{s.name}] {toks[0]!}: {toks.size - 1} cells for {s.columns.size} columns"
      cur := some { s with rows := s.rows.push (toks[0]!, (toks.extract 1 (s.columns.size + 1))) }
  if let some s := cur then sections := sections.push s
  if !sawTarget then throw "no `target:` line"
  if sections.isEmpty then throw "no sections"
  return { target, sections }

/-- A cell whose wait's budget ended while the page still changed, or whose tool or probe the
machine stopped: neither a pass nor a failure. -/
def inconclusive (v : String) : Bool := v.startsWith "inconclusive:"

/-- The gate: every cell under a `target:` reader is `pass`; returns the offending cells,
a target reader missing from a section's columns among them. -/
def offences (m : Matrix) : Array String := Id.run do
  let mut out : Array String := #[]
  for s in m.sections do
    if s.rows.isEmpty then out := out.push s!"[{s.name}]: no rows"
    for t in m.target do
      match s.columns.idxOf? t with
      | none => out := out.push s!"[{s.name}]: target reader {t} has no column"
      | some i =>
        for (key, cells) in s.rows do
          let c := cells[i]!
          if c != "pass" then out := out.push s!"[{s.name}] {key} / {t} = {c}"
  return out

def checkFile (path : String) : IO UInt32 := do
  if !(← System.FilePath.pathExists path) then
    return (← die 2 s!"html-oracle: {path} is missing; regenerate it")
  let text ← IO.FS.readFile path
  let keys ← match ← Scoreboard.hermeticHtmlKeys with
    | .ok keys => pure keys
    | .error e => return (← die 2 s!"html-oracle: cannot rebuild freshness keys: {e}")
  match parseMatrix text with
  | .error e => die 2 s!"html-oracle: {path}: {e}"
  | .ok m =>
    let bad := offences m ++ (Scoreboard.browserFaceFaults text keys.browserFaceSource keys.expectedFaces).map
      ("browser-face: " ++ ·)
    if bad.isEmpty then
      IO.println s!"html-oracle: every target cell and browser-face capture passes ({String.intercalate " " m.target.toList})"
      return 0
    IO.println s!"html-oracle: {bad.size} target or browser-face checks not passing in {path}:"
    for b in bad do IO.println s!"  {b}"
    if bad.any fun b => inconclusive ((b.splitOn " = ").getLastD "") then
      IO.println "html-oracle: an inconclusive cell is a page still changing when its wait's budget \
ended, or a tool the machine stopped: rerun on a quieter host or with a larger HARD_TIMEOUT_MS"
    return 1

/-- The browser-side probe, run by node with the Playwright module in `PW_MODULE`: one line per
(fixture, reader, feature), `pass`, `fail:<reason>`, `inconclusive:<reason>` or `na`, read off the
live page, plus `reader` lines with the tool facts and a `budget` or `unfinished` line if it stops. -/
def probeJs : String := r#"
const path = require('path');
const { execFileSync } = require('child_process');
const pw = require(process.env.PW_MODULE);
const dir = process.argv[2];
const fixtures = process.argv.slice(3);
const out = (...cols) => console.log(cols.join('\t'));
const clean = (s) => String(s).replace(/\s+/g, ' ').trim();

// The run's budget; each wait has a tenth of it, and one that runs out is inconclusive.
const HARD_MS = +(process.env.HARD_TIMEOUT_MS || 900000);
const STEP_MS = Math.ceil(HARD_MS / 10);
const watchdog = setTimeout(() => { out('budget', String(HARD_MS)); process.exit(4); }, HARD_MS);
class Unfinished extends Error {}
const unfinished = (e) => e instanceof Unfinished || e instanceof pw.errors.TimeoutError;
const budgeted = (ctx) => {
  ctx.setDefaultTimeout(STEP_MS);
  ctx.setDefaultNavigationTimeout(STEP_MS);
  return ctx;
};
// A frame the browser draws, asked again within the step budget while it cannot draw one yet.
const drawn = async (page) => {
  const end = Date.now() + STEP_MS;
  for (;;) {
    try { return await page.screenshot(); } catch (e) {
      if (unfinished(e) || page.isClosed() || Date.now() >= end)
        throw new Unfinished('no frame drawn: ' + clean(String(e.message).split('\n')[0]));
      await new Promise(r => setTimeout(r, STEP_MS / 100));
    }
  }
};
// A tool's text output, or a loss that is the machine's when the tool outran the step budget.
const toolText = (cmd, args) => {
  try { return execFileSync(cmd, args, { encoding: 'utf8', timeout: STEP_MS }); } catch (e) {
    const why = cmd + ': ' + clean(String(e.message).split('\n')[0]);
    if (e.code === 'ETIMEDOUT' || e.signal) throw new Unfinished(why);
    throw new Error(why);
  }
};

const hexToRgb = (h) => {
  const m = /^#([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})$/i.exec(h.trim());
  return m ? `rgb(${parseInt(m[1], 16)}, ${parseInt(m[2], 16)}, ${parseInt(m[3], 16)})` : h.trim();
};
// The engine's own token set: light ink, light surface, dark ink, dark surface.
const [lightInk, lightSurface, darkInk, darkSurface] = (process.env.LT_TOKENS || '').split(/\s+/).map(hexToRgb);

// Every check runs inside the page and returns {ok, n, why}; n = 0 means
// the fixture does not exercise the feature.
const checks = {
  'code-height': () => {
    const boxes = [...document.querySelectorAll('section.slide pre')]
      .filter(p => p.getBoundingClientRect().width > 0);
    const bad = boxes.filter(p => p.scrollHeight > p.clientHeight + 1);
    return { ok: bad.length === 0, n: boxes.length,
      why: bad.length ? `${bad.length} code boxes hide lines inside the slide` : '' };
  },
  images: () => {
    const imgs = [...document.images];
    const bad = imgs.filter(i => !(i.complete && i.naturalWidth > 0 && i.naturalHeight > 0
      && (!i.getAttribute('width') || +i.getAttribute('width') === i.naturalWidth)
      && (!i.getAttribute('height') || +i.getAttribute('height') === i.naturalHeight)));
    return { ok: bad.length === 0, n: imgs.length,
      why: bad.length ? `${bad.length}/${imgs.length} images not loaded at their declared natural size: ${bad[0].getAttribute('src')} natural ${bad[0].naturalWidth}x${bad[0].naturalHeight} declared ${bad[0].getAttribute('width')}x${bad[0].getAttribute('height')}` : '' };
  },
  fonts: async () => {
    await document.fonts.ready;
    const faces = [...document.fonts];
    const st = await Promise.all(faces.map(f => f.load().then(() => f.status, () => f.status)));
    const badIdx = st.findIndex(s => s !== 'loaded');
    const fams = [...new Set(faces.map(f => f.family.replace(/^"|"$/g, '')))];
    const unchecked = fams.filter(f => !document.fonts.check(`16px "${f}"`));
    return { ok: badIdx < 0 && unchecked.length === 0, n: faces.length,
      why: badIdx >= 0 ? `face ${faces[badIdx].family} ${faces[badIdx].weight} ${faces[badIdx].style} status ${st[badIdx]}`
         : unchecked.length ? `fonts.check false for ${unchecked.join(',')}` : '' };
  },
  mathml: () => {
    const ms = [...document.querySelectorAll('math')];
    const bad = ms.filter(m => {
      // MathML Core mpadded may reserve zero height/depth while its
      // contents still paint. Measure those contents, not the carrier.
      const range = document.createRange();
      range.selectNodeContents(m);
      const r = range.getBoundingClientRect();
      return !(m.namespaceURI === 'http://www.w3.org/1998/Math/MathML' && r.width > 0 && r.height > 0);
    });
    return { ok: bad.length === 0, n: ms.length,
      why: bad.length ? `${bad.length}/${ms.length} <math> with empty rendered contents or outside the MathML namespace` : '' };
  },
  // A text-sourced math alphabet projects to real CSS, because Chromium (and
  // WebKit) honour no non-`normal` mathvariant: so the leaf's COMPUTED
  // family/weight/style must be the slot's, not the surrounding math font.
  // Every styled leaf carries `font-family: var(--font-*)` inline; here the
  // computed family must equal that variable's own resolved value (the inline
  // rule beat `math { font-family: var(--font-math) }`), the computed weight
  // must be 700 exactly when the inline style asked for it, the computed
  // style italic exactly when it did, and the shown scalar must stay the
  // literal base character (ASCII), never a Mathematical Alphanumeric remap.
  mathAlpha: () => {
    const norm = (s) => String(s).replace(/["']/g, '').replace(/\s+/g, ' ').trim().toLowerCase();
    const leaves = [...document.querySelectorAll('math mi[style*="--font-"], math mn[style*="--font-"]')];
    const bad = [];
    for (const el of leaves) {
      const cs = getComputedStyle(el);
      const m = /var\((--font-[a-z]+)\)/.exec(el.style.fontFamily || el.getAttribute('style') || '');
      const wantFam = m ? norm(cs.getPropertyValue(m[1])) : '';
      const gotFam = norm(cs.fontFamily);
      const wantWeight = (el.style.fontWeight || '400');
      const wantStyle = (el.style.fontStyle || 'normal');
      const text = el.textContent || '';
      const cp = text.codePointAt(0);
      const ok = m && wantFam.length > 0 && gotFam === wantFam
        && String(cs.fontWeight) === String(wantWeight)
        && cs.fontStyle === wantStyle
        && [...text].length === 1 && cp < 0x80;
      if (!ok) bad.push(`${el.tagName.toLowerCase()} '${text}' family ${gotFam} want ${wantFam} weight ${cs.fontWeight} want ${wantWeight} style ${cs.fontStyle} want ${wantStyle} cp ${cp}`);
    }
    return { ok: bad.length === 0, n: leaves.length,
      why: bad.length ? `${bad.length}/${leaves.length} styled math leaves off: ${bad[0]}` : '' };
  },
  lang: () => {
    const l = document.documentElement.lang;
    return { ok: /^[a-zA-Z]{2,3}(-[a-zA-Z0-9]+)*$/.test(l), n: 1, why: `html lang=${JSON.stringify(l)}` };
  },
  landmarks: () => {
    const mains = document.querySelectorAll('main').length;
    const h1 = document.querySelectorAll('h1').length;
    return { ok: mains === 1 && h1 <= 1, n: 1, why: `main x${mains} h1 x${h1}` };
  },
  // A deck: the snap points the stylesheet declares are exactly the ones
  // the browser computes, each on the pager's grid of whole viewports, and
  // the scroll space is exactly one viewport per snap: anything else in the
  // row, as a heading between two stages, moves every later stage off it.
  snaps: async () => {
    const root = getComputedStyle(document.documentElement);
    if (!/mandatory/.test(root.scrollSnapType)) return { ok: true, n: 0, why: '' };
    await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
    const declared = document.querySelectorAll('[data-snap]').length;
    const points = [...document.querySelectorAll('*')]
      .filter(e => /^start/.test(getComputedStyle(e).scrollSnapAlign)
        && getComputedStyle(e).display !== 'none');
    const vw = window.innerWidth;
    const off = points.map(e => e.getBoundingClientRect().left + window.scrollX)
      .filter(x => Math.abs(x - Math.round(x / vw) * vw) > 0.5);
    const spare = document.scrollingElement.scrollWidth - declared * vw;
    const ok = declared > 0 && points.length === declared && off.length === 0 &&
      Math.abs(spare) <= 1;
    return { ok, n: 1, why: `data-snap x${declared} computed-start x${points.length} ` +
      `off-grid x${off.length} spare ${Math.round(spare)}px` };
  },
  // A box its scope sets stands on the scope's side, as TeX sets a box in a
  // line — a table or a lone minipage under `.centered` on the scope's
  // centre, under `.ragged-right` on its right edge — and a centred
  // headline's matter on its band's centre: within half a CSS pixel, read
  // off the layout boxes, against the scope's content box.
  'box-side': () => {
    const outer = (el) => { const r = el.getBoundingClientRect(); return [r.left, r.right]; };
    const inner = (el) => {
      const r = el.getBoundingClientRect(), s = getComputedStyle(el);
      return [r.left + parseFloat(s.paddingLeft) + parseFloat(s.borderLeftWidth),
        r.right - parseFloat(s.paddingRight) - parseFloat(s.borderRightWidth)];
    };
    const sideOf = (el) => el.classList.contains('centered') ? 'center' : 'right';
    const off = [];
    let n = 0;
    const judge = (what, [l, r], [fl, fr], side) => {
      n++;
      const d = side === 'center' ? (l + r - fl - fr) / 2 : r - fr;
      if (Math.abs(d) > 0.5) off.push(`${what} ${d.toFixed(2)}px off the ${side === 'center' ? 'centre' : 'right edge'}`);
    };
    for (const t of document.querySelectorAll('.centered > table, .ragged-right > table'))
      judge('table', outer(t), inner(t.parentElement), sideOf(t.parentElement));
    for (const row of document.querySelectorAll('.centered > .columns, .ragged-right > .columns')) {
      const boxes = row.querySelectorAll(':scope > .column');
      if (boxes.length === 1) judge('lone box', outer(boxes[0]), inner(row), sideOf(row.parentElement));
    }
    for (const m of document.querySelectorAll('body > header.headline > .headline-matter'))
      if (getComputedStyle(m).textAlign === 'center')
        judge('headline matter', outer(m), inner(m.parentElement), 'center');
    return { ok: off.length === 0, n, why: off.join('; ') };
  },
  // A disclosure is the platform's own: on screen a closed one shows its
  // summary alone and an open one its body too, and its summary opens and
  // closes it. Each is put back as it stood. One the page does not show —
  // inside a closed disclosure, or a hidden alternative — is judged where
  // it is shown, never here.
  disclosure: async () => {
    const frame = () => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
    const ds = [...document.querySelectorAll('details')];
    const body = (d) => [...d.children].filter(c => c.tagName !== 'SUMMARY');
    const shown = (d) => body(d).every(c => c.checkVisibility());
    const bad = [];
    for (const d of ds) {
      if (!d.checkVisibility()) continue;
      const s = d.querySelector(':scope > summary');
      if (!s || !s.checkVisibility()) { bad.push('summary not shown'); continue; }
      const was = d.open;
      if (body(d).length && shown(d) !== was) bad.push(was ? 'open hides its body' : 'closed shows its body');
      s.click(); await frame();
      if (d.open === was || (body(d).length && shown(d) === was)) bad.push('summary does not toggle');
      s.click(); await frame();
      if (d.open !== was) bad.push('not restored');
    }
    return { ok: bad.length === 0, n: ds.length > 0 ? 1 : 0,
      why: `${ds.length} disclosures` + (bad.length ? ': ' + [...new Set(bad)].join(', ') : '') };
  },
};

// A CSS-pixel half is the declared browser bound: deviceScaleFactor=1,
// Chromium's layout boxes are quantized below it, while a wrong ancestor in
// this fixture differs by tens of pixels. Every expected value is recomputed
// from the semantic owner's live content box, never from the emitted cqi text.
const affineGeometry = () => {
  const bound = 0.5;
  const top = document.querySelector('.u-affinetop');
  if (!top) return { ok: true, n: 0, why: '' };
  const pt = n => n * 96 / 72.27; // the fixture's TeX points, in CSS px
  const num = (style, property) => parseFloat(style.getPropertyValue(property));
  const contentWidth = el => {
    const r = el.getBoundingClientRect(), s = getComputedStyle(el);
    return r.width - num(s, 'padding-left') - num(s, 'padding-right')
      - num(s, 'border-left-width') - num(s, 'border-right-width');
  };
  const specs = [
    ['top', '.u-affinetop', role => document.querySelector('main'), null],
    ['minipage', '.u-affinemini', role => role.closest('.column'), pt(240)],
    ['column', '.u-affinecolumn', role => role.closest('.column'), pt(180)],
    ['p-cell', '.u-affinepcell', role => role.closest('td'), pt(140)],
    ['target-cell', '.u-affinexcell', role => role.closest('td'), pt(220)],
  ];
  const offences = [], measured = [];
  const judge = (where, property, got, want) => {
    if (!Number.isFinite(got) || Math.abs(got - want) > bound) {
      const shown = Number.isFinite(got) ? got.toFixed(3) : String(got);
      offences.push(`${where} ${property} ${shown}px, expected ${want.toFixed(3)}px`);
    }
  };
  for (const [name, selector, ownerOf, target] of specs) {
    const role = document.querySelector(selector), owner = role && ownerOf(role);
    const font = role && role.querySelector('[style*="font-size"]');
    const room = role && role.querySelector('[style*="margin-inline-start"]');
    const left = role && role.querySelector('.u-affineleft');
    const right = role && role.querySelector('.u-affineright');
    const rule = role && role.querySelector('[style*="inline-size"]');
    if (!(role && owner && font && room && left && right && rule)) {
      offences.push(`${name} is missing its role, owner, font, hspace markers, or rule box`);
      continue;
    }
    const width = contentWidth(owner), fs = getComputedStyle(font);
    const rs = getComputedStyle(rule);
    const leftBox = left.getBoundingClientRect(), rightBox = right.getBoundingClientRect();
    const values = {
      fontSize: num(fs, 'font-size'), lineHeight: num(fs, 'line-height'),
      hspace: rightBox.left - leftBox.right, ruleWidth: num(rs, 'inline-size'),
      ruleHeight: num(rs, 'block-size'), ruleRaise: num(rs, 'vertical-align'),
    };
    judge(name, 'font-size', values.fontSize, 0.10 * width + pt(2));
    judge(name, 'line-height', values.lineHeight, 0.12 * width + pt(3));
    judge(name, 'hspace', values.hspace, 0.20 * width + pt(3));
    judge(name, 'rule width', values.ruleWidth, 0.25 * width - pt(2));
    judge(name, 'rule height', values.ruleHeight, 0.02 * width + pt(1));
    judge(name, 'rule raise', values.ruleRaise, 0.01 * width + pt(1));
    if (target !== null) judge(name, 'owner width', width, target);
    measured.push(`${name} owner=${width.toFixed(2)} font=${values.fontSize.toFixed(2)} line=${values.lineHeight.toFixed(2)} hspace=${values.hspace.toFixed(2)} rule=${values.ruleWidth.toFixed(2)}x${values.ruleHeight.toFixed(2)}+${values.ruleRaise.toFixed(2)}`);
  }
  const widths = specs.map(([, selector, ownerOf]) => {
    const role = document.querySelector(selector);
    return role && ownerOf(role) ? contentWidth(ownerOf(role)) : 0;
  });
  if (Math.max(...widths) - Math.min(...widths) < 40)
    offences.push('the fixture owners are not distinct enough to expose an ancestor binding');
  return { ok: offences.length === 0, n: measured.length,
    why: offences.length ? offences.join('; ') + `; measured ${measured.join(' | ')}` : measured.join(' | ') };
};
checks['affine-screen'] = affineGeometry;

const readColors = () => {
  const b = getComputedStyle(document.body);
  return { bg: b.backgroundColor, fg: b.color,
    scheme: getComputedStyle(document.documentElement).colorScheme,
    deck: /mandatory/.test(getComputedStyle(document.documentElement).scrollSnapType) };
};

// WCAG 2.2 relative luminance and contrast ratio over computed rgb() values.
const luminance = (rgb) => {
  const m = /rgba?\((\d+), (\d+), (\d+)/.exec(rgb);
  if (!m) return NaN;
  const c = [m[1], m[2], m[3]].map(v => { const x = v / 255; return x <= 0.03928 ? x / 12.92 : ((x + 0.055) / 1.055) ** 2.4; });
  return 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2];
};
const contrast = (fg, bg) => {
  const a = luminance(fg), b = luminance(bg);
  return (Math.max(a, b) + 0.05) / (Math.min(a, b) + 0.05);
};

// Body text against the body surface in both schemes: at least SC 1.4.3's
// 4.5:1 in each, and the scheme contract as the stylesheet states it — the
// dark block is a default for what the document left undeclared, a declared
// value is the document's in both schemes, and a page that declares one
// scheme (`color-scheme: light`, a page with colours of its own) shows a
// dark-mode reader exactly its light colours.
const judgeSchemes = (light, dark) => {
  const single = !/dark/.test(light.scheme || '');
  const inkDeclared = light.fg !== lightInk, surfaceDeclared = light.bg !== lightSurface;
  const cl = contrast(light.fg, light.bg), cd = contrast(dark.fg, dark.bg);
  const expected = single ? dark.bg === light.bg && dark.fg === light.fg
    : !inkDeclared && !surfaceDeclared ? dark.bg === darkSurface && dark.fg === darkInk
    : inkDeclared && surfaceDeclared ? dark.bg === light.bg && dark.fg === light.fg
    : true;
  const arm = single ? 'one scheme' : !inkDeclared && !surfaceDeclared ? 'default tokens'
    : inkDeclared && surfaceDeclared ? 'declared colours' : 'mixed';
  return { ok: cl >= 4.5 && cd >= 4.5 && expected, n: 1,
    why: `${arm}: light ${light.fg} on ${light.bg} ${cl.toFixed(2)}:1, dark ${dark.fg} on ${dark.bg} ${cd.toFixed(2)}:1` };
};

const mediaChecks = {
  'reduced-motion': async () => {
    await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
    const anims = document.getAnimations().length;
    const steps = [...document.querySelectorAll('.step')];
    const dim = steps.filter(s => +getComputedStyle(s).opacity < 1).length;
    const sb = getComputedStyle(document.documentElement).scrollBehavior;
    return { ok: anims === 0 && dim === 0 && sb !== 'smooth', n: 1,
      why: `animations x${anims} dim-steps x${dim} scroll-behavior=${sb}` };
  },
  // Print: the deck's print partition (no spacer, every step uncovered, one
  // frame per page) and, for a body reading the default tokens, black on
  // white. A body reading declared colours keeps them under print too
  // (source order, the same contract as the colour scheme): recorded, not
  // judged.
  print: (deck) => {
    const b = getComputedStyle(document.body);
    const steps = [...document.querySelectorAll('.step')];
    const dim = steps.filter(s => +getComputedStyle(s).opacity < 1).length;
    const spacers = [...document.querySelectorAll('.snap')].filter(s => getComputedStyle(s).display !== 'none').length;
    const slides = deck ? [...document.querySelectorAll('section.slide')] : [];
    const unbroken = slides.filter(s => getComputedStyle(s).breakAfter !== 'page').length;
    const screenFollows = document.documentElement.dataset.ltxFollows === 'tokens';
    const bodyOk = !screenFollows || (b.backgroundColor === 'rgb(255, 255, 255)' && b.color === 'rgb(0, 0, 0)');
    const ok = bodyOk && dim === 0 && spacers === 0 && unbroken === 0;
    return { ok, n: 1, why: `bg=${b.backgroundColor} fg=${b.color} (${screenFollows ? 'default tokens' : 'declared colours'}) dim-steps x${dim} visible-spacers x${spacers} slides-without-break x${unbroken}/${slides.length}` };
  },
  // Paper has no collapse: printed, every disclosure shows its body, open or
  // not, and its summary no toggle's marker.
  'print-disclosure': () => {
    const ds = [...document.querySelectorAll('details')];
    const hidden = ds.flatMap(d => [...d.children].filter(c => c.tagName !== 'SUMMARY'))
      .filter(c => !c.checkVisibility()).length;
    const marked = ds.map(d => d.querySelector(':scope > summary'))
      .filter(s => s && getComputedStyle(s).listStyleType !== 'none').length;
    return { ok: hidden === 0 && marked === 0, n: ds.length > 0 ? 1 : 0,
      why: `${ds.length} disclosures, ${hidden} body blocks hidden on paper, ${marked} toggle markers` };
  },
};

// Scripting off, synchronous (no timers run in a page with scripting
// disabled): the deck's marker is absent and a non-deck page carries no
// executable script. The scroll is applied here; the read follows a frame
// the driver has the browser draw, so the scroll-driven uncover has had it.
const noScriptScroll = () => {
  const se = document.scrollingElement;
  se.scrollTo({ left: se.scrollWidth, top: se.scrollHeight, behavior: 'instant' });
  return se.scrollLeft;
};
const noScriptRead = () => {
  const deck = /mandatory/.test(getComputedStyle(document.documentElement).scrollSnapType);
  const scripts = [...document.scripts].filter(s => !s.type || /javascript|module/i.test(s.type)).length;
  if (!deck) return { ok: scripts === 0, n: 1, why: `executable scripts x${scripts}` };
  const marker = document.documentElement.hasAttribute('data-deck-script');
  const steps = [...document.querySelectorAll('.step')];
  const dim = steps.filter(s => +getComputedStyle(s).opacity < 1).length;
  return { ok: !marker && dim === 0, n: 1,
    why: `marker=${marker} steps x${steps.length} dim-at-end x${dim}` };
};

const cell = (r) => r.n === 0 ? 'na' : r.ok ? 'pass'
  : (r.unfinished ? 'inconclusive:' : 'fail:') + clean(r.why);
const lost = (e) => (unfinished(e) ? 'inconclusive:' : 'fail:') + clean(String(e.message).split('\n')[0]);

// A printed deck loses nothing and wastes nothing. The deck is printed once,
// as a reader prints it: the sheet the page's own @page size, the size
// preferred, backgrounds off; paper is read back with pdftotext, one page
// per form feed. Two judgements, one construct each:
//  - print-spill: a stage whose content runs past its sheet continues on
//    the next, so every letter and digit the page lays out reaches paper —
//    the multiset, NFKC and case folded, so a list marker or a hyphen the
//    print adds cannot mask a loss, and a math italic or a small capital is
//    the letter it spells. Only a deck with a stage taller than its sheet
//    exercises it: elsewhere nothing can reach a sheet's edge.
//  - print-sheets: no sheet goes to paper blank or with furniture alone —
//    one with no letter or digit, or exactly a stage's footline's letters
//    and digits and no stage's body's, is allowed only for a stage that
//    lays out none outside its footline. A stage's padding alone once took
//    a sheet of its own, and so did the tail of a stage that opened below a
//    heading instead of on a sheet of its own, and a footline pulled onto
//    the stage's edge through its padding, its frame number alone on it.
// Playwright prints to PDF in Chromium alone.
const census = (s) => {
  const m = new Map();
  for (const c of s.normalize('NFKC').toLowerCase())
    if (/[\p{L}\p{N}]/u.test(c)) m.set(c, (m.get(c) || 0) + 1);
  return m;
};
const inked = (s) => /[\p{L}\p{N}]/u.test(s);
// The deck's page, as its own @page rule declares it: the PDF page's size
// in points, which is the sheet the print judgements read and the aspect
// the stage judgement sets the viewport to.
const pageSizeOf = (page) => page.evaluate(() => {
  const find = (rules) => {
    for (const r of rules) {
      if (r instanceof CSSPageRule) return r.style.getPropertyValue('size');
      if (r.cssRules) { const s = find(r.cssRules); if (s) return s; }
    }
    return '';
  };
  for (const sheet of document.styleSheets) { const s = find(sheet.cssRules); if (s) return s; }
  return '';
});
const printDeck = async (page, name, fx) => {
  const none = { ok: true, n: 0, why: '' };
  if (name !== 'chromium') return { spill: none, sheets: none };
  const size = await pageSizeOf(page);
  const pt = /^([\d.]+)pt ([\d.]+)pt$/.exec(size.trim());
  if (!pt) {
    const bad = { ok: false, n: 1, why: `no @page size in points (${size})` };
    return { spill: bad, sheets: bad };
  }
  const sheetH = +pt[2] * 4 / 3;
  await page.setViewportSize({ width: Math.round(+pt[1] * 4 / 3), height: Math.round(sheetH) });
  const laid = await page.evaluate((h) => {
    const stages = [...document.querySelectorAll('section.slide, section.section-page')];
    const own = (s, foot) => [...s.children].filter(c => c.matches('footer.slide-foot') === foot)
      .map(c => c.innerText).join(' ');
    return { spill: stages.filter(s =>
        Math.max(s.scrollHeight, s.getBoundingClientRect().height) > h + 1).length,
      bare: stages.filter(s => !/[\p{L}\p{N}]/u.test(own(s, false))).length,
      bodies: stages.map(s => own(s, false)), feet: stages.map(s => own(s, true)),
      text: document.querySelector('main').innerText };
  }, sheetH);
  const pdf = path.join(dir, fx + '.printed.pdf');
  await page.pdf({ path: pdf, preferCSSPageSize: true });
  let paper;
  try { paper = toolText('pdftotext', ['-enc', 'UTF-8', pdf, '-']); }
  catch (e) {
    const bad = { ok: false, n: 1, unfinished: unfinished(e), why: clean(e.message) };
    return { spill: bad, sheets: bad };
  }
  const sheets = paper.split('\f').slice(0, -1);
  // A sheet holding a stage's footline and nothing else: its letters and
  // digits are exactly one footline's, and no stage's body is those.
  const same = (a, b) => a.size === b.size && [...a].every(([c, n]) => b.get(c) === n);
  const feet = laid.feet.filter(inked).map(census), bodies = laid.bodies.map(census);
  const wasted = sheets.filter(t => !inked(t) ||
    (feet.some(f => same(f, census(t))) && !bodies.some(b => same(b, census(t))))).length;
  const sheetsCell = { ok: wasted <= laid.bare, n: 1,
    why: `${wasted} of ${sheets.length} sheets blank or furniture alone, ` +
      `${laid.bare} stage(s) with no text outside the footline` };
  if (laid.spill === 0) return { spill: none, sheets: sheetsCell };
  const want = census(laid.text), got = census(paper);
  const lost = [...want].filter(([c, n]) => (got.get(c) || 0) < n);
  const short = lost.reduce((a, [c, n]) => a + n - (got.get(c) || 0), 0);
  return { sheets: sheetsCell, spill: { ok: lost.length === 0, n: 1,
    why: `${laid.spill} stage(s) taller than the sheet, ${short} laid-out characters missing on paper` } };
};

// A code block's lines wrap only where the page's own wrap may: every line
// box break inside a code line falls at a space, between two fallback
// tokens read off the line's text — a word (letters, digits, `_`, `'`,
// every scalar past ASCII), a run of operator characters, any other
// character alone, each character of a script that wraps between its
// characters, a character that holds to its neighbour reading with it, as
// the engine reads them (the tables `codeTables` writes from
// `Listing.wrapsBetweenChars`, `holdsToPrevious` and `holdsToNext`) — or
// inside a token wider than its line, which breaks where it must; never
// inside `:=`, `->` or an identifier that fits. In a block that carries a
// `<wbr>` — a declared listing that wraps at listings' units — a break
// falls only at a space or the `<wbr>` the page stands between two units (a
// unit may part a fallback token: `0x1F` is the units `0` and `x1F`), or
// inside a unit the page holds nowhere because it is wider than a line, or
// between two characters of scripts that wrap between their characters
// where the engine parts its units, which the page leaves to the browser.
// Thai and Lao break only between the words a dictionary finds (the
// browser's own segmenter's), a subset of the clusters the page may break
// between, save inside a word wider than a line. And a wrapping block
// holds its lines inside its box: none runs past it, save a box whose
// continuation line cannot hold the units the page holds in every box
// (`HtmlDoc.codeShortColumns`), which no wrap keeps inside.
const codeWrapJudge = (tables) => {
  const inR = (rs, cp) => {
    let lo = 0, hi = rs.length - 1;
    while (lo <= hi) {
      const m = (lo + hi) >> 1;
      if (cp < rs[m][0]) hi = m - 1; else if (cp > rs[m][1]) lo = m + 1; else return true;
    }
    return false;
  };
  const cls = (c) => {
    const cp = c.codePointAt(0);
    if (c === ' ' || c === '\t') return 'space';
    if (inR(tables.apart, cp)) return 'single';
    if (/[A-Za-z0-9_']/.test(c) || cp > 127) return 'word';
    if ('!#$%&*+-./:<=>?@\\^|~'.includes(c)) return 'op';
    return 'single';
  };
  const blocks = [...document.querySelectorAll('pre > code')]
    .filter(c => c.getBoundingClientRect().width > 0);
  let wraps = 0;
  const bad = [], over = [];
  for (const code of blocks) {
    const pre = code.parentElement;
    const cs = getComputedStyle(pre);
    // a continuation line's room, the block's less the hang its continuations take
    const room = pre.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight) -
      Math.abs(parseFloat(cs.textIndent) || 0);
    const overrun = /^(pre-wrap|break-spaces)$/.test(cs.whiteSpace) &&
      pre.scrollWidth > pre.clientWidth + 1 ? pre.scrollWidth - pre.clientWidth : 0;
    const chars = [];
    let wbr = false, units = false;
    const walker = document.createTreeWalker(code, NodeFilter.SHOW_TEXT | NodeFilter.SHOW_ELEMENT);
    for (let t = walker.nextNode(); t; t = walker.nextNode()) {
      if (t.nodeType === Node.ELEMENT_NODE) { if (t.tagName === 'WBR') { wbr = true; units = true; } continue; }
      const tok = t.parentElement.closest('.tok');
      const holder = tok && code.contains(tok) ? tok : null;
      let i = 0;
      for (const ch of t.data) {
        const r = document.createRange();
        r.setStart(t, i); r.setEnd(t, i + ch.length);
        const rect = [...r.getClientRects()].find(x => x.width > 0 || x.height > 0);
        chars.push({ ch, top: rect ? rect.top : null, w: rect ? rect.width : 0, wbr, holder });
        wbr = false;
        i += ch.length;
      }
    }
    // a block whose continuation line holds no unit the page always holds
    // (`HtmlDoc.codeShortColumns`) cannot keep its lines inside its box
    const cells = chars.filter(c => c.w > 0 && !/\s/.test(c.ch)).map(c => c.w).sort((a, b) => a - b);
    const cell = cells.length ? cells[cells.length >> 1] : 0;
    if (overrun && room >= (tables.short + 1) * cell) over.push(overrun);
    // Thai and Lao words, as the browser's segmenter finds them, line by line
    const words = new Intl.Segmenter('th', { granularity: 'word' });
    let wseg = 0;
    const wordWidth = new Map();
    for (let a = 0; a < chars.length;) {
      let b = a;
      while (b < chars.length && chars[b].ch !== '\n') b++;
      const line = chars.slice(a, b);
      const starts = new Set();
      if (line.some(c => inR(tables.words, c.ch.codePointAt(0)))) {
        let off = 0;
        const at = new Map(line.map((c, k) => { const o = off; off += c.ch.length; return [o, k]; }));
        for (const s of words.segment(line.map(c => c.ch).join(''))) starts.add(at.get(s.index));
      }
      line.forEach((c, k) => {
        if (starts.has(k)) wseg++;
        c.wb = starts.has(k);
        c.wseg = wseg;
        wordWidth.set(wseg, (wordWidth.get(wseg) || 0) + c.w);
      });
      wseg++;
      a = b + 1;
    }
    // under listings' rule, the stretches between two break points the page
    // marks — a space or a `<wbr>` — that no element holds: a unit wider
    // than a line, which breaks where it must
    let seg = 0;
    const segWidth = new Map(), heldWidth = new Map();
    for (const c of chars) {
      if (c.ch === '\n' || c.ch === ' ' || c.ch === '\t' || c.wbr || c.holder) seg++;
      c.seg = seg;
      if (!c.holder) segWidth.set(seg, (segWidth.get(seg) || 0) + c.w);
      else heldWidth.set(c.holder, (heldWidth.get(c.holder) || 0) + c.w);
    }
    // the fallback tokens, glued as the engine glues them
    let tok = 0, prev = null, held = false;
    const width = new Map();
    for (const c of chars) {
      c.sp = c.ch === ' ' || c.ch === '\t';
      if (c.ch === '\n') { tok++; prev = null; held = false; c.tok = tok; continue; }
      const cp = c.ch.codePointAt(0);
      const glued = !c.sp && (held || inR(tables.before, cp));
      held = inR(tables.after, cp);
      const k = cls(c.ch);
      if (!glued && (prev !== k || k === 'single')) tok++;
      prev = k;
      c.tok = tok;
      width.set(tok, (width.get(tok) || 0) + c.w);
    }
    let last = null;
    for (const c of chars) {
      if (c.ch === '\n') { last = null; continue; }
      if (c.top === null) continue;
      if (last && c.top > last.top + 2) {
        wraps++;
        const inside = last.tok === c.tok;
        const wide = inside && width.get(c.tok) > room + 0.5;
        // a unit wider than a line breaks where it must: one the page holds
        // nowhere, or one a box too narrow for it released
        const longUnit = (!last.holder && !c.holder && last.seg === c.seg &&
          segWidth.get(c.seg) > room + 0.5) ||
          (last.holder && last.holder === c.holder && heldWidth.get(c.holder) > room + 0.5);
        const lp = last.ch.codePointAt(0), cp = c.ch.codePointAt(0);
        const parted = inR(tables.apart, lp) && inR(tables.apart, cp) &&
          !inR(tables.before, cp) && !inR(tables.after, lp);
        const dictionary = inR(tables.words, lp) && inR(tables.words, cp);
        const ok = (units ? (last.sp || c.sp || c.wbr || longUnit || parted)
          : (last.sp || c.sp || !inside || wide)) &&
          (!dictionary || c.wb || wordWidth.get(c.wseg) > room + 0.5);
        if (!ok) bad.push(JSON.stringify(last.ch + '|' + c.ch));
      }
      last = c;
    }
  }
  return { ok: bad.length === 0 && over.length === 0, n: blocks.length, wraps,
    why: `${blocks.length} code blocks, ${wraps} wraps` +
      (bad.length ? ', inside a token at ' + [...new Set(bad)].slice(0, 6).join(' ') : '') +
      (over.length ? ', a wrapping block overflowing its box by ' + over.map(Math.round).join(' ') + ' px' : '') };
};
const codeTables = JSON.parse(process.env.LT_CODE_TABLES ||
  '{"apart":[],"words":[],"before":[],"after":[],"short":3}');

// The narrow screen widths both line judges read.
const narrowWidths = [320, 360, 600, 900];

// A formula's text run keeps its line, as TeX sets a word in one box: at
// every narrow width, where a column too narrow for its formula would part a
// breakable run, each scalar of each shown math token of two or more scalars
// has a box, all on its first scalar's line, and each of its spaces a width,
// so none collapses as the box keeps it.
const mathLineJudge = () => {
  const runs = [];
  for (const el of document.querySelectorAll('math :is(mi, mn, mo, mtext, ms)')) {
    if (!el.checkVisibility()) continue;
    for (const t of el.childNodes)
      if (t.nodeType === 3 && [...t.data].length > 1) runs.push(t);
  }
  const bad = [];
  for (const t of runs) {
    const tops = [];
    let at = 0, lost = false;
    for (const ch of t.data) {
      const r = document.createRange();
      r.setStart(t, at);
      r.setEnd(t, at + ch.length);
      const q = r.getBoundingClientRect();
      if ((q.width === 0 && q.height === 0) || (ch === ' ' && q.width === 0)) lost = true;
      else tops.push(q.top);
      at += ch.length;
    }
    if (lost || Math.max(...tops) - Math.min(...tops) > 1) bad.push(JSON.stringify([...t.data.trim()].slice(0, 40).join('')));
  }
  return { ok: bad.length === 0, n: runs.length,
    why: bad.length ? `${bad.length}/${runs.length} math text runs leave their line: ${bad.slice(0, 3).join(', ')}` : '' };
};

const mathLine = async (page) => {
  const off = [];
  let n = 0;
  try {
    for (const w of narrowWidths) {
      await page.setViewportSize({ width: w, height: 720 });
      await page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
      const r = await page.evaluate(mathLineJudge);
      n = Math.max(n, r.n);
      if (!r.ok) off.push(w + ' px: ' + r.why);
    }
  } finally {
    await page.setViewportSize({ width: 1280, height: 720 });
  }
  return { ok: off.length === 0, n, why: off.join('; ') };
};

// The judge at narrow screens, where long lines wrap — from the 320 CSS px
// WCAG 2.2's reflow criterion sets (SC 1.4.10) — and on paper.
const codeWrap = async (page) => {
  const runs = [];
  try {
    for (const w of narrowWidths) {
      await page.setViewportSize({ width: w, height: 720 });
      await page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
      runs.push(['screen ' + w, await page.evaluate(codeWrapJudge, codeTables)]);
    }
    await page.emulateMedia({ media: 'print' });
    await page.setViewportSize({ width: 600, height: 720 });
    await page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
    runs.push(['print 600', await page.evaluate(codeWrapJudge, codeTables)]);
  } finally {
    await page.emulateMedia({ media: 'screen' });
    await page.setViewportSize({ width: 1280, height: 720 });
  }
  const n = runs.some(([, r]) => r.n > 0 && r.wraps > 0) ? 1 : 0;
  const off = runs.filter(([, r]) => !r.ok);
  return { ok: off.length === 0, n,
    why: (off.length ? off : runs).map(([k, r]) => k + ': ' + r.why).join('; ') };
};

// On a flow page wider than its measure no wide block, text or outline passes the viewport, and the
// outline and text stand as its MyST layout sets them within testdata/oracles/myst-themes.tsv's.
const webRows = (process.env.LT_MYST || '').split('\n')
  .filter(l => l && !l.startsWith('#') && !l.startsWith('layout\t')).map(l => l.split('\t'));
const webRef = (layout, key) => {
  const r = webRows.find(r => r[0] === layout && r[1] === key);
  return r && r[4] !== '-' ? { v: +r[2], tol: +r[4] } : null;
};
const webRead = () => {
  const main = document.querySelector('body > main');
  if (!main || /mandatory/.test(getComputedStyle(document.documentElement).scrollSnapType))
    return { flow: false };
  const root = document.documentElement;
  const rem = parseFloat(getComputedStyle(root).fontSize);
  let grid = null;
  for (const sheet of document.styleSheets) for (const r of sheet.cssRules)
    if (r instanceof CSSMediaRule && [...r.cssRules].some(x => x.selectorText === 'body' &&
        x.style.gridTemplateColumns)) {
      const m = /min-width:\s*([\d.]+)em/.exec(r.conditionText);
      if (m) grid = +m[1] * rem;
    }
  const nav = document.querySelector('body > nav.outline');
  const over = Math.max(0, ...[main, nav, ...main.querySelectorAll('pre, .display, div.math-display, table.bt-natural')]
    .filter(e => e && getComputedStyle(e).display !== 'none')
    .map(e => Math.round(e.getBoundingClientRect().right - root.clientWidth)));
  if (!nav) return { flow: true, nav: false, grid, over };
  const ns = getComputedStyle(nav);
  const col = ns.gridColumnStart;
  const probe = document.createElement('span');
  probe.textContent = '0'.repeat(100);
  probe.style.whiteSpace = 'nowrap';
  probe.style.position = 'absolute';
  main.appendChild(probe);
  const ch = probe.getBoundingClientRect().width / 100;
  probe.remove();
  const m = main.getBoundingClientRect(), n = nav.getBoundingClientRect();
  const ms = getComputedStyle(main);
  const text = m.width - parseFloat(ms.paddingLeft) - parseFloat(ms.paddingRight);
  const room = root.scrollHeight - innerHeight;
  let stays = true;
  for (const y of room > 0 ? [room / 2, room] : []) {
    window.scrollTo(0, y);
    const t = nav.getBoundingClientRect();
    stays = stays && t.top > -1 && t.top < 1;
  }
  window.scrollTo(0, 0);
  return { flow: true, nav: true, grid, over, shown: ns.display !== 'none' && n.width > 0,
    layout: col === 'lead' ? 'book' : col === 'margin' ? 'article' : null,
    ownMeasure: getComputedStyle(root).getPropertyValue('--measure').includes('ch'),
    ch, rem, text, mainX: m.left, mainR: m.right, navX: n.left, navR: n.right, navW: n.width,
    sticky: ns.position === 'sticky' && stays };
};
const webLayout = async (page) => {
  const settle = () => page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
  const at = async (w) => {
    await page.setViewportSize({ width: Math.round(w), height: 900 });
    await settle();
    return page.evaluate(webRead);
  };
  try {
    const first = await at(1440);
    if (!first.flow) return { ok: true, n: 0, why: '' };
    const why = [];
    const widths = [1000, 1100, 1200, 1440];
    if (first.grid) widths.push(first.grid - 1, first.grid + 1, first.grid + 40);
    for (const w of widths) {
      const r = await at(w);
      if (r.over > 1) why.push(`a block passes the viewport by ${r.over} px at ${Math.round(w)} px`);
    }
    if ((await at(390)).shown) why.push('the outline is shown on a phone');
    const wideAt = first.grid && first.grid + 1 > 1440 ? first.grid + 1 : 1440;
    const wide = await at(wideAt);
    if (wide.nav) {
      const near = (key, got) => {
        const r = webRef(wide.layout, key);
        if (r && wideAt === 1440 && Math.abs(got - r.v) > r.tol)
          why.push(`${key} ${got.toFixed(1)} against ${r.v}±${r.tol}`);
      };
      if (!wide.shown || !wide.layout) why.push(`the outline stands in no layout column at ${wideAt} px`);
      else {
        if (wide.layout === 'book') {
          if (wide.navR > wide.mainX) why.push('the book outline does not stand before the text');
          near('nav-gap@1440', wide.mainX - wide.navR);
        } else {
          if (wide.navX < wide.mainR) why.push('the article outline does not stand after the text');
          near('nav-gap@1440', wide.navX - wide.mainR);
        }
        near('nav-width@1440', wide.navW);
        if (!wide.sticky) why.push('the outline does not stay at the viewport top as the page scrolls');
      }
    }
    if (wide.nav && wide.ownMeasure && wide.layout) {
      const r = webRef(wide.layout, 'prose-ch');
      const inset = +((webRows.find(r => r[0] === wide.layout && r[1] === 'prose-inset') || [])[2] || 0);
      if (r && Math.abs((wide.text - inset * wide.rem) / wide.ch - r.v) > r.tol)
        why.push(`prose ${((wide.text - inset * wide.rem) / wide.ch).toFixed(2)} ch against ${r.v}±${r.tol}`);
    }
    return { ok: why.length === 0, n: 1,
      why: (wide.layout || 'single column') + ': ' + (why.join('; ') || 'as the reference') };
  } finally {
    await page.setViewportSize({ width: 1280, height: 720 });
  }
};

// A page's code reaches paper whole and at the page's own scale. The page
// is printed as a reader's print dialog prints a page that declares no
// sheet: Letter, 0.4 in margins, backgrounds off; paper is read back with
// pdftotext. Two facts, one judgement: laid out for that sheet's printable
// width, nothing runs past it — Chromium prints a page that does at a
// reduced scale, every line of it smaller — no code block's lines run past
// its own box, over what stands beside it, and every letter and digit the
// page lays out is on paper, the multiset, NFKC and case folded
// (`census`). A deck pages on its own sheet (`print-spill`).
const printCode = async (page, name, fx) => {
  const none = { ok: true, n: 0, why: '' };
  if (name !== 'chromium') return none;
  const has = await page.evaluate(() =>
    !/mandatory/.test(getComputedStyle(document.documentElement).scrollSnapType) &&
      document.querySelectorAll('pre > code').length > 0);
  if (!has) return none;
  const width = Math.round((8.5 - 2 * 0.4) * 96);
  await page.emulateMedia({ media: 'print' });
  await page.setViewportSize({ width, height: 1000 });
  await page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
  const laid = await page.evaluate(() => ({
    past: document.documentElement.scrollWidth - document.documentElement.clientWidth,
    over: [...document.querySelectorAll('pre')].filter(p => p.getBoundingClientRect().width > 0)
      .map(p => p.scrollWidth - p.clientWidth).filter(d => d > 1),
    text: (document.querySelector('main') || document.body).innerText }));
  const pdf = path.join(dir, fx + '.code.pdf');
  await page.pdf({ path: pdf, format: 'Letter',
    margin: { top: '0.4in', bottom: '0.4in', left: '0.4in', right: '0.4in' } });
  await page.setViewportSize({ width: 1280, height: 720 });
  let paper;
  try { paper = toolText('pdftotext', ['-enc', 'UTF-8', pdf, '-']); }
  catch (e) { return { ok: false, n: 1, unfinished: unfinished(e), why: clean(e.message) }; }
  const want = census(laid.text), got = census(paper);
  const short = [...want].reduce((a, [c, k]) => a + Math.max(0, k - (got.get(c) || 0)), 0);
  return { ok: laid.past <= 1 && laid.over.length === 0 && short === 0, n: 1,
    why: `${Math.max(0, laid.past)} px past the sheet's printable width, ` +
      `${short} laid-out characters missing on paper` +
      (laid.over.length ? ', a code block running past its box by ' +
        laid.over.map(Math.round).join(' ') + ' px' : '') };
};

// A frame its PDF page holds is held by its stage: at the deck's own aspect
// (1280 CSS px wide, the height the PDF page's ratio gives), no stage's
// content runs past its foot, by as much as one pixel — the stage scrolls
// (`overflow-y: auto`), so a spill hides the content below the foot until a
// reader scrolls the slide, and a platform with classic scrollbars draws a
// bar across the stage for a single pixel of it. The premise comes from
// the PDF build of the same source, written beside the page as
// `<fixture>.unfit`: the frames that continue on a further page (W0384,
// named by frame number) and the frames that declare `[allowframebreaks]`;
// their stages are not judged. Numbers restart after `\appendix`, so a
// repeated number exempts both of its frames: the check only weakens. The
// stage is judged in its first snap state, the one a reader lands on.
const stageFit = async (page, fx) => {
  const none = { ok: true, n: 0, why: '' };
  const deck = await page.evaluate(() =>
    /mandatory/.test(getComputedStyle(document.documentElement).scrollSnapType));
  if (!deck) return none;
  const size = await pageSizeOf(page);
  const pt = /^([\d.]+)pt ([\d.]+)pt$/.exec(size.trim());
  if (!pt) return { ok: false, n: 1, why: `no @page size in points (${size})` };
  let exempt;
  try {
    exempt = require('fs').readFileSync(path.join(dir, fx + '.unfit'), 'utf8')
      .split(/\s+/).filter(Boolean);
  } catch (e) { return { ok: false, n: 1, why: 'no PDF premise for the deck: ' + clean(e.message) }; }
  await page.setViewportSize({ width: 1280, height: Math.round(1280 * +pt[2] / +pt[1]) });
  await page.evaluate(() => document.fonts.ready);
  await page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
  const r = await page.evaluate((exempt) => {
    let n = 0;
    const over = [];
    for (const s of document.querySelectorAll('section.slide')) {
      const track = s.closest('.slide-track');
      const num = s.dataset.frameNumber || (track && track.dataset.frameNumber);
      if (num && exempt.includes(num)) continue;
      n++;
      const spill = s.scrollHeight - s.clientHeight;
      if (spill > 0) over.push(`${s.id || (track && track.id) || num} by ${spill}px`);
    }
    return { n, over };
  }, exempt);
  await page.setViewportSize({ width: 1280, height: 720 });
  return { ok: r.over.length === 0, n: r.n,
    why: r.over.length ? `${r.over.length}/${r.n} stages run past their foot: ${r.over.join(', ')}` : '' };
};

// The window shapes a reader brings besides the deck's own are reported, never
// gated, as the shape is the reader's: per stage in the snap state a reader
// lands on, the outermost element its scrollport clips by more than a pixel
// and each text block set on more lines than at the deck's own aspect.
const readerShapes = [['16:10', 1440, 900], ['4:3', 1024, 768], ['phone', 390, 844]];
const textBlocks = 'p, li, dt, dd, h1, h2, h3, h4, h5, h6, figcaption, caption, td, th, pre, summary';
const shapeRead = (textBlocks) => {
  const name = (el) => {
    const t = [...(el.textContent || '').replace(/\s+/g, ' ').trim()].slice(0, 32).join('');
    return el.tagName.toLowerCase() + (t ? ' ' + JSON.stringify(t) : '');
  };
  const extent = (el) => {
    if (el.matches('img, svg, canvas, video')) return el.getBoundingClientRect();
    const r = document.createRange();
    r.selectNodeContents(el);
    return r.getBoundingClientRect();
  };
  // A line is a run of its text's fragments whose middles stand inside one band, so a
  // raised script or a taller run shares its line and a child box counts no line of its own.
  const lines = (el) => {
    const qs = [];
    const walk = document.createTreeWalker(el, NodeFilter.SHOW_TEXT);
    for (let t = walk.nextNode(); t; t = walk.nextNode()) {
      if (!t.data.trim()) continue;
      const r = document.createRange();
      r.selectNodeContents(t);
      for (const q of r.getClientRects()) if (q.width > 0 && q.height > 0) qs.push(q);
    }
    qs.sort((a, b) => a.top - b.top);
    let n = 0, bottom = -Infinity;
    for (const q of qs) {
      if ((q.top + q.bottom) / 2 > bottom) { n++; bottom = q.bottom; } else bottom = Math.max(bottom, q.bottom);
    }
    return n;
  };
  const inks = (el) => el.matches('img, svg, math, canvas, video') ||
    [...el.childNodes].some(n => n.nodeType === 3 && n.data.trim());
  // Out of sight by design, as a page-less section's heading: the reader's window clips nothing.
  const unseen = (el) => /inset\(50%\)/.test(getComputedStyle(el).clipPath);
  const frames = [];
  for (const s of document.querySelectorAll('section.slide, section.section-page')) {
    const track = s.closest('.slide-track');
    const label = s.id || (track && track.id) || s.dataset.frameNumber || s.dataset.slideLabel || '-';
    const box = s.getBoundingClientRect();
    const left = box.left + s.clientLeft, top = box.top + s.clientTop;
    const right = left + s.clientWidth, bottom = top + s.clientHeight;
    const past = (el) => {
      const r = extent(el);
      if (r.width === 0 && r.height === 0) return [];
      return [['right', r.right - right], ['below', r.bottom - bottom], ['left', left - r.left]]
        .filter(([, d]) => d > 1);
    };
    const clipped = [];
    let held = null;
    for (const el of s.querySelectorAll('*')) {
      if (held && held.contains(el)) continue;
      if (!el.checkVisibility() || unseen(el) || !inks(el) || past(el).length === 0) continue;
      let top = el;
      while (top.parentElement && top.parentElement !== s && past(top.parentElement).length) top = top.parentElement;
      clipped.push(name(top) + ' ' + past(top).map(([w, d]) => Math.round(d) + 'px ' + w).join(' '));
      held = top;
    }
    const counts = [...s.querySelectorAll(textBlocks)].filter(el => !unseen(el))
      .map(el => [name(el), el.checkVisibility() ? lines(el) : 0]);
    frames.push({ label, clipped, counts });
  }
  return frames;
};

// One deck's report rows: per shape, `fits` or each stage's clipped and newly
// wrapped elements, the deck's own aspect first.
const stageShapes = async (page) => {
  const deck = await page.evaluate(() =>
    /mandatory/.test(getComputedStyle(document.documentElement).scrollSnapType));
  if (!deck) return [];
  const pt = /^([\d.]+)pt ([\d.]+)pt$/.exec((await pageSizeOf(page)).trim());
  if (!pt) return [['own', '-', 'unmeasured: no @page size in points']];
  const read = async (w, h) => {
    await page.setViewportSize({ width: w, height: h });
    await page.evaluate(() => document.fonts.ready);
    await page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
    return page.evaluate(shapeRead, textBlocks);
  };
  const ownH = Math.round(1280 * +pt[2] / +pt[1]);
  const rows = [];
  try {
    const own = await read(1280, ownH);
    for (const [shape, w, h] of [['own', 1280, ownH], ...readerShapes]) {
      const frames = shape === 'own' ? own : await read(w, h);
      const at = `${shape} ${w}x${h}`;
      let any = false;
      frames.forEach((f, i) => {
        const base = (own[i] || { counts: [] }).counts;
        const wrapped = f.counts.flatMap(([n, k], j) =>
          base[j] && k > base[j][1] ? [`${n} ${base[j][1]}→${k} lines`] : []);
        if (f.clipped.length === 0 && wrapped.length === 0) return;
        any = true;
        rows.push([at, f.label, [f.clipped.length ? 'clipped: ' + f.clipped.join('; ') : '',
          wrapped.length ? 'wrapped: ' + wrapped.join('; ') : ''].filter(Boolean).join('  ')]);
      });
      if (!any) rows.push([at, '-', 'fits']);
    }
  } catch (e) {
    rows.push(['-', '-', 'unmeasured: ' + clean(String(e.message).split('\n')[0])]);
  } finally {
    await page.setViewportSize({ width: 1280, height: 720 });
  }
  return rows;
};

// A screenshot's pixels: Chromium's PNG, 8-bit RGB or RGBA, each row unfiltered.
const pngPixels = (buf) => {
  let at = 8, w = 0, h = 0, bpp = 4;
  const idat = [];
  while (at < buf.length) {
    const len = buf.readUInt32BE(at), type = buf.toString('latin1', at + 4, at + 8);
    if (type === 'IHDR') {
      w = buf.readUInt32BE(at + 8); h = buf.readUInt32BE(at + 12);
      if (buf[at + 16] !== 8 || buf[at + 20] !== 0) throw new Error('screenshot: not an 8-bit plain PNG');
      bpp = buf[at + 17] === 2 ? 3 : 4;
    } else if (type === 'IDAT') idat.push(buf.subarray(at + 8, at + 8 + len));
    else if (type === 'IEND') break;
    at += 12 + len;
  }
  const raw = require('zlib').inflateSync(Buffer.concat(idat));
  const stride = w * bpp, px = Buffer.alloc(h * stride);
  for (let y = 0; y < h; y++) {
    const f = raw[y * (stride + 1)], src = y * (stride + 1) + 1, row = y * stride;
    for (let x = 0; x < stride; x++) {
      const a = x >= bpp ? px[row + x - bpp] : 0, b = y > 0 ? px[row - stride + x] : 0;
      const c = x >= bpp && y > 0 ? px[row - stride + x - bpp] : 0;
      let v = raw[src + x];
      if (f === 1) v += a;
      else if (f === 2) v += b;
      else if (f === 3) v += (a + b) >> 1;
      else if (f === 4) {
        const q = a + b - c, pa = Math.abs(q - a), pb = Math.abs(q - b), pc = Math.abs(q - c);
        v += pa <= pb && pa <= pc ? a : pb <= pc ? b : c;
      }
      px[row + x] = v & 255;
    }
  }
  return { w, h, bpp, px };
};

// The device pixels two shots of one viewport differ at by more than a tenth of a channel's range,
// which a re-rasterized glyph or image edge stays within, by column, or null past a twentieth.
const shotChanges = (a, b) => {
  const cols = new Map();
  let n = 0;
  for (let y = 0; y < a.h; y++) {
    const row = y * a.w * a.bpp;
    for (let x = 0; x < a.w; x++) {
      const i = row + x * a.bpp;
      if (Math.abs(a.px[i] - b.px[i]) <= 25 && Math.abs(a.px[i + 1] - b.px[i + 1]) <= 25 &&
          Math.abs(a.px[i + 2] - b.px[i + 2]) <= 25) continue;
      if (++n > a.w * a.h / 20) return null;
      const rows = cols.get(x);
      if (rows) rows.push(y); else cols.set(x, [y]);
    }
  }
  return { cols, w: a.w, h: a.h };
};

// The viewport at rest, a drawn frame no different from the one before it (decoded only where their
// bytes differ, the first where no animation runs and the fonts are loaded), asked again within the
// budget, a page still changing when it ends no verdict.
const settled = async (page, budget = STEP_MS) => {
  const end = Date.now() + budget;
  let last = await drawn(page);
  if (await page.evaluate(() => document.getAnimations().length === 0 && document.fonts.status === 'loaded'))
    return Object.assign(pngPixels(last), { buf: last });
  for (;;) {
    const next = await drawn(page);
    if (next.equals(last)) return Object.assign(pngPixels(next), { buf: next });
    const shown = pngPixels(next), ch = shotChanges(pngPixels(last), shown);
    if (ch && ch.cols.size === 0) return Object.assign(shown, { buf: next });
    if (Date.now() >= end) throw new Unfinished(`the page still changed after ${budget} ms`);
    last = next;
  }
};

// The runs of adjacent changed columns, each with its first and last changed row.
const changeBands = (ch) => {
  const bands = [];
  for (const x of [...ch.cols.keys()].sort((p, q) => p - q)) {
    const rows = ch.cols.get(x), last = bands[bands.length - 1];
    if (last && x === last.to + 1) {
      last.to = x; last.top = Math.min(last.top, rows[0]); last.bottom = Math.max(last.bottom, rows[rows.length - 1]);
    } else bands.push({ from: x, to: x, top: rows[0], bottom: rows[rows.length - 1] });
  }
  return bands;
};

// Under the pager a stage is no tab stop, so an address or a click focuses none that fits its box.
const stagePagerJudge = () => {
  const stages = [...document.querySelectorAll('section.slide, section.section-page')];
  const bad = document.documentElement.hasAttribute('data-deck-script') ? [] : ['the pager did not run'];
  for (const s of stages) {
    const name = s.id || s.dataset.slideLabel || '-';
    if (s.hasAttribute('tabindex')) { bad.push(`${name} stays a tab stop under the pager`); continue; }
    if (s.scrollHeight > s.clientHeight + 1 || s.scrollWidth > s.clientWidth + 1) continue;
    s.focus({ preventScroll: true });
    if (document.activeElement === s) { bad.push(`${name} takes focus under the pager`); s.blur(); }
  }
  return { n: stages.length, bad };
};

// A stage read without the pager, focused under keyboard modality: its outline, ground and mark,
// its furniture's boxes, and its kind; every stage's premises when `only` is null.
const stageMarkJudge = (only) => {
  const stages = [...document.querySelectorAll('section.slide[tabindex], section.section-page[tabindex]')];
  const parts = [['band', ':scope > header'], ['footline', ':scope > footer.slide-foot'], ['logo', ':scope .slide-logo']];
  const read = (s) => {
    s.focus({ preventScroll: true });
    const cs = getComputedStyle(s), mark = getComputedStyle(s, '::before'), r = s.getBoundingClientRect();
    const furniture = parts.flatMap(([what, sel]) => [...s.querySelectorAll(sel)].map(el => {
      const q = el.getBoundingClientRect();
      return { what, box: { left: q.left, right: q.right, top: q.top, bottom: q.bottom } };
    }));
    const probe = document.createElement('div');
    probe.style.cssText = 'position: absolute; width: var(--safearea, 6vmin); height: 0; color: var(--ltx-focus)';
    s.append(probe);
    const safe = probe.getBoundingClientRect().width, focus = getComputedStyle(probe).color;
    probe.remove();
    const sides = [mark.borderLeftColor, mark.borderRightColor];
    const m = { name: s.id || s.dataset.slideLabel || '-', seen: s.matches(':focus-visible'), safe,
      outline: cs.outlineStyle,
      marked: mark.content !== 'none' && mark.borderLeftStyle !== 'none' && mark.borderRightStyle !== 'none',
      inked: sides.every(c => c === cs.color) || sides.every(c => c === focus),
      still: mark.position === 'sticky' || mark.position === 'fixed' ||
        (mark.position === 'absolute' && s.scrollHeight <= s.clientHeight + 1),
      width: parseFloat(mark.borderLeftWidth) || 0, shown: Math.abs(r.left) < 0.5,
      spills: s.scrollHeight > s.clientHeight + 1, furniture,
      kind: [s.className, s.closest('.slide-track') ? 'stepped' : '', ...furniture.map(f => f.what)].join(' ') };
    s.blur();
    return m;
  };
  if (only !== null) return read(stages[only]);
  const bad = [], kinds = new Map();
  stages.forEach((s, i) => {
    const m = read(s), why = [];
    if (!m.seen) why.push('takes no visible focus');
    if (m.outline !== 'none') why.push(`draws a ${m.outline} outline`);
    if (!m.marked) why.push('draws no mark');
    if (!m.inked) why.push('marks in no colour or neither in its ink nor in the focus colour');
    if (!m.still) why.push('marks in a box that scrolls with its content');
    if (why.length) bad.push(`${m.name} ${why.join(', ')}`);
    if (!kinds.has(m.kind)) kinds.set(m.kind, i);
  });
  return { n: stages.length, bad, kinds: [...kinds.entries()].map(([kind, i]) => [i, /band|footline|logo/.test(kind)]) };
};

// One stage at its snap: focusing it changes pixels only inside its side margins, off the
// viewport's outermost pixels and outside its band, footline and logo; with its children hidden,
// two bands each its mark's width or a pixel more, the same scrolled to its end when it spills.
const stageMarkShot = async (p, k, scale, shape, measure, budget) => {
  const at = `at ${shape} ${scale}x`;
  const sel = 'section.slide[tabindex], section.section-page[tabindex]';
  await p.evaluate(({ k, sel }) => {
    const s = document.querySelectorAll(sel)[k];
    s.scrollTop = 0;
    (s.closest('.slide-track') || s).scrollIntoView({ behavior: 'instant', inline: 'start', block: 'nearest' });
  }, { k, sel });
  // a page without script runs no animation frame; each shot is the frame it draws at rest
  const shot = () => settled(p, budget);
  let rest = await shot();
  const m = await p.evaluate(stageMarkJudge, k);
  if (!m.shown) return [`${at} ${m.name} stands off the viewport`];
  // a page that moved between the shots, its blurred frame no longer its first, gave no verdict
  const pair = async () => {
    const plain = rest || await shot();
    rest = null;
    await p.evaluate(({ k, sel }) => document.querySelectorAll(sel)[k].focus({ preventScroll: true }),
      { k, sel });
    const marked = await shot();
    await p.evaluate(() => document.activeElement && document.activeElement.blur());
    const again = await drawn(p);
    if (!again.equals(plain.buf)) {
      const back = shotChanges(plain, pngPixels(again));
      if (!back || back.cols.size > 0) throw new Unfinished('the page changed while focus was judged');
    }
    return shotChanges(plain, marked);
  };
  const off = [];
  const seen = await pair();
  if (!seen) return [`${at} focusing ${m.name} changes the viewport at large`];
  // a safe area narrower than the mark leaves it no margin to stand in, nor its side to keep clear,
  // and a fractional scale rounds an edge a device pixel either way
  const cols = [...seen.cols.keys()];
  const margin = Math.ceil(Math.max(m.safe, m.width) * scale) + (Number.isInteger(scale) ? 0 : 1);
  const clear = Math.min(m.safe / 2, m.safe - m.width) * scale >= 1;
  if (cols.length === 0) off.push(`${at} ${m.name} shows no mark`);
  if (cols.some(x => x >= margin && x < seen.w - margin))
    off.push(`${at} focusing ${m.name} changes pixels outside its side margins`);
  if ((clear && cols.some(x => x < 1 || x > seen.w - 2)) ||
      [...seen.cols.values()].some(rows => rows[0] < 1 || rows[rows.length - 1] > seen.h - 2))
    off.push(`${at} focusing ${m.name} changes the viewport's outermost pixels`);
  for (const f of m.furniture) {
    const x0 = Math.ceil(f.box.left * scale), x1 = Math.floor(f.box.right * scale);
    const y0 = Math.ceil(f.box.top * scale), y1 = Math.floor(f.box.bottom * scale);
    for (const [x, rows] of seen.cols)
      if (x >= x0 && x < x1 && rows.some(y => y >= y0 && y < y1)) {
        off.push(`${at} focusing ${m.name} changes its ${f.what}`);
        break;
      }
  }
  if (!measure && !m.spills) return off;
  await p.evaluate(() => {
    const hide = document.createElement('style');
    hide.id = 'ltx-oracle-hide';
    hide.textContent = 'section.slide > *, section.section-page > * { visibility: hidden !important; }';
    document.head.append(hide);
  });
  try {
    const whole = await pair();
    const bands = whole ? changeBands(whole) : [];
    if (measure) {
      if (bands.length !== 2) off.push(`${at} ${m.name}'s mark is ${bands.length} bands of pixels, not two`);
      for (const b of bands)
        if (b.to - b.from + 1 > Math.ceil(m.width * scale) + 1)
          off.push(`${at} ${m.name}'s mark is a band ${b.to - b.from + 1} device px wide`);
      if (bands.length === 2 && !(bands[0].to < whole.w / 2 && bands[1].from > whole.w / 2))
        off.push(`${at} ${m.name}'s mark leaves its side margins`);
    }
    if (m.spills && bands.length > 0) {
      const end = await p.evaluate(({ k, sel }) => {
        const s = document.querySelectorAll(sel)[k];
        s.scrollTop = s.scrollHeight;
        return s.scrollTop;
      }, { k, sel });
      const later = await pair();
      const moved = later ? changeBands(later) : [];
      const same = moved.length === bands.length && moved.every((b, i) =>
        Math.abs(b.from - bands[i].from) <= 1 && Math.abs(b.to - bands[i].to) <= 1 &&
        Math.abs(b.top - bands[i].top) <= 1 && Math.abs(b.bottom - bands[i].bottom) <= 1);
      if (!same) off.push(`${at} ${m.name}'s mark moves as the stage scrolls ${end}px`);
    }
  } finally {
    await p.evaluate(() => document.getElementById('ltx-oracle-hide').remove());
  }
  return off;
};

// A focused stage shows the deck's own mark, never the browser's ring: under the pager no stage
// is a tab stop, and read without it every stage draws no outline but a mark in its ink or the
// deck's focus colour that holds still as the stage scrolls, which one stage of each kind shows as
// two bands of pixels inside its side margins, clear of the viewport's edges and its band, footline
// and logo, at the deck's own aspect at 1x, 1.5x and 2x, and a stage of each kind with furniture
// shows so at every reader shape; each shot is a frame at rest, and a page still changing when its
// budget ends leaves the cell inconclusive.
const stageFocus = async (page, browser, open, budget = STEP_MS) => {
  const deck = await page.evaluate(() =>
    /mandatory/.test(getComputedStyle(document.documentElement).scrollSnapType));
  if (!deck) return { ok: true, n: 0, why: '' };
  const pt = /^([\d.]+)pt ([\d.]+)pt$/.exec((await pageSizeOf(page)).trim());
  if (!pt) return { ok: false, n: 1, why: 'no @page size in points' };
  const W = 1280, H = Math.round(1280 * +pt[2] / +pt[1]);
  const off = (await page.evaluate(stagePagerJudge)).bad.slice(0, 2);
  const at = async (scale, body) => {
    const ctx = budgeted(await browser.newContext({ viewport: { width: W, height: H },
      deviceScaleFactor: scale, javaScriptEnabled: false }));
    try {
      const p = await ctx.newPage();
      await open(p);
      await p.evaluate(() => document.fonts.ready);
      await p.keyboard.press('Shift');
      return await body(p);
    } finally { await ctx.close(); }
  };
  try {
    const judged = await at(1, (p) => p.evaluate(stageMarkJudge, null));
    off.push(...judged.bad.slice(0, 2));
    // the scales and shapes are judged side by side, each in a context of its own
    const shapes = [[1, ['own', W, H]], ...readerShapes.map((s) => [1, s]), [1.5, ['own', W, H]],
      [2, ['own', W, H]]];
    const runs = await Promise.allSettled([...shapes.map(([scale, [shape, w, h]]) => at(scale, async (p) => {
      const found = [];
      await p.setViewportSize({ width: w, height: h });
      for (const [k, furnished] of judged.kinds)
        if (shape === 'own' || furnished)
          found.push(...await stageMarkShot(p, k, scale, shape, shape === 'own', budget));
      return found;
    })), at(1, async (p) => {
      const found = [];
      if (judged.n > 0) {
        // forced colours keep the mark in their own ink, so a focused stage still shows its focus
        await p.emulateMedia({ forcedColors: 'active' });
        const sel = 'section.slide[tabindex], section.section-page[tabindex]';
        await p.evaluate((sel) => {
          const s = document.querySelector(sel);
          (s.closest('.slide-track') || s).scrollIntoView({ behavior: 'instant', inline: 'start', block: 'nearest' });
        }, sel);
        const plain = await settled(p, budget);
        await p.evaluate((sel) => document.querySelector(sel).focus({ preventScroll: true }), sel);
        const marked = await settled(p, budget);
        await p.evaluate(() => document.activeElement && document.activeElement.blur());
        const forced = shotChanges(plain, marked);
        if (forced && forced.cols.size === 0) found.push('in forced colours a focused stage shows no focus');
      }
      return found;
    })]);
    const lost = runs.find((r) => r.status === 'rejected');
    if (lost) throw lost.reason;
    for (const r of runs) off.push(...r.value);
    return { ok: off.length === 0, n: judged.n, findings: off,
      why: off.length ? `${off.length} findings; ${off.slice(0, 4).join('; ')}` : '' };
  } catch (e) {
    if (!unfinished(e)) throw e;
    return { ok: false, n: 1, unfinished: true, findings: off, why: clean(e.message) };
  }
};

// Under the pager a key a focused element can still scroll by scrolls it, and at its end the key
// pages and the focus left in the stage it pages past is released.
const deckKeys = async (page) => {
  const why = [];
  await settled(page);
  const start = await page.evaluate(() => location.hash);
  const found = await page.evaluate(() => {
    const pre = [...document.querySelectorAll('section.slide pre[tabindex]')]
      .find(p => p.scrollWidth > p.clientWidth + 1);
    if (!pre) return false;
    pre.scrollLeft = 0;
    pre.focus();
    return true;
  });
  if (!found) return { ok: false, n: 1, why: 'no code block runs past its box' };
  await page.keyboard.press('ArrowRight');
  await settled(page);
  const held = await page.evaluate(() => ({ tag: document.activeElement.tagName,
    left: document.activeElement.scrollLeft, hash: location.hash }));
  if (held.tag !== 'PRE' || held.left <= 0 || held.hash !== start)
    why.push(`a focused code block running past its box paged instead of scrolling (${JSON.stringify(held)})`);
  await page.evaluate(() => { const a = document.activeElement; a.scrollLeft = a.scrollWidth; });
  await page.keyboard.press('ArrowRight');
  await settled(page);
  const left = await page.evaluate(() => ({ hash: location.hash,
    held: !!document.activeElement.closest('.slide-track, section.slide, section.section-page') }));
  if (left.hash === start) why.push('a code block at its end kept the key from paging');
  if (left.held) why.push('paging left the focus in the stage it paged past');
  return { ok: why.length === 0, n: 1, why: why.join('; ') };
};

// A display wider than its stage scrolls sideways inside its own box, a tab stop holding all its
// ink's height; its stage never scrolls sideways.
const wideDisplays = () => {
  const bad = [];
  let n = 0;
  for (const d of document.querySelectorAll('section.slide .display')) {
    const s = d.closest('section.slide');
    const r = document.createRange();
    r.selectNodeContents(d);
    if (r.getBoundingClientRect().width <= d.clientWidth + 1) continue;
    n++;
    const at = s.id || '-';
    if (s.scrollWidth > s.clientWidth + 1) bad.push(`${at} scrolls sideways for its display`);
    if (d.scrollWidth <= d.clientWidth + 1) bad.push(`${at}'s display runs past its box unscrolled`);
    if (d.scrollHeight > d.clientHeight + 1) bad.push(`${at}'s display cuts its ink's height`);
    if (d.tabIndex !== 0) bad.push(`${at}'s scrolling display is no tab stop`);
  }
  return { ok: n > 0 && bad.length === 0, n,
    why: bad.length ? bad.join('; ') : n ? '' : 'no display wider than its stage' };
};

// Read without the pager, an address naming a page-less section's label, and a scroll into view
// by its own default of the section's heading, land on the stage set after the section.
const stageLanding = async (p, url, label, stage) => {
  const at = () => p.evaluate(() => {
    const s = [...document.querySelectorAll('section.slide, section.section-page')]
      .find(e => Math.abs(e.getBoundingClientRect().left) < 1);
    return s ? s.id || s.dataset.slideLabel || '-' : 'no stage';
  });
  const why = [];
  await p.goto(url + '#' + encodeURIComponent(label));
  await settled(p);
  const byAddress = await at();
  if (byAddress !== stage) why.push(`the address #${label} landed on ${byAddress}`);
  await p.goto(url);
  await settled(p);
  await p.evaluate(() => document.querySelector('section.slide > h2').scrollIntoView());
  await settled(p);
  const byScroll = await at();
  if (byScroll !== stage) why.push(`the section's heading scrolled into view landed on ${byScroll}`);
  return { ok: why.length === 0, n: 1, why: why.join('; ') };
};

const deckLinks = async (page, url) => {
  const info = await page.evaluate(() => {
    if (!document.documentElement.hasAttribute('data-deck-script')) return null;
    const snaps = [...document.querySelectorAll('[data-snap]')];
    const stageOf = s => s.closest('.slide-track') || s;
    // Frame numbers can restart: group by stage identity, never by number.
    const stages = [...new Set(snaps.map(stageOf))];
    const labels = snaps.map(s => s.dataset.slideLabel);
    const routes = new Map(labels.map((label, i) => [label, i]));
    labels.forEach((label, i) => {
      if (label?.endsWith('.1')) routes.set(label.slice(0, -2), i);
    });
    const ids = [...document.querySelectorAll('[id]')].map(el => el.id);
    // Canonical routes take priority over a colliding native title or spacer ID.
    const aliases = [...new Set([...snaps, ...stages])].filter(el => el.id)
      .map(el => ({id: el.id, i: snaps.findIndex(s => s === el || stageOf(s) === el)}))
      .filter(({id, i}) => ids.filter(other => other === id).length === 1 &&
        (!routes.has(id) || routes.get(id) === i));
    return {labels, aliases,
      routes: Object.fromEntries([...routes, ...aliases.map(({id, i}) => [id, i])]),
      stages: stages.map(stage => snaps.flatMap((s, i) => stageOf(s) === stage ? [i] : []))};
  });
  if (!info || info.labels.length === 0) return {n: 0};
  // The page at rest: unchanged across two frames, standing at the snap its address names or
  // still after a scroll seen to end; or unchanged for ten frames with no scroll in flight.
  const restAt = ([routes, i, token]) => {
    let st = globalThis.ltxRest;
    if (!st || st.token !== token) {
      if (st) st.off();
      const on = {scroll: () => { st.moving = true; st.scrolled = true; },
        scrollend: () => { st.moving = false; }};
      st = globalThis.ltxRest = {token, last: null, still: 0, moving: false, scrolled: false,
        off: () => { for (const [t, f] of Object.entries(on)) removeEventListener(t, f, true); }};
      for (const [t, f] of Object.entries(on)) addEventListener(t, f, true);
    }
    const snaps = document.querySelectorAll('[data-snap]');
    const shown = k => {
      const snap = snaps[k];
      if (!snap) return false;
      const track = snap.closest('.slide-track');
      const el = snap.getBoundingClientRect().width > 0 || !track ? snap : track.querySelector('section.slide');
      const step = track ? [...track.querySelectorAll('[data-snap]')].indexOf(snap) + 1 : 0;
      return Math.abs(el.getBoundingClientRect().left) < 1 &&
        (!track || track.dataset.snapped === String(step));
    };
    let key = null;
    try { key = decodeURIComponent(location.hash.slice(1)); } catch (_) {}
    const named = key !== null && Object.hasOwn(routes, key) ? routes[key] : -1;
    const marks = [...document.querySelectorAll('.slide-track')].map(t => t.dataset.snapped);
    st.seen = {named, shown: shown(i), standing: named >= 0 && shown(named), hash: location.hash};
    const sig = JSON.stringify([scrollX, scrollY, st.seen, marks]);
    st.still = sig === st.last ? st.still + 1 : 0;
    st.last = sig;
    const rest = (st.still >= 1 && (named < 0 || st.seen.standing || (st.scrolled && !st.moving))) ||
      (st.still >= 10 && !st.moving);
    if (rest) st.off();
    return rest && st.seen;
  };
  let rests = 0;
  const expect = async (i, label = info.labels[i]) => {
    const want = '#' + encodeURIComponent(label);
    let seen;
    try {
      seen = await (await page.waitForFunction(restAt, [info.routes, i, ++rests])).jsonValue();
    } catch (e) {
      if (!unfinished(e)) throw e;
      const last = await page.evaluate(() => globalThis.ltxRest && globalThis.ltxRest.seen);
      throw new Unfinished(`no rest in ${STEP_MS} ms` +
        (last ? `, last at address ${last.hash} with snap ${i} ${last.shown ? 'shown' : 'not shown'}` : ''));
    }
    if (!seen.shown || seen.hash !== want)
      throw new Error(`came to rest at address ${seen.hash} with snap ${i} ` +
        `${seen.shown ? 'shown' : 'not shown'}; expected address ${want} with it shown`);
  };
  const visit = async (i, label = info.labels[i], base = url) => {
    await page.goto(base + '#' + encodeURIComponent(label));
    await expect(i, label);
  };
  const stepped = info.stages.find(s => s.length > 1);
  let phase = 'emitted labels';
  let floorFile = null;
  let verdict = {ok: true, n: 1};
  try {
    if (info.labels.some(label => typeof label !== 'string' || !label.trim()))
      throw new Error('a snap has no data-slide-label');
    if (new Set(info.labels).size !== info.labels.length)
      throw new Error('canonical slide labels are not unique');
    phase = 'initial fragment';
    await expect(0);
    for (let i = 0; i < info.labels.length; i++) {
      phase = 'canonical fragment ' + info.labels[i];
      await visit(i);
    }
    phase = 'canonical reload';
    await page.reload();
    await expect(info.labels.length - 1);
    for (let i = 0; i < info.labels.length; i++) {
      if (!info.labels[i].endsWith('.1')) continue;
      const bare = info.labels[i].slice(0, -2);
      phase = 'bare first reveal ' + bare;
      await visit(i, bare);
      await page.reload();
      await expect(i, bare);
    }
    for (const {id, i} of info.aliases) {
      phase = 'native alias ' + id;
      await visit(i, id);
    }
    if (info.labels.length > 1) {
      phase = 'keyboard next';
      await visit(0);
      await page.keyboard.press('ArrowRight');
      await expect(1);
      phase = 'history back';
      await page.goBack(); await expect(0);
      phase = 'history forward';
      await page.goForward(); await expect(1);
      await page.reload(); await expect(1);
    }
    const lastStage = info.stages[info.stages.length - 1][0];
    if (info.stages.length > 1) {
      phase = 'native scroll';
      await visit(0);
      await page.evaluate(i => {
        const snap = document.querySelectorAll('[data-snap]')[i];
        const el = snap.getBoundingClientRect().width > 0 ? snap :
          snap.closest('.slide-track').querySelector('section.slide');
        el.scrollIntoView({behavior: 'instant', inline: 'start', block: 'nearest'});
      }, lastStage);
      await expect(lastStage);
    }
    await page.emulateMedia({reducedMotion: 'reduce'});
    await page.reload();
    const middle = info.stages.findIndex((s, i) => s.length > 1 && i > 0 && i + 1 < info.stages.length);
    if (middle >= 0) {
      const [a, b, c] = info.stages.slice(middle - 1, middle + 2).map(s => s[0]);
      phase = 'reduced-motion forward through a stepped stage';
      await visit(a);
      await page.keyboard.press('ArrowRight'); await expect(b);
      await page.keyboard.press('ArrowRight'); await expect(c);
      phase = 'reduced-motion history';
      await page.goBack(); await expect(b);
      await page.goForward(); await expect(c);
      await page.reload(); await expect(c);
      phase = 'reduced-motion reverse through a stepped stage';
      await page.keyboard.press('ArrowLeft'); await expect(b);
      await page.keyboard.press('ArrowLeft'); await expect(a);
    }
    phase = 'reduced-motion End and Home';
    await visit(0);
    await page.keyboard.press('End'); await expect(lastStage);
    await page.keyboard.press('Home'); await expect(0);
    if (stepped) {
      phase = 'reduced-motion explicit reveal and reload';
      await visit(stepped[1]);
      await page.reload(); await expect(stepped[1]);
      const stage = info.stages.indexOf(stepped);
      if (stage + 1 < info.stages.length) {
        phase = 'reduced-motion next stage from an explicit reveal';
        await page.keyboard.press('ArrowRight'); await expect(info.stages[stage + 1][0]);
      }
      if (stage > 0) {
        phase = 'reduced-motion previous stage from an explicit reveal';
        await visit(stepped[1]);
        await page.keyboard.press('ArrowLeft'); await expect(info.stages[stage - 1][0]);
      }
      await page.emulateMedia({reducedMotion: 'no-preference'});
      phase = 'hidden-spacer floor';
      const fs = require('fs');
      const source = fs.readFileSync(new URL(url), 'utf8');
      // Force the emitted fallback rules before script startup, including on reload.
      const floor = source.replace(/@supports (not )?\(animation-timeline: view\(\)\)/g,
        '@supports $1(ltx-oracle-no-timeline: none)');
      if (floor === source) throw new Error('no view-timeline gate to exercise the floor');
      const floorUrl = new URL(url);
      floorUrl.pathname += '.floor-' + process.pid + '.html';
      fs.writeFileSync(floorUrl, floor, {flag: 'wx'});
      floorFile = floorUrl;
      await visit(stepped[0], info.labels[stepped[0]], floorUrl.href);
      const hidden = await page.evaluate(indices => indices.every(i =>
        document.querySelectorAll('[data-snap]')[i].getBoundingClientRect().width === 0) &&
        !matchMedia('(prefers-reduced-motion: reduce)').matches, stepped);
      if (!hidden) throw new Error('the floor did not collapse the stepped spacers');
      await page.keyboard.press('ArrowRight'); await expect(stepped[1]);
      phase = 'hidden-spacer history back';
      await page.goBack(); await expect(stepped[0]);
      phase = 'hidden-spacer history forward';
      await page.goForward(); await expect(stepped[1]);
      phase = 'hidden-spacer reload and scroll sync';
      await page.reload(); await expect(stepped[1]);
      await page.evaluate(async () => {
        dispatchEvent(new Event('scroll'));
        await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
      });
      await expect(stepped[1]);
    }
  } catch (e) {
    verdict = {ok: false, n: 1, unfinished: unfinished(e), why: phase + ': ' + clean(e.message)};
  }
  // A cleanup that fails leaves the verdict standing and the fixture's later checks unmeasured.
  try {
    if (floorFile) require('fs').unlinkSync(floorFile);
    await page.evaluate(() => { if (globalThis.ltxRest) globalThis.ltxRest.off(); });
    await page.emulateMedia({reducedMotion: 'no-preference'});
    await page.goto(url);
    await page.evaluate(() => document.fonts.ready);
  } catch (e) { verdict.after = e; }
  return verdict;
};

async function runReader(name) {
  let browser;
  try {
    browser = await pw[name].launch({ headless: true, timeout: 2 * STEP_MS,
      args: name === 'chromium' ? ['--no-sandbox', '--disable-gpu'] : [] });
  } catch (e) {
    out('reader', name, 'unavailable', clean(String(e && e.message || e).split('\n')[0]));
    return;
  }
  out('reader', name, 'version', browser.version());
  // Both sides of the content/advance distinction, checked with the same
  // live-page judge before any fixture can be credited to this reader.
  const controlCtx = budgeted(await browser.newContext());
  const control = await controlCtx.newPage();
  try {
    const visible = '<math><mi>x</mi></math>';
    const carrier = '<math style="font-size:0"><mpadded height="0px" depth="0px">' +
      '<mrow style="font-size:16px"><mi>x</mi></mrow></mpadded></math>';
    for (const [label, html, want] of [
      ['ordinary', visible, true],
      ['zero-height carrier', carrier, true],
      ['hidden', '<div style="display:none">' + carrier + '</div>', false],
      ['empty', '<math></math>', false],
      ['zero-size contents', carrier.replace('font-size:16px', 'font-size:0'), false],
    ]) {
      await control.setContent(html);
      const got = await control.evaluate(checks.mathml);
      if (got.n !== 1 || got.ok !== want) throw new Error('mathml control: ' + label);
    }
    await control.setContent(visible);
    await control.evaluate(() => {
      const wrong = document.createElementNS('http://www.w3.org/1999/xhtml', 'math');
      wrong.textContent = 'x';
      document.querySelector('math').replaceWith(wrong);
    });
    if ((await control.evaluate(checks.mathml)).ok) throw new Error('mathml control: namespace');
    // The math-line judge breaks twice: a run its column narrows parts at a
    // space, and a run's edge spaces collapse; the same runs kept pass.
    const narrowRun = (style) => '<div style="width: 120px"><math display="block"><mtable><mtr><mtd>' +
      '<mi' + style + '>by an invented placeholder reason</mi></mtd></mtr></mtable></math></div>';
    await control.setContent(narrowRun(''));
    const parted = await control.evaluate(mathLineJudge);
    if (parted.ok || parted.n !== 1) throw new Error('math-line control: a parted run');
    await control.setContent(narrowRun(' style="white-space: pre"'));
    const kept = await control.evaluate(mathLineJudge);
    if (!kept.ok || kept.n !== 1) throw new Error('math-line control: a kept run');
    const edged = (style) => '<math><mi' + style + '> if </mi></math>';
    await control.setContent(edged(' style="white-space: nowrap"'));
    if ((await control.evaluate(mathLineJudge)).ok) throw new Error('math-line control: collapsed edge spaces');
    await control.setContent(edged(' style="white-space: pre"'));
    if (!(await control.evaluate(mathLineJudge)).ok) throw new Error('math-line control: kept edge spaces');
    // The shape report names what a narrow window costs a stage and nothing at
    // the deck's own aspect, a held run it clips and a line it re-wraps, or says
    // its control failed, a report the gate never reads.
    try {
      const stagePage = '<style>html { scroll-snap-type: x mandatory } section.slide { width: 100vw; ' +
        'height: 100dvh; overflow: auto } p { font-size: 4vh; margin: 0 }</style><section class="slide" ' +
        'id="s1"><p>an invented line the deck holds</p><p style="white-space: nowrap">a held invented ' +
        'run wider than a phone</p></section>';
      await control.setViewportSize({ width: 1280, height: 720 });
      await control.setContent(stagePage);
      const ownShape = await control.evaluate(shapeRead, textBlocks);
      await control.setViewportSize({ width: 390, height: 844 });
      const narrowShape = await control.evaluate(shapeRead, textBlocks);
      const ok = ownShape.length === 1 && ownShape[0].clipped.length === 0 &&
        narrowShape[0].clipped.some(c => c.startsWith('p "a held')) &&
        narrowShape[0].counts[0][1] > ownShape[0].counts[0][1];
      if (!ok) out('shape', '-', name, 'control', '-', 'unmeasured: the control reads ' +
        clean(JSON.stringify([ownShape[0], narrowShape[0]])));
    } catch (e) {
      out('shape', '-', name, 'control', '-', 'unmeasured: ' + clean(String(e.message).split('\n')[0]));
    } finally {
      await control.setViewportSize({ width: 1280, height: 720 });
    }
    // The stage-focus judge breaks five ways (the browser's ring at the viewport's edges, a mark
    // into the foot, a mark that scrolls with its stage, a mark forced colours drop, a tab stop
    // under the pager), passes the deck's mark beside a bar that runs once across the top, and is
    // inconclusive, never failing, on a page that never rests or that moves in steps.
    const focusStage = (rule, body) => '<!doctype html><html data-deck-script><head><style>@page { size: 960pt 540pt } html { scroll-snap-type: x mandatory } ' +
      'body { margin: 0 } main { display: flex } section.slide { box-sizing: border-box; width: 100vw; ' +
      'flex: 0 0 100vw; height: 100dvh; padding: 0 6vmin; overflow-y: auto; position: relative; display: flex; ' +
      'flex-direction: column; background: #fff; color: #222 } footer.slide-foot { position: sticky; ' +
      'bottom: 0; margin: auto -6vmin 0; height: 3vh; flex-shrink: 0 } footer.slide-foot > span { ' +
      'position: absolute; left: 1vh; bottom: 0; font: 2vh sans-serif } ' + rule + '</style></head><body>' +
      '<main><section class="slide" tabindex="0" data-snap>' + body + '<footer class="slide-foot">' +
      '<span>An invented footline</span></footer></section></main></body></html>';
    const focusInk = 'linear-gradient(currentColor, currentColor)';
    const focusMark = (size) => 'section.slide:focus-visible { outline: none; background-image: ' + focusInk +
      ', ' + focusInk + '; background-size: 2px ' + size + '; background-position: left 3vmin center, ' +
      'right 3vmin center; background-repeat: no-repeat }';
    const deckMark = (top, height) => 'section.slide:focus-visible { outline: none } ' +
      'section.slide:focus-visible::before { content: ""; position: sticky; top: ' + top + '; flex: none; ' +
      'align-self: stretch; height: ' + height + '; margin: 0 calc(50% - 50vw + 3vmin) -' + height +
      '; border-inline: 2px solid; pointer-events: none }';
    const focusScrolls = 'section.slide:focus-visible { outline: none } section.slide:focus-visible::before { ' +
      'content: ""; position: absolute; top: 25%; height: 50%; left: 3vmin; right: 3vmin; ' +
      'border-left: 2px solid; border-right: 2px solid }';
    const bar = (run) => '.ltx-bar { position: fixed; top: 0; left: 0; width: 100%; height: 3px; ' +
      'background: #222; transform-origin: 0 50%; animation: ltx-oracle-bar ' + run + ' } ' +
      '@keyframes ltx-oracle-bar { from { transform: scaleX(0) } to { transform: scaleX(1) } }';
    const focusLine = '<p>An invented line.</p>';
    for (const [label, html, want] of [
        ['the browser ring', focusStage('', focusLine), /outermost/],
        ['a mark into the foot', focusStage(deckMark('0', '100dvh'), focusLine), /changes its footline/],
        ['a mark that scrolls', focusStage(focusScrolls, focusLine.repeat(60)), /moves as the stage scrolls/],
        ['a mark forced colours drop', focusStage(focusMark('50%'), focusLine), /forced colours/],
        ['a tab stop under the pager', focusStage(deckMark('25dvh', '50dvh'), focusLine), /tab stop under the pager/]]) {
      await control.setContent(html);
      if (!label.startsWith('a tab stop'))
        await control.evaluate(() => document.querySelector('section.slide').removeAttribute('tabindex'));
      const got = await stageFocus(control, browser, (p) => p.setContent(html));
      if (got.ok || got.unfinished || !got.findings.some(f => want.test(f)))
        throw new Error('stage-focus control: ' + label + ' ' + got.why);
    }
    const once = focusStage(deckMark('25dvh', '50dvh') + bar('4s linear both'), '<div class="ltx-bar"></div>' + focusLine);
    await control.setContent(once);
    await control.evaluate(() => document.querySelector('section.slide').removeAttribute('tabindex'));
    const rested = await stageFocus(control, browser, (p) => p.setContent(once));
    if (!rested.ok) throw new Error('stage-focus control: a bar that runs once ' + rested.why);
    for (const [label, run] of [['a page that never rests', '1s linear infinite'],
        ['a page that moves in steps', '2s steps(4) infinite']]) {
      const ever = focusStage(deckMark('25dvh', '50dvh') + bar(run), '<div class="ltx-bar"></div>' + focusLine);
      await control.setContent(ever);
      await control.evaluate(() => document.querySelector('section.slide').removeAttribute('tabindex'));
      const restless = await stageFocus(control, browser, (p) => p.setContent(ever), STEP_MS / 30);
      if (!restless.unfinished) throw new Error('stage-focus control: ' + label + ' ' + restless.why);
    }
    // Both disclosure judges break once: a closed body forced into view on
    // screen, and a closed body printed with no print rule to show it.
    const closed = '<details><summary>A</summary><p>B</p></details>';
    const lift = '<style>@media print { details::details-content { content-visibility: visible; } ' +
      'summary { list-style: none; } }</style>';
    await control.setContent(closed);
    if (!(await control.evaluate(checks.disclosure)).ok) throw new Error('disclosure control: native');
    await control.setContent('<style>details::details-content { content-visibility: visible; }</style>' + closed);
    if ((await control.evaluate(checks.disclosure)).ok) throw new Error('disclosure control: forced open');
    await control.emulateMedia({ media: 'print' });
    await control.setContent(closed);
    if ((await control.evaluate(mediaChecks['print-disclosure'])).ok)
      throw new Error('print-disclosure control: no print rule');
    await control.setContent(lift + closed);
    if (!(await control.evaluate(mediaChecks['print-disclosure'])).ok)
      throw new Error('print-disclosure control: the print rule');
    // The code-wrap judge breaks once: a narrow block whose atoms are held
    // wraps between them, and the same block with nothing held wraps
    // inside a token.
    const atoms = '<span class="tok">alpha_beta</span><span class="tok">-&gt;</span>'.repeat(6);
    await control.emulateMedia({ media: 'screen' });
    const block = (rule) => '<style>' + rule + '</style><pre style="width: 120px; ' +
      'white-space: pre-wrap; overflow-wrap: break-word; font: 14px monospace"><code>' +
      atoms + '</code></pre>';
    await control.setViewportSize({ width: 400, height: 300 });
    await control.setContent(block('pre .tok { white-space: nowrap; }'));
    const held = await control.evaluate(codeWrapJudge, codeTables);
    if (!held.ok || held.wraps === 0) throw new Error('code-wrap control: held atoms ' + held.why);
    await control.setContent(block(''));
    if ((await control.evaluate(codeWrapJudge, codeTables)).ok) throw new Error('code-wrap control: nothing held');
    // Two units of one fallback token part only at the `<wbr>` between them,
    // and a pair of units wider than the line with no `<wbr>` between them
    // parts where the page marked no break.
    const units = (unit, sep) => '<pre style="width: 120px; white-space: pre-wrap; overflow-wrap: break-word; ' +
      'font: 14px monospace"><code>' + ('<span class="tok">' + unit[0] + '</span>' + sep +
      '<span class="tok">' + unit[1] + '</span><wbr>').repeat(6) + '</code></pre>';
    await control.setContent('<style>pre .tok { white-space: nowrap; }</style>' +
      units(['0000000', 'xxxxxxx'], '<wbr>'));
    const marked = await control.evaluate(codeWrapJudge, codeTables);
    if (!marked.ok || marked.wraps === 0) throw new Error('code-wrap control: units at their wbr ' + marked.why);
    await control.setContent('<style>pre .tok { white-space: nowrap; }</style>' +
      units(['00000000', 'xxxxxxxx'], ''));
    if ((await control.evaluate(codeWrapJudge, codeTables)).ok) throw new Error('code-wrap control: units unmarked');
    // A wrapping block whose held atom runs past its box fails it.
    await control.setContent('<style>pre .tok { white-space: nowrap; }</style><pre style="width: 120px; ' +
      'white-space: pre-wrap; font: 14px monospace"><code><span class="tok">' + 'x'.repeat(40) +
      '</span></code></pre>');
    if ((await control.evaluate(codeWrapJudge, codeTables)).ok) throw new Error('code-wrap control: overflow');
    // The paper judge breaks once: a held atom wider than the sheet prints
    // the page small and loses its tail; the engine's own page holding one,
    // and a comment in a script that wraps between its characters, prints
    // whole at its own scale.
    if (name === 'chromium') {
      await control.setContent('<main><p>Prose.</p><pre style="white-space: pre-wrap"><code>' +
        '<span style="white-space: nowrap">' + 'x'.repeat(160) + '</span></code></pre></main>');
      if ((await printCode(control, name, 'print-code-held')).ok) throw new Error('print-code control: a held atom');
      await control.emulateMedia({ media: 'screen' });
    }
    if (name === 'chromium' && process.env.LT_CODE_PRINT) {
      await control.goto('file://' + process.env.LT_CODE_PRINT, { waitUntil: 'load' });
      await control.evaluate(() => document.fonts.ready);
      const engine = await printCode(control, name, 'print-code-engine');
      if (!engine.ok || engine.n !== 1) throw new Error("print-code control: the engine's page " + engine.why);
      await control.emulateMedia({ media: 'screen' });
    }
    // A held atom in a box narrower than it, beside another box, runs over
    // its neighbour on paper; the engine's page of such boxes, and of a
    // breaking listing's Thai, holds its code in its boxes on paper and on
    // every screen, the Thai parting only between its words.
    if (name === 'chromium') {
      await control.setContent('<main style="container-type: inline-size"><div style="display: grid; ' +
        'grid-template-columns: 20% 80%"><div style="container-type: inline-size"><pre style="white-space: ' +
        'pre-wrap"><code><span style="white-space: nowrap">' + 'x'.repeat(30) + '</span></code></pre></div>' +
        '<p>Prose beside the box.</p></div></main>');
      if ((await printCode(control, name, 'print-code-box')).ok) throw new Error('print-code control: a box run past');
      await control.emulateMedia({ media: 'screen' });
      const thai = 'ภาษาไทยไม่มีช่องว่างระหว่างคำจึงต้องตัดบรรทัดระหว่างคำแทนการเว้นวรรค';
      await control.setViewportSize({ width: 480, height: 300 });
      await control.setContent('<pre style="width: 160px; white-space: pre-wrap; overflow-wrap: break-word; ' +
        'font: 16px monospace"><code>' + [...thai].join('<wbr>') + '</code></pre>');
      if ((await control.evaluate(codeWrapJudge, codeTables)).ok)
        throw new Error('code-wrap control: Thai parted between its letters');
    }
    if (name === 'chromium' && process.env.LT_CODE_NARROW) {
      await control.goto('file://' + process.env.LT_CODE_NARROW, { waitUntil: 'load' });
      await control.evaluate(() => document.fonts.ready);
      const wrapped = await codeWrap(control);
      if (!wrapped.ok || wrapped.n !== 1) throw new Error("code-wrap control: the engine's narrow page " + wrapped.why);
      await control.setViewportSize({ width: 480, height: 720 });
      await control.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
      const thaiAt480 = await control.evaluate(codeWrapJudge, codeTables);
      if (!thaiAt480.ok || thaiAt480.wraps === 0)
        throw new Error("code-wrap control: the engine's Thai listing at 480 px " + thaiAt480.why);
      const boxed = await printCode(control, name, 'print-code-narrow');
      if (!boxed.ok || boxed.n !== 1) throw new Error("print-code control: the engine's narrow page " + boxed.why);
      await control.emulateMedia({ media: 'screen' });
    }
    // The engine's deck: its pager yields a key a focused code block still scrolls by and releases
    // the focus it pages past, its wide display scrolls in its own box at a phone's shape, and read
    // without script its page-less section's label and heading land on their stage.
    if (name === 'chromium' && process.env.LT_DECK_KEYS) {
      const url = 'file://' + process.env.LT_DECK_KEYS;
      await control.setViewportSize({ width: 1280, height: 720 });
      await control.goto(url, { waitUntil: 'load' });
      await control.evaluate(() => document.fonts.ready);
      const keyed = await deckKeys(control);
      if (!keyed.ok) throw new Error("deck-keys control: the engine's deck " + keyed.why);
      await control.setViewportSize({ width: 390, height: 844 });
      await settled(control);
      const wide = await control.evaluate(wideDisplays);
      if (!wide.ok) throw new Error("display-fit control: the engine's deck at a phone's shape " + wide.why);
      await control.setViewportSize({ width: 1280, height: 720 });
      const plainCtx = budgeted(await browser.newContext({ viewport: { width: 1280, height: 720 },
        javaScriptEnabled: false }));
      try {
        const landed = await stageLanding(await plainCtx.newPage(), url, 'sec:beta', 'wide');
        if (!landed.ok) throw new Error("stage-landing control: the engine's deck " + landed.why);
      } finally { await plainCtx.close(); }
    }
    // A deck declaring a safe area narrower than its mark keeps the mark in the margin it has.
    if (name === 'chromium' && process.env.LT_DECK_THIN) {
      const url = 'file://' + process.env.LT_DECK_THIN;
      await control.goto(url, { waitUntil: 'load' });
      const thin = await stageFocus(control, browser, (p) => p.goto(url, { waitUntil: 'load' }));
      if (!thin.ok) throw new Error("stage-focus control: the engine's thin safe area " + thin.why);
    }
  } finally { await controlCtx.close(); }
  for (const fx of fixtures) {
    const url = 'file://' + path.join(dir, fx + '.html');
    const ctx = budgeted(await browser.newContext({ viewport: { width: 1280, height: 720 }, deviceScaleFactor: 1 }));
    const page = await ctx.newPage();
    const errors = [];
    page.on('pageerror', e => errors.push('pageerror ' + e.message));
    page.on('console', m => { if (m.type() === 'error') errors.push(m.text() + ' ' + ((m.location() || {}).url || '')); });
    page.on('requestfailed', r => errors.push('requestfailed ' + r.url()));
    try {
      await page.goto(url, { waitUntil: 'load' });
      await page.evaluate(() => document.fonts.ready);
      await page.evaluate(() => new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))));
      const ready = await page.evaluate(() => document.readyState);
      out(fx, name, 'load', ready === 'complete' && errors.length === 0 ? 'pass'
        : 'fail:' + clean(ready !== 'complete' ? 'readyState ' + ready : errors[0]));
      for (const [feature, fn] of Object.entries(checks)) {
        out(fx, name, feature, cell(await page.evaluate(fn)));
      }
      out(fx, name, 'math-line', cell(await mathLine(page)));
      out(fx, name, 'stage-fit', cell(await stageFit(page, fx)));
      for (const [shape, frame, what] of await stageShapes(page).catch(e =>
          [['-', '-', 'unmeasured: ' + clean(String(e.message).split('\n')[0])]]))
        out('shape', fx, name, shape, frame, clean(what));
      out(fx, name, 'stage-focus', cell(await stageFocus(page, browser,
        (p) => p.goto(url, { waitUntil: 'load' }))));
      const links = await deckLinks(page, url);
      out(fx, name, 'deck-links', cell(links));
      if (links.after) throw links.after;
      out(fx, name, 'code-wrap', cell(await codeWrap(page)));
      out(fx, name, 'web-layout', cell(await webLayout(page)));
      const light = await page.evaluate(readColors);
      await page.evaluate((follows) => { document.documentElement.dataset.ltxFollows = follows; },
        light.bg === lightSurface && light.fg === lightInk ? 'tokens' : 'declared');
      await page.emulateMedia({ colorScheme: 'dark' });
      const dark = await page.evaluate(readColors);
      out(fx, name, 'color-scheme', cell(judgeSchemes(light, dark)));
      await page.emulateMedia({ colorScheme: 'light', reducedMotion: 'reduce' });
      out(fx, name, 'reduced-motion', cell(await page.evaluate(mediaChecks['reduced-motion'])));
      await page.emulateMedia({ reducedMotion: 'no-preference', media: 'print' });
      out(fx, name, 'affine-print', cell(await page.evaluate(affineGeometry)));
      out(fx, name, 'print', cell(await page.evaluate(mediaChecks.print, light.deck)));
      out(fx, name, 'print-disclosure', cell(await page.evaluate(mediaChecks['print-disclosure'])));
      const printed = light.deck ? await printDeck(page, name, fx)
        : { spill: { n: 0 }, sheets: { n: 0 } };
      out(fx, name, 'print-spill', cell(printed.spill));
      out(fx, name, 'print-sheets', cell(printed.sheets));
      out(fx, name, 'print-code', cell(light.deck ? { n: 0 } : await printCode(page, name, fx)));
    } catch (e) {
      out(fx, name, 'error', lost(e));
    }
    await ctx.close();
    const ctx2 = budgeted(await browser.newContext({ viewport: { width: 1280, height: 720 }, javaScriptEnabled: false }));
    const p2 = await ctx2.newPage();
    try {
      await p2.goto(url, { waitUntil: 'load' });
      await p2.evaluate(noScriptScroll);
      await drawn(p2);
      out(fx, name, 'no-script', cell(await p2.evaluate(noScriptRead)));
    } catch (e) {
      out(fx, name, 'no-script', lost(e));
    }
    await ctx2.close();
  }
  await browser.close();
}

(async () => {
  for (const r of process.env.LT_READERS.split(' ')) await runReader(r);
  clearTimeout(watchdog);
})().catch(e => { out(unfinished(e) ? 'unfinished' : 'error', clean(String(e && e.message || e))); process.exit(4); });
"#

/-- The numbers of the frames a deck's PDF build continues on a further page: the subjects
of its W0384 records. -/
def spilledFrames (porcelain : String) : Array String :=
  ((porcelain.splitOn "\n").filter (hasSub · "\"code\":\"W0384\"")).toArray.filterMap fun l =>
    match (l.splitOn "\"subject\":\"").drop 1 with
    | rest :: _ => some ((rest.splitOn "\"").headD "")
    | [] => none
where hasSub (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- A deck's frames that declare `[allowframebreaks]`, by the number their stages carry,
read through the driver's front door; `none` for a source that is not a deck. -/
def breakableFrames (path : System.FilePath) : IO (Option (Array String)) := do
  let file := path.toString
  let bytes ← match ← LeanTex.Cli.Input.readSource file with
    | .ok bytes => pure bytes
    | .error d => throw (IO.userError d.message)
  let src ← LeanTex.Cli.Input.readDocument file bytes
  let (doc, _) := Elab.runExecuted file src.executed src.diags
  unless doc.docClass.record.model == .frame do return none
  let nums := doc.frameNumbers
  let mut out : Array String := #[]
  for h : i in [0:doc.body.size] do
    if let .frame _ _ _ true _ := doc.body[i] then
      if let some (some n) := nums[i]? then out := out.push (toString n)
  return some out

/-- Copy a directory tree: every file `walkDir` lists, at the same path
under `dst`. -/
def copyTree (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  let root := src.toString ++ "/"
  for f in ← System.FilePath.walkDir src do
    if ← f.isDir then continue
    let rel := (f.toString.drop root.length).toString
    let d := dst / rel
    if let some parent := d.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile d (← IO.FS.readBinFile f)

/-- Decode an SVG data URL independently of the engine's encoder; malformed base64 is a
failed capture. -/
def svgPayload (root : System.FilePath) (href : String) : IO (Except String ByteArray) := do
  let dataPrefix := "data:image/svg+xml;base64,"
  if !href.startsWith dataPrefix then return .error "non-svg-resource"
  let file := root / "capture-base64"
  IO.FS.writeFile file ((href.drop dataPrefix.length).toString)
  let child ← IO.Process.spawn
    { cmd := "base64", args := #["-d", file.toString]
      stdin := .null, stdout := .piped, stderr := .null }
  let data ← child.stdout.readBinToEnd
  if (← child.wait) != 0 then return .error "invalid-base64"
  return .ok data

/-- The SVG data URLs of the built pages, read with libxml's HTML parser, by image or
source ordinal, with converter failures kept as explicit records. -/
def capturedBrowserFaces (root : System.FilePath) (fixtures : Array String)
    (failures : Array Scoreboard.BrowserFace) : IO (Array Scoreboard.BrowserFace) := do
  let mut out := failures
  for fixture in fixtures do
    for (tag, attr, role) in [("img", "src", "i"), ("source", "srcset", "p")] do
      let parsed ← IO.Process.output
        { cmd := "xmllint"
          args := #["--nonet", "--html", "--xpath", "//" ++ tag ++ "/@" ++ attr,
            (root / (fixture ++ ".html")).toString] }
      if parsed.exitCode != 0 && !(parsed.exitCode == 11 &&
          parsed.stdout.isEmpty && (parsed.stderr.splitOn "XPath set is empty").length > 1) then
        out := out.push (Scoreboard.BrowserFace.failed fixture "html-parse")
        continue
      for (tail, k) in ((parsed.stdout.splitOn (" " ++ attr ++ "=\"")).drop 1).toArray.zipIdx do
        let href := (tail.splitOn "\"").head!
        if !href.startsWith "data:image/svg+xml;base64," then continue
        let name := Scoreboard.browserFaceHref fixture role k href
        match ← svgPayload root href with
        | .ok bytes => out := out.push (Scoreboard.BrowserFace.captured fixture name bytes)
        | .error why => out := out.push { fixture, href := name, result := .failed why }
  return out

structure Cell where
  fixture : String
  reader : String
  feature : String
  value : String

structure Probe where
  cells : Array Cell
  /-- reader → version, when the launch succeeded. -/
  versions : Array (String × String)
  /-- reader → reason, when it did not. -/
  unavailable : Array (String × String)
  /-- The loss the probe named when it stopped before its last row. -/
  unfinished : Option String
  /-- (fixture, reader, shape, frame, what) for each deck's reported window shapes. -/
  shapes : Array (String × String × String × String × String)

def parseProbe (out : String) : Probe := Id.run do
  let mut p : Probe :=
    { cells := #[], versions := #[], unavailable := #[], unfinished := none, shapes := #[] }
  for l in out.splitOn "\n" do
    match l.splitOn "\t" with
    | ["reader", r, "version", v] => p := { p with versions := p.versions.push (r, v) }
    | ["reader", r, "unavailable", why] => p := { p with unavailable := p.unavailable.push (r, why) }
    | ["budget", ms] => p := { p with unfinished := some s!"the probe's {ms} ms budget ran out" }
    | ["unfinished", why] => p := { p with unfinished := some why }
    | ["shape", fx, r, shape, frame, what] =>
      p := { p with shapes := p.shapes.push (fx, r, shape, frame, what) }
    | [fx, r, f, v] => p := { p with cells := p.cells.push { fixture := fx, reader := r, feature := f, value := v } }
    | _ => pure ()
  return p

def reasonOf (v : String) : String :=
  (v.drop (if inconclusive v then "inconclusive:" else "fail:").length).toString

/-- What stands for a cell the probe never wrote: its fixture's error row, else the loss the probe
named, else a failure. -/
def missingValue (p : Probe) (fixture reader : String) : String :=
  match p.cells.find? fun c => c.fixture == fixture && c.reader == reader && c.feature == "error" with
  | some c => (if inconclusive c.value then "inconclusive:" else "fail:") ++ "not measured: " ++ reasonOf c.value
  | none => match p.unfinished with
    | some why => s!"inconclusive:not measured: {why}"
    | none => "fail:not measured: no row from the probe"

/-- The cell for one (feature, reader) over every fixture: the first failing fixture, else the
first inconclusive one, with each such fixture's reason. -/
def featureCell (p : Probe) (fixtures : Array String) (feature reader : String) :
    String × Array String := Id.run do
  if (p.versions.find? (·.1 == reader)).isNone then return ("untested", #[])
  let mut acc : Array (String × String × Bool) := #[]
  let mut exercised := 0
  for fx in fixtures do
    let value := match p.cells.find? fun c => c.fixture == fx && c.reader == reader && c.feature == feature with
      | some c => c.value
      | none => missingValue p fx reader
    if value == "na" then continue
    exercised := exercised + 1
    if value != "pass" then acc := acc.push (fx, reasonOf value, inconclusive value)
  if exercised == 0 then return ("untested", #[])
  let failing := (acc.filter (!·.2.2)).size
  let more (n : Nat) : String := if n > 1 then s!"+{n - 1}" else ""
  let cell := match acc.find? (!·.2.2), acc.find? (·.2.2) with
    | some (fx, _), _ => s!"fail:{fx}{more failing}"
    | none, some (fx, _) => s!"inconclusive:{fx}{more (acc.size - failing)}"
    | none, none => "pass"
  return (cell, acc.map fun (fx, why, _) => s!"{fx}: {why}")

/-- The cell for one (fixture, reader): its first failing feature, else its first inconclusive
one, and the features the fixture exercises. -/
def fixtureCell (p : Probe) (fixture reader : String) : String × Array String := Id.run do
  if (p.versions.find? (·.1 == reader)).isNone then return ("untested", #[])
  let mut ex : Array String := #[]
  let mut firstFail : Option String := none
  let mut firstOpen : Option String := none
  for f in features do
    let cell := p.cells.find? fun c => c.fixture == fixture && c.reader == reader && c.feature == f
    let value := match cell with
      | some c => c.value
      | none => missingValue p fixture reader
    if cell.isSome && value != "na" then ex := ex.push f
    if inconclusive value then firstOpen := firstOpen <|> some f
    else if value != "pass" && value != "na" then firstFail := firstFail <|> some f
  return (match firstFail, firstOpen with
    | some f, _ => s!"fail:{f}"
    | none, some f => s!"inconclusive:{f}"
    | none, none => "pass", ex)

/-- One table line: cells padded to their column, never fewer than two
spaces apart, no trailing space. -/
def tableLine (key : String) (cells : Array String) (tail : String := "") : String :=
  let keyW := 18
  let colW := 14
  let pad := fun (s : String) (w : Nat) => padRight s (max w (s.length + 2))
  (cells.foldl (fun acc c => acc ++ pad c colW) (pad key keyW) ++ tail).trimAsciiEnd.toString

def renderMatrix (p : Probe) (fixtures unbuilt : Array String)
    (tools date srcKey browserSourceKey : String)
    (browserFaces : Array Scoreboard.BrowserFace) : String := Id.run do
  let mut out := "# generated by scripts/html-oracle.lean — do not hand-edit; regenerate: lake env lean --run scripts/html-oracle.lean\n"
  out := out ++ s!"target: {String.intercalate " " targetReaders}\n"
  out := out ++ s!"tools: {tools}\n"
  out := out ++ s!"date: {date}\n"
  -- The HTML key is hermetic; the browser-face keys bind the vector inputs and outputs.
  out := out ++ s!"src-key: {srcKey}\n"
  out := out ++ s!"browser-face-src-key: {browserSourceKey}\n"
  out := out ++ s!"browser-face-key: {Scoreboard.browserFaceKey browserFaces}\n"
  for face in browserFaces.qsort fun a b =>
      if a.fixture == b.fixture then a.href < b.href else a.fixture < b.fixture do
    out := out ++ face.render ++ "\n"
  out := out ++ s!"fixtures: {fixtures.size} built"
  out := out ++ (if unbuilt.isEmpty then "\n" else s!", unbuilt: {String.intercalate " " unbuilt.toList}\n")
  out := out ++ "\n[feature]\n"
  out := out ++ tableLine "# feature" readers.toArray ++ "\n"
  for f in features do
    let mut cells : Array String := #[]
    let mut notes : Array String := #[]
    for r in readers do
      let (c, why) := featureCell p fixtures f r
      cells := cells.push c
      notes := notes ++ why.map (s!"#   {r} {·}")
    out := out ++ tableLine f cells ++ "\n"
    for n in notes do out := out ++ n ++ "\n"
  out := out ++ "\n[fixture]\n"
  out := out ++ tableLine "# fixture" readers.toArray "exercised" ++ "\n"
  for fx in fixtures do
    let mut cells : Array String := #[]
    let mut ex : Array String := #[]
    for r in readers do
      let (c, e) := fixtureCell p fx r
      cells := cells.push c
      if ex.isEmpty then ex := e
    out := out ++ tableLine fx cells (if ex.isEmpty then "-" else String.intercalate "," ex.toList) ++ "\n"
  return out

/-- The engine's reading of a code character as code point ranges
(`Listing.wrapsBetweenChars`, `holdsToPrevious`, `holdsToNext`), so the code-wrap judge
and the page read one table. -/
def codeTables : String :=
  let ranges (p : Char → Bool) : String := Id.run do
    let mut out : Array String := #[]
    let mut start : Option Nat := none
    for n in [0:0x40001] do
      let inside := n < 0x40000 && (n < 0xD800 || 0xDFFF < n) && p (Char.ofNat n)
      match start, inside with
      | none, true => start := some n
      | some a, false =>
        out := out.push s!"[{a},{n - 1}]"
        start := none
      | _, _ => pure ()
    return "[" ++ ",".intercalate out.toList ++ "]"
  "{\"apart\":" ++ ranges Listing.wrapsBetweenChars ++ ",\"words\":" ++
    ranges Listing.wrapsAtWords ++ ",\"before\":" ++
    ranges Listing.holdsToPrevious ++ ",\"after\":" ++ ranges Listing.holdsToNext ++
    s!",\"short\":{HtmlDoc.codeShortColumns}}"

/-- The page the paper judge's engine control prints: prose, then a code line with a token
wider than any sheet and a comment in a script wrapping between characters. -/
def codePrintSource : String :=
  "# Printed code\n\nA paragraph of prose before the code.\n\n```python\n" ++
  "value = compute(" ++ "".pushn 'x' 140 ++ ")\n" ++
  "# この行は折り返しを確かめるための架空のコメントで、句読点の前では改行しません。" ++
  "二行目に続く文も「括弧」の中で切れません。\n```\n"

/-- The page the narrow-box controls build: a breaking listing in a box a fifth of the
line wide, the same box before a wider one, and a breaking Thai listing. -/
def codeNarrowSource : String :=
  "\\documentclass{article}\n\\usepackage{listings}\n\\begin{document}\n" ++
  "Prose before the boxes.\n\n" ++
  "\\noindent\\begin{minipage}{0.48\\textwidth}\nLeft box prose that fills the left half " ++
  "of the line with ordinary words for the reader.\n\\end{minipage}\\hfill" ++
  "\\begin{minipage}{0.2\\textwidth}\n\\begin{lstlisting}[breaklines=true]\n" ++
  "abcdefghijklmnopqrstuvwxyzA\nalpha_beta_gamma_delta(x) -> y\n\\end{lstlisting}\n" ++
  "\\end{minipage}\n\n" ++
  "\\noindent\\begin{minipage}{0.2\\textwidth}\n\\begin{lstlisting}[breaklines=true]\n" ++
  "abcdefghijklmnopqrstuvwxyzA\n\\end{lstlisting}\n\\end{minipage}\\hfill" ++
  "\\begin{minipage}{0.75\\textwidth}\nRight box prose that fills the right side of the " ++
  "line with ordinary words for the reader to read here.\n\\end{minipage}\n\n" ++
  "\\begin{lstlisting}[breaklines=true]\n" ++
  "th = \"ภาษาไทยไม่มีช่องว่างระหว่างคำจึงต้องตัดบรรทัดระหว่างคำแทนการเว้นวรรค" ++
  "และสระต้องอยู่กับพยัญชนะ\"\nyear = 2567 # ๒๕๖๗\n\\end{lstlisting}\n\\end{document}\n"

/-- A Playwright module standing in for the host's, `LT_REAL_PW`: each page's renderer held
`LT_THROTTLE` times slower from its first `ArrowRight` to its next navigation, every `ArrowRight`
swallowed under `LT_SWALLOW`, and no scroll after the first key under `LT_STUCK`. -/
def loadShimJs : String := r#"
const real = require(process.env.LT_REAL_PW);
const rate = +(process.env.LT_THROTTLE || 1);
const swallow = !!process.env.LT_SWALLOW;
const stuck = !!process.env.LT_STUCK;
const page = (p) => {
  let cdp = null, state = 'idle';
  const hold = async (r) => {
    cdp = cdp || await p.context().newCDPSession(p);
    await cdp.send('Emulation.setCPUThrottlingRate', { rate: r });
  };
  const press = p.keyboard.press.bind(p.keyboard);
  p.keyboard.press = async (key, options) => {
    if (key === 'ArrowRight' && state === 'idle') { state = 'held'; await hold(rate); }
    return press(key, options);
  };
  for (const m of ['goBack', 'goto', 'reload', 'emulateMedia']) {
    const f = p[m].bind(p);
    p[m] = async (...a) => {
      if (state === 'held') { state = 'done'; await hold(1); }
      return f(...a);
    };
  }
  return p;
};
const context = async (c) => {
  if (swallow) await c.addInitScript(() => addEventListener('keydown', (e) => {
    if (e.key === 'ArrowRight') { e.preventDefault(); e.stopImmediatePropagation(); }
  }, true));
  if (stuck) await c.addInitScript(() => {
    let keyed = false;
    addEventListener('keydown', () => { keyed = true; }, true);
    const scroll = Element.prototype.scrollIntoView;
    Element.prototype.scrollIntoView = function (...a) { if (!keyed) scroll.apply(this, a); };
  });
  const newPage = c.newPage.bind(c);
  c.newPage = async (...a) => page(await newPage(...a));
  return c;
};
const chromium = Object.create(real.chromium);
chromium.launch = async (options) => {
  const b = await real.chromium.launch(options);
  const newContext = b.newContext.bind(b);
  b.newContext = async (...a) => context(await newContext(...a));
  const newPage = b.newPage.bind(b);
  b.newPage = async (...a) => { const p = page(await newPage(...a)); if (swallow) await context(p.context()); return p; };
  return b;
};
module.exports = Object.assign(Object.create(real), { chromium });
"#

/-- The engine control deck the pager, display and landing controls read: a code line wider than
any stage, a link, a page-less section's label, a display wider than a phone, and a last frame. -/
def deckKeysSource : String :=
  "\\documentclass{beamer}\n\\AtBeginSection{}\n\\begin{document}\n" ++
  "\\begin{frame}[fragile]{Keys}\n\\begin{verbatim}\n" ++
  "an_invented_identifier = compute(" ++ "".pushn 'x' 140 ++ ")\n\\end{verbatim}\n" ++
  "See \\href{https://example.org}{an invented link}.\n\\end{frame}\n" ++
  "\\section{Beta}\\label{sec:beta}\n" ++
  "\\begin{frame}{Wide}\n\\[ a_1 + a_2 + a_3 + a_4 + a_5 + a_6 + a_7 + a_8 + a_9 + a_{10} + a_{11} = b \\]\n" ++
  "\\end{frame}\n\\begin{frame}{Last}\nA closing invented line.\n\\end{frame}\n\\end{document}\n"

/-- The engine control deck with a safe area narrower than a focus mark and a pixel. -/
def deckThinSource : String :=
  "\\documentclass{beamer}\n\\tokens{ safearea = 2pt }\n\\begin{document}\n" ++
  "\\begin{frame}{Thin}\nAn invented line set to the stage's edge.\n\\end{frame}\n\\end{document}\n"

/-- An invented deck of three frames, the second in two steps. -/
def loadDeckSource : String :=
  "\\documentclass{beamer}\n\\begin{document}\n" ++
  "\\begin{frame}{First}\nA placeholder line.\n\\end{frame}\n" ++
  "\\begin{frame}{Second}\nOne line.\n\\pause\nAnother line.\n\\end{frame}\n" ++
  "\\begin{frame}{Third}\nA closing line.\n\\end{frame}\n\\end{document}\n"

/-- How much slower the load check holds the renderer: a keyboard step then takes several
seconds of wall clock to come to rest. -/
def loadThrottle : Nat := 200

/-- The deck-links cell of one probe run over the invented deck in `dir`, under the shim. -/
def loadRun (probe shim : System.FilePath) (module : String) (dir : System.FilePath)
    (throttle : Nat) (swallow stuck : Bool) : IO String := do
  let out ← IO.Process.output
    { cmd := "node", args := #[probe.toString, dir.toString, "deck"]
      env := #[("PW_MODULE", some shim.toString), ("LT_REAL_PW", some module),
        ("LT_THROTTLE", some (toString throttle)), ("LT_SWALLOW", if swallow then some "1" else none),
        ("LT_STUCK", if stuck then some "1" else none),
        ("LT_READERS", some "chromium"), ("LT_CODE_TABLES", some codeTables),
        ("HARD_TIMEOUT_MS", some "1200000")] }
  let p := parseProbe out.stdout
  match p.cells.find? fun c => c.fixture == "deck" && c.feature == "deck-links" with
  | some c => return c.value
  | none => return missingValue p "deck" "chromium"

/-- The deck-links verdict of a probe, this tree's or one read from a file, holds under load: an
invented deck passes with its renderer unloaded and held `loadThrottle` times slower through the
keyboard step, and fails, loaded or not, once its `ArrowRight` is swallowed. -/
def loadCheck (probePath : Option String) : IO UInt32 := do
  if !(← System.FilePath.pathExists leantexBin) then
    return (← die 2 s!"html-oracle: {leantexBin} not found; run lake build first")
  let some (module, _) ← findChromium "node"
    | return (← die 2 "html-oracle: the load check needs a Playwright module that launches Chromium")
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "deck.tex") loadDeckSource
    let built ← IO.Process.output
      { cmd := leantexBin
        args := #["-q", "build", (dir / "deck.tex").toString, "-o", (dir / "deck.html").toString] }
    if built.exitCode != 0 then
      return (← die 2 s!"html-oracle: the load check's deck did not build:\n{built.stdout}{built.stderr}")
    let probe := dir / "probe.cjs"
    IO.FS.writeFile probe (← match probePath with
      | some path => IO.FS.readFile path
      | none => pure probeJs)
    let shim := dir / "shim.cjs"
    IO.FS.writeFile shim loadShimJs
    let mut bad := 0
    for (name, rate, swallow, stuck, want) in [("unloaded", 1, false, false, "pass"),
        (s!"renderer {loadThrottle}× slower through the keyboard step", loadThrottle, false, false,
          "pass"),
        ("ArrowRight swallowed", 1, true, false, "fail:keyboard next"),
        (s!"ArrowRight swallowed, renderer {loadThrottle}× slower", loadThrottle, true, false,
          "fail:keyboard next"),
        ("no scroll after the first key", 1, false, true, "fail:keyboard next")] do
      let got ← loadRun probe shim module dir rate swallow stuck
      let ok := got.startsWith want
      IO.println s!"html-oracle: load check, {name}: deck-links {got}{if ok then "" else s!" (expected {want})"}"
      unless ok do bad := bad + 1
    if bad == 0 then IO.println "html-oracle: load check ok"
    return if bad == 0 then 0 else 1

/-- The window-shape report: per deck, reader and shape, each frame its stage clips or re-wraps,
or `fits`; the gate never reads it, since the window's shape is the reader's. -/
def renderShapes (p : Probe) (date srcKey : String) : String := Id.run do
  let mut out := "# generated by scripts/html-oracle.lean — a report, never a gate: the window's \
shape is the reader's\n"
  out := out ++ "# per deck and window shape, each stage that clips an element or sets a text \
block on more lines than at the deck's own aspect, in the snap state a reader lands on\n"
  out := out ++ s!"date: {date}\nsrc-key: {srcKey}\n"
  for (r, v) in p.versions do out := out ++ s!"reader: {r} {v}\n"
  let fixtures := p.shapes.foldl (fun acc (fx, _) => if acc.contains fx then acc else acc.push fx) #[]
  for fx in fixtures do
    out := out ++ s!"\n[{fx}]\n"
    for (f, r, shape, frame, what) in p.shapes do
      if f == fx then out := out ++ s!"{r}  {shape}  {frame}  {what}\n"
  return out

def regenerate : IO UInt32 := do
  if !(← System.FilePath.pathExists leantexBin) then
    return (← die 2 s!"html-oracle: {leantexBin} not found; run lake build first")
  -- Both freshness keys come from the tier's functions, as `htmlreader --check` reads them.
  let keys ← match ← Scoreboard.hermeticHtmlKeys with
    | .ok keys => pure keys
    | .error e =>
      return (← die 2 s!"html-oracle: cannot compute the corpus's freshness keys ({e}), \
so the matrix would describe pages nothing ties to this tree; nothing written")
  let date := (← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d"] }).stdout.trimAscii.toString
  let haveNode ← hasCmd "node"
  let nodeVersion ← if haveNode
    then pure (← IO.Process.output { cmd := "node", args := #["--version"] }).stdout.trimAscii.toString
    else pure "absent"
  let chromium ← if haveNode then findChromium "node" else pure none
  let work ← IO.FS.createTempDir
  try
    copyTree "testdata/corpus" (work / "corpus")
    let mut fixtures : Array String := #[]
    let mut unbuilt : Array String := #[]
    let mut faceFailures : Array Scoreboard.BrowserFace := #[]
    for (name, path) in ← Scoreboard.Hermetic.corpusDocs (work / "corpus") do
      let r ← IO.Process.output
        { cmd := leantexBin
          args := #["-q", "--porcelain", "build", path.toString,
            "-o", (work / "corpus" / (name ++ ".html")).toString] }
      let log := r.stdout ++ r.stderr
      faceFailures := faceFailures ++ Scoreboard.browserFaceFailures name log
      if r.exitCode == 0 then fixtures := fixtures.push name else unbuilt := unbuilt.push name
      -- A deck's stage premise, read off TeX source: what its PDF build does not vouch for.
      if path.extension == some "tex" then
        if let some breakable ← breakableFrames path then
          let pdf ← IO.Process.output
            { cmd := leantexBin
              args := #["-q", "--porcelain", "build", path.toString,
                "-o", (work / "corpus" / (name ++ ".pdf")).toString] }
          IO.FS.writeFile (work / "corpus" / (name ++ ".unfit"))
            (String.intercalate " " (spilledFrames pdf.stdout ++ breakable).toList)
    let browserFaces ← capturedBrowserFaces (work / "corpus") fixtures faceFailures
    -- The paper judge's engine control: a page no fixture is.
    let control := work / "control"
    IO.FS.createDirAll control
    IO.FS.writeFile (control / "code-print.md") codePrintSource
    let built ← IO.Process.output
      { cmd := leantexBin
        args := #["-q", "--porcelain", "build", (control / "code-print.md").toString,
          "-o", (control / "code-print.html").toString] }
    if built.exitCode != 0 then
      return (← die 2 s!"html-oracle: the paper judge's control page did not build:\n{built.stdout}{built.stderr}")
    IO.FS.writeFile (control / "code-narrow.tex") codeNarrowSource
    let narrow ← IO.Process.output
      { cmd := leantexBin
        args := #["-q", "--porcelain", "build", (control / "code-narrow.tex").toString,
          "-o", (control / "code-narrow.html").toString] }
    if narrow.exitCode != 0 then
      return (← die 2 s!"html-oracle: the narrow-box control page did not build:\n{narrow.stdout}{narrow.stderr}")
    IO.FS.writeFile (control / "deck-keys.tex") deckKeysSource
    let keyDeck ← IO.Process.output
      { cmd := leantexBin
        args := #["-q", "--porcelain", "build", (control / "deck-keys.tex").toString,
          "-o", (control / "deck-keys.html").toString] }
    if keyDeck.exitCode != 0 then
      return (← die 2 s!"html-oracle: the deck control page did not build:\n{keyDeck.stdout}{keyDeck.stderr}")
    IO.FS.writeFile (control / "deck-thin.tex") deckThinSource
    let thin ← IO.Process.output
      { cmd := leantexBin
        args := #["-q", "--porcelain", "build", (control / "deck-thin.tex").toString,
          "-o", (control / "deck-thin.html").toString] }
    if thin.exitCode != 0 then
      return (← die 2 s!"html-oracle: the thin deck control page did not build:\n{thin.stdout}{thin.stderr}")
    let mut probe : Probe :=
      { cells := #[], versions := #[], unavailable := #[], unfinished := none, shapes := #[] }
    let mut tools := s!"node {nodeVersion}"
    match chromium with
    | none =>
      tools := tools ++ "  chromium untested (no Playwright module launches a cached Chromium; LEANTEX_PLAYWRIGHT names one)"
      probe := { probe with unavailable := probe.unavailable.push ("chromium", "no launchable module") }
      probe := { probe with unavailable := probe.unavailable.push ("firefox", "not attempted") }
    | some (m, _) =>
      IO.FS.writeFile (work / "probe.cjs") probeJs
      let col (s : Ir.Scheme) (r : Ir.Role) : String :=
        HtmlDoc.cssColor ((Ir.Design.at ({} : Ir.Palette) s r).getD Ir.Color.black)
      let tokens := s!"{col .light .ink} {col .light .page} {col .dark .ink} {col .dark .page}"
      let out ← IO.Process.output
        { cmd := "node"
          args := #[(work / "probe.cjs").toString, (work / "corpus").toString] ++ fixtures
          env := #[("PW_MODULE", some m), ("LT_TOKENS", some tokens),
                   ("LT_READERS", some (String.intercalate " " readers)),
                   ("LT_CODE_TABLES", some codeTables),
                   ("LT_CODE_PRINT", some (control / "code-print.html").toString),
                   ("LT_CODE_NARROW", some (control / "code-narrow.html").toString),
                   ("LT_DECK_KEYS", some (control / "deck-keys.html").toString),
                   ("LT_DECK_THIN", some (control / "deck-thin.html").toString),
                   ("LT_MYST", some (← IO.FS.readFile mystPath))] }
      if out.exitCode != 0 then
        IO.eprintln s!"html-oracle: the probe exited {out.exitCode}:\n{out.stderr}"
      probe := parseProbe out.stdout
      if out.exitCode != 0 && probe.unfinished.isNone &&
          !(out.stdout.splitOn "\n").any (·.startsWith "error\t") then
        probe := { probe with
          unfinished := some s!"the probe stopped with exit {out.exitCode}, naming no loss" }
      let pwv ← moduleVersion m
      for r in readers do
        match probe.versions.find? (·.1 == r) with
        | some (_, v) => tools := tools ++ s!"  {r} {v} (playwright {pwv})"
        | none =>
          let why := ((probe.unavailable.find? (·.1 == r)).map (·.2)).getD "no row from the probe"
          tools := tools ++ s!"  {r} untested ({why})"
    tools := tools ++ s!"  {← toolVersion "xmllint" #["--version"]}"
    tools := tools ++ s!"  {← toolVersion "xsltproc" #["--version"]}"
    tools := tools ++ s!"  {← toolVersion "rsvg-convert" #["--version"]}"
    tools := tools ++ s!"  {← toolVersion "pdftocairo" #["-v"]}"
    tools := tools ++ s!"  {← pdftotextVersion}"
    let text := renderMatrix probe fixtures unbuilt tools date keys.html keys.browserFaceSource
      browserFaces
    let lost : Array String := match parseMatrix text with
      | .ok m => (offences m).filter fun (b : String) => inconclusive ((b.splitOn " = ").getLastD "")
      | .error _ => #[]
    unless lost.isEmpty do
      IO.println s!"html-oracle: {lost.size} target cells inconclusive, so {matrixPath} stays as \
committed:"
      for b in lost do IO.println s!"  {b}"
      return 1
    IO.FS.createDirAll "testdata/oracles"
    IO.FS.writeFile matrixPath text
    IO.FS.writeFile shapesPath (renderShapes probe date keys.html)
    IO.println s!"html-oracle: wrote {matrixPath} and {shapesPath} — {fixtures.size} fixtures, {tools}"
  finally
    IO.FS.removeDirAll work
  checkFile matrixPath

/-- The checker against hand-written matrices: a green file passes, an `untested` or
`fail:` target cell fails, a non-target cell gates nothing, a missing target column is an
offence. -/
def selftest : IO UInt32 := do
  let green := "target: chromium\n[feature]\n# feature chromium firefox\nload pass untested\n" ++
    "[fixture]\n# fixture chromium firefox exercised\ndeck pass untested load\n"
  let cases : List (String × String × Nat) :=
    [("green", green, 0),
     ("target untested", green.replace "load pass untested" "load untested untested", 1),
     ("target fail", green.replace "deck pass untested" "deck fail:load untested", 1),
     ("target inconclusive", green.replace "deck pass untested" "deck inconclusive:load untested", 1),
     ("non-target moves", green.replace "load pass untested" "load pass fail:x", 0),
     ("target column missing", green.replace "# feature chromium firefox\nload pass untested"
        "# feature firefox\nload untested", 1)]
  let mut bad := 0
  for (name, text, want) in cases do
    let got := match parseMatrix text with
      | .ok m => (offences m).size
      | .error _ => 99
    if got != want then
      IO.eprintln s!"FAIL {name}: {got} offences, expected {want}"
      bad := bad + 1
  -- A failing fixture outranks an inconclusive one, and a fixture the probe never reached is
  -- inconclusive only where the probe named its loss.
  let probeOf (xs : List (String × String)) (unfinished : Option String) : Probe :=
    { cells := xs.toArray.map fun (fixture, value) =>
        { fixture, reader := "chromium", feature := "deck-links", value }
      versions := #[("chromium", "1")], unavailable := #[], unfinished, shapes := #[] }
  let cellOf (p : Probe) (xs : Array String) := featureCell p xs "deck-links" "chromium"
  let budget := (parseProbe "budget\t900000\n").unfinished
  let errRow : Cell :=
    { fixture := "b", reader := "chromium", feature := "error", value := "inconclusive:page.goto: Timeout" }
  for (name, ok) in [
      ("a failure outranks an inconclusive fixture",
        cellOf (probeOf [("a", "pass"), ("b", "inconclusive:x"), ("c", "fail:y")] none) #["a", "b", "c"]
          == ("fail:c", #["b: x", "c: y"])),
      ("an inconclusive fixture outranks a pass",
        cellOf (probeOf [("a", "pass"), ("b", "inconclusive:x")] none) #["a", "b"]
          == ("inconclusive:b", #["b: x"])),
      ("the probe's budget line names its loss", budget == some "the probe's 900000 ms budget ran out"),
      ("a fixture past a named loss is inconclusive",
        (cellOf (probeOf [("a", "pass")] budget) #["a", "b"]).1 == "inconclusive:b"),
      ("a fixture missing with no named loss fails",
        (cellOf (probeOf [("a", "pass")] none) #["a", "b"]).1 == "fail:b"),
      ("a fixture's inconclusive error row stands for its missing cells",
        (fixtureCell (probeOf [("b", "pass")] none) "b" "chromium").1 == "fail:load" &&
        (fixtureCell { probeOf [] none with cells := #[errRow] } "b" "chromium").1
          == "inconclusive:load")] do
    unless ok do
      IO.eprintln s!"FAIL cells: {name}"
      bad := bad + 1
  for (name, text) in [("no target", "[feature]\n# feature chromium\nload pass\n"),
                       ("row before header", "target: chromium\n[feature]\nload pass\n"),
                       ("short row", "target: chromium\n[feature]\n# feature chromium firefox\nload pass\n")] do
    if (parseMatrix text).isOk then
      IO.eprintln s!"FAIL {name}: parsed"
      bad := bad + 1
  let captureFails ← IO.FS.withTempDir fun root => do
    let fixture := "embedded"
    let bytes := "<svg/>".toUTF8
    let href := "data:image/svg+xml;base64,PHN2Zy8+"
    let pin := Scoreboard.sha256Hex href.toUTF8
    -- Repeated bytes are distinct image uses, and a print poster is distinct from its screen.
    IO.FS.writeFile (root / (fixture ++ ".html"))
      ("<!doctype html><html><body><picture><source srcset=\"" ++ href ++
        "\"><img src=\"" ++ href ++ "\"></picture><img src=\"" ++ href ++
        "\"></body></html>")
    let expected := #["i0", "i1", "p0"] |>.map fun role =>
      Scoreboard.BrowserFace.captured fixture (fixture ++ "/" ++ role ++ "-" ++ pin ++ ".svg") bytes
    let captured ← capturedBrowserFaces root #[fixture] #[]
    let mut failures := 0
    if captured != expected then
      IO.eprintln "FAIL browser capture: each embedded use is captured exactly, with no sidecars"
      failures := failures + 1
    IO.FS.writeFile (root / (fixture ++ ".html"))
      ("<!doctype html><html><body><img src=\"data:image/png;base64,iVBORw0KGgo=\">" ++
        "&lt;img src=\"" ++ href ++ "\"&gt;<script>'<img src=\"" ++ href ++
        "\">'</script><div hidden><img src=\"" ++ href ++ "\"></div></body></html>")
    let hidden ← capturedBrowserFaces root #[fixture] #[]
    if hidden != #[expected[1]!] then
      IO.eprintln "FAIL browser capture: parsed hidden images retain their ordinal; quoted markup is not a use"
      failures := failures + 1
    IO.FS.writeFile (root / (fixture ++ ".html"))
      "<!doctype html><html><body><img src=\"data:image/svg+xml;base64,!?\"></body></html>"
    let malformed ← capturedBrowserFaces root #[fixture] #[]
    let badName := Scoreboard.browserFaceHref fixture "i" 0 "data:image/svg+xml;base64,!?"
    if malformed != #[{ fixture, href := badName, result := .failed "invalid-base64" }] then
      IO.eprintln "FAIL browser capture: malformed embedded payload is an explicit failed capture"
      failures := failures + 1
    return failures
  bad := bad + captureFails
  -- The stage premise: only W0384 records name continuing frames; breaks read as the build does.
  let porcelain := "{\"code\":\"W0384\",\"subject\":\"7\",\"message\":\"a frame continues\"}\n" ++
    "{\"code\":\"W0384\",\"message\":\"no subject\"}\n" ++
    "{\"code\":\"W0005\",\"subject\":\"3\"}\nnot a record\n"
  if spilledFrames porcelain != #["7"] then
    IO.eprintln s!"FAIL stage premise: W0384 subjects alone name spilled frames ({spilledFrames porcelain})"
    bad := bad + 1
  let premiseFails ← IO.FS.withTempDir fun root => do
    IO.FS.writeFile (root / "part.tex")
      "\\begin{frame}[allowframebreaks]{Second}\nA placeholder line.\n\\end{frame}\n"
    IO.FS.writeFile (root / "deck.tex")
      ("\\documentclass{beamer}\n\\begin{document}\n" ++
        "\\begin{frame}{First}\nA placeholder line.\n\\end{frame}\n\\input{part}\n" ++
        "\\begin{frame}[allowframebreaks]{Third}\nA placeholder line.\n\\end{frame}\n" ++
        "\\end{document}\n")
    IO.FS.writeFile (root / "flow.tex")
      "\\documentclass{article}\n\\begin{document}\nA placeholder line.\n\\end{document}\n"
    let mut failures := 0
    let deck ← breakableFrames (root / "deck.tex")
    if deck != some #["2", "3"] then
      IO.eprintln s!"FAIL stage premise: an input file's breakable frame is read and numbered ({deck})"
      failures := failures + 1
    let flow ← breakableFrames (root / "flow.tex")
    if flow != none then
      IO.eprintln s!"FAIL stage premise: a flow document has no stages to exempt ({flow})"
      failures := failures + 1
    return failures
  bad := bad + premiseFails
  if bad == 0 then
    IO.println "html-oracle: selftest ok"
    return 0
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--selftest"] => selftest
  | ["--check"] => checkFile matrixPath
  | ["--check", path] => checkFile path
  | ["--load-check"] => loadCheck none
  | ["--load-check", path] => loadCheck (some path)
  | [] => regenerate
  | _ => die 3 "usage: html-oracle [--check [path] | --selftest | --load-check [probe.cjs]]"
