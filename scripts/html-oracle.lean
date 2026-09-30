/-
HTML artifact oracle: what a real browser makes of every corpus page. Run
from the repository root after `lake build`:

  lake env lean --run scripts/html-oracle.lean                   regenerate the matrix, then check it
  lake env lean --run scripts/html-oracle.lean --check [path]    check the checked-in matrix (or another file) only
  lake env lean --run scripts/html-oracle.lean --selftest        the checker against hand-written matrices

Builds every `tests/corpus/*.tex` to HTML in a scratch copy of the corpus
(so a page sits beside the files it names, as `leantex doc.tex` leaves it),
drives the host's cached Playwright Chromium over each page, and writes
`tests/oracles/html-reader-matrix.txt`: target readers, host-tool versions and
a date, one row per feature × reader and fixture × reader, plus a separate
browser-face source key and exact converted href/content captures. A converter
failure is a failed capture even when removing the `<img>` would otherwise
turn the browser's image check into `na`. This script is the matrix's only
writer; the file has exactly a golden's exposure.

Cells: `pass` — every fixture that exercises the feature holds it in that
reader; `fail:<fixture>` — one that does not, its reason in the `#` line
beneath; `untested` — the reader could not run, or no fixture exercises
the feature. The check demands `pass` in every `target:` column; a
non-target column (Firefox on this host: the cached build cannot start) is
recorded data and gates nothing.

The engine proves what it emits; a browser's behaviour is a measurement,
never a theorem. No dependency is added: the Playwright module and browser
are found where `npx playwright install` leaves them (`LEANTEX_PLAYWRIGHT`
names a module directory explicitly), or the reader is `untested`.
-/
import LeanTex
import scripts.Board

open LeanTex.Core

def matrixPath : String := "tests/oracles/html-reader-matrix.txt"
def leantexBin : String := ".lake/build/bin/leantex"

/-- The readers the matrix declares as targets — the strength of the claim,
declared by the file, not by what a host has installed. -/
def targetReaders : List String := ["chromium"]

/-- Every reader the probe knows how to drive, in column order. -/
def readers : List String := ["chromium", "firefox"]

/-- The feature rows, in the order the probe emits them. -/
def features : List String :=
  ["load", "images", "fonts", "mathml", "lang", "landmarks", "snaps", "box-side",
   "affine-screen", "affine-print", "color-scheme", "reduced-motion", "print", "print-spill",
   "print-sheets", "no-script"]

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

def padRight (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

def hasCmd (cmd : String) : IO Bool := do
  try
    return (← IO.Process.output { cmd, args := #["--version"] }).exitCode == 0
  catch _ => return false

/-- The reader the print judgements (`print-spill`, `print-sheets`) read
paper with, as the tools line records it: `pdftotext -v`'s first line, or
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

-- ## The checked-in file

/-- One section of the matrix: its name, its reader columns, and its rows
(key, then one cell per column; trailing columns are data). -/
structure Section where
  name : String
  columns : Array String
  rows : Array (String × Array String)

structure Matrix where
  target : Array String
  sections : Array Section

/-- Parse the matrix text. `#` lines are comments, except that the first
one after a `[section]` header names the columns. -/
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

/-- The gate: every cell under a `target:` reader is `pass`. Returns the
offending cells, `section/key/reader = cell`. A target reader missing from
a section's columns is itself an offence. -/
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
    let bad := offences m ++
      (Scoreboard.browserFaceFaults text keys.browserFaceSource keys.expectedFaces).map
      ("browser-face: " ++ ·)
    if bad.isEmpty then
      IO.println s!"html-oracle: every target cell and browser-face capture passes ({String.intercalate " " m.target.toList})"
      return 0
    IO.println s!"html-oracle: {bad.size} target or browser-face checks not passing in {path}:"
    for b in bad do IO.println s!"  {b}"
    return 1

-- ## The probe

/-- The browser-side probe, run by node with the Playwright module named in
`PW_MODULE`. It prints one tab-separated line per (fixture, reader, feature):
`pass`, `fail:<reason>`, or `na` when the fixture does not exercise the
feature; `reader <name> version|unavailable <text>` lines carry the tool
facts. Every check reads the live page — computed style, layout boxes,
`document.fonts`, the FontFaceSet, media emulation — never the source. -/
def probeJs : String := r#"
const path = require('path');
const { execFileSync } = require('child_process');
const pw = require(process.env.PW_MODULE);
const dir = process.argv[2];
const fixtures = process.argv.slice(3);
const out = (...cols) => console.log(cols.join('\t'));
const clean = (s) => String(s).replace(/\s+/g, ' ').trim();

const HARD_MS = +(process.env.HARD_TIMEOUT_MS || 900000);
const watchdog = setTimeout(() => { out('error', 'hard timeout'); process.exit(4); }, HARD_MS);

const hexToRgb = (h) => {
  const m = /^#([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})$/i.exec(h.trim());
  return m ? `rgb(${parseInt(m[1], 16)}, ${parseInt(m[2], 16)}, ${parseInt(m[3], 16)})` : h.trim();
};
// The engine's own token set: light ink, light surface, dark ink, dark surface.
const [lightInk, lightSurface, darkInk, darkSurface] = (process.env.LT_TOKENS || '').split(/\s+/).map(hexToRgb);

// Every check runs inside the page and returns {ok, n, why}; n = 0 means
// the fixture does not exercise the feature.
const checks = {
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
      const r = m.getBoundingClientRect();
      return !(m.namespaceURI === 'http://www.w3.org/1998/Math/MathML' && r.width > 0 && r.height > 0);
    });
    return { ok: bad.length === 0, n: ms.length,
      why: bad.length ? `${bad.length}/${ms.length} <math> with an empty box or outside the MathML namespace` : '' };
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
  // the browser computes, and the scroll space is one viewport per snap.
  snaps: async () => {
    const root = getComputedStyle(document.documentElement);
    if (!/mandatory/.test(root.scrollSnapType)) return { ok: true, n: 0, why: '' };
    await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
    const declared = document.querySelectorAll('[data-snap]').length;
    const computed = [...document.querySelectorAll('*')]
      .filter(e => /^start/.test(getComputedStyle(e).scrollSnapAlign)
        && getComputedStyle(e).display !== 'none').length;
    const se = document.scrollingElement;
    const pages = Math.round(se.scrollWidth / window.innerWidth);
    const ok = declared > 0 && computed === declared && pages === declared;
    return { ok, n: 1, why: `data-snap x${declared} computed-start x${computed} pages x${pages}` };
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
};

// A CSS-pixel half is the declared browser bound: deviceScaleFactor=1,
// Chromium's layout boxes are quantized below it, while a wrong ancestor in
// this fixture differs by tens of pixels. Every expected value is recomputed
// from the semantic owner's live content box, never from the emitted cqi text.
const affineGeometry = () => {
  const bound = 0.5;
  const top = document.querySelector('.u-affinetop');
  if (!top) return { ok: true, n: 0, why: '' };
  const pt = n => n * 4 / 3;
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
};

// Scripting off, synchronous (no timers run in a page with scripting
// disabled): the deck's marker is absent and a non-deck page carries no
// executable script. The scroll is applied here; the read follows a pause
// on the driver's side so the scroll-driven uncover has had its frame.
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

const cell = (r) => r.n === 0 ? 'na' : r.ok ? 'pass' : 'fail:' + clean(r.why);

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
//  - print-sheets: no sheet goes to paper blank — one with no letter or
//    digit is allowed only for a stage that lays out none. A stage's
//    padding alone once took a sheet of its own, and so did the tail of a
//    stage that opened below a heading instead of on a sheet of its own.
// Playwright prints to PDF in Chromium alone.
const census = (s) => {
  const m = new Map();
  for (const c of s.normalize('NFKC').toLowerCase())
    if (/[\p{L}\p{N}]/u.test(c)) m.set(c, (m.get(c) || 0) + 1);
  return m;
};
const inked = (s) => /[\p{L}\p{N}]/u.test(s);
const printDeck = async (page, name, fx) => {
  const none = { ok: true, n: 0, why: '' };
  if (name !== 'chromium') return { spill: none, sheets: none };
  const size = await page.evaluate(() => {
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
  const pt = /^([\d.]+)pt ([\d.]+)pt$/.exec(size.trim());
  if (!pt) {
    const bad = { ok: false, n: 1, why: `no @page size in points (${size})` };
    return { spill: bad, sheets: bad };
  }
  const sheetH = +pt[2] * 4 / 3;
  await page.setViewportSize({ width: Math.round(+pt[1] * 4 / 3), height: Math.round(sheetH) });
  const laid = await page.evaluate((h) => {
    const stages = [...document.querySelectorAll('section.slide, section.section-page')];
    return { spill: stages.filter(s =>
        Math.max(s.scrollHeight, s.getBoundingClientRect().height) > h + 1).length,
      bare: stages.filter(s => !/[\p{L}\p{N}]/u.test(s.innerText)).length,
      text: document.querySelector('main').innerText };
  }, sheetH);
  const pdf = path.join(dir, fx + '.printed.pdf');
  await page.pdf({ path: pdf, preferCSSPageSize: true });
  let paper;
  try { paper = execFileSync('pdftotext', ['-enc', 'UTF-8', pdf, '-'], { encoding: 'utf8' }); }
  catch (e) {
    const bad = { ok: false, n: 1, why: 'pdftotext: ' + clean(String(e.message).split('\n')[0]) };
    return { spill: bad, sheets: bad };
  }
  const sheets = paper.split('\f').slice(0, -1);
  const blank = sheets.filter(t => !inked(t)).length;
  const sheetsCell = { ok: blank <= laid.bare, n: 1,
    why: `${blank} of ${sheets.length} sheets blank, ${laid.bare} stage(s) with no text` };
  if (laid.spill === 0) return { spill: none, sheets: sheetsCell };
  const want = census(laid.text), got = census(paper);
  const lost = [...want].filter(([c, n]) => (got.get(c) || 0) < n);
  const short = lost.reduce((a, [c, n]) => a + n - (got.get(c) || 0), 0);
  return { sheets: sheetsCell, spill: { ok: lost.length === 0, n: 1,
    why: `${laid.spill} stage(s) taller than the sheet, ${short} laid-out characters missing on paper` } };
};

async function runReader(name) {
  let browser;
  try {
    browser = await pw[name].launch({ headless: true,
      args: name === 'chromium' ? ['--no-sandbox', '--disable-gpu'] : [] });
  } catch (e) {
    out('reader', name, 'unavailable', clean(String(e && e.message || e).split('\n')[0]));
    return;
  }
  out('reader', name, 'version', browser.version());
  for (const fx of fixtures) {
    const url = 'file://' + path.join(dir, fx + '.html');
    const ctx = await browser.newContext({ viewport: { width: 1280, height: 720 }, deviceScaleFactor: 1 });
    const page = await ctx.newPage();
    const errors = [];
    page.on('pageerror', e => errors.push('pageerror ' + e.message));
    page.on('console', m => { if (m.type() === 'error') errors.push(m.text() + ' ' + ((m.location() || {}).url || '')); });
    page.on('requestfailed', r => errors.push('requestfailed ' + r.url()));
    try {
      await page.goto(url, { waitUntil: 'load', timeout: 30000 });
      await page.evaluate(() => document.fonts.ready);
      await page.waitForTimeout(100);
      const ready = await page.evaluate(() => document.readyState);
      // A stylesheet or icon the document names by URL is the author's
      // file, not the engine's emission: its absence from the fixture is
      // not a load failure.
      const declared = await page.evaluate(() => [...document.querySelectorAll('link[href]')].map(l => l.href));
      const own = errors.filter(e => !declared.some(u => e.includes(u)));
      out(fx, name, 'load', ready === 'complete' && own.length === 0 ? 'pass'
        : 'fail:' + clean(ready !== 'complete' ? 'readyState ' + ready : own[0]));
      for (const [feature, fn] of Object.entries(checks)) {
        out(fx, name, feature, cell(await page.evaluate(fn)));
      }
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
      const printed = light.deck ? await printDeck(page, name, fx)
        : { spill: { n: 0 }, sheets: { n: 0 } };
      out(fx, name, 'print-spill', cell(printed.spill));
      out(fx, name, 'print-sheets', cell(printed.sheets));
    } catch (e) {
      out(fx, name, 'error', 'fail:' + clean(String(e.message).split('\n')[0]));
    }
    await ctx.close();
    const ctx2 = await browser.newContext({ viewport: { width: 1280, height: 720 }, javaScriptEnabled: false });
    const p2 = await ctx2.newPage();
    try {
      await p2.goto(url, { waitUntil: 'load', timeout: 30000 });
      await p2.evaluate(noScriptScroll);
      await p2.waitForTimeout(200);
      out(fx, name, 'no-script', cell(await p2.evaluate(noScriptRead)));
    } catch (e) {
      out(fx, name, 'no-script', 'fail:' + clean(String(e.message).split('\n')[0]));
    }
    await ctx2.close();
  }
  await browser.close();
}

(async () => {
  for (const r of process.env.LT_READERS.split(' ')) await runReader(r);
  clearTimeout(watchdog);
})().catch(e => { out('error', clean(String(e && e.message || e))); process.exit(4); });
"#

-- ## Tools

/-- The Playwright module directories to try: `LEANTEX_PLAYWRIGHT` first,
then every `~/.npm/_npx/*/node_modules/playwright` — where
`npx playwright install` leaves the module. Nothing is installed here. -/
def playwrightCandidates : IO (Array String) := do
  let mut out : Array String := #[]
  if let some p ← IO.getEnv "LEANTEX_PLAYWRIGHT" then out := out.push p
  if let some home ← IO.getEnv "HOME" then
    let npx : System.FilePath := home / ".npm" / "_npx"
    if ← npx.isDir then
      for e in (← npx.readDir).qsort (·.fileName < ·.fileName) do
        let m := e.path / "node_modules" / "playwright"
        if ← (m / "package.json").pathExists then out := out.push m.toString
  return out

/-- The module's declared version, from its package.json. -/
def moduleVersion (m : String) : IO String := do
  let pkg ← IO.FS.readFile (m ++ "/package.json")
  match (pkg.splitOn "\"version\": \"").drop 1 with
  | v :: _ => return ((v.splitOn "\"").headD "?")
  | [] => return "?"

/-- The first module whose Chromium launches on this host, with the version
it reports; the launch is the only test that counts — a module whose browser
revision is not in the cache throws here, and the next candidate is tried. -/
def findChromium (node : String) : IO (Option (String × String)) := do
  for m in ← playwrightCandidates do
    let launch := "require(process.env.PW_MODULE).chromium.launch({headless:true,args:['--no-sandbox','--disable-gpu']})" ++
      ".then(b=>{console.log(b.version());return b.close()})" ++
      ".catch(e=>{console.error(String(e.message).split('\\n')[0]);process.exit(1)})"
    let out ← IO.Process.output
      { cmd := node
        args := #["-e", launch]
        env := #[("PW_MODULE", some m)] }
    if out.exitCode == 0 then
      return some (m, out.stdout.trimAscii.toString)
  return none

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

/-- Exact generated SVG bytes under the hrefs present in the pages the browser
will open. Converter diagnostics enter as failed records, so a missing tool
cannot silently turn a previously exercised image into a passing `na` cell. -/
def capturedBrowserFaces (root : System.FilePath) (fixtures : Array String)
    (failures : Array Scoreboard.BrowserFace) : IO (Array Scoreboard.BrowserFace) := do
  let mut out := failures
  let rootPrefix := root.toString ++ "/"
  for fixture in fixtures do
    let html ← IO.FS.readFile (root / (fixture ++ ".html"))
    let assets := root / (fixture ++ ".assets")
    if !(← assets.isDir) then continue
    for file in (← System.FilePath.walkDir assets).qsort (·.toString < ·.toString) do
      if (← file.isDir) || file.extension != some "svg" then continue
      let href := (file.toString.drop rootPrefix.length).toString
      if (html.splitOn href).length > 1 then
        out := out.push (Scoreboard.BrowserFace.captured fixture href (← IO.FS.readBinFile file))
      else
        out := out.push { fixture, href, result := .failed "unlinked-svg" }
  return out

-- ## Aggregation

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

def parseProbe (out : String) : Probe := Id.run do
  let mut p : Probe := { cells := #[], versions := #[], unavailable := #[] }
  for l in out.splitOn "\n" do
    match l.splitOn "\t" with
    | ["reader", r, "version", v] => p := { p with versions := p.versions.push (r, v) }
    | ["reader", r, "unavailable", why] => p := { p with unavailable := p.unavailable.push (r, why) }
    | [fx, r, f, v] => p := { p with cells := p.cells.push { fixture := fx, reader := r, feature := f, value := v } }
    | _ => pure ()
  return p

def reasonOf (v : String) : String := (v.drop "fail:".length).toString

/-- The cell for one (feature, reader) over every fixture, plus the reasons
of the fixtures that failed. A fixture the probe abandoned mid-page (an
`error` row) fails every feature it did not report. -/
def featureCell (p : Probe) (fixtures : Array String) (feature reader : String) :
    String × Array String := Id.run do
  if (p.versions.find? (·.1 == reader)).isNone then return ("untested", #[])
  let mut fails : Array (String × String) := #[]
  let mut exercised := 0
  for fx in fixtures do
    match p.cells.find? fun c => c.fixture == fx && c.reader == reader && c.feature == feature with
    | some c =>
      if c.value == "na" then pure ()
      else
        exercised := exercised + 1
        if c.value != "pass" then fails := fails.push (fx, reasonOf c.value)
    | none =>
      let err := p.cells.find? fun c => c.fixture == fx && c.reader == reader && c.feature == "error"
      exercised := exercised + 1
      fails := fails.push (fx, "not measured: " ++ (err.map (reasonOf ·.value)).getD "no row from the probe")
  if exercised == 0 then return ("untested", #[])
  if fails.isEmpty then return ("pass", #[])
  let head := fails[0]!.1
  let more := if fails.size > 1 then s!"+{fails.size - 1}" else ""
  return (s!"fail:{head}{more}", fails.map fun (fx, why) => s!"{fx}: {why}")

/-- The cell for one (fixture, reader): the first failing feature, and the
features the fixture exercises. -/
def fixtureCell (p : Probe) (fixture reader : String) : String × Array String := Id.run do
  if (p.versions.find? (·.1 == reader)).isNone then return ("untested", #[])
  let mut ex : Array String := #[]
  let mut firstFail : Option String := none
  for f in features do
    match p.cells.find? fun c => c.fixture == fixture && c.reader == reader && c.feature == f with
    | some c =>
      if c.value != "na" then
        ex := ex.push f
        if c.value != "pass" && firstFail.isNone then firstFail := some f
    | none => if firstFail.isNone then firstFail := some f
  return (match firstFail with | some f => s!"fail:{f}" | none => "pass", ex)

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
  -- The HTML key is hermetic. Browser conversion is host-only: its source
  -- key binds this report to the current vector inputs, hrefs and shared
  -- recipe; its content key binds it to the exact converted bytes below.
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

-- ## Main

def regenerate : IO UInt32 := do
  if !(← System.FilePath.pathExists leantexBin) then
    return (← die 2 s!"html-oracle: {leantexBin} not found; run lake build first")
  -- Both freshness keys come from the tier's functions, so the matrix and
  -- `htmlreader --check` cannot disagree about the hermetic inputs.
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
    copyTree "tests/corpus" (work / "corpus")
    let mut fixtures : Array String := #[]
    let mut unbuilt : Array String := #[]
    let mut boundaryFailures : Array Scoreboard.BrowserFace := #[]
    -- Per fixture, the converter its W0605 log named — so a missing expected
    -- face becomes a failed record naming that tool.
    let mut faceTool : Array (String × String) := #[]
    for e in (← (work / "corpus").readDir).qsort (·.fileName < ·.fileName) do
      if e.fileName.endsWith ".tex" then
        let name := (e.fileName.dropEnd ".tex".length).toString
        let r ← IO.Process.output
          { cmd := leantexBin
            args := #["-q", "build", e.path.toString, "-o", (work / "corpus" / (name ++ ".html")).toString] }
        let log := r.stdout ++ r.stderr
        if (log.splitOn "warning[W0605]").length > 1 then
          let tool := if (log.splitOn "rsvg-convert").length > 1
            then "rsvg-convert" else "pdftocairo"
          faceTool := faceTool.push (name, tool)
        if (log.splitOn "warning[W0378]").length > 1 then
          boundaryFailures := boundaryFailures.push
            (Scoreboard.BrowserFace.failed name "!pdftocairo-boundary" "pdftocairo-boundary")
        if r.exitCode == 0 then fixtures := fixtures.push name else unbuilt := unbuilt.push name
    let captured ← capturedBrowserFaces (work / "corpus") fixtures boundaryFailures
    -- Account every expected converted-image face that produced no file at
    -- all (its conversion failed, so `capturedBrowserFaces` saw nothing) as a
    -- failed record naming the expected href and the tool.
    let mut browserFaces := captured
    for (fx, href) in keys.expectedFaces do
      unless browserFaces.any (fun f => f.fixture == fx && f.href == href) do
        let tool := ((faceTool.find? (·.1 == fx)).map (·.2)).getD "pdftocairo"
        browserFaces := browserFaces.push (Scoreboard.BrowserFace.failed fx href tool)
    let mut probe : Probe := { cells := #[], versions := #[], unavailable := #[] }
    let mut tools := s!"node {nodeVersion}"
    match chromium with
    | none =>
      tools := tools ++ "  chromium untested (no Playwright module launches a cached Chromium; LEANTEX_PLAYWRIGHT names one)"
      probe := { probe with unavailable := probe.unavailable.push ("chromium", "no launchable module") }
      probe := { probe with unavailable := probe.unavailable.push ("firefox", "not attempted") }
    | some (m, _) =>
      IO.FS.writeFile (work / "probe.cjs") probeJs
      let tokens := s!"{HtmlDoc.cssColor Contrast.light.ink} {HtmlDoc.cssColor Contrast.light.surface} " ++
        s!"{HtmlDoc.cssColor Contrast.dark.ink} {HtmlDoc.cssColor Contrast.dark.surface}"
      let out ← IO.Process.output
        { cmd := "node"
          args := #[(work / "probe.cjs").toString, (work / "corpus").toString] ++ fixtures
          env := #[("PW_MODULE", some m), ("LT_TOKENS", some tokens),
                   ("LT_READERS", some (String.intercalate " " readers))] }
      if out.exitCode != 0 then
        IO.eprintln s!"html-oracle: the probe exited {out.exitCode}:\n{out.stderr}"
      probe := parseProbe out.stdout
      let pwv ← moduleVersion m
      for r in readers do
        match probe.versions.find? (·.1 == r) with
        | some (_, v) => tools := tools ++ s!"  {r} {v} (playwright {pwv})"
        | none =>
          let why := ((probe.unavailable.find? (·.1 == r)).map (·.2)).getD "no row from the probe"
          tools := tools ++ s!"  {r} untested ({why})"
    tools := tools ++ s!"  {← toolVersion "xmllint" #["--version"]}"
    tools := tools ++ s!"  {← toolVersion "rsvg-convert" #["--version"]}"
    tools := tools ++ s!"  {← toolVersion "pdftocairo" #["-v"]}"
    tools := tools ++ s!"  {← pdftotextVersion}"
    IO.FS.createDirAll "tests/oracles"
    IO.FS.writeFile matrixPath
      (renderMatrix probe fixtures unbuilt tools date keys.html keys.browserFaceSource browserFaces)
    IO.println s!"html-oracle: wrote {matrixPath} — {fixtures.size} fixtures, {tools}"
  finally
    IO.FS.removeDirAll work
  checkFile matrixPath

/-- The checker against matrices written by hand: a green file passes; one
target cell `untested` or `fail:` fails it; a non-target cell gates nothing;
a target reader without a column is itself an offence. -/
def selftest : IO UInt32 := do
  let green := "target: chromium\n[feature]\n# feature chromium firefox\nload pass untested\n" ++
    "[fixture]\n# fixture chromium firefox exercised\ndeck pass untested load\n"
  let cases : List (String × String × Nat) :=
    [("green", green, 0),
     ("target untested", green.replace "load pass untested" "load untested untested", 1),
     ("target fail", green.replace "deck pass untested" "deck fail:load untested", 1),
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
  for (name, text) in [("no target", "[feature]\n# feature chromium\nload pass\n"),
                       ("row before header", "target: chromium\n[feature]\nload pass\n"),
                       ("short row", "target: chromium\n[feature]\n# feature chromium firefox\nload pass\n")] do
    if (parseMatrix text).isOk then
      IO.eprintln s!"FAIL {name}: parsed"
      bad := bad + 1
  if bad == 0 then
    IO.println "html-oracle: selftest ok"
    return 0
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--selftest"] => selftest
  | ["--check"] => checkFile matrixPath
  | ["--check", path] => checkFile path
  | [] => regenerate
  | _ => die 3 "usage: html-oracle [--check [path] | --selftest]"
