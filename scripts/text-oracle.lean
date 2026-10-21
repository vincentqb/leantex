/-
The text-layer oracle: each corpus artifact's text read by this engine's readers and by pdftotext
and Chromium, one cell per fixture × tool in testdata/oracles/text-layer-matrix.txt.
Usage: lake build leantex ScriptsModules && lake env lean --run scripts/text-oracle.lean
-/
import LeanTex
import scripts.Board
import scripts.Playwright

open LeanTex.Core

def matrixPath : String := "testdata/oracles/text-layer-matrix.txt"
def leantexBin : String := ".lake/build/bin/leantex"

/-- A text with each run of white space and form feeds one space, none at either end. -/
def normWs (s : String) : String :=
  " ".intercalate ((s.split fun c => c.isWhitespace || c == '\x0C').toList.map (·.toString)
    |>.filter (!·.isEmpty))

/-- A string as the DOM dump spells it: quoted, a quote, backslash and line feed escaped, other
controls as `\u` escapes. -/
def esc (s : String) : String := Id.run do
  let mut o := "\""
  for ch in s.toList do
    let c := ch.toNat
    if ch == '"' then o := o ++ "\\\""
    else if ch == '\\' then o := o ++ "\\\\"
    else if ch == '\n' then o := o ++ "\\n"
    else if c < 0x20 || c == 0x7f then
      let h := String.ofList (Nat.toDigits 16 c)
      o := o ++ "\\u" ++ "".pushn '0' (4 - h.length) ++ h
    else o := o.push ch
  return o ++ "\""

mutual

/-- A parsed tree as the DOM dump spells it. -/
def dump : HtmlRead.Dom → String
  | .text s => esc s
  | .elem t attrs kids =>
    let a := attrs.foldl (fun acc (k, v) => acc ++ " " ++ k ++ "=" ++ esc v) ""
    "<" ++ t ++ a ++ ">" ++ dumpList "" kids.toList ++ "</>"

def dumpList (acc : String) : List HtmlRead.Dom → String
  | [] => acc
  | d :: rest => dumpList (acc ++ dump d) rest

end

/-- The browser side: each page loaded with scripting off, its document element dumped. -/
def domProbe : String := r#"
const pw = require(process.env.PW_MODULE);
const fs = require('fs');
const path = require('path');
(async () => {
  const b = await pw.chromium.launch({headless: true, args: ['--no-sandbox', '--disable-gpu']});
  const ctx = await b.newContext({javaScriptEnabled: false});
  const page = await ctx.newPage();
  for (const f of process.argv.slice(2)) {
    await page.goto('file://' + path.resolve(f), {waitUntil: 'domcontentloaded', timeout: 120000});
    const out = await page.evaluate(() => {
      const esc = s => {
        let o = '"';
        for (const ch of s) {
          const c = ch.codePointAt(0);
          if (ch === '"') o += '\\"'; else if (ch === '\\') o += '\\\\';
          else if (ch === '\n') o += '\\n';
          else if (c < 0x20 || c === 0x7f) o += '\\u' + c.toString(16).padStart(4, '0');
          else o += ch;
        }
        return o + '"';
      };
      const dump = n => {
        if (n.nodeType === 3) return esc(n.data);
        if (n.nodeType === 8) return '<!--' + esc(n.data) + '-->';
        if (n.nodeType !== 1) return '';
        let s = '<' + n.localName.toLowerCase();
        for (const a of n.attributes) s += ' ' + a.name.toLowerCase() + '=' + esc(a.value);
        s += '>';
        const kids = n.localName === 'template' ? n.content.childNodes : n.childNodes;
        for (const k of kids) s += dump(k);
        return s + '</>';
      };
      return dump(document.documentElement);
    });
    fs.writeFileSync(f + '.dom', out);
  }
  await b.close();
})().catch(e => { console.error(String(e.message).split('\n')[0]); process.exit(1); });
"#

/-- One tool's version line, or `none` when it does not run. -/
def pdftotextVersion : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "pdftotext", args := #["-v"] }
    let line := ((out.stderr ++ out.stdout).splitOn "\n").headD ""
    return ((line.splitOn " ").getLast?).map (·.trimAscii.toString)
  catch _ => return none

/-- The PDF cell: pdftotext's raw content-order text, its page crop widened past any text a file
places outside its pages, against this engine's reading, each run of white space one space. -/
def pdfCell (pdf : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile pdf
  let ours ← match PdfTextRead.extract bytes with
    | .ok x => pure (some (normWs (x.contentText true)))
    | .error _ => pure none
  let some ours := ours | return "fail:unread"
  let out ← IO.Process.output
    { cmd := "pdftotext"
      args := #["-raw", "-enc", "UTF-8", "-W", "100000", "-H", "100000", pdf.toString, "-"] }
  if out.exitCode != 0 then return "fail:tool"
  return if ours == normWs out.stdout then "pass" else "fail:text"

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then
    let tree : HtmlRead.Dom := .elem "p" #[("title", "q\"")] #[.text "a\nb"]
    let ok := dump tree == "<p title=\"q\\\"\">\"a\\nb\"</>" && normWs " a\x0C  b\n" == "a b"
    IO.println (if ok then "text-oracle selftest: all passed" else "FAIL text-oracle selftest")
    return if ok then 0 else 1
  if !(← System.FilePath.pathExists leantexBin) then
    IO.eprintln s!"text-oracle: {leantexBin} not found; run lake build first"
    return 2
  let ptv ← pdftotextVersion
  let chromium ← findChromium "node"
  IO.FS.withTempDir fun dir => do
    let docs ← Scoreboard.Hermetic.corpusDocs "testdata/corpus"
    let mut built : Array (String × Option System.FilePath × Option System.FilePath) := #[]
    for (name, path) in docs do
      let pdf := dir / s!"{name}.pdf"
      let html := dir / s!"{name}.html"
      let b1 ← IO.Process.output { cmd := leantexBin, args := #["-q", "build", path.toString, "-o", pdf.toString] }
      let b2 ← IO.Process.output { cmd := leantexBin, args := #["-q", "build", path.toString, "-o", html.toString] }
      built := built.push (name,
        if b1.exitCode == 0 || (← pdf.pathExists) then some pdf else none,
        if b2.exitCode == 0 || (← html.pathExists) then some html else none)
    let mut pdfRows : Array (String × String) := #[]
    for (name, pdf?, _) in built do
      let cell ← match pdf?, ptv with
        | none, _ => pure "unbuilt"
        | _, none => pure "untested"
        | some pdf, some _ => pdfCell pdf
      pdfRows := pdfRows.push (name, cell)
    let htmls := built.filterMap fun (_, _, h) => h
    let mut browserVersion := "absent"
    let mut browserRan := false
    if let some (module, version) := chromium then
      browserVersion := version
      let probe := dir / "dom.cjs"
      IO.FS.writeFile probe domProbe
      let out ← IO.Process.output
        { cmd := "node"
          args := #[probe.toString] ++ htmls.map (·.toString)
          env := #[("PW_MODULE", some module)] }
      if out.exitCode != 0 then
        IO.eprintln s!"text-oracle: the browser probe failed: {out.stderr}"
      else browserRan := true
    let mut htmlRows : Array (String × String) := #[]
    for (name, _, html?) in built do
      let cell ← match html?, browserRan with
        | none, _ => pure "unbuilt"
        | _, false => pure "untested"
        | some html, true =>
          let domPath : System.FilePath := html.toString ++ ".dom"
          if !(← domPath.pathExists) then pure "fail:browser"
          else
            let want ← IO.FS.readFile domPath
            match HtmlRead.parse (← IO.FS.readFile html) with
            | some d => pure (if dump d == want then "pass" else "fail:tree")
            | none => pure "fail:unread"
      htmlRows := htmlRows.push (name, cell)
    let pad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)
    let w := (docs.foldl (fun m (n, _) => max m n.length) 0) + 2
    let mut out := s!"# generated by scripts/text-oracle.lean — do not hand-edit\n\
target: pdftotext chromium\n\
tools: pdftotext {ptv.getD "absent"}  chromium {browserVersion}\n\
reader-key: {← Scoreboard.textLayerKey}\n\n[pdf]\n# {pad "fixture" (w - 2)}pdftotext\n"
    for (n, c) in pdfRows do out := out ++ pad n w ++ c ++ "\n"
    out := out ++ s!"\n[html]\n# {pad "fixture" (w - 2)}chromium\n"
    for (n, c) in htmlRows do out := out ++ pad n w ++ c ++ "\n"
    IO.FS.writeFile matrixPath out
    let passes (rows : Array (String × String)) := (rows.filter (·.2 == "pass")).size
    IO.println s!"text-oracle: pdf {passes pdfRows}/{pdfRows.size}, html {passes htmlRows}/{htmlRows.size}; wrote {matrixPath}"
    return 0
