/-
Report of the engine's drawing of each invented SVG against Chromium's and librsvg's by DSSIM; a
figure drawn whole stays within the fallback's distance plus its noise.
Usage: lake build ScriptsModules && lake env lean --run scripts/svg-diff.lean [--update | --keep <dir> | --selftest]
-/
import scripts.RasterJudge
import LeanTex.Core.SvgPoster
import LeanTex.Core.LayoutFigure
import LeanTex.Core.SvgImport
import LeanTex.Core.FigureOutline

open LeanTex.Core

def recordPath : String := "testdata/oracles/svg-diff.tsv"

/-- The least `ε`: under a tenth of the raster judge's own tolerance. -/
def slack : Float := 0.002

/-- A font set of three roles — serif, sans, mono — from `dir`: each role's
regular, bold, italic and bold italic file, a missing style falling to the
role's regular. -/
def facesIn (dir : System.FilePath) (roles : Array (Array (Option String))) :
    IO (Except String Font.FontSet) := do
  let mut fonts : Array Font.Font := #[]
  let mut index : Array ((Nat × Nat × Bool) × Nat) := #[]
  let keys := #[(400, false), (700, false), (400, true), (700, true)]
  for (styles, slot) in roles.zipIdx do
    let regular := fonts.size
    for ((w, i), k) in keys.zipIdx do
      match styles[k]?.join with
      | none => index := index.push ((slot, w, i), regular)
      | some file =>
        let p := dir / file
        unless ← p.pathExists do return .error s!"{p} is missing"
        match Font.parse (← IO.FS.readBinFile p) with
        | .ok f =>
          index := index.push ((slot, w, i), fonts.size)
          fonts := fonts.push f
        | .error e => return .error s!"{p}: {e}"
  return .ok { fonts, index }

/-- The shipped faces the corpus sets in, every style the fonts directory
holds. -/
def shippedFaces : IO (Except String Font.FontSet) :=
  facesIn "testdata/corpus/fonts" #[
    #[some "SourceSerifPro-Regular.otf", some "SourceSerifPro-Bold.otf",
      some "SourceSerifPro-RegularIt.otf", some "SourceSerifPro-BoldIt.otf"],
    #[some "OpenSans-Regular.ttf", some "OpenSans-Bold.ttf", some "OpenSans-Italic.ttf",
      some "OpenSans-BoldItalic.ttf"],
    #[some "SourceCodePro-Regular.otf", none, none, none]]

/-- The host's faces each role reads — from `LEANTEX_DIFF_FONTS`, else
`/usr/share/fonts/dejavu` — and the generic family each role answers. -/
def hostRoles : Array (String × Array (Option String)) := #[
  ("serif", #[some "DejaVuSerif.ttf", some "DejaVuSerif-Bold.ttf", some "DejaVuSerif-Italic.ttf",
    some "DejaVuSerif-BoldItalic.ttf"]),
  ("sans-serif", #[some "DejaVuSans.ttf", some "DejaVuSans-Bold.ttf", some "DejaVuSans-Oblique.ttf",
    some "DejaVuSans-BoldOblique.ttf"]),
  ("monospace", #[some "DejaVuSansMono.ttf", some "DejaVuSansMono-Bold.ttf",
    some "DejaVuSansMono-Oblique.ttf", some "DejaVuSansMono-BoldOblique.ttf"])]

/-- The host's faces in `dir`, once fontconfig is checked to answer each role's generic
family in each style with the file loaded for it, the face Chromium and librsvg set the
reference's text in. -/
def hostFacesIn (dir : System.FilePath) : IO (Except String Font.FontSet) := do
  let styles := #[("", 0), (":bold", 1), (":italic", 2), (":bold:italic", 3)]
  for (generic, files) in hostRoles do
    for (suffix, k) in styles do
      let some file := files[k]?.join | continue
      let some r ← runTool "fc-match" #["-f", "%{file}", generic ++ suffix]
        | return .error "svg-diff needs fontconfig (fc-match)"
      unless r.stdout.trimAscii.toString == (dir / file).toString do
        return .error s!"fontconfig answers {generic}{suffix} with {r.stdout}, not {dir / file}: point LEANTEX_DIFF_FONTS at the faces it answers"
  facesIn dir (hostRoles.map (·.2))

def hostFaces : IO (Except String Font.FontSet) := do
  hostFacesIn ((← IO.getEnv "LEANTEX_DIFF_FONTS").getD "/usr/share/fonts/dejavu")

def fixtureFiles : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for dir in ["testdata/svg", "testdata/corpus/figures"] do
    for e in (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName) do
      if e.fileName.endsWith ".svg" then out := out.push e.path
  return out

/-- The width every drawing is shown at, in CSS pixels. -/
def rasterWidth : Nat := 800

/-- Playwright's module, looked up and never installed: `LEANTEX_PLAYWRIGHT`, else the
first `~/.npm/_npx/*/node_modules/playwright`. -/
def playwrightModule : IO (Option String) := do
  if let some m ← IO.getEnv "LEANTEX_PLAYWRIGHT" then return some m
  let some home ← IO.getEnv "HOME" | return none
  let npx := System.FilePath.mk home / ".npm" / "_npx"
  if !(← npx.isDir) then return none
  for e in ← npx.readDir do
    let m := e.path / "node_modules" / "playwright"
    if ← m.pathExists then return some m.toString
  return none

/-- The browser half: for each `svg<TAB>png<TAB>width` line of its list,
the SVG shown as an image of that width on a white page, the image's box
captured. -/
def shootJs : String :=
  "const fs = require('fs');\n" ++
  "const pw = require(process.env.PW_MODULE);\n" ++
  "(async () => {\n" ++
  "  const jobs = fs.readFileSync(process.argv[2], 'utf8').split('\\n').filter(l => l).map(l => l.split('\\t'));\n" ++
  "  const b = await pw.chromium.launch({headless: true, args: ['--no-sandbox', '--disable-gpu']});\n" ++
  "  const p = await b.newPage({viewport: {width: 1000, height: 1000}});\n" ++
  "  for (const [svg, png, w] of jobs) {\n" ++
  "    const src = 'data:image/svg+xml;base64,' + fs.readFileSync(svg).toString('base64');\n" ++
  "    await p.setContent(`<html><body style=\"margin:0;background:#fff\"><img id=\"f\" style=\"width:${w}px;display:block\" src=\"${src}\"></body></html>`);\n" ++
  "    await p.waitForFunction(() => { const i = document.getElementById('f'); return i.complete && i.naturalWidth > 0; });\n" ++
  "    await (await p.$('#f')).screenshot({path: png});\n" ++
  "  }\n" ++
  "  await b.close();\n" ++
  "})().catch(e => { console.error(e); process.exit(1); });\n"

/-- Every drawing of a run, rasterized in one browser session. -/
def rasterizeAll (dir : System.FilePath) (jobs : Array (System.FilePath × System.FilePath × Nat)) :
    IO Unit := do
  let some pw ← playwrightModule | throw <| IO.userError "svg-diff needs Playwright's Chromium"
  IO.FS.writeFile (dir / "shoot.js") shootJs
  IO.FS.writeFile (dir / "jobs.tsv")
    (String.join (jobs.toList.map fun (s, p, w) => s!"{s}\t{p}\t{w}\n"))
  let some r ← runTool "env" #[s!"PW_MODULE={pw}", "node", (dir / "shoot.js").toString,
      (dir / "jobs.tsv").toString]
    | throw <| IO.userError "svg-diff needs node"
  unless r.exitCode == 0 do throw <| IO.userError s!"svg-diff: Chromium failed: {r.stderr}"

mutual

-- conserves: none — a rewriting that takes elements out of a tree.
/-- A tree with every SVG element `drop` names taken out. -/
def pruneOne (drop : List String) : Xml.Item → Option Xml.Item
  | .text s => some (.text s)
  | .elem ns name attrs kids =>
    if ns == Svg.svgNs && drop.contains name then none
    else some (.elem ns name attrs (pruneList drop #[] kids.toList))

def pruneList (drop : List String) (acc : Array Xml.Item) : List Xml.Item → Array Xml.Item
  | [] => acc
  | n :: rest => pruneList drop ((pruneOne drop n).elim acc acc.push) rest

end

/-- The engine's standalone drawing of a pose in `fs`, `mutate` applied to
its import first (the identity, but for the selftest). -/
def nativeOf (fs : Font.FontSet) (mutate : Gfx.Figure Gfx.Run → Gfx.Figure Gfx.Run)
    (pose : Xml.Item) : String :=
  let (shaped, _) := Layout.shapeFigure fs (mutate (Svg.importTree pose).fig)
  FigureOutline.poster fs shaped

/-- librsvg's drawing of a canonical spelling, as the SVG it draws. -/
def fallbackOf (dir : System.FilePath) (tag : String) (canonical : ByteArray) :
    IO System.FilePath := do
  let input := dir / s!"{tag}.canonical.svg"
  let output := dir / s!"{tag}.fallback.svg"
  IO.FS.writeBinFile input canonical
  let some r ← runTool "rsvg-convert" #["--format=svg", "--output", output.toString, input.toString]
    | throw <| IO.userError "svg-diff needs rsvg-convert"
  unless r.exitCode == 0 do throw <| IO.userError s!"svg-diff: librsvg does not draw {tag}"
  return output

/-- One figure's distances from the reference (the engine's in the host's and the shipped
faces, the fallback's, the judge's two noises, both geometries) and whether the engine
draws it whole. -/
structure Row where
  name : String
  exact : Bool
  host : Float
  shipped : Float
  fallback : Float
  resample : Float
  respell : Float
  geom : Float
  fallbackGeom : Float
  deriving Inhabited

/-- A figure's tolerance: its larger noise, at least `slack`. -/
def Row.epsilon (r : Row) : Float := max slack (max r.resample r.respell)

def dist (dir : System.FilePath) (tag : String) (a b : System.FilePath) : IO Float := do
  match ← dssimAgainst dir tag a.toString b.toString with
  | some v => return v
  | none => throw <| IO.userError "svg-diff needs ImageMagick (magick compare)"

/-- Every figure's row: each drawn its ways, all rasterized, then judged;
the rasters copied to `keep` when it is given. -/
def measureAll (host shipped : Font.FontSet)
    (mutate : Gfx.Figure Gfx.Run → Gfx.Figure Gfx.Run := id) (keep : Option System.FilePath := none) :
    IO (Array Row) :=
  IO.FS.withTempDir fun dir => do
    let mut jobs : Array (System.FilePath × System.FilePath × Nat) := #[]
    let mut figs : Array (String × String × Bool) := #[]
    for f in ← fixtureFiles do
      let name := f.fileName.getD f.toString
      let tag := (name.dropEnd 4).toString
      let bytes ← IO.FS.readBinFile f
      let pose ← match SvgPoster.pose bytes false with
        | .ok t => pure t
        | .error e => throw <| IO.userError s!"svg-diff: {name} does not import: {e}"
      let exact := (Svg.importTree pose).fig.losses.isEmpty
      let still := (pruneOne Svg.animations pose).getD pose
      let bare := (pruneOne ["text"] still).getD still
      let put (k : String) (b : ByteArray) : IO System.FilePath := do
        let p := dir / s!"{tag}.{k}.svg"
        IO.FS.writeBinFile p b
        return p
      let authored ← put "ref" (if Svg.moves pose then Xml.renderItem still else bytes)
      let respelled ← put "respelled" (Xml.renderItem still)
      let bareRef ← put "bare" (Xml.renderItem bare)
      let inHost ← put "host" (nativeOf host mutate pose).toUTF8
      let inShipped ← put "shipped" (nativeOf shipped mutate pose).toUTF8
      let nativeBare ← put "native-bare" (nativeOf host mutate bare).toUTF8
      let fallback ← fallbackOf dir tag (Xml.renderItem pose)
      let fallbackBare ← fallbackOf dir s!"{tag}-bare" (Xml.renderItem bare)
      for (k, p, w) in [("ref", authored, rasterWidth), ("wide", authored, rasterWidth + 1),
          ("respelled", respelled, rasterWidth), ("bare", bareRef, rasterWidth),
          ("host", inHost, rasterWidth), ("shipped", inShipped, rasterWidth),
          ("native-bare", nativeBare, rasterWidth), ("fallback", fallback, rasterWidth),
          ("fallback-bare", fallbackBare, rasterWidth)] do
        jobs := jobs.push (p, dir / s!"{tag}.{k}.png", w)
      figs := figs.push (name, tag, exact)
    rasterizeAll dir jobs
    if let some k := keep then
      IO.FS.createDirAll k
      for (_, png, _) in jobs do
        IO.FS.writeBinFile (k / (png.fileName.getD "x.png")) (← IO.FS.readBinFile png)
    let mut rows : Array Row := #[]
    for (name, tag, exact) in figs do
      let png (k : String) : System.FilePath := dir / s!"{tag}.{k}.png"
      rows := rows.push {
        name, exact
        host := ← dist dir s!"{tag}-h" (png "host") (png "ref")
        shipped := ← dist dir s!"{tag}-s" (png "shipped") (png "ref")
        fallback := ← dist dir s!"{tag}-f" (png "fallback") (png "ref")
        resample := ← dist dir s!"{tag}-w" (png "wide") (png "ref")
        respell := ← dist dir s!"{tag}-r" (png "respelled") (png "ref")
        geom := ← dist dir s!"{tag}-g" (png "native-bare") (png "bare")
        fallbackGeom := ← dist dir s!"{tag}-fg" (png "fallback-bare") (png "bare") }
    return rows

/-- A distance spelled to five places. -/
def spell (v : Float) : String :=
  let n := (v * 100000).round.toUInt64.toNat
  let s := toString n
  let s := "".pushn '0' (6 - min 6 s.length) ++ s
  s!"{(s.take (s.length - 5)).toString}.{(s.drop (s.length - 5)).toString}"

/-- What the gate names: a figure drawn whole whose drawing in the host's
faces, whole or in its geometry, is farther from the reference than the
fallback's past its tolerance. -/
def offences (rows : Array Row) : Array String :=
  rows.foldl (fun acc r =>
    let ε := r.epsilon
    if !r.exact then acc else
    let acc := if r.host > r.fallback + ε then
        acc.push s!"{r.name}: the engine's drawing {spell r.host}, the fallback's {spell r.fallback} (ε {spell ε})"
      else acc
    if r.geom > r.fallbackGeom + ε then
      acc.push s!"{r.name}: the engine's geometry {spell r.geom}, the fallback's {spell r.fallbackGeom} (ε {spell ε})"
    else acc) #[]

def columns : String :=
  "figure\troute\tengine\tfallback\tshipped-faces\tresample\trespell\tengine-geometry\tfallback-geometry"

def Row.line (r : Row) : String :=
  s!"{r.name}\t{if r.exact then "native" else "lossy"}\t{spell r.host}\t{spell r.fallback}\t{spell r.shipped}\t{spell r.resample}\t{spell r.respell}\t{spell r.geom}\t{spell r.fallbackGeom}"

/-- The judge broken once, each way, on synthetic rows, then the true pipeline with the
engine's import emptied. -/
def selftest (host shipped : Font.FontSet) : IO UInt32 := do
  let mut fails : Array String := #[]
  let row (n : String) (exact : Bool) (drawn geom noise : Float) : Row :=
    { name := n, exact, host := drawn, shipped := 0, fallback := 0.002, resample := noise, respell := 0
      geom, fallbackGeom := 0.002 }
  if (offences #[row "a" true 0.001 0.001 0, row "b" true 0.05 0.001 0]).size != 1 then
    fails := fails.push "a drawing past the fallback is named, one within it is not"
  if (offences #[row "a" true 0.001 0.001 0, row "b" true 0.001 0.05 0]).size != 1 then
    fails := fails.push "a geometry past the fallback is named, one within it is not"
  if !(offences #[row "c" false 0.05 0.05 0]).isEmpty then
    fails := fails.push "a lossy figure is not held to the fallback"
  if !(offences #[row "d" true 0.02 0.02 0.02]).isEmpty then
    fails := fails.push "a figure's noise widens its tolerance"
  if !((spell 0.012345 == "0.01235") || (spell 0.012345 == "0.01234")) then
    fails := fails.push s!"spelling: {spell 0.012345}"
  -- Faces fontconfig does not answer the generics with are refused, never compared.
  if (← hostFacesIn "testdata/corpus/fonts").toBool then
    fails := fails.push "faces fontconfig does not answer with are refused"
  let blank ← measureAll host shipped fun fig =>
    { fig with nodes := #[], symbols := #[], outlines := #[] }
  let named := offences blank
  let mut caught := 0
  for b in blank do
    if b.exact then
      if named.any (·.startsWith s!"{b.name}: the engine's drawing") then caught := caught + 1
      else if b.host > 4 * b.epsilon then
        fails := fails.push s!"{b.name}: an empty drawing reads as no worse than the fallback"
  if caught == 0 then fails := fails.push "an empty drawing is named for no figure"
  IO.println s!"svg-diff selftest: the empty drawing named on {caught} figures"
  for f in fails do IO.eprintln s!"FAIL {f}"
  IO.println s!"svg-diff selftest: {fails.size} failures"
  return if fails.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  let host ← match ← hostFaces with
    | .ok fs => pure fs
    | .error e => IO.eprintln s!"svg-diff: {e}"; return 1
  let shipped ← match ← shippedFaces with
    | .ok fs => pure fs
    | .error e => IO.eprintln s!"svg-diff: {e}"; return 1
  if args.contains "--selftest" then return ← selftest host shipped
  let keep := match args.dropWhile (· != "--keep") with
    | _ :: d :: _ => some (System.FilePath.mk d)
    | _ => none
  let rows ← measureAll host shipped id keep
  IO.println s!"svg-diff: {columns}"
  for r in rows do IO.println s!"svg-diff: {r.line}"
  if args.contains "--update" then
    IO.FS.writeFile recordPath (String.intercalate "\n"
      (["# written by scripts/svg-diff.lean --update, as evidence (the gate reads its own run): each",
        "# invented figure's DSSIM from Chromium's drawing of its authored bytes — the engine's in the",
        "# host's faces, the fallback's (librsvg of the canonical parse), the engine's in the shipped",
        "# faces, the judge's noise (the reference one pixel wider; the canonical respelling), then",
        "# the engine's and the fallback's geometry, every text taken out. Never worse: a figure",
        s!"# drawn whole stays within the fallback, whole and in its geometry, by its noise, at least {spell slack}.",
        s!"# {columns}"] ++ rows.toList.map Row.line) ++ "\n")
    IO.println s!"svg-diff: recorded {rows.size} figures"
  let bad := offences rows
  for b in bad do IO.eprintln s!"svg-diff: worse: {b}"
  return if bad.isEmpty then 0 else 1
