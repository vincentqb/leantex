import LeanTex.Cli.ImageAssets
import Tests.Support

/-! External source-only image oracle. No generated PDF, frame sequence or
cached conversion is present when the real driver starts. -/

namespace Tests

/-- Read the raw RGB raster Poppler wrote, on pixel boundaries. Looking for
three bytes at every offset would also count transitions from white to black
as red, even on a page with no coloured ink. -/
private def terminalInk (file : System.FilePath) : IO (Nat × Nat) := do
  let bytes ← IO.FS.readBinFile file
  let mut start := 0
  let mut lines := 0
  for i in [:bytes.size] do
    if bytes[i]! == 10 then lines := lines + 1
    if lines == 3 then
      start := i + 1
      break
  let header := String.fromUTF8! (bytes.extract 0 start)
  unless header.startsWith "P6\n" && header.endsWith "\n255\n" &&
      start > 0 && (bytes.size - start) % 3 == 0 do
    throw <| IO.userError "the raster oracle requires Poppler's raw RGB PPM"
  let mut red := 0
  let mut blue := 0
  for i in [start:bytes.size:3] do
    if bytes[i]! == 255 && bytes[i + 1]! == 0 && bytes[i + 2]! == 0 then red := red + 1
    if bytes[i]! == 0 && bytes[i + 1]! == 0 && bytes[i + 2]! == 255 then blue := blue + 1
  return (red, blue)

/-- Build both artifacts from two SVGs alone. The moving square starts
invisible and ends red; its native PDF and print face must paint the end,
while the browser receives the unchanged animation. The other source is an
extensionless static include. -/
def svgTerminalDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let moving := (svgDocument (width := 32) (height := 16))
    "<rect width=\"16\" height=\"16\" fill=\"red\" opacity=\"0\">\
    <animate attributeName=\"opacity\" values=\"0;1\" keyTimes=\"0;1\" \
      calcMode=\"linear\" dur=\"2s\" repeatCount=\"indefinite\"/>\
    <animate attributeName=\"x\" values=\"0;16\" keyTimes=\"0;1\" \
      calcMode=\"linear\" dur=\"2s\" repeatCount=\"indefinite\"/>\
    </rect>"
  let still := (svgDocument (width := 32) (height := 16)) "<rect width=\"16\" height=\"16\" fill=\"blue\"/>"
  IO.FS.withTempDir fun dir => do
    IO.FS.writeBinFile (dir / "moving.svg") moving
    IO.FS.writeBinFile (dir / "still.svg") still
    IO.FS.writeFile (dir / "figure.tex")
      "\\documentclass{article}\n\\begin{document}\n\
      \\animategraphics[poster=last,width=64pt,alt={Moving square}]{10}{moving}{}{}\n\
      \\includegraphics[width=64pt,alt={Static square}]{still}\n\
      \\end{document}\n"
    for ext in ["pdf", "html"] do
      let run ← IO.Process.output {
        cmd := binary.toString, cwd := some dir
        args := #["figure.tex", "-o", ("figure." ++ ext)]
        env := #[("LEANTEX_FONT", some font.toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
      let log := run.stdout ++ run.stderr
      check ref s!"source-only SVG: {ext} builds both figures without image loss"
        (run.exitCode == 0 && !((log.splitOn "W0601").length > 1) &&
          !((log.splitOn "W0602").length > 1) && !((log.splitOn "W0605").length > 1))
    let html ← IO.FS.readFile (dir / "figure.html")
    check ref "source-only SVG: both HTML images have reachable source attributes"
      ((html.splitOn "<img ").length == 3 && (html.splitOn "data-image-src=").length == 1)
    let mut originalMoving := false
    let mut originalStill := false
    let mut staticRed := false
    for entry in ← (dir / "figure.assets").readDir do
      let bytes ← IO.FS.readBinFile entry.path
      let name := entry.fileName
      let linked := hasStr html ("figure.assets/" ++ name)
      if bytes == moving then originalMoving := linked
      if bytes == still then originalStill := linked
      if name.startsWith "p" && name.endsWith ".svg" && linked then
        let pdf := dir / "poster.pdf"
        let converted ← IO.Process.output {
          cmd := "rsvg-convert"
          args := #["--format=pdf", "--output", pdf.toString, entry.path.toString] }
        if converted.exitCode == 0 then
          let raster ← IO.Process.output {
            cmd := "pdftoppm"
            args := #["-r", "144", "-singlefile", pdf.toString, (dir / "poster").toString] }
          if raster.exitCode == 0 then
            let (red, _) ← terminalInk (dir / "poster.ppm")
            staticRed := staticRed || red > 400
    check ref "source-only SVG: HTML publishes the original moving and static bytes"
      (originalMoving && originalStill)
    check ref "source-only SVG: the linked print poster paints the final red square"
      staticRed
    let raster ← IO.Process.output {
      cmd := "pdftoppm"
      args := #["-r", "72", "-singlefile", (dir / "figure.pdf").toString,
        (dir / "page").toString] }
    check ref "source-only SVG: the shipped PDF renders" (raster.exitCode == 0)
    if raster.exitCode == 0 then
      let (red, blue) ← terminalInk (dir / "page.ppm")
      -- Each square is 32pt wide, or 1024 pixels at 72dpi; allow antialiasing.
      check ref "source-only SVG: native PDF paints the final animation and static figure"
        (red > 700 && blue > 700)
    check ref "source-only SVG: compilation needs no generated figure PDF"
      (!(← (dir / "moving.pdf").pathExists) && !(← (dir / "still.pdf").pathExists))
    check ref "source-only SVG: compilation preserves both author sources"
      ((← IO.FS.readBinFile (dir / "moving.svg")) == moving &&
        (← IO.FS.readBinFile (dir / "still.svg")) == still)

private def terminalBoundaryError (result : Except String α) : Bool :=
  match result with
  | .error err => (err.splitOn "SVG last poster").length > 1
  | .ok _ => false

/-- Compare the converter's actual PDF drawing, including opacity resources.
The reader removes file metadata and renumbers the copied resource graph. -/
private def terminalSamePlan (a b : LeanTex.Core.Image.Plan) : Bool :=
  match a.form, b.form with
  | some af, some bf =>
    let a := af.val
    let b := bf.val
    let chunk : LeanTex.Core.PdfRead.Chunk → Nat ⊕ ByteArray := fun
      | .bytes bytes => .inr bytes
      | .ref n => .inl n
    #[a.x0, a.y0, a.x1, a.y1] == #[b.x0, b.y0, b.x1, b.y1] &&
      a.content == b.content && a.resources.map chunk == b.resources.map chunk &&
      (a.objects.map fun o => (o.chunks.map chunk, o.stream)) ==
        (b.objects.map fun o => (o.chunks.map chunk, o.stream))
  | _, _ => false

private def terminalRaster (dir : System.FilePath) (name : String)
    (bytes : ByteArray) : IO ByteArray := do
  let input := dir / (name ++ ".svg")
  let output := dir / (name ++ ".png")
  IO.FS.writeBinFile input bytes
  let run ← IO.Process.output {
    cmd := "rsvg-convert"
    args := #["--format=png", "--output", output.toString, input.toString] }
  unless run.exitCode == 0 do
    throw <| IO.userError s!"SVG terminal raster {name}: {run.stdout}{run.stderr}"
  let raster ← IO.FS.readBinFile output
  if raster.isEmpty then throw <| IO.userError s!"SVG terminal raster {name} is empty"
  return raster

/-- `.last` owes the pose immediately before a synchronized cycle ends.
Unsupported tracks return a boundary error, even when their last token
looks valid. Accepted tracks produce the same PDF drawing and rasterized
print face as an independently authored static pose, distinct from the
base drawing. Requires xmllint, xsltproc and librsvg. -/
def svgTerminalBoundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let track (attr values timing : String) :=
    s!"<animate attributeName=\"{attr}\" values=\"{values}\" {timing}/>"
  let square (attrs animation : String) :=
    s!"<rect width=\"16\" height=\"16\" fill=\"red\" {attrs}>{animation}</rect>"
  let clock := "dur=\"2s\" repeatCount=\"indefinite\" "
  let linear := clock ++ "calcMode=\"linear\" keyTimes=\"0;1\""
  let three := clock ++ "calcMode=\"linear\" keyTimes=\"0;0.5;1\""
  let x := track "x" "0;16" linear
  let opacity := track "opacity" "0;1" linear
  let pathStart := "M0,0L16,0L16,16L0,16"
  let pathEnd := "M16,0L32,0L32,16L16,16"
  let path (animation : String) :=
    s!"<path fill=\"red\" d=\"{pathStart}\">{animation}</path>"
  for (name, body) in [
      ("discrete keyTime one is not the pre-end pose",
        square "x=\"0\"" (track "x" "0;16"
          (clock ++ "calcMode=\"discrete\" keyTimes=\"0;1\""))),
      ("malformed middle scalar", square "x=\"0\"" (track "x" "0;nope;16" three)),
      ("malformed middle opacity",
        square "opacity=\"0\"" (track "opacity" "0;0.5oops;1" three)),
      ("empty middle scalar", square "x=\"0\"" (track "x" "0;;16" three)),
      ("nonfinite middle scalar", square "x=\"0\"" (track "x" "0;Infinity;16" three)),
      ("NaN middle scalar", square "x=\"0\"" (track "x" "0;NaN;16" three)),
      ("unit-bearing middle scalar", square "x=\"0\"" (track "x" "0;8px;16" three)),
      ("singleton values track", square "x=\"0\"" (track "x" "16" clock)),
      ("invalid middle M/L path number",
        path (track "d" (pathStart ++ ";M0,0Lbad,16;" ++ pathEnd) three)),
      ("invalid final M/L path pair",
        path (track "d" (pathStart ++ ";M16,0L32,") linear)),
      ("mismatched linear path length",
        path (track "d" (pathStart ++ ";M16,0L32,0L32,16") linear)),
      ("extra M command in path",
        path (track "d" (pathStart ++ ";M16,0M32,0L32,16L16,16") linear)),
      ("duplicate target attribute", square "x=\"0\"" (x ++ x)),
      ("geometry attribute on the wrong target",
        "<circle cx=\"8\" cy=\"8\" r=\"8\" fill=\"red\">" ++ x ++ "</circle>"),
      ("opacity on a nongraphical target",
        "<defs>" ++ opacity ++ "</defs>" ++ square "" ""),
      ("href fragment target",
        square "id=\"target\" x=\"0\"" (track "x" "0;16" (linear ++ " href=\"#target\""))),
      ("aliased xlink fragment target",
        square "id=\"target\" x=\"0\"" (track "x" "0;16"
          (linear ++ " xmlns:l=\"http://www.w3.org/1999/xlink\" l:href=\"#target\""))),
      ("sibling fragment target",
        square "id=\"target\" x=\"0\"" "" ++
          track "x" "0;16" (linear ++ " href=\"#target\"")),
      ("inline CSS overrides opacity", square "style=\"opacity:0\"" opacity),
      ("stylesheet overrides opacity",
        "<style>rect { opacity: 0 }</style>" ++ square "" opacity),
      ("unequal durations",
        square "x=\"0\" opacity=\"0\"" (x ++ track "opacity" "0;1" "dur=\"3s\"")),
      ("exponent duration", square "x=\"0\"" (track "x" "0;16" "dur=\"2e0s\"")),
      ("space before duration unit", square "x=\"0\"" (track "x" "0;16" "dur=\"2 s\"")),
      ("delayed begin", square "x=\"0\"" (track "x" "0;16" (linear ++ " begin=\"1s\""))),
      ("early end", square "x=\"0\"" (track "x" "0;16" (linear ++ " end=\"1s\""))),
      ("additive track", square "x=\"0\"" (track "x" "0;16" (linear ++ " additive=\"sum\""))),
      ("accumulating track",
        square "x=\"0\"" (track "x" "0;16" (linear ++ " accumulate=\"sum\""))),
      ("partial repeat", square "x=\"0\"" (track "x" "0;16" "dur=\"2s\" repeatCount=\"1.5\"")),
      ("set element", square "opacity=\"0\""
        "<set attributeName=\"opacity\" to=\"1\" begin=\"1s\"/>"),
      ("motion element", square ""
        "<animateMotion path=\"M 0 0 L 16 0\" dur=\"2s\"/>"),
      ("transform element", square ""
        "<animateTransform attributeName=\"transform\" type=\"translate\" from=\"0 0\" to=\"16 0\" dur=\"2s\"/>"),
      ("colour animation element", square ""
        "<animateColor attributeName=\"fill\" values=\"red;blue\" dur=\"2s\"/>")] do
    let source := (svgDocument (width := 32) (height := 16)) body
    let first ← LeanTex.Cli.ImageAssets.svgPlan .default source .first
    check ref s!"SVG terminal boundary {name}: base SVG remains readable" first.isOk
    let last ← LeanTex.Cli.ImageAssets.svgPlan .default source .last
    check ref s!"SVG terminal boundary {name}: native last returns its boundary error"
      (terminalBoundaryError last)
    let poster ← LeanTex.Cli.ImageAssets.svgPoster source .last
    check ref s!"SVG terminal boundary {name}: print last returns its boundary error"
      (terminalBoundaryError poster)
  let finalSquare := square "x=\"16\" opacity=\"1\"" ""
  for (name, body, expected) in [
      ("linear scalar and fractional opacity",
        square "x=\"0\" opacity=\"0\""
          (track "x" "-8;4;16" three ++ track "opacity" "0;0.25;0.5" three),
        square "x=\"16\" opacity=\"0.5\"" ""),
      ("discrete last keyTime below one",
        square "x=\"0\"" (track "x" "0;8;16"
          (clock ++ "calcMode=\"discrete\" keyTimes=\"0;0.25;0.75\"")),
        finalSquare),
      ("default linear keyTimes",
        square "x=\"0\" opacity=\"0\""
          (track "x" "0;8;16" clock ++ track "opacity" "0;0.5;1" clock),
        finalSquare),
      ("default discrete keyTimes",
        square "x=\"0\"" (track "x" "0;8;16" (clock ++ "calcMode=\"discrete\"")),
        finalSquare),
      ("absent base x attribute", square "" x, finalSquare),
      ("empty base x attribute", square "x=\"\"" x, finalSquare),
      ("matching M/L path structure",
        path (track "d" (pathStart ++ ";" ++ pathEnd) linear),
        s!"<path fill=\"red\" d=\"{pathEnd}\"/>"),
      ("whitespace around M/L coordinates",
        path (track "d" (pathStart ++ ";M 16 , 0 L 32 , 0 L 32 , 16 L 16 , 16") linear),
        s!"<path fill=\"red\" d=\"{pathEnd}\"/>")] do
    let source := (svgDocument (width := 32) (height := 16)) body
    let target := (svgDocument (width := 32) (height := 16)) expected
    let first ← LeanTex.Cli.ImageAssets.svgPlan .default source .first
    let last ← LeanTex.Cli.ImageAssets.svgPlan .default source .last
    let static ← LeanTex.Cli.ImageAssets.svgPlan .default target .first
    match first, last, static with
    | .ok first, .ok last, .ok static =>
      check ref s!"SVG terminal {name}: native last is the expected static drawing"
        (terminalSamePlan last static)
      check ref s!"SVG terminal {name}: native last differs from the base drawing"
        (!terminalSamePlan first last)
    | .error err, _, _ | _, .error err, _ | _, _, .error err =>
      check ref s!"SVG terminal {name}: conversion failed: {err}" false
    match ← LeanTex.Cli.ImageAssets.svgPoster source .last with
    | .error err => check ref s!"SVG terminal {name}: print face failed: {err}" false
    | .ok poster =>
      IO.FS.withTempDir fun dir => do
        let actual ← terminalRaster dir "actual" poster
        let wanted ← terminalRaster dir "expected" target
        let base ← terminalRaster dir "base" source
        check ref s!"SVG terminal {name}: print face paints the expected terminal pixels"
          (actual == wanted)
        check ref s!"SVG terminal {name}: terminal pixels differ from the base drawing"
          (actual != base)

end Tests
