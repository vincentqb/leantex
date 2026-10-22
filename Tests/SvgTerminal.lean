module

public import LeanTex.Cli.ImageAssets
public import LeanTex.Core.SvgImport
public import LeanTex.Core.SvgPoster
public import Tests.SvgValidation
public import Tests.Support

public section

/-! A source-only image oracle: no generated PDF, frame sequence or cached conversion exists when
the driver starts. -/

namespace Tests

/-- The red and blue pixels of Poppler's raw RGB raster. -/
private def terminalInk (file : System.FilePath) : IO (Nat × Nat) := do
  let counts ← ppmCounts file #[(255, 0, 0), (0, 0, 255)]
  return (counts[0]?.getD 0, counts[1]?.getD 0)

/-- Both artifacts from two SVGs alone: the moving square's PDF and print face paint its end pose,
the browser the unchanged animation. -/
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
          !((log.splitOn "W0602").length > 1))
    let html ← IO.FS.readFile (dir / "figure.html")
    check ref "source-only SVG: both HTML images have reachable source attributes"
      ((html.splitOn "<img ").length == 3 && (html.splitOn "data-image-src=").length == 1)
    let embedded (attr : String) : IO (Array ByteArray) := do
      let mut out : Array ByteArray := #[]
      for piece in (html.splitOn s!"{attr}=\"").drop 1 do
        let href := (piece.splitOn "\"").headD ""
        if href.startsWith "data:image/svg+xml" then
          let (_, data) ← htmlDataDecode href
          out := out.push data
      return out
    let images ← embedded "src"
    let posters ← embedded "srcset"
    let originalMoving := images.contains moving
    let originalStill := images.contains still
    let mut staticRed := false
    for poster in posters do
      let face := dir / "poster.svg"
      IO.FS.writeBinFile face poster
      let pdf := dir / "poster.pdf"
      let converted ← IO.Process.output {
        cmd := "rsvg-convert"
        args := #["--format=pdf", "--output", pdf.toString, face.toString] }
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

/-- `.last` owes the pose just before a synchronized cycle ends, unsupported tracks are a boundary
error, and the pose rasterizes to its target; requires librsvg. -/
def svgTerminalBoundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (name, body) in svgTerminalRefused do
    let source := (svgDocument (width := 32) (height := 16)) body
    check ref s!"SVG terminal boundary {name}: base SVG remains readable"
      (LeanTex.Core.SvgPoster.pose source false).toBool
    check ref s!"SVG terminal boundary {name}: native last returns its boundary error"
      (terminalBoundaryError (LeanTex.Core.SvgPoster.pose source true))
    let poster ← LeanTex.Cli.ImageAssets.canonicalPoster source .last
    check ref s!"SVG terminal boundary {name}: print last returns its boundary error"
      (terminalBoundaryError poster)
  for (name, body, expected) in svgTerminalAccepted do
    let source := (svgDocument (width := 32) (height := 16)) body
    let target := (svgDocument (width := 32) (height := 16)) expected
    let marks (bytes : ByteArray) (atEnd : Bool) :=
      (LeanTex.Core.SvgPoster.pose bytes atEnd).map fun t => (LeanTex.Core.Svg.importTree t).fig.marks
    match marks source false, marks source true, marks target false with
    | .ok first, .ok last, .ok static =>
      check ref s!"SVG terminal {name}: native last is the expected static drawing" (last == static)
      check ref s!"SVG terminal {name}: native last differs from the base drawing" (first != last)
    | .error err, _, _ | _, .error err, _ | _, _, .error err =>
      check ref s!"SVG terminal {name}: import failed: {err}" false
    match svgNativeDocument source (atEnd := true) with
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
