module

public import LeanTex.Cli.ImageAssets
public import LeanTex.Core.SvgImport
public import LeanTex.Core.SvgPoster
public import LeanTex.Core.GfxSvg
public import Tests.Support

public section

namespace Tests

open LeanTex.Core

/-- The engine's own drawing of a source's pose as a standalone SVG, for an external rasterizer to
compare. -/
def svgNativeDocument (bytes : ByteArray) (atEnd : Bool := false) : Except String ByteArray := do
  let pose ← SvgPoster.pose bytes atEnd
  let fig := (Svg.importTree pose).fig
  pure (GfxSvg.document (fun _ _ => Html.text "") #[] fig).toUTF8

/-- A converted PDF poster stretches its own viewBox onto the first-frame canvas, as the native PDF
form does. -/
def svgPosterCanvasChecks (ref : IO.Ref (List String)) : IO Unit := do
  let poster ← LeanTex.Cli.ImageAssets.pdfSvg svgCanvasPdf .last
  match poster with
  | .error err => check ref s!"PDF poster conversion: {err}" false
  | .ok bytes =>
    IO.FS.withTempDir fun dir => do
      let file := dir / "poster.svg"
      IO.FS.writeBinFile file bytes
      let parsed ← IO.Process.output { cmd := "xmllint", args := #["--nonet", "--nocatalogs",
        "--xpath", "boolean(/*[local-name()='svg' and @viewBox='0 0 60 120' and @preserveAspectRatio='none'])",
        file.toString] }
      check ref "the converted poster stretches the selected page to the canvas"
        (parsed.exitCode == 0 && parsed.stdout.trimAscii.toString == "true")

/-- Companion lookup at the driver's one-read capture site: accepted companions publish
byte-for-byte, unsupported or absent ones keep the converted poster. -/
def svgCompanionDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let moving := svgDocument
    "<rect width=\"20\" height=\"20\" fill=\"red\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>"
  let lower := svgDocument
    "<rect width=\"20\" height=\"20\" fill=\"blue\"><animate attributeName=\"opacity\" values=\"1;0;1\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>"
  let unsupported := svgDocument "<image href=\"missing.png\" width=\"20\" height=\"20\"/>"
  IO.FS.withTempDir fun dir => do
    for (name, lowerBytes, upperBytes, expected) in [
        ("uppercase", none, some moving, some moving),
        ("both", some lower, some moving, some lower),
        ("unsafe", none, some unsupported, none),
        ("absent", none, none, none)] do
      let input := dir / name
      let output := input / "out"
      IO.FS.createDirAll output
      IO.FS.writeBinFile (input / "sequence.PDF") svgCanvasPdf
      if let some bytes := lowerBytes then IO.FS.writeBinFile (input / "sequence.svg") bytes
      if let some bytes := upperBytes then IO.FS.writeBinFile (input / "sequence.SVG") bytes
      IO.FS.writeFile (input / "figure.tex")
        "\\documentclass{article}\n\\begin{document}\n\
        \\animategraphics[poster=last,alt={Moving square}]{10}{sequence.PDF}{}{}\n\
        \\end{document}\n"
      let run ← IO.Process.output {
        cmd := binary.toString, cwd := some input
        args := #["figure.tex", "-o", (output / "figure.html").toString]
        env := #[("LEANTEX_FONT", some font.toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
      check ref s!"SVG companion {name}: the driver builds" (run.exitCode == 0)
      let html ← IO.FS.readFile (output / "figure.html")
      let (primarySrc, primary) ← svgPublishedAsset html "img" "src"
      let published ← output.readDir
      check ref s!"SVG companion {name}: one HTML file contains all rendering resources"
        (published.map (·.fileName) == #["figure.html"])
      match expected with
      | some bytes =>
        let (posterSrc, poster) ← svgPublishedAsset html "source" "srcset"
        check ref s!"SVG companion {name}: original animation bytes publish"
          (primary == bytes && !poster.isEmpty)
        check ref s!"SVG companion {name}: the static media fallback is reachable"
          (primarySrc != posterSrc)
      | none =>
        check ref s!"SVG companion {name}: the selected PDF still supplies a static face"
          (!primary.isEmpty && primary != unsupported &&
            (html.splitOn "<img ").length == 2 && (html.splitOn "<source ").length == 1)
      check ref s!"SVG companion {name}: source bytes remain unchanged"
        ((← IO.FS.readBinFile (input / "sequence.PDF")) == svgCanvasPdf &&
          (← if let some bytes := upperBytes then
            pure ((← IO.FS.readBinFile (input / "sequence.SVG")) == bytes)
          else pure true))

/-- A moving figure's still face never asks the converter. -/
def svgFailureDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let tools := dir / "bin"
    IO.FS.createDirAll tools
    let wrapper := tools / "rsvg-convert"
    let log := dir / "calls.log"
    IO.FS.writeFile wrapper s!"#!/bin/sh\n\
echo \"$*\" >> '{log}'\n\
echo 'deliberate conversion failure' >&2\n\
exit 19\n"
    let mode ← IO.Process.output { cmd := "chmod", args := #["+x", wrapper.toString] }
    unless mode.exitCode == 0 do throw <| IO.userError "could not prepare the converter probe"
    let moving := svgDocument
      "<rect width=\"20\" height=\"20\" fill=\"red\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>"
    IO.FS.writeBinFile (dir / "moving.svg") moving
    IO.FS.writeFile (dir / "figure.tex")
      "\\documentclass{article}\n\\begin{document}\n\
\\includegraphics[alt={A moving square}]{moving.svg}\n\\end{document}\n"
    let output := dir / "out"
    let run ← IO.Process.output {
      cmd := binary.toString, cwd := some dir
      args := #["figure.tex", "-o", (output / "figure.html").toString]
      env := #[("PATH", some (tools.toString ++ ":" ++ path)),
        ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
    check ref "moving figure driver: the page builds" (run.exitCode == 0)
    let html ← try IO.FS.readFile (output / "figure.html")
      catch err => throw <| IO.userError s!"{err}\n{run.stdout}{run.stderr}"
    let out := run.stdout ++ run.stderr
    check ref "moving figure driver: no loss is reported" (!hasStr out "[W0602]" && !hasStr out "[W0609]")
    let called ← if ← log.pathExists then pure !(← IO.FS.readFile log).isEmpty else pure false
    check ref "moving figure driver: the converter is never called" !called
    let (_, primary) ← svgPublishedAsset html "img" "src"
    let (_, poster) ← svgPublishedAsset html "source" "srcset"
    check ref "moving figure driver: the browser receives the authored animation" (primary == moving)
    check ref "moving figure driver: the still face is a static SVG the native judge admits"
      (match Svg.judge poster with
        | .ok t => (SvgPoster.tracksOne #[] t).isEmpty && !bytesContain poster "<animate"
        | .error _ => false)

/-- A source whose outside resources a drawing would discard is refused by the native judge before
anything draws it. -/
def svgValidationConverterChecks (ref : IO.Ref (List String)) : IO Unit := do
  let rect := "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  for (name, body) in [
      ("relative image", rect ++ "<image href=\"missing.png\" width=\"20\" height=\"20\"/>"),
      ("relative paint", "<style>rect { fill: url(missing.svg#paint) red }</style>" ++ rect)] do
    check ref s!"SVG route refuses {name} before losing its ink"
      (svgBoundaryError (SvgPoster.pose (svgDocument body) false))

/-- An exporter's external doctype is an identifier, not a request to load its DTD, and the figure
still draws in both artifacts. -/
def svgDoctypeDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let drawing := String.fromUTF8! <| svgDocument
    "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  IO.FS.withTempDir fun dir => do
    for (name, prolog) in [
        ("public", "<!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1//EN\" \
          \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd\">"),
        ("missing", "<!DOCTYPE svg SYSTEM \"missing.dtd\">")] do
      let input := dir / name
      let output := input / "out"
      IO.FS.createDirAll output
      let bytes := (prolog ++ drawing).toUTF8
      IO.FS.writeBinFile (input / "figure.svg") bytes
      IO.FS.writeFile (input / "figure.tex")
        "\\documentclass{article}\n\\begin{document}\n\
        \\includegraphics[width=20pt,alt={Red square}]{figure.svg}\n\
        \\end{document}\n"
      for extension in ["html", "pdf"] do
        let run ← IO.Process.output {
          cmd := binary.toString, cwd := some input
          args := #["figure.tex", "-o", (output / ("figure." ++ extension)).toString]
          env := #[("LEANTEX_FONT", some font.toString),
            ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
        let log := run.stdout ++ run.stderr
        check ref s!"SVG doctype {name}: {extension} keeps the figure"
          (run.exitCode == 0 && (log.splitOn "W0602").length == 1)
      let html ← IO.FS.readFile (output / "figure.html")
      let (_, published) ← svgPublishedAsset html "img" "src"
      check ref s!"SVG doctype {name}: original browser source publishes"
        (published == bytes)
      check ref s!"SVG doctype {name}: the page links its visible figure"
        ((html.splitOn "<img ").length == 2 &&
          (html.splitOn "data-image-src=").length == 1)
      let raster ← IO.Process.output {
        cmd := "pdftoppm", args := #["-r", "72", "-singlefile", "-f", "1", "-l", "1",
          (output / "figure.pdf").toString, (output / "page").toString] }
      check ref s!"SVG doctype {name}: the PDF renders" (raster.exitCode == 0)
      if raster.exitCode == 0 then
        let pixels ← IO.FS.readBinFile (output / "page.ppm")
        let mut red := 0
        for i in [:pixels.size - 2] do
          if pixels[i]! == 255 && pixels[i + 1]! == 0 && pixels[i + 2]! == 0 then
            red := red + 1
        -- A 20pt square at 72dpi contains 400 pixels; allow edge antialiasing.
        check ref s!"SVG doctype {name}: the shipped PDF paints the red square"
          (red > 200)
      check ref s!"SVG doctype {name}: captured source remains unchanged"
        ((← IO.FS.readBinFile (input / "figure.svg")) == bytes)

/-- An external identifier supplies no entity values or paint defaults, compared by rendered
pixels. -/
def svgDtdDependencyChecks (ref : IO.Ref (List String)) : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let dtd := dir / "outside.dtd"
    let prolog := s!"<!DOCTYPE svg SYSTEM \"{dtd}\">"
    IO.FS.writeFile dtd "<!ENTITY outside 'green'>"
    for id in [prolog, "<!DOCTYPE svg SYSTEM \"missing.dtd\">"] do
      for body in ["<rect width=\"20\" height=\"20\" fill=\"&outside;\"/>",
          "<text>&outside;</text>"] do
        let result := Svg.judge (id ++ String.fromUTF8! (svgDocument body)).toUTF8
        check ref "SVG named entities never silently lose their values"
          (match result with
            | .error r => hasStr r.message "SVG resource boundary"
            | .ok _ => false)
    let mut rasters : Array ByteArray := #[]
    for (name, declaration, fill) in [
        ("plain", "", ""), ("default-green", prolog, ""),
        ("default-blue", prolog, ""), ("black", "", " fill=\"black\""),
        ("green", "", " fill=\"green\"")] do
      let color := if name == "default-blue" then "blue" else "green"
      IO.FS.writeFile dtd s!"<!ATTLIST rect fill CDATA '{color}'>"
      let source := (declaration ++ String.fromUTF8!
        (svgDocument s!"<rect width=\"20\" height=\"20\"{fill}/>")).toUTF8
      match svgNativeDocument source with
      | .error err => check ref s!"SVG default comparison {name}: {err}" false
      | .ok bytes =>
        let input := dir / (name ++ ".svg")
        let output := dir / (name ++ ".png")
        IO.FS.writeBinFile input bytes
        let run ← IO.Process.output {
          cmd := "rsvg-convert"
          args := #["--format=png", "--output", output.toString, input.toString] }
        check ref s!"SVG default comparison {name} renders" (run.exitCode == 0)
        if run.exitCode == 0 then rasters := rasters.push (← IO.FS.readBinFile output)
    check ref "SVG external defaults never change the drawn pixels"
      (rasters.size == 5 && !rasters[0]!.isEmpty &&
        (rasters.toList.take 4).all (· == rasters[0]!) && rasters[4]! != rasters[0]!)

/-- The supported subset and its counterexamples through the native judge; needs librsvg, xmllint
and Poppler on the host. -/
def svgValidationChecks (ref : IO.Ref (List String)) : IO Unit := do
  svgPosterCanvasChecks ref
  svgCompanionDriverChecks ref
  svgValidationConverterChecks ref
  svgDoctypeDriverChecks ref
  svgDtdDependencyChecks ref
  let moving := "<rect width=\"20\" height=\"20\" fill=\"red\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>"
  for (name, body) in svgBoundaryAdmitted do
    check ref s!"SVG validation admits {name}" (Svg.judge (svgDocument body)).toBool
  for (name, body) in svgBoundaryRefused do
    check ref s!"SVG resource boundary refuses {name}"
      (match Svg.judge (svgDocument (svgRedSquare ++ body)) with
        | .error r => hasStr r.message "SVG resource boundary"
        | .ok _ => false)
  for (name, source) in svgBoundaryMalformed (String.fromUTF8! (svgDocument svgRedSquare)) do
    check ref s!"SVG validation refuses {name} source" (!(Svg.judge source.toUTF8).toBool)
  let poster ← LeanTex.Cli.ImageAssets.canonicalPoster (svgDocument moving)
  match poster with
  | .error err => check ref s!"SVG static poster conversion: {err}" false
  | .ok bytes =>
    IO.FS.withTempDir fun dir => do
      let file := dir / "poster.svg"
      IO.FS.writeBinFile file bytes
      let parsed ← IO.Process.output { cmd := "xmllint", args := #["--nonet", "--nocatalogs",
        "--xpath", "boolean(/*[local-name()='svg']) and not(//*[local-name()='animate' or local-name()='set' or local-name()='animateTransform' or local-name()='animateMotion'])", file.toString] }
      check ref "SVG poster is parsed static SVG"
        (parsed.exitCode == 0 && parsed.stdout.trimAscii.toString == "true")
  let emptyPoster ← LeanTex.Cli.ImageAssets.canonicalPoster ByteArray.empty
  check ref "SVG poster refuses empty source" (!emptyPoster.isOk)
  svgFailureDriverChecks ref

end Tests
