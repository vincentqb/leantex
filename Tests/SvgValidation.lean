import LeanTex.Cli.ImageAssets
import Tests.Support

namespace Tests

/-- Check the actual converter output, not the outer image box: a PDF
poster must stretch its own viewBox when placed on the first-frame canvas,
as the native PDF form does. Browser paint is the companion external oracle. -/
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
      check ref "converted PDF poster stretches the selected page to the animation canvas"
        (parsed.exitCode == 0 && parsed.stdout.trimAscii.toString == "true")

/-- Exercise extension lookup at the driver's one-read capture site.
Accepted companions publish byte-for-byte; an unsafe or absent companion
keeps the converted PDF poster. Lowercase retains precedence when both exist. -/
def svgCompanionDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "tests/corpus/fonts/OpenSans-Regular.ttf"
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
      let (primarySrc, primary) ← svgPublishedAsset html output "img" "src"
      let published ← output.readDir
      check ref s!"SVG companion {name}: one HTML file contains all rendering resources"
        (published.map (·.fileName) == #["figure.html"])
      match expected with
      | some bytes =>
        let (posterSrc, poster) ← svgPublishedAsset html output "source" "srcset"
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

/-- Exercise the driver's second conversion after the native SVG decode
succeeds. A converter failure must remove the moving browser asset, ship
a named placeholder and retain the reason in its one diagnostic. This
oracle needs the built CLI and installed converters, not a mock store. -/
def svgFailureDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let found ← IO.Process.output { cmd := "sh", args := #["-c", "command -v rsvg-convert"] }
  if found.exitCode != 0 then throw <| IO.userError "rsvg-convert is required"
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let tools := dir / "bin"
    IO.FS.createDirAll tools
    let wrapper := tools / "rsvg-convert"
    IO.FS.writeFile wrapper "#!/bin/sh\n\
for arg do\n\
  if [ \"$arg\" = \"--format=svg\" ]; then\n\
    echo 'deliberate poster conversion failure' >&2\n\
    exit 19\n\
  fi\n\
done\n\
exec \"$LEANTEX_SVG_CONVERTER\" \"$@\"\n"
    let mode ← IO.Process.output { cmd := "chmod", args := #["+x", wrapper.toString] }
    unless mode.exitCode == 0 do throw <| IO.userError "could not prepare the converter probe"
    IO.FS.writeBinFile (dir / "moving.svg") (svgDocument
      "<rect width=\"20\" height=\"20\" fill=\"red\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>")
    IO.FS.writeFile (dir / "figure.tex")
      "\\documentclass{article}\n\\begin{document}\n\
\\includegraphics[alt={A moving square}]{moving.svg}\n\\end{document}\n"
    let output := dir / "out"
    let run ← IO.Process.output {
      cmd := binary.toString, cwd := some dir
      args := #["figure.tex", "-o", (output / "figure.html").toString]
      env := #[("PATH", some (tools.toString ++ ":" ++ path)),
        ("LEANTEX_SVG_CONVERTER", some found.stdout.trimAscii.toString),
        ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
    check ref "failed browser poster leaves a buildable labelled fallback" (run.exitCode == 0)
    let html ← try IO.FS.readFile (output / "figure.html")
      catch err => throw <| IO.userError s!"{err}\n{run.stdout}{run.stderr}"
    let log := run.stdout ++ run.stderr
    check ref "driver records the failed poster conversion once"
      ((log.splitOn "warning[W0605]").length == 2 &&
        (log.splitOn "deliberate poster conversion failure").length == 2)
    check ref "driver emits a named placeholder without a moving image URL"
      ((html.splitOn "data-image-src=\"moving.svg\"").length == 2 &&
        (html.splitOn "aria-label=\"A moving square\"").length == 2 &&
        (html.splitOn "<img ").length == 1)
    let assets := output / "figure.assets"
    let published ← if ← assets.pathExists then assets.readDir else pure #[]
    check ref "driver does not publish the moving bytes after poster failure"
      published.isEmpty

/-- External oracle (xmllint/librsvg), separate from hermetic tests. A
converter exit of zero must not admit a source whose outside resources it
silently discarded. All inputs are synthetic and all references missing. -/
def svgValidationConverterChecks (ref : IO.Ref (List String)) : IO Unit := do
  let rect := "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  for (name, body) in [
      ("relative image", rect ++ "<image href=\"missing.png\" width=\"20\" height=\"20\"/>"),
      ("relative paint", "<style>rect { fill: url(missing.svg#paint) red }</style>" ++ rect)] do
    let result ← LeanTex.Cli.ImageAssets.svgPlan .default (svgDocument body)
    check ref s!"SVG conversion refuses {name} before losing its ink" (svgBoundaryError result)

/-- An exporter's external doctype is an identifier, not a request to
load its DTD. Adding it must retain the drawn figure in both artifacts.
The actual driver and installed converters witness this boundary. -/
def svgDoctypeDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "tests/corpus/fonts/OpenSans-Regular.ttf"
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
          (run.exitCode == 0 && (log.splitOn "W0602").length == 1 &&
            (log.splitOn "W0605").length == 1)
      let html ← IO.FS.readFile (output / "figure.html")
      let (_, published) ← svgPublishedAsset html output "img" "src"
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

/-- An external identifier must not supply missing entity values or paint
defaults. Compare rendered pixels while the owned DTD's defaults change. -/
def svgDtdDependencyChecks (ref : IO.Ref (List String)) : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let dtd := dir / "outside.dtd"
    let prolog := s!"<!DOCTYPE svg SYSTEM \"{dtd}\">"
    IO.FS.writeFile dtd "<!ENTITY outside 'green'>"
    for id in [prolog, "<!DOCTYPE svg SYSTEM \"missing.dtd\">"] do
      for body in ["<rect width=\"20\" height=\"20\" fill=\"&outside;\"/>",
          "<text>&outside;</text>"] do
        let result ← LeanTex.Cli.ImageAssets.validateSvg
          (id ++ String.fromUTF8! (svgDocument body)).toUTF8
        check ref "SVG named entities never silently lose their values" (svgBoundaryError result)
    let mut rasters : Array ByteArray := #[]
    for (name, declaration, fill) in [
        ("plain", "", ""), ("default-green", prolog, ""),
        ("default-blue", prolog, ""), ("black", "", " fill=\"black\""),
        ("green", "", " fill=\"green\"")] do
      let color := if name == "default-blue" then "blue" else "green"
      IO.FS.writeFile dtd s!"<!ATTLIST rect fill CDATA '{color}'>"
      let source := (declaration ++ String.fromUTF8!
        (svgDocument s!"<rect width=\"20\" height=\"20\"{fill}/>")).toUTF8
      match ← LeanTex.Cli.ImageAssets.svgPoster source with
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

/-- The narrow supported subset and its encoded counterexamples, through
actual XML parsing and conversion. This oracle needs xmllint and librsvg;
it must be invoked explicitly on a host providing those tools. -/
def svgValidationChecks (ref : IO.Ref (List String)) : IO Unit := do
  svgPosterCanvasChecks ref
  svgCompanionDriverChecks ref
  svgValidationConverterChecks ref
  svgDoctypeDriverChecks ref
  svgDtdDependencyChecks ref
  let rect := "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  let moving := "<rect width=\"20\" height=\"20\" fill=\"red\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>"
  for (name, body) in [
      ("shape", rect),
      ("SMIL", moving),
      ("fragment", "<defs><path id=\"p\" d=\"M0 0h20v20z\"/></defs><use href=\"#p\"/>"),
      ("fragment paint", "<defs><linearGradient id=\"paint\"><stop stop-color=\"red\"/></linearGradient></defs><rect width=\"20\" height=\"20\" fill=\"url(#paint)\"/>"),
      ("aliased fragment", "<defs><path id=\"p\" d=\"M0 0h20v20z\"/></defs><use xmlns:l=\"http://www.w3.org/1999/xlink\" l:href=\"&#35;p\"/>"),
      ("predefined and numeric references", "<title>&quot;&apos;&amp;&lt;&gt;&#65;&#x42;</title><rect aria-label=\"&quot;&apos;&amp;&lt;&gt;&#65;&#x42;\" width=\"20\" height=\"20\" fill=\"red\"/>"),
      ("plain style CDATA", "<style><![CDATA[rect { fill: red }]]></style>" ++ rect),
      ("XML comments and prose", "<!-- <image href=\"outside.png\"/> --><title>url(outside.png)</title>" ++ rect)] do
    let result ← LeanTex.Cli.ImageAssets.validateSvg (svgDocument body)
    check ref s!"SVG validation admits {name}" result.isOk
  for (name, body) in [
      ("network image", "<image href=\"https://example.invalid/tile.png\"/>"),
      ("protocol-relative image", "<image href=\"//example.invalid/tile.png\"/>"),
      ("absolute image", "<image href=\"/tile.png\"/>"),
      ("empty href", "<image href=\"\"/>"),
      ("character-encoded image", "<image href=\"&#x74;&#105;le.png\"/>"),
      ("aliased image", "<image xmlns:l=\"http://www.w3.org/1999/xlink\" l:href=\"tile.png\"/>"),
      ("base URI", "<g xml:base=\"https://example.invalid/\"><use href=\"#p\"/></g>"),
      ("paint-server fallback", "<defs><linearGradient id=\"paint\"/></defs><rect fill=\"url(#paint) red\"/>"),
      ("CSS escaped URL", "<style>rect { fill: u\\72l(tile.svg#p) }</style>"),
      ("CSS import", "<style>@import 'outside.css';</style>"),
      ("CSS string image", "<style>rect { fill: image-set('tile.png' 1x) }</style>"),
      ("split style text", "<style>u<!--comment--><![CDATA[rl(tile.png)]]></style>"),
      ("animated href", "<image><set attributeName=\"l:href\" to=\"tile.png\"/></image>"),
      ("animated style", "<rect><set attributeName=\"style\" to=\"fill:red\"/></rect>"),
      ("embedded SVG", "<image href=\"data:image/svg+xml,%3Csvg/%3E\"/>"),
      ("foreign object", "<foreignObject><img src=\"tile.png\"/></foreignObject>"),
      ("script", "<script>fetch('tile.png')</script>"),
      ("event handler", "<rect onload=\"fetch('tile.png')\"/>")] do
    let result ← LeanTex.Cli.ImageAssets.validateSvg (svgDocument (rect ++ body))
    check ref s!"SVG resource boundary refuses {name}" (svgBoundaryError result)
  for (name, source) in [
      ("empty", ""), ("whitespace", " \n\t "), ("foreign root", "<html/>"),
      ("truncated", "<svg href=\""), ("mismatched", "<svg><g></svg>"),
      ("extra root", "<svg/><svg/>"), ("unclosed", "<svg>"),
      ("unquoted attribute", "<svg width=20/>"),
      ("DTD attribute", "<!DOCTYPE svg [<!ATTLIST rect fill CDATA 'green'>]>" ++
        String.fromUTF8! (svgDocument rect)),
      ("DTD element", "<!DOCTYPE svg [<!ELEMENT svg ANY>]>" ++
        String.fromUTF8! (svgDocument rect)),
      ("entity declaration", "<!DOCTYPE svg [<!ENTITY x 'tile.png'>]>" ++
        String.fromUTF8! (svgDocument (rect ++ "<image href=\"&x;\"/>"))),
      ("stylesheet PI", "<?xml-stylesheet href=\"outside.css\"?>" ++ String.fromUTF8! (svgDocument rect))] do
    let result ← LeanTex.Cli.ImageAssets.validateSvg source.toUTF8
    check ref s!"SVG validation refuses {name} source" (!result.isOk)
  let poster ← LeanTex.Cli.ImageAssets.svgPoster (svgDocument moving)
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
  let emptyPoster ← LeanTex.Cli.ImageAssets.svgPoster ByteArray.empty
  check ref "SVG poster refuses empty source" (!emptyPoster.isOk)
  svgFailureDriverChecks ref

end Tests
