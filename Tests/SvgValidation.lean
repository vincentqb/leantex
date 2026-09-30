import LeanTex.Cli.ImageAssets

namespace Tests

private def svgCheck (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit :=
  unless ok do ref.modify (name :: ·)

private def svgDocument (body : String) : ByteArray :=
  ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"20\" height=\"20\">" ++
    body ++ "</svg>").toUTF8

private def boundaryError (result : Except String α) : Bool :=
  match result with
  | .error err => (err.splitOn "SVG resource boundary").length > 1
  | .ok _ => false

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
    svgCheck ref "failed browser poster leaves a buildable labelled fallback" (run.exitCode == 0)
    let html ← try IO.FS.readFile (output / "figure.html")
      catch err => throw <| IO.userError s!"{err}\n{run.stdout}{run.stderr}"
    let log := run.stdout ++ run.stderr
    svgCheck ref "driver records the failed poster conversion once"
      ((log.splitOn "warning[W0605]").length == 2 &&
        (log.splitOn "deliberate poster conversion failure").length == 2)
    svgCheck ref "driver emits a named placeholder without a moving image URL"
      ((html.splitOn "data-image-src=\"moving.svg\"").length == 2 &&
        (html.splitOn "aria-label=\"A moving square\"").length == 2 &&
        (html.splitOn "<img ").length == 1)
    svgCheck ref "driver does not publish the moving bytes after poster failure"
      (!(← (output / "figure.assets" / "i0-moving.svg").pathExists))

/-- External oracle (xmllint/librsvg), separate from hermetic tests. A
converter exit of zero must not admit a source whose outside resources it
silently discarded. All inputs are synthetic and all references missing. -/
def svgValidationConverterChecks (ref : IO.Ref (List String)) : IO Unit := do
  let rect := "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  for (name, body) in [
      ("relative image", rect ++ "<image href=\"missing.png\" width=\"20\" height=\"20\"/>"),
      ("relative paint", "<style>rect { fill: url(missing.svg#paint) red }</style>" ++ rect)] do
    let result ← LeanTex.Cli.ImageAssets.svgPlan .default (svgDocument body)
    svgCheck ref s!"SVG conversion refuses {name} before losing its ink" (boundaryError result)

/-- The narrow supported subset and its encoded counterexamples, through
actual XML parsing and conversion. This oracle needs xmllint and librsvg;
it must be invoked explicitly on a host providing those tools. -/
def svgValidationChecks (ref : IO.Ref (List String)) : IO Unit := do
  svgValidationConverterChecks ref
  let rect := "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  let moving := "<rect width=\"20\" height=\"20\" fill=\"red\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>"
  for (name, body) in [
      ("shape", rect),
      ("SMIL", moving),
      ("fragment", "<defs><path id=\"p\" d=\"M0 0h20v20z\"/></defs><use href=\"#p\"/>"),
      ("fragment paint", "<defs><linearGradient id=\"paint\"><stop stop-color=\"red\"/></linearGradient></defs><rect width=\"20\" height=\"20\" fill=\"url(#paint)\"/>"),
      ("aliased fragment", "<defs><path id=\"p\" d=\"M0 0h20v20z\"/></defs><use xmlns:l=\"http://www.w3.org/1999/xlink\" l:href=\"&#35;p\"/>"),
      ("plain style CDATA", "<style><![CDATA[rect { fill: red }]]></style>" ++ rect),
      ("XML comments and prose", "<!-- <image href=\"outside.png\"/> --><title>url(outside.png)</title>" ++ rect)] do
    let result ← LeanTex.Cli.ImageAssets.validateSvg (svgDocument body)
    svgCheck ref s!"SVG validation admits {name}" result.isOk
  for (name, body) in [
      ("network image", "<image href=\"https://example.invalid/tile.png\"/>"),
      ("text element", "<text x=\"5\" y=\"15\">hi</text>"),
      ("tspan in text", "<text x=\"5\" y=\"15\"><tspan>hi</tspan></text>"),
      ("font-family attribute", "<g font-family=\"serif\"><rect width=\"2\" height=\"2\"/></g>"),
      ("svg font element", "<font id=\"f\"><glyph unicode=\"a\"/></font>"),
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
    svgCheck ref s!"SVG resource boundary refuses {name}" (boundaryError result)
  for (name, source) in [
      ("empty", ""), ("whitespace", " \n\t "), ("foreign root", "<html/>"),
      ("truncated", "<svg href=\""), ("mismatched", "<svg><g></svg>"),
      ("extra root", "<svg/><svg/>"), ("unclosed", "<svg>"),
      ("unquoted attribute", "<svg width=20/>"),
      ("DTD", "<!DOCTYPE svg SYSTEM \"missing.dtd\">" ++ String.fromUTF8! (svgDocument rect)),
      ("entity declaration", "<!DOCTYPE svg [<!ENTITY x 'tile.png'>]>" ++
        String.fromUTF8! (svgDocument (rect ++ "<image href=\"&x;\"/>"))),
      ("stylesheet PI", "<?xml-stylesheet href=\"outside.css\"?>" ++ String.fromUTF8! (svgDocument rect))] do
    let result ← LeanTex.Cli.ImageAssets.validateSvg source.toUTF8
    svgCheck ref s!"SVG validation refuses {name} source" (!result.isOk)
  let poster ← LeanTex.Cli.ImageAssets.svgPoster (svgDocument moving)
  match poster with
  | .error err => svgCheck ref s!"SVG static poster conversion: {err}" false
  | .ok bytes =>
    IO.FS.withTempDir fun dir => do
      let file := dir / "poster.svg"
      IO.FS.writeBinFile file bytes
      let parsed ← IO.Process.output { cmd := "xmllint", args := #["--nonet", "--nocatalogs",
        "--xpath", "boolean(/*[local-name()='svg']) and not(//*[local-name()='animate' or local-name()='set' or local-name()='animateTransform' or local-name()='animateMotion'])", file.toString] }
      svgCheck ref "SVG poster is parsed static SVG"
        (parsed.exitCode == 0 && parsed.stdout.trimAscii.toString == "true")
  let emptyPoster ← LeanTex.Cli.ImageAssets.svgPoster ByteArray.empty
  svgCheck ref "SVG poster refuses empty source" (!emptyPoster.isOk)
  svgFailureDriverChecks ref

end Tests
