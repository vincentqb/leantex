module

public import LeanTex.Cli.DriverDiag
public import Tests.Images
public import Lean.Data.Json

public section

namespace Tests

open LeanTex.Core LeanTex.Cli

private def imageLoaderOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let source := Ir.picSrcPrefix ++ "0123456789abcdef0123456789abcdef"
  let own : Span := ⟨"included/pictures.tex",
    { line := 18, col := 7, origins := [⟨1, "drawpicture"⟩] }⟩
  let request : Span := ⟨"included/requests.tex",
    { line := 23, col := 6, origins := [⟨2, "placepicture"⟩] }⟩
  let locate (src : String) (fetch : Image.Fetch) (spans : Array (String × Span)) :=
    (Image.fulfilRequests #[({ src }, fetch)]).2.map (DriverDiag.atImageRequest spans src)
  let refusal := Diag.demote
    { DriverDiag.boundaryFailed "lualatex" "synthetic failure" source (some own) with
      refused := some "synthetic-picture", sites := 3 }
  let located := locate source (.refused refusal) #[(source, request)]
  t "image origins: located refusals keep their diagnostic and location"
    (located == #[{ refusal with subject := some source }])
  t "image origins: located refusals keep macro provenance"
    ((located[0]?.bind (·.span)).map (·.pos.origins) == some own.pos.origins)
  let supplied := locate source (.refused { refusal with span := none }) #[(source, request)]
  t "image origins: an unlocated refusal inherits the request without other changes"
    (supplied == #[{ refusal with span := some request, subject := some source }])
  t "image origins: inherited locations keep macro provenance"
    ((supplied[0]?.bind (·.span)).map (·.pos.origins) == some request.pos.origins)
  let unknown := locate "missing.png" (.missing "missing.png") #[("other.png", request)]
  t "image origins: an unrelated request never invents a location"
    (unknown.size == 1 && unknown.all fun d => d.kind == .W0601 && d.span.isNone)
  let unreadable := locate "missing.png" (.unreadable "is a directory") #[("missing.png", request)]
  t "image origins: an unreadable path carries its request location"
    (unreadable.size == 1 && unreadable.all fun d =>
      d.kind == .W0601 && d.span == some request && d.subject == some "missing.png")

/-- The built driver reports image losses at the first executed request,
including an included file. Dormant definitions and skipped branches are
not source sites, and a later repeated request does not replace the first.
Synthetic boundary tools make the W0378 path independent of installed TeX
or converters. Missing assets refuse self-contained HTML publication only
after these driver diagnostics have been emitted. -/
def imageOriginsChecks (ref : IO.Ref (List String)) : IO Unit := do
  imageLoaderOriginChecks ref
  let t := check ref
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let tools := dir / "bin"
    let chapter := dir / "chapters" / "images.tex"
    IO.FS.createDirAll tools
    IO.FS.createDirAll (dir / "chapters")
    IO.FS.writeFile (tools / "lualatex") "#!/bin/sh\n\
if [ \"$1\" = \"--version\" ]; then\n\
  printf '%s\\n' 'synthetic image origins tool'\n\
  exit 0\n\
fi\n\
exec /bin/cp \"$LEANTEX_IMAGE_ORIGINS_PDF\" pic.pdf\n"
    IO.FS.writeFile (tools / "pdftocairo") "#!/bin/sh\n\
printf '%s\\n' 'deliberate image origins conversion failure' >&2\n\
exit 19\n"
    let mode ← IO.Process.output { cmd := "chmod", args := #["+x",
      (tools / "lualatex").toString, (tools / "pdftocairo").toString] }
    unless mode.exitCode == 0 do throw <| IO.userError "could not prepare the image origins tools"
    IO.FS.writeBinFile (dir / "boundary.pdf") svgCanvasPdf
    IO.FS.writeFile (dir / "invalid.png") "not an image"
    IO.FS.writeBinFile (dir / "metadata.jpg")
      (jpegOf (iccApp2 1 1 [1, 2, 3] ++ exifApp1 6 true) 2 1 3)
    IO.FS.writeFile (dir / "root.tex") (String.intercalate "\n" [
      "\\documentclass{article}",
      "\\newcommand{\\dormantimage}{\\includegraphics[alt={Dormant}]{missing.png}}",
      "\\begin{document}",
      "\\iffalse",
      "\\includegraphics[alt={Skipped}]{missing.png}",
      "\\begin{tikzpicture}",
      "\\shade (0,0) rectangle (2,1);",
      "\\end{tikzpicture}",
      "\\fi",
      "\\input{chapters/images}",
      "\\includegraphics[alt={Later}]{missing.png}",
      "\\end{document}", ""])
    IO.FS.writeFile chapter (String.intercalate "\n" [
      "% Synthetic included image requests.", "",
      "\\includegraphics[alt={Missing}]{missing.png}",
      "\\includegraphics[alt={Invalid}]{invalid.png}",
      "\\includegraphics[alt={Profiled and oriented}]{metadata.jpg}",
      "\\begin{tikzpicture}",
      "\\shade (0,0) rectangle (2,1);",
      "\\end{tikzpicture}", ""])
    let result ← IO.Process.output {
      cmd := binary.toString
      args := #[(dir / "root.tex").toString, "-o", (dir / "out.html").toString, "--porcelain"]
      env := #[("PATH", some (tools.toString ++ ":" ++ path)),
        ("LEANTEX_FONT", some font.toString),
        ("LEANTEX_IMAGE_ORIGINS_PDF", some (dir / "boundary.pdf").toString),
        ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
    let records := (result.stdout.splitOn "\n").filterMap fun line => (Lean.Json.parse line).toOption
    t "image origins: the missing asset refuses self-contained publication"
      (result.exitCode == 1 && records.any fun record =>
        record.getObjValAs? String "code" == .ok "E0606")
    for (code, line) in [("W0601", 3), ("W0602", 4), ("W0603", 5), ("W0604", 5), ("W0378", 6)] do
      let named := records.filter fun record => record.getObjValAs? String "code" == .ok code
      t s!"image origins: {code} fires once through the driver" (named.length == 1)
      t s!"image origins: {code} names the executed included request"
        (named.length == 1 && named.all fun record =>
          record.getObjValAs? String "file" == .ok chapter.toString &&
          record.getObjValAs? Nat "line" == .ok line &&
          record.getObjValAs? Nat "col" == .ok 1)
      let command := if code == "W0378" then "\\begin" else "\\includegraphics"
      t s!"image origins: {code} quotes the written command through the driver"
        (named.length == 1 && named.all fun record =>
          record.getObjValAs? String "trigger" == .ok command)

end Tests
