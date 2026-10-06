/-
External title-page placement differential. Run from the repository root:

  lake build leantex
  lake env lean --run scripts/title-placement-diff.lean
  lake env lean --run scripts/title-placement-diff.lean --selftest

This is a report and deeper oracle, never a `lake test` gate. It writes only
under `.lake/title-placement-diff/`, builds two invented beamer templates
with LuaLaTeX and leantex, and asks independent PDF tools what each artifact
states: Ghostscript txtwrite at 1440 dpi for baselines, Poppler bbox for word
boxes, and Poppler raster plus ImageMagick for the page ground.

The placement bound is 0.25 PDF point. Ghostscript's grid contributes at
most 0.05 pt across two rounded readings; LuaTeX converts a 33 TeX-point
baseline skip to PDF points, contributing 0.123 pt against leantex's declared
PDF-point unit. The next 0.05-pt grid value, 0.20 pt, leaves less than one
coordinate quantum for both PDF spellings; 0.25 pt is therefore the smallest
honest bound on this extractor. It is a placement bound, not a glyph-box
identity claim: Poppler's vertical word boxes read each writer's font
descriptor differently and are printed as evidence rather than gated.
-/
import LeanTex

open LeanTex.Core

structure GhostLine where
  text : String
  x20 : Int
  y20 : Int
  deriving Repr, BEq, Inhabited

structure WordBox where
  text : String
  x0u : Int
  y0u : Int
  x1u : Int
  y1u : Int
  deriving Repr, BEq, Inhabited

def lineNames : List String :=
  ["TITLEALPHA", "SUBTITLEBETA", "AUTHORGAMMA", "INSTITUTEDELTA"]

def attrOf (line attr : String) : Option String := do
  let after ← (line.splitOn (attr ++ "=\""))[1]?
  (after.splitOn "\"").head?

def fixedMicro (s : String) : Option Int := do
  let (mantissa, scale) ← Decl.parseDecimal s
  return mantissa * 1000000 / (scale : Int)

def wordText (line : String) : String :=
  let after := String.intercalate ">" ((line.splitOn ">").drop 1)
  let body := (after.splitOn "</word>").headD ""
  ((body.replace "&amp;" "&").replace "&lt;" "<").replace "&gt;" ">"

def parseGhost (xml : String) : Array GhostLine := Id.run do
  let mut out : Array GhostLine := #[]
  let mut point : Option (Int × Int) := none
  let mut text := ""
  for raw in xml.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "<span " then
      let coords := ((attrOf line "bbox").getD "").splitOn " "
      point := match coords[0]?.bind String.toInt?, coords[1]?.bind String.toInt? with
        | some x, some y => some (x, y)
        | _, _ => none
      text := ""
    else if line.startsWith "<char " then
      if let some c := attrOf line "c" then text := text ++ c
    else if line == "</span>" then
      if let some (x, y) := point then out := out.push { text := text, x20 := x, y20 := y }
      point := none
      text := ""
  return out

def parsePoppler (xml : String) : Array WordBox := Id.run do
  let mut out : Array WordBox := #[]
  for raw in xml.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "<word " then
      match (attrOf line "xMin").bind fixedMicro, (attrOf line "yMin").bind fixedMicro,
          (attrOf line "xMax").bind fixedMicro, (attrOf line "yMax").bind fixedMicro with
      | some x0, some y0, some x1, some y1 =>
        out := out.push { text := wordText line, x0u := x0, y0u := y0, x1u := x1, y1u := y1 }
      | _, _, _, _ => pure ()
  return out

def runTool (cmd : String) (args : Array String) (cwd : System.FilePath) : IO IO.Process.Output := do
  let out ← IO.Process.output { cmd := cmd, args := args, cwd := cwd }
  if out.exitCode != 0 then
    throw (IO.userError s!"{cmd} exited {out.exitCode}: {(out.stdout ++ out.stderr).trimAscii.toString}")
  return out

def firstLine (s : String) : String := (s.splitOn "\n").headD "unknown"

def version (cmd : String) (args : Array String) (cwd : System.FilePath) : IO String := do
  try
    let out ← IO.Process.output { cmd := cmd, args := args, cwd := cwd }
    if out.exitCode == 0 then return firstLine (out.stdout ++ out.stderr)
    return "unavailable"
  catch _ => return "unavailable"

def common (fontDir : String) : String :=
  "\\documentclass[aspectratio=169]{beamer}\n" ++
  "\\usepackage{tikz}\n\\usepackage{fontspec}\n" ++
  s!"\\setsansfont\{OpenSans-Regular.ttf}[Path={fontDir}/,BoldFont=OpenSans-Bold.ttf," ++
  "ItalicFont=OpenSans-Italic.ttf,BoldItalicFont=OpenSans-BoldItalic.ttf]\n" ++
  "\\setbeamertemplate{navigation symbols}{}\n" ++
  "\\definecolor{probeGround}{HTML}{253546}\n" ++
  "\\definecolor{probeInk}{HTML}{F5EFE3}\n" ++
  "\\definecolor{probeAccent}{HTML}{89D7B1}\n" ++
  "\\setbeamerfont{probe title}{size*={28pt}{33pt},series=\\bfseries}\n" ++
  "\\setbeamerfont{probe subtitle}{size*={15pt}{19pt}}\n" ++
  "\\setbeamerfont{probe author}{size*={13pt}{17pt}}\n" ++
  "\\setbeamerfont{probe institute}{size*={10pt}{13pt}}\n"

def metadata : String :=
  "\\title{TITLEALPHA}\n\\subtitle{SUBTITLEBETA}\n" ++
  "\\author{AUTHORGAMMA}\n\\institute{INSTITUTEDELTA}\n" ++
  "\\begin{document}\n\\begin{frame}[plain]\\titlepage\\end{frame}\n\\end{document}\n"

def compoundTemplate (fontDir : String) : String :=
  common fontDir ++
  "\\makeatletter\n\\setbeamertemplate{title page}{%\n" ++
  "\\begin{tikzpicture}[remember picture,overlay]\n" ++
  "\\fill[probeGround] (current page.south west) rectangle (current page.north east);\n" ++
  "\\node[anchor=west,align=left,inner sep=2pt,text width=0.72\\paperwidth,text=probeInk] " ++
  "at ([xshift=18mm,yshift=7mm]current page.west) " ++
  "{{\\raggedright\\usebeamerfont{probe title}\\inserttitle\\par}%\n" ++
  "\\ifx\\insertsubtitle\\@empty\\else\\vskip3pt" ++
  "{\\raggedright\\usebeamerfont{probe subtitle}\\color{probeAccent}\\insertsubtitle\\par}\\fi};\n" ++
  "\\node[anchor=south west,align=left,inner sep=2pt,text width=0.46\\paperwidth,text=probeAccent] " ++
  "at ([xshift=18mm,yshift=12mm]current page.south west) " ++
  "{{\\raggedright\\usebeamerfont{probe author}\\insertauthor\\par}%\n" ++
  "\\ifx\\insertinstitute\\@empty\\else\\vskip2pt" ++
  "{\\raggedright\\usebeamerfont{probe institute}\\color{probeInk}\\insertinstitute\\par}\\fi};\n" ++
  "\\end{tikzpicture}}\n\\makeatother\n" ++ metadata

def splitTemplate (fontDir : String) : String :=
  common fontDir ++
  "\\setbeamertemplate{title page}{%\n\\begin{tikzpicture}[remember picture,overlay]\n" ++
  "\\fill[probeGround] (current page.south west) rectangle (current page.north east);\n" ++
  "\\node[anchor=west,align=left,text=probeInk,font=\\usebeamerfont{probe title}] " ++
  "at ([xshift=18mm,yshift=18mm]current page.west) {\\inserttitle};\n" ++
  "\\node[anchor=west,align=left,text=probeAccent,font=\\usebeamerfont{probe subtitle}] " ++
  "at ([xshift=18mm,yshift=-10mm]current page.west) {\\insertsubtitle};\n" ++
  "\\node[anchor=south west,align=left,text=probeAccent,font=\\usebeamerfont{probe author}] " ++
  "at ([xshift=18mm,yshift=22mm]current page.south west) {\\insertauthor};\n" ++
  "\\node[anchor=south west,align=left,text=probeInk,font=\\usebeamerfont{probe institute}] " ++
  "at ([xshift=18mm,yshift=9mm]current page.south west) {\\insertinstitute};\n" ++
  "\\end{tikzpicture}}\n" ++ metadata

def point20 (v : Int) : String :=
  let sign := if v < 0 then "-" else ""
  let n := v.natAbs
  s!"{sign}{n / 20}.{(n % 20) * 5 / 10}{(n % 20) * 5 % 10}"

def pointMicro (v : Int) : String :=
  let sign := if v < 0 then "-" else ""
  let n := v.natAbs
  let frac := toString (n % 1000000)
  s!"{sign}{n / 1000000}.{String.ofList (List.replicate (6 - frac.length) '0')}{frac}"

def selftest : IO UInt32 := do
  let ghost := "<page>\n<span bbox=\"10 20 30 20\" font=\"F\" size=\"10\">\n" ++
    "<char bbox=\"10 20 15 20\" c=\"A\"/>\n<char bbox=\"15 20 20 20\" c=\"B\"/>\n</span>\n</page>"
  let pop := "<word xMin=\"1.250000\" yMin=\"2.500000\" xMax=\"3.750000\" yMax=\"4.000000\">AB</word>"
  let gs := parseGhost ghost
  let ps := parsePoppler pop
  let expectedGhost : Array GhostLine := #[{ text := "AB", x20 := 10, y20 := 20 }]
  let expectedPop : Array WordBox :=
    #[{ text := "AB", x0u := 1250000, y0u := 2500000,
        x1u := 3750000, y1u := 4000000 }]
  let ok := gs == expectedGhost && ps == expectedPop
  if ok then
    IO.println "title-placement-diff --selftest: all passed"
    return 0
  IO.eprintln s!"title-placement-diff --selftest: FAIL ghost={repr gs} poppler={repr ps}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  let root ← IO.currentDir
  let leantex := root / ".lake" / "build" / "bin" / "leantex"
  unless ← leantex.pathExists do
    IO.eprintln "title-placement-diff: build leantex first"
    return 2
  let work := root / ".lake" / "title-placement-diff"
  if ← work.pathExists then IO.FS.removeDirAll work
  IO.FS.createDirAll work
  let fontDir := (root / "testdata" / "corpus" / "fonts").toString
  let tools := [("lualatex", #["--version"]), ("gs", #["--version"]),
    ("pdftotext", #["-v"]), ("pdftoppm", #["-v"]), ("magick", #["-version"])]
  for (cmd, probe) in tools do
    if (← version cmd probe root) == "unavailable" then
      IO.eprintln s!"title-placement-diff: {cmd} not available — untested"
      return 2
  IO.println "title-placement-diff: synthetic LuaLaTeX/leantex title placement"
  IO.println "  baseline bound: 0.25 pt (5 units on Ghostscript's 1440-dpi grid)"
  IO.println s!"  lualatex: {← version "lualatex" #["--version"] root}"
  IO.println s!"  ghostscript: {← version "gs" #["--version"] root}"
  IO.println s!"  poppler: {← version "pdftotext" #["-v"] root}"
  IO.println s!"  imagemagick: {← version "magick" #["-version"] root}"
  let mut failed := false
  let mut worst : Int := 0
  for (name, source) in [("compound", compoundTemplate fontDir), ("split", splitTemplate fontDir)] do
    let src := work / s!"{name}.tex"
    IO.FS.writeFile src source
    let luaArgs := #["-halt-on-error", "-interaction=batchmode", s!"-output-directory={work}", src.toString]
    let _ ← runTool "lualatex" luaArgs root
    let _ ← runTool "lualatex" luaArgs root
    let luaPdf := work / s!"{name}-lualatex.pdf"
    IO.FS.writeBinFile luaPdf (← IO.FS.readBinFile (work / s!"{name}.pdf"))
    let leanPdf := work / s!"{name}-leantex.pdf"
    let _ ← runTool leantex.toString #[src.toString, "-o", leanPdf.toString] root
    let extract (tag : String) (pdf : System.FilePath) : IO (Array GhostLine × Array WordBox × String) := do
      let ghost := work / s!"{name}-{tag}-ghost.xml"
      let pop := work / s!"{name}-{tag}-poppler.xml"
      let raster := work / s!"{name}-{tag}-page"
      let _ ← runTool "gs" #["-q", "-dNOPAUSE", "-dBATCH", "-r1440", "-sDEVICE=txtwrite",
        "-dTextFormat=0", s!"-sOutputFile={ghost}", pdf.toString] root
      let _ ← runTool "pdftotext" #["-bbox", pdf.toString, pop.toString] root
      let _ ← runTool "pdftoppm" #["-f", "1", "-singlefile", "-png", "-r", "72",
        pdf.toString, raster.toString] root
      let png := System.FilePath.mk (raster.toString ++ ".png")
      let ground ← runTool "magick" #[png.toString, "-format",
        "%[pixel:p{1,1}]|%[pixel:p{226,127}]|%[pixel:p{452,253}]", "info:"] root
      return (parseGhost (← IO.FS.readFile ghost), parsePoppler (← IO.FS.readFile pop),
        ground.stdout.trimAscii.toString)
    let (lg, lp, lground) ← extract "lualatex" luaPdf
    let (eg, ep, eground) ← extract "leantex" leanPdf
    IO.println s!"\n{name}:"
    for line in lineNames do
      match lg.find? (·.text == line), eg.find? (·.text == line),
          lp.find? (·.text == line), ep.find? (·.text == line) with
      | some l, some e, some lb, some eb =>
        let dy := e.y20 - l.y20
        worst := max worst dy.natAbs
        let ok := dy.natAbs ≤ 5
        unless ok do failed := true
        IO.println s!"  {line}: baseline lualatex {point20 l.y20} pt, leantex {point20 e.y20} pt, delta {point20 dy} pt [{if ok then "PASS" else "FAIL"}]"
        IO.println s!"    Poppler box lualatex [{pointMicro lb.x0u}, {pointMicro lb.y0u}, {pointMicro lb.x1u}, {pointMicro lb.y1u}]"
        IO.println s!"    Poppler box leantex  [{pointMicro eb.x0u}, {pointMicro eb.y0u}, {pointMicro eb.x1u}, {pointMicro eb.y1u}]"
      | _, _, _, _ =>
        failed := true
        IO.println s!"  {line}: missing from an extractor [FAIL]"
    let expected := "srgb(37,53,70)|srgb(37,53,70)|srgb(37,53,70)"
    let groundOk := lground == expected && eground == expected
    unless groundOk do failed := true
    IO.println s!"  ground lualatex {lground}; leantex {eground} [{if groundOk then "PASS" else "FAIL"}]"
  IO.println s!"\ntitle-placement-diff: worst baseline delta {point20 worst} pt; bound 0.25 pt"
  if failed then
    IO.eprintln "title-placement-diff: FAIL"
    return 1
  IO.println "title-placement-diff: PASS"
  return 0
