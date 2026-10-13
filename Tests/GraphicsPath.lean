module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- A boundary renderer that draws only where `figs/dot.png` stands beside the standalone as
`\graphicspath` finds it, and refuses with LaTeX's words otherwise. -/
def stagedRenderer (pdf : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'synthetic boundary renderer 1'\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "if [ ! -f figs/dot.png ]; then\n" ++
  "  printf '%s\\n' \"! LaTeX Error: File 'dot' not found.\" > pic.log\n" ++
  "  exit 1\n" ++
  "fi\n" ++
  "/bin/cp " ++ shQuote pdf.toString ++ " pic.pdf || exit 3\n" ++
  "printf '%s\\n' 'Output written on pic.pdf (1 page).' > pic.log\n"

/-- An image a `\graphicspath` directory holds is the document's image, for the engine and for a
boundary request's staged files, in graphicx's candidate order. -/
def graphicsPathChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let raws (s : String) := (Parse.parse "t" (Lex.lex "t" s).1).1
  t "graphics path: the last declaration's directories, wherever it stands"
    (Compat.graphicsPath "t" (raws ("\\graphicspath{{a/}}\n\\begin{document}\n" ++
      "\\graphicspath{{figs/}{more/}}\nx\n\\end{document}\n")) == #["figs/", "more/"])
  t "graphics path: none declared, none searched"
    (Compat.graphicsPath "t" (raws "\\begin{document}\nx\n\\end{document}\n")).isEmpty
  t "graphics path: each extension as written, then under each directory"
    ((Image.searchCandidates #["figs/", "more/"] "dot").take 6 ==
      ["dot", "figs/dot", "more/dot", "dot.pdf", "figs/dot.pdf", "more/dot.pdf"])
  t "graphics path: without one, the candidates as they were"
    (Image.searchCandidates #[] "dot" == Image.sourceCandidates "dot")
  let binary ← IO.FS.realPath binary
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let png ← IO.FS.readBinFile "testdata/corpus/rects.png"
  let pdf ← IO.FS.realPath "testdata/corpus/figures/box.pdf"
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    IO.FS.createDirAll (dir / "figs")
    IO.FS.writeBinFile (dir / "figs" / "dot.png") png
    writeScript (dir / "bin" / "lualatex") (stagedRenderer pdf)
    let build (doc : String) : IO (UInt32 × Bool × Array (String × String)) := do
      IO.FS.writeFile (dir / "doc.tex") doc
      let out := dir / "doc.pdf"
      if ← out.pathExists then IO.FS.removeFile out
      let r ← IO.Process.output {
        cmd := binary.toString, cwd := some dir
        args := #["doc.tex", "-o", out.toString, "--porcelain"]
        env := #[("PATH", some (dir / "bin").toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString),
          ("LEANTEX_FONT", some font.toString)] }
      return (r.exitCode, ← out.pathExists, porcelainCodes r.stdout)
    let (e1, w1, c1) ← build ("\\documentclass{article}\n\\usepackage{graphicx}\n" ++
      "\\graphicspath{{figs/}}\n\\begin{document}\n" ++
      "\\includegraphics[width=1cm,alt={An invented dot}]{dot}\n\\end{document}\n")
    t s!"graphics path: the figure ships ({e1}; {c1})"
      (e1 == 0 && w1 && !c1.any fun (c, _) => c == "W0601" || c == "W0301")
    let (e2, w2, c2) ← build ("\\documentclass{article}\n\\usepackage{tikz}\n" ++
      "\\graphicspath{{figs/}}\n\\begin{document}\nBefore.\n\n" ++
      "\\begin{tikzpicture}\\node at (0,0) {\\includegraphics[width=1cm]{dot}};" ++
      "\\pattern (0,0) rectangle (1,1);\\end{tikzpicture}\n\nAfter.\n\\end{document}\n")
    t s!"graphics path: the boundary picture including it is drawn ({e2}; {c2})"
      (e2 == 0 && w2 && !c2.any fun (c, _) =>
        ["W0382", "W0419", "N0419", "W0379", "W0601"].contains c)

end Tests
