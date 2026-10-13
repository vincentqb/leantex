module

public import LeanTex.Cli.FontDiscovery
public import LeanTex.Cli.FontAssembly
public import Tests.TikzCd

public section

namespace Tests

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly

/-- The faces a host resolves for a deck declaring none, the engine's default sans and its math
companion, as the fixture's request spells them. -/
def boundaryFixtureFaces : Ir.FontSpec :=
  { body := some "DejaVu Sans", math := some "TeX Gyre DejaVu Math" }

/-- A boundary picture sets in the faces the page sets in: an undeclared role carries the face the
engine resolved, a face the tool cannot see travels nowhere, and the committed fixture's PDF holds
OpenType programs only. -/
def boundaryFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let firstPass (src : String) : Ir.Doc :=
    let (toks, lds) := Lex.lex "t" src
    let (raws, pds) := Parse.parse "t" toks
    (Elab.runRawsSpanned "t" raws (lds ++ pds)).1
  let faces ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FaceScan := { faces, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  let doc := firstPass (dvDoc "\\usepackage{tikz-cd}\n" ("\\[" ++ cdLossy ++ "\\]"))
  let reqOf (d : Ir.Doc) (spec : Ir.FontSpec) : String :=
    (((Ir.pictureRefs d spec)[0]?).map (·.2)).getD ""
  match ← buildFontSet doc scan cache (.provisional true) with
  | .error _ => t "boundary faces: the vendored scan assembles" false
  | .ok (fs, _, _, _) =>
    let spec := boundaryFonts doc fs scan
    let req := reqOf doc spec
    let mathFam := (fs.math.bind (fs.fonts[·]?)).map (·.family)
    t "boundary faces: an undeclared text role travels as the face the page sets in"
      (spec.body == some fs.body.family && hasStr req s!"\\setmainfont\{{fs.body.family}}")
    t "boundary faces: an undeclared math role travels as the face the engine set formulas in"
      (mathFam.isSome && spec.math == mathFam &&
        hasStr req s!"\\setmathfont\{{mathFam.getD ""}}")
    -- An undeclared typewriter role travels as the face the page sets its code in.
    let codeDoc := firstPass (dvDoc "\\usepackage{tikz-cd}\n"
      ("Words with \\texttt{code} beside them.\n\n\\[" ++ cdLossy ++ "\\]"))
    let monoFaces := faces ++
      FontScan.family4 "DejaVu Sans Mono" (testFonts ++ "/SourceCodePro-Regular.otf") true
    let monoScan : FaceScan := { scan with faces := monoFaces }
    match ← buildFontSet codeDoc monoScan cache (.provisional true) with
    | .ok (codeFs, _, _, _) =>
      let codeSpec := boundaryFonts codeDoc codeFs monoScan
      t s!"boundary faces: an undeclared typewriter role travels as the family the page sets code \
in ({codeSpec.mono})"
        (codeSpec.mono == some "DejaVu Sans Mono" &&
          (monoDefaultOf codeDoc monoFaces []).1.map (·.family) == some "DejaVu Sans Mono" &&
          hasStr (reqOf codeDoc codeSpec) "\\setmonofont{DejaVu Sans Mono}")
      t "boundary faces: a document setting no code sends no typewriter face"
        (spec.mono.isNone && !hasStr req "\\setmonofont")
      t "boundary faces: a typewriter face the document ships, or only the engine was told of, stays home"
        ((boundaryFonts codeDoc codeFs { monoScan with docDirs := [testFonts] }).mono.isNone &&
          (boundaryFonts codeDoc codeFs { monoScan with privateDirs := [testFonts] }).mono.isNone)
    | .error _ => t "boundary faces: the typewriter scan assembles" false
    t "boundary faces: a document's own request names no face it did not declare"
      (let plain := reqOf doc doc.fonts
       !hasStr plain "\\setmainfont" && !hasStr plain "\\setmathfont" && !plain.isEmpty)
    let shipped : FaceScan := { scan with docDirs := [testFonts] }
    let kept := boundaryFonts doc fs shipped
    t "boundary faces: a face the document ships in its own directory travels nowhere"
      (kept.body.isNone && kept.math.isNone)
    -- A root only the engine was told about is no root the tool searches.
    let engineOnly := boundaryFonts doc fs { scan with privateDirs := [testFonts] }
    t "boundary faces: a face only the engine was told where to find travels nowhere"
      (engineOnly.body.isNone && engineOnly.math.isNone)
    let elsewhere := boundaryFonts doc fs { scan with privateDirs := ["/nonexistent/fonts"] }
    t "boundary faces: an engine-only root elsewhere keeps the shared faces travelling"
      (elsewhere.body == spec.body && elsewhere.math == spec.math)
    let declared := firstPass (dvDoc "\\usepackage{tikz-cd}\n\\fonts{ math = \"Latin Modern Math\" }\n"
      ("\\[" ++ cdLossy ++ "\\]"))
    t "boundary faces: a declared role stands as written"
      ((boundaryFonts declared fs scan).math == some "Latin Modern Math")
  let fixture := reqOf doc boundaryFixtureFaces
  let src ← IO.FS.readFile "testdata/boundary/cd-faces.tex"
  t "boundary faces: the fixture is the request the wrapper states" (src == fixture)
  let pdf ← IO.FS.readBinFile "testdata/boundary/cd-faces.pdf"
  match PdfRead.objects pdf with
  | .error e => t s!"boundary faces: the fixture's PDF parses: {e}" false
  | .ok es =>
    let descs := es.val.filter fun e => e.val.get? "Type" == some (.name "FontDescriptor")
    let names := descs.filterMap fun e => match e.val.get? "FontName" with
      | some (.name n) => some n
      | _ => none
    t "boundary faces: the fixture's PDF sets its formulas in the math face it names"
      (names.any fun n => hasStr n "TeXGyreDejaVuMath")
    t "boundary faces: the fixture's PDF embeds no Type 1 program"
      (!descs.isEmpty && descs.all fun e => (e.val.get? "FontFile").isNone)
    t "boundary faces: the fixture's PDF names no Type 1 font"
      (es.val.all fun e => !(e.val.get? "Type" == some (.name "Font") &&
        e.val.get? "Subtype" == some (.name "Type1")))

/-- A boundary renderer that refuses every request naming a text face and draws every other by
copying a committed PDF, logging each request to `runs`. -/
def faceRefusingRenderer (pdf runs : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'synthetic boundary renderer 1'\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "printf '%s\\n' run >> " ++ shQuote runs.toString ++ "\n" ++
  "faced=0\n" ++
  "while IFS= read -r line || [ -n \"$line\" ]; do\n" ++
  "  case \"$line\" in *setmainfont*) faced=1 ;; esac\n" ++
  "done < pic.tex\n" ++
  "if [ $faced = 1 ]; then\n" ++
  "  printf '%s\\n' '! Package fontspec Error: The font cannot be found.' > pic.log\n" ++
  "  exit 1\n" ++
  "fi\n" ++
  "/bin/cp " ++ shQuote pdf.toString ++ " pic.pdf || exit 3\n" ++
  "printf '%s\\n' 'Output written on pic.pdf (1 page).' > pic.log\n"

/-- The page's faces never cost a picture its drawing: under a face-refusing renderer the picture is
the boundary's after two requests, and a warm rebuild asks nothing. -/
def boundaryFaceRetryChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath binary
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let pdf ← IO.FS.realPath "testdata/boundary/cd-faces.pdf"
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    let runs := dir / "runs"
    writeScript (dir / "bin" / "lualatex") (faceRefusingRenderer pdf runs)
    let face := dir / "home" / ".fonts" / "OpenSans-Regular.ttf"
    IO.FS.createDirAll (dir / "home" / ".fonts")
    IO.FS.writeBinFile face (← IO.FS.readBinFile font)
    IO.FS.writeFile (dir / "doc.tex") ("\\documentclass{article}\n\\usepackage{newtxtext}\n" ++
      "\\begin{document}\nBefore.\n\n\\begin{tikzpicture}\\node at (0,0) {Alpha};" ++
      "\\pattern (0,0) rectangle (1,1);\\end{tikzpicture}\n\nAfter.\n\\end{document}\n")
    let build : IO (UInt32 × Bool × Array (String × String) × Nat) := do
      let out := dir / "doc.pdf"
      if ← out.pathExists then IO.FS.removeFile out
      let r ← IO.Process.output {
        cmd := binary.toString, cwd := some dir
        args := #["doc.tex", "-o", out.toString, "--porcelain"]
        env := #[("PATH", some (dir / "bin").toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString),
          ("HOME", some (dir / "home").toString), ("LEANTEX_FONT", some face.toString)] }
      let mut n := 0
      if ← runs.pathExists then
        n := (((← IO.FS.readFile runs).splitOn "\n").filter (!·.isEmpty)).length
      return (r.exitCode, ← out.pathExists, porcelainCodes r.stdout, n)
    let undrawn (cs : Array (String × String)) : Bool :=
      cs.any fun (c, _) => ["W0382", "W0419", "N0419", "W0379", "W0362"].contains c
    let (e1, w1, c1, n1) ← build
    t s!"boundary face retry: the cold build ships ({e1}; {c1})" (e1 == 0 && w1)
    t s!"boundary face retry: the picture is the boundary's drawing ({c1})" (!undrawn c1)
    t s!"boundary face retry: the page's request, then the document's own ({n1} runs)" (n1 == 2)
    let (e2, w2, c2, n2) ← build
    t s!"boundary face retry: the warm build ships the same drawing ({e2}; {c2})"
      (e2 == 0 && w2 && !undrawn c2)
    t s!"boundary face retry: the warm build asks the renderer nothing ({n2 - n1} runs)"
      (n2 == n1)

end Tests
