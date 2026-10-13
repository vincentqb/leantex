module

public import LeanTex.Cli.FontDiscovery
public import LeanTex.Cli.FontAssembly
public import Tests.TikzCd

public section

namespace Tests

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly

/-- The faces a host resolves for a deck that declares none — the engine's
default sans and its designed math companion — as the fixture's request
spells them. -/
def boundaryFixtureFaces : Ir.FontSpec :=
  { body := some "DejaVu Sans", math := some "TeX Gyre DejaVu Math" }

/-- **A boundary picture sets in the faces the page sets in.** The invariant
whose absence set every diagram the reference talks drew at the boundary in
lualatex's Computer Modern: a request's standalone named only the faces the
document declared, so a deck that declared none — its text in the engine's
default sans, its formulas in that face's math companion — sent its
diagrams to a tool that set them in other faces, as Type 1 programs a
vector import cannot read. The request now carries, for a role the document
left undeclared, the face the engine resolved (`boundaryFonts`); a declared
role stands as written, and a face the document ships in its own directory,
or one found only where the engine alone was told to look, travels nowhere,
since the tool cannot see it. The fixture beside it is the
request for an invented diagram under the faces a host resolves for such a
deck, and the PDF lualatex made of it: the check holds the request to the
committed source, so a wrapper change fails here until the PDF is
regenerated (`lualatex cd-faces.tex` in `testdata/boundary`), and holds the
PDF to its font programs — OpenType, never Type 1. -/
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
    -- An undeclared typewriter role travels as the face the page sets its
    -- code in, a platform monospace here, so a picture's code is the page's.
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
    -- A root only the engine was told about (`--font-dir`,
    -- `LEANTEX_FONT_PATH`) is no root the tool searches: a family found
    -- there alone would name a face lualatex cannot find, failing a picture
    -- its Computer Modern default draws.
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
  -- The committed fixture: the request under a host's resolved faces, and
  -- what lualatex made of it.
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

/-- A boundary renderer that refuses every request naming a text face, as a
document's own package refuses one beside it — newtxtext under LuaTeX loads
fontspec with `.otf` defaults, so the face is looked for as a file — and
draws every other by copying a committed PDF; each request it reads appends
a line to `runs`. Shell builtins and `/bin/cp` alone. -/
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

/-- **The page's faces never cost a picture its drawing.** The invariant whose
absence withdrew every picture of a document loading newtxtext, txfonts,
newpxmath, mathabx, libertinust1math or stix: the boundary request carries
the faces the page sets in, a package the document loads refuses fontspec or
unicode-math beside them, and the picture the document's own request draws
fell back to the rendered subset with its losses named. The built binary, on
a machine whose renderer refuses every request naming a face
(`faceRefusingRenderer`), for a deck whose engine-resolved face travels (a
face under the user's own font directory): the picture is the boundary's —
no withdrawal, no placeholder, no refusal — after two requests, the page's
and the document's own; and a warm rebuild asks the renderer nothing, both
answers remembered. The caller supplies an already-built binary. -/
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
