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
role stands as written, and a face the document ships in its own directory
travels nowhere, since the tool cannot see it. The fixture beside it is the
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
    let spec := boundaryFonts doc.fonts fs scan
    let req := reqOf doc spec
    let mathFam := (fs.math.bind (fs.fonts[·]?)).map (·.family)
    t "boundary faces: an undeclared text role travels as the face the page sets in"
      (spec.body == some fs.body.family && hasStr req s!"\\setmainfont\{{fs.body.family}}")
    t "boundary faces: an undeclared math role travels as the face the engine set formulas in"
      (mathFam.isSome && spec.math == mathFam &&
        hasStr req s!"\\setmathfont\{{mathFam.getD ""}}")
    t "boundary faces: a document's own request names no face it did not declare"
      (let plain := reqOf doc doc.fonts
       !hasStr plain "\\setmainfont" && !hasStr plain "\\setmathfont" && !plain.isEmpty)
    let shipped : FaceScan := { scan with docDirs := [testFonts] }
    let kept := boundaryFonts doc.fonts fs shipped
    t "boundary faces: a face the document ships in its own directory travels nowhere"
      (kept.body.isNone && kept.math.isNone)
    let declared := firstPass (dvDoc "\\usepackage{tikz-cd}\n\\fonts{ math = \"Latin Modern Math\" }\n"
      ("\\[" ++ cdLossy ++ "\\]"))
    t "boundary faces: a declared role stands as written"
      ((boundaryFonts declared.fonts fs scan).math == some "Latin Modern Math")
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

end Tests
