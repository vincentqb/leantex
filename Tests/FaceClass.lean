module

public import Tests.Support
public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FaceClass

/-- The first line on page `i` whose text starts with `w`: its baseline from the page's top and its
left edge. -/
private def lineAt (out : Layout.Out) (i : Nat) (w : String) : Option (Dim.Length × Dim.Length) :=
  (out.pages[i]?.bind fun p => p.lines.find? fun l =>
    (lineText l).trimAscii.toString.startsWith w).map fun l => (l.y, l.x)

/-- The leantex face class (`tex/ltface.cls`): its presets' records, a card's face on its grid and a
poster's column grid, as lualatex sets the class. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let near (a b : Dim.Length) : Bool := (a - b).abs ≤ Dim.pt 1 / (100 : Int)
  let card := "\\documentclass[preset=card]{ltface}\n\\begin{document}\n\\begin{frame}\n" ++
    "Alder Placeholder\n\nBirch is a line long enough to wrap across the card's measure twice.\n" ++
    "\\end{frame}\n\\begin{frame}{Cedar}\nDelta below a title.\n\\end{frame}\n\\end{document}\n"
  let (doc, ds) := elabStr card
  let warned := (ds.filter fun d => d.severity == .warning || d.severity == .error).map (·.code)
  t s!"face class: a card loads with nothing warned ({warned})" warned.isEmpty
  t "face class: preset=card is the card, ISO/IEC 7810's ID-1 at 10pt inside a 5mm safe margin"
    (doc.docClass == .face .card && doc.page.width == Dim.mm100 8560 &&
      doc.page.height == Dim.mm100 5398 && doc.page.fontSize == Dim.pt 10 &&
      doc.page.hmargin == Dim.mm 5 && doc.page.vmargin == Dim.mm 5 && doc.page.grid == some true)
  let (alias, _) := elabStr (card.replace "[preset=card]{ltface}" "{card}")
  t "face class: \\documentclass{card} is the card preset" (alias.docClass == .face .card)
  t "face class: the card keeps the card class's contracts"
    ((Ir.DocClass.face .card).record.pagesBound == some .faces &&
      (Ir.DocClass.face .card).record.inkInArea.isSome &&
      ((Ir.DocClass.face .card).record.xHeightFloor.map (·.1)) == some Ir.cardXHeightFloor)
  let out := layoutOf fonts doc
  let lead := Dim.pt 12
  let top := Dim.mm 5
  -- lualatex: the face's first line a leading below the safe margin, each next a leading on.
  t "face class: a card's first line stands a leading below its margin, the next on the grid"
    ((lineAt out 0 "Alder").any (fun (y, _) => near y (top + lead)) &&
      (lineAt out 0 "Birch").any (fun (y, _) => near y (top + 2 * lead)))
  t "face class: a card's title stands on its first line, its body on the next"
    ((lineAt out 1 "Cedar").any (fun (y, _) => near y (top + lead)) &&
      (lineAt out 1 "Delta").any (fun (y, _) => near y (top + 2 * lead)))
  let poster := "\\documentclass{ltface}\n\\begin{document}\n\\begin{frame}\n" ++
    "\\begin{columns}[T]\n\\begin{column}{0.38\\textwidth}\nAlder.\n\\end{column}\n" ++
    "\\begin{column}{0.2\\textwidth}\nBirch.\n\\end{column}\n\\end{columns}\n\\end{frame}\n" ++
    "\\end{document}\n"
  let (pdoc, _) := elabStr poster
  t "face class: \\documentclass{ltface} is the poster, beamerposter's A0 board at 24.88pt"
    (pdoc.docClass == .face .poster && pdoc.page.width == Dim.mm 1189 &&
      pdoc.page.fontSize == Ir.posterFontSize)
  let textW := pdoc.page.width - 2 * pdoc.page.hmargin
  let plead := Ir.leadingFor Ir.posterFontSize
  let grid := Ir.faceColumns textW (2 * plead) Ir.posterFontSize 66
  let chars := Ir.faceChars10 Ir.posterFontSize grid.width
  t s!"face class: the poster holds five columns of 60 to 75 characters ({grid.count}, {chars})"
    (grid.count == 5 && 600 ≤ chars && chars ≤ 750)
  let pout := layoutOf fonts pdoc
  -- lualatex: each column spans its nearest whole columns, two leadings between them.
  t "face class: a column spans whole grid columns, the next a gutter on"
    ((lineAt pout 0 "Birch").any fun (_, x) =>
      near x (pdoc.page.hmargin + 2 * grid.width + 2 * grid.gutter))
  t "face class: a narrow column spans one grid column, a wide one all of them"
    (grid.spans [Dim.pt 1] == [grid.width] &&
      grid.spans [textW] == [5 * grid.width + 4 * grid.gutter])
  -- A row's columns end on the grid column nearest its width so far, so halves and thirds fit.
  t "face class: two half columns span the grid between them, three thirds too"
    (grid.spans [textW / (2 : Int), textW / (2 : Int)] ==
        [3 * grid.width + 2 * grid.gutter, 2 * grid.width + grid.gutter] &&
      (grid.spans [textW / (3 : Int), textW / (3 : Int), textW / (3 : Int)]).foldl (· + ·) 0 +
        2 * grid.gutter ≤ textW)
  let (mini, _) := elabStr ("\\documentclass{ltface}\n\\begin{document}\n\\begin{frame}\n" ++
    "\\begin{minipage}{0.5\\textwidth}\nAlder.\n\\end{minipage}\\hfill\n" ++
    "\\begin{minipage}{0.3\\textwidth}\nBirch.\n\\end{minipage}\n\\end{frame}\n\\end{document}\n")
  -- lualatex: a minipage keeps its declared width; only beamer's columns span the grid.
  t "face class: a minipage on a poster keeps its declared width"
    ((lineAt (layoutOf fonts mini) 0 "Birch").any fun (_, x) =>
      near x (pdoc.page.width - pdoc.page.hmargin - textW * (3 : Int) / (10 : Int)))
  let (sized, sizedDs) := elabStr (card.replace "[preset=card]" "[preset=card, fontsize=12pt]")
  t "face class: fontsize= sets a face's body, its leading 1.2 of it"
    (sized.page.fontSize == Dim.pt 12 && !(sizedDs.any (·.code == "W0104")))
  let (_, badDs) := elabStr (card.replace "[preset=card]" "[preset=badge]")
  t "face class: an unknown preset is named, the poster standing"
    (badDs.any fun d => d.code == "W0104" && hasStr d.message "badge")
  let (fonted, fontDs) := elabStr (card.replace "\\begin{document}"
    "\\fonts{ body = \"Example Serif\" }\n\\begin{document}")
  t "face class: a document's body family replaces the class's faces with no warning"
    (!(fontDs.any (·.code == "W0343")) && fonted.fonts.faceFor 0 700 false == none &&
      fonted.fonts.body == some "Example Serif")
  let html := (HtmlDoc.emit {} doc).1
  t "face class: a card's web page is its faces as slides" (hasStr html "<section class=\"slide")
  t "face class: tex/ltfacesource.tex is generated from the source leantex splices"
    ((← IO.FS.readFile "tex/ltfacesource.tex") == Ir.ltFaceSourceTex)

/-- `tex/ltfacesource.tex` written from `Ir.ltFaceSourceTex` under `--update`. -/
def update : IO Unit := do
  IO.FS.writeFile "tex/ltfacesource.tex" Ir.ltFaceSourceTex
  IO.println "updated tex/ltfacesource.tex"

end Tests.FaceClass
