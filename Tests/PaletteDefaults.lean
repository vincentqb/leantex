module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.PaletteDefaults

/-- The glyph runs a page set, with the scalars each shipped. -/
private def runsOf (out : Layout.Out) : Array (String × Ir.Color) :=
  out.pages.flatMap fun p => p.lines.flatMap fun l => l.segs.filterMap fun
    | .run _ ink _ _ glyphs .. =>
      if glyphs.isEmpty then none else some (String.ofList (glyphs.map (·.2.1)).toList, ink)
    | _ => none

/-- A role's value in a page's light stylesheet, its `var()` chain chased. -/
private def cssRole (css : String) (r : Ir.Role) : Option String :=
  chaseCssValue (screenRootVars css) (HtmlDoc.roleRef r)

/-- **What an undeclared document and a shipped bundle show.** moloch draws
its progress bar and title separator in its lineage colour, exactly as
lualatex writes it, and its alert is that colour realized as text on its
page, its hue held within a degree at 4.6:1; an undeclared list marks its
items in one colour on the page and in the HTML; an undeclared article's
HTML stands on the white its PDF prints, which paints no page and sets
every word in black; a markdown note's fenced code stands on its code
ground in both artifacts; and an undeclared deck's blocks are tinted cards,
each title band and body a tint at least 1.10:1 apart. Read off the shipped
pages, the PDF's operators and the typed HTML. Invented content. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  -- moloch's lineage, as lualatex writes it: `0.92157 0.50587 0.10588 rg`.
  let (mdoc, _) := elabStr ("\\documentclass[aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\title{Probe Title}\n\\author{Probe Author}\n\\begin{document}\n\\maketitle\n" ++
    "\\begin{frame}{One}Probe.\\end{frame}\n\\end{document}")
  let mgeom := Layout.Geom.ofPage mdoc.page
  let mpdf := pdfText (Pdf.write mgeom fonts (layoutOf fonts mdoc mgeom).pages mdoc.info)
  t "moloch: the title separator draws lualatex's lineage operator"
    (bytesContain mpdf "0.92157 0.50587 0.10588 rg")
  let lineage := Ir.Color.ofHtml 0xEB 0x81 0x1B
  match Ir.Design.declared? mdoc.palette .alert, Ir.Design.at mdoc.palette .print .page with
  | some alert, some page =>
    t s!"moloch: the alert {alert.css} keeps the lineage's hue within a degree"
      (hueGap (hueOf alert) (hueOf lineage) ≤ 1000)
    t s!"moloch: the alert {alert.css} reads at 4.6:1 on its page"
      (4600 ≤ Contrast.contrastMilli alert page)
  | _, _ => t "moloch: the alert and the page resolve" false
  -- An undeclared list: one marker colour on the page and in the HTML.
  let (ldoc, _) := elabStr (dvDoc "" ("Probe words.\n\\begin{itemize}\n\\item First\n" ++
    "\\item Second\n\\end{itemize}"))
  let lout := layoutOf fonts ldoc
  let bullets := (runsOf lout).filter (·.1.any (· == '•')) |>.map (·.2)
  let lcss := (HtmlDoc.emit {} ldoc).1
  t s!"an undeclared list: the page and the HTML mark it in one colour ({bullets.map (·.css)}, {cssRole lcss .marker})"
    (!bullets.isEmpty && bullets.all fun c => cssRole lcss .marker == some (HtmlDoc.cssColor c))
  -- An undeclared article: the HTML on white, the PDF unpainted and black.
  let (adoc, _) := elabStr (dvDoc "" "Probe words in an undeclared article.")
  let ageom := Layout.Geom.ofPage adoc.page
  let aout := layoutOf fonts adoc ageom
  let apdf := pdfText (Pdf.write ageom fonts aout.pages adoc.info)
  t "an undeclared article: the HTML body stands on white"
    (cssRole (HtmlDoc.emit {} adoc).1 .page == some "#ffffff")
  t "an undeclared article: the PDF paints no page and sets its words in black"
    (aout.pages.all (·.fills.isEmpty) && (runsOf aout).all (·.2 == Ir.Color.black) &&
      !bytesContain apdf " rg\n" && !bytesContain apdf " k\n")
  -- A markdown note's fenced code: its code ground in both artifacts.
  let (mddoc, _) := elabMd "Probe words.\n\n```\nalpha = 1\nbravo = 2\n```\n"
  let ground := Ir.Design.at mddoc.palette .print .codeSurface
  let mdout := layoutOf fonts mddoc
  t s!"a markdown note: the fenced code stands on its code ground in the PDF ({ground.map (·.css)})"
    (ground.isSome && mdout.pages.any fun p => p.fills.any fun f => some f.color == ground)
  t "a markdown note: the HTML paints the same ground"
    ((ground.map HtmlDoc.cssColor) == cssRole (HtmlDoc.emit {} mddoc).1 .codeSurface &&
      ground.isSome)
  -- An undeclared deck: tinted cards on every block.
  let (ddoc, _) := elabStr ("\\documentclass[aspectratio=169]{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}{Cards}\n\\begin{block}{Plain}Kilo body.\\end{block}\n" ++
    "\\begin{alertblock}{Alerted}Lima body.\\end{alertblock}\n" ++
    "\\begin{exampleblock}{Example}Mike body.\\end{exampleblock}\n\\end{frame}\n\\end{document}")
  let fills := (layoutOf fonts ddoc).pages.flatMap (·.fills) |>.map (·.color)
  for (kind, barRole, bodyRole) in [("block", Ir.Role.blockTitleBar, Ir.Role.blockBodyGround),
      ("alert", .alertTitleBar, .alertBodyGround), ("example", .exampleTitleBar, .exampleBodyGround)] do
    match Ir.Design.at ddoc.palette .print barRole, Ir.Design.at ddoc.palette .print bodyRole with
    | some bar, some body =>
      t s!"an undeclared deck: the {kind} block paints its title band and body"
        (fills.contains bar && fills.contains body)
      t s!"an undeclared deck: the {kind} band and body stand at least 1.10:1 apart"
        (1100 ≤ Contrast.contrastMilli bar body)
      for fill in [bar, body] do
        t s!"an undeclared deck: the {kind} fill {fill.css} shows chroma 0.005 or more"
          (5 * 10 ^ 15 ≤ (lchOf fill).1)
    | _, _ => t s!"an undeclared deck: the {kind} block has a band and a body" false

end Tests.PaletteDefaults
