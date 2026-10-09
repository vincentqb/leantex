module

public import Tests.Support
public import LeanTex.Core.SeedPalette

public section

open LeanTex.Core

/-- Invented seed families, both polarities. The export is exercised through
the real elaborator and both shipped representations, not an IR dump. -/
def seedPaletteChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let pdfGround (geom : Layout.Geom) (color : Ir.Color) (out : Layout.Out) :=
    let want := geom.ground color
    out.pages.size == 1 && out.pages.all fun page =>
      page.fills[0]?.any fun fill =>
        fill.x == want.x && fill.y == want.y && fill.w == want.w &&
          fill.h == want.h && fill.color == want.color
  let htmlGround (color : Ir.Color) (head : Array Html.Node) :=
    let css := treeCssList "" head.toList
    let property (selector key : String) :=
      ((String.intercalate ";" (cssRulesOf css selector)).splitOn ";").foldl
        (fun value decl => match decl.splitOn ":" with
          | [name, found] =>
            if name.trimAscii.toString == key then some found.trimAscii.toString else value
          | _ => value) none
    property ":root" "--bg" == some color.css &&
      property "body" "background" == some "var(--bg)"
  let inks : List Ir.Color :=
    [{ r := 25, g := 42, b := 61 }, { r := 43, g := 31, b := 53 },
     { r := 32, g := 49, b := 39 }]
  let accents : List Ir.Color :=
    [{ r := 196, g := 106, b := 119 }, { r := 32, g := 147, b := 151 },
     { r := 150, g := 120, b := 190 }, { r := 250, g := 157, b := 37 },
     { r := 245, g := 206, b := 56 }, { r := 55, g := 207, b := 195 }]
  for ink in inks do
    for accent in accents do
      for dark in [false, true] do
        let seeds : SeedPalette.Seeds :=
          if dark then ⟨Ir.Color.white, ink, accent⟩ else ⟨ink, Ir.Color.white, accent⟩
        let name := s!"seed palette {reprStr seeds}"
        match SeedPalette.generate seeds with
        | none => t (name ++ " derives all roles") false
        | some palette =>
          t (name ++ " meets every role/ground contract")
            (SeedPalette.contract seeds palette.colors)
          let c := palette.colors
          t (name ++ " separates panel, edge and text in contrast order")
            (Contrast.contrastMilli c.surface seeds.paper <
                Contrast.contrastMilli c.diagramMuted seeds.paper &&
              Contrast.contrastMilli c.diagramMuted seeds.paper <
                Contrast.contrastMilli c.muted seeds.paper &&
              Contrast.contrastMilli c.muted seeds.paper <
                Contrast.contrastMilli seeds.ink seeds.paper)
          let pre := SeedPalette.declarations "sample" seeds palette
          let build (ground role : String) :=
            elabStr ("\\documentclass{article}" ++ pre ++
              "\\palette{bg=" ++ ground ++ ", fg=" ++ role ++ "}" ++
              "\\begin{document}\\textcolor{" ++ role ++ "}{Witness}\\end{document}")
          for (ground, groundColor, role, color) in [
              ("samplePaper", seeds.paper, "sampleMuted", c.muted),
              ("sampleSurface", c.surface, "sampleMuted", c.muted),
              ("samplePaper", seeds.paper, "sampleAccentText", c.accentText),
              ("sampleSurface", c.surface, "sampleAccentText", c.accentText),
              ("sampleInk", seeds.ink, "sampleMutedOnDark", c.mutedOnDark),
              ("sampleInk", seeds.ink, "sampleAccentOnDark", c.accentOnDark)] do
            let (doc, ds) := build ground role
            t (name ++ " exports clean TeX declarations")
              (ds.all (·.severity == .note))
            let out := layoutOf fonts doc
            t (name ++ s!" {ground}/{role} paints the PDF ground")
              (pdfGround (.ofPage doc.page) groundColor out)
            t (name ++ s!" {ground}/{role} paints PDF glyphs")
              ((allLines out).any fun line => lineText line == "Witness" &&
                line.segs.any fun seg => match seg with
                  | .run _ value _ _ _ _ _ _ _ _ _ => value == color
                  | _ => false)
            let (head, nodes, _) := HtmlDoc.emitTree {} doc
            t (name ++ s!" {ground}/{role} paints the HTML ground")
              (htmlGround groundColor head)
            t (name ++ s!" {ground}/{role} paints typed HTML")
              ((elemStylesList #[] nodes.toList).any fun (text, style) =>
                text == "Witness" &&
                  style == s!"color: var(--{role}, {color.css})")
          for (ground, groundColor) in [
              ("samplePaper", seeds.paper), ("sampleSurface", c.surface),
              ("sampleAccentSoft", c.accentSoft)] do
            let (doc, ds) := elabStr ("\\documentclass{article}" ++ pre ++
              "\\palette{bg=" ++ ground ++ ",fg=sampleInk}\\pictures{tool=none}" ++
              "\\begin{document}\\begin{tikzpicture}" ++
              "\\fill[sampleAccent] (0,0) rectangle (1,1);" ++
              "\\draw[draw=sampleAccentEdge] (2,0) -- (3,1);" ++
              "\\end{tikzpicture}\\end{document}")
            t (name ++ " exports clean diagram colours")
              (ds.all (·.severity == .note))
            let out := layoutOf fonts doc
            t (name ++ s!" {ground} paints the PDF diagram ground")
              (pdfGround (.ofPage doc.page) groundColor out)
            t (name ++ s!" {ground} preserves decorative fill and essential stroke in PDF")
              (out.pages.any fun page =>
                page.fills.any (·.color == seeds.accent) &&
                  page.paths.any fun p => p.stroke.any (·.color == c.accentEdge))
            let (head, nodes, _) := HtmlDoc.emitTree {} doc
            t (name ++ s!" {ground} paints the HTML diagram ground")
              (htmlGround groundColor head)
            let attrs := elemAttrsList (fun _ => true) #[] nodes.toList
            t (name ++ s!" {ground} preserves decorative fill and essential stroke in HTML")
              (attrs.any (fun (_, a) => a.contains ("fill", seeds.accent.css)) &&
                attrs.any fun (_, a) => a.contains ("stroke", c.accentEdge.css))
  -- Keeping the same foreground while changing only its enclosing ground
  -- must fail both artifact judges.
  let (wrongGround, _) := elabStr
    "\\documentclass{article}\\palette{bg=black,fg=black}\
\\begin{document}Witness\\end{document}"
  t "seed palette PDF guard rejects a replaced ground"
    (!(pdfGround (.ofPage wrongGround.page) Ir.Color.white (layoutOf fonts wrongGround)))
  let (head, _, _) := HtmlDoc.emitTree {} wrongGround
  t "seed palette HTML guard rejects a replaced ground"
    (!(htmlGround Ir.Color.white head))
  for seeds in [
      (⟨Ir.Color.black, Ir.Color.white, { r := 140, g := 140, b := 140 }⟩ :
        SeedPalette.Seeds),
      (⟨Ir.Color.white, { r := 32, g := 49, b := 39 },
        { r := 150, g := 111, b := 190 }⟩ : SeedPalette.Seeds)] do
    t "seed palette derives edges when the unchanged accent cannot serve"
      (SeedPalette.generate seeds |>.isSome)
  for seeds in [
      (⟨Ir.Color.white, Ir.Color.white, Ir.Color.black⟩ : SeedPalette.Seeds),
      (⟨Ir.Color.black, Ir.Color.white, Ir.Color.white⟩ : SeedPalette.Seeds),
      (⟨{ Ir.Color.black with cmyk := some (0, 0, 0, 1000) },
        Ir.Color.white, { r := 196, g := 106, b := 119 }⟩ :
        SeedPalette.Seeds)] do
    t "seed palette refuses unsatisfied seed contracts"
      (SeedPalette.generate seeds |>.isNone)
