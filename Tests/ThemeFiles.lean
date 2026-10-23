module

public import Tests.Support
import LeanTex.Cli.Args
import LeanTex.Core.ThemeImport

public section

open LeanTex.Core

namespace Tests.ThemeFiles

/-- The leantex classes' themes: a theme is its palette alone, shipped to TeX resolved
(`tex/lttheme-<name>.tex`), and a palette key paints the beamer elements its role does
(`tex/ltbeamercolors.tex`). -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (name, text) in Theme.texFiles do
    t s!"theme files: tex/lttheme-{name}.tex is generated from the theme's palette"
      ((← IO.FS.readFile s!"tex/lttheme-{name}.tex") == text)
  t "theme files: tex/ltbeamercolors.tex is generated from the role registry"
    ((← IO.FS.readFile "tex/ltbeamercolors.tex") == Ir.ltBeamerColorsTex)
  t "theme files: the frame title's band colour paints beamer's frametitle background"
    (hasStr Ir.ltBeamerColorsTex "\\setbeamercolor { frametitle } { bg = ltx-frametitlebg }")
  let src := "\\documentclass{ltframe}\n\\theme{moloch}\n\\begin{document}\n" ++
    "\\begin{frame}{Kilo}\nAlpha.\n\\end{frame}\n\\end{document}\n"
  let (doc, ds) := elabStr src
  let moloch := (Theme.find? "moloch").map fun th => th.realize Ir.GroundDepth.decks
  t "theme files: a leantex class takes a theme's palette"
    (moloch.any fun p => p.entries.all fun (k, c) => doc.palette.entries.contains (k, c))
  t "theme files: a leantex class takes none of a theme's styles, tokens or chrome, and names them"
    ((doc.styles.find? "frametitle").isNone &&
      ds.any fun d => d.code == "W0355" && hasStr (d.detail.getD "") "styles")
  let (beamer, _) := elabStr (src.replace "{ltframe}" "{beamer}")
  t "theme files: beamer takes the whole theme" ((beamer.styles.find? "frametitle").isSome)
  -- The importers: a stylesheet's custom properties and a beamer colour theme to a `\palette`.
  let html := (HtmlDoc.emit {} doc).1
  let (fromCss, _) := ThemeImport.ofCss html []
  -- A page's top-level `:root` declares the roles it uses.
  t "theme import: leantex's own stylesheet returns the theme's colours its page declares"
    (moloch.any fun p => ["fg", "bg", "frametitlebg", "frametitlefg"].all fun key =>
      p.entries.any fun (k, c) => k.key == key && fromCss.contains (key, c.hex))
  let (mapped, skipped) := ThemeImport.ofCss ":root { --brand: #12a4f0; --spacing: 4px; }"
    [("brand", "accent")]
  t "theme import: a mapped property names its key, an unmapped one is skipped by name"
    (mapped == #[("accent", "#12A4F0")] && skipped == #[.unmapped "spacing"])
  let (fromSty, _) := ThemeImport.ofBeamer "beamercolorthemeexample.sty"
    "\\setbeamercolor{frametitle}{fg=white,bg=black}\n\\setbeamercolor{alerted text}{fg=red}\n"
  t s!"theme import: a beamer colour theme's colours are their roles' keys, and only those ({fromSty})"
    (fromSty.qsort (·.1 < ·.1) ==
      #[("alert", "#FF0000"), ("alerttitlefg", "#FF0000"), ("framesubtitlefg", "#FFFFFF"),
        ("frametitlebg", "#000000"), ("frametitlefg", "#FFFFFF")])
  let (styDoc, styDs) := elabStr ("\\documentclass{ltframe}\n" ++
    ThemeImport.themeFile "beamercolorthemeexample.sty" fromSty ++ "\\begin{document}\n\\end{document}\n")
  t "theme import: an imported beamer theme reads back with nothing refused"
    (!(styDs.any fun d => d.severity == .error || d.code == "E0320") &&
      styDoc.palette.entries.any fun (k, c) => k.key == "frametitlebg" && c.hex == "#000000")
  let (css, cssSkips) := ThemeImport.ofCss
    (":root{--ltx-fg:#abc;/* --ltx-bg: #ffffff; */--brand:#112233}\n" ++
      "@media (prefers-color-scheme: dark){:root{--ltx-fg:#000000;}}\n") [("brand", "accent")]
  t s!"theme import: a top-level :root rule's last declaration, three digits doubled ({css})"
    (css == #[("fg", "#AABBCC"), ("accent", "#112233")])
  t "theme import: a comment declares nothing and a rule inside @media is named, not read"
    (cssSkips.any fun k => k matches .outside "ltx-fg" _)
  let file := ThemeImport.themeFile "example.css" mapped
  let (themed, _) := elabStr ("\\documentclass{ltframe}\n" ++ file ++ "\\begin{document}\n\\end{document}\n")
  t "theme import: the theme file is a palette leantex reads"
    (themed.palette.entries.any fun (k, c) => k.key == "accent" && c.hex == "#12A4F0")
  t "theme import: the command line reads its source, maps and output"
    (match LeanTex.Cli.parse
        ["theme", "import", "--css", "x.css", "--map", "brand=accent", "-o", "t.tex"] with
      | .ok cfg => cfg.cmd == .themeImport .css "x.css" [("brand", "accent")] &&
          cfg.output == some "t.tex"
      | .error _ => false)

/-- The theme files and the beamer colour table written under `--update`. -/
def update : IO Unit := do
  for (name, text) in Theme.texFiles do
    IO.FS.writeFile s!"tex/lttheme-{name}.tex" text
  IO.FS.writeFile "tex/ltbeamercolors.tex" Ir.ltBeamerColorsTex
  IO.println "updated tex/lttheme-*.tex and tex/ltbeamercolors.tex"

end Tests.ThemeFiles
