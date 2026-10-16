module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- hyperref's `colorlinks` paints a cross-reference in `linkcolor`, a URL in `urlcolor` and a
citation's mark in `citecolor`, as lualatex does, and nothing without it. -/
def linkColorChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n\\section{Alpha}\\label{a}\n" ++
    "See \\ref{a}, \\url{https://example.org}, \\hyperlink{a}{Zephyr} and \\cite{k}.\n" ++
    "\\begin{thebibliography}{9}\n\\bibitem{k} A. Person. A title. 2020.\n" ++
    "\\end{thebibliography}\n\\end{document}"
  -- The ink each glyph ships in, on the body line that holds the links.
  let inks (pre : String) : List (Char × Ir.Color) :=
    let (d, _) := Bib.apply #[] (elabStr (doc pre)).1 Bib.plainReading
    let lines := (bodyLines (layoutOf fs d)).toList.filter fun l =>
      l.segs.any fun s => match s with
        | .run _ _ _ _ gs _ _ _ _ _ _ => gs.any (·.2.1 == 'S')
        | _ => false
    lines.flatMap fun l => l.segs.toList.flatMap fun s => match s with
      | .run _ c _ _ gs _ _ _ _ _ _ => gs.toList.map fun g => (g.2.1, c)
      | _ => []
  let inkOf (xs : List (Char × Ir.Color)) (c : Char) : List Ir.Color :=
    (xs.filter (·.1 == c)).map (·.2)
  let red : Ir.Color := { r := 255, g := 0, b := 0 }
  let green : Ir.Color := { r := 0, g := 255, b := 0 }
  let blue : Ir.Color := { r := 0, g := 0, b := 255 }
  let black := Ir.Color.black
  let magenta : Ir.Color := ((default : Ir.Palette).resolve "magenta").getD black
  -- '1' is the reference and the citation mark, 'x' the URL's, 'Z' the `\hyperlink`'s.
  let dflt := inks "\\usepackage[colorlinks]{hyperref}"
  t "colorlinks: the reference, then the citation, in red and green"
    (inkOf dflt '1' == [red, green])
  t "colorlinks: the URL in magenta" (!(inkOf dflt 'x').isEmpty && (inkOf dflt 'x').all (· == magenta))
  -- An internal `\hyperlink` is a cross-reference, painted in `linkcolor`.
  t "colorlinks: the internal \\hyperlink text in link ink (red)"
    (!(inkOf dflt 'Z').isEmpty && (inkOf dflt 'Z').all (· == red))
  t "colorlinks: the citation's brackets and the words keep the running ink"
    ((inkOf dflt '[').all (· == black) && (inkOf dflt ']').all (· == black) &&
      (inkOf dflt 'S').all (· == black))
  let set := inks "\\usepackage{hyperref}\n\\hypersetup{colorlinks, urlcolor=blue, citecolor=red}"
  t "hypersetup: a declared colour replaces its kind's default, the others keep theirs"
    (inkOf set '1' == [red, red] && (inkOf set 'x').all (· == blue))
  let all := inks "\\usepackage[colorlinks, allcolors=blue]{hyperref}"
  t "allcolors: every kind in the one colour" (inkOf all '1' == [blue, blue] && (inkOf all 'x').all (· == blue))
  for pre in ["\\usepackage{hyperref}", "\\usepackage[hidelinks]{hyperref}",
      "\\usepackage{hyperref}\n\\hypersetup{urlcolor=blue}"] do
    let xs := inks pre
    t s!"no colorlinks, no link ink: {pre}" (xs.all (·.2 == black) && !xs.isEmpty)
  -- HTML: the same ink, inside the link, on the link's own text.
  let html := (HtmlDoc.emit {} (Bib.apply #[] (elabStr (doc
    "\\usepackage[colorlinks]{hyperref}")).1 Bib.plainReading).1).1
  t "colorlinks: the HTML links carry their kinds' ink"
    (hasStr html (HtmlDoc.cssColor red) && hasStr html (HtmlDoc.cssColor magenta) &&
      hasStr html (HtmlDoc.cssColor green))
  -- A coloured link keeps its name and role.
  t "colorlinks: the HTML link keeps its href and visible text"
    (hasStr html "href=\"https://example.org\"" && hasStr html "https://example.org")
