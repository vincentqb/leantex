module

public import Tests.Layout

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- `\hspace` is the shared affine glue at the measure where it stands. -/
def hspaceAffineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let para (body : String) : Option (Array Ir.Inline) :=
    match (elabStr (metricDoc body)).1.body with
    | #[.para xs] => some xs
    | _ => none
  let ptGlue (n : Int) : Dim.SymGlue := { width := .ofLength (Dim.pt n) }
  t "hspace carries one affine value instead of its source text"
    (para "Alpha\\hspace{6pt}Bravo" ==
      some #[.text "Alpha", .hspace (.lit (ptGlue 6)) false, .text "Bravo"] &&
      (dvE (metricDoc "Alpha\\hspace{6pt}Bravo")).isEmpty)
  t "hspace finite stretch and shrink use the same typed glue"
    (para "Alpha\\hspace{1em plus 2pt minus 1pt}Bravo" ==
      some #[.text "Alpha", .hspace (.lit {
        width := { em := 1000 }, stretch := { sp := Dim.pt 2 },
        shrink := { sp := Dim.pt 1 } }) false, .text "Bravo"])
  t "hspace fill spellings normalize to the existing fill node"
    (para "a\\hspace{\\fill}b" == some #[.text "a", .fill, .text "b"] &&
      para "a\\hspace{\\stretch{1}}b" == some #[.text "a", .fill, .text "b"] &&
      para "a\\hspace{0pt plus 1fill}b" == some #[.text "a", .fill, .text "b"])
  let localElab := elabStr (metricDoc
    "\\begin{minipage}{100pt}A\\hspace{0.5\\linewidth + 3pt}B\\end{minipage}")
  let localOut := layoutOf oneFace localElab.1
  let localGaps := (bodyLines localOut).flatMap metricInnerGaps
  t s!"hspace resolves linewidth at its minipage, not the outer page ({reprStr localGaps})"
    (localGaps == #[Dim.pt 53])
  let negative := metricOut oneFace "Alpha\\hspace{-2pt}Bravo"
  t "a negative hspace pulls the following ink back"
    ((bodyLines negative).flatMap metricInnerGaps == #[Dim.pt (-2)])
  let starred := bodyLines (metricOut oneFace "Alpha\\\\\\hspace*{1cm}Bravo")
  let plain := bodyLines (metricOut oneFace "Alpha\\\\\\hspace{1cm}Bravo")
  let firstInk (l : Layout.LineOut) : Option Dim.Length := ((metricRunsAt l)[0]?).map (·.2)
  t "the star keeps hspace after a line break; plain glue is discarded"
    (starred.size == 2 && plain.size == 2 &&
      (starred[1]?.bind firstInk) == (starred[1]?.map (·.x + Dim.mm 10)) &&
      (plain[1]?.bind firstInk) == (plain[1]?.map (·.x)))
  let ds := dvE (metricDoc "a\\hspace{unknown}b\\hspace{alsoUnknown}c")
  t "each unreadable hspace is named at its own site"
    ((ds.filter (·.code == "E0331")).size == 2)
  let html := (HtmlDoc.emit {} (elabStr (metricDoc
    "\\begin{minipage}{100pt}a\\hspace{0.5\\linewidth + 3pt}b\\end{minipage}")).1).1
  t "HTML carries an affine hspace as inline room"
    (hasStr html s!"margin-inline-start:calc(50% + {(Dim.pt 3).toBpString}pt)")

/-- `\rule` paints the typed rectangle at its local measure. -/
def inlineRuleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := "\\begin{minipage}{100pt}A\\rule[1pt]{0.5\\linewidth - 3pt}{4pt}B\\end{minipage}"
  let ds := dvE (metricDoc src)
  let out := metricOut oneFace src
  t "rule is a native command with no length or unknown-command loss"
    (ds.all fun d => d.severity != .error && d.code != "W0301")
  t "rule resolves its width against the minipage and ships its rectangle"
    (metricRuleSegs out == #[(Dim.pt 47, Dim.pt 4, Dim.pt 1, Ir.Color.black)])
  t "rule contributes no source spelling to the page"
    ((bodyLines out).all fun l => (metricRunsAt l).all fun (s, _) =>
      !hasStr s "linewidth" && !hasStr s "pt")
  let html := (HtmlDoc.emit {} (elabStr (metricDoc src)).1).1
  t "HTML carries the rule's width, height, raise and paint"
    (hasStr html s!"inline-size:calc(50% - {(Dim.pt 3).toBpString}pt)" &&
      hasStr html s!"block-size:{(Dim.pt 4).toBpString}pt" &&
      hasStr html s!"vertical-align:{(Dim.pt 1).toBpString}pt" &&
      hasStr html "background:currentColor")
  t "markdown keeps surrounding text and no metric spelling"
    (MarkdownDoc.inlineText #[.text "A", .rule (.lit (ptGlue 4))
      (.lit (ptGlue 1)) (.lit {}) , .text "B"] == "AB")
  let nonlinear := dvE (metricDoc "A\\rule{\\linewidth * \\columnwidth}{1pt}B")
  t "nonlinear rule arithmetic is refused by name"
    (nonlinear.any fun d => d.code == "E0331" && hasStr d.message "length times a length")
  let register := dvE (metricDoc "A\\rule{\\wd\\strutbox}{1pt}B")
  t "register rule arithmetic is refused by name"
    (register.any fun d => d.code == "E0331" && hasStr d.message "register")
where
  ptGlue (n : Int) : Dim.SymGlue := { width := .ofLength (Dim.pt n) }

/-- A document's `pt` is TeX's point: `\the` prints what TeX prints, and a big point stays PDF's. -/
def pointDoorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := "\\documentclass{article}\n\\newlength\\la\\setlength\\la{10pt}\n" ++
    "\\begin{document}\n\\edef\\x{\\the\\la}A\\x B\n\\end{document}\n"
  let txt := match (elabStr src).1.body with
    | #[.para xs] => Ir.plainText xs
    | _ => ""
  -- lualatex 1.24: `\the` of a length set to 10pt prints 10.0pt.
  t s!"\\the of 10pt prints TeX's 10.0pt ({txt})" (txt == "A10.0ptB")
  t "72.27 TeX points and 72 big points are each an inch"
    (Decl.parseLength "72.27pt" == some (.ofLength (Dim.inch 1)) &&
      Decl.parseLength "72bp" == some (.ofLength (Dim.inch 1)))

/-- A TeX length reads and prints as TeX reads and prints it: each term on TeX's grid of scaled
points, a pixel a big point, a `\dimexpr` division rounded and calc's truncated. -/
def texLengthChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- lualatex 1.24 prints each `\the` of the length set to its spelling.
  let cases : List (String × String) :=
    [("3.5truein", "252.94499pt"), ("1px", "1.00374pt"), ("1bp", "1.00374pt"), ("1cm", "28.45274pt"),
     ("1mm", "2.84526pt"), ("1dd", "1.07pt"), ("1cc", "12.8401pt"), ("1pc", "12.0pt"),
     ("0.33333333333333333333pt", "0.33333pt"), ("12345sp", "0.18837pt"), ("-1.5in", "-108.405pt"),
     ("2.5\\lb", "2.50934pt"), ("-0.7\\la", "-35.41199pt"),
     ("\\dimexpr\\la*2/3\\relax", "33.72585pt"), ("\\dimexpr\\la/7\\relax", "7.22697pt"),
     ("\\dimexpr-\\la/7\\relax", "-7.22697pt"), ("\\la/7", "7.22696pt"), ("-\\la/7", "-7.22696pt"),
     ("\\la*3/7", "21.6809pt"), ("\\dimexpr(\\la+1bp)*2\\relax", "103.18503pt"),
     ("1bp+1bp", "2.00748pt"), ("\\la-2.25cm", "-13.42992pt"), ("7.2bp", "7.22699pt"),
     ("0.1in", "7.22743pt"), ("25.4mm", "72.26997pt")]
  for (spelled, printed) in cases do
    let src := "\\documentclass{article}\n\\usepackage{calc}\n\\newlength\\la\\setlength\\la{50.58878pt}\n" ++
      "\\newlength\\lb\\setlength\\lb{1bp}\\newlength\\lt\\setlength\\lt{" ++ spelled ++ "}\n" ++
      "\\begin{document}\n\\edef\\x{\\the\\lt}A\\x B\n\\end{document}\n"
    let txt := match (elabStr src).1.body with
      | #[.para xs] => Ir.plainText xs
      | _ => ""
    t s!"\\the of {spelled} prints TeX's {printed} ({txt})" (txt == s!"A{printed}B")
  t "a TeX document's pixel is a big point" (Decl.parseLength "3px" == some (.ofLength (Dim.bp 3)))
  -- lualatex 1.24: an edef's dimexpr rounds its division; a dimension past TeX's largest is refused.
  let edefOf (body : String) : String × Nat :=
    let (doc, ds) := elabStr ("\\documentclass{article}\n\\newlength\\la\\setlength\\la{50.58878pt}\n" ++
      "\\newlength\\lh\\setlength\\lh{20000pt}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n")
    (match doc.body with
      | #[.para xs] => Ir.plainText xs
      | _ => "", (ds.filter (·.code == "W0357")).size)
  for (body, printed) in [("\\edef\\x{\\the\\dimexpr\\la/7\\relax}A\\x B", "A7.22697ptB"),
      ("\\edef\\x{\\the\\dimexpr-\\la*3/7\\relax}A\\x B", "A-21.68091ptB"),
      ("\\edef\\x{\\the\\dimexpr\\la/7 }A\\x B", "A7.22697ptB")] do
    t s!"an edef's {body} prints {printed}" ((edefOf body).1 == printed)
  t "a dimension past TeX's largest is refused by name, never printed"
    ((edefOf "\\edef\\x{\\the\\lh}A\\x B").2 == 1)
  t "a length times or over a whole number reads, over a fraction it is refused, as TeX refuses it"
    (Decl.texLength (fun _ => some 1000) "\\la*3/2" == some 1500 &&
      Decl.texLength (fun _ => some 1000) "\\la*1.5" == none &&
      Decl.texLength (fun _ => some 1000) "\\la/2.5" == none)
