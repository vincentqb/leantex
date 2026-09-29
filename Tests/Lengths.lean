import Tests.Layout

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- `\hspace` is the shared affine glue at the measure where it stands. -/
def hspaceAffineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let para (body : String) : Option (Array Ir.Inline) :=
    match (elabStr (metricDoc body)).1.body with
    | #[.para xs] => some xs
    | _ => none
  let ptGlue (n : Int) : Dim.SymGlue := { width := .ofSp (Dim.pt n) }
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
  t s!"hspace resolves linewidth at its minipage, not the outer page ({localGaps})"
    (localGaps == #[Dim.pt 53])
  let negative := metricOut oneFace "Alpha\\hspace{-2pt}Bravo"
  t "a negative hspace pulls the following ink back"
    ((bodyLines negative).flatMap metricInnerGaps == #[Dim.pt (-2)])
  let starred := bodyLines (metricOut oneFace "Alpha\\\\\\hspace*{1cm}Bravo")
  let plain := bodyLines (metricOut oneFace "Alpha\\\\\\hspace{1cm}Bravo")
  let firstInk (l : Layout.LineOut) : Option Dim.Sp := ((metricRunsAt l)[0]?).map (·.2)
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
    (hasStr html "margin-inline-start:calc(50% + 3pt)")

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
    (hasStr html "inline-size:calc(50% - 3pt)" && hasStr html "block-size:4pt" &&
      hasStr html "vertical-align:1pt" && hasStr html "background:currentColor")
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
  ptGlue (n : Int) : Dim.SymGlue := { width := .ofSp (Dim.pt n) }
