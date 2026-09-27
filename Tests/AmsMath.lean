import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A `gridEnvs` row's probe: the cells `a`–`d` in the shape its column
model takes — one column for `gather` and a one-column spec, two otherwise. -/
def gridProbeBody (kind : Math.GridKind) : String :=
  let oneCol := match kind with
    | .gather => true
    | .array cols => cols.size == 1
    | .align => false
  if oneCol then "a \\\\ c" else "a & b \\\\ c & d"

def gridProbeCall (env : String) (kind : Math.GridKind) : String :=
  if env == "substack" then s!"$\\substack\{{gridProbeBody kind}}$"
  else s!"$\\begin\{{env}}{gridProbeBody kind}\\end\{{env}}$"

/-- amsmath's grid environments are the grids their definitions build
(`MathParse.gridEnvs`, one row per environment, sourced to amsmath.sty).

* **Each row is its definition.** The formula equals the one amsmath.sty's
  own expansion spells with the engine's `array` and `\left…\right`, or,
  for an alignment, the display alignment of the same column model. The
  expansions are the reference, written from amsmath.sty rather than from
  the table, so a row whose data drifts fails here.
* **Each row ships its cells and delimiters, and nothing of its source**:
  the glyphs the PDF's page carries and the HTML's text content are the
  cells in reading order between the row's delimiters, with no diagnostic —
  on the base engine the source text shipped instead, under W0012. -/
def amsGridChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let cells := "a & b \\\\ c & d"
  let arr := s!"\\begin\{array}\{cccccccccc}{cells}\\end\{array}"
  let expansions : List (String × String) := [
    ("matrix", s!"${arr}$"),
    ("pmatrix", s!"$\\left({arr}\\right)$"),
    ("bmatrix", s!"$\\left[{arr}\\right]$"),
    ("Bmatrix", s!"$\\left\\\{{arr}\\right\\}$"),
    ("vmatrix", s!"$\\left|{arr}\\right|$"),
    ("Vmatrix", s!"$\\left\\|{arr}\\right\\|$"),
    ("cases", s!"$\\left\\\{\\begin\{array}\{ll}{cells}\\end\{array}\\right.$"),
    ("aligned", s!"\\begin\{align*}{cells}\\end\{align*}"),
    ("gathered", "\\begin{gather*}a \\\\ c\\end{gather*}"),
    ("split", s!"\\begin\{align*}{cells}\\end\{align*}"),
    ("substack", "$\\begin{array}{c}a \\\\ c\\end{array}$")]
  t "amsmath grids: every row has its reference expansion, and no other"
    (expansions.map (·.1) == MathParse.gridEnvs.map (·.1))
  let mathLetter (c : Char) : Char := MathParse.italicVar c
  for (env, kind, l, r) in MathParse.gridEnvs do
    let call := gridProbeCall env kind
    let (doc, ds) := elabStr (dvDoc "" call)
    t s!"amsmath grid {env}: no diagnostic" ds.isEmpty
    let reference := (expansions.lookup env).getD ""
    t s!"amsmath grid {env}: the formula its definition expands to"
      ((firstFormula doc).isSome &&
        firstFormula doc == firstFormula (elabStr (dvDoc "" reference)).1)
    let body := (gridProbeBody kind).toList.filter Char.isAlpha
    let expected := String.ofList <|
      (l.toList ++ body.map mathLetter ++ r.toList)
    let shipped := String.ofList ((pageTextOf fs (dvDoc "" call)).toList.filter
      (!·.isWhitespace))
    t s!"amsmath grid {env}: the page ships its cells between its delimiters \
(got '{shipped}')" (shipped == expected)
    let (_, html, _) := HtmlDoc.emitTree {} doc
    let text := String.ofList ((nodeTextList "" html.toList).toList.filter
      (!·.isWhitespace))
    t s!"amsmath grid {env}: the HTML carries its cells between its delimiters \
(got '{text}')" (text == expected)
  -- An alignment sets its cells in display style wherever it stands
  -- (amsmath.sty, `\start@aligned` and `gathered`: `$\m@th\displaystyle{##}$`),
  -- so a fraction in an inline `aligned` sets its numerator at the formula's
  -- own size, where an inline fraction's is a script size.
  let glyphSizes (src : String) : Array Dim.Sp :=
    let (d, _) := elabStr src
    (bodyLines (layoutOf fs d)).flatMap fun l => l.segs.filterMap fun s =>
      match s with
      | .run _ _ _ _ glyphs sz _ _ _ _ => if glyphs.isEmpty then none else some sz
      | _ => none
  let oneSize (xs : Array Dim.Sp) : Bool :=
    !xs.isEmpty && xs.all (· == xs[0]!)
  let inlineFrac := dvDoc "" "$x\\frac{a}{b}$"
  let alignedFrac := dvDoc "" "$x\\begin{aligned}\\frac{a}{b}\\end{aligned}$"
  t "amsmath alignment: an inline fraction's parts set smaller than the formula"
    (!oneSize (glyphSizes inlineFrac))
  t "amsmath alignment: an inline aligned cell sets in display style"
    ((elabStr alignedFrac).2.isEmpty && oneSize (glyphSizes alignedFrac))
  t "amsmath alignment: the HTML table restores display style inline"
    (hasStr (HtmlDoc.emit {} (elabStr alignedFrac).1).1 "<mtable displaystyle=\"true\">")

def amsmathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let serif ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"amsmath: serif unparsable: {e}")
  let fs ← mathSetOf (oneFaceOf serif)
  amsGridChecks ref fs
