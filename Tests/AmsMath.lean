import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A `gridEnvs` row's probe: the cells `a`–`d` in the shape its column
model takes — one column for `gather` and a one-column spec, two otherwise. -/
def gridProbeBody (kind : Math.GridKind) : String :=
  let oneCol := match kind with
    | .gather => true
    | .array cols _ => cols.size == 1
    | .align => false
  if oneCol then "a \\\\ c" else "a & b \\\\ c & d"

def gridProbeCall (env : String) (kind : Math.GridKind) : String :=
  if env == "substack" then s!"$\\substack\{{gridProbeBody kind}}$"
  else s!"$\\begin\{{env}}{gridProbeBody kind}\\end\{{env}}$"

/-- The formula with its delimited grid's `\arraystretch` set to `s`: how a
reference spelled with `array`, whose surface reads no stretch, states a
definition that declares one (`cases`). -/
def restretch (s : Nat) : Math.MList → Math.MList
  | .cons (.atom c (.delim l r (.cons (.atom c' (.grid (.array cols _) rows)
      sup sub lim) .nil)) sup' sub' lim') .nil =>
    .cons (.atom c (.delim l r (.cons (.atom c' (.grid (.array cols s) rows)
      sup sub lim) .nil)) sup' sub' lim') .nil
  | l => l

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
  let expansions : List (String × String × Nat) := [
    ("matrix", s!"${arr}$", 1000),
    ("pmatrix", s!"$\\left({arr}\\right)$", 1000),
    ("bmatrix", s!"$\\left[{arr}\\right]$", 1000),
    ("Bmatrix", s!"$\\left\\\{{arr}\\right\\}$", 1000),
    ("vmatrix", s!"$\\left|{arr}\\right|$", 1000),
    ("Vmatrix", s!"$\\left\\|{arr}\\right\\|$", 1000),
    -- `\env@cases` also sets `\def\arraystretch{1.2}`
    ("cases", s!"$\\left\\\{\\begin\{array}\{ll}{cells}\\end\{array}\\right.$", 1200),
    ("aligned", s!"\\begin\{align*}{cells}\\end\{align*}", 1000),
    ("gathered", "\\begin{gather*}a \\\\ c\\end{gather*}", 1000),
    ("split", s!"\\begin\{align*}{cells}\\end\{align*}", 1000),
    ("substack", "$\\begin{array}{c}a \\\\ c\\end{array}$", 1000)]
  t "amsmath grids: every row has its reference expansion, and no other"
    (expansions.map (·.1) == MathParse.gridEnvs.map (·.1))
  let mathLetter (c : Char) : Char := MathParse.italicVar c
  for (env, kind, l, r) in MathParse.gridEnvs do
    let call := gridProbeCall env kind
    let (doc, ds) := elabStr (dvDoc "" call)
    t s!"amsmath grid {env}: no diagnostic" ds.isEmpty
    let (reference, stretch) := (expansions.lookup env).getD ("", 1000)
    t s!"amsmath grid {env}: the formula its definition expands to"
      ((firstFormula doc).isSome && firstFormula doc ==
        (firstFormula (elabStr (dvDoc "" reference)).1).map (restretch stretch))
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
  -- A lone fence never grows: TeX stretches a delimiter only under
  -- `\left`/`\right`, while MathML Core's operator dictionary makes every
  -- fence stretchy, so beside a grown brace `f(x)`'s parentheses ballooned.
  let fx := (HtmlDoc.emit {} (elabStr (dvDoc ""
    "\\[ f(x) = \\begin{cases} 1 & a \\\\ 0 & b \\end{cases} \\]")).1).1
  t "amsmath grids: a lone fence keeps its size beside a grown one in HTML"
    (hasStr fx "<mo stretchy=\"false\">(</mo>" &&
      hasStr fx "<mo stretchy=\"true\" symmetric=\"true\">{</mo>")
  -- `cases` sets `\arraystretch` 1.2 (`\env@cases`), so its rows stand 1.2
  -- times an array's pitch apart on the page: the raise of the first row's
  -- cell over the second's, read off the shipped runs.
  let pitchOf (src : String) : Option Dim.Sp := do
    let (d, _) := elabStr src
    let raises := (bodyLines (layoutOf fs d)).flatMap fun l => l.segs.filterMap
      fun s => match s with
        | .run _ _ _ _ glyphs _ _ raise _ _ =>
          if glyphs.any (·.2 == MathParse.italicVar 'a') then some (0, raise)
          else if glyphs.any (·.2 == MathParse.italicVar 'c') then some (1, raise)
          else none
        | _ => none
    let ra ← raises.find? (·.1 == 0)
    let rc ← raises.find? (·.1 == 1)
    return ra.2 - rc.2
  let casesPitch := pitchOf (dvDoc "" "$\\begin{cases} a & b \\\\ c & d \\end{cases}$")
  let arrayPitch := pitchOf (dvDoc ""
    "$\\left\\{\\begin{array}{ll} a & b \\\\ c & d \\end{array}\\right.$")
  t s!"amsmath cases: rows stand 1.2 array pitches apart \
(cases {casesPitch}, array {arrayPitch})"
    (match casesPitch, arrayPitch with
      | some c, some a => a > 0 && c == a * 1200 / 1000
      | _, _ => false)
  t "amsmath cases: the HTML cells take the stretch as padding"
    (hasStr (HtmlDoc.emit {} (elabStr (dvDoc ""
      "$\\begin{cases} a & b \\\\ c & d \\end{cases}$")).1).1
      "padding-top: calc(0.5ex + 0.120em)")

def amsmathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let serif ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"amsmath: serif unparsable: {e}")
  let fs ← mathSetOf (oneFaceOf serif)
  amsGridChecks ref fs
