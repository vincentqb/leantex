import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A `gridEnvs` row's probe: the cells `a`–`d` in the shape its column
model takes — one column for `gather` and a one-column spec, two otherwise. -/
def gridProbeBody (kind : Math.GridKind) : String :=
  let oneCol := match kind with
    | .gather => true
    | .array cols _ => cols.size == 1
    | .align | .small => false
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

/-- The formula with its undelimited grid set as `smallmatrix`'s: how a
reference spelled with `matrix`'s `array` states the cells `smallmatrix`
sets in its own grid. -/
def resmall : Math.MList → Math.MList
  | .cons (.atom c (.grid (.array _ _) rows) sup sub lim) .nil =>
    .cons (.atom c (.grid .small rows) sup sub lim) .nil
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
  let expansions : List (String × String × (Math.MList → Math.MList)) := [
    ("matrix", s!"${arr}$", restretch 1000),
    ("pmatrix", s!"$\\left({arr}\\right)$", restretch 1000),
    ("bmatrix", s!"$\\left[{arr}\\right]$", restretch 1000),
    ("Bmatrix", s!"$\\left\\\{{arr}\\right\\}$", restretch 1000),
    ("vmatrix", s!"$\\left|{arr}\\right|$", restretch 1000),
    ("Vmatrix", s!"$\\left\\|{arr}\\right\\|$", restretch 1000),
    -- `\env@cases` also sets `\def\arraystretch{1.2}`
    ("cases", s!"$\\left\\\{\\begin\{array}\{ll}{cells}\\end\{array}\\right.$",
      restretch 1200),
    ("aligned", s!"\\begin\{align*}{cells}\\end\{align*}", restretch 1000),
    ("gathered", "\\begin{gather*}a \\\\ c\\end{gather*}", restretch 1000),
    ("split", s!"\\begin\{align*}{cells}\\end\{align*}", restretch 1000),
    ("substack", "$\\begin{array}{c}a \\\\ c\\end{array}$", restretch 1000),
    -- `smallmatrix` is its own grid: the matrix's cells, set as it sets them
    ("smallmatrix", s!"${arr}$", resmall)]
  t "amsmath grids: every row has its reference expansion, and no other"
    (expansions.map (·.1) == MathParse.gridEnvs.map (·.1))
  let mathLetter (c : Char) : Char := MathParse.italicVar c
  for (env, kind, l, r) in MathParse.gridEnvs do
    let call := gridProbeCall env kind
    let (doc, ds) := elabStr (dvDoc "" call)
    t s!"amsmath grid {env}: no diagnostic" ds.isEmpty
    let (reference, shape) := (expansions.lookup env).getD ("", id)
    t s!"amsmath grid {env}: the formula its definition expands to"
      ((firstFormula doc).isSome && firstFormula doc ==
        (firstFormula (elabStr (dvDoc "" reference)).1).map shape)
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
      | .run _ _ _ _ glyphs sz _ _ _ _ _ => if glyphs.isEmpty then none else some sz
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
        | .run _ _ _ _ glyphs _ _ _ raise _ _ =>
          if glyphs.any (·.2.1 == MathParse.italicVar 'a') then some (0, raise)
          else if glyphs.any (·.2.1 == MathParse.italicVar 'c') then some (1, raise)
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
  -- `smallmatrix` against lualatex's \showbox of the same formulas under the
  -- test face (FiraMath, unicode-math, 10pt; 2026-09-28), in thousandths of
  -- the formula's size: cells at the face's script size (7.2 of 10), a thin
  -- space each side and a thick one between columns (`a\\c` is 7.43 wide,
  -- `a&b\\a&b` 14.38), rows `6\ex@` apart (`a\\c`) unless their boxes would
  -- come within `1.5\ex@` (`a&b\\c&d`: 0.09 + 1.5 + 5.39). ±1 is \showbox's
  -- rounding. Every row failed before smallmatrix was its own grid, where the
  -- environment was the parser's decline (W0012).
  let small (cells : String) : String :=
    dvDoc "" s!"$\\begin\{smallmatrix}{cells}\\end\{smallmatrix}$"
  let near (a b : Int) : Bool := (a - b).natAbs ≤ 1
  let runsOf (src : String) : Array (Dim.Sp × Bool × Dim.Sp) :=
    (bodyLines (layoutOf fs (elabStr src).1)).flatMap fun l => l.segs.filterMap fun s =>
      match s with
      | .run _ _ _ w glyphs sz _ _ _ _ _ => some (w, !glyphs.isEmpty, sz)
      | _ => none
  match (glyphSizes (dvDoc "" "$x$"))[0]? with
  | none => t "amsmath smallmatrix: the formula size was read" false
  | some size =>
    let permille (x : Dim.Sp) : Int := x * 1000 / size
    let width (src : String) : Int := permille ((runsOf src).foldl (· + ·.1) 0)
    t "amsmath smallmatrix: its cells set at the script size"
      ((elabStr (small "a&b\\\\c&d")).2.isEmpty &&
       ((runsOf (small "a&b\\\\c&d")).filter (·.2.1)).all (near 720 <| permille ·.2.2))
    t "amsmath smallmatrix: a thin space each side, a thick one between columns"
      (near (width (small "a\\\\c")) 743 && near (width (small "a&b\\\\a&b")) 1438)
    t "amsmath smallmatrix: rows stand 6\\ex@ apart, or 1.5\\ex@ clear"
      (((pitchOf (small "a\\\\c")).map permille).any (near 600) &&
       ((pitchOf (small "a&b\\\\c&d")).map permille).any (near 697))
  t "amsmath smallmatrix: the HTML table sets its cells a script level down"
    (hasStr (HtmlDoc.emit {} (elabStr (small "a&b\\\\c&d")).1).1
      "<mtable scriptlevel=\"1\"")

/-- `\tag{t}` stands in the number's place — `(t)`, or `t` under `\tag*` —
and steps no counter; a label binds to the tag, so `\eqref` reads it
(amsldoc §3.4). Where no number is rendered yet (an alignment's rows) the
tag is named, never set inside the formula. -/
def amsTagChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let squash (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
  let v (c : Char) : Char := MathParse.italicVar c
  let src := dvDoc "" ("\\begin{equation}x\\tag{5}\\label{e}\\end{equation}\n" ++
    "\\begin{equation}y\\end{equation}\n" ++
    "\\begin{equation*}z\\tag*{A}\\end{equation*}\n\n\\eqref{e}")
  let (doc, ds) := elabStr src
  t "amsmath tag: no diagnostic" ds.isEmpty
  let page := squash (pageTextOf fs src)
  t s!"amsmath tag: the tag stands in the number's place, steps no counter, and \
\\eqref reads it (got '{page}')"
    (page == String.ofList [v 'x', '(', '5', ')', v 'y', '(', '1', ')', v 'z', 'A',
      '(', '5', ')'])
  let html := (HtmlDoc.emit {} doc).1
  t "amsmath tag: the HTML number spans carry the tags"
    (hasStr html "<span class=\"eqnum\">(5)</span>" &&
      hasStr html "<span class=\"eqnum\">(1)</span>" &&
      hasStr html "<span class=\"eqnum\">A</span>")
  let aligned := dvDoc "" "\\begin{align*}x &= y\\tag{3}\\end{align*}"
  t "amsmath tag: an alignment's tag is named, never set inside the formula"
    ((warnCodes aligned).contains "W0015" && !(pageTextOf fs aligned).contains '3')
  -- amsmath's `\[` is `equation*` (amsmath.sty:
  -- `\DeclareRobustCommand{\[}{\begin{equation*}}`): one construct under two
  -- spellings, so every body elaborates to one document and one accounting
  -- under both. `\[`'s own arm once dropped a tag, silently.
  for body in ["a = b", "a = b \\label{k}", "a = b \\tag{A}", "a = b \\tag*{B}",
      "\\label{k} a = b \\tag{A}", "a = b \\nonumber"] do
    let (bd, bds) := elabStr (dvDoc "" s!"Text.\n\\[ {body} \\]\nMore \\ref\{k}.")
    let (ed, eds) := elabStr (dvDoc ""
      s!"Text.\n\\begin\{equation*} {body} \\end\{equation*}\nMore \\ref\{k}.")
    t s!"amsmath tag: '\\[ {body} \\]' is equation*"
      (bd == ed && bds.map (·.code) == eds.map (·.code))
  let bracket := dvDoc "" "\\[ a = b \\tag{A} \\]"
  let bracketPage := squash (pageTextOf fs bracket)
  t s!"amsmath tag: '\\[ … \\tag \\]' sets its tag in the number's place \
(got '{bracketPage}')"
    ((dvE bracket).isEmpty &&
      bracketPage == String.ofList [v 'a', '=', v 'b', '(', 'A', ')'])
  t "amsmath tag: the HTML number span of '\\[ … \\tag \\]' carries the tag"
    (hasStr (HtmlDoc.emit {} (elabStr bracket).1).1 "<span class=\"eqnum\">(A)</span>")

mutual

/-- Every `span.eqnum` of an emitted tree, in document order: the number
beside each numbered display, as the HTML ships it. -/
def eqnumSpansOne (acc : Array Html.Node) : Html.Node → Array Html.Node
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    if tag == "span" && attrs.contains ("class", "eqnum") then acc.push (.elem tag attrs kids)
    else eqnumSpansList acc kids.toList

def eqnumSpansList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | k :: rest => eqnumSpansList (eqnumSpansOne acc k) rest

end

mutual

/-- Does a subtree hold an element with this tag? -/
def hasElemOne (tag : String) : Html.Node → Bool
  | .text _ | .style _ | .script _ _ => false
  | .elem t _ kids => t == tag || hasElemList tag kids.toList

def hasElemList (tag : String) : List Html.Node → Bool
  | [] => false
  | k :: rest => hasElemOne tag k || hasElemList tag rest

end

/-- A tag's argument is text set in an `\hbox` (amsmath's `\tagform@` and
`\maketag@@@`): markup and math in it are ink, never source. One argument
per kind — math, a command, text with a script, a reference with a prime —
each read off the laid page as face and scalar per glyph, and off the HTML
number span's tree; a label on a tag binds the tag's text, not its source.
On the base engine each shipped its argument's source as text, silently. -/
def amsTagTextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fs ← serifFacesSet
    | t "amsmath tag text: the serif faces and the math face load" false
  let (roman, bold, math) := (0, 1, 4)
  let v (c : Char) : Char := MathParse.italicVar c
  let ast := ((MathParse.ctrlAtom.lookup "ast").map (·.2)).getD '?'
  let glyphs (src : String) : Array (Nat × Char × Dim.Sp) :=
    (bodyLines (layoutOf fs (elabStr src).1)).flatMap fun l => l.segs.flatMap fun s =>
      match s with
      | .run idx _ _ _ gs _ _ _ raise _ _ => gs.map fun g => (idx, g.2.1, raise)
      | _ => #[]
  let formula : List (Nat × Char) := [(math, v 'a'), (math, '='), (math, v 'b')]
  let cases : List (String × List (Nat × Char) × String × String) := [
    ("$\\ast$", [(roman, '('), (math, ast), (roman, ')')], s!"({ast})", "math"),
    ("\\textbf{C}", [(roman, '('), (bold, 'C'), (roman, ')')], "(C)", "strong"),
    ("C$_1$", [(roman, '('), (roman, 'C'), (math, '1'), (roman, ')')], "(C1)", "msub")]
  for (arg, want, html, elem) in cases do
    let src := dvDoc "" s!"\\begin\{equation} a = b \\tag\{{arg}} \\end\{equation}"
    let got := (glyphs src).toList.map fun (i, c, _) => (i, c)
    t s!"amsmath tag text: \\tag\{{arg}} ships its argument as ink (got {got})"
      ((dvE src).isEmpty && got == formula ++ want)
    let (_, tree, _) := HtmlDoc.emitTree {} (elabStr src).1
    let spans := eqnumSpansList #[] tree.toList
    t s!"amsmath tag text: the HTML number span of \\tag\{{arg}} is its ink"
      (spans.size == 1 && spans.all fun s => nodeTextOne "" s == html && hasElemOne elem s)
  t "amsmath tag text: a tag's script is a script"
    ((glyphs (dvDoc "" "\\begin{equation} a = b \\tag{C$_1$} \\end{equation}")).any
      fun (i, c, r) => i == math && c == '1' && r < 0)
  -- A reference inside a tag resolves where the number stands, as amsmath's
  -- `\@currentlabel` is the tag's own text: `(1′)`, the prime a script.
  let primed := dvDoc "" ("\\begin{equation} x \\label{p} \\end{equation}\n" ++
    "\\begin{equation} y \\tag{\\ref{p}$'$} \\end{equation}")
  let pg := (glyphs primed).toList.map fun (i, c, _) => (i, c)
  t s!"amsmath tag text: a reference in a tag resolves beside its prime (got {pg})"
    ((dvE primed).isEmpty && pg == [(math, v 'x'), (roman, '('), (roman, '1'), (roman, ')'),
      (math, v 'y'), (roman, '('), (roman, '1'), (math, '\u2032'), (roman, ')')])
  -- A label on a tag binds the tag's text: `\eqref` reads the ink, not the
  -- argument's spelling.
  let labelled := dvDoc "" ("\\begin{equation} a = b \\label{d} \\tag{$\\ast$} \\end{equation}\n\n" ++
    "See \\eqref{d}.")
  let text := nodeTextList "" (HtmlDoc.emitTree {} (elabStr labelled).1).2.1.toList
  t s!"amsmath tag text: \\eqref reads a tag's ink (got '{text}')"
    ((dvE labelled).isEmpty && hasStr text s!"See ({ast}).")

/-- The control words a call spells: `\name` runs of letters. -/
def callCtrlWords (call : String) : List String := Id.run do
  let cs := call.toList
  let mut out : List String := []
  let mut i := 0
  for _ in [0:cs.length + 1] do
    if i ≥ cs.length then break
    if cs[i]! == '\\' then
      let name := (cs.drop (i + 1)).takeWhile Char.isAlpha
      unless name.isEmpty do out := ("\\" ++ String.ofList name) :: out
      i := i + 1 + name.length
    else i := i + 1
  return out

/-- An implemented amsmath row ships no source: no control word its call
spells reaches the laid page or the HTML text. The class the tag's
argument belonged to, where recognising the command changed the document
(so `compatRowEffect` held) and the change was its own spelling set as
text. -/
def amsIndexInkChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let content ← IO.FS.readFile "tests/compat-index/amsmath.txt"
  for line in content.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " with
    | place :: "impl" :: _ =>
      let call := (line.drop (place.length + " impl ".length)).toString
      let src := compatRowSrc "amsmath" place call
      let page := pageTextOf fs src
      let html := nodeTextList "" (HtmlDoc.emitTree {} (elabStr src).1).2.1.toList
      let leaked := (callCtrlWords call).filter fun w => hasStr page w || hasStr html w
      check ref s!"amsmath index: '{call}' ships its own source {leaked}" leaked.isEmpty
    | _ => pure ()

/-- amsmath's fractions are rows of one generalized fraction
(`MathParse.fracCmds`, from amsmath.sty's own `\genfrac` definitions).

* **Each row is its definition**: the formula equals `\genfrac` spelled
  with the row's arguments, written here from amsmath.sty; a row added
  without its reference fails.
* **A fraction spaces as the Ord its braces make**: `$x\cmd{a}{b}y$` sets
  exactly as wide as `$x{\cmd{a}{b}}y$`, since latex.ltx and amsmath.sty
  brace every fraction; the engine once set an Inner's thin space each side.
* **The style is the declared one**: an inline `\dfrac`'s parts set at the
  formula's own size, a displayed `\tfrac`'s at an inline fraction's.
* **A stack has no rule and grows its delimiters**: `\binom` ships its
  parentheses around stacked parts with no bar, each at least amsmath's
  fraction delimiter size (2.40 em displayed, 1.01 em otherwise); a
  declared thickness is the bar's; the MathML declares the same.

On the base engine `\dfrac` and `\tfrac` set as `\frac` in the current
style, silently, and `\binom` and `\genfrac` set their source as text. -/
def amsFracChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let expansions : List (String × String) := [
    ("frac", "\\genfrac{}{}{}{}"), ("dfrac", "\\genfrac{}{}{}{0}"),
    ("tfrac", "\\genfrac{}{}{}{1}"), ("binom", "\\genfrac{(}{)}{0pt}{}"),
    ("dbinom", "\\genfrac{(}{)}{0pt}{0}"), ("tbinom", "\\genfrac{(}{)}{0pt}{1}")]
  t "amsmath fractions: every row has its reference expansion, and no other"
    (expansions.map (·.1) == MathParse.fracCmds.map (·.1))
  let laid (src : String) : Array Layout.LineOut :=
    bodyLines (layoutOf fs (elabStr (dvDoc "" src)).1)
  let lineWidth (src : String) : Dim.Sp := (((laid src)[0]?).map (·.setWidth)).getD 0
  for (cmd, gen) in expansions do
    let (d, ds) := elabStr (dvDoc "" s!"$\\{cmd}\{a}\{b}$")
    t s!"amsmath fraction \\{cmd}: no diagnostic" ds.isEmpty
    t s!"amsmath fraction \\{cmd}: the formula its \\genfrac definition is"
      ((firstFormula d).isSome &&
        firstFormula d == firstFormula (elabStr (dvDoc "" s!"${gen}\{a}\{b}$")).1)
    let (w, wb) := (lineWidth s!"$x\\{cmd}\{a}\{b}y$", lineWidth s!"$x\{\\{cmd}\{a}\{b}}y$")
    t s!"amsmath fraction \\{cmd}: spaces as the Ord its braces make ({w} vs {wb})"
      (w > 0 && w == wb)
  let sizeOf (src : String) (c : Char) : Option Dim.Sp :=
    ((laid src).toList.flatMap fun l => l.segs.toList.filterMap fun s => match s with
      | .run _ _ _ _ gs sz _ _ _ _ _ => if gs.any (·.2.1 == c) then some sz else none
      | _ => none).head?
  let (a, x) := (MathParse.italicVar 'a', MathParse.italicVar 'x')
  t "amsmath fraction: an inline \\dfrac's parts set at the formula's size"
    ((sizeOf "$x\\dfrac{a}{b}$" a).isSome &&
      sizeOf "$x\\dfrac{a}{b}$" a == sizeOf "$x\\dfrac{a}{b}$" x)
  t "amsmath fraction: a displayed \\tfrac's parts set at an inline fraction's size"
    ((sizeOf "$x\\frac{a}{b}$" a).isSome &&
      sizeOf "\\[ x\\tfrac{a}{b} \\]" a == sizeOf "$x\\frac{a}{b}$" a &&
      sizeOf "\\[ x\\tfrac{a}{b} \\]" a != sizeOf "\\[ x\\tfrac{a}{b} \\]" x)
  let rules (src : String) : List Dim.Sp :=
    (laid src).toList.flatMap fun l => l.segs.toList.filterMap fun s => match s with
      | .rule _ th _ _ => some th
      | _ => none
  let mathGlyphs (src : String) : List (Nat × Char) :=
    (laid src).toList.flatMap fun l => l.segs.toList.flatMap fun s => match s with
      | .run idx _ _ _ gs _ _ _ _ _ _ => gs.toList.map fun g => (idx, g.2.1)
      | _ => []
  let mathFace := fs.math.getD 0
  t "amsmath binom: a stack sets its parts between its parentheses with no rule"
    ((rules "$\\binom{n}{k}$").isEmpty && (rules "$\\frac{n}{k}$").length == 1 &&
      mathGlyphs "$\\binom{n}{k}$" == ['(', MathParse.italicVar 'n',
        MathParse.italicVar 'k', ')'].map (mathFace, ·))
  t "amsmath genfrac: a declared thickness is the bar's"
    (rules "$\\genfrac{}{}{1pt}{}{a}{b}$" == [Dim.pt 1])
  -- The parenthesis's variant, read off the run and the face that set it.
  let parenExtent (src : String) : Option (Int × Nat) :=
    ((laid src).toList.flatMap fun l => l.segs.toList.filterMap fun s => match s with
      | .run idx _ _ _ gs _ _ _ _ _ _ => (gs.find? (·.2.1 == '(')).bind fun (g, _) =>
          (fs.fonts[idx]?).bind fun f =>
            (f.yExtent g).map fun (lo, hi) => (hi - lo, f.unitsPerEm)
      | _ => none).head?
  let inl := parenExtent "$\\binom{n}{k}$"
  let dsp := parenExtent "\\[ \\binom{n}{k} \\]"
  t s!"amsmath binom: each parenthesis covers the fraction delimiter size \
(inline {inl}, displayed {dsp})"
    (match inl, dsp with
      | some (hi, upem), some (hd, _) =>
        hi * 100 ≥ 101 * (upem : Int) && hd * 100 ≥ 240 * (upem : Int) && hd > hi
      | _, _ => false)
  let html (src : String) : String := (HtmlDoc.emit {} (elabStr (dvDoc "" src)).1).1
  t "amsmath binom: the MathML stacks with no rule between fixed-size fences"
    (hasStr (html "$\\binom{n}{k}$") "<mfrac linethickness=\"0\">" &&
      hasStr (html "$\\binom{n}{k}$") "minsize=\"1.01em\" maxsize=\"1.01em\">(</mo>" &&
      hasStr (html "\\[ \\binom{n}{k} \\]") "minsize=\"2.4em\" maxsize=\"2.4em\">(</mo>")
  t "amsmath dfrac: the MathML declares the display style"
    (hasStr (html "$\\dfrac{a}{b}$") "<mrow displaystyle=\"true\" scriptlevel=\"0\"><mfrac>")

/-- amsmath's modulo commands are their definitions (amsmath.sty), measured
on the laid line: each formula is as wide as the definition spelled with
the engine's own kerns (`\;` 5 mu, `\:` 4, `\,` 3, `\quad` 18) and an
upright `\text{mod}` — `\bmod` 5 mu a side; `\mod` 12 mu inline, then
`\,\,`; `\pod` 8 mu inline and 18 in a display, then its parenthesised
argument; `\pmod` a `\pod` of "mod" 6 mu before the argument. The semantic
dots set the glyphs amsmath `\let`s them to. -/
def amsModChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let widthOf (body : String) : Dim.Sp :=
    (((bodyLines (layoutOf fs (elabStr (dvDoc "" body)).1))[0]?).map (·.setWidth)).getD 0
  let pairs : List (String × String) := [
    ("$a \\bmod b$", "$a \\;\\text{mod}\\; b$"),
    ("$a \\mod b$", "$a \\:\\:\\:\\text{mod}\\,\\, b$"),
    ("$a \\pod{b}$", "$a \\:\\:(b)$"),
    ("$a \\pmod{b}$", "$a \\:\\:(\\text{mod}\\,\\,b)$"),
    ("\\[ a \\pmod{b} \\]", "\\[ a \\quad(\\text{mod}\\,\\,b) \\]"),
    ("$a \\dotsi b$", "$a \\!\\cdots b$")]
  for (cmd, defn) in pairs do
    t s!"amsmath mod: {cmd} sets no diagnostic" (dvE (dvDoc "" cmd)).isEmpty
    -- One kern spelled as several rounds once per kern: 12 mu as `\:\:\:`
    -- may differ from one 12 mu kern by the 2 sp its two extra roundings owe.
    let (w, d) := (widthOf cmd, widthOf defn)
    t s!"amsmath mod: {cmd} is as wide as its definition ({w} vs {d})"
      (w > 0 && w - d ≤ 2 && d - w ≤ 2)
  t "amsmath mod: the HTML sets the upright word and fixed parentheses"
    (let h := (HtmlDoc.emit {} (elabStr (dvDoc "" "$a \\pmod{b}$")).1).1
     hasStr h "<mi>mod</mi>" && hasStr h "<mo stretchy=\"false\">(</mo>")
  let squash (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
  for (cmd, glyph) in [("dotsc", '…'), ("dotso", '…'), ("dotsb", '\u22EF'),
      ("dotsm", '\u22EF')] do
    let src := dvDoc "" s!"$a \\{cmd} b$"
    t s!"amsmath dots: \\{cmd} sets {glyph}"
      ((dvE src).isEmpty && squash (pageTextOf fs src) ==
        String.ofList [MathParse.italicVar 'a', glyph, MathParse.italicVar 'b'])

/-- amsmath's `\numberwithin{counter}{within}` (amsmath.sty:
`\@addtoreset{counter}{within}` with `\the<counter>` redefined as
`\the<within>.\arabic{counter}`): the counter restarts whenever the heading
counter moves and renders after it — the equation counter and a theorem
counter alike — and a counter numbered per document runs on across
`\appendix`, which resets only the heading counters (article.cls). The page
and the references read exactly as lualatex sets the same document. Before
this feature `\numberwithin` was unknown (W0301) and a per-document theorem
counter restarted at `\appendix`: every row failed. -/
def amsNumberWithinChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let squash (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
  let v (c : Char) : String := String.ofList [MathParse.italicVar c]
  let pre := "\\usepackage{amsmath}\n\\newtheorem{thm}{Theorem}\n\\newtheorem{lem}{Lemma}\n" ++
    "\\numberwithin{equation}{section}\n\\numberwithin{lem}{section}\n"
  let eq (x : String) : String := s!"\\begin\{equation}{x}\\end\{equation}\n"
  let body := eq "w" ++ "\\section{Alpha}\n\\begin{thm}one\\end{thm}\n" ++
    "\\begin{lem}two\\end{lem}\n" ++ eq "x\\label{a}" ++ eq "y" ++ "\\subsection{Sub}\n" ++
    eq "u" ++ "\\section{Beta}\n" ++ eq "z\\label{b}" ++ "\\begin{lem}three\\end{lem}\n" ++
    "\\appendix\n\\section{Gamma}\n\\begin{thm}four\\end{thm}\n" ++ eq "v" ++
    "See \\eqref{a} and \\eqref{b}."
  let src := dvDoc pre body
  t "numberwithin: no warning" (warnCodes src).isEmpty
  let page := squash (pageTextOf fs src)
  let expected := v 'w' ++ "(0.1)1AlphaTheorem1oneLemma1.1two" ++ v 'x' ++ "(1.1)" ++
    v 'y' ++ "(1.2)1.1Sub" ++ v 'u' ++ "(1.3)2Beta" ++ v 'z' ++ "(2.1)Lemma2.1three" ++
    "AGammaTheorem2four" ++ v 'v' ++ "(A.1)See(1.1)and(2.1)."
  t s!"numberwithin: equations and lemmas restart at each section, a theorem runs on \
past the appendix (got '{page}')" (page == expected)
  let html := (HtmlDoc.emit {} (elabStr src).1).1
  t "numberwithin: the HTML number spans carry the section's numbers"
    (hasStr html "<span class=\"eqnum\">(0.1)</span>" &&
      hasStr html "<span class=\"eqnum\">(2.1)</span>" &&
      hasStr html "<span class=\"eqnum\">(A.1)</span>")
  t "numberwithin: a counter it does not number within a heading is named"
    ((warnCodes (dvDoc "\\usepackage{amsmath}\n\\numberwithin{figure}{section}\n" "x")).contains
      "W0110")

def amsmathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let serif ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"amsmath: serif unparsable: {e}")
  let fs ← mathSetOf (oneFaceOf serif)
  amsGridChecks ref fs
  amsTagChecks ref fs
  amsNumberWithinChecks ref fs
  amsTagTextChecks ref
  amsFracChecks ref fs
  amsModChecks ref fs
  amsIndexInkChecks ref fs
