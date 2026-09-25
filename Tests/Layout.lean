import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

inductive Piece where
  | W (w : Int)
  | G
  | H (w : Int)
  | B

open Piece in
def mkItems (ps : List Piece) : Array Layout.Item := Id.run do
  let mut items : Array Layout.Item := #[]
  for p in ps do
    match p with
    | .W w => items := items.push (.box (Dim.pt w) 0 Ir.Color.black none #[] (Dim.pt 10) false 0 none (.leaf 0))
    | .G => items := items.push (.glue { width := Dim.pt 10, stretch := Dim.pt 5, shrink := Dim.pt 3 })
    | .H w => items := items.push (.pen (Dim.pt w) Layout.hyphenPenalty true 0 Ir.Color.black #[])
    | .B =>
      items := items.push (.glue { fil := true })
      items := items.push (.pen 0 Layout.forcedCost false 0 Ir.Color.black #[])
  items := items.push (.glue { fil := true })
  items := items.push (.pen 0 Layout.forcedCost false 0 Ir.Color.black #[])
  return items

def W (w : Int) : Piece := .W w
def G : Piece := .G
def H (w : Int := 3) : Piece := .H w
def BRK : List Piece := [.B]

/-- Total demerits of a specific break sequence (must end at the final
forced penalty), or none when it spans a forced break. -/
def seqCost (items : Array Layout.Item) (target : Dim.Sp) (breaks : List Nat) :
    Option Int := Id.run do
  let mut prev : Nat := 0
  let mut first := true
  let mut prevFlagged := false
  let mut total : Int := 0
  for b in breaks do
    let a := if first then Layout.lineStart items 0 else Layout.lineStart items (prev + 1)
    -- `kp`'s own `a ≤ j` gate: a "line" whose start passes its break is
    -- empty and no rendering ships it, so the oracle refuses it too.
    if a > b then
      return none
    for k in [a:b] do
      if Layout.isForced items k then
        return none
    let m := Layout.measure items a b
    total := total + Layout.lineDemerits items m target b
    if prevFlagged && Layout.isFlagged items b then
      total := total + Layout.doubleHyphenDemerits
    if prevFlagged && b == items.size - 1 then
      total := total + Layout.finalHyphenDemerits
    prev := b
    prevFlagged := Layout.isFlagged items b
    first := false
  if breaks.getLast? != some (items.size - 1) then
    return none
  return some total

/-- Minimum cost over every legal break sequence (exponential; tiny inputs). -/
def bruteBest (items : Array Layout.Item) (target : Dim.Sp) : Option Int := Id.run do
  let n := items.size
  let legal := (List.range n).filter (Layout.canBreakAt items)
  let mut best : Option Int := none
  -- enumerate subsets of legal breakpoints that end at the final penalty
  let optional' := legal.filter (· != n - 1)
  let m := optional'.length
  for mask in [0:2 ^ m] do
    let mut chosen : List Nat := []
    for (b, idx) in optional'.zipIdx do
      if mask / 2 ^ idx % 2 == 1 then
        chosen := chosen ++ [b]
    match seqCost items target (chosen ++ [n - 1]) with
    | some c =>
      match best with
      | some b0 => if c < b0 then best := some c
      | none => best := some c
    | none => pure ()
  return best

/-- List marking over the positioned page: enumerate shows its order per
level and a nested list resets while the enclosing counter resumes; itemize
marks depth, degrading to a stand-in only where no face covers the class
glyph; an overlay-stepped item keeps its marker on every handout page (the
slides bug); declared markers override per level and fall back to the base
element; depth past four warns and still renders. Own function: `main`'s
elaboration budget. -/
def listChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (font : Font.Font) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let runOn (src : String) : Array Layout.LineOut × Array Diag :=
    let (d, _) := Elab.run "t" src
    let out := layoutOf oneFace d geom
    (bodyLines out, out.diags)
  let markerOf (l : Layout.LineOut) : String :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ _ _ _ glyphs _ _ _ _ _) => String.ofList (glyphs.toList.map (·.2))
    | _ => ""
  -- The numbering functions and their decoders (`\labelenum*`, classes.dtx).
  t "enum labels match the class defaults"
    (ListMark.enumLabel 1 1 == "1." && ListMark.enumLabel 2 1 == "(a)" &&
     ListMark.enumLabel 3 4 == "iv." && ListMark.enumLabel 4 2 == "B." &&
     ListMark.enumLabel 1 12 == "12." && ListMark.enumLabel 2 26 == "(z)")
  t "alph past its range degrades to arabic, distinctly"
    (ListMark.enumLabel 2 27 == "(27)")
  -- Roman injectivity, the one level the theorems leave to a decoder check:
  -- the round-trip over LaTeX's whole counter range implies it.
  t "roman round-trips over the counter range"
    ((List.range 32767).all fun k =>
      ListMark.romanVal (ListMark.romanN (k + 1)).toList == k + 1)
  -- Order is shown on the page.
  let (enumLines, _) := runOn
    "\\begin{enumerate}\\item alpha\\item beta\\item gamma\\end{enumerate}"
  t "enumerate numbers its items in order"
    (enumLines.map markerOf == #["1.", "2.", "3."])
  -- Nesting resets, the enclosing counter resumes, the level styles differ.
  let (nestLines, _) := runOn ("\\begin{enumerate}\\item one\\item two" ++
    "\\begin{enumerate}\\item inner\\item inner too\\end{enumerate}" ++
    "\\item three\\end{enumerate}")
  t "nested enumerate resets and the outer resumes"
    (nestLines.map markerOf == #["1.", "2.", "(a)", "(b)", "3."])
  -- Depth is shown: four itemize levels, each marker nonempty, adjacent
  -- levels distinct. Whether level 3 is the class asterisk or its stand-in
  -- follows the face, which is what keeps this hermetic.
  let (itemLines, _) := runOn ("\\begin{itemize}\\item a" ++
    "\\begin{itemize}\\item b\\begin{itemize}\\item c" ++
    "\\begin{itemize}\\item d\\end{itemize}\\end{itemize}\\end{itemize}\\end{itemize}")
  let marks := itemLines.map markerOf
  let lvl3 := if (font.gid '∗').isSome then "∗" else "*"
  t "itemize marks the four class levels"
    (marks == #["•", "–", lvl3, "·"])
  t "no itemize marker is empty" (marks.all (!·.isEmpty))
  t "adjacent itemize levels differ"
    (marks[0]! != marks[1]! && marks[1]! != marks[2]! && marks[2]! != marks[3]!)
  -- A stepped item keeps its marker: two items, two handout pages, a
  -- marker on every item line of both (this is the deck's page-3 bug).
  let (stepLines, _) := runOn ("\\documentclass{beamer}\n\\usetheme{default}\n" ++
    "\\begin{document}\n" ++
    "\\begin{frame}\\begin{itemize}\\item<1-> alpha\\item<2-> beta" ++
    "\\end{itemize}\\end{frame}\n\\end{document}")
  t "stepped items keep their markers on every page"
    (stepLines.size == 4 && (stepLines.map markerOf).all (· == "•"))
  -- Dim-not-hide dims the marker with its item: on the first handout page
  -- the second item is covered, marker included.
  let markerColor (l : Layout.LineOut) : Option Ir.Color :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ c _ _ _ _ _ _ _ _) => some c
    | _ => none
  t "a covered item's marker dims with it"
    (markerColor stepLines[1]! == some (Ir.Design.ofDoc {}).cover.plain &&
     markerColor stepLines[0]! == some Ir.Color.black)
  -- Declared markers: the base element styles every level; a level style
  -- overrides its own level only.
  let (ovLines, _) := runOn ("\\documentclass{article}\n" ++
    "\\style{itemize}{ marker = {x} }\n\\begin{document}\n" ++
    "\\begin{itemize}\\item a\\begin{itemize}\\item b\\end{itemize}\\end{itemize}\n" ++
    "\\end{document}")
  t "a base marker override styles every level"
    (ovLines.map markerOf == #["x", "x"])
  let (lvLines, _) := runOn ("\\documentclass{article}\n" ++
    "\\style{itemize2}{ marker = {+} }\n\\begin{document}\n" ++
    "\\begin{itemize}\\item a\\begin{itemize}\\item b\\end{itemize}\\end{itemize}\n" ++
    "\\end{document}")
  t "a level marker override styles its level alone"
    (lvLines.map markerOf == #["•", "+"])
  -- Depth past the class's four levels warns and still renders, reusing
  -- the fourth level's marker.
  let (deepLines, deepDiags) := runOn ("\\begin{itemize}\\item a" ++
    "\\begin{itemize}\\item b\\begin{itemize}\\item c\\begin{itemize}\\item d" ++
    "\\begin{itemize}\\item e\\end{itemize}\\end{itemize}\\end{itemize}" ++
    "\\end{itemize}\\end{itemize}")
  t "a fifth level warns W0010" (deepDiags.any (·.code == "W0010"))
  t "a fifth level still renders the fourth's marker"
    (deepLines.size == 5 && markerOf deepLines[4]! == "·")
  -- A declared marker whose glyph no face covers warns rather than
  -- vanishing silently: the diagnostics ride with the paragraph's.
  let (_, glyphDiags) := runOn ("\\documentclass{article}\n" ++
    "\\style{itemize}{ marker = {✦} }\n\\begin{document}\n" ++
    "\\begin{itemize}\\item a\\end{itemize}\n\\end{document}")
  t "an uncoverable marker glyph warns" (glyphDiags.any (·.code == "E0405"))
  -- The scalar walk offers the default marker glyphs to the driver's
  -- fallback scan, per level actually reached.
  let scalars := Layout.docScalars (Elab.run "t"
    ("\\begin{itemize}\\item a\\begin{itemize}\\item b\\end{itemize}" ++
     "\\end{itemize}")).1
  t "docScalars carries the reached default markers"
    (scalars.contains '•' && scalars.contains '–' &&
     scalars.contains '*' && scalars.contains '-' && !scalars.contains '∗')

/-- **A numbered algorithm's line numbers stand inside the text area.**
The invariant a `markerIndent` of the block's own indent did not hold: the
number column right-aligns `\labelsep` left of that offset, so at indent 0
the numbers set in the page margin (10.7 pt out on the corpus fixture, with
no diagnostic). algorithm2e reserves the column inside the algorithm's own
box instead — the body opens one `\algomargin` in and the number is lapped
back into that inset (algorithm2e.sty:2621-2624, 1645-1647) — and the
engine's own HTML path already did (`ol.algorithm.numbered`'s padding).

Asserted over `Layout.Out`: the leftmost ink of every line, numbers
included, against the margin. The corpus fixture's two-digit numbers are
covered by the default reserve alone, so the widest-number arm is reached
by a synthetic hundred-line algorithm, where `\llap` into a fixed inset is
exactly what would put a three-digit number back in the margin. -/
def algNumberColumnChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let alg (numbered : Bool) (n : Nat) : String :=
    "\\documentclass{article}\n\\begin{document}\n\\begin{algorithm}\n" ++
    (if numbered then "\\LinesNumbered\n" else "") ++
    String.join ((List.range n).map fun k => s!"step {k + 1}\\;\n") ++
    "\\end{algorithm}\n\\end{document}"
  let linesOf (src : String) : Array Layout.LineOut :=
    let (d, _) := Elab.run "t" src
    bodyLines (layoutOf oneFace d geom)
  let leftmost (ls : Array Layout.LineOut) : Dim.Sp :=
    ls.foldl (fun m l => min m l.x) geom.pageW
  -- Thirteen lines, the corpus fixture's own count: every line's ink,
  -- number included, stands at or right of the margin.
  let short := linesOf (alg true 13)
  t s!"a numbered algorithm's numbers stand inside the measure \
({(leftmost short).toPtString} vs {geom.hmargin.toPtString})"
    (0 < short.size && geom.hmargin ≤ leftmost short)
  -- The widest-number arm: three digits need more than the default inset,
  -- so the reserve follows the number rather than the constant. `\llap`
  -- into a fixed inset is what would put them back in the margin.
  let long := linesOf (alg true 120)
  t s!"a hundred-line algorithm's three-digit numbers stay inside \
({(leftmost long).toPtString} vs {geom.hmargin.toPtString})"
    (0 < long.size && geom.hmargin ≤ leftmost long)
  -- The column is the numbers': an unnumbered algorithm reserves none, so
  -- its code keeps the full measure.
  let plain := linesOf (alg false 13)
  t s!"an unnumbered algorithm reserves no number column \
({(leftmost plain).toPtString})"
    (0 < plain.size && leftmost plain == geom.hmargin)
  -- The reserve, measured: every one of the three sets the same first line
  -- (`step 1;`), and a line's right edge is its content's own — the marker
  -- rides inside `setWidth` from `x` — so the difference between two right
  -- edges is exactly the difference between two reserves.
  let rightOf (ls : Array Layout.LineOut) : Dim.Sp :=
    (ls[0]?.map fun l => l.x + l.setWidth).getD 0
  t s!"the default column is two ems, algorithm2e's inset and the HTML's padding \
({(rightOf short - rightOf plain).toPtString})"
    (rightOf short - rightOf plain == 2 * geom.fontSize)
  t s!"a wider number widens the column \
({(rightOf long - rightOf short).toPtString})"
    (rightOf plain < rightOf short && rightOf short < rightOf long)

/-- Line-level typesetting checks against a one-face set. Its own function:
`main` is a single `do` block, and Lean's elaboration budget for one block
runs out long before the tests do. -/
def lineChecks (ref : IO.Ref (List String)) (geom : Layout.Geom) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  -- Fixed-width spaces are kerns. Looking up a glyph at U+2009 drops the
  -- space, because a Type 1-derived face has none -- and warns instead of
  -- setting it.
  let widthOf (src : String) : Dim.Sp :=
    let (d, _) := Elab.run "t" src
    (((layoutOf oneFace d geom).pages.flatMap (·.lines))[0]?.map
      (·.setWidth)).getD 0
  let plainW := widthOf "ab"
  let thinW := widthOf "a\\,b"
  t "thin space widens the line" (thinW == plainW + geom.fontSize / 6)
  t "thin space warns about nothing"
    ((layoutOf oneFace (Elab.run "t" "a\\,b").1 geom).diags.isEmpty)
  t "no-break space is an unbreakable interword space"
    (widthOf "a\\nbsp b" > plainW)
  -- `~` is what LaTeX authors actually type for it.
  t "tilde is a no-break space"
    ((Elab.run "t" "a~b").1.body == #[.para #[.text "a\u00a0b"]])
  t "tilde does not break the line" (widthOf "a~b" == widthOf "a\u00a0b")
  t "escaped tilde is a literal tilde"
    ((Elab.run "t" "a\\~b").1.body == #[.para #[.text "a~b"]])
  -- `\noindent` asks for what every paragraph here already has — no
  -- first-line indent, in any class — so its arm answers with a note and
  -- the page shows the first line at the margin with it and without it.
  let firstX (src : String) : Option Dim.Sp :=
    ((bodyLines (layoutOf oneFace (Elab.run "t" src).1 geom))[0]?).map (·.x)
  t "noindent's first line stands at the margin, as every first line does"
    (firstX "\\noindent alpha beta" == some geom.hmargin &&
     firstX "alpha beta" == some geom.hmargin)

  -- Small caps on a face without smcp+c2sc are synthesised UNIFORM: every
  -- letter its capital form, the whole word at one reduced size — mixed
  -- case cannot come out at two heights. (`\scshape` used to do nothing at
  -- all; then it kept capitals full-size beside scaled lowercase.)
  let scOut := layoutOf oneFace (Elab.run "t" "\\scshape aB").1 geom
  let scRuns := (bodyLines scOut).flatMap (·.segs.filterMap fun s =>
    match s with
    | .run _ _ _ _ glyphs size _ _ _ _ => some (glyphs.map (·.2), size)
    | _ => none)
  t "synthesised small caps carry no lowercase form"
    (!scRuns.isEmpty && scRuns.all fun (cs, _) => cs.all fun c => !c.isLower)
  t "synthesised small caps are uniform: mixed case sets at one reduced size"
    (scRuns.all (·.2 == geom.fontSize * Layout.smallCapScale / 1000))

  -- `\hfill` on a paragraph's last line must reach the margin. The
  -- line-running fill is also fil glue, and sharing the leftover with it
  -- puts the right-hand text halfway there -- which is what LaTeX does and
  -- what nobody setting a row of dates wants.
  let measureOf (src : String) : Array Dim.Sp :=
    let (d, _) := Elab.run "t" src
    (bodyLines (layoutOf oneFace d geom)).map (·.setWidth)
  -- A paragraph ending in `\\` used to vanish whole: the break's own
  -- forced penalty and the paragraph terminator left an empty last line
  -- with no feasible predecessor, and the breaker returned no lines.
  t "paragraph ending in a break keeps its content"
    ((measureOf "first line\\\\\n\nsecond").size == 2)
  let lastLine := measureOf "Left \\hfill Right"
  t "hfill reaches the margin on a final line"
    (lastLine.size == 1 && lastLine[0]! == geom.textWidth)
  let brokenLine := measureOf "Left \\hfill Right\\\\Second"
  t "hfill reaches the margin before a break"
    (brokenLine.size == 2 && brokenLine[0]! == geom.textWidth)
  -- Without an \hfill the last line stays ragged: the fill still fills.
  t "no hfill leaves the last line short"
    (brokenLine.size == 2 && brokenLine[1]! < geom.textWidth)
  -- Verbatim: one set line per code line, interior blank lines included —
  -- a blank line inside a code block used to have no feasible break and
  -- could vanish with everything after it.
  t "verbatim sets one line per code line, blanks included"
    ((measureOf "\\begin{verbatim}\na\n\nb\n\\end{verbatim}").size == 3)

  -- Character protrusion (stage 1): every justified full line's boundary
  -- glyphs hang into the margin by the cmr-default fractions of their own
  -- width (`Layout.protrusionLR`); the line is set against the enlarged
  -- measure and shifted left by the hang, so the optical edge is straight
  -- and breaks are unchanged. Every word of the fixture starts 'A' and
  -- ends '.', so both boundary glyphs of every full line are known
  -- whatever breaks the breaker picks; the fil-set last line keeps its
  -- exact margins. The left hang is exact; the right edge sits within the
  -- period's allowance up to the glue set's sub-sp rounding (each gap
  -- rounds under 1 sp), so the band asserted is (allowance/2, 2×).
  let font := oneFace.get 0
  let scaledAdv (c : Char) : Dim.Sp :=
    (font.advance c * geom.fontSize.toNat) / font.unitsPerEm
  let lp := scaledAdv 'A' * 50 / 1000
  let rp := scaledAdv '.' * 700 / 1000
  let protDoc := (Elab.run "t" (String.intercalate " " (List.replicate 40 "Aaaa."))).1
  let protLines := bodyLines (layoutOf oneFace protDoc geom)
  let full := protLines.pop
  t "protrusion fixture wraps into full lines" (protLines.size ≥ 3)
  t "protrusion hangs every full line left by exactly the A's fraction"
    (!full.isEmpty && full.all fun l => l.x == geom.hmargin - lp && l.hang == lp)
  t "protrusion hangs the period past the measure by its allowance"
    (full.all fun l =>
      l.x + l.setWidth > geom.hmargin + geom.textWidth + rp / 2 &&
      l.x + l.setWidth < geom.hmargin + geom.textWidth + 2 * rp)
  let offLines := bodyLines (layoutOf oneFace protDoc { geom with protrude := false })
  t "protrusion never re-breaks: the line count is the unprotruded one"
    (protLines.size == offLines.size)
  t "protrusion off restores the exact margins"
    (offLines.all fun l => l.x == geom.hmargin && l.hang == 0 &&
      l.x + l.setWidth ≤ geom.hmargin + geom.textWidth)
  t "a page declares protrusion off"
    ((Elab.run "t" "\\documentclass{article}\\page{ protrusion = off }\
\\begin{document}x\\end{document}").1.page.protrude == some false)

  -- Font expansion: one bounded factor per line (`Layout.expandFactor`,
  -- ±20‰), fonts absorbing the delta first and glue taking the remainder.
  -- The bound is `expandFactor_bounded`; these pin the realization.
  t "expansion stays within microtype's bounds on every line"
    (protLines.all fun l =>
      -(Layout.expandLimit : Int) ≤ l.expand && l.expand ≤ (Layout.expandLimit : Int))
  t "some full line actually expands on the wrapped fixture"
    ((protLines.pop).any fun l => l.expand != 0)
  t "expansion off zeroes every factor and keeps run widths natural"
    ((bodyLines (layoutOf oneFace protDoc { geom with expand := false })).all
      fun l => l.expand == 0)
  t "a page declares expansion off"
    ((Elab.run "t" "\\documentclass{article}\\page{ expansion = off }\
\\begin{document}x\\end{document}").1.page.expand == some false)

/-- Cross-references: a \label binds to the nearest preceding numbered
thing in flow order, resolution is one pure pass over the IR
(`Ir.resolveOneRef_exact` is the statement; these run it), a forward
reference costs nothing, an unresolved one is LaTeX's `??` named by W0349,
and a duplicate key keeps its first binding (W0350). -/
def refChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let art (body : String) : Ir.Doc × Array Diag :=
    elabStr ("\\documentclass{article}\\begin{document}\n" ++ body ++ "\n\\end{document}")
  let refShows (doc : Ir.Doc) (key : String) : Option (String × Option String) := Id.run do
    for b in doc.body do
      if let .para xs := b then
        for x in xs do
          if let .ref k _ text target := x then
            if k == key then return some (text, target)
    return none
  -- Forward reference: the label follows the reference and still resolves.
  let (fwd, fwdDs) := art
    "\\section{A}\\label{s:a}\nSee \\ref{s:b}.\n\\section{B}\\label{s:b}\nBack to \\ref{s:a}."
  t "a forward reference resolves without a second pass"
    (fwdDs.isEmpty && refShows fwd "s:b" == some ("2", some "s:b") &&
     refShows fwd "s:a" == some ("1", some "s:a"))
  -- eqref parenthesises whatever the label's number is (amsmath's \eqref).
  let (eq, _) := art "\\section{A}\\label{s:a}\nAs \\eqref{s:a}."
  t "eqref parenthesises the number" (refShows eq "s:a" == some ("(1)", some "s:a"))
  -- A missing key is LaTeX's ?? and W0349 names it, once per key.
  let (missing, missDs) := art "\\section{A}\nSee \\ref{gone} and \\ref{gone}."
  t "an unresolved reference is ?? and W0349 names the key once"
    (refShows missing "gone" == some ("??", none) &&
     (missDs.filter (·.code == "W0349")).size == 1)
  -- A label where nothing is numbered binds to nothing.
  let (bare, bareDs) := art "\\label{early}\nSee \\ref{early}."
  t "a label where nothing numbers resolves to ??"
    (refShows bare "early" == some ("??", none) &&
     bareDs.any (·.code == "W0349"))
  -- A duplicate key keeps its first binding; W0350 names the second.
  let (dup, dupDs) := art
    "\\section{A}\\label{k}\n\\section{B}\\label{k}\nSee \\ref{k}."
  t "a duplicate label warns and the first wins"
    (dupDs.any (·.code == "W0350") && refShows dup "k" == some ("1", some "k"))
  -- A label inside a captioned float binds to the float's number, and one
  -- after the float binds back to the enclosing heading (group scoping).
  let (flt, _) := art ("\\section{A}\\label{s:a}\n" ++
    "\\begin{figure}\\caption{Invented}\\label{fig:x}\\end{figure}\n" ++
    "\\label{after}\nSee \\ref{fig:x} and \\ref{after}.")
  t "a float's label takes the float's number; one after it, the section's"
    ((refShows flt "fig:x").map (·.1) == some "1" &&
     (refShows flt "after").map (·.1) == some "1" &&
     (refShows flt "fig:x").bind (·.2) == some "fig:x")
  -- An equation's label binds to the equation's own number, scoped to the
  -- environment; \nonumber opts out and frees the number for the next.
  let (eqn, eqnDs) := art ("\\section{A}\n" ++
    "\\begin{equation}\\label{eq:one} a = b \\end{equation}\n" ++
    "\\begin{equation} c = d \\nonumber\\end{equation}\n" ++
    "\\begin{equation}\\label{eq:two} e = f \\end{equation}\n" ++
    "See \\eqref{eq:one} and \\eqref{eq:two}.")
  t "equation labels bind to the equation's number; nonumber opts out"
    (eqnDs.isEmpty &&
     (refShows eqn "eq:one").map (·.1) == some "(1)" &&
     (refShows eqn "eq:two").map (·.1) == some "(2)")
  -- The label table (bound at elaboration) and Ir.numberFloats (assigned
  -- over the finished IR) are two sites counting one thing; this pins them
  -- equal: each float's carried num is the number its label resolves to.
  let (agree, _) := art ("\\section{A}\n" ++
    "\\begin{figure}\\caption{One}\\label{f:1}\\end{figure}\n" ++
    "\\begin{table}\\caption{T}\\label{t:1}\\end{table}\n" ++
    "\\begin{figure}\\caption{Two}\\label{f:2}\\end{figure}\n" ++
    "Refs: \\ref{f:1} \\ref{t:1} \\ref{f:2}.")
  let floatNums := agree.body.toList.filterMap fun b => match b with
    | Ir.Block.float _ num _ _ _ => some num
    | _ => none
  t "float labels resolve to the numbers numberFloats carries"
    (floatNums == [some 1, some 1, some 2] &&
     (refShows agree "f:1").map (·.1) == some "1" &&
     (refShows agree "t:1").map (·.1) == some "1" &&
     (refShows agree "f:2").map (·.1) == some "2")
  -- A subfigure's label resolves to the parent's number and its own letter
  -- (subcaption manual §"Referencing subfigures": \ref shows "1a"); the
  -- parent's label keeps the plain number. The binding is read off the
  -- numbered IR (Ir.floatLabelRows) — elaboration predicts nothing.
  let (sub, _) := art ("\\begin{figure}\n" ++
    "\\begin{subfigure}{0.4\\textwidth}left\\caption{L}\\label{sf:l}\\end{subfigure}\n" ++
    "\\begin{subfigure}{0.4\\textwidth}right\\caption{R}\\label{sf:r}\\end{subfigure}\n" ++
    "\\caption{Parent}\\label{fig:p}\\end{figure}\n" ++
    "See \\ref{sf:l}, \\ref{sf:r}, \\ref{fig:p}.")
  t "a subfigure label resolves to the parent number and its letter"
    ((refShows sub "sf:l").map (·.1) == some "1a" &&
     (refShows sub "sf:r").map (·.1) == some "1b" &&
     (refShows sub "fig:p").map (·.1) == some "1")
  -- First wins across the merge: a duplicate key inside a float cannot
  -- override the binding of its first declaration outside the float —
  -- the collect reports every label, so the float duplicate is never a
  -- key's first row.
  let (dupf, dupfDs) := art ("\\section{A}\n\\section{B}\\label{k}\n" ++
    "\\begin{figure}\\caption{C}\\label{k}\\end{figure}\nSee \\ref{k}.")
  t "a float duplicate of an outside key warns and the first wins"
    (dupfDs.any (·.code == "W0350") && refShows dupf "k" == some ("2", some "k"))
  -- A numbered equation inside a float keeps the equation's binding: the
  -- collect reports an equation's labels unbound, so the merge leaves the
  -- number elaboration recorded.
  let (eqf, _) := art ("\\begin{figure}\\caption{C}\n" ++
    "\\begin{equation}\\label{eq:f} x = y \\end{equation}\\end{figure}\n" ++
    "As \\eqref{eq:f}.")
  t "an equation label inside a float keeps the equation's number"
    ((refShows eqf "eq:f").map (·.1) == some "(1)")
  -- The anchor sanitiser: author text entering an id keeps no whitespace.
  t "an anchor keeps no whitespace and stays nonempty"
    (Ir.labelAnchor "a b\"c" == "a-b-c" && Ir.labelAnchor "" == "label")
  -- HTML: the anchor and the link are the same pure function's answer.
  let (htmlDoc, _) := art "\\section{A}\\label{s:a}\nSee \\ref{s:a}."
  let page := (HtmlDoc.emit {} htmlDoc).1
  t "HTML links a resolved reference to its label's anchor"
    ((page.splitOn "<span id=\"s:a\">").length == 2 &&
     (page.splitOn "href=\"#s:a\"").length == 2)
  -- The rendered check: a \label alone on its source line opens no blank
  -- line — the shipped pages with and without it are line-for-line equal.
  let run (body : String) : Nat :=
    let (doc, _) := art body
    let out := layoutOf oneFace doc
    out.pages.foldl (fun n p => n + p.lines.size) 0
  t "a lone label line ships no blank line"
    (run "\\section{A}\\label{s:a}\nText after." == run "\\section{A}\nText after.")

/-- The quotation node: `{quote}` and `{quotation}` elaborate to the one
`Block.quote` (classes.dtx defines both as `\list{}{\rightmargin
\leftmargin}`; they differ only in a paragraph indent the engine cannot
spell yet). The PDF sets it inside both margins, HTML as `<blockquote>`
through the escaper, markdown as one `> `-marked block. Own function:
`main`'s elaboration budget. -/
def quoteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Before.\\begin{quote}One invented line.\\end{quote}" ++
    "\\begin{quotation}First paragraph.\n\nSecond paragraph.\\end{quotation}" ++
    "After.\\end{document}")
  t "quote source is clean" ds.isEmpty
  t "quote and quotation elaborate to the one quote node"
    (doc.body.size == 4 &&
      (match doc.body[1]?, doc.body[2]? with
       | some (Ir.Block.quote q1), some (Ir.Block.quote q2) =>
         q1.size == 1 && q2.size == 2
       | _, _ => false))
  -- Markdown: `> ` marks the quoted line, and the separator between two
  -- quoted paragraphs keeps a bare `>` so the quotation stays one block
  -- (CommonMark §5.1: a block quote does not continue across a blank line).
  let md := (MarkdownDoc.emit doc)
  t "markdown sets the quotation as > lines"
    ((md.splitOn "> One invented line.").length == 2)
  t "markdown keeps a two-paragraph quotation one block"
    ((md.splitOn "> First paragraph.\n>\n> Second paragraph.").length == 2)
  -- HTML: the platform's own construct, built through the typed tree.
  let page := (HtmlDoc.emit {} doc).1
  t "html sets the quotation as a blockquote"
    (match (page.splitOn "<blockquote>")[1]? with
     | some rest =>
       ((rest.splitOn "</blockquote>")[0]?.map fun inner =>
         (inner.splitOn "<p>One invented line.</p>").length == 2).getD false
     | none => false)
  let (esc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{quote}2 < 3\\end{quote}\\end{document}")
  t "html escapes quoted content like any other"
    ((((HtmlDoc.emit {} esc).1.splitOn "2 &lt; 3").length == 2))
  -- Both margins move in (classes.dtx: `\rightmargin\leftmargin`): the
  -- quoted line starts one list indent past the left margin and its set
  -- width never reaches past the narrowed right edge.
  let geom : Layout.Geom := {}
  let out := layoutOf oneFace doc geom
  let lines := out.pages.flatMap (·.lines)
  let quoted := lines.filter fun l => l.x == geom.hmargin + geom.listIndent
  t "pdf quotation indents from the left margin" (quoted.size ≥ 1)
  t "pdf quotation keeps inside the narrowed right margin"
    (quoted.all fun l =>
      decide (l.x + l.setWidth ≤ geom.hmargin + geom.textWidth - geom.listIndent))
  t "pdf prose around the quotation keeps the full measure"
    (lines.any fun l => l.x == geom.hmargin)

/-- A declared box width reaches the page as the width it declares: a
fraction of the enclosing measure as that fraction, an absolute length as
that length. Asserted over `Layout.Out` — the claim is how wide the lines
inside the box are set, never an IR dump. Both rows fail while the carrier
spells a width as `Option Nat` per mille: an absolute length is not a
fraction of anything, so it had no representation and the box silently took
the whole measure (W0314). The macro row is the same gap from the surface
side — a width the document spells through its own command never reached
the reader that resolves fractions. Invented content and lengths. -/
def boxWidthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let filler := "Panel prose long enough to need more than one line inside its box."
  let boxDoc (pre : String) (w : String) : String :=
    "\\documentclass{article}" ++ pre ++ "\\begin{document}\\begin{minipage}{" ++ w ++
    "}" ++ filler ++ "\\end{minipage}\\end{document}"
  let widest (src : String) : Dim.Sp :=
    ((allLines (layoutOf oneFace (elabStr src).1 geom)).filter
      fun l => !l.furniture && !l.segs.isEmpty).foldl
        (fun m l => max m (l.x + l.setWidth - geom.hmargin)) 0
  -- A half-measure fraction is the control: it worked before this change and
  -- must still, so the carrier is not trading one spelling for another.
  let half := widest (boxDoc "" ".5\\textwidth")
  t "a fractional box width still sets at its fraction"
    (decide (half ≤ geom.textWidth / 2) && decide (half > geom.textWidth / 4))
  -- An absolute length: 90pt of a 345pt measure, so a box that took the whole
  -- measure would overshoot by nearly four times.
  let abs90 := widest (boxDoc "" "90pt")
  t "an absolute box width sets at that length"
    (decide (abs90 ≤ Dim.pt 90) && decide (abs90 > Dim.pt 30))
  t "an absolute box width is no longer a named loss"
    (!(warnCodes (boxDoc "" "90pt")).contains "W0314")
  -- A width the document spells through its own command resolves to what the
  -- command expands to, so the fraction reader sees a fraction.
  let viaMacro := widest (boxDoc "\\newcommand{\\panelw}{.5\\textwidth}" "\\panelw")
  t "a box width spelled through a document command resolves"
    (viaMacro == half)
  t "a box width spelled through a document command is no longer a named loss"
    (!(warnCodes (boxDoc "\\newcommand{\\panelw}{.5\\textwidth}" "\\panelw")).contains
      "W0314")
  -- `\parbox{w}{t}` is `{minipage}{w}` with an inline-only body (latex.ltx
  -- builds both through `\@iiiparbox`), so its declared width sets the same
  -- box rather than being dropped.
  let parbox := widest ("\\documentclass{article}\\begin{document}\\parbox{90pt}{" ++
    filler ++ "}\\end{document}")
  t "a parbox sets at its declared width"
    (decide (parbox ≤ Dim.pt 90) && decide (parbox > Dim.pt 30))
  t "a parbox width is no longer dropped"
    (!(warnCodes ("\\documentclass{article}\\begin{document}\\parbox{90pt}{x}" ++
      "\\end{document}")).contains "W0104")
  -- A width wider than the measure cannot make the box wider than the page:
  -- the resolved length is clamped where the measure is known, which is the
  -- reason an absolute length rides as a length and is not pre-divided into
  -- per mille at elaboration.
  t "an absolute width past the measure is clamped to it"
    (decide (widest (boxDoc "" "900pt") ≤ geom.textWidth))
  -- The HTML track for each spelling, from the same IR value: a fraction is a
  -- percentage, an absolute length a length, and a shared column a free
  -- fraction of the leftover (`Ir.BoxWidth.track`, `boxWidth_tracks_agree`).
  t "each declared width has its own HTML track"
    (Ir.Track.css (Ir.BoxWidth.trackOf (.frac 500)) == "50%" &&
      Ir.Track.css (Ir.BoxWidth.trackOf (.abs (Dim.pt 90))) == "90pt" &&
      Ir.Track.css (Ir.BoxWidth.trackOf .share) == "1fr")

/-- A declared ragged setting reaches the page on the side it declares:
`\raggedright`/`{flushleft}` hang their lines from the left edge of the
measure, `\raggedleft`/`{flushright}` from the right. Asserted over
`Layout.Out` — the claim is where lines land, never an IR dump — and the
ordering is the content-free half: whatever the words, a right-set line's
own right edge is the measure's, and a left-set line's origin is the
margin. Both fail while `Ir.Block.ragged` is direction-free: every ragged
scope kept the left origin and the right-set spellings were a named loss,
so a staggered right-aligned scope collapsed to the left margin. -/
def raggedSideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let right := geom.hmargin + geom.textWidth
  let doc (decl : String) : String :=
    "\\documentclass{article}\\begin{document}" ++ decl ++
    "One short line.\\\\ Another short line.\\\\ A third short line." ++
    "\\end{document}"
  let linesOf (decl : String) : Array Layout.LineOut :=
    (allLines (layoutOf oneFace (elabStr (doc decl)).1 geom)).filter
      fun l => !l.furniture && !l.segs.isEmpty
  let leftSet := linesOf "\\raggedright "
  let rightSet := linesOf "\\raggedleft "
  -- Content-free: the three lines are short, so none fills the measure and
  -- each side's claim is about the origin the setting chose, not the words.
  t "the ragged probe set three unfilled lines on each side"
    (leftSet.size == 3 && rightSet.size == 3 &&
      rightSet.all fun l => decide (l.setWidth < geom.textWidth))
  t "a left-set ragged scope hangs its lines from the margin"
    (leftSet.all fun l => l.x + l.hang == geom.hmargin)
  t "a right-set ragged scope hangs its lines from the measure's right edge"
    (rightSet.all fun l => l.x + l.setWidth == right)
  -- The environment spelling of the same two declarations.
  let envLeft := linesOf "\\begin{flushleft}"
  t "the flushleft environment sets from the margin"
    (envLeft.size ≥ 1 && envLeft.all fun l => l.x + l.hang == geom.hmargin)
  let envRight := (allLines (layoutOf oneFace (elabStr
    ("\\documentclass{article}\\begin{document}\\begin{flushright}" ++
      "One short line.\\\\ Another short line.\\end{flushright}" ++
      "\\end{document}")).1 geom)).filter fun l => !l.furniture && !l.segs.isEmpty
  t "the flushright environment sets from the measure's right edge"
    (envRight.size == 2 && envRight.all fun l => l.x + l.setWidth == right)
  -- Right-set lines are not centred: a centred scope leaves equal slack on
  -- both sides, so the two settings must disagree on the same content.
  let centred := (allLines (layoutOf oneFace (elabStr (doc "\\centering ")).1 geom)).filter
    fun l => !l.furniture && !l.segs.isEmpty
  t "a right-set line is not a centred line"
    (centred.size == 3 && centred.all fun l => decide (l.x + l.setWidth < right))
  -- The named loss retires: nothing is dropped, so nothing is reported.
  t "the right-set spellings are no longer a named loss"
    (!(warnCodes (doc "\\raggedleft ")).contains "W0104" &&
      !(warnCodes ("\\documentclass{article}\\begin{document}" ++
        "\\begin{flushright}x\\end{flushright}\\end{document}")).contains "W0104")
  -- The other artifact, from the same IR value: the typed tree carries the
  -- side's class and the sheet declares that side's edge. A width honoured
  -- on the page and dropped in the HTML is the defect class the carrier
  -- exists to prevent, so both projections are judged here
  -- (`Ir.ragged_sides_agree` is the statement; these are its two emitters).
  let treeOf (decl : String) : Html.Node :=
    HtmlDoc.blockNode {} (elabStr (doc decl)).1.body[0]!
  let classOf : Html.Node → Option String
    | .elem _ attrs _ => (attrs.find? fun a => a.1 == "class").map (·.2)
    | _ => none
  t "the typed tree carries the declared side's class"
    (classOf (treeOf "\\raggedright ") == some (HtmlDoc.raggedClass .left) &&
      classOf (treeOf "\\raggedleft ") == some (HtmlDoc.raggedClass .right))
  t "the sheet declares each side's own edge"
    (HtmlDoc.raggedRule .left == ".ragged { text-align: left; }\n" &&
      HtmlDoc.raggedRule .right == ".ragged-right { text-align: right; }\n")

/-- `\centering` is a declaration: it centres the rest of its scope, the way
`\bfseries` sets bold. Own function, same reason. -/
def centeringChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (c1, ds1) := elabStr "{\\centering x\\par} y"
  t "centering centres the rest of its group" (ds1.isEmpty &&
    c1.body == #[.center #[.para #[.text "x"]], .para #[.text "y"]])
  -- The declaration survives a paragraph end inside the scope, as \bfseries
  -- does: both paragraphs centre.
  t "centering carries across par like other declarations"
    ((elabStr "{\\centering a\\par b}").1.body ==
      #[.center #[.para #[.text "a"]], .center #[.para #[.text "b"]]])
  -- The frame spelling, which is how every deck asks for a standout layout.
  let (fr, frDs) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}\\centering Questions?\\end{frame}\\end{document}")
  t "centering inside a frame centres its content" (frDs.isEmpty &&
    fr.body == #[.frame #[] false .center false #[.center #[.para #[.text "Questions?"]]]])
  -- Inside inline content there is no block to centre; the warning stays.
  t "centering in an argument still warns"
    (warnCodes "\\textbf{\\centering x}" == ["W0108"])
  -- A float's alignment grouping is transparent: the LaTeX-manual idiom
  -- `\begin{figure}\begin{center} B \caption{..} \end{center}\end{figure}`
  -- and `\begin{figure}\centering B \caption{..}\end{figure}` elaborate to
  -- the same Ir — same float, same caption, same label binding, same
  -- diagnostics — for `center` and for `centering` as the group's name,
  -- and the caption inside the grouping is never an unknown command.
  let floatDoc (inner : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ inner ++ "\n\\end{document}"
  let figBody := "A panel body.\n\\caption{An invented panel.}\n\\label{fig:p}\n"
  let grouped (env : String) := floatDoc
    ("\\begin{figure}[h]\n\\begin{" ++ env ++ "}\n" ++ figBody ++
      "\\end{" ++ env ++ "}\n\\end{figure}\nSee \\ref{fig:p}.")
  let flat := floatDoc
    ("\\begin{figure}[h]\n\\centering\n" ++ figBody ++ "\\end{figure}\nSee \\ref{fig:p}.")
  let sig (ds : Array Diag) : Array (String × Severity × String) :=
    ds.map fun d => (d.code, d.severity, d.message)
  let (gDoc, gDs) := elabStr (grouped "center")
  let (fDoc, fDs) := elabStr flat
  t "a float's center group is transparent: same Ir as \\centering"
    (gDoc == fDoc)
  t "a float's center group is transparent: same diagnostics"
    (sig gDs == sig fDs)
  t "the caption inside the group is the float's, never unknown"
    (gDs.all (·.code != "W0301"))
  let (cDoc, cDs) := elabStr (grouped "centering")
  t "the centering environment name is the same transparent group"
    (cDoc == fDoc && sig cDs == sig fDs)
  -- The table twin: a caption after \end{tabular} inside the group.
  let tblBody := "\\begin{tabular}{ll}\na & b \\\\\n\\end{tabular}\n" ++
    "\\caption{An invented strip.}\n\\label{tab:s}\n"
  let (tg, tgDs) := elabStr (floatDoc
    ("\\begin{table}[h]\n\\begin{center}\n" ++ tblBody ++ "\\end{center}\n\\end{table}"))
  let (tf, tfDs) := elabStr (floatDoc
    ("\\begin{table}[h]\n\\centering\n" ++ tblBody ++ "\\end{table}"))
  t "a table's center group is transparent: same Ir and diagnostics"
    (tg == tf && sig tgDs == sig tfDs && tgDs.all (·.code != "W0301"))

/-- Both backends print one triple for an RGB colour: the HTML hex and the
PDF `rg` operands are two projections of the one `Ir.Color` — and both are
injective (`cssColor_inj`, `pdfComponents_inj`), so the two artifacts keep
apart exactly the same inks. A projection corollary in the shape of
`Pdf.html_fonts_cover_pdf`; it stands beside the tests rather than in a
backend module because it names both backends and neither imports the
other's colour printer. -/
theorem backend_rgb_exact (c : Ir.Color) (h : c.cmyk = none) :
    HtmlDoc.cssColor c =
        "#" ++ Ir.Color.hexByte c.r false ++ Ir.Color.hexByte c.g false ++
          Ir.Color.hexByte c.b false ∧
      c.pdfFill = Ir.Color.pdfMilli (Ir.Color.milli c.r) ++ " " ++
        Ir.Color.pdfMilli (Ir.Color.milli c.g) ++ " " ++
        Ir.Color.pdfMilli (Ir.Color.milli c.b) ++ " rg" :=
  ⟨rfl, by rw [Ir.Color.pdfFill_srgb c h]; rfl⟩

/-- `\vspace{\fill}` and `\vfill`: TeX's first-order infinite glue, whose
share of the page's leftover is what places the content. Asserted over
`Layout.Out` — the claim is about where lines land, never about an IR
dump. -/
def filChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let linesOf (src : String) : Array Layout.LineOut :=
    allLines (layoutOf oneFace (elabStr src).1 geom)
  let doc (body : String) : String :=
    s!"\\documentclass\{article}\\begin\{document}{body}\\end\{document}"
  let top := linesOf (doc "hello")
  let mid := linesOf (doc "\\vspace*{\\fill}\nhello\n\\vspace*{\\fill}")
  let low := linesOf (doc "\\vspace*{\\fill}\nhello")
  t "the fill sandwich centres its page"
    (match top[0]?, mid[0]?, low[0]? with
     | some a, some b, some c =>
       -- strictly between top-flush and bottom-flush, and nearer neither
       -- edge than a line of text: the two fils split the leftover.
       a.y < b.y && b.y < c.y &&
         (b.y - a.y - (c.y - b.y)).natAbs ≤ 1
     | _, _, _ => false)
  t "a leading fill alone pushes content to the bottom"
    (match low[0]?, mid[0]? with
     | some c, some b => c.y > b.y
     | _, _ => false)
  t "a trailing fill alone moves nothing"
    ((linesOf (doc "hello\n\\vspace*{\\fill}")).map (·.y) == top.map (·.y))
  -- A minipage is one column of declared width: the column model reused,
  -- not a parallel box model.
  t "minipage is one column of its declared width"
    ((elabStr (doc "\\begin{minipage}{0.5\\textwidth}x\\end{minipage}")).1.body ==
      #[.columns #[(.frac 500, #[.para #[.text "x"]])]])
  t "a bare textwidth minipage takes the whole measure"
    ((elabStr (doc "\\begin{minipage}{\\textwidth}x\\end{minipage}")).1.body ==
      #[.columns #[(.frac 1000, #[.para #[.text "x"]])]])
  t "minipage alignment options are a note, never an error"
    (let ds := (elabStr (doc "\\begin{minipage}[c][2cm][t]{\\textwidth}x\\end{minipage}")).2
     ds.all (·.severity != .error) && ds.any (·.code == "N0102"))
  -- \pagebreak: the declared boundary, asserted over the shipped pages.
  let pagesOf (src : String) : Nat :=
    let (d, _) := Elab.run "t" src
    (layoutOf oneFace d geom).pages.size
  t "pagebreak opens a fresh page"
    (pagesOf (doc "one\\pagebreak\ntwo") == 2)
  t "newpage and clearpage are the same boundary"
    (pagesOf (doc "one\\newpage\ntwo") == 2 &&
     pagesOf (doc "one\\clearpage\ntwo") == 2)
  t "adjacent pagebreaks never make a blank page"
    (pagesOf (doc "one\\pagebreak\\pagebreak\ntwo") == 2)
  t "a trailing pagebreak adds no empty page"
    (pagesOf (doc "one\\pagebreak") == 1)
  -- Native declarations in the body: \palette and \tokens apply where
  -- they stand (LaTeX's \colorlet and \setlength are body-legal) and ride
  -- the IR as .setPalette/.setTokens state blocks the backends replay in
  -- flow order. The document palette stays the preamble+theme state —
  -- epoch 0 — so a body declaration is confined to what follows it.
  let lastSetPalette (d : Ir.Doc) : Option Ir.Palette :=
    d.body.foldl (fun acc b => match b with
      | .setPalette p => some p
      | _ => acc) none
  let lastSetTokens (d : Ir.Doc) : Option Ir.Tokens :=
    d.body.foldl (fun acc b => match b with
      | .setTokens tk => some tk
      | _ => acc) none
  t "a body palette colours what follows through its own state block"
    (let (d, ds) := elabStr (doc "\\palette{ accent2 = #7C3AED }\\textcolor{accent2}{x}")
     ds.all (·.severity != .error) && ds.all (·.code != "W0304") &&
       (lastSetPalette d).bind (·.find? "accent2")
         == some { r := 0x7C, g := 0x3A, b := 0xED } &&
       d.palette.find? "accent2" == none)
  t "a body colorlet aliases a preamble colour in the flow state"
    (let (d, _) := elabStr
      "\\documentclass{article}\\definecolor{a}{HTML}{112233}\
\\begin{document}\\colorlet{b}{a}x\\end{document}"
     (lastSetPalette d).bind (·.find? "b") == some { r := 0x11, g := 0x22, b := 0x33 })
  t "a body setlength declares its token in the flow state"
    ((lastSetTokens (elabStr (doc "\\setlength{\\x}{4pt}y")).1).bind (·.find? "x")
      == some { width := .ofSp (Dim.pt 4) })
  t "a preamble-only declaration in the body is W0340, not unknown"
    (let ds := (elabStr (doc "x\n\n\\page{ size = a5 }\n\ny")).2
     ds.any (·.code == "W0340") && ds.all (·.code != "W0301") &&
       ds.all (·.severity != .error))
  -- CMYK: the print model survives as declared. The PDF paints DeviceCMYK
  -- with the declared components (asserted over the written bytes); the
  -- screen preview is the CSS Color 4 device-cmyk naive conversion, pinned
  -- here so it cannot drift silently.
  let (cdoc, cds) := elabStr
    "\\documentclass{article}\\definecolor{ink}{cmyk}{0,.83,.76,.07}\
\\begin{document}\\textcolor{ink}{x}\\end{document}"
  t "a cmyk definecolor lands in the palette with its components"
    (cds.all (·.severity != .error) && cds.all (·.code != "W0102") &&
      cdoc.palette.find? "ink" == some (Ir.Color.ofCmyk 0 830 760 70))
  t "the cmyk screen preview is the CSS device-cmyk conversion"
    (Ir.Color.ofCmyk 0 830 760 70 ==
      { r := 237, g := 40, b := 57, cmyk := some (0, 830, 760, 70) })
  let cpdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace cdoc geom).pages cdoc.info)
  t "the pdf paints a cmyk colour in DeviceCMYK, components as declared"
    (bytesContain cpdf "0 0.83 0.76 0.07 k")
  t "the html backend converts, explicitly, to the preview"
    (((HtmlDoc.emit {} cdoc).1.splitOn
        (HtmlDoc.cssColor (Ir.Color.ofCmyk 0 830 760 70))).length ≥ 2 &&
      HtmlDoc.cssColor (Ir.Color.ofCmyk 0 830 760 70) == "#ed2839")
  -- A colour expression keeps its model (xcolor §2.3.2: evaluated in the
  -- first colour's model). Before `mix` dispatched on the model, a
  -- CMYK-first mix was repainted as DeviceRGB — `0 0.502 0.502 rg` for
  -- `press!50!ink2` — and `cmyk_components_kept` covered atoms only.
  let (mdoc, mds) := elabStr
    "\\documentclass{article}\\definecolor{press}{cmyk}{1,0,0,0}\
\\definecolor{ink2}{cmyk}{0,0,0,1}\\definecolor{brand}{HTML}{336699}\
\\begin{document}\\textcolor{press!50!ink2}{x}\\end{document}"
  t "a cmyk-first mix of two cmyk atoms stays cmyk with exact components"
    (mds.all (·.severity != .error) &&
      (mdoc.palette.resolve "press!50!ink2").map (·.cmyk) == some (some (500, 0, 0, 500)))
  t "a trailing percentage mixes a cmyk colour toward cmyk white, exactly"
    ((mdoc.palette.resolve "press!50").map (·.cmyk) == some (some (500, 0, 0, 0)) &&
      (mdoc.palette.resolve "press!30!ink2!50").map (·.cmyk) == some (some (150, 0, 0, 350)))
  t "an rgb-first mix stays rgb whatever it mixes in"
    ((mdoc.palette.resolve "brand!50!press").map (·.cmyk) == some none &&
      (mdoc.palette.resolve "brand!50!press").map (·.model) == some Ir.Color.Model.srgb)
  t "an rgb atom enters a cmyk mix through xcolor's rgb→cmy→cmyk conversion"
    ((mdoc.palette.resolve "press!50!brand").map (·.cmyk) ==
      some (some (700, 100, 0, 200)) &&
      (mdoc.palette.resolve "press!50!brand").map (·.model) == some Ir.Color.Model.cmyk)
  t "the mixed cmyk colour's preview is its own declared-model preview"
    ((mdoc.palette.resolve "press!50!ink2") == some (Ir.Color.ofCmyk 500 0 0 500))
  let mpdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace mdoc geom).pages mdoc.info)
  t "the pdf paints a cmyk-first mix in DeviceCMYK, never as an rgb repaint"
    (bytesContain mpdf "0.5 0 0 0.5 k" && !bytesContain mpdf "0 0.502 0.502 rg")
  -- The print boxes follow from the declared bleed: pageBoxes_nest proves
  -- TrimBox ⊆ BleedBox ⊆ MediaBox with the trim at the declared size;
  -- this pins that the written page dictionary carries all three.
  let (bdoc, bds) := elabStr
    "\\documentclass{card}\\page{ bleed = 3mm }\\begin{document}x\\end{document}"
  let bgeom := Layout.Geom.ofPage bdoc.page
  let bpdf := pdfText (Pdf.write bgeom oneFace (layoutOf oneFace bdoc bgeom).pages bdoc.info)
  let (media, bleedBox, trim) := Pdf.pageBoxes bgeom.pageW bgeom.pageH bgeom.bleed
  t "a declared bleed writes trim, bleed and art boxes as consequences"
    (bds.all (·.severity != .error) &&
     bytesContain bpdf s!"/TrimBox {trim.render}" &&
     bytesContain bpdf s!"/BleedBox {bleedBox.render}" &&
     bytesContain bpdf s!"/ArtBox {trim.render}" &&
     bytesContain bpdf s!"/MediaBox {media.render}")
  t "zero bleed writes no boxes: the defaults already say all boxes coincide"
    (let (zdoc, _) := elabStr "\\documentclass{card}\\begin{document}x\\end{document}"
     let zgeom := Layout.Geom.ofPage zdoc.page
     let zpdf := pdfText (Pdf.write zgeom oneFace (layoutOf oneFace zdoc zgeom).pages zdoc.info)
     !bytesContain zpdf "/TrimBox" && !bytesContain zpdf "/BleedBox")

/-- The band projection over synthetic outlines: the invariant is that no
ink inside the band escapes the reported intervals, whatever its shape —
wholly inside the band, spanning it, or dipping into it at a curve
extremum. Scanline sampling missed the first and clipped the extent of
slanted strokes; the projection cannot. Band `[-100, -50]` matches the
shipped CFF faces' scale. -/
def inkGeometryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let iv (cmds : Array Ink.Cmd) (minY : Int) : Array (Int × Int) :=
    Ink.bandIntervals ⟨cmds, minY⟩ (-100) (-50)
  -- A rectangle wholly inside the band, spanning no scanline a sampler
  -- would choose: its projection is still its full width.
  let floatRectCmds : Array Ink.Cmd := #[.move 100 (-60), .line 200 (-60),
    .line 200 (-70), .line 100 (-70)]
  let floatRect := iv floatRectCmds (-70)
  t "ink: contour wholly inside the band is covered"
    (floatRect.size == 1 && floatRect.all fun (lo, hi) => lo ≤ 100 && hi ≥ 200)
  -- A tall rectangle spanning the band: the interior comes from the midline
  -- fill, not just the side edges.
  let tallRectCmds : Array Ink.Cmd := #[.move 300 0, .line 400 0,
    .line 400 (-200), .line 300 (-200)]
  let tallRect := iv tallRectCmds (-200)
  t "ink: contour spanning the band covers its full width"
    (tallRect.size == 1 && tallRect.all fun (lo, hi) => lo ≤ 300 && hi ≥ 400)
  -- A band-spanning contour with a curved side: chord vertices come from
  -- flattening, and one landing on the fill scanline drops the crossing
  -- pair there, so the stroke's interior vanishes from the report. The
  -- control point is chosen so a flattener that does not force even doubled
  -- coordinates puts its k=4 chord vertex exactly on the band's midline
  -- scanline (doubled y −149).
  let curvedSpanCmds : Array Ink.Cmd := #[.move 300 0, .line 400 0,
    .quad 405 (-49) 400 (-200), .line 300 (-200)]
  let curvedSpan := iv curvedSpanCmds (-200)
  t "ink: curve-sided contour spanning the band covers its full width"
    (curvedSpan.size == 1 && curvedSpan.all fun (lo, hi) => lo ≤ 300 && hi ≥ 400)
  -- A shallow curve dipping into the band: the lens between the quadratic
  -- and its chord lies inside, and its whole x-extent is reported even
  -- though only the extremum neighbourhood reaches the band's midline.
  let dipCmds : Array Ink.Cmd := #[.move 500 (-60), .quad 550 (-90) 600 (-60)]
  let dip := iv dipCmds (-75)
  t "ink: curve extremum reports the whole lens extent"
    (dip.size == 1 && dip.all fun (lo, hi) => lo ≤ 502 && hi ≥ 598)
  -- A slanted stroke through the band: ink between the entry and exit
  -- depths is continuous, so the report is one interval over the whole
  -- crossing, not samples with gaps.
  let slantCmds : Array Ink.Cmd := #[.move 700 (-40), .line 750 (-110),
    .line 770 (-110), .line 720 (-40)]
  let slant := iv slantCmds (-110)
  t "ink: slanted stroke is one gap-free interval"
    (slant.size == 1 && slant.all fun (lo, hi) => lo ≤ 709 && hi ≥ 761)
  -- Contours clear of the band report nothing.
  t "ink: contour above the band is empty"
    ((iv #[.move 0 0, .line 50 0, .line 50 (-40), .line 0 (-40)] (-40)).isEmpty)
  t "ink: contour below the band is empty"
    ((iv #[.move 0 (-120), .line 50 (-120), .line 50 (-160), .line 0 (-160)]
      (-160)).isEmpty)
  -- The coverage invariant against an oracle that shares nothing with the
  -- implementation: Float flattening at 32 chords and a half-open crossing
  -- rule, which counts exactly one of two edges meeting at a vertex on the
  -- scanline and so cannot lose a crossing pair there. Every ink run the
  -- oracle finds, at any height inside the band, must lie inside the
  -- reported intervals (2 font units of slack for the flattening
  -- difference).
  let oracleRuns (cmds : Array Ink.Cmd) (y : Float) : Array (Float × Float) := Id.run do
    let mut edges : Array (Float × Float × Float × Float) := #[]
    let mut cx : Float := 0
    let mut cy : Float := 0
    let mut sx : Float := 0
    let mut sy : Float := 0
    let mut opened := false
    for c in cmds do
      match c with
      | .move x yv =>
        if opened && (cx != sx || cy != sy) then
          edges := edges.push (cx, cy, sx, sy)
        cx := Float.ofInt x
        cy := Float.ofInt yv
        sx := cx
        sy := cy
        opened := true
      | .line x yv =>
        edges := edges.push (cx, cy, Float.ofInt x, Float.ofInt yv)
        cx := Float.ofInt x
        cy := Float.ofInt yv
      | .quad qx qy x yv =>
        let x0 := cx
        let y0 := cy
        let x1 := Float.ofInt qx
        let y1 := Float.ofInt qy
        let x2 := Float.ofInt x
        let y2 := Float.ofInt yv
        for k in [1:33] do
          let s := Float.ofNat k / 32
          let u := 1 - s
          let px := u * u * x0 + 2 * u * s * x1 + s * s * x2
          let py := u * u * y0 + 2 * u * s * y1 + s * s * y2
          edges := edges.push (cx, cy, px, py)
          cx := px
          cy := py
      | .cube ax ay bx by' x yv =>
        let x0 := cx
        let y0 := cy
        let x1 := Float.ofInt ax
        let y1 := Float.ofInt ay
        let x2 := Float.ofInt bx
        let y2 := Float.ofInt by'
        let x3 := Float.ofInt x
        let y3 := Float.ofInt yv
        for k in [1:33] do
          let s := Float.ofNat k / 32
          let u := 1 - s
          let px := u*u*u*x0 + 3*u*u*s*x1 + 3*u*s*s*x2 + s*s*s*x3
          let py := u*u*u*y0 + 3*u*u*s*y1 + 3*u*s*s*y2 + s*s*s*y3
          edges := edges.push (cx, cy, px, py)
          cx := px
          cy := py
    if opened && (cx != sx || cy != sy) then
      edges := edges.push (cx, cy, sx, sy)
    let mut xs : Array (Float × Int) := #[]
    for (x0, y0, x1, y1) in edges do
      if (y0 ≤ y && y < y1) || (y1 ≤ y && y < y0) then
        xs := xs.push (x0 + (x1 - x0) * (y - y0) / (y1 - y0),
          if y0 < y1 then 1 else -1)
    let sorted := xs.qsort fun a b => a.1 < b.1
    let mut runs : Array (Float × Float) := #[]
    let mut wind : Int := 0
    let mut lo : Float := 0
    for (x, d) in sorted do
      let w := wind + d
      if wind == 0 && w != 0 then
        lo := x
      if wind != 0 && w == 0 then
        runs := runs.push (lo, x)
      wind := w
    return runs
  let shapes : Array (String × Array Ink.Cmd × Int) :=
    #[("floatRect", floatRectCmds, -70), ("tallRect", tallRectCmds, -200),
      ("curvedSpan", curvedSpanCmds, -200), ("dip", dipCmds, -75),
      ("slant", slantCmds, -110)]
  for (name, cmds, minY) in shapes do
    let reported := iv cmds minY
    let mut escaped := false
    for j in [1:10] do
      let y : Float := -100 + 5 * Float.ofNat j
      for (a, b) in oracleRuns cmds y do
        if a + 2 < b - 2 then
          unless reported.any fun (rlo, rhi) =>
              Float.ofInt rlo ≤ a + 2 && b - 2 ≤ Float.ofInt rhi do
            escaped := true
    t s!"ink oracle: no {name} ink in the band escapes the report" (!escaped)
  -- Budget-exceeded outlines are undecodable, never silently truncated: a
  -- glyph declaring more contours or points than the decoder's budget is
  -- `none`, so the consumer clears its whole advance instead of trusting an
  -- incomplete decode. Minimal hand-built sfnts, one glyph each, yMin dipped
  -- below the band so the header shortcut cannot mask the decode.
  let mkSfnt (tables : Array (String × ByteArray)) : ByteArray := Id.run do
    let pushU16 (d : ByteArray) (v : Nat) : ByteArray :=
      (d.push (UInt8.ofNat (v / 256 % 256))).push (UInt8.ofNat (v % 256))
    let pushU32 (d : ByteArray) (v : Nat) : ByteArray :=
      pushU16 (pushU16 d (v / 65536)) (v % 65536)
    let mut d := pushU32 ByteArray.empty 0x00010000
    d := pushU16 d tables.size
    d := pushU16 (pushU16 (pushU16 d 0) 0) 0
    let mut off := 12 + 16 * tables.size
    for (tag, body) in tables do
      d := d ++ tag.toUTF8
      d := pushU32 d 0
      d := pushU32 d off
      d := pushU32 d body.size
      off := off + body.size
    for (_, body) in tables do
      d := d ++ body
    return d
  -- indexToLocFormat 0 at offset 50: short loca.
  let head52 : ByteArray := ⟨Array.replicate 52 (0 : UInt8)⟩
  let srcOf (glyf : Array UInt8) : Ink.Src :=
    let loca : ByteArray := ⟨#[0, 0, UInt8.ofNat (glyf.size / 2 / 256),
      UInt8.ofNat (glyf.size / 2 % 256)]⟩
    Ink.Src.make (mkSfnt #[("head", head52), ("loca", loca), ("glyf", ⟨glyf⟩)])
      false 1
  -- numberOfContours 200 (budget 128); yMin -200.
  let overContours : Array UInt8 :=
    #[0, 200, 0, 0, 0xFF, 0x38] ++ Array.replicate 14 (0 : UInt8)
  t "ink: contour budget exceeded is undecodable"
    ((srcOf overContours).inkAt 0 (-100) (-50) |>.isNone)
  -- one contour whose endPtsOfContours declares 5001 points (budget 4096).
  let overPoints : Array UInt8 :=
    #[0, 1, 0, 0, 0xFF, 0x38, 0, 0, 0, 0, 19, 136] ++ Array.replicate 8 (0 : UInt8)
  t "ink: point budget exceeded is undecodable"
    ((srcOf overPoints).inkAt 0 (-100) (-50) |>.isNone)
  -- A composite whose declared bbox lies: the header says yMin 0, clear of
  -- the band, but its component (glyph 0, a square reaching y −200) spans
  -- it. The declared box is only the glyph's own point bbox for a simple
  -- glyph; a composite's must be decoded, so a yMin shortcut trusting it
  -- would paint a rule through ink.
  let g0 : Array UInt8 :=
    -- one contour, bbox (0,−200)–(100,0), 4 on-curve points
    #[0, 1,  0, 0,  0xFF, 0x38,  0, 100,  0, 0,
      0, 3,  0, 0,
      0x31, 0x33, 0x15, 0x23,
      100, 100, 200,
      0]  -- pad to even length for short loca
  let g1 : Array UInt8 :=
    -- numberOfContours −1; bbox declares yMin 0; one component: glyph 0,
    -- word xy args (0,0), no MORE_COMPONENTS
    #[0xFF, 0xFF,  0, 0,  0, 0,  0, 100,  0, 0,
      0, 3,  0, 0,  0, 0,  0, 0]
  let compSrc : Ink.Src :=
    let glyf := g0 ++ g1
    let loca : ByteArray := ⟨#[0, 0,
      0, UInt8.ofNat (g0.size / 2),
      0, UInt8.ofNat (glyf.size / 2)]⟩
    Ink.Src.make (mkSfnt #[("head", head52), ("loca", loca), ("glyf", ⟨glyf⟩)])
      false 2
  t "ink: composite with a lying bbox is decoded, not trusted"
    (compSrc.inkAt 1 (-100) (-50) == some #[(0, 100)])
  t "ink: the lying composite's simple component answers for itself"
    (compSrc.inkAt 0 (-100) (-50) == some #[(0, 100)])

/-- Native underline: a decoration never breaks a glyph. Drawn from the
font's own `post` metrics and interrupted where a glyph's outline ink
crosses the rule's band, with clearance either side — `q` keeps its rule
under the bowl and clears it at the stem; `text-decoration-skip-ink` is the
browser's spelling of the same invariant. Undecodable outlines clear their
whole advance. Both outline formats are exercised: Open Sans is TrueType
`glyf`, Source Serif Pro is CFF Type 2 charstrings. Own function, same
elaboration-budget reason as the others. -/
def linkSignalChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Colour is never the only signal (WCAG 2.2 SC 1.4.1). A link's
  -- affordance is the underline in both backends -- the HTML anchor keeps
  -- the browser's, and the PDF path draws one: before this, a PDF link had
  -- no visual signal at all, not even colour.
  let out := layoutOf oneFace
    (Elab.run "t" "see \\href{https://example.org/}{the example} here").1 geom
  let segs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  let linkRuns := segs.filterMap fun s => match s with
    | .run _ _ (some _) _ _ _ ul _ _ _ => some ul
    | _ => none
  t "pdf link runs exist" (!linkRuns.isEmpty)
  t "pdf link runs are underlined" (linkRuns.all (· == true))
  t "pdf link draws its underline rule" (segs.any fun s => match s with
    | .rule .. => true
    | _ => false)

def underlineChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font.Font) : IO Unit := do
  let t := check ref
  -- IR shape
  t "underline ir shape" ((elabStr "\\underline{a}").1.body ==
    #[.para #[.underline #[.text "a"]]])
  t "uline is underline" ((elabStr "\\uline{b}").1.body ==
    #[.para #[.underline #[.text "b"]]])
  -- The font's own glyph outlines decide what interrupts the rule.
  let gidOf (c : Char) : Nat := (font.gid c).getD 0
  let hasInk (c : Char) : Bool := !(font.inkAt (gidOf c)).isEmpty
  t "g has ink in the band" (hasInk 'g')
  t "y has ink in the band" (hasInk 'y')
  -- Band containment is per-face (post values are fallback-normalized, so
  -- it is not a theorem past the position `underline_in_descent` covers):
  -- on every shipped fixture face the whole band — position down to
  -- position minus thickness — stays inside the metric descent, so the
  -- rule and the descenders it clears share one region.
  let shipped ← FontDb.scanRoots [testFonts]
  let mut bandOk := true
  for face in shipped do
    if let .ok f := Font.parse (← IO.FS.readBinFile face.path) then
      let (p, th) := f.band
      unless f.descent ≤ p - th && p < 0 do bandOk := false
  t "every shipped face's underline band stays in its descent" bandOk
  t "a has no ink in the band" (!hasInk 'a')
  t "x-height b has no ink in the band" (!hasInk 'b')
  t "comma has ink in the band" (hasInk ',')
  t "parens have ink in the band" (hasInk '(' && hasInk ')')
  -- Ink is an interval, not the whole advance: q's stem crosses the band on
  -- the right of its bowl, so its interval starts past the advance midpoint
  -- and is far narrower than the glyph.
  let qAdv : Int := font.widths[gidOf 'q']?.getD 0
  let qInk := font.inkAt (gidOf 'q')
  t "q ink is a narrow interval, not the advance"
    (qInk.size == 1 && qInk.all fun (lo, hi) =>
      lo > qAdv / 2 && hi - lo < qAdv / 3)
  -- Double-storey g crosses the band twice: the ear side and the tail loop.
  t "g ink is two intervals" ((font.inkAt (gidOf 'g')).size == 2)
  -- ç is a composite (c plus a cedilla component): composites decode
  -- through their components, so the obstruction is the cedilla's narrow
  -- crossing, not a conservative whole advance.
  let cedAdv : Int := font.widths[gidOf 'ç']?.getD 0
  let cedInk := font.inkAt (gidOf 'ç')
  t "composite ç ink is the cedilla, not the advance"
    (cedInk.size == 1 && cedInk.all fun (lo, hi) => lo > 0 && hi < cedAdv)
  -- The lazy per-glyph decode is memoized: Lean's `Thunk` is call-by-need
  -- (`Thunk.get` caches in the runtime object), so a repeated glyph decodes
  -- once however often layout asks. 100k forced reads must land orders of
  -- magnitude under 100k fresh decodes (tens of µs each) — the bound fails
  -- by more than an order of magnitude if each read decoded afresh.
  let t0 ← IO.monoMsNow
  let mut inkReads := 0
  for _ in [0:100000] do
    inkReads := inkReads + (font.inkAt (gidOf 'q')).size
  let inkMs := (← IO.monoMsNow) - t0
  t s!"repeated glyph ink is memoized ({inkMs} ms for {inkReads} reads)"
    (inkReads == 100000 && inkMs < 500)
  -- Layout: rule segs under the underlined run, split around actual ink.
  let outOf (fs : Font.FontSet) (src : String) : Layout.Out :=
    layoutOf fs (Elab.run "t" src).1 geom
  let rulesOf (fs : Font.FontSet) (src : String) : Array (Dim.Sp × Dim.Sp) :=
    ((outOf fs src).pages.flatMap (·.lines)).flatMap (·.segs.filterMap fun s =>
      match s with
      | .rule w th _ _ => some (w, th)
      | _ => none)
  let widthOf (fs : Font.FontSet) (src : String) : Dim.Sp :=
    (((outOf fs src).pages.flatMap (·.lines))[0]?.map (·.setWidth)).getD 0
  let coverage (fs : Font.FontSet) (src : String) : Dim.Sp × Dim.Sp :=
    ((rulesOf fs src).foldl (fun acc (w, _) => acc + w) (0 : Dim.Sp),
     widthOf fs src)
  t "underline emits a rule" ((rulesOf oneFace "\\underline{ab}").size ≥ 1)
  t "plain text emits no rule" ((rulesOf oneFace "ab").isEmpty)
  -- A descender inside the word splits the rule into pieces around its
  -- stroke, so a one-word underline with an interior 'q' carries at least
  -- two, and the pieces cover strictly less than the set width.
  t "underline splits around a descender" ((rulesOf oneFace "\\underline{aqa}").size ≥ 2)
  let (aqaRules, aqaWidth) := coverage oneFace "\\underline{aqa}"
  t "underline leaves a gap at the descender" (0 < aqaRules && aqaRules < aqaWidth)
  -- The load-bearing shape of the invariant: a lone underlined q keeps its
  -- rule under the bowl — most of the advance — rather than losing all of
  -- it, and the gap at the stem is real.
  let (qRules, qWidth) := coverage oneFace "\\underline{q}"
  t "underlined q keeps rule under its bowl" (qRules > qWidth * 2 / 5)
  t "underlined q still clears its stem" (qRules < qWidth)
  -- Adjacent descenders each interrupt only at their own stroke: gy keeps
  -- rule under g's bowl and between the strokes, where the whole-advance
  -- skip left nothing at all.
  let (gyRules, gyWidth) := coverage oneFace "\\underline{gy}"
  t "underline under gy keeps some rule" (0 < gyRules && gyRules < gyWidth)
  -- Punctuation that reaches down interrupts too.
  t "underline splits at a comma" ((rulesOf oneFace "\\underline{a,a}").size ≥ 2)
  -- A longer word with spread descenders: interrupted more than once, most
  -- of the rule intact.
  let (genRules, genWidth) := coverage oneFace "\\underline{genuinely}"
  t "genuinely keeps most of its rule"
    ((rulesOf oneFace "\\underline{genuinely}").size ≥ 3 &&
     genRules > genWidth / 2 && genRules < genWidth)
  -- The rules ride their own line at the text line's baseline, so the PDF
  -- writer's x-tracking stays linear and link rectangles see no extra runs.
  let abLines := bodyLines (outOf oneFace "\\underline{ab}")
  t "underline rules ride a second line at the same y"
    (abLines.size == 2 && abLines[0]!.y == abLines[1]!.y &&
     abLines[1]!.segs.all fun s => match s with
      | .run .. => false
      | _ => true)
  -- The CFF path (Type 2 charstrings) answers the same questions from its
  -- own outlines.
  let serifPath := testFonts ++ "/SourceSerifPro-Regular.otf"
  if ← System.FilePath.pathExists serifPath then
    match Font.parse (← IO.FS.readBinFile serifPath) with
    | .error e => failures ref s!"underline cff parse: {e}"
    | .ok serif =>
      let sgid (c : Char) : Nat := (serif.gid c).getD 0
      let sqAdv : Int := serif.widths[sgid 'q']?.getD 0
      let sqInk := serif.inkAt (sgid 'q')
      t "cff q ink is a narrow interval, not the advance"
        (sqInk.size == 1 && sqInk.all fun (lo, hi) =>
          lo > sqAdv / 2 && hi - lo < sqAdv / 3)
      t "cff g ink is two intervals" ((serif.inkAt (sgid 'g')).size == 2)
      t "cff a has no ink in the band" ((serif.inkAt (sgid 'a')).isEmpty)
      let serifSet : Font.FontSet := {
        fonts := #[serif]
        index := ((List.range 3).flatMap fun slot =>
          [((slot, 400, false), 0), ((slot, 700, false), 0),
           ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray
      }
      let (cqRules, cqWidth) := coverage serifSet "\\underline{q}"
      t "cff underlined q keeps rule under its bowl"
        (cqRules > cqWidth * 2 / 5 && cqRules < cqWidth)
      -- Obstructions live in line coordinates, so ink reaching over a run
      -- boundary clears the neighbouring rule. Both directions: the italic
      -- g's negative left sidebearing reaches back into the upright a's
      -- rule, and an upright g's clearance spills forward past its advance
      -- into the underlined a that follows it.
      let itPath := testFonts ++ "/SourceSerifPro-RegularIt.otf"
      if ← System.FilePath.pathExists itPath then
        match Font.parse (← IO.FS.readBinFile itPath) with
        | .error e => failures ref s!"underline italic parse: {e}"
        | .ok serifIt =>
          let mixedSet : Font.FontSet := {
            fonts := #[serif, serifIt]
            index := ((List.range 3).flatMap fun slot =>
              [((slot, 400, false), 0), ((slot, 700, false), 0),
               ((slot, 400, true), 1), ((slot, 700, true), 1)]).toArray
          }
          let firstRunAndRule (src : String) : Dim.Sp × Dim.Sp := Id.run do
            let lines := ((outOf mixedSet src).pages.flatMap (·.lines))
            let runW := ((lines[0]?.map (·.segs)).getD #[]).filterMap fun s =>
              match s with
              | .run _ _ _ w _ _ _ _ _ _ => some w
              | _ => none
            let ruleW := ((lines[1]?.map (·.segs)).getD #[]).filterMap fun s =>
              match s with
              | .rule w _ _ _ => some w
              | _ => none
            return (runW[0]?.getD 0, ruleW[0]?.getD 0)
          let (aW, aRule) := firstRunAndRule "\\underline{a\\textit{g}}"
          t "italic overhang clears the rule across the style boundary"
            (aW > 0 && aRule > 0 && aRule < aW)
          let (gW, gRule) := firstRunAndRule "\\textit{g}\\underline{a}"
          t "a neighbouring run's descender clears the adjacent rule"
            (gW > 0 && gRule > 0 && gRule < (firstRunAndRule "\\textit{a}\\underline{a}").2)
  else
    failures ref s!"underline: {serifPath} missing from the checkout"
  -- Truncated font data: forcing the lazy ink of every descender-ish glyph
  -- on every truncation that still parses must return a verdict, never
  -- panic — and the verdict is conservative: what the intact outline tables
  -- say for that font's own normalized band (a cut can drop `post`, moving
  -- the band to the default) when the outlines survived, the whole advance
  -- when they did not. A rule through ink is never among the outcomes.
  match ← findFont with
  | some fontData =>
    match Font.parse fontData with
    | .error e => failures ref s!"underline: full font parse: {e}"
    | .ok full =>
      let intact := Ink.Src.make fontData full.isCff full.numGlyphs
      let mut checked := 0
      let mut conservative := true
      for k in [0:64] do
        match Font.parse (fontData.extract 0 (fontData.size * k / 64)) with
        | .error _ => pure ()
        | .ok f =>
          let (bpos, bthick) := f.band
          for c in "gqy,()".toList do
            let g := (f.gid c).getD 0
            let whole := #[((0 : Int), (f.widths[g]?.getD 0 : Int))]
            checked := checked + 1
            unless f.inkAt g == whole ||
                some (f.inkAt g) == intact.inkAt g (bpos - bthick) bpos do
              conservative := false
      t s!"truncated ink is the intact intervals or the whole advance ({checked} checked)"
        (checked > 0 && conservative)
  | none => pure ()
  -- Undecodable outline tables are conservative for every glyph: corrupt
  -- the outline table's directory entry (length past the file) and the font
  -- still parses, but 'a' — no descender, not on any character list — now
  -- obstructs its whole advance, because a rule cannot be trusted over ink
  -- the decoder cannot see.
  let corruptTable (tag : String) (d0 : ByteArray) : ByteArray := Id.run do
    let mut d := d0
    let n := Ink.u16 d 4
    for k in [0:n] do
      let entry := 12 + 16 * k
      if entry + 16 ≤ d.size && d.extract entry (entry + 4) == tag.toUTF8 then
        for j in [0:4] do
          d := d.set! (entry + 12 + j) 0xFF
    return d
  match ← findFont with
  | some fontData =>
    match Font.parse (corruptTable "loca" fontData) with
    | .error e => failures ref s!"underline: corrupt loca parse: {e}"
    | .ok f =>
      let g := (f.gid 'a').getD 0
      t "corrupt loca: a obstructs its whole advance"
        (f.inkAt g == #[(0, (f.widths[g]?.getD 0 : Int))])
  | none => pure ()
  if ← System.FilePath.pathExists serifPath then
    match Font.parse (corruptTable "CFF " (← IO.FS.readBinFile serifPath)) with
    | .error e => failures ref s!"underline: corrupt CFF parse: {e}"
    | .ok f =>
      let g := (f.gid 'a').getD 0
      t "corrupt CFF: a obstructs its whole advance"
        (f.inkAt g == #[(0, (f.widths[g]?.getD 0 : Int))])
  -- Underline metrics normalize through one helper shared by ink extraction
  -- and rule placement: a `post` table declaring an implausible position
  -- (above the baseline, or below the face's descender line — a rule
  -- there would leave the descender region, `underline_in_descent`) or
  -- thickness (nonpositive, or over a quarter em) falls back to the
  -- convention, each independently.
  t "band: declared plausible values pass" (Font.underlineBand 2048 (-500) (-154) 102 == (-154, 102))
  t "band: zero position falls back" ((Font.underlineBand 1000 (-250) 0 50).1 == -100)
  t "band: positive position falls back" ((Font.underlineBand 1000 (-250) 200 50).1 == -100)
  t "band: absurdly deep position falls back" ((Font.underlineBand 1000 (-250) (-30000) 50).1 == -100)
  t "band: a position below the descender line falls back"
    ((Font.underlineBand 1000 (-250) (-300) 50).1 == -100)
  t "band: zero thickness falls back" ((Font.underlineBand 1000 (-250) (-50) 0).2 == 50)
  t "band: negative thickness falls back" ((Font.underlineBand 1000 (-250) (-50) (-80)).2 == 50)
  t "band: absurdly thick falls back" ((Font.underlineBand 1000 (-250) (-50) 900).2 == 50)
  t "band: one bad value keeps the other" (Font.underlineBand 1000 (-250) (-50) (-80) == (-50, 50))
  -- End to end: a font whose post table declares a positive position and a
  -- negative thickness still draws a positive-thickness rule below the
  -- baseline.
  match ← findFont with
  | some fontData =>
    let patched := Id.run do
      let mut d := fontData
      match Ink.findTable d "post" with
      | some post =>
        -- underlinePosition at offset 8, underlineThickness at 10: put
        -- +200 and -80 (big-endian FWords).
        d := d.set! (post.offset + 8) 0x00
        d := d.set! (post.offset + 9) 200
        d := d.set! (post.offset + 10) 0xFF
        d := d.set! (post.offset + 11) (0x100 - 80)
        return d
      | none => return d
    match Font.parse patched with
    | .error e => failures ref s!"underline: patched post parse: {e}"
    | .ok bad =>
      t "band: patched font reads the absurd metrics"
        (bad.underlinePosition == 200 && bad.underlineThickness == -80)
      let badSet : Font.FontSet := {
        fonts := #[bad]
        index := ((List.range 3).flatMap fun slot =>
          [((slot, 400, false), 0), ((slot, 700, false), 0),
           ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray
      }
      let badRules := ((outOf badSet "\\underline{ab}").pages.flatMap
        (·.lines)).flatMap (·.segs.filterMap fun s =>
          match s with
          | .rule w th raise _ => some (w, th, raise)
          | _ => none)
      t "band: absurd post metrics still rule below the baseline"
        (badRules.size ≥ 1 && badRules.all fun (w, th, raise) =>
          w > 0 && th > 0 && raise < 0)
  | none => pure ()
  -- HTML: <u> plus the skip-ink stylesheet; links get the same treatment.
  let (uPage, _) := HtmlDoc.emit {} (elabStr "\\underline{x}").1
  t "html underline is u" ((uPage.splitOn "<u>x</u>").length == 2)
  t "html u skips ink"
    ((uPage.splitOn "u { text-decoration: underline; text-decoration-skip-ink: auto;").length == 2)
  t "html links skip ink" ((uPage.splitOn "text-decoration-skip-ink").length ≥ 3)
  -- Compat: soul's \ul and the xparse \varul spelling become the native.
  t "compat ul" ((elabStr "\\ul{x}").1.body == #[.para #[.underline #[.text "x"]]])
  t "compat varul drops its options"
    ((elabStr "\\varul<5>[0.2ex][0.1ex]{x}").1.body ==
      #[.para #[.underline #[.text "x"]]])
  t "compat varul without options"
    ((elabStr "\\varul{x}").1.body == #[.para #[.underline #[.text "x"]]])
  t "compat soul is a note"
    ((elabStr ("\\documentclass{article}\\usepackage{soul}" ++
      "\\begin{document}x\\end{document}")).2.all (·.severity == .note))
  -- A document's own \varul definition loses to the native, with the
  -- existing built-in warning saying so.
  let redef := elabStr ("\\documentclass{article}" ++
    "\\NewDocumentCommand{\\varul}{ O{} m }{#2}" ++
    "\\begin{document}\\varul{y}\\end{document}")
  t "document varul definition is ignored"
    ((redef.2.filter (·.severity == .warning)).any (·.code == "W0303") &&
     redef.1.body == #[.para #[.underline #[.text "y"]]])

/-- Vertical spacing is TeX's, checked on the placed lines. Own function,
same elaboration-budget reason as the others. -/
def spacingChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font.Font) : IO Unit := do
  let t := check ref
  let ysOf (g : Layout.Geom) (src : String) : Array Dim.Sp :=
    -- Text lines only: an underline rule rides a sibling line at the same y.
    ((layoutOf oneFace (Elab.run "t" src).1 g).pages.flatMap (·.lines)).filterMap fun l =>
      if !l.furniture &&
          l.segs.any (fun s => match s with | .run .. => true | _ => false) then some l.y else none
  let pagesOf (g : Layout.Geom) (src : String) : Nat :=
    (layoutOf oneFace (Elab.run "t" src).1 g).pages.size
  let body := geom.fontSize
  let leading := Ir.leadingFor body geom.leading
  let scaled (sz : Dim.Sp) (units : Int) : Dim.Sp := units * sz / font.unitsPerEm
  let leadedAt (sz : Dim.Sp) : Dim.Sp × Dim.Sp :=
    Layout.leadedBox (scaled sz font.ascent) (scaled sz (-font.descent))
      (Ir.leadingFor sz geom.leading)
  -- Interline is the metric rule (CSS 2.1 §10.8.1): the previous line's
  -- leaded below plus this line's leaded above — for uniform text exactly
  -- one leading, and after a Huge line the Huge box's own below, never a
  -- collision term.
  let plain := ysOf geom "a\n\nb"
  t "peers sit a leading plus parskip apart"
    (plain.size == 2 && plain[1]! - plain[0]! == leading + (geom.parskip.resolve body 0).width)
  -- A blank line that survives TeX's comment rule is the same boundary: a
  -- comment line before it hides its own end-of-line, not the blank line
  -- (`Lex.blank_line_par_agree`). Judged on the placed baselines, as the
  -- peer gap above is — two paragraphs, the declared peer gap between.
  let commented := ysOf geom "a\n  % an aside\n\n  b"
  t "peers stay peers across a comment line before the blank line"
    (commented.size == 2 && commented[1]! - commented[0]! == plain[1]! - plain[0]!)
  -- A display formula stands inside the display skips, not the peer gap:
  -- paragraph, display, paragraph places three baselines whose two gaps
  -- each exceed the leading by the resolved `abovedisplayskip` /
  -- `belowdisplayskip` — the default at the governing size, the token
  -- where the document declares one, and the numbered `{equation}` the
  -- same. Asserted over `Layout.Out`, never the IR (AGENTS).
  let dispSkip := (Ir.displaySkipDefault body).resolve body 0
  let disp := ysOf geom "a\n\n\\[ x = 1 \\]\n\nb"
  t "a display formula opens the display skip above and below"
    (disp.size == 3 && disp[1]! - disp[0]! == leading + dispSkip.width &&
      disp[2]! - disp[1]! == leading + dispSkip.width)
  t "the display skip is not the peer gap"
    (dispSkip.width != (geom.parskip.resolve body 0).width)
  let eqn := ysOf geom "a\n\n\\begin{equation} x = 1 \\end{equation}\n\nb"
  t "a numbered equation opens the same display skips"
    (eqn.size == 3 && eqn[1]! - eqn[0]! == leading + dispSkip.width &&
      eqn[2]! - eqn[1]! == leading + dispSkip.width)
  let declared := ysOf geom
    "\\tokens{ abovedisplayskip = 30pt, belowdisplayskip = 3pt }a\n\n\\[ x = 1 \\]\n\nb"
  t "declared display skips are the ones paid, above and below apart"
    (declared.size == 3 && declared[1]! - declared[0]! == leading + Dim.pt 30 &&
      declared[2]! - declared[1]! == leading + Dim.pt 3)
  let inlineDisp := ysOf geom "a $x$ b\n\nc"
  t "an inline formula opens no display skip"
    (inlineDisp.size == 2 &&
      inlineDisp[1]! - inlineDisp[0]! == leading + (geom.parskip.resolve body 0).width)
  let huge := ysOf geom "{\\Huge Title \\par}\n\nbody"
  let hugeSize := body * 2488 / 1000
  t "a Huge title ends one paragraph, not two lines" (huge.size == 2)
  t "the line after a Huge title is spaced by the metric rule"
    (huge.size == 2 && huge[1]! - huge[0]! ==
      (leadedAt hugeSize).2 + (leadedAt body).1 + (geom.parskip.resolve body 0).width)
  t "the line after a Huge title is not a Huge leading away"
    (huge.size == 2 && huge[1]! - huge[0]! < Ir.leadingFor hugeSize geom.leading)
  t "the first line hangs the title's own leaded ascent below the margin"
    (huge.size == 2 && huge[0]! == geom.vmargin + max (scaled body font.ascent) (leadedAt hugeSize).1)
  -- The grid, realized: a uniform paragraph's baselines sit exactly one
  -- leading apart — `baselines_on_grid`'s algebra on the shipped page,
  -- unconditional, no per-font inequality.
  let uni := ysOf geom (String.intercalate " " (List.replicate 60 "grid"))
  t "uniform baselines sit on the grid"
    (uni.size ≥ 3 && (uni.zip (uni.extract 1 uni.size)).all
      (fun (a, b) => b - a == leading))
  -- A mid-paragraph size change displaces by the larger leaded box —
  -- deterministic and glyph-free — and the paragraph returns to the grid
  -- on the next uniform pair: the documented cost of honest metrics.
  let mixed := ysOf geom ("{\\Huge M} " ++
    String.intercalate " " (List.replicate 60 "grid"))
  t "a size change displaces by the metric rule and leaves the grid"
    (mixed.size ≥ 3 && mixed[1]! - mixed[0]! == (leadedAt hugeSize).2 + (leadedAt body).1 &&
     mixed[1]! - mixed[0]! != leading && mixed[2]! - mixed[1]! == leading)
  -- The heading rule is raised half the x-height of the heading's own
  -- face at the heading's size — never the body's — asserted over
  -- `Layout.Out`, per AGENTS: a visual bug's regression never reads an IR
  -- dump. The x-height is the measured ink 'x' (`Font.xHeightOptical`).
  let rdoc := (Elab.run "t" ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink }\\begin{document}\\section{S}x\\end{document}")).1
  let ruleRaises := ((layoutOf oneFace rdoc geom).pages.flatMap (·.lines)).filterMap
    fun l => if l.furniture then none else
      l.segs.findSome? fun s => match s with
        | .rule _ _ raise _ => if raise > 0 then some raise else none
        | _ => none
  t "the heading rule sits at half the heading's own x-height"
    (ruleRaises ==
      #[(font.xHeightOptical : Int) * Layout.sectionSize geom 1 / font.unitsPerEm / 2])
  -- TeX's `\leaders\hrule height h` has zero depth: its bottom edge is the
  -- heading's baseline and `h` is its thickness. Position and thickness
  -- are one IR fact (`Ir.RulePosition`, `heading_rule_position_exact`);
  -- `Seg.rule`'s raise is its projection, so a baseline rule is raise 0
  -- and the native `rule = c` keeps exactly the x-height raise above.
  let firstRule (d : Ir.Doc) : Array (Int × Int) :=
    ((layoutOf oneFace d geom).pages.flatMap (·.lines)).filterMap
      fun l => if l.furniture then none else
        l.segs.findSome? fun s => match s with
          | .rule _ th raise _ => some (th, raise)
          | _ => none
  let komaRule := (Elab.run "t" ("\\documentclass{scrartcl}\\definecolor{ink}{HTML}{112233}" ++
    "\\makeatletter\\renewcommand\\sectionlinesformat[4]{#3#4 \\textcolor{ink}{\\leaders\\hrule height 2pt\\hfill}}\\makeatother" ++
    "\\begin{document}\\section{S}x\\end{document}")).1
  t "a TeX hrule heading rule sits on the baseline at its declared height"
    (firstRule komaRule == #[(Dim.pt 2, 0)])
  let nativeBaseline := (Elab.run "t" ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink, rule-position = baseline, rule-thickness = 2pt }" ++
    "\\begin{document}\\section{S}x\\end{document}")).1
  t "a native baseline rule is the same Layout.Out fact"
    (firstRule nativeBaseline == firstRule komaRule)
  -- The synthetic résumé shape: a huge centred title, a two-line contact
  -- block, a ruled section and its first entry. The rule's bottom is the
  -- section title's baseline, and the section's declared `before` stays
  -- above the title block's declared gap in the placed baselines.
  let heroDoc := (Elab.run "t" ("\\documentclass{scrartcl}\\definecolor{ink}{HTML}{112233}" ++
    "\\makeatletter\\renewcommand\\sectionlinesformat[4]{#3#4 \\textcolor{ink}{\\leaders\\hrule height 1pt\\hfill}}\\makeatother" ++
    "\\begin{document}\\begin{center}{\\Huge\\bfseries Placeholder Person}\\\\[2ex]" ++
    "one@example.org\\\\ example.org\\end{center}" ++
    "\\section{Experience}Entry title\\end{document}")).1
  let heroLines := ((layoutOf oneFace heroDoc geom).pages.flatMap (·.lines)).filter (!·.furniture)
  let ruledLine := heroLines.find? fun l => l.segs.any fun s => match s with
    | .rule .. => true | _ => false
  t "the synthetic hero page draws its section rule on the section baseline"
    ((ruledLine.bind fun l => l.segs.findSome? fun s => match s with
        | .rule _ th raise _ => some (th, raise)
        | _ => none) == some (Dim.pt 1, 0))
  t "the synthetic hero page sets title, two contact lines, section, entry"
    (heroLines.size == 5 && (heroLines.zip (heroLines.extract 1 heroLines.size)).all
      fun (a, b) => a.y < b.y)
  -- Gaps: a bare `\vspace` is a `\vskip` — it adds, both to other declared
  -- glue and to the peer parskip TeX contributes when the *following*
  -- paragraph starts (`Layout.skip_monotone`). An element's own space (a
  -- list's topsep, a heading's or a role's `before`, `\block[before]{body}`)
  -- takes the larger against what is owed and stands in place of the peer
  -- default, as LaTeX's `\addvspace` does.
  let pq := Ir.rhythmQuantum geom.fontSize
  let vs := ysOf geom "a\n\n\\vspace{20pt}\nb"
  t "a bare vspace adds to parskip"
    (vs.size == 2 && vs[1]! - vs[0]! == leading + pq + Dim.pt 20)
  -- The regression: a positive skip between two paragraphs must never bring
  -- them closer. `\smallskip` did exactly that — its 3pt stood in place of
  -- the 6pt parskip it displaced, so inserting glue narrowed the gap by 3pt.
  let plain := ysOf geom "a\n\nb"
  let gapOf (mid : String) : Option Dim.Sp :=
    let ys := ysOf geom ("a\n\n" ++ mid ++ "\nb")
    if ys.size == 2 then some (ys[1]! - ys[0]!) else none
  let plainGap : Option Dim.Sp :=
    if plain.size == 2 then some (plain[1]! - plain[0]!) else none
  t "a positive skip never narrows the paragraph gap"
    (["\\smallskip", "\\medskip", "\\bigskip", "\\vspace{1pt}"].all fun m =>
      match gapOf m, plainGap with
      | some g, some p => decide (g ≥ p)
      | _, _ => false)
  t "the skip macros add LaTeX's own 3/6/12pt above the peer gap"
    (([("\\smallskip", 3), ("\\medskip", 6), ("\\bigskip", 12)] : List (String × Int)).all
      fun (m, n) => gapOf m == some (leading + pq + Dim.pt n))
  let blk := ysOf geom "a\n\n\\block[before = 20pt]{b}"
  t "block before is the gap" (blk.size == 2 && blk[1]! - blk[0]! == leading + Dim.pt 20)
  let listSrc (mid : String) := "\\documentclass{article}\\style{itemize}{ before = 10pt }" ++
    "\\begin{document}a\\begin{itemize}\\item b\\end{itemize}" ++ mid ++ "c\\end{document}"
  let ls := ysOf geom (listSrc "")
  t "list topsep stands above the list" (ls.size == 3 && ls[1]! - ls[0]! == leading + Dim.pt 10)
  t "list topsep stands below the list too" (ls.size == 3 && ls[2]! - ls[1]! == leading + Dim.pt 10)
  let lv := ysOf geom (listSrc "\\vspace{7pt}")
  t "a vspace after a list adds to its topsep and the peer gap"
    (lv.size == 3 && lv[2]! - lv[1]! == leading + pq + Dim.pt 17)
  let secSrc := "\\documentclass{article}\\style{itemize}{ before = 10pt }" ++
    "\\style{section}{ before = 15pt, after = 4pt }" ++
    "\\begin{document}\\begin{itemize}\\item b\\end{itemize}\\section{S}c\\end{document}"
  let sec := ysOf geom secSrc
  t "a heading after a list takes the larger space, not the sum"
    (sec.size == 3 && sec[1]! - sec[0]! ==
      (leadedAt body).2 + (leadedAt (Layout.sectionSize geom 1)).1 + Dim.pt 15)
  -- parskip is a page property with rubber.
  let g0 := ysOf { geom with parskip := { width := Dim.Length.ofSp 0 } } "a\n\nb"
  t "parskip zero sets peers one leading apart" (g0.size == 2 && g0[1]! - g0[0]! == leading)
  let (pDoc, pDs) := elabStr ("\\documentclass{article}\\page{ parskip = 3pt plus 1pt minus 1pt }" ++
    "\\begin{document}x\\end{document}")
  t "page parskip declared" (pDs.isEmpty && pDoc.page.parskip ==
    some { width := Dim.Length.ofSp (Dim.pt 3), stretch := Dim.Length.ofSp (Dim.pt 1),
           shrink := Dim.Length.ofSp (Dim.pt 1) })
  -- A page is set like a line: skips shrink, within their limits, before a
  -- break is taken; beyond them the page breaks.
  let firstY := geom.vmargin + scaled body font.ascent
  let three := "a\n\n\\vspace{20pt minus 8pt}\nb\n\n\\vspace{20pt minus 8pt}\nc"
  let natural := firstY + 2 * (leading + pq + Dim.pt 20) + scaled body (-font.descent)
  let tight : Layout.Geom := { geom with pageH := natural - Dim.pt 10 + geom.vmargin }
  t "within its shrink the page holds" (pagesOf tight three == 1)
  let ys := ysOf tight three
  t "the shrunk page moves later lines up, in proportion"
    (ys.size == 3 && ys[0]! == firstY && ys[2]! < firstY + 2 * (leading + pq + Dim.pt 20) &&
      ys[1]! - ys[0]! == leading + pq + Dim.pt 20 - Dim.pt 5 &&
      ys[2]! - ys[1]! == leading + pq + Dim.pt 20 - Dim.pt 5)
  t "a shrunk page says so"
    ((layoutOf oneFace (Elab.run "t" three).1 tight).diags.any (·.code == "N0200"))
  let tooTight : Layout.Geom := { geom with pageH := natural - Dim.pt 20 + geom.vmargin }
  t "beyond its shrink the page breaks" (pagesOf tooTight three == 2)
  t "an unshrunk page says nothing"
    (!(layoutOf oneFace (Elab.run "t" three).1 geom).diags.any (·.code == "N0200"))
  -- The three horizontal origins a declared alignment names, judged over
  -- `Layout.Out`: left, centred, and — the one line placement had no
  -- arithmetic for — flush right. Read two-way, `align = right` fell into the
  -- centred arm, so the PDF centred a heading the HTML backend right-aligned
  -- from the same declaration. The ordering is the content-free half:
  -- whatever the heading's width, its origin moves strictly right as the
  -- declaration does.
  let alignSrc (al : String) := "\\documentclass{article}" ++
    (if al.isEmpty then "" else "\\style{abstract}{ align = " ++ al ++ " }") ++
    "\\begin{document}\\begin{abstract}Placeholder abstract body.\\end{abstract}" ++
    "Body text.\\end{document}"
  let alignX (al : String) : Option Dim.Sp :=
    let (d, _) := elabStr (alignSrc al)
    lineXOf (censusOf (coveredColorsOf d) (layoutOf oneFace d geom)) 0 "Abstract"
  match alignX "left", alignX "", alignX "right" with
  | some l, some c, some rgt =>
    t "a declared alignment moves the heading's origin: left, centre, right"
      (decide (l < c) && decide (c < rgt))
    t "an undeclared abstract heading keeps the class's centred origin"
      (decide (l < c))
  | _, _, _ => t "the alignment probe produced its heading" false

/-- Title bars stand their declared gap from the type's body: the cap line
above the text, the baseline below it (`Layout.interlineFor`,
`Layout.title_bars_symmetric`) — asserted over `Layout.Out`, never an IR
dump. The fixture is the paper's shape: a LARGE title over two lines,
every word descender-free, a heavier bar above than below, equal declared
gaps. Both facts fail under the strut-and-metric placement this
convention replaced: a rule-only line carried the body strut, and the
gaps ran to the leaded box. The descender probe is the content-free
half: furniture that moved with the letters would make the artifact
content-dependent. -/
def titleBarChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font.Font) : IO Unit := do
  let t := check ref
  let src (last : String) := "\\documentclass{article}" ++
    "\\style{titlepage}{ rule-above = 4pt, rule-above-gap = 18pt, " ++
    "rule-below = 1pt, rule-below-gap = 18pt }" ++
    "\\title{Invented Title Bars Stand All Their Rules " ++ last ++ "}" ++
    "\\author{Placeholder Name}" ++
    "\\begin{document}\\maketitle Body text.\\end{document}"
  -- A measure narrow enough that the LARGE title breaks over two lines.
  let tg : Layout.Geom := { geom with pageW := Dim.inch 3 + 2 * geom.hmargin }
  let titleSize := geom.fontSize * ((Ir.sizeScale.lookup "LARGE").getD 1000) / 1000
  let cap : Dim.Sp := (font.capHeight : Int) * titleSize / font.unitsPerEm
  let probe (last : String) : Option (Dim.Sp × Dim.Sp × Nat) := do
    let lines := bodyLines (layoutOf oneFace (Elab.run "t" (src last)).1 tg)
    let bars := lines.filter (fun l => Layout.ruleOnly l.segs)
    let titles := lines.filter (fun l => !Layout.ruleOnly l.segs && l.size == titleSize)
    let bar1 ← bars[0]?
    let bar2 ← bars[1]?
    let firstT ← titles[0]?
    let lastT ← titles.back?
    let th2 ← bar2.segs.findSome? fun s => match s with
      | .rule _ th _ _ => some th | _ => none
    return ((firstT.y - cap) - bar1.y, (bar2.y - th2) - lastT.y, titles.size)
  match probe "Even", probe "Gyp" with
  | some (above, below, n), some (_, below', n') =>
    t "title bars: the title broke over two lines" (n == 2 && n' == 2)
    t "title bars: the rule stands its declared gap above the cap line"
      (above == Dim.pt 18)
    t "title bars: equal declared gaps are equal visible gaps"
      (below == Dim.pt 18 && above == below)
    t "title bars: a descender on the last line never moves the bottom bar"
      (below' == below)
  | _, _ => t "title bars: the probe produced its lines" false
  -- Undeclared, the gaps are the engine's rhythm tokens: three quanta on
  -- both sides (`Ir.titleBarGap`, `title_bar_rhythm`) — the default is
  -- symmetric; declared asymmetry is the author's.
  let dsrc := "\\documentclass{article}" ++
    "\\style{titlepage}{ rule-above = 4pt, rule-below = 1pt }" ++
    "\\title{Invented Title Bars Stand All Their Rules Even}" ++
    "\\author{Placeholder Name}" ++
    "\\begin{document}\\maketitle Body text.\\end{document}"
  let dlines := bodyLines (layoutOf oneFace (Elab.run "t" dsrc).1 tg)
  let dbars := dlines.filter (fun l => Layout.ruleOnly l.segs)
  let dtitles := dlines.filter (fun l => !Layout.ruleOnly l.segs && l.size == titleSize)
  let q := Ir.rhythmQuantum geom.fontSize
  t "title bars: the undeclared gap is three rhythm quanta, both sides"
    ((do
      let bar1 ← dbars[0]?
      let bar2 ← dbars[1]?
      let firstT ← dtitles[0]?
      let lastT ← dtitles.back?
      return (firstT.y - cap) - bar1.y == 3 * q &&
        (bar2.y - Dim.pt 1) - lastT.y == 3 * q : Option Bool).getD false)

/-- Recovery emits the author's content, never the source's syntax. An
unknown command's leading `[...]` run is how the author addressed the
command — a parameter, not content — so no character of it reaches the
shipped page, while every `{...}` group survives, and no space the author
never wrote is fabricated after the kept text. Judged over `Layout.Out`'s
glyphs, never the IR dump: a bracketed number once shipped in front of a
URL while the suite was green. `elabInlines` terminates provably now, so
the elaborator half is stated at last — `elab_inlines_option_run_dropped`,
staged under Obligations with its proof open on the elaboration budget;
until that proof lands, this stays its shipped-page witness. -/
def recoveryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let pageText (src : String) : String := pageTextOf oneFace src (some geom)
  let has := hasStr
  -- The user's own case: a bracketed number in front of a URL, and one in
  -- front of an email address.
  let url := pageText "\\textls[16]{placeholder}.example.org"
  t "an unknown command's option run ships no character"
    (!has url "[" && !has url "]" && !has url "16")
  t "the kept group stays fused to what follows it"
    (has url "placeholder.example.org")
  let mail := pageText "\\textls[16]{someone}@example.org"
  t "an option run before an email address ships nothing"
    (!has mail "[" && has mail "someone@example.org")
  t "the drop is visible, named by its own code"
    ((warnCodes "\\textls[16]{placeholder}.example.org").contains "W0341")
  -- Consecutive runs are one parameter train; both groups are content. The
  -- example is a name the engine does not know: `\parbox` stood here once
  -- and is a kernel box now, whose first group is a width rather than
  -- content (`boxArgChecks`).
  let par := pageText "\\zzz[c][2cm]{alpha}{beta}"
  t "consecutive option runs all go with the command"
    (!has par "[" && !has par "2cm" && has par "alpha beta")
  -- An unclosed run is malformed content, not an option: kept and named.
  let open_ := pageText "\\foo[16 oops"
  t "an unclosed bracket run stays on the page"
    (has open_ "[16 oops" &&
     (warnCodes "\\foo[16 oops").contains "W0310" &&
     !(warnCodes "\\foo[16 oops").contains "W0341")
  -- A bracket on a later line is content, where LaTeX stops looking too.
  let later := pageText "\\foo\n[note] stays"
  t "a bracket run on the next line is content"
    (has later "[note] stays" && !(warnCodes "\\foo\n[note] stays").contains "W0341")
  -- No fabricated space: the give-back happens only when one was written.
  t "no space is fabricated after a kept group"
    (pageText "\\foo{a}.b" == "a.b")
  t "a written space after a kept group survives"
    (pageText "\\foo{a} b" == "a b")
  -- The starred form's `*` still belongs to the command, options after it.
  t "a starred unknown command drops its options too"
    (let s := pageText "\\foo*[1]{x}"; s == "x")
  -- The math recovery floor: a formula the engine cannot model degrades to
  -- its text content, never to its markup. Setting a formula's source as
  -- body ink is the worst recovery there is — a reader sees control
  -- sequences where an equation belongs — so the floor drops the markup and
  -- keeps what was content (`Ir.floorInk_mem`). The construct is still
  -- named by W0012; the loss is announced, not shown.
  let deg := pageText "$\\overset{?}{=}$"
  t "a degraded formula ships no control sequence"
    (!has deg "\\" && !has deg "{" && !has deg "}" && !has deg "overset")
  t "a degraded formula keeps its text content"
    (has deg "?" && has deg "=")
  -- The lower bound the theorem does not reach: content survives the mask,
  -- and exactly the markup goes. `floorInk_mem` is an upper bound — it
  -- holds for a mask that dropped everything — so these are the executable
  -- half, pinned as whole strings rather than as absences.
  t "a plain content run passes through the floor unchanged"
    (pageText "$\\overset{abc + 12}{d}$" == "abc + 12d")
  t "exactly the command and its braces go"
    (pageText "$\\overset{a}{b}$" == "ab")
  t "a naming command's argument goes, the next one stays"
    (pageText "$\\overset{\\textcolor{indigo}{q}}{r}$" == "qr")
  t "both lengths of a two-name command go"
    (pageText "$\\overset{\\rule{1pt}{2pt}x}{y}$" == "xy")
  t "a naming command's option run goes with its name"
    (pageText "$\\overset{\\textcolor[rgb]{1,0,0}{s}}{t}$" == "st")
  t "a second naming command does not eat the content group"
    (pageText "$\\overset{\\color{red}\\textcolor{blue}{u}}{v}$" == "uv")
  -- The three shapes a positional scan loses if it is too strict, each of
  -- which shipped a length or a bracket as ink: a width-taking wrapper, a
  -- starred command whose star is part of its name, and an option run the
  -- scan stepped over without marking.
  t "a width-taking wrapper drops its width, keeps its body"
    (pageText "$\\overset{\\parbox{5cm}{text}}{y}$" == "texty")
  t "a starred command's star goes with its name"
    (pageText "$\\overset{\\hspace*{1pt}k}{y}$" == "ky")
  t "an option run goes even where no group follows it"
    (pageText "$\\overset{\\textcolor[rgb]x}{y}$" == "xy")
  t "an option run trailing a named argument goes too"
    (pageText "$\\overset{\\raisebox{-1pt}[2pt]{keep}}{y}$" == "keepy")
  t "the row separator's own option run goes with it"
    (pageText "$\\overset{x\\\\[2ex]y}{z}$" == "xyz")
  -- The space a dropped command's name leaves behind goes with the name:
  -- `\phantom {hidden}` is written with one, and keeping it indented the
  -- floor.
  t "no space survives a dropped command"
    (pageText "$\\overset{k\\phantom{hidden}}{y}$" == "ky")
  -- A formula that is markup and symbol commands end to end salvages
  -- nothing, and a blank page is not an honest floor either: the declared
  -- placeholder ships instead (`Ir.floorInk_accounts`).
  t "a formula with no content characters ships the declared placeholder"
    (pageText "$\\overset{\\alpha}{\\beta}$" == "[…]")
  -- A colour name is the markup of `\textcolor`, not content: it may not
  -- appear on the page even though it stands inside a brace group.
  let col := pageText "$\\overset{\\textcolor{indigo}{q}}{=}$"
  t "a degraded formula ships no colour name"
    (!has col "indigo" && !has col "textcolor" && has col "q")
  -- The alignment tab and the script marks are markup too.
  let tab := pageText "\\begin{align*} \\overset{a}{b} &= c_d \\end{align*}"
  t "a degraded alignment ships no tab or script mark"
    (!has tab "&" && !has tab "_" && !has tab "\\" && has tab "c")
  -- Without a math face a formula the engine *can* model still sets as
  -- text (W0003) — the same policy applies, so that path cannot leak
  -- markup either; there the floor is the parsed glyph text.
  t "the no-math-face floor ships no control sequence"
    (let s := pageText "$\\alpha^2$"
     !has s "\\" && !has s "alpha" && has s "2")

/-- The recovery floor read as what it is: a function of the declared `Loss`.
`Ir.FloorHonest` is the judge every floor is checked against and
`Ir.floorInk_covers` discharges it for the filtered salvage over every
registered code; these are the page-level rows behind it, plus the two
boundaries a reader of the theorem would otherwise have to guess at.

Read off `Layout.Out`, never an IR dump: the claim is about what a page
shows, and the fixture that pinned the original defect as intended behaviour
is why. -/
def floorPolicyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pageText (src : String) : String := pageTextOf oneFace src (some ({} : Layout.Geom))
  let has := hasStr
  -- The registry side, as the page sees it: the codes that owe ink are
  -- exactly the degraded ones, and the floor a code demands is its loss's.
  t "exactly the degraded codes owe the reader ink"
    (DiagCode.all.all fun c => c.floor.inks == (c.loss == .degraded))
  t "a floor that owes ink is a floor that ships"
    (DiagCode.all.all fun c => !c.floor.inks || c.floor.ships)
  t "the codes with no content operand owe no ink and ship none"
    (DiagCode.all.all fun c =>
      (c.loss != .config && c.loss != .info) || (!c.floor.ships && !c.floor.inks))
  -- The paid-for clause where it bites, over four shapes whose content
  -- characters are none: the page says something stood here.
  t "every all-markup formula ships the declared placeholder"
    ([ "$\\overset{\\alpha}{\\beta}$", "$\\overset{\\gamma}{\\delta}$",
       "$\\overset{\\phantom{x}}{\\alpha}$", "$\\overset{\\label{k}}{\\beta}$" ].all
      fun src => pageText src == "[…]")
  -- The drawn-and-markup-free clause over the same shapes plus content
  -- ones: no page ships LaTeX's punctuation where a formula stood.
  t "no degraded formula ships LaTeX punctuation"
    ([ "$\\overset{a+b}{c}$", "$\\overset{\\textcolor{teal}{p}}{q}$",
       "$\\overset{\\alpha}{\\beta}$", "$\\overset{x_1}{y^2}$" ].all
      fun src =>
        let s := pageText src
        !has s "\\" && !has s "{" && !has s "}" && !has s "$" &&
        !has s "&" && !has s "^" && !has s "_" && !has s "~")
  -- The first boundary: "carried content" is one question with one answer,
  -- and the floor's own mask answers it. A source that is markup end to end
  -- carried nothing; one with a letter in it carried something.
  t "a markup-only source carried no content"
    (!Ir.floorCarries "\\overset{\\alpha}{\\beta}" &&
     !Ir.floorCarries "\\," && !Ir.floorCarries "{}")
  t "a source with a content character carried content"
    (Ir.floorCarries "\\overset{abc}{d}" && Ir.floorCarries "x")
  -- The second boundary, and the one a reader of `floorInk_covers` would
  -- otherwise mistake for a defect: a space-only formula parses, so its
  -- floor is the parse's scalars — none — and the page ships nothing. That
  -- is honest, because the source carried no content character either; a
  -- placeholder here would invent ink where an author wrote a thin space.
  t "a space-only formula inks nothing, and carried nothing to ink"
    (pageText "$\\,$" == "" && !Ir.floorCarries "\\,")
  t "a formula with one digit inks it without a math face"
    (pageText "$\\,2$" == "2")
  -- A parsed atom's scalars are content by the parser's decision, so the
  -- character test does not run over them: the floor that is right must not
  -- be condemned by the judge that governs the other one.
  t "the parsed floor ships the brace glyph its author spelled"
    (let s := pageText "$\\{x\\}$"; has s "{" && has s "}" && !has s "\\")
  -- An option run immediately after a control word is that command's, as
  -- LaTeX reads it, and it is markup whether or not the engine knows the
  -- command. Only `Ir.floorNamedArgs` commands swept one, so `\sqrt[3]{8}`
  -- shipped `[3]` and an unknown command shipped its whole option list —
  -- the drop the engine already makes in text (W0341) and in a node body,
  -- missing at the first of the three floors to be written.
  t "a known command's index option never reaches the page"
    (pageText "$\\overset{a}{b}\\sqrt[3]{8}$" == "ab8")
  t "an unknown command's option run never reaches the page"
    (pageText "$\\overset{a}{b}\\zzz[opt]{x}$" == "abx")
  t "an option run after a command with no group goes too"
    (pageText "$\\overset{\\alpha[1]z}{y}$" == "zy")
  -- And a bracket that follows no command is content: an interval is not an
  -- option list, which is why this sweep is keyed on the control word and
  -- not on the character.
  t "a bracket run following no command stays on the page"
    (pageText "$\\overset{[0,1]}{y}$" == "[0,1]y")
  t "a bracket run opening a formula stays on the page"
    (pageText "$\\overset{a}{b}[2,3]$" == "ab[2,3]")

/-- Vertical distribution: beamer's frame options select the split, the
default centres (beamer user guide §8.1), and a titled frame's page-top
chrome never moves with the body. -/
def vdistChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let linesOf (src : String) : Array Layout.LineOut :=
    allLines (layoutOf oneFace (elabStr src).1 geom)
  let firstY (body : String) : Dim.Sp :=
    ((linesOf (deck169Body body))[0]?.map (·.y)).getD 0
  let yT := firstY "\\begin{frame}[t]\nhello\n\\end{frame}"
  let yC := firstY "\\begin{frame}\nhello\n\\end{frame}"
  let yB := firstY "\\begin{frame}[b]\nhello\n\\end{frame}"
  t "a frame centres by default, [t] sits above it" (yT < yC)
  t "[b] sits below the centre" (yC < yB)
  -- 1:1 is the halving and 1:0 the whole leftover: centre is halfway
  -- between top and bottom, up to the division's rounding.
  t "centre is halfway between [t] and [b]"
    (yB - yC == yC - yT || yB - yC == yC - yT + 1)
  -- Ratio 0:1 reproduces the undistributed placement exactly
  -- (VDist.top_is_flush at page level): a [t] frame's first line sits
  -- where an article's does.
  t "[t] is the old top-flush placement"
    (yT == firstY "hello")
  -- Two paragraphs in a frame stay two through frame elaboration and the
  -- distribution: the frame's text baselines are the article's peer pair
  -- (`spacingChecks`), whether or not a comment line precedes the blank
  -- line that separates them.
  let textYs (body : String) : Array Dim.Sp :=
    (linesOf (deck169Body body)).filterMap fun l =>
      if !l.furniture && l.segs.any (fun s => match s with | .run .. => true | _ => false)
      then some l.y else none
  let framePlain := textYs "\\begin{frame}[t]\nFirst label --- one\n\nSecond label --- two\n\\end{frame}"
  let frameCommented := textYs
    "\\begin{frame}[t]\n  First label --- one\n  % an aside\n\n  Second label --- two\n\\end{frame}"
  let peerGap := Ir.leadingFor geom.fontSize geom.leading +
    (geom.parskip.resolve geom.fontSize 0).width
  t "a frame's two paragraphs sit the peer gap apart"
    (framePlain.size == 2 && framePlain[1]! - framePlain[0]! == peerGap)
  t "a comment line before the blank line keeps a frame's two paragraphs"
    (frameCommented == framePlain)
  t "[t] parses to top"
    ((elabStr (deck169Body "\\begin{frame}[t]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] false .top false #[.para #[.text "x"]]])
  t "[b] parses to bottom"
    ((elabStr (deck169Body "\\begin{frame}[b]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] false .bottom false #[.para #[.text "x"]]])
  t "[t,standout] keeps both"
    ((elabStr (deck169Body "\\begin{frame}[t,standout]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] true .top false #[.para #[.text "x"]]])
  -- A titled frame's title is page-top chrome: distributing the body must
  -- not move the title line, and the title bar keeps its height.
  let titled (opt : String) : String :=
    deck169Body ("\\begin{frame}" ++ opt ++ "{Head}\nbody text\n\\end{frame}")
  let tLines := linesOf (titled "[t]")
  let cLines := linesOf (titled "")
  t "a titled frame has title and body lines" (tLines.size ≥ 2 && cLines.size ≥ 2)
  t "the title never moves with the distribution"
    (((tLines[0]?).map (·.y)) == ((cLines[0]?).map (·.y)))
  t "the body distributes below the title"
    ((((tLines[1]?).map (·.y)).getD 0) < (((cLines[1]?).map (·.y)).getD 0))
  -- With a frametitlebg palette the title is a colour bar; centring the
  -- body must not stretch it.
  let barH (opt : String) : Dim.Sp :=
    let src := "\\documentclass[aspectratio=169]{slides}\n" ++
      "\\palette{frametitlebg = #23373B}\n\\begin{document}\n" ++
      "\\begin{frame}" ++ opt ++ "{Head}\nbody text\n\\end{frame}\n\\end{document}"
    (((layoutOf oneFace (elabStr src).1 geom).pages.flatMap
      (·.fills))[0]?.map (·.h)).getD 0
  t "the title bar keeps its height under centring" (barH "" == barH "[t]")
  -- The title frame: golden distribution, and the titlepage style decides
  -- the horizontal alignment and the separator.
  let titled := deck169Body "\\title{A Deck}\\author{Pat Placeholder}\n\\maketitle"
  t "the title frame declares the golden split"
    (match (elabStr titled).1.body with
     | #[.frame _ _ .golden _ _] => true
     | _ => false)
  t "an undeclared title page centres"
    (match (elabStr titled).1.body with
     | #[.frame _ _ _ _ #[.center _]] => true
     | _ => false)
  let styledSrc := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{sep = #445566}\n" ++
    "\\style{titlepage}{align = left, separator = sep}\n" ++
    "\\begin{document}\n\\title{A Deck}\\author{Pat Placeholder}\n\\maketitle\n" ++
    "\\end{document}"
  t "a left title page is ragged and carries the separator"
    (match (elabStr styledSrc).1.body with
     | #[.frame _ _ .golden _ inner] =>
       -- The separator stands inside its declared-gap wrapper
       -- (`separatorgap` above it, the rule convention's gap).
       inner.size ≥ 2 && inner.any (fun b => match b with
         | .rule _ (some "sep") _ => true
         | .spaced _ #[.rule _ (some "sep") _] => true
         | _ => false) && !inner.any (fun b => match b with
         | .center _ => true
         | _ => false)
     | _ => false)
  -- The separator lays out as a full-measure rule line.
  t "the separator sets as a full-measure rule"
    ((linesOf styledSrc).any fun l => l.segs.any fun sg =>
      match sg with
      | .rule w _ _ _ => w == geom.textWidth
      | _ => false)
  -- The deck's title takes the bundle's declared title font, one scale
  -- step over the body (`Large`), not the flow class's `\@maketitle`
  -- fallback two steps up (`LARGE`): the fallback is sourced for an
  -- article page, and a deck that inherits it sets its title 20% large,
  -- which re-flows a declared title line. Judged over `Layout.Out`'s
  -- shipped line sizes, never an IR dump.
  let deckTitleSrc := "\\documentclass[aspectratio=169]{slides}\n\\theme{moloch}\n" ++
    "\\begin{document}\n\\title{Alpha Beta}\\author{Pat Placeholder}\n" ++
    "\\maketitle\n\\end{document}"
  let deckTitleSize := Ir.scaleStep geom.fontSize "Large"
  t "a deck title sets at the bundle's declared step, not the flow fallback"
    ((linesOf deckTitleSrc).any (·.size == deckTitleSize) &&
      !(linesOf deckTitleSrc).any (·.size == Ir.scaleStep geom.fontSize "LARGE"))
  -- The title page's split composes the enclosing frame's own centring
  -- with the template's glue: the frame contributes one fil unit on each
  -- side and the template 1.618 more above (`Ir.VAlign.shares`). The
  -- share is scale-free, so it is read the way the oracle reads beamer's
  -- — from the rate at which the block moves as its own height grows,
  -- which cancels the first line's height and the last line's depth.
  let titleBlock (extra : String) : Option (Dim.Sp × Dim.Sp) := do
    let ls := (linesOf ("\\documentclass[aspectratio=169]{slides}\n\\theme{moloch}\n" ++
      "\\begin{document}\n\\title{Alpha" ++ extra ++ "}\\author{Pat Placeholder}\n" ++
      "\\maketitle\n\\end{document}")).filter (!·.furniture)
    let first ← ls[0]?
    let last ← ls.back?
    return (first.y, last.y - first.y)
  match titleBlock "", titleBlock "\\\\ Beta\\\\ Gamma\\\\ Delta" with
  | some (y1, span1), some (y2, span2) =>
    let (above, below) := Ir.VAlign.golden.shares
    -- Taller block, smaller leftover, so the block's top rises by the
    -- above share of the growth.
    let predicted := y1 - (span2 - span1) * above / (above + below)
    t "the title page's block grew" (span1 < span2)
    t "the title page splits its leftover by the composed golden share"
      ((y2 - predicted).natAbs ≤ 2)
  | _, _ => t "the title page's split probe produced its blocks" false
  -- A title whose breaks the author declared keeps them: the second
  -- declared line stays one line and keeps its declared indent, rather
  -- than re-flowing and returning the remainder to the flush-left margin
  -- — the pattern a reader sees as a broken indent. The measure here
  -- holds the declared line at the deck's own title step.
  let brokenSrc := "\\documentclass[aspectratio=169]{slides}\n\\theme{moloch}\n" ++
    "\\begin{document}\n\\title{Alpha beta gamma\\\\ \\quad delta epsilon zeta}" ++
    "\\author{Pat Placeholder}\n\\maketitle\n\\end{document}"
  let titleLines := (linesOf brokenSrc).filter fun l =>
    !l.furniture && l.size == deckTitleSize
  t "a declared two-line title stays two lines"
    (titleLines.size == 2)
  -- The declared indent survives the declared break: `\quad` sets as a
  -- one-em run at the title's own size, and a run is not glue, so the
  -- break does not discard it the way TeX discards leading glue.
  let firstRunWidth (l : Layout.LineOut) : Option Dim.Sp :=
    l.segs.findSome? fun sg => match sg with
      | .run _ _ _ w _ _ _ _ _ _ => some w
      | _ => none
  t "the declared second line keeps its indent"
    ((do
      let a ← titleLines[0]?
      let b ← titleLines[1]?
      let wa ← firstRunWidth a
      let wb ← firstRunWidth b
      -- One em at the title's size leads the second line, and the first
      -- line opens on type instead.
      return wb == deckTitleSize && wa != deckTitleSize : Option Bool).getD false)
  -- A deck's paragraphs advance by the body leading alone: beamer sets
  -- `\parskip` to zero (beamerbasemisc.sty), so a frame spends nothing
  -- between paragraphs, where a flow page spends the engine's rhythm
  -- quantum. Read under each document's *own* page geometry, since the
  -- value is the class's default. The gap accumulates: on a frame of
  -- several paragraphs a quantum apiece is what pushes content that fits
  -- beamer's stage past this engine's, and a spilt frame costs a
  -- continuation page (W0384).
  let ownGeomYs (src : String) : Array Dim.Sp :=
    let (doc, _) := elabStr src
    (bodyLines (layoutOf oneFace doc (Layout.Geom.ofPage doc.page))).filterMap fun l =>
      if l.segs.any (fun s => match s with | .run .. => true | _ => false)
      then some l.y else none
  let deckYs := ownGeomYs (deck169Body
    "\\begin{frame}[t]\nAlpha beta gamma.\n\nDelta epsilon zeta.\n\\end{frame}")
  let flowYs := ownGeomYs
    "\\documentclass{article}\\begin{document}\nAlpha beta gamma.\n\nDelta epsilon zeta.\n\\end{document}"
  let deckFontSize := (elabStr (deck169Body "\\begin{frame}\nx\n\\end{frame}")).1.page.fontSize
  t "a deck's paragraphs advance by the body leading, spending no parskip"
    (deckYs.size == 2 &&
      deckYs[1]! - deckYs[0]! == Ir.leadingFor deckFontSize)
  t "a flow page still spends its rhythm quantum between paragraphs"
    (flowYs.size == 2 &&
      flowYs[1]! - flowYs[0]! ==
        Ir.leadingFor Ir.baseFontSize + Ir.rhythmQuantum Ir.baseFontSize)

/-- The running head's reserved band (`furnitureBand`/`Geom.bodyTop`): with a
top margin too small to hold the head line, body ink still starts at least
`inkClearance` below the head's ink bottom — `bodyTop_clears_head` is the
sufficiency proof; this is its witness over the shipped lines, the
invariant whose absence let the head collide with the first body line. The
mirrored default is also pinned: at the default margins the band is zero,
so an undeclared page is unchanged. -/
def headBandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let tight := "\\documentclass{article}\\page{ vmargin = 14pt }" ++
    "\\runninghead{Invented Notes \\hfill p. \\pagenumber}" ++
    "\\begin{document}Body text under a tight margin.\\end{document}"
  let (doc, _) := elabStr tight
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  let lines := (out.pages[0]?.map (·.lines)).getD #[]
  let font := oneFace.body
  let scale (u : Int) : Dim.Sp := u * geom.fontSize / (font.unitsPerEm : Int)
  let headY := geom.vmargin / 2 + scale font.ascent
  t "the tight-margin page ships its head line" (lines.any fun l => l.y == headY)
  let headBottom := headY + scale (-font.descent)
  let bodyInkTops := lines.filterMap fun l =>
    if l.y == headY then none else some (l.y - scale font.capHeight)
  t "body ink clears the head's ink by the clearance floor under a tight margin"
    (!bodyInkTops.isEmpty &&
      bodyInkTops.all fun top => headBottom + Layout.inkClearance ≤ top)
  -- The default margin holds the head whole: the band is zero and the
  -- first body line sits exactly where a headless page puts it.
  let dflt (head : Bool) : Option Dim.Sp := Id.run do
    let src := "\\documentclass{article}" ++
      (if head then "\\runninghead{Invented Notes}" else "") ++
      "\\begin{document}Body text at the default margin.\\end{document}"
    let (doc, _) := elabStr src
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom
    let lines := (out.pages[0]?.map (·.lines)).getD #[]
    return (lines.filter fun l => l.y ≠ geom.vmargin / 2 + scale font.ascent)
      |>.foldl (fun acc l => match acc with
        | none => some l.y
        | some y => some (min y l.y)) none
  t "the default margin reserves no band: the body does not move"
    (dflt true == dflt false && (dflt false).isSome)
  -- `slides_lines_survive_bands` allows each running line two em of ink;
  -- the shipped test faces sit inside that bound, so the theorem's
  -- hypothesis is real, not aspirational.
  for name in ["OpenSans-Regular.ttf", "SourceSerifPro-Regular.otf",
               "SourceCodePro-Regular.otf"] do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f =>
      t s!"{name} line ink stays under two em"
        (f.ascent + (-f.descent) ≤ 2 * (f.unitsPerEm : Int))
    | .error e => failures ref s!"headBand font parse {name}: {e}"

/-- `furniture_symmetric` realised over `Layout.Out`, together with the
position half no theorem states — these checks are that half, an oracle:
with a running head and foot declared, every page ships
its furniture at the geometry's own baselines — the short last page
included, so the foot never floats up toward a page's last line. The
positions are a function of the geometry alone (`furnHeadY`/`furnFootY`
take no content), and this is the executable witness that `Layout.run`
places the shipped lines at exactly those functions' values; the gap
equalities over those functions are `furniture_symmetric`'s statement and
are not re-derived here. -/
def furnitureSymmetryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let para := String.intercalate " " (List.replicate 300 "filler words run on")
  let src := "\\documentclass{article}" ++
    "\\runninghead{Invented Notes}\\runningfoot{p. \\pagenumber}" ++
    s!"\\begin\{document}\n{para}\n\n{para}\n\nshort tail\n\\end\{document}"
  let (doc, ds) := elabStr src
  t "symmetry source clean" (ds.filter (·.severity == .error)).isEmpty
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  t "the fixture runs past one page" (out.pages.size ≥ 2)
  let font := oneFace.body
  let scale (u : Int) : Dim.Sp := u * geom.fontSize / (font.unitsPerEm : Int)
  let a := scale font.ascent
  let d := scale (-font.descent)
  let band := Layout.furnitureBand geom.vmargin (a + d) none
  let (headY, footY) := furnYs font geom
  t "every page ships its head and foot at the geometry's own baselines"
    (out.pages.all fun p =>
      p.lines.any (fun l => l.furniture && l.y == headY) &&
      p.lines.any (fun l => l.furniture && l.y == footY))
  let bodyBottom := geom.pageH - geom.vmargin - band.band
  -- Full-page evidence: the first page's body demonstrably reaches the
  -- reserved bottom, so the equal gap below is a distance to real ink.
  t "the first page fills its body area"
    ((out.pages[0]?.map fun p => p.lines.any fun l =>
      !l.furniture && l.y + d + Ir.leadingFor geom.fontSize > bodyBottom).getD false)
  -- Content-free evidence: the last page is short, and its furniture
  -- stands exactly where the full pages' does.
  t "the short last page keeps its foot in place"
    ((out.pages.back?.map fun p =>
      p.lines.any (fun l => l.furniture && l.y == footY) &&
      p.lines.all (fun l => l.furniture || l.y + d + Ir.leadingFor geom.fontSize ≤ bodyBottom))
      |>.getD false)
  -- Declared gaps: the LaTeX spellings read through the one correction
  -- (`furnGapOfSep`), so equal declared values mean equal gaps — without
  -- the strut patch (`geometry_roundtrip` holds the reading invertible).
  let declPre (page : String) : String := "\\documentclass{article}" ++ page ++
    "\\runninghead{Invented Notes}\\runningfoot{p. \\pagenumber}" ++
    s!"\\begin\{document}\n{para}\n\\end\{document}"
  let dsrc := declPre "\\page{ headsep = 20pt, footskip = 20pt }"
  let (dDoc, dDs) := elabStr dsrc
  t "declared-gap source clean" (dDs.filter (·.severity == .error)).isEmpty
  let dGeom := Layout.Geom.ofPage dDoc.page
  let dOut := layoutOf oneFace dDoc dGeom
  let dGap := Layout.furnGapOfSep (Dim.pt 20) d
  let dBand := Layout.furnitureBand dGeom.vmargin (a + d) (some dGap)
  let (dHeadY, dFootY) := furnYs font dGeom (some dGap)
  t "equal declared seps place head and foot from one band"
    (dOut.pages.all fun p =>
      p.lines.any (fun l => l.furniture && l.y == dHeadY) &&
      p.lines.any (fun l => l.furniture && l.y == dFootY))
  t "the declared gap is honoured exactly on the page"
    ((dGeom.vmargin + dBand.band) - (dHeadY + d) == dGap &&
     (dFootY - a) - (dGeom.pageH - dGeom.vmargin - dBand.band) == dGap)
  t "equal declared seps carry no note" (!dOut.diags.any (·.code == "N0021"))
  let (nDoc, _) := elabStr (declPre "\\page{ headsep = 20pt, footskip = 30pt }")
  let nOut := layoutOf oneFace nDoc
  t "differing declared seps are named as declared, once"
    ((nOut.diags.filter (·.code == "N0021")).size == 1 &&
      nOut.diags.all fun dg => dg.code != "N0021" || dg.severity == .note)
  -- The native spelling: one ink-terms knob, both sides at once.
  let (fDoc, _) := elabStr (declPre "\\page{ furnituregap = 12pt }")
  let fGeom := Layout.Geom.ofPage fDoc.page
  let fOut := layoutOf oneFace fDoc fGeom
  let (fHeadY, fFootY) := furnYs font fGeom (some (Dim.pt 12))
  t "the native furnituregap places both sides"
    (fOut.pages.all fun p =>
      p.lines.any (fun l => l.furniture && l.y == fHeadY) &&
      p.lines.any (fun l => l.furniture && l.y == fFootY))
  t "the native gap carries no note" (!fOut.diags.any (·.code == "N0021"))

/-- The plain page-number census over `Layout.Out` — these facts are the
claim, an oracle and not a theorem (the theorem form needs the collect
walk's induction, the wall `pages_partition_frames` records): under the
flow model's default page style — `plain`, the one article.cls
initialises (classes.dtx; ltpage.dtx `\ps@plain` centres `\thepage` in the
foot) — every page carries exactly one number glyph run in the footer
band, equal to its index; a page before `footFrom` (the title page under
`\thispagestyle{empty}`) carries none; `numbers = off` and the `resume`
record carry none anywhere; a declared `\runningfoot` owns the band and
the default never doubles it. -/
def pageNumberChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let build (src : String) : Layout.Out × Layout.Geom :=
    let (doc, _) := elabStr src
    let geom := Layout.Geom.ofPage doc.page
    (layoutOf oneFace doc geom, geom)
  -- The footer band's runs on page i: furniture lines at the foot
  -- baseline (`furnFootY` — the foot's ink bottom stands `edge` above the
  -- page edge), each read back as its glyph text.
  let font := oneFace.body
  let footTexts (out : Layout.Out) (geom : Layout.Geom) (i : Nat) : Array String :=
    ((out.pages[i]?.map (·.lines)).getD #[]).filterMap fun l =>
      if l.furniture && l.y == (furnYs font geom).2 then
        some (lineText l (gapAsSpace := false))
      else none
  let threeBody := "One.\\pagebreak Two.\\pagebreak Three."
  let (out, geom) := build (dvDoc "" threeBody)
  t "plain numbers every page: three pages ship" (out.pages.size == 3)
  for i in [0:3] do
    t s!"plain numbers every page: page {i + 1} ships exactly its own number"
      (footTexts out geom i == #[toString (i + 1)])
  -- Centred: the number's run starts left of centre and ends right of it
  -- (the fil pair splits the slack, as pad_center does).
  t "plain numbers every page: the number is centred on the measure"
    (((out.pages[0]?.map (·.lines)).getD #[]).any fun l =>
      l.furniture && l.segs.any fun s =>
        match s with
        | .gap w _ => w > (geom.textWidth - Dim.pt 20) / 2
        | _ => false)
  let (offOut, offGeom) := build (dvDoc "\\page{ numbers = off }" threeBody)
  t "numbers = off ships no number on any page"
    ((List.range 3).all fun i => footTexts offOut offGeom i == #[])
  let (resumeOut, resumeGeom) := build
    ("\\documentclass{resume}\\begin{document}Alex Placeholder\\end{document}")
  t "a resume page carries no default number"
    (footTexts resumeOut resumeGeom 0 == #[])
  let (onOut, onGeom) := build
    ("\\documentclass{resume}\\page{ numbers = on }\\begin{document}x\\end{document}")
  t "numbers = on takes control of the resume's default"
    (footTexts onOut onGeom 0 == #["1"])
  let (declOut, declGeom) := build (dvDoc "\\runningfoot{note \\pagenumber}" threeBody)
  t "a declared runningfoot owns the band: no doubled default"
    (footTexts declOut declGeom 1 == #["note2"])
  -- The title page's `\thispagestyle{empty}`: this page only — page 1
  -- carries no number and every later page keeps its own.
  let (emptyOut, emptyGeom) := build (dvDoc "\\thispagestyle{empty}" threeBody)
  t "thispagestyle empty on page 1 ships no number there"
    (footTexts emptyOut emptyGeom 0 == #[])
  t "and every page after the first keeps exactly its own number"
    (footTexts emptyOut emptyGeom 1 == #["2"] && footTexts emptyOut emptyGeom 2 == #["3"])

/-- The F5 correction, executably: a slot's box is a function of the
declared layout and the geometry alone (`Layout.bandSlotX` — the other
slot is not an argument), priorities decide who yields
(`Ir.ChromeSlot.priority`, total by `priority_injective` and
`BandSlot.rank_ne_of_side_ne`), and yielding is in place and named. One
deck, three left slots — empty, a section title, an unbreakable overlong
note — and the number's line must be byte-identical in x and width across
all three. On the collision the number is painted first (under), still at
the right margin, and W0333 names both the slot that yielded and the slot
that displaced it. -/
def bandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let longTok := String.ofList (List.replicate 10 "0123456789".toList).flatten
  let frame := "\\begin{frame}{F}\nx\n\\end{frame}"
  let run (left : String) : Layout.Out × Array CensusPage :=
    let (doc, _) := elabStr (deck169
      "\\theme{moloch}\\chrome{ footer = { left = \\sectiontitle } }\\title{T}\\author{A}"
      (s!"\\maketitle\n{left}{frame}"))
    let out := layoutOf oneFace doc
    (out, censusOf (coveredColorsOf doc) out)
  -- The number's box on the frame's page: the line whose text is exactly
  -- the number, as (x, width).
  let numBox (c : Array CensusPage) (page : Nat) : Option (Dim.Sp × Dim.Sp) :=
    (c[page]?.bind fun p => p.lines.find? (·.text == "1")).map fun l => (l.x, l.width)
  let (emptyOut, emptyC) := run ""
  let (secOut, secC) := run "\\section{S}\n"
  let (noteOut, noteC) := run s!"\\framefoot\{{longTok}}\n"
  t "band: the empty and filled left slots leave the number's box unmoved"
    (numBox emptyC 1 == numBox secC 2 && (numBox emptyC 1).isSome)
  t "band: the colliding left slot leaves the number's box unmoved too"
    (numBox noteC 1 == numBox emptyC 1)
  t "band: no collision, no yield" ((emptyOut.diags ++ secOut.diags).all
    (·.code != "W0333"))
  t "band: the yield is named with both slots"
    (noteOut.diags.any fun d => d.code == "W0333" && d.severity == .warning &&
      hasStr d.message "framenumber" && hasStr d.message "framefoot note")
  t "band: the yielding number is painted first, under the note"
    ((noteC[1]?.map fun p =>
      match p.lines.findIdx? (·.text == "1"),
            p.lines.findIdx? (fun l => hasStr l.text longTok) with
      | some ni, some ti => ni < ti
      | _, _ => false).getD false)
  -- The section-title case of the same order: an unbreakable overlong
  -- section title displaces the number, never the reverse.
  let (secCollideOut, secCollideC) := run s!"\\section\{{longTok}}\n"
  t "band: the number yields to the section title by declared priority"
    (secCollideOut.diags.any fun d => d.code == "W0333" &&
      hasStr d.message "framenumber yields" && hasStr d.message "sectiontitle")
  t "band: and holds the right margin while yielding"
    (numBox secCollideC 2 == numBox emptyC 1)

-- Cross-backend agreement -------------------------------------------------

/-- Scope: a setting's effect is confined to its declared extent. First the
misplaced-declaration door: a native declaration met where it cannot stand
is ours — named as misplaced, never "unknown" — and its arguments never
become page ink. The invariant whose absence allowed the defect: an
argument that addresses the engine is not content, so no recovery path may
keep it as text. Ink claims are asserted over `Layout.Out` (the census),
never an IR dump. -/
def scopeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let doc (body : String) : String :=
    s!"\\documentclass\{article}\\begin\{document}\n{body}\n\\end\{document}"
  let censusOfSrc (src : String) : Array CensusPage :=
    let (d, _) := elabStr src
    censusOf (coveredColorsOf d) (layoutOf oneFace d geom)
  -- t1: a body running head is a named drop, never body ink.
  let headSrc := doc "\\runninghead{Chapter One}\n\nBody text stands alone."
  let ds1 := (elabStr headSrc).2
  t "a body runninghead is E0347, never unknown"
    (ds1.any (·.code == "E0347") && ds1.all (·.code != "W0301"))
  t "the dropped head text never ships as body ink"
    (let c := censusOfSrc headSrc
     !hasStr (censusText c) "Chapter One" && hasStr (censusText c) "Body text stands alone.")
  t "a body runningfoot with [from] is the same door"
    (let ds := (elabStr (doc "x\n\n\\runningfoot[from=2]{page \\pagenumber}\n\ny")).2
     ds.any (·.code == "E0347") && ds.all (·.code != "W0301"))
  -- t3: a declaration inside inline content is misplaced, never unknown —
  -- and its key/value block never leaks into the sentence (the old path
  -- kept `q = #112233` as text and E0311'd the `#`).
  let inlSrc := doc "a {\\palette{ q = #112233 } b} c"
  let dsi := (elabStr inlSrc).2
  t "an inline palette is W0346, never unknown, and its block never errors"
    (dsi.any (·.code == "W0346") && dsi.all (·.code != "W0301") &&
      dsi.all (·.code != "E0311"))
  t "the inline declaration's block never ships as ink"
    (let c := censusOfSrc inlSrc
     !hasStr (censusText c) "112233" && hasStr (censusText c) "b c")
  t "an inline preamble-only declaration is W0346 too"
    (let ds := (elabStr (doc "\\textbf{\\page{ size = a5 } x}")).2
     ds.any (·.code == "W0346") && ds.all (·.code != "W0301"))
  t "an inline runninghead drops content, an error like the body form"
    (let ds := (elabStr (doc "\\textbf{\\runninghead{X} y}")).2
     ds.any (·.code == "E0347") && ds.all (·.code != "W0301"))
  -- t5: a body fg is confined to the flow after its declaration — the
  -- motivating regression: through `bodyPalette` it once recoloured the
  -- whole page retroactively, first paragraph included. Judged over the
  -- shipped runs of `Layout.Out`, never an IR dump.
  let runsOf (src : String) : Array (String × Ir.Color) :=
    let (d, _) := elabStr src
    let out := layoutOf oneFace d geom
    out.pages.flatMap fun p => p.lines.map fun l =>
      (lineText l,
       (l.segs.findSome? fun seg => match seg with
        | .run _ color _ _ _ _ _ _ _ _ => some color
        | _ => none).getD Ir.Color.black)
  let colorOf (runs : Array (String × Ir.Color)) (needle : String) : Option Ir.Color :=
    (runs.find? fun (text, _) => hasStr text needle).map (·.2)
  let red : Ir.Color := { r := 0xAA, g := 0x22, b := 0x22 }
  let t5 := runsOf (doc
    "Before text stands in the default ink.\n\n\
\\block{\\palette{ fg = #AA2222 }\n\nInside text takes the declared ink.}\n\n\
After text keeps it: flow scope, no brace revert.")
  t "a body fg never reaches the content before its declaration"
    (colorOf t5 "Before text" == some Ir.Color.black)
  t "a body fg colours the content after it, inside the scope"
    (colorOf t5 "Inside text" == some red)
  t "a body fg flows past the closing brace (no brace revert)"
    (colorOf t5 "After text" == some red)
  -- t2: a named colour resolves against the palette in force where it is
  -- used — the pre-declaration use ships the preamble value, the
  -- post-declaration use the body value, in the PDF's shipped runs.
  let pre : Ir.Color := { r := 0x11, g := 0x55, b := 0xCC }
  let post : Ir.Color := { r := 0xCC, g := 0x11, b := 0x00 }
  let t2src := "\\documentclass{article}\\palette{ accent = #1155CC }\
\\begin{document}\n\\textcolor{accent}{Early ink} here.\n\n\
\\palette{ accent = #CC1100 }\n\n\\textcolor{accent}{Late ink} there.\n\\end{document}"
  let t2 := runsOf t2src
  t "a pre-declaration named use ships the preamble value"
    (colorOf t2 "Early ink" == some pre)
  t "a post-declaration named use ships the body value"
    (colorOf t2 "Late ink" == some post)
  -- The typed HTML tree honours the same flow: `:root` carries epoch 0,
  -- and each sibling after the declaration carries the redefinition on
  -- its own style attribute (custom properties inherit into it).
  let (d2, _) := elabStr t2src
  let (head2, body2, _) := HtmlDoc.emitTree {} d2
  let headCss := head2.foldl (fun s n => match n with
    | .style css => s ++ css
    | _ => s) ""
  t "the html :root carries the epoch-0 palette value"
    (hasStr headCss "--accent: #1155cc" && !hasStr headCss "--accent: #cc1100")
  let styleAttrs (nodes : Array Html.Node) : Array (String × String) :=
    -- (own text, style attribute) of each top-level element, in order
    nodes.filterMap fun n => match n with
      | .elem _ attrs _ =>
        some (nodeTextOne "" n, ((attrs.find? (·.1 == "style")).map (·.2)).getD "")
      | _ => none
  let tops := body2.foldl (fun acc n => match n with
    | .elem "main" _ kids => acc ++ kids
    | _ => acc) #[]
  let entries := styleAttrs tops
  t "the html sibling before the declaration carries no epoch redefinition"
    ((entries.find? fun (txt, _) => hasStr txt "Early ink").map
      (fun (_, st) => !hasStr st "--accent") == some true)
  t "the html sibling after the declaration redefines the property on itself"
    ((entries.find? fun (txt, _) => hasStr txt "Late ink").map
      (fun (_, st) => hasStr st "--accent: #cc1100") == some true)
  -- The nested walk (`blockNodesInto`): an epoch inside a block reaches
  -- its later siblings, and — the documented divergence from the PDF's
  -- whole-flow scope — dies at the enclosing element's close, because a
  -- custom property cannot reach an ancestor's later siblings without a
  -- wrapper, and a wrapper would break the rhythm rules' `* + *` sibling
  -- adjacency.
  let (d5, _) := elabStr (doc
    "\\block{First inside.\n\n\\palette{ accent = #CC1100 }\n\nSecond inside.}\n\n\
Outside after.")
  let (_, body5, _) := HtmlDoc.emitTree {} d5
  let els5 := elemStylesList #[] body5.toList
  t "a nested epoch redefines the property on its later siblings"
    (els5.any fun (txt, st) => hasStr txt "Second inside" &&
      !hasStr txt "First inside" && hasStr st "--accent: #cc1100")
  t "a nested epoch never reaches the content before it"
    (els5.all fun (txt, st) => !(hasStr txt "First inside" &&
      !hasStr txt "Second inside" && hasStr st "--accent"))
  t "html: a nested epoch ends at its enclosing element (the named divergence)"
    (els5.all fun (txt, st) => !(hasStr txt "Outside after" && hasStr st "--accent"))
  -- The deck walk threads the same epoch: a declaration between frames
  -- reaches the sections after it.
  let (dd, _) := elabStr ("\\documentclass{slides}\\palette{ accent = #1155CC }\
\\begin{document}\n\\framefoot{note}\n\\begin{frame}{A}\none\n\\end{frame}\n\n\
\\palette{ accent = #CC1100 }\n\n\\begin{frame}{B}\ntwo\n\\end{frame}\n\\end{document}")
  let (_, bodyd, _) := HtmlDoc.emitTree {} dd
  let elsd := elemStylesList #[] bodyd.toList
  t "a deck epoch redefines the property on the frames after it"
    (elsd.any fun (txt, st) => hasStr txt "two" && !hasStr txt "one" &&
      hasStr st "--accent: #cc1100")
  t "a deck epoch never reaches the frames before it"
    (elsd.all fun (txt, st) => !(hasStr txt "one" && !hasStr txt "two" &&
      hasStr st "--accent"))
  -- The confinement oracle — `setting_confined_to_suffix`'s executable
  -- form, over `Layout.run`'s shipped pages: the page closed before the
  -- declaration is identical with and without it. The theorem itself is
  -- blocked: unfolding `collectBlock` needs its equation lemmas, whose
  -- generation for that match exhausts `whnf` (the
  -- `role_transparent_layout` blocker); `Acc.setPalette_emits_nothing`
  -- carries the provable core (the arm emits nothing).
  let outOf (src : String) : Layout.Out :=
    let (d, _) := elabStr src
    layoutOf oneFace d geom
  let confWith := outOf (doc
    "Page one text.\n\\pagebreak\n\\palette{ fg = #AA2222 }\n\nPage two text.")
  let confWithout := outOf (doc "Page one text.\n\\pagebreak\n\nPage two text.")
  t "the page closed before a declaration is identical without it (oracle)"
    (match confWith.pages[0]?, confWithout.pages[0]? with
     | some p1, some p2 => reprStr p1 == reprStr p2
     | _, _ => false)
  t "and the declaration changed the page after it (the oracle bites)"
    (match confWith.pages[1]?, confWithout.pages[1]? with
     | some p1, some p2 => reprStr p1 != reprStr p2
     | _, _ => false)
  -- Contrast per epoch: a pairing is judged against the palette in force
  -- where it is used, never the document's final (or initial) one.
  let codesOf := dvE
  -- A use whose epoch declares a dark page is judged on that page.
  let dsDark := codesOf (doc
    "\\palette{ bg = #202020, dim = #333333 }\n\n\\textcolor{dim}{dim words} here.")
  t "a use inside a dark-page epoch is judged on that page, and realizes there"
    (dsDark.any fun d => d.code == "N0022" && hasStr d.message "#202020")
  -- A body epoch that declares a page and leaves the ink defaulted is the
  -- W0330 defect wherever it is declared.
  t "a body epoch's defaulted ink on its declared page is W0330"
    ((codesOf (doc "x\n\n\\palette{ bg = #111111 }\n\ny")).any (·.code == "W0330"))
  -- The decorative exemption is the epoch's: a plain redeclaration removes
  -- it for the uses after, and only those.
  let dsRedecl := codesOf ("\\documentclass{article}\
\\palette[decorative]{ q = #BBBBBB }\\begin{document}\n\
\\textcolor{q}{quiet before} stays exempt.\n\n\\palette{ q = #BBBBBB }\n\n\
\\textcolor{q}{loud after} is judged.\n\\end{document}")
  t "a plain body redeclaration removes the decorative exemption from here on"
    (dsRedecl.any fun d => d.code == "N0022" && hasStr d.message "'q'")
  -- The resolved-design judge (W0345) is per epoch: a bad frame-title
  -- pair declared before a frame is judged for it; declared after the
  -- last frame, it styles nothing and stays silent.
  let deckDoc (mid tail : String) : String :=
    "\\documentclass{slides}\\theme{moloch}\\begin{document}\n\
\\begin{frame}{A}\none\n\\end{frame}\n\n" ++ mid ++
    "\\begin{frame}{B}\ntwo\n\\end{frame}\n\n" ++ tail ++ "\\end{document}"
  t "a bad frame-title pair declared before a frame is judged for it, and realizes"
    ((codesOf (deckDoc "\\palette{ frametitlebg = #F2F2F0 }\n\n" "")).any
      fun d => d.code == "N0022" && hasStr d.message "'frametitlefg'")
  t "a bad frame-title pair declared after the last frame styles nothing"
    ((codesOf (deckDoc "" "\\palette{ frametitlebg = #F2F2F0 }\n\n")).all
      fun d => d.code != "W0345" && d.code != "N0022")
  -- Per (fg, bg) pair, not per token: moloch's darkened alert passes on
  -- the light page and fails on the dark frame-title bar — the same
  -- colour, two grounds, judged where each sits.
  let deckAlert (title body : String) : String :=
    "\\documentclass{slides}\\theme{moloch}\\begin{document}\n\
\\begin{frame}{" ++ title ++ "}\n" ++ body ++ "\n\\end{frame}\n\\end{document}"
  t "an accent inside the frame title is judged on the bar, and realizes there"
    ((codesOf (deckAlert "An \\alert{urgent} word" "plain body")).any
      fun d => d.code == "N0022" && hasStr d.message "the frame-title bar")
  t "the same accent in the body is judged on the page, and passes there"
    ((codesOf (deckAlert "A title" "an \\alert{urgent} word")).all
      fun d => d.code != "W0315" && d.code != "N0022")
  t "an accent inside a standout frame is judged on the inversion, and realizes"
    ((codesOf ("\\documentclass{slides}\\theme{moloch}\\begin{document}\n\
\\begin{frame}[standout]\nan \\alert{urgent} word\n\\end{frame}\n\\end{document}")).any
      fun d => d.code == "N0022" && hasStr d.message "the standout frame")

/-- Tables and floats: the too-wide diagnostic, the caption's source side,
and the rule extents on the shipped page — a rule claim is judged from
`Layout.Out`, never the IR dump. Its own function: `main`'s do block has no
elaboration budget left. -/
def tableChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrap (tab : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ tab ++ "\n\\end{document}"
  let layoutOut (src : String) : Layout.Out :=
    let doc := (elabStr src).1
    layoutOf oneFace doc
  let layoutDiags (src : String) : Array Diag := (layoutOut src).diags
  -- Each page's shipped text, for page-membership claims: a "these land
  -- together" assertion is judged over `Layout.Out`, never the IR dump.
  let pageTexts (out : Layout.Out) : Array String :=
    out.pages.map fun p => String.join (p.lines.toList.map fun l =>
      String.join (l.segs.toList.map fun s => match s with
        | .run _ _ _ _ glyphs _ _ _ _ _ => String.ofList (glyphs.toList.map (·.2))
        | _ => " "))
  let samePage (src : String) (marks : List String) : Bool :=
    let texts := pageTexts (layoutOut src)
    let pageOf (m : String) : Option Nat :=
      texts.findIdx? fun t => (t.splitOn m).length > 1
    match marks.map pageOf with
    | [] => true
    | p :: rest => p.isSome && rest.all (· == p)
  t "a table wider than the measure is named, in points"
    ((layoutDiags (wrap "\\begin{tabular}{p{0.8\\linewidth}p{0.8\\linewidth}}a & b \\\\\\end{tabular}")).any
      (·.code == "W0338"))
  t "a fitting table is not named"
    (!(layoutDiags (wrap "\\begin{tabular}{ll}a & b \\\\\\end{tabular}")).any
      (·.code == "W0338"))
  t "a caption written above its table stands above"
    (match (elabStr (wrap "\\begin{table}\\caption{Above}\\begin{tabular}{l}a\\\\\\end{tabular}\\end{table}")).1.body with
     | #[.float .table _ true _ cap] => Ir.plainText cap == "Above"
     | _ => false)
  t "a caption written below its table stands below"
    (match (elabStr (wrap "\\begin{table}\\begin{tabular}{l}a\\\\\\end{tabular}\\caption{Below}\\end{table}")).1.body with
     | #[.float .table _ false _ cap] => Ir.plainText cap == "Below"
     | _ => false)
  -- Numbering: each kind counts its own captioned floats in document
  -- order (numberFloats_exact is the theorem; these witness the wiring
  -- from elaboration through the assignment pass).
  t "captioned floats number per kind in document order"
    ((elabStr (wrap ("\\begin{figure}\\caption{f one}\\end{figure}\n" ++
      "\\begin{table}\\caption{t one}\\begin{tabular}{l}a\\\\\\end{tabular}\\end{table}\n" ++
      "\\begin{figure}\\caption{f two}\\end{figure}"))).1.body.toList.filterMap
      (fun b => match b with
        | .float k n _ _ _ => some (k, n)
        | _ => none) ==
      [(.figure, some 1), (.table, some 1), (.figure, some 2)])
  t "a captionless float bears no number and steps no counter"
    ((elabStr (wrap ("\\begin{figure}bare\\end{figure}\n" ++
      "\\begin{figure}\\caption{first}\\end{figure}"))).1.body.toList.filterMap
      (fun b => match b with
        | .float _ n _ _ _ => some n
        | _ => none) == [none, some 1])
  -- The prefix is one definition site both backends read.
  t "caption prefixes spell from the node"
    (Ir.captionPrefix Locale.en .figure (some 2) == some "Figure 2: " &&
     Ir.captionPrefix Locale.en .table (some 1) == some "Table 1: " &&
     Ir.captionPrefix Locale.en .sub (some 1) == some "(a) " &&
     Ir.captionPrefix Locale.en .sub (some 2) == some "(b) " &&
     Ir.captionPrefix Locale.de .figure (some 2) == some "Abbildung 2: " &&
     Ir.captionPrefix Locale.en .figure none == none)
  -- subcaption's subfigure: a minipage-shaped box with its own caption,
  -- lettered under the parent's number (subcaption §2). Consecutive ones
  -- share a `.columns` row; the `\hfill` between them is the gutter.
  let subSrc := wrap ("\\begin{figure}\\centering\n" ++
    "\\begin{subfigure}[t]{0.4\\textwidth}\\centering\nleft panel\n" ++
    "\\caption{First sub}\\end{subfigure}\n\\hfill\n" ++
    "\\begin{subfigure}[t]{0.4\\textwidth}\\centering\nright panel\n" ++
    "\\caption{Second sub}\\end{subfigure}\n" ++
    "\\caption{The parent}\\end{figure}")
  t "subfigures elaborate to lettered sub floats in one columns row"
    (match (elabStr subSrc).1.body with
     | #[.float .figure (some 1) false inner cap] =>
       Ir.plainText cap == "The parent" &&
       (match inner with
        | #[.columns #[(.frac w1, #[.float .sub (some 1) false _ c1]),
                       (.frac w2, #[.float .sub (some 2) false _ c2])]] =>
          w1 == 400 && w2 == 400 &&
          Ir.plainText c1 == "First sub" && Ir.plainText c2 == "Second sub"
        | _ => false)
     | _ => false)
  t "a subfigure outside a figure stays an unknown environment"
    ((elabStr (wrap "\\begin{subfigure}{0.4\\textwidth}x\\caption{c}\\end{subfigure}")).2.any
      (·.code == "W0302"))
  t "subfigure letters reset per parent"
    (match (elabStr (wrap ("\\begin{figure}\n" ++
      "\\begin{subfigure}{0.9\\textwidth}a\\caption{one}\\end{subfigure}\n" ++
      "\\caption{P1}\\end{figure}\n" ++
      "\\begin{figure}\n" ++
      "\\begin{subfigure}{0.9\\textwidth}b\\caption{two}\\end{subfigure}\n" ++
      "\\caption{P2}\\end{figure}"))).1.body with
     | #[.float .figure (some 1) false i1 _, .float .figure (some 2) false i2 _] =>
       (match i1, i2 with
        | #[.columns #[(_, #[.float .sub (some n1) _ _ _])]],
          #[.columns #[(_, #[.float .sub (some n2) _ _ _])]] =>
          n1 == 1 && n2 == 1
        | _, _ => false)
     | _ => false)
  -- The typed-tree half of the rendered check: each subfigure is a
  -- nested <figure> with its lettered <figcaption>, through the escaper
  -- by construction.
  let subHtml := (HtmlDoc.emit {} (elabStr subSrc).1).1
  t "subfigures are nested figures with lettered figcaptions in HTML"
    ((subHtml.splitOn "<figure class=\"float subfloat\">").length == 3 &&
     (subHtml.splitOn "<figcaption>(a) First sub</figcaption>").length == 2 &&
     (subHtml.splitOn "<figcaption>(b) Second sub</figcaption>").length == 2 &&
     (subHtml.splitOn "<figcaption>Figure 1: The parent</figcaption>").length == 2)
  -- A float is unbreakable: LaTeX's float model places the whole box or
  -- defers it, never splits one (ltfloat.dtx; the float body is Knuth's
  -- `\vbox`). The `\vspace` sweep parks the object at every position
  -- around the page bottom in 3pt steps, so some step lands the seam
  -- exactly there whatever the face's metrics — and at every step the
  -- caption and its object ship on one page, judged over `Layout.Out`.
  let tieDoc (pts : Nat) : String :=
    "\\documentclass{article}\n\\page{ size = a5 }\n\\begin{document}\n" ++
    s!"top\n\n\\vspace\{{pts}pt}\n\n\\begin\{table}\n" ++
    "\\begin{tabular}{l}\nalpha \\\\\n\\end{tabular}\n" ++
    "\\caption{Below the table}\n\\end{table}\n\\end{document}"
  t "a float ships whole at every seam position"
    ((List.range 50).all fun k =>
      samePage (tieDoc (350 + 3 * k)) ["alpha", "Below the table"])
  t "a float that fits mid-page stays on its page"
    ((pageTexts (layoutOut (tieDoc 12))).size == 1 &&
      samePage (tieDoc 12) ["top", "alpha", "Below the table"])
  -- The table that shipped one cell per page: a six-row booktabs table
  -- with inline math in its first column, standing where little of the
  -- page is left. Every cell of every row lands on one page with the
  -- caption, at every seam position.
  let mathTable (pts : Nat) : String :=
    "\\documentclass{article}\n\\page{ size = a5 }\n\\begin{document}\n" ++
    s!"top\n\n\\vspace\{{pts}pt}\n\n\\begin\{table}\n\\centering\n" ++
    "\\caption{Six rows}\n\\begin{tabular}{lrr}\n\\toprule\n" ++
    "kind & alpha & beta \\\\\n\\midrule\n" ++
    "$T_\\mathrm{aa}$ & 13 & 2 \\\\\n$T_\\mathrm{bb}$ & 16 & 3 \\\\\n" ++
    "$T_\\mathrm{cc}$ & 1 & 1 \\\\\nrowd & 30 & 6 \\\\\n" ++
    "rowe & 365 & 165 \\\\\nrowf & 999 & 111 \\\\\n" ++
    "\\bottomrule\n\\end{tabular}\n\\end{table}\n\\end{document}"
  t "a six-row table with math cells ships whole at every seam position"
    ((List.range 40).all fun k =>
      samePage (mathTable (280 + 6 * k)) ["Six rows", "kind", "rowd", "rowf"])
  -- A float taller than the text block still ships whole: placed alone on
  -- its own page, the overrun named (W0358), never split.
  let tallDoc :=
    "\\documentclass{article}\n\\page{ size = a5 }\n\\begin{document}\ntop\n\n" ++
    "\\begin{table}\n\\begin{tabular}{l}\nfirstrow \\\\\n" ++
    String.join (List.replicate 58 "middle \\\\\n") ++
    "lastrow \\\\\n\\end{tabular}\n\\caption{Below the table}\n\\end{table}\n" ++
    "\\end{document}"
  t "a float taller than the text block is placed alone, whole, and named"
    ((layoutDiags tallDoc).any (·.code == "W0358") &&
      samePage tallDoc ["firstrow", "lastrow", "Below the table"])
  t "a fitting float is not named tall"
    (!(layoutDiags (tieDoc 12)).any (·.code == "W0358"))
  -- `spill_accounts` (W0384), over the shipped pages: a frame whose
  -- content does not fit closes its page mid-frame and continues; without
  -- a declared [allowframebreaks] that continuation is paid for by exactly
  -- one warning naming the frame — with the declaration, or on an
  -- article's page close (flow, not a spill), none. The page counts hold
  -- either way: the diagnostic never changes what ships.
  let tall (opts : String) :=
    "\\documentclass{slides}\n\\theme{moloch}\n\\begin{document}\n" ++
    "\\begin{frame}" ++ opts ++ "{Too tall}\n" ++
    String.join (List.replicate 30 "one line\n\n") ++ "\\end{frame}\n\\end{document}"
  let tallOut := layoutOf oneFace (elabStr (tall "")).1
  let breakOut := layoutOf oneFace (elabStr (tall "[allowframebreaks]")).1
  t "spill: an undeclared frame that continues fires W0384 exactly once, naming the frame"
    (tallOut.pages.size ≥ 2 &&
     (tallOut.diags.filter (·.code == "W0384")).size == 1 &&
     (tallOut.diags.find? (·.code == "W0384")).bind (·.subject) == some "1")
  t "spill: [allowframebreaks] declares the continuation; the pages ship, the account is silent"
    (breakOut.pages.size == tallOut.pages.size && breakOut.diags.all (·.code != "W0384") &&
     (dvE (tall "[allowframebreaks]")).all (·.code != "N0102"))
  t "spill: a frame that fits is silent"
    ((layoutOf oneFace (elabStr (deck169 "\\theme{moloch}"
      "\\begin{frame}{Fits}\none line\n\\end{frame}")).1).diags.all (·.code != "W0384"))
  t "spill: an article's page close is flow, never a spill"
    ((layoutDiags ("\\documentclass{article}\n\\page{ size = a5 }\n\\begin{document}\n" ++
      String.join (List.replicate 120 "one line\n\n") ++ "\\end{document}")).all
        (·.code != "W0384"))
  -- Alternation's spill account, over the shipped pages. A step page inks
  -- one group of an `\alt` (`Ir.altShowsFirst`), so its height — and the
  -- spill it is charged for — is that group's alone. The pair of `step`
  -- nodes alternation replaced put BOTH groups on every step page, so it
  -- was the taller reading of the same source: more pages, and one
  -- collapsed report, because every step page carried identical content
  -- and W0384 dedupes by message. These pin the direction, so a later
  -- change cannot make selection cost pages or invent an account: the
  -- stacked shape is asserted beside the selected one in each, which is
  -- what keeps the claims from passing vacuously.
  let altFiller (tag : String) (rows reps : Nat) : String :=
    String.join ((List.range rows).map fun i =>
      tag ++ " " ++ toString i ++ " " ++
        String.join (List.replicate reps "band of body text ") ++ "\n\n")
  let altFrame (body : String) : String :=
    deck169 "\\theme{moloch}"
      ("\\begin{frame}{Alternating}\n" ++ body ++ "\n\\end{frame}")
  let altSrc (a b : String) : String :=
    altFrame ("\\alt<2>{" ++ a ++ "}{" ++ b ++ "}")
  -- The shape `\alt` used to elaborate to: the active group in range, the
  -- other before it, both on the page under dim-not-hide.
  let stackSrc (a b : String) : String :=
    altFrame ("\\onslide<2>{" ++ a ++ "}\\onslide<1>{" ++ b ++ "}")
  let shipsMark (src mark : String) : Array Bool :=
    (pageTexts (layoutOut src)).map fun txt => (txt.splitOn mark).length > 1
  let spillTexts (src : String) : Array String :=
    ((layoutDiags src).filter (·.code == "W0384")).map (·.message)
  let one := "Alphafill"
  let two := "Bravofill"
  let shortA := altFiller one 1 1
  let shortB := altFiller two 1 1
  t "alternation: each step page inks one group, where the stack it replaced inks both"
    (shipsMark (altSrc shortA shortB) one == #[false, true] &&
     shipsMark (altSrc shortA shortB) two == #[true, false] &&
     shipsMark (stackSrc shortA shortB) one == #[true, true] &&
     shipsMark (stackSrc shortA shortB) two == #[true, true])
  -- The step count is the spec's, not the selection's: a frame whose every
  -- step fits ships exactly one page per step under either shape.
  t "alternation: a fitting frame ships one page per step, as the stack does"
    ((layoutOut (altSrc shortA shortB)).pages.size ==
       (layoutOut (stackSrc shortA shortB)).pages.size &&
     (layoutOut (altSrc shortA shortB)).pages.size == 2 &&
     (layoutOut (altFrame ("\\alt<3-4>{" ++ shortA ++ "}{" ++ shortB ++ "}" ++
       "\n\\pause\\pause\\pause"))).pages.size == 4)
  -- Selection never costs a page and never adds an account: swept across
  -- the page boundary, so the claim covers a group that fits, one that
  -- does not, and the seam between them.
  t "alternation: never more pages and never more spill accounts than the stack"
    ((List.range 9).all fun k =>
      let a := altFiller one (5 + 2 * k) 3
      let b := altFiller two (5 + 2 * k) 3
      (layoutOut (altSrc a b)).pages.size ≤ (layoutOut (stackSrc a b)).pages.size &&
        (spillTexts (altSrc a b)).size ≤ (spillTexts (stackSrc a b)).size)
  -- And the account it does raise is true: what a step page is charged for
  -- is what the group it ships is charged for standing alone, so
  -- alternation neither invents a spill nor inflates one. The groups spill
  -- by different amounts — one is set larger, so a different band is the
  -- one that fails to fit — because equal numbers would let a wrong
  -- attribution pass: W0384 dedupes by message, which is exactly how the
  -- stacked shape reported one figure for a frame whose two readings
  -- overflow by two.
  let overA := altFiller one 20 3
  let overB := "{\\Large " ++ altFiller two 9 3 ++ "}"
  t "alternation: a step page's spill is the selected group's own, not the stack's"
    (spillTexts (altSrc overA overB) ==
       (spillTexts (altFrame overB)) ++ (spillTexts (altFrame overA)) &&
     (spillTexts (altFrame overA)).size == 1 &&
     (spillTexts (altFrame overB)).size == 1 &&
     spillTexts (altFrame overA) != spillTexts (altFrame overB) &&
     spillTexts (stackSrc overA overB) == spillTexts (altFrame overA))
  -- The caption gap has a side: `captionsep` on the object side,
  -- `floatsep` on the text side, whichever side the caption stands
  -- (classes.dtx: `\abovecaptionskip` 10pt between object and caption,
  -- `\belowcaptionskip` 0pt — the text side is the float separation the
  -- text already has; the caption package's `tableposition=top` swaps
  -- the pair for a caption above — the sourcing note at
  -- `Ir.captionSepDefault`). Judged over `Layout.Out` baselines: both
  -- text-side deltas agree, the object side sits exactly one half-unit
  -- (floatsep − captionsep, 6pt at the 10pt base) tighter, and the
  -- float's total extent is caption-position-independent — the realized
  -- form of `floatPlan_gaps_conserved`.
  let figDoc (above : Bool) (decl : String := "") : String :=
    "\\documentclass{article}\n" ++ decl ++ "\\begin{document}\nbefore words\n\n" ++
    (if above then
      "\\begin{figure}\n\\caption{Caption words}\nBody line\n\\end{figure}"
     else
      "\\begin{figure}\nBody line\n\\caption{Caption words}\n\\end{figure}") ++
    "\n\nafter words\n\\end{document}"
  let deltas (src : String) : Option (Int × Int × Int) :=
    match (layoutOut src).pages[0]? with
    | some p =>
      match (p.lines.filter (!·.furniture)).map (·.y) with
      | #[y0, y1, y2, y3] => some (y1 - y0, y2 - y1, y3 - y2)
      | _ => none
    | none => none
  t "the caption gap is object-side: text sides agree, object side ½u tighter"
    (match deltas (figDoc false), deltas (figDoc true) with
     | some (b1, b2, b3), some (a1, a2, a3) =>
       b1 == b3 && b1 - b2 == Dim.pt 6 &&
       a1 == a3 && a1 - a2 == Dim.pt 6
     | _, _ => false)
  t "a captioned float's extent is caption-position-independent"
    (match deltas (figDoc false), deltas (figDoc true) with
     | some (b1, b2, b3), some (a1, a2, a3) => b1 + b2 + b3 == a1 + a2 + a3
     | _, _ => false)
  t "captionsetup skip=12pt raises the object side to the text side's 12pt"
    (match deltas (figDoc false "\\captionsetup{skip=12pt}\n") with
     | some (d1, d2, _) => d1 == d2
     | _ => false)
  -- Rules span exactly their columns, judged on the page: the full rules
  -- share one left edge and one width; the trimmed \cmidrule lies strictly
  -- inside them. An executable check, not a theorem — the extents live in
  -- `collectTable`'s local arithmetic.
  let doc := (elabStr (wrap ("\\begin{tabular}{ll}\\toprule\na & b \\\\ \\cmidrule(lr){2-2}\nc & d \\\\ \\bottomrule\\end{tabular}"))).1
  let out := layoutOf oneFace doc
  let ruleSegs : Array (Dim.Sp × Dim.Sp) := Id.run do
    let mut acc : Array (Dim.Sp × Dim.Sp) := #[]
    for p in out.pages do
      for l in p.lines do
        let mut x := l.x
        for s in l.segs do
          match s with
          | .rule w _ _ _ =>
            acc := acc.push (x, w)
            x := x + w
          | .gap g _ => x := x + g
          | .run _ _ _ w _ _ _ _ _ _ => x := x + w
          | .image _ w _ => x := x + w
    return acc
  t "the three rules ship" (ruleSegs.size == 3)
  t "toprule and bottomrule span the same extent"
    ((ruleSegs[0]?).isSome && ruleSegs[0]? == ruleSegs[2]?)
  t "the trimmed cmidrule lies strictly inside the full rules"
    (match ruleSegs[0]?, ruleSegs[1]? with
     | some (fx, fw), some (cx, cw) => decide (fx < cx && cx + cw < fx + fw)
     | _, _ => false)

def kpChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- knuth–plass: DP result equals brute-force minimum over all break sequences
  let cases : List (String × Array Layout.Item × Dim.Sp) := [
    ("three words", mkItems [W 100, G, W 100, G, W 100], Dim.pt 250),
    ("four words", mkItems [W 50, G, W 60, G, W 70, G, W 80], Dim.pt 150),
    ("forced mid", mkItems ([W 100, G, W 100] ++ BRK ++ [W 100]), Dim.pt 250),
    ("overfull word", mkItems [W 300], Dim.pt 100),
    ("tight fit", mkItems [W 80, G, W 80, G, W 80, G, W 80, G, W 80], Dim.pt 170),
    ("hyphen choice", mkItems [W 60, G, W 40, H, W 50, G, W 60], Dim.pt 120),
    ("double hyphen", mkItems [W 70, H, W 70, H, W 70, H, W 70], Dim.pt 80),
    ("hyphen vs glue", mkItems [W 50, G, W 30, H, W 30, G, W 50, G, W 40], Dim.pt 100)]
  for (name, items, target) in cases do
    let kpBreaks := (Layout.kp items target).toList
    let kpCost := seqCost items target kpBreaks
    let brute := bruteBest items target
    t s!"kp optimal ({name})" (kpCost.isSome && kpCost == brute && !kpBreaks.isEmpty)
  -- Ragged setting prices looseness: under fil interword glue every
  -- minimal-line-count break sequence ties at zero badness (fil hides all
  -- looseness from the badness function, TeXbook ch. 14), and the DP's
  -- tie-break packs lines from the paragraph's end — ten equal words at a
  -- three-word measure broke 1/3/3/3, the whole slack dumped on the first
  -- line (the beamerposter first-line defect). Finite stretch makes the
  -- packed shape strictly cheaper: every line but the last fills.
  let ragged := Layout.raggedItems
    (mkItems (List.intersperse G (List.replicate 10 (W 50))))
  let rNats : Array Dim.Sp := Id.run do
    let mut prev := 0
    let mut first := true
    let mut nats : Array Dim.Sp := #[]
    for b in Layout.kp ragged (Dim.pt 200) do
      let a := if first then Layout.lineStart ragged 0
        else Layout.lineStart ragged (prev + 1)
      nats := nats.push (Layout.measure ragged a b).natural
      prev := b
      first := false
    return nats
  t "ragged breaking fills every line but the last"
    (rNats.size == 4 && rNats.pop.all (· ≥ Dim.pt 150))
  t "ragged glue is finite; a declared fil stays free"
    ((Layout.raggedItems (mkItems [W 50, G, W 50])).all fun it => match it with
      | .glue g => (g.fil && g.stretch == 0) || (!g.fil && g.stretch == g.width * 6)
      | _ => true)

def hyphenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Hyphenation. Expectations are real TeX \showhyphens output with the SAME
  -- pattern set the engine embeds (luatex + hyph-en-us.tex, hyphenmins 2/3);
  -- plain lualatex is a different oracle because TeX Live maps `english` to
  -- hyphen.tex, Knuth's frozen subset. \showhyphens lists every admissible
  -- break, not one chosen rendering. Full 552-word check: scripts/hyphen-diff.lean
  let pats := Hyphen.english.get
  let hyph (w : String) : String := Id.run do
    let breaks := Hyphen.hyphenate pats w
    let mut out := ""
    for (c, i) in w.toList.zipIdx do
      if i > 0 && breaks.contains i then
        out := out.push '-'
      out := out.push c
    return out
  t "hyphen patterns loaded" (pats.map.size > 4000)
  t "hyphen incomprehensibility" (hyph "incomprehensibility" == "in-com-pre-hen-si-bil-ity")
  t "hyphen internationalization" (hyph "internationalization" == "in-ter-na-tion-al-iza-tion")
  t "hyphen algorithm" (hyph "algorithm" == "al-go-rithm")
  t "hyphen paragraph" (hyph "paragraph" == "para-graph")
  t "hyphen typesetting" (hyph "typesetting" == "type-set-ting")
  t "hyphen hyphenation" (hyph "hyphenation" == "hy-phen-ation")
  t "hyphen long word" (hyph "floccinaucinihilipilification" ==
    "floc-cin-aucini-hilip-il-i-fi-ca-tion")
  t "hyphen exception dictionary" (hyph "associate" == "as-so-ciate")
  t "hyphen short word untouched" (hyph "cat" == "cat")
  t "hyphen capitalized" (hyph "Paragraph" == "Para-graph")
  -- These three pin the pattern set: Knuth's hyphen.tex gives def-i-ni-tion,
  -- mono-tone, and no break at all in toolchain.
  t "hyphen set is ushyphmax (definition)" (hyph "definition" == "de-f-i-n-i-tion")
  t "hyphen set is ushyphmax (monotone)" (hyph "monotone" == "mo-not-one")
  t "hyphen set is ushyphmax (toolchain)" (hyph "toolchain" == "tool-chain")
  -- French (hyph-fr.tex, selected per language: patsOf). Expectations are
  -- lualatex \showhyphens output under [french]{babel} on this host, the
  -- same oracle as the English rows.
  let frp := Hyphen.french.get
  let hyphFr (w : String) : String := Id.run do
    let breaks := Hyphen.hyphenate frp w
    let mut out := ""
    for (c, i) in w.toList.zipIdx do
      if i > 0 && breaks.contains i then
        out := out.push '-'
      out := out.push c
    return out
  t "hyphen french patterns loaded" (frp.map.size > 1000)
  t "hyphen fr considérablement" (hyphFr "considérablement" == "consi-dé-ra-ble-ment")
  t "hyphen fr constitution" (hyphFr "constitution" == "consti-tu-tion")
  t "hyphen fr déclaration" (hyphFr "déclaration" == "dé-cla-ra-tion")
  -- The word boundary is Unicode (Nfc.isLetter/toLower): an accented word
  -- hyphenates whole, capitalized included.
  t "hyphen fr accented capital folds" (hyphFr "Bélair" == "Bé-lair")
  -- German (hyph-de-1996.tex, hyphenmins 2/2 from the locale record).
  -- Verified against luatex loading the same file: hyphen-diff --lang de,
  -- 2800 words, exact.
  let dep := Hyphen.german.get
  let hyphDe (w : String) : String := Id.run do
    let breaks := Hyphen.hyphenate dep w
    let mut out := ""
    for (c, i) in w.toList.zipIdx do
      if i > 0 && breaks.contains i then
        out := out.push '-'
      out := out.push c
    return out
  t "hyphen german patterns loaded" (dep.map.size > 30000)
  t "hyphen de wissenschaft" (hyphDe "Wissenschaft" == "Wis-sen-schaft")
  t "hyphen de compound" (hyphDe "Donaudampfschifffahrt" == "Do-nau-dampf-schiff-fahrt")
  t "hyphen de rightmin 2" (hyphDe "Zusammenfassung" == "Zu-sam-men-fas-sung")
  -- English patterns on the same word give different (wrong) breaks: the
  -- selection is load-bearing.
  t "hyphen en mis-breaks french" (hyph "considérablement" != "consi-dé-ra-ble-ment")
  -- patsOf: the one selection site (hyphenation_follows_language is the
  -- theorem; these pin the executable readings).
  t "patsOf main for untagged" (Layout.patsOf (some pats) none |>.isSome)
  t "patsOf tagged run takes its own language"
    ((Layout.patsOf (some pats) (some "fr")).map (·.map.size) == some frp.map.size)
  t "patsOf off is off for every tag" ((Layout.patsOf none (some "fr")).isNone)
  -- leftMin=2 / rightMin=3 are enforced, so no break may strand 1 letter or 2.
  t "hyphen respects hyphenmins" ((Hyphen.hyphenate pats "typesetting").all
    fun p => p ≥ 2 && p + 3 ≤ 11)

/-- The measure band (W0201): fires on continuous text set too wide or too
narrow, is scoped to pages rather than slides, and is silenced by declaring
`\page{ measure = free }`. -/
def measureChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Long enough to set at least four full lines at any measure under test.
  let prose := String.intercalate " " (List.replicate 40 "typesetting is the arrangement of type")
  let diagsOf (pre : String) (body : String) (geom : Layout.Geom := {}) : Array Diag :=
    let src := pre ++ "\\begin{document}" ++ body ++ "\\end{document}"
    (layoutOf oneFace (Elab.run "t" src).1 geom).diags
  let w0201 (ds : Array Diag) : Array Diag := ds.filter (·.code == "W0201")
  -- The word-processor default this engine replaced: letter with 1in
  -- margins holds ~100 characters at 10pt, far outside 45–90.
  let wide := diagsOf "\\documentclass{article}\\page{ hmargin = 1in }" prose
  t "wide measure warns" ((w0201 wide).size == 1)
  t "wide measure says narrow"
    ((w0201 wide).all fun d => (d.help.getD "").startsWith "narrow")
  t "measure = free silences the band"
    ((w0201 (diagsOf "\\documentclass{article}\\page{ hmargin = 1in, measure = free }" prose)).isEmpty)
  t "slides are outside the rule's scope"
    ((w0201 (diagsOf "\\documentclass{slides}" prose)).isEmpty)
  -- A card is display text too, and its default measure (~214pt, under 45
  -- characters) would earn "widen" in an article: the band is about
  -- continuous reading and does not apply to the class.
  let (cardProse, _) := Elab.run "t" ("\\documentclass{card}\\begin{document}" ++
    prose ++ "\\end{document}")
  t "cards are outside the rule's scope"
    ((w0201 (layoutOf oneFace cardProse).diags).isEmpty)
  t "short text is not continuous reading"
    ((w0201 (diagsOf "\\documentclass{article}\\page{ hmargin = 1in }" "one line.")).isEmpty)
  let narrowGeom : Layout.Geom :=
    { pageW := Dim.pt 200, pageH := Dim.pt 2000, hmargin := Dim.pt 10, vmargin := Dim.pt 10 }
  let narrow := diagsOf "\\documentclass{article}" prose narrowGeom
  t "narrow measure warns and says widen"
    ((w0201 narrow).size == 1 &&
     (w0201 narrow).all fun d => (d.help.getD "").startsWith "widen")
  -- The default article page carries Bringhurst's 26-pica text block, and
  -- the band it was chosen for holds on it.
  let (dfltDoc, _) := Elab.run "t" ("\\documentclass{article}\\begin{document}" ++
    prose ++ "\\end{document}")
  t "default article text block is 26 picas"
    (dfltDoc.page.width - 2 * dfltDoc.page.hmargin == Ir.articleTextBlock)
  t "default article measure is in band"
    ((w0201 (layoutOf oneFace dfltDoc).diags).isEmpty)
  -- A document that declared any \page geometry keeps every value it named.
  let (declDoc, _) := Elab.run "t"
    "\\documentclass{article}\\page{ vmargin = 0.5in }\\begin{document}x\\end{document}"
  t "declared \\page keeps the named margins" (declDoc.page.hmargin == Dim.inch 1)
  t "measure key rejects a stray value"
    ((elabStr "\\documentclass{article}\\page{ measure = loose }\\begin{document}x\\end{document}").2.any
      (·.code == "E0323"))
  -- The body size: slides default to beamer's documented 11pt, articles to
  -- the 10pt base; a class option or \page{ fontsize } takes precedence.
  let pageOf (src : String) : Ir.PageSpec :=
    (elabStr (src ++ "\\begin{document}x\\end{document}")).1.page
  t "slides default to beamer's 11pt"
    ((pageOf "\\documentclass{slides}").fontSize == Ir.slidesFontSize)
  t "articles keep the 10pt base"
    ((pageOf "\\documentclass{article}").fontSize == Ir.baseFontSize)
  t "a bare size class option is honored"
    ((pageOf "\\documentclass[10pt]{slides}").fontSize == Dim.pt 10)
  t "a fontsize= class option is honored"
    ((pageOf "\\documentclass[paper=letter, fontsize=12pt]{article}").fontSize == Dim.pt 12)
  t "\\page fontsize wins over the class option"
    ((pageOf "\\documentclass[10pt]{article}\\page{ fontsize = 14pt }").fontSize == Dim.pt 14)
  -- The guard admits exactly what `Layout.heading_hierarchy` covers: its
  -- 1 pt floor. A sub-point base was reachable and outside the theorem
  -- before the guard aligned (the D2 gap: positive but below the floor).
  t "a sub-point \\page fontsize is rejected and keeps the base"
    (((elabStr ("\\documentclass{article}\\page{ fontsize = 0.4pt }" ++
        "\\begin{document}x\\end{document}")).2.any (·.code == "E0323")) &&
     (pageOf "\\documentclass{article}\\page{ fontsize = 0.4pt }").fontSize
       == Ir.baseFontSize)

/-- Vertical-rhythm diagnostics: a heading binds to the text it introduces,
so declared space below it must not exceed the declared space above. -/
def rhythmChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let layoutDiags (styleBlock : String) : Array Diag :=
    let src := "\\documentclass{article}\\tokens{ u = 4pt }" ++ styleBlock ++
      "\\begin{document}\\section{Head}Body\\end{document}"
    (layoutOf oneFace (Elab.run "t" src).1 {}).diags
  t "heading below-heavy spacing warns"
    ((layoutDiags "\\style{section}{ before = u, after = 2 * u }").any (·.code == "W0202"))
  t "heading above-heavy spacing is silent"
    (!(layoutDiags "\\style{section}{ before = 2 * u, after = u }").any (·.code == "W0202"))
  t "heading equal spacing is silent"
    (!(layoutDiags "\\style{section}{ before = u, after = u }").any (·.code == "W0202"))
  t "an undeclared side is not compared"
    (!(layoutDiags "\\style{section}{ after = 2 * u }").any (·.code == "W0202"))

/-- The `card` document class: trade-standard trim sizes, print safe-zone
margins, no hyphenation, no running furniture, bleed on request. -/
def cardChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let card (opts body : String) (pre : String := "") : String :=
    s!"\\documentclass{opts}\{card}\n{pre}\\begin\{document}\n{body}\n\\end\{document}"
  let (cDoc, cDs) := elabStr (card "" "Pat Placeholder")
  t "card class parses clean" (!cDs.any (·.severity == .error))
  -- ISO/IEC 7810 ID-1, the size most business cards follow: 85.60 × 53.98 mm.
  t "card defaults to ISO/IEC 7810 ID-1"
    (cDoc.page.width == Dim.mm100 8560 && cDoc.page.height == Dim.mm100 5398)
  t "us option is the 3.5 × 2 in trade size"
    ((elabStr (card "[us]" "x")).1.page.width == Dim.pt 252 &&
     (elabStr (card "[us]" "x")).1.page.height == Dim.pt 144)
  t "jis option is the 91 × 55 mm meishi"
    ((elabStr (card "[jis]" "x")).1.page.width == Dim.mm 91 &&
     (elabStr (card "[jis]" "x")).1.page.height == Dim.mm 55)
  -- Margins default to the print safe zone: content there risks the trim.
  t "card margins default to the safe zone"
    (cDoc.page.hmargin == Dim.mm 5 && cDoc.page.vmargin == Dim.mm 5)
  t "a declared page beats the card defaults"
    ((elabStr (card "" "x" "\\page{ width = 100pt, height = 60pt, margin = 4pt }\n")).1.page.width
      == Dim.pt 100)
  t "card turns hyphenation off by default"
    (cDoc.page.hyphenate == some false)
  -- Below the 40-character working minimum for justified text the measure
  -- is set ragged (Bringhurst): forcing justification at card width gives
  -- the breaker only overfull answers.
  t "card sets ragged by default" (cDoc.page.justify == some false)
  t "justify is a page key any class may declare"
    ((elabStr "\\page{ justify = off }\\begin{document}x\\end{document}").1.page.justify
      == some false)
  let prose := String.intercalate " " (List.replicate 20 "placeholder words")
  let judgeOverfull (pre : String) : Bool :=
    let doc := (elabStr (card "" prose pre)).1
    let out := layoutOf oneFace doc
    out.diags.any (·.code == "W0005")
  t "ragged card prose breaks without overfull lines" (!judgeOverfull "")
  t "the same prose justified at card width cannot break"
    (judgeOverfull "\\page{ justify = on }\n")
  t "article leaves hyphenation to the class default"
    ((elabStr "x").1.page.hyphenate == none)
  t "hyphenate is a page key any class may declare"
    ((elabStr "\\page{ hyphenate = off }\\begin{document}x\\end{document}").1.page.hyphenate
      == some false)
  t "hyphenate rejects a value that is not on or off"
    (errCodes "\\page{ hyphenate = 5pt }\\begin{document}x\\end{document}" == ["E0323"])
  -- The gate lives in layout: the same narrow measure hyphenates as an
  -- article and must not as a card, whoever loaded the patterns.
  let hyphenRendered (doc : Ir.Doc) : Bool :=
    let out := layoutOf oneFace doc (pats := some pats)
    out.pages.any fun p => p.lines.any fun l =>
      l.segs.any fun s => match s with
        | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2 == '-')
        | .gap _ _ | .rule .. | .image .. => false
  let narrowPage := "\\page{ width = 90pt, height = 400pt, margin = 10pt }\n"
  let word := "incomprehensibility incomprehensibility"
  t "an article at this measure does hyphenate"
    (hyphenRendered (elabStr (s!"{narrowPage}\\begin\{document}\n{word}\n\\end\{document}")).1)
  t "a card never hyphenates"
    (!hyphenRendered (elabStr (card "" word narrowPage)).1)
  -- A card carries no running furniture: the declaration is dropped loudly.
  let (rDoc, rDs) := elabStr (card "" "x" "\\runninghead{name \\pagenumber}\n")
  t "card drops running content with W0317"
    (rDs.any (·.code == "W0317") && rDoc.head.isNone)
  -- Two faces are two frames: one page each, through the same page-boundary
  -- mechanism every class shares.
  let two := card "" "\\begin{frame}front\\end{frame}\n\\begin{frame}back\\end{frame}"
  let (twoDoc, twoDs) := elabStr two
  t "card faces source clean" (!twoDs.any (·.severity == .error))
  t "two faces are two pages"
    ((layoutOf oneFace twoDoc).pages.size == 2)
  -- Bleed grows the medium and records the trim box; without it the page
  -- dictionaries stay exactly as they were.
  let (bDoc, bDs) := elabStr (card "" "x" "\\page{ bleed = 3mm }\n")
  t "bleed declaration is clean" (!bDs.any (·.severity == .error))
  t "bleed reaches the page spec" (bDoc.page.bleed == Dim.mm 3)
  let bGeom := Layout.Geom.ofPage bDoc.page
  let bOut := layoutOf oneFace bDoc bGeom
  let bPdf := pdfText (Pdf.write bGeom oneFace bOut.pages)
  t "bleed writes a TrimBox 3mm in from the medium corner"
    (bytesContain bPdf "/TrimBox [8.504 8.504 251.15 161.518]")
  t "bleed grows the MediaBox by twice itself"
    (bytesContain bPdf "/MediaBox [0 0 259.654 170.022]")
  -- The ink shifts with the trim box: the first glyph sits at the margin
  -- measured from the trim corner (8.504 + 14.173 pt), not the medium corner.
  t "bleed shifts the content with the trim box"
    (bytesContain bPdf "1 0 0 1 22.677 ")
  let plainGeom := Layout.Geom.ofPage cDoc.page
  let plainPdf := pdfText (Pdf.write plainGeom oneFace
    (layoutOf oneFace cDoc plainGeom).pages)
  t "no bleed, no TrimBox" (!bytesContain plainPdf "/TrimBox")
  -- What the class guarantees, stated as the assertions the engine already
  -- enforces. Declaring an assertion of the same form is intent and takes
  -- control of the bound.
  let cardAsserts (src : String) := (elabStr src).1.asserts
  let plainAsserts := cardAsserts (card "" "x")
  t "card implies its three guarantees"
    (plainAsserts.any (·.kind == .pages .le 1) &&
     plainAsserts.any (·.kind == .textInArea) &&
     plainAsserts.any (·.kind == .minXHeight Ir.cardXHeightFloor))
  t "two faces raise the fits bound" ((cardAsserts two).any (·.kind == .pages .le 2))
  t "declared intent silences the class default"
    (((cardAsserts (card "" "x" "\\assert{ pages <= 4 }\n")).filter
      (fun a => match a.kind with | .pages _ _ => true | _ => false)).size == 1)
  t "article never gets the card contract" ((elabStr "x").1.asserts.isEmpty)
  t "assert text.in_area is declarable anywhere"
    ((elabStr "\\assert{ text.in_area }\\begin{document}x\\end{document}").1.asserts.any
      (·.kind == .textInArea))
  t "assert text.xheight takes a dimension"
    ((elabStr "\\assert{ text.xheight >= 2mm }\\begin{document}x\\end{document}").1.asserts.any
      (·.kind == .minXHeight (Dim.mm 2)))
  t "assert text.xheight rejects a word"
    (errCodes "\\assert{ text.xheight >= wide }\\begin{document}x\\end{document}" == ["E0325"])
  -- Each guarantee fails on the card built to violate it, through the same
  -- judge-the-shipped-pages path the build uses.
  let judge (src : String) : Array Diag :=
    let doc := (elabStr src).1
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom
    Check.all (Check.Shipped.ofOut geom oneFace out true) doc.asserts
  let lorem := String.intercalate " " (List.replicate 60 "placeholder words fill the face")
  t "an over-full card fails its faces assertion"
    ((judge (card "" lorem)).any fun d => (d.message.splitOn "pages <= 1").length == 2)
  t "an unbreakable run past the safe margin fails text.in_area"
    ((judge (card "" ("W" ++ "".pushn 'm' 60))).any fun d =>
      (d.message.splitOn "text.in_area").length == 2 &&
      (d.message.splitOn "right margin").length == 2)
  t "tiny type fails the legibility floor"
    ((judge (card "" "{\\tiny Pat Placeholder}")).any fun d =>
      (d.message.splitOn "text.xheight").length == 2)
  t "a reasonable card passes its whole contract"
    ((judge (card "" "Pat Placeholder\\\\ {\\small pat@example.org}")).isEmpty)
  -- Running furniture stands in the margin by design — LaTeX's own page
  -- styles put it there — and the furniture pass reserves its band by
  -- construction, so the area judge exempts the lines it marks: the ink
  -- the document flows is still held to the frame (the card tests above),
  -- and furniture glyphs still feed the legibility floor.
  t "a running head does not fail text.in_area"
    ((judge ("\\runninghead{Pat Placeholder \\hfill \\pagenumber}\n" ++
      "\\assert{ text.in_area }\n" ++
      "\\begin{document}\nbody text\n\\end{document}")).isEmpty)
  t "furniture glyphs still feed the legibility floor"
    ((judge ("\\runninghead{{\\tiny Pat}}\n\\assert{ text.xheight >= 1.5mm }\n" ++
      "\\begin{document}\nbody\n\\end{document}")).any fun d =>
      (d.message.splitOn "text.xheight").length == 2)
  -- The card's base size resolves through the same PageSpec path every
  -- class uses: declared \page{fontsize} first, then the class option,
  -- then the shared 10pt base — never a card-private constant.
  t "card takes the shared base size" (cDoc.page.fontSize == Ir.baseFontSize)
  t "a card class option sets the base size through the shared path"
    ((elabStr (card "[12pt]" "x")).1.page.fontSize == Dim.pt 12)
  -- Contrast is the colour slice's contract, reused rather than restated:
  -- the pairing warning and its declared-intent silence reach a card
  -- through the same docDiags walk as every other class.
  t "an illegible card pairing realizes through the colour contract (N0022)"
    ((noteCodes (card "" "\\textcolor{washed}{faint}"
      "\\palette{ washed = #DDDDDD }\n")).contains "N0022")
  t "declared decorative intent silences it on a card too"
    (let src := card "" "\\textcolor{washed}{faint}"
      "\\palette[decorative]{ washed = #DDDDDD }\n"
     !(warnCodes src).contains "W0315" && !(noteCodes src).contains "N0022")

/-- Printer's cut marks, wired: the `\page` keys parse into the spec, the
declared faces ship exactly the eight derived fills, off means none, and
the ink follows the registration reading. The geometry itself is theorem
country (`Layout.cutmarks_on_trim_exact`, `cutmarks_in_bleed_covers`,
`cutmarks_symmetric_mem`); the census row over trio-card judges the
shipped card. -/
def cutMarkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (page : String) (pre : String := "") : String :=
    s!"\\documentclass\{card}{pre}\\page\{ {page} }\\begin\{document}x\\end\{document}"
  let pageOf (page : String) : Ir.PageSpec := (elabStr (src page)).1.page
  t "marks = cut declares the marks" ((pageOf "marks = cut").marks == true)
  t "marks stay off undeclared" ((pageOf "bleed = 3mm").marks == false)
  t "marks = none declares the way back" ((pageOf "marks = cut, marks = none").marks == false)
  t "mark-gap and mark-thickness are declared dimensions"
    (let p := pageOf "marks = cut, mark-gap = 0.1in, mark-thickness = 1pt"
     p.markGap == Dim.inch 1 / 10 && p.markThickness == Dim.pt 1)
  t "an unknown marks value is refused by name"
    (errCodes (src "marks = frame") == ["E0323"])
  t "the defaults are the sourced tokens"
    (({} : Ir.PageSpec).markGap == Ir.cutMarkGap &&
     ({} : Ir.PageSpec).markThickness == Ir.cutMarkThickness)
  let outOf (page : String) (pre : String := "") : Layout.Out :=
    layoutOf oneFace (elabStr (src page pre)).1
  t "a declared bleed ships the eight marks on every face"
    (let out := outOf "bleed = 3mm, marks = cut"
     out.pages.size ≥ 1 && out.pages.all fun p => p.fills.size == 8)
  t "marks without a bleed to stand in ship nothing"
    ((outOf "marks = cut").pages.all fun p => p.fills.isEmpty)
  t "no marks ship undeclared"
    ((outOf "bleed = 3mm").pages.all fun p => p.fills.isEmpty)
  t "registration ink follows the document's colour model"
    (Ir.Color.registration true == Ir.Color.ofCmyk 1000 1000 1000 1000 &&
     Ir.Color.registration false == Ir.Color.black)
  t "an RGB document's marks paint plain black"
    ((outOf "bleed = 3mm, marks = cut").pages.all fun p =>
      p.fills.all fun f => f.color == Ir.Color.black)
  t "a print document's marks paint in DeviceCMYK registration"
    ((outOf "bleed = 3mm, marks = cut" "\\palette{ spot = cmyk(1, 0, 0, 0) }").pages.all
      fun p => p.fills.all fun f => f.color.cmyk == some (1000, 1000, 1000, 1000))

/-- The poster's legibility floor, judged over the shipped pages. The floor
is derived from the calibration the class already sources — beamerposter's
scale-1 normalsize at the 3.5 mrad fluent-reading bound (Legge & Bigelow
2011) gives a ~1 m reading distance — so the class default itself must
pass: a floor that rejects the package's own body size (as a 1.5 m
convention did, at 5.25 mm) states an assertion its own defaults violate.
What it exists to catch — an unscaled article body pasted on a board —
still fails. -/
def posterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let poster (pre body : String) : String :=
    s!"\\documentclass\{poster}\n{pre}\\begin\{document}\n\\begin\{frame}\n{body}\n\\end\{frame}\n\\end\{document}"
  let pDoc := (elabStr (poster "" "x")).1
  t "poster implies its contract: the faces bound, ink in area, the 1m floor"
    (pDoc.asserts.any (·.kind == .pages .le 1) &&
     pDoc.asserts.any (·.kind == .textInArea) &&
     pDoc.asserts.any (·.kind == .minXHeight Ir.posterXHeightFloor))
  let judge (src : String) : Array Diag :=
    let doc := (elabStr src).1
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom
    Check.all (Check.Shipped.ofOut geom oneFace out true) doc.asserts
  t "the class default body passes its own floor"
    ((judge (poster "" "Body text at beamerposter's own calibration.")).all
      fun d => (d.message.splitOn "text.xheight").length == 1)
  t "an unscaled article body pasted on the board fails the floor"
    -- 11pt, not 10: a declared 10pt equals the PageSpec default, so the
    -- class record silently wins it back — a doors quirk noted in the
    -- fontsize fold, not this contract's to fix.
    ((judge (poster "\\page{ fontsize = 11pt }\n" "An unscaled article body.")).any
      fun d => (d.message.splitOn "text.xheight").length == 2)
  -- The list indent follows the type (`listIndentFor`): frozen at the
  -- 10pt base's 15pt, an enumerate marker plus its \labelsep hung left
  -- past the print margin at the poster's base — the A0 poster's own
  -- text.in_area failure once images fit their columns. Judged through
  -- the class's shipped-ink contract, the judge the build runs.
  t "an enumerate at poster size keeps its marker inside the print margin"
    ((judge (poster "" "\\begin{enumerate}\n\\item one\n\\item two\n\\end{enumerate}")).all
      fun d => (d.message.splitOn "text.in_area").length == 1)
  -- The first line of a column paragraph fills the column: ragged glue
  -- prices looseness finitely (`Layout.raggedItems`), so the breaker can
  -- no longer dump a paragraph's whole slack on its first line — the
  -- beamerposter defect where every paragraph's first line broke at
  -- roughly half the measure while the lines below filled it. Judged over
  -- `Layout.Out` (the page-claim rule), never a raster or an IR dump.
  let colPoster :=
    "\\documentclass[final]{beamer}\n" ++
    "\\usepackage[size=custom,width=100,height=80,scale=1.2]{beamerposter}\n" ++
    "\\begin{document}\n\\begin{frame}[t]\n\\begin{columns}[t]\n" ++
    "\\begin{column}{0.3\\textwidth}\n" ++
    "Placeholder prose long enough to wrap over several lines inside the " ++
    "column so the breaker has real choices about where every line ends " ++
    "and the ragged edge stays quiet under the reading.\n" ++
    "\\end{column}\n\\begin{column}{0.3\\textwidth}\n" ++
    "Second column filler words that also wrap onto a handful of lines " ++
    "to check the same fact against a second measure, with a few extra " ++
    "words added so the wrap onto a third line is certain.\n" ++
    "\\end{column}\n\\end{columns}\n\\end{frame}\n\\end{document}"
  let cDoc := (elabStr colPoster).1
  let cLines := bodyLines (layoutOf oneFace cDoc (Layout.Geom.ofPage cDoc.page))
  let colXs := (cLines.map (·.x)).foldl (fun acc x =>
    if acc.contains x then acc else acc.push x) #[]
  t "the column fixture ships two columns of several lines each at one left edge"
    (colXs.size == 2 && colXs.all fun x => (cLines.filter (·.x == x)).size ≥ 3)
  t "every ragged column line but the last fills its measure"
    (colXs.all fun x =>
      let ls := cLines.filter (·.x == x)
      let full := ls.foldl (fun m l => max m l.setWidth) 0
      ls.pop.all fun l => l.setWidth * 10 ≥ full * 7)

/-- The picture block through layout: shapes land as fills and label runs
through one `Pic.Place` transform. The transform and bounding-box facts are
theorems (`Pic.Place.ofPage_toPage`, `Pic.Picture.box_in_bbox`); what is
checked here is the placement they license — where the box lands, that the
label centres on its anchor, that `{center}` centres the box, and that
W0335 fires when the box cannot fit the text area (the diagnostic half of
the stays-in-its-box contract). -/
def pictureLayoutChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let red : Ir.Color := { r := 200, g := 40, b := 40 }
  let pic : Ir.Pic.Picture := { shapes := #[
    .rect 0 0 (Dim.pt 20) (Dim.pt 10) red,
    .label (Dim.pt 10) (Dim.pt 5) #[.text "7"] Ir.Color.black 800 .center] }
  t "picture bbox joins its shapes"
    (pic.bbox == ((0, 0), (Dim.pt 20, Dim.pt 10)))
  let run (body : Array Ir.Block) : Layout.Out :=
    layoutOf oneFace { body := body } geom
  let out := run #[.picture pic]
  t "picture ships one page" (out.pages.size == 1)
  t "picture rect ships as one fill of its own size and colour"
    ((out.pages[0]?.bind fun p => p.fills[0]?.map fun f =>
      p.fills.size == 1 && f.x == geom.hmargin && f.y == geom.vmargin &&
      f.w == Dim.pt 20 && f.h == Dim.pt 10 && f.color == red).getD false)
  t "picture label ships its glyphs centred on the anchor"
    ((out.pages[0]?.map fun p =>
      match (p.lines.filter (!·.furniture)).toList with
      | [l] =>
        (match l.segs.toList with
         | [Layout.Seg.run _ _ _ _ glyphs _ _ _ _ _] =>
           String.ofList (glyphs.toList.map (·.2)) == "7"
         | _ => false)
        && l.x + l.setWidth / 2 == geom.hmargin + Dim.pt 10
      | _ => false).getD false)
  -- A fills-only picture is page content: the page ships.
  let bare := run #[.picture { shapes := #[.rect 0 0 (Dim.pt 5) (Dim.pt 5) red] }]
  t "a picture of fills alone still ships its page"
    ((bare.pages[0]?.map fun p => p.fills.size == 1).getD false)
  -- An outlined node ships as a page path through the same transform:
  -- the centre maps like any picture point, the paint rides unchanged.
  let circled : Ir.Pic.Picture := { shapes := #[
    .circle (Dim.pt 10) (Dim.pt 5) (Dim.pt 5) (some ({} : Ir.Pic.Stroke)) (some red)] }
  let outC := run #[.picture circled]
  t "an outlined circle ships as one page path with its paint"
    ((outC.pages[0]?.bind fun p => p.paths[0]?.map fun pa =>
      (match pa.path with
       | .circle cx cy r =>
         cx == geom.hmargin + Dim.pt 5 && cy == geom.vmargin + Dim.pt 5 && r == Dim.pt 5
       | .rect _ _ _ _ => false
       | .segs _ => false
       | .tri _ _ _ _ _ _ => false) &&
      pa.stroke == some ({} : Ir.Pic.Stroke) && pa.fill == some red).getD false)
  -- `{center}` centres the box, as it centres a paragraph's lines.
  let centered := run #[.center #[.picture pic]]
  t "a centred picture centres its box"
    ((centered.pages[0]?.bind fun p => p.fills[0]?.map fun f =>
      f.x == geom.hmargin + (geom.textWidth - Dim.pt 20) / 2).getD false)
  -- The diagnostic half of the contract: a box the text area cannot hold.
  let wide := run #[.picture { shapes :=
    #[.rect 0 0 (geom.textWidth + Dim.pt 50) (Dim.pt 10) red] }]
  t "a picture wider than the text area warns W0335"
    (wide.diags.any (·.code == "W0335"))
  t "a fitting picture does not warn W0335"
    (!out.diags.any (·.code == "W0335"))

/-- **The wobble, and the three constraints on correcting it.** TeX centres
a node on `(ht − dp)/2` of its *measured* box, so depth enters at slope one
half and a word with a descender floats up — 1.155 pt between `value` and
`inventory` in Computer Modern at 10 pt, the effect this pins the absence of.

Asserted over `Layout.Out` (the baselines two sibling labels are actually
set on) and over the exported measurement, never over an IR dump. Three
things are checked, one per constraint: the wobble is gone, a hand-written
correction stays inert, and the reason the extent-based design exists is
still visible as a named debt rather than a silent crop. -/
def labelBaselineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let run (body : Array Ir.Block) : Layout.Out :=
    layoutOf oneFace { body := body } geom
  -- Constraint one: correct the wobble. Two labels at one anchor height,
  -- one word with a descender and one without.
  let pair (a b : String) : Ir.Pic.Picture := { shapes := #[
    .label (Dim.pt 10) (Dim.pt 20) #[.text a] Ir.Color.black 1000 .center,
    .label (Dim.pt 60) (Dim.pt 20) #[.text b] Ir.Color.black 1000 .center] }
  let baselines (p : Ir.Pic.Picture) : List Dim.Sp :=
    ((run #[.picture p]).pages[0]?.map fun pg =>
      (pg.lines.filter (!·.furniture)).toList.map (·.y)).getD []
  t "two sibling labels ship two lines"
    ((baselines (pair "value" "inventory")).length == 2)
  t "a descender does not lift a label off its neighbour's baseline"
    (match baselines (pair "value" "inventory") with
     | [p, q] => p == q
     | _ => false)
  t "nor does a word of nothing but descenders"
    (match baselines (pair "WAX" "gjpqy") with
     | [p, q] => p == q
     | _ => false)
  -- Absolute, not only relative: the baseline a line actually ships on is
  -- the one `Ir.Pic.labelBaseline` predicts, mapped through the picture's
  -- own hull. The placement recomputes `box top + height` rather than
  -- calling the IR function — it must, because under `[scale=]` the height
  -- rides untransformed while a mapped point would not — so nothing at
  -- build time ties the two, and this is what does. A uniform shift of every
  -- label passes the two equalities above and fails here.
  let m := Layout.labelMetric geom oneFace
  let solo : Ir.Pic.Picture := { shapes := #[
    .label (Dim.pt 10) (Dim.pt 5) #[.text "value"] Ir.Color.black 1000 .center] }
  let hull := solo.inkBbox m
  let inkS := m #[.text "value"] 1000
  t "the shipped baseline is the one the IR predicts"
    (((run #[.picture solo]).pages[0]?.bind fun pg =>
      (pg.lines.filter (!·.furniture))[0]?.map fun l =>
        l.y == geom.vmargin
          + (hull.2.2 - Ir.Pic.labelBaseline (Dim.pt 5) .center inkS)).getD false)
  -- The same fact at the measurement, where the reason is visible: the band
  -- is the face's declared cap height and descent, so it cannot vary with
  -- the text, while the set width must and does.
  let inkV := m #[.text "value"] 1000
  let inkI := m #[.text "inventory"] 1000
  t "the declared band is one number per face, whatever the word"
    (inkV.height == inkI.height && inkV.depth == inkI.depth)
  t "the set width still follows the glyphs"
    (inkV.w != inkI.w && inkV.w > 0)
  t "so does the baseline the placement reads"
    (Ir.Pic.labelBaseline (Dim.pt 20) .center inkV
      == Ir.Pic.labelBaseline (Dim.pt 20) .center inkI)
  -- The seat that remains, as the number it is: a centred label stands
  -- (depth − height)/2 from its anchor, which is depth/2 above where a band
  -- trimmed to the alphabetic baseline would put it (css-inline-3 §6).
  -- Uniform, therefore not a wobble — a declared reference.
  let seat := Ir.Pic.labelBaseline (Dim.pt 20) .center inkV - Dim.pt 20
  t "the seat is (depth − height)/2, to within one scaled point"
    ((inkV.depth - inkV.height) / 2 <= seat
      && seat <= (inkV.depth - inkV.height) / 2 + 1)
  t "and it sits depth/2 above a cap-to-baseline band"
    (seat > -inkV.height / 2 && seat - (-inkV.height / 2) == inkV.depth / 2)
  -- Constraint two: a hand-written correction must not break. A phantom
  -- whose metrics the label already declares changes no component.
  let dominated : Ir.Pic.LabelInk :=
    { w := 0, height := inkV.height - Dim.pt 1, depth := inkV.depth - Dim.pt 1 }
  t "a phantom box the label already covers moves neither letters nor box"
    (Ir.Pic.labelInkBox 0 (Dim.pt 20) .center (inkV.join dominated)
        == Ir.Pic.labelInkBox 0 (Dim.pt 20) .center inkV
      && Ir.Pic.labelBaseline (Dim.pt 20) .center (inkV.join dominated)
        == Ir.Pic.labelBaseline (Dim.pt 20) .center inkV)
  -- And one that is not covered: it grows the band, and no further than the
  -- join — the one surviving channel, bounded rather than denied.
  let deeper : Ir.Pic.LabelInk := { w := 0, height := 0, depth := inkV.depth + Dim.pt 2 }
  let boxV := Ir.Pic.labelInkBox 0 (Dim.pt 20) .center inkV
  let boxJ := Ir.Pic.labelInkBox 0 (Dim.pt 20) .center (inkV.join deeper)
  t "a phantom deeper than the band grows it, and only to the join"
    (boxJ.1.2 <= boxV.1.2 && boxV.2.2 <= boxJ.2.2
      && (inkV.join deeper).depth == inkV.depth + Dim.pt 2
      && (inkV.join deeper).height == inkV.height)
  -- Constraint three: keep the reason the extent-based design exists. The
  -- band is the face's *declared* ink band, and a diacritic inks above it —
  -- so the box does not cover every glyph, and nothing yet says so. This is
  -- `ink_covered_or_named`'s witness: the debt is real, not hypothetical.
  let font := oneFace.body
  let capTop : Option (Int × Int) := do
    let g ← font.gid 'É'
    let (_, hi) ← font.yExtent g
    return (hi, font.capHeight)
  t "a diacritic inks above the declared cap height"
    (match capTop with
     | some (hi, cap) => cap < hi
     | none => false)
  t "and the face reserves room for it, so the bound is declared too"
    (match capTop with
     | some (hi, _) => hi <= font.ascent
     | none => false)
  t "while the descent band does cover the descenders"
    (match (do
      let g ← font.gid 'y'
      let (lo, _) ← font.yExtent g
      return lo) with
     | some lo => font.descent <= lo
     | none => false)

/-- The block half of `role_transparent_layout`, pinned executably: an
*unstyled* role ships exactly the pages its content ships unwrapped — zero
PDF bytes move. (A `\style{<role>}` gives the role declared rhythm; that
styled path is under test in styleChecks, not here.) An oracle over
`Layout.run` and `Pdf.write`, not a theorem: the collector's match resists
equation-lemma generation (see the note beside its `.role` arm), so the
fact is held here, over the shipped bytes themselves. -/
def roleLayoutChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrapped : Ir.Doc := { body := #[.role "entry"
    #[.para #[.role "muted" #[.text "quiet"], .text " words"]]] }
  let plain : Ir.Doc := { body := #[.para #[.text "quiet", .text " words"]] }
  let out1 := layoutOf oneFace wrapped geom
  let out2 := layoutOf oneFace plain geom
  t "a role ships zero PDF bytes"
    ((Pdf.write geom oneFace out1.pages).data == (Pdf.write geom oneFace out2.pages).data)
  -- The styled path: a role's declared rhythm applies where the role
  -- stands — the same shipped positions as spelling the space at the use
  -- site — so the value lives once, upstream. Judged over `Layout.Out`.
  let linesOf (src : String) : Array (String × Dim.Sp) :=
    let (d, _) := elabStr src
    (layoutOf oneFace d geom).pages.flatMap fun p =>
      p.lines.map fun l => (l.segs.foldl (fun s seg => match seg with
        | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.foldl (fun s (_, c) => s.push c) s
        | .gap _ _ => s.push ' '
        | _ => s) "", l.y)
  let doc (pre body : String) : String :=
    s!"\\documentclass\{article}\\define \\entry(a: content) \{\\a\\par}{pre}" ++
    s!"\\begin\{document}\nlead\n\n{body}\n\\end\{document}"
  let styled := linesOf (doc "\\style{entry}{ before = 24pt }" "\\entry{follow}")
  let spelled := linesOf (doc "" "\\block[before = 24pt]{follow\\par}")
  let bare := linesOf (doc "" "\\entry{follow}")
  t "a styled role's rhythm matches the space spelled at the use site"
    (styled == spelled)
  t "and moves the role's first line where the unstyled role's stood higher"
    (match styled.find? (·.1 == "follow"), bare.find? (·.1 == "follow") with
     | some (_, ys), some (_, yb) => decide (ys > yb)
     | _, _ => false)

/-- Nav medium semantics, judged over `Layout.Out` and the shipped PDF
bytes — never an IR dump. A nav is furniture, and each medium has its own
answer: the paged surface renders an unpinned nav as the document outline
(ISO 32000-2 §12.3.3), a pinned nav (viewport furniture) as nothing, and
the markdown twin drops both — exactly as `.note` is not handout content.
Unwrapped, a menu once printed its links as body text in the PDF and as
`[One](#one)` lines in the twin: the leak that forced backend wrappers
around every navigation landmark. Invented content. -/
def navLayoutChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src :=
    "\\documentclass{article}\\begin{document}\n" ++
    "\\begin{nav}\\href{#one-head}{One} \\href{#two-head}{Two} " ++
    "\\href{https://example.org}{Out} \\href{#nowhere}{Lost}\\end{nav}\n\n" ++
    "\\section*{One Head}\nfirst body\n\n\\pagebreak\n\n" ++
    "\\section*{Two Head}\nsecond body\n\n" ++
    "\\begin{nav}[label = Up, pin = bottom right]\\href{#top}{Up}\\end{nav}\n" ++
    "\\end{document}"
  let (doc, ds) := elabStr src
  t "nav layout source clean" (ds.all (·.severity == .note))
  let out := layoutOf oneFace doc geom
  let ink := String.intercalate " " (out.pages.toList.map fun p =>
    String.intercalate " " (p.lines.toList.map (lineText ·)))
  t "an unwrapped menu nav ships no body ink"
    (!hasStr ink "One Two" && !hasStr ink "Out" && !hasStr ink "Lost")
  t "a pinned nav ships no body ink either" (!hasStr ink "Up")
  t "the content around the navs still ships"
    (hasStr ink "first body" && hasStr ink "second body")
  t "the outline holds one entry per menu link, in order"
    (out.outline.map (·.title) == #["One", "Two", "Out", "Lost"])
  t "in-document targets resolve to the pages their headings land on"
    ((out.outline.find? (·.title == "One")).map (·.page) == some (some 0) &&
     (out.outline.find? (·.title == "Two")).map (·.page) == some (some 1))
  t "an external target rides as its URL"
    ((out.outline.find? (·.title == "Out")).map (·.url) ==
      some (some "https://example.org"))
  t "an unresolved target is a bare entry"
    ((out.outline.find? (·.title == "Lost")).map (fun e => e.page.isNone && e.url.isNone) ==
      some true)
  -- The emission itself, on the shipped bytes: the outline objects and the
  -- catalog's reference; a document with no nav ships neither, so an
  -- outline-free file is unchanged.
  let pdf := pdfText (Pdf.write geom oneFace out.pages {} {} out.outline)
  t "the PDF carries the outline"
    (bytesContain pdf "/Outlines" && bytesContain pdf "/Title (One)" &&
     bytesContain pdf "/Title (Two)" && bytesContain pdf "/Dest [" &&
     bytesContain pdf "/S /URI /URI (https://example.org)")
  let (plainDoc, _) := elabStr "\\documentclass{article}\\begin{document}\nx\n\\end{document}"
  let plainOut := layoutOf oneFace plainDoc geom
  t "no nav, no outline, nothing emitted"
    (plainOut.outline.isEmpty &&
      !bytesContain (pdfText (Pdf.write geom oneFace plainOut.pages {} {} plainOut.outline))
        "/Outlines")
  t "the xref survives the outline objects"
    (match checkXref (Pdf.write geom oneFace out.pages {} {} out.outline) with
     | .ok n => n > 0
     | .error _ => false)
  -- The markdown twin: both navs drop whole; the sections stay.
  let md := MarkdownDoc.emit doc
  t "the twin drops both navs and keeps the sections"
    (!hasStr md "](#one-head)" && !hasStr md "](#top)" &&
      hasStr md "One Head" && hasStr md "second body")


/-- A LaTeX class zeroes `\parskip`; its headings keep their own rhythm
(`Ir.heading_space_above_ge_below`): more space above than below, neither
zero. The regression this pins: heading defaults derived from the peer gap
collapsed to nothing under a class-declared `parskip = 0pt`, and the
heading hugged the paragraph above it. -/
def headingRhythmChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let (d, _) := elabStr ("\\documentclass{scrartcl}\n\\begin{document}\n" ++
    "Opening line.\n\n\\section*{Alpha}\n\nClosing line.\n\\end{document}")
  t "premise: the class declared a zero parskip"
    ((d.page.parskip.map (·.width.sp)) == some 0)
  let out := layoutOf oneFace d
  let c := censusOf #[] out
  let yOf (s : String) : Option Dim.Sp := lineYOf c 0 s
  match yOf "Opening", yOf "Alpha", yOf "Closing" with
  | some yo, some yh, some yc =>
    let leading := Ir.leadingFor (Layout.Geom.ofPage d.page).fontSize
    -- Two interlines plus the two default tokens (a unit above, a half
    -- below), within a point of slack: without the tokens the same page
    -- carries interlines alone, ~12pt less.
    t "the heading's own rhythm stands: a full unit above plus a half below"
      (yc - yo ≥ 2 * leading
        + (Ir.headingBeforeDefault (Layout.Geom.ofPage d.page).fontSize).width.sp
        + (Ir.headingAfterDefault (Layout.Geom.ofPage d.page).fontSize).width.sp
        - Dim.pt 1)
    t "more space above the heading than below it"
      (yh - yo > yc - yh)
  | _, _, _ => failures ref "heading rhythm: probe lines missing from the page"

/-- A title is not a paragraph: its ragged display lines balance and never
strand one word on a line (the finite-stretch ragged setting plus the
minimum-last-line parfill, `Layout.displayItems`). Greedy ragged packing
sets everything-but-the-last-word on line one here and strands
"Functions".

The second half is the shape the *author* declared, not the one the breaker
prefers: a `\\` in a title is a decision about where a line ends, and a
declared segment too wide for the measure loses it — the breaker finds a
legal break inside the segment and the remainder returns to the flush-left
margin, which reads as a broken indent. W0005 has nothing to say (no line
is overfull), so the loss went unnamed; these rows read the count off
`Layout.Out` and the naming off the run's own diagnostics, with both floors
pinned — a break that holds is silent, and a title declaring no break has
no shape to lose. -/
def titleBreakChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let (d, _) := elabStr ("\\page{ width = 480pt, hmargin = 30pt, height = 500pt }\n" ++
    "\\title{Alpha Beta Gamma Epsilon Omega Sigma Zeta Functions}\n" ++
    "\\begin{document}\n\\maketitle\nBody.\n\\end{document}")
  let c := censusOf #[] (layoutOf oneFace d)
  t "the title wraps to two lines"
    ((lineYOf c 0 "Alpha").isSome && (lineYOf c 0 "Functions").isSome &&
      lineYOf c 0 "Alpha" != lineYOf c 0 "Functions")
  t "the break balances: no two-word first line under a full second"
    (((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Alpha").map
      fun l => hasStr l.text "Gamma").getD false)
  t "the break balances: no one-word last line"
    (((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Functions").map
      fun l => hasStr l.text "Zeta").getD false)
  -- A break the author declared is a decision about shape, and a segment
  -- that does not fit the measure loses it: the breaker finds a legal
  -- break inside the declared line and the remainder returns to the
  -- flush-left margin, which reads as a broken indent. The page shows it,
  -- so the page is what says so — and W0005 correctly does not fire,
  -- because no line is overfull.
  let narrow := "\\page{ width = 260pt, hmargin = 30pt, height = 500pt }\n"
  let declared (title : String) : Ir.Doc :=
    (elabStr (narrow ++ s!"\\title\{{title}}\n" ++
      "\\begin{document}\n\\maketitle\nBody.\n\\end{document}")).1
  let lost := declared "Coordinating Placeholder Schedules\\\\\\quad A Second Declared Line"
  let lostOut := layoutOf oneFace lost
  let lostC := censusOf #[] lostOut
  let titleWords := ["Coordinating", "Placeholder", "Schedules", "Second", "Declared", "Line"]
  let titleLines (c : Array CensusPage) : Nat :=
    (c[0]?.map fun p =>
      (p.lines.filter fun l => titleWords.any (hasStr l.text ·)).size).getD 0
  t "a declared two-line title that does not fit ships more than two lines"
    (decide (titleLines lostC > 2))
  t "a declared break destroyed by re-flow is named"
    (lostOut.diags.any (·.code == "W0386"))
  t "the re-flow is not an overfull line, so W0005 stays silent"
    (!lostOut.diags.any (·.code == "W0005"))
  t "the loss is named once for the paragraph that lost it"
    ((lostOut.diags.filter (·.code == "W0386")).size == 1)
  -- Two floors the account must not cross: a declared break that holds is
  -- silent, and a title that declared no break has no shape to lose.
  let keptOut := layoutOf oneFace (declared "Short Title\\\\Second Line")
  t "a declared break that holds is silent"
    (!keptOut.diags.any (·.code == "W0386"))
  t "a title declaring no break never reports one"
    (!(layoutOf oneFace
      (declared "Coordinating Placeholder Schedules Across Several Regions")).diags.any
        (·.code == "W0386"))

/-- xcolor's `\color{n}` at the flow's top level is the document's ink:
the declared body colour routes through the palette's one resolving site
(`fg`) and reaches every uncoloured shipped run — never silently pure
black. The regression this pins: a near-black body declared this way
shipped as #000000. -/
def bodyColorChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let (d, _) := elabStr ("\\palette{ charcoal = #18181B }\n\\begin{document}\n" ++
    "\\color{charcoal}\nBody words here.\n\\end{document}")
  let out := layoutOf oneFace d
  let charcoal : Ir.Color := { r := 0x18, g := 0x18, b := 0x1B }
  t "the declared body colour reaches the shipped runs"
    ((out.pages.flatMap (·.lines)).any fun l => l.segs.any fun s => match s with
      | .run _ c _ _ glyphs _ _ _ _ _ => c == charcoal && !glyphs.isEmpty
      | _ => false)
  t "no body run stayed silently pure black"
    ((bodyLines out).all fun l => l.segs.all fun s => match s with
      | .run _ c _ _ glyphs _ _ _ _ _ => glyphs.isEmpty || c != Ir.Color.black
      | _ => true)

/-- The page-1 fix, judged on shipped pages, never on the IR dump: the
mark is a raised smaller run in its sentence's line; the note lands at
the foot of the mark's own page — above `bodyBottom`, non-furniture,
under its rule — and the page's vertical distribution never moves it. A
line whose note does not fit spills with it (the sweep), and a note
taller than the text block overruns, named (W0372). -/
def footnoteLayoutChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let hasMarkRun (geom : Layout.Geom) (l : Layout.LineOut) : Bool :=
    l.segs.any fun s => match s with
      | .run _ _ _ _ _ sz _ raise _ _ => raise > 0 && sz > 0 && sz < geom.fontSize
      | _ => false
  let src := dvDoc "" "A first sentence\\footnote{a note body} continues here."
  let (doc, _) := elabStr src
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc
  let notesOf (out : Layout.Out) : Array Layout.LineOut :=
    out.pages.flatMap (·.lines.filter (·.note))
  let flowOf (out : Layout.Out) : Array Layout.LineOut :=
    out.pages.flatMap (·.lines.filter (fun l => !l.note && !l.furniture))
  t "footnote: one page" (out.pages.size == 1)
  t "footnote: note-flagged lines ship" (!(notesOf out).isEmpty)
  t "footnote: the mark is a raised smaller run in the flow"
    ((flowOf out).any (hasMarkRun geom))
  t "footnote: the note stands below every flow line, above bodyBottom"
    ((notesOf out).all fun n => n.y ≤ geom.bodyBottom &&
      (flowOf out).all fun b => b.y < n.y)
  t "footnote: the rule ships with the notes"
    ((notesOf out).any fun l => l.segs.any fun s => s matches .rule _ _ _ _)
  t "footnote: notes are body ink, never furniture"
    ((notesOf out).all fun l => !l.furniture)
  -- The mark's page carries its note: on a multi-page article the note
  -- stands at the foot of page 1, and nothing note-flagged leaks onward.
  let filler := String.intercalate " " (List.replicate 40 "wandering syllables")
  let src2 := dvDoc "" ("Opening claim\\footnote{the note under discussion} here.\n\n" ++
    String.intercalate "\n\n" (List.replicate 24 filler))
  let (doc2, _) := elabStr src2
  let out2 := layoutOf oneFace doc2
  t "footnote: the article spans pages" (out2.pages.size ≥ 2)
  t "footnote: the note ships on page 1, its mark's page"
    (((out2.pages[0]?.map fun p => p.lines.any (·.note)).getD false) &&
      (out2.pages.toList.drop 1).all fun p => p.lines.all (!·.note))
  -- The sweep: wherever the mark's line falls as filler grows — page
  -- middle, page boundary (the spill), fresh page — mark and note share
  -- one page index, and exactly one page carries the note.
  let mut sweepOk := true
  for k in [0:18] do
    let src3 := dvDoc "" (String.intercalate "\n\n" (List.replicate k filler) ++
      "\n\nA measured claim\\footnote{its supporting note} stands here.")
    let (doc3, _) := elabStr src3
    let out3 := layoutOf oneFace doc3
    let geom3 := Layout.Geom.ofPage doc3.page
    let notePages := (List.range out3.pages.size).filter fun i =>
      ((out3.pages[i]?.map fun p => p.lines.any (·.note)).getD false)
    let markPages := (List.range out3.pages.size).filter fun i =>
      ((out3.pages[i]?.map fun p =>
        p.lines.any fun l => !l.note && !l.furniture && hasMarkRun geom3 l).getD false)
    unless notePages.length == 1 && markPages == notePages do
      sweepOk := false
  t "footnote: mark and note share one page at every fill depth" sweepOk
  -- The frame foot: the same flush lands a deck's note at the bottom of
  -- its frame's page while the centred body stays above it.
  let dsrc := deck169Frame "Frame words\\footnote{a frame-foot note} here."
  let (ddoc, _) := elabStr dsrc
  let dgeom := Layout.Geom.ofPage ddoc.page
  let dout := layoutOf oneFace ddoc
  t "footnote: a frame's note lands at the frame foot"
    (!(notesOf dout).isEmpty &&
      (notesOf dout).all fun n => n.y ≤ dgeom.bodyBottom &&
        (flowOf dout).all fun b => b.y < n.y)
  -- W0372: a note taller than the text block overruns, named; an
  -- ordinary note stays silent.
  let (bigDoc, _) := elabStr (dvDoc
    "\\page{ width = 120pt, height = 150pt, margin = 20pt }\n"
    ("x\\footnote{" ++ String.intercalate " " (List.replicate 60 "wow") ++ "}"))
  t "footnote: a note taller than the text block fires W0372"
    ((layoutOf oneFace bigDoc).diags.any (·.code == "W0372"))
  t "footnote: an ordinary note stays silent on W0372"
    (out.diags.all (·.code != "W0372") && (dvE src).all (·.code != "W0372"))
  -- The declared token: on a full page the fit floor is the note block
  -- plus the footins gap, so a larger \tokens{ footins } presses the last
  -- flow line higher above the notes (the notes themselves are anchored
  -- at bodyBottom and never move).
  let gapOf (pre : String) : Option Dim.Sp := Id.run do
    let (d, _) := elabStr (dvDoc pre
      ("Top claim\\footnote{gap probe} anchor.\n\n" ++
        String.intercalate "\n\n" (List.replicate 24 filler)))
    let o := layoutOf oneFace d
    let some p0 := o.pages[0]? | return none
    let flows := p0.lines.filter (fun l => !l.note && !l.furniture)
    let notes := p0.lines.filter (·.note)
    let some top := (notes.map (·.y)).min? | return none
    let some bot := (flows.map (·.y)).max? | return none
    return some (top - bot)
  t "footnote: the footins token declares the body-to-note gap"
    (match gapOf "", gapOf "\\tokens{ footins = 60pt }\n" with
     | some g1, some g2 => g2 > g1
     | _, _ => false)

/-! ## Leaf attribution (M7-18a)

The invariant: for every page of `Layout.run … doc` and every line `l` on
it, `¬ l.furniture ∧ l.segs` carries a glyph run `→ l.leaf = some k` with
`k < (Struct.leaves (Struct.ofDoc (Layout.pdfView doc))).size`, `k` the
first leaf of the block whose text the line sets (a footnote's lines name
the note's first leaf), and the ink of every leaf the block owns stands, in
preorder, inside the ink its lines paint — gaps read as spaces, a line-end
hyphen joined away, the no-break space and soft hyphen outside the measure
(`Obligations.inkChars`) — with equality where the block carries no
generated ink. Generated ink the tree does not census (the abstract
heading, the headline band) is `none`; decoration of a block (a section
number, a list marker, a caption prefix, a bibliography marker) rides the
block's leaf. The owed statements are `lines_attributed_covers` and
`lines_attributed_text` (Obligations.lean); these rows are their executable
witness over the corpus, and the exceptions are enumerated, never a
wildcard:
- `.formula` leaves: the leaf is the source, the page paints the rendering
  (M7-24 owns the run channel);
- `.picture` leaves: census empty by `Struct`'s named gap (`image-alt-policy`);
  the picture's label lines carry its leaf;
- `.aside`, `.nav`, `.artifact` leaves: no ink on the PDF path (a speaker
  note, the outline, furniture the furniture pass lays and flags);
- an icon's leaf is its text alternative, its ink a glyph (M7-22a);
- a numbered verbatim block interleaves generated numbers with its one leaf;
- a standout frame's title has leaves and no line. -/

/-- A leaf of the projected tree with its ancestors' kinds, root first,
and whether it stands in the first paragraph of a list item (the one
whose first line carries the marker). -/
structure LeafRow where
  id : Nat
  leaf : Struct.Leaf
  path : List Struct.Kind
  marked : Bool

mutual

def leafRowsList (path : List Struct.Kind) (first inMarked : Bool) (acc : Array LeafRow) :
    List Struct.Node → Array LeafRow
  | [] => acc
  | n :: rest => leafRowsList path false inMarked (leafRowsOne path first inMarked acc n) rest

def leafRowsOne (path : List Struct.Kind) (first inMarked : Bool) (acc : Array LeafRow) :
    Struct.Node → Array LeafRow
  | .leaf id l => acc.push { id := id, leaf := l, path := path.reverse, marked := inMarked }
  | .node k kids =>
    leafRowsList (k :: path) (k == .body) (inMarked || (first && k == .paragraph)) acc
      kids.toList

end

def leafRows (t : Struct.Tree) : Array LeafRow :=
  leafRowsList [] false false #[] t.children.toList

/-- The ink the comparison reads: `Obligations.inkChars`'s exclusions plus
every fixed-space character (a kern, no glyph) and the hyphen — an
this block-level census joins a line-end hyphen away whatever its origin
(the run channel names the breaker's `.hyphen` apart; `leafInk` below
keeps the authored one) — case-folded, since a declared case transform
repaints a leaf's letters in another case. -/
def attrInk (s : String) : Array Char :=
  (s.toList.toArray.filter fun c =>
    !(c.isWhitespace || c == '\u00a0' || c == '\u00ad' || c == '-'
      || (Layout.fixedSpace c).isSome)).map Char.toLower

/-- The glyph text of one line for the attribution census: a raised run is
skipped — a footnote mark (generated ink) or a math script (a formula group
is compared by containment only). -/
def attrLineText (l : Layout.LineOut) : String :=
  l.segs.foldl (fun s seg => match seg with
    | .run _ _ _ _ glyphs _ _ raise _ _ =>
      if raise != 0 then s else glyphs.foldl (fun s (_, c) => s.push c) s
    | .gap _ _ => s.push ' '
    | _ => s) ""

def hasGlyphRun (l : Layout.LineOut) : Bool :=
  l.segs.any fun s => match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ => !glyphs.isEmpty
    | _ => false

/-- The text of a block's lines, in page order: gaps as spaces, a line-end
hyphen joined away. -/
def joinAttributed (ls : Array Layout.LineOut) : String :=
  ls.foldl (fun acc l =>
    let t := attrLineText l
    if acc.isEmpty then t
    else if acc.endsWith "-" then (acc.dropEnd 1).toString ++ t
    else acc ++ " " ++ t) ""

/-- The first index at or past `start` where `needle` occurs in `hay`. -/
def findFrom (hay needle : Array Char) (start : Nat) : Option Nat := Id.run do
  if needle.isEmpty then return some start
  if hay.size < needle.size then return none
  for i in [start:hay.size - needle.size + 1] do
    let mut ok := true
    for j in [0:needle.size] do
      if hay[i + j]! != needle[j]! then
        ok := false
        break
    if ok then return some i
  return none

/-- The kinds that own set text: the nearest of these above a leaf is the
block a line attributes to. -/
def ownerKind : Struct.Kind → Bool
  | .paragraph | .heading _ | .title | .cell | .caption | .code | .bibEntry
  | .artifact | .note | .formula | .label => true
  | .document | .section | .list _ | .item | .body | .table | .row | .figure
  | .quote | .aside | .nav | .link _ | .span _ | .reference _ => false

def ownerOf (r : LeafRow) : Option Struct.Kind := (r.path.filter ownerKind).getLast?

/-- A leaf the PDF path deliberately ships no text for, by kind. -/
def unshippedKind (r : LeafRow) : Bool :=
  r.path.any (fun k => k matches .aside | .nav | .artifact | .formula)
    || (r.leaf matches .picture | .image _ _ | .linebreak)

def leafAttributionChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDb.scanRoots [testFonts]
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc0, _) ← elabFixture n src
    let doc := Layout.pdfView doc0
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let out := layoutOf fs doc (Layout.Geom.ofPage doc.page) (some pats)
    let tree := Struct.ofDoc doc
    let rows := leafRows tree
    let size := rows.size
    -- the generated lines the tree does not census, by their text
    let generated : Array String := #[doc.info.locale.abstract] ++
      (match doc.headline with
        | some hl => #[Ir.plainText hl.title, Ir.plainText hl.author, Ir.plainText hl.institute]
        | none => #[])
    -- leaves whose text the page paints otherwise, from the IR
    let iconAlts := Ir.foldBlocks (fun out _ => out) (fun out x => match x with
      | .icon _ label => out.push label
      | _ => out) (#[] : Array String) doc.body
    let numberedCode := Ir.foldBlocks (fun out b => match b with
      | .verbatim _ s spec => if spec.numbers then out.push s else out
      | _ => out) (fun out _ => out) (#[] : Array String) doc.body
    let standoutTitles := Ir.foldBlocks (fun out b => match b with
      | .frame title true _ _ _ => out.push (Ir.plainText title)
      | _ => out) (fun out _ => out) (#[] : Array String) doc.body
    let excluded (r : LeafRow) : Bool :=
      unshippedKind r || (match r.leaf with
        | .text s => iconAlts.contains s || numberedCode.contains s || standoutTitles.contains s
        | _ => false)
    -- a glyph no face covers is dropped and named (E0405): only covered
    -- characters are compared
    let covered (c : Char) : Bool := fs.fonts.any fun f => (f.gid c).isSome
    let lines := allLines out
    let body := lines.filter fun l => !l.furniture && hasGlyphRun l
    -- 1. every non-furniture glyph line names a leaf below the array's size
    let mut noneLines : Array String := #[]
    for l in body do
      match l.leaf with
      | some k => t s!"leaf {n}: index {k} is below {size}" (k < size)
      | none =>
        let txt := attrInk (lineText l)
        unless generated.any (fun g => attrInk g == txt) do
          noneLines := noneLines.push (lineText l)
    t s!"leaf {n}: every body line names a leaf ({noneLines.toList.take 3})" noneLines.isEmpty
    -- 5. furniture never names a leaf; a note line names a note leaf
    t s!"leaf {n}: furniture lines carry none" (lines.all fun l => !l.furniture || l.leaf.isNone)
    t s!"leaf {n}: note lines name a note leaf" (body.all fun l => !l.note ||
      (match l.leaf with
        | some k => (rows[k]?.map fun r => r.path.contains .note).getD false
        | none => false))
    -- 2. the ink of every leaf stands, in order, inside its block's lines
    let named := (body.filterMap (·.leaf)).qsort (· < ·) |>.foldl
      (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
    let underNote (k : Nat) : Bool := (rows[k]?.map fun r => r.path.contains .note).getD false
    let ownerGroup (r : LeafRow) : Option Nat :=
      (named.filter fun k => k ≤ r.id && underNote k == r.path.contains .note).back?
    let mut mismatch : Option String := none
    let mut exactFail : Option String := none
    let mut uncovered : Array String := #[]
    for k in named do
      -- the block's lines per page: a stepped frame sets its blocks once per
      -- step page, a flow paragraph may split across two pages
      let parts := out.pages.filterMap fun p =>
        let ls := p.lines.filter fun l => !l.furniture && hasGlyphRun l && l.leaf == some k
        if ls.isEmpty then none else some (attrInk (joinAttributed ls))
      let actual := parts.flatten
      let owned := rows.filter fun r => ownerGroup r == some k
      let mine := owned.filter (!excluded ·)
      let mut pos := 0
      let mut expected : Array Char := #[]
      for r in mine do
        let ink := (attrInk r.leaf.census).filter covered
        expected := expected ++ ink
        match findFrom actual ink pos with
        | some i => pos := i + ink.size
        | none =>
          if mismatch.isNone then
            mismatch := some s!"{n} leaf {r.id} in group {k}: {r.leaf.census.quote} not in \
{(String.ofList actual.toList).quote}"
      -- exact where the block carries no generated ink: a plain paragraph
      -- (not the marker-bearing first paragraph of an item), a cell, a title,
      -- none of its leaves excluded above
      let exact := owned.all fun r => !excluded r && !r.marked &&
        (match ownerOf r with
          | some .paragraph | some .cell | some .title => true
          | _ => false)
      let repeated := parts.all (· == expected)
      if exact && !mine.isEmpty && expected != actual && !repeated && exactFail.isNone then
        exactFail := some s!"{n} group {k}: expected {(String.ofList expected.toList).quote} \
got {(String.ofList actual.toList).quote}"
    t s!"leaf {n}: every leaf's ink stands in its block's lines ({mismatch.getD ""})"
      mismatch.isNone
    t s!"leaf {n}: a plain block's lines are exactly its leaves ({exactFail.getD ""})"
      exactFail.isNone
    -- 3. every inked leaf is attributed or an enumerated exception
    for r in rows do
      unless excluded r || (attrInk r.leaf.census).isEmpty || (ownerGroup r).isSome do
        uncovered := uncovered.push s!"{r.id}:{r.leaf.census.quote}"
    t s!"leaf {n}: every inked leaf is attributed ({uncovered.toList.take 3})" uncovered.isEmpty
  -- 6. the indices, concretely: [heading, paragraph with a footnote] numbers
  -- heading 0, paragraph text 1, note body 2, continuation 3 — the heading's
  -- line names 0, the paragraph's 1, the note's 2.
  let (sdoc, _) := elabStr (dvDoc ""
    "\\section{Head}\n\nText\\footnote{note body} more words here.")
  let sout := layoutOf oneFace sdoc
  let slines := (allLines sout).filter fun l => !l.furniture && hasGlyphRun l
  let leafOf (needle : String) : Option Nat :=
    (slines.find? fun l => hasStr (lineText l) needle).bind (·.leaf)
  t "leaf synthetic: heading names leaf 0" (leafOf "Head" == some 0)
  t "leaf synthetic: paragraph names leaf 1" (leafOf "Text" == some 1)
  t "leaf synthetic: note names leaf 2" (leafOf "note body" == some 2)
  t "leaf synthetic: the tree has four leaves"
    ((Struct.ofDoc (Layout.pdfView sdoc)).leaves.size == 4)

/-! ## Inline attribution (M7-18b)

The invariant: every glyph run on a non-furniture line carries an
`Attribution` other than `.unattributed` unless the site names why (the
abstract heading and the headline band, 18a's `none` lines); the runs
attributed `.leaf k`, concatenated in page order with word gaps as spaces
and `.hyphen` runs dropped, equal `leaves[k].census` exactly (ink-normalised:
whitespace and the no-break/fixed spaces are glyphless boxes, case folded
for a declared case transform, uncovered characters dropped and named by
E0405); `.block k` names generated ink of the block opening at `k`;
`.label` runs are the marker line's and stand before its text; `.noteMark
n` runs are exactly the marks of the footnotes numbered `n`
(`Ir.footnotesOf`); a `gap _ true` stands only between two runs of one
line, and a plain paragraph's word gaps plus its glue breaks are its
census spaces. The theorem behind the walk is `flatten_attr_covers`
(Layout.lean: a counting walk never emits `.unattributed`); these rows are
the executable census over the corpus. Exclusions, each a sentence:
- `.formula` leaves: the leaf is the source, the page paints the rendering
  (M7-24 owns the run channel);
- an icon's leaf is its text alternative, its run a glyph (M7-22a);
- a verbatim block, a listing caption and a bibliography entry are one
  flat leaf each (`Struct`'s shape): their runs are `.block k`, never
  `.leaf`;
- `.aside`, `.nav`, `.artifact`, `.picture`, `.image`, `.linebreak`
  leaves ship no run. -/

/-- A run's attribution, `none` for any other segment. -/
def segAttr : Layout.Seg → Option Layout.Attribution
  | .run _ _ _ _ _ _ _ _ _ a => some a
  | _ => none

def segGlyphText : Layout.Seg → String
  | .run _ _ _ _ glyphs _ _ _ _ _ => String.ofList (glyphs.toList.map (·.2))
  | _ => ""

def isGlyphRun : Layout.Seg → Bool
  | .run _ _ _ _ glyphs _ _ _ _ _ => !glyphs.isEmpty
  | _ => false

def isInkSeg : Layout.Seg → Bool
  | .run _ _ _ _ glyphs _ _ _ _ _ => !glyphs.isEmpty
  | .image _ _ _ => true
  | _ => false

def isWordGap : Layout.Seg → Bool
  | .gap _ word => word
  | _ => false

/-- Ink for the exact census: whitespace, the no-break space and the fixed
spaces (glyphless boxes) and the soft hyphen dropped, case folded. The
hyphen stays: the breaker's own is named `.hyphen` and dropped by the
caller, so an authored hyphen counts. -/
def leafInk (s : String) : Array Char :=
  (s.toList.toArray.filter fun c =>
    !(c.isWhitespace || c == '\u00a0' || c == '\u00ad' || (Layout.fixedSpace c).isSome)).map
    Char.toLower

/-- The text the runs attributed `.leaf k` paint on one line, `.hyphen`
runs dropped; a word gap between two of them reads as a space. -/
def leafLineText (l : Layout.LineOut) (k : Nat) : String := Id.run do
  let mut s := ""
  let mut pendingGap := false
  for seg in l.segs do
    match segAttr seg with
    | some (.leaf j) =>
      if j == k then
        if pendingGap && !s.isEmpty then s := s.push ' '
        s := s ++ segGlyphText seg
      pendingGap := false
    | some .hyphen => pendingGap := false
    | some _ => pendingGap := false
    | none => if isWordGap seg then pendingGap := true
  return s

def inlineAttributionChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDb.scanRoots [testFonts]
  let mut labelFixtures : Array String := #[]
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc0, _) ← elabFixture n src
    let doc := Layout.pdfView doc0
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let out := layoutOf fs doc (Layout.Geom.ofPage doc.page) (some pats)
    let tree := Struct.ofDoc doc
    let rows := leafRows tree
    let size := rows.size
    let covered (c : Char) : Bool := fs.fonts.any fun f => (f.gid c).isSome
    let lines := allLines out
    let body := lines.filter fun l => !l.furniture && hasGlyphRun l
    let generated : Array String := #[doc.info.locale.abstract] ++
      (match doc.headline with
        | some hl => #[Ir.plainText hl.title, Ir.plainText hl.author, Ir.plainText hl.institute]
        | none => #[])
    -- 1. no unattributed run off the furniture, except the enumerated lines
    let mut unattributed : Array String := #[]
    let mut outOfRange : Array String := #[]
    for l in body do
      let txt := attrInk (lineText l)
      let exempt := generated.any (fun g => attrInk g == txt)
      for seg in l.segs do
        if isGlyphRun seg then
          match segAttr seg with
          | some .unattributed => unless exempt do unattributed := unattributed.push (lineText l)
          | some (.leaf k) | some (.block k) =>
            unless k < size do outOfRange := outOfRange.push s!"{k} on {lineText l}"
          | _ => pure ()
    t s!"attr {n}: no unattributed run on a body line ({unattributed.toList.take 3})"
      unattributed.isEmpty
    t s!"attr {n}: every leaf and block index is below {size} ({outOfRange.toList.take 3})"
      outOfRange.isEmpty
    -- a `.leaf` run names a text leaf: images, pictures and breaks ship no run
    let leafRunIds := body.flatMap fun l => l.segs.filterMap fun seg =>
      match segAttr seg with
      | some (.leaf k) => if isGlyphRun seg then some k else none
      | _ => none
    t s!"attr {n}: a leaf run names a text leaf"
      (leafRunIds.all fun k => (rows[k]?.map fun r => r.leaf matches .text _).getD false)
    -- 2. exact census per counted text leaf
    let iconAlts := Ir.foldBlocks (fun out _ => out) (fun out x => match x with
      | .icon _ label => out.push label
      | _ => out) (#[] : Array String) doc.body
    let flatBlocks := Ir.foldBlocks (fun out b => match b with
      | .verbatim _ s spec =>
        let out := out.push s
        match spec.caption with
        | some (_, cap) => out.push (Ir.plainText cap)
        | none => out
      | _ => out) (fun out _ => out) (#[] : Array String) doc.body
    let excluded (r : LeafRow) : Bool :=
      unshippedKind r || r.path.contains .bibEntry || (match r.leaf with
        | .text s => iconAlts.contains s || flatBlocks.contains s
        | _ => false)
    let mut exactFail : Option String := none
    let mut exactLeaves := 0
    for r in rows do
      if excluded r then continue
      match r.leaf with
      | .text s =>
        let expected := (leafInk s).filter covered
        let painted := out.pages.foldl (fun acc p =>
          p.lines.foldl (fun acc l =>
            if l.furniture then acc else
            let part := leafLineText l r.id
            if part.isEmpty then acc else acc.push part) acc) (#[] : Array String)
        -- a stepped frame paints its blocks once per step page: the parts
        -- are the same text repeated; a flow paragraph's parts join
        let actual := leafInk (" ".intercalate painted.toList)
        let repeated := !painted.isEmpty && painted.all fun p => leafInk p == expected
        if !expected.isEmpty then exactLeaves := exactLeaves + 1
        if actual != expected && !repeated && exactFail.isNone then
          exactFail := some s!"leaf {r.id}: expected {(String.ofList expected.toList).quote} \
got {(String.ofList actual.toList).quote}"
      | _ => pure ()
    t s!"attr {n}: every counted leaf's runs are exactly its census \
({exactLeaves} leaves; {exactFail.getD ""})" exactFail.isNone
    -- 4. a word gap stands inside its line's ink — a run or an image on
    -- each side of it (a fill's gap may sit between: `a \hfill b` sets
    -- space, fill, space) — and two word gaps never meet: a space is one
    -- glue
    let mut badGap : Option String := none
    for l in lines do
      for i in [0:l.segs.size] do
        if isWordGap l.segs[i]! then
          let before := (l.segs.extract 0 i).any isInkSeg
          let after := (l.segs.extract (i + 1) l.segs.size).any isInkSeg
          let lone := i + 1 == l.segs.size || !isWordGap l.segs[i + 1]!
          unless before && after && lone do
            if badGap.isNone then badGap := some (lineText l)
    t s!"attr {n}: a word gap stands inside its line's ink, alone ({badGap.getD ""})"
      badGap.isNone
    -- 5. note marks are exactly the document's footnotes
    let marks := (body.flatMap fun l => l.segs.filterMap fun seg =>
      match segAttr seg with
      | some (.noteMark num) => some num
      | _ => none).qsort (· < ·) |>.foldl
        (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
    let notes := ((Ir.footnotesOf doc.body).map fun (num, _) => num.getD 0).qsort (· < ·)
      |>.foldl (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
    t s!"attr {n}: note marks are the footnotes {notes} (got {marks})" (marks == notes)
    -- 6. labels: the marker runs lead their line, and there is one marker
    -- line per list item opening with a paragraph and per numbered
    -- algorithm line
    let mut labelOff : Option String := none
    let mut labelLines := 0
    for l in body do
      let attrs := l.segs.filterMap fun seg => if isGlyphRun seg then segAttr seg else none
      let labels := attrs.filter (· matches .label)
      unless labels.isEmpty do
        labelLines := labelLines + 1
        -- every label run precedes every other run
        let firstOther := attrs.findIdx? (fun a => !(a matches .label))
        let lastLabel := attrs.size - 1 - ((attrs.reverse.findIdx? (· matches .label)).getD 0)
        match firstOther with
        | some j => if j < lastLabel && labelOff.isNone then labelOff := some (lineText l)
        | none => pure ()
    let expectedMarkers := Ir.foldBlocks (fun acc b => match b with
      | .list _ items => acc + (items.filter fun item =>
          match (item.toList.dropWhile fun blk =>
              blk matches .setPalette _ | .setTokens _).head? with
          | some (.para _) => true
          | _ => false).size
      | .algorithm numbered _ ls => if numbered then acc + ls.size else acc
      | _ => acc) (fun acc _ => acc) 0 doc.body
    -- a stepped frame repeats its lines per page, and a declared marker may
    -- be an image (no run): the count is compared only where every page is
    -- the document's one flow and every marker is the class's text
    let declaredMarker := doc.styles.entries.any fun (_, st) => st.marker.isSome
    if (out.pages.size == 1 || !(doc.body.any fun b => b matches .frame ..)) && !declaredMarker then
      t s!"attr {n}: one marker line per item and numbered line ({labelLines} vs \
{expectedMarkers})" (labelLines == expectedMarkers)
    t s!"attr {n}: label runs lead their line ({labelOff.getD ""})" labelOff.isNone
    if labelLines > 0 then labelFixtures := labelFixtures.push n
    -- 3. hyphens: a `.hyphen` run ends its line, paints a hyphen, and the
    -- word it splits reads whole in the census once the hyphen is dropped
    let mut hyphens := 0
    let mut badHyphen : Option String := none
    let census := tree.text
    for p in out.pages do
      for i in [0:p.lines.size] do
        let l := p.lines[i]!
        for j in [0:l.segs.size] do
          if segAttr l.segs[j]! == some .hyphen then
            hyphens := hyphens + 1
            let last := j + 1 == l.segs.size
            let glyph := segGlyphText l.segs[j]! == "-"
            let before := if j > 0 then segGlyphText l.segs[j - 1]! else ""
            -- the next line of the block in page order (an underline
            -- sibling is pushed between and carries no run)
            let after := match (p.lines.extract (i + 1) p.lines.size).find?
                (fun nl => !nl.furniture && hasGlyphRun nl && nl.leaf == l.leaf) with
              | some nl => (nl.segs.find? isGlyphRun).map segGlyphText |>.getD ""
              | none => ""
            let joined := before ++ after
            let whole := !before.isEmpty && !after.isEmpty && hasStr census joined
            unless last && glyph && whole do
              if badHyphen.isNone then badHyphen := some s!"{lineText l} | {joined}"
    t s!"attr {n}: a hyphen run ends its line and its word reads whole \
({hyphens} hyphens; {badHyphen.getD ""})" badHyphen.isNone
    if n == "paragraphs" then
      t "attr paragraphs: the breaker hyphenates at least once" (hyphens > 0)
      -- word gaps + glue breaks = census spaces, per plain paragraph: a
      -- break at glue consumes one space, a break at a hyphen (the
      -- breaker's or an authored one) none
      let mut arith : Option String := none
      let groups := (body.filterMap (·.leaf)).qsort (· < ·) |>.foldl
        (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
      for k in groups do
        let ls := body.filter (·.leaf == some k)
        let owned := rows.filter fun r => (match r.path.getLast? with
          | some .paragraph => true | _ => false) && k ≤ r.id &&
          (groups.filter fun g => g ≤ r.id).back? == some k
        if owned.isEmpty || ls.isEmpty then continue
        -- every space of the paragraph's text atoms is one glue (a formula's
        -- source spaces are math, not glue)
        let spaces := owned.foldl (fun acc r => match r.leaf with
          | .text s => acc + (s.toList.filter (· == ' ')).length
          | _ => acc) 0
        let wordGaps := ls.foldl (fun acc l => acc + (l.segs.filter isWordGap).size) 0
        let hyphenEnds := ls.foldl (fun acc l =>
          match l.segs.back? with
          | some seg => if segAttr seg == some .hyphen || (segGlyphText seg).endsWith "-"
              then acc + 1 else acc
          | none => acc) 0
        let glueBreaks := ls.size - 1 - hyphenEnds
        if wordGaps + glueBreaks != spaces && arith.isNone then
          arith := some s!"group {k}: {wordGaps} gaps + {glueBreaks} breaks vs {spaces} spaces"
      t s!"attr paragraphs: word gaps and glue breaks are the census spaces ({arith.getD ""})"
        arith.isNone
  t s!"attr: lists, algorithm and lists-styled carry label runs ({labelFixtures})"
    (["lists", "algorithm", "lists-styled"].all labelFixtures.contains)
  -- the indices, concretely: a link, a language span, a reference and a
  -- footnote each carry their atoms' leaves; the mark is `.noteMark`
  let (sdoc, _) := elabStr (dvDoc ""
    "\\section{Head}\n\nSee \\href{https://example.org}{the site} and \
\\foreignlanguage{french}{bonjour}\\footnote{note body} here.")
  let sout := layoutOf oneFace sdoc
  let slines := (allLines sout).filter fun l => !l.furniture && hasGlyphRun l
  let attrOf (needle : String) : Option Layout.Attribution :=
    slines.findSome? fun l => l.segs.findSome? fun seg =>
      if hasStr (segGlyphText seg) needle then segAttr seg else none
  let stree := Struct.ofDoc (Layout.pdfView sdoc)
  let leafNamed (needle : String) : Option Nat :=
    (stree.leaves.find? fun (_, l) => match l with
      | .text s => hasStr s needle
      | _ => false).map (·.1)
  t "attr synthetic: the heading's run is its leaf" (attrOf "Head" == (leafNamed "Head").map .leaf)
  t "attr synthetic: the link's run is its body's leaf"
    (attrOf "site" == (leafNamed "the site").map .leaf)
  t "attr synthetic: the language span's run is its leaf"
    (attrOf "bonjour" == (leafNamed "bonjour").map .leaf)
  t "attr synthetic: the note body's run is its leaf"
    (attrOf "body" == (leafNamed "note body").map .leaf)
  t "attr synthetic: the tail after the note resumes past the note's leaves"
    (attrOf "here" == (leafNamed " here").map .leaf)
  t "attr synthetic: the mark's digit is a note mark, in the text and leading the note"
    ((slines.filter fun l => l.segs.any fun seg =>
      segAttr seg == some (.noteMark 1) && segGlyphText seg == "1").size == 2)

/-- A declaration standing between blocks scopes every following block of
its group — size and colour like `\centering` — and never sets an empty
styled paragraph in its place. The page fact behind `decl_between_blocks_covers`:
`\footnotesize` before a tabular sizes the cells at the footnotesize step,
`\normalsize` after it returns the paragraph to the body size, and the
lines in between hold only the table's text. -/
def declBlockChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := "\\footnotesize\n\\begin{tabular}{ll}\nalpha & beta \\\\\n" ++
    "gamma & delta\n\\end{tabular}\n\\normalsize\nBody text after the table."
  let (doc, diags) := Elab.run "t" src
  let c := censusOf #[] (layoutOf oneFace doc geom)
  let small := Ir.scaleStep geom.fontSize "footnotesize"
  t "decl between blocks: the fixture elaborates clean" (diags.all (·.code.startsWith "N"))
  t "decl between blocks: the table's cells set at the footnotesize step"
    (lineSizeOf c 0 "alpha" == some small && lineSizeOf c 0 "gamma" == some small)
  t "decl between blocks: the paragraph after \\normalsize sets at the body size"
    (lineSizeOf c 0 "Body text" == some geom.fontSize)
  t "decl between blocks: no empty styled paragraph stands before the table"
    ((c[0]?.map fun p => p.lines.all fun l => !l.text.trimAscii.toString.isEmpty).getD false)
  -- The grouped spelling and the declaration spelling agree on the page.
  let grouped := "{\\footnotesize\n\\begin{tabular}{ll}\nalpha & beta \\\\\n" ++
    "gamma & delta\n\\end{tabular}}\nBody text after the table."
  let cg := censusOf #[] (layoutOf oneFace (Elab.run "t" grouped).1 geom)
  t "decl between blocks: the grouped spelling sizes the cells the same way"
    (lineSizeOf cg 0 "alpha" == some small && lineSizeOf cg 0 "Body text" == some geom.fontSize)
  -- A bare palette name between blocks colours the blocks that follow.
  let colored := "\\palette{ accent = #336699 }\n\\accent\n\\begin{itemize}\\item one\\end{itemize}"
  let cout := layoutOf oneFace (Elab.run "t" colored).1 geom
  -- The body `\palette` ships as a `setPalette` block, so the value is
  -- spelled here rather than read from the preamble palette.
  let accent : Ir.Color := { r := 51, g := 102, b := 153 }
  let itemRuns := (bodyLines cout).flatMap (·.segs.filterMap fun s =>
    match s with
    | .run _ color _ _ glyphs _ _ _ _ _ =>
      if glyphs.any (·.2 == 'o') then some color else none
    | _ => none)
  t "decl between blocks: a bare palette name colours the list after it"
    (!itemRuns.isEmpty && itemRuns.all (· == accent))
