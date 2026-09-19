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
    | .W w => items := items.push (.box (Dim.pt w) 0 Ir.Color.black none #[] (Dim.pt 10) false 0)
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
    for k in [a:b] do
      if Layout.isForced items k then
        return none
    let m := Layout.measure items a b
    total := total + Layout.lineDemerits items m target b
    if prevFlagged && Layout.isFlagged items b then
      total := total + Layout.doubleHyphenDemerits
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
    (out.pages.flatMap (·.lines), out.diags)
  let markerOf (l : Layout.LineOut) : String :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ _ _ _ glyphs _ _ _) => String.ofList (glyphs.toList.map (·.2))
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
  let (stepLines, _) := runOn ("\\documentclass{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}\\begin{itemize}\\item<1-> alpha\\item<2-> beta" ++
    "\\end{itemize}\\end{frame}\n\\end{document}")
  t "stepped items keep their markers on every page"
    (stepLines.size == 4 && (stepLines.map markerOf).all (· == "•"))
  -- Dim-not-hide dims the marker with its item: on the first handout page
  -- the second item is covered, marker included.
  let markerColor (l : Layout.LineOut) : Option Ir.Color :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ c _ _ _ _ _ _) => some c
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

  -- Small caps on a face without smcp+c2sc are synthesised UNIFORM: every
  -- letter its capital form, the whole word at one reduced size — mixed
  -- case cannot come out at two heights. (`\scshape` used to do nothing at
  -- all; then it kept capitals full-size beside scaled lowercase.)
  let scOut := layoutOf oneFace (Elab.run "t" "\\scshape aB").1 geom
  let scRuns := (scOut.pages.flatMap (·.lines)).flatMap (·.segs.filterMap fun s =>
    match s with
    | .run _ _ _ _ glyphs size _ _ => some (glyphs.map (·.2), size)
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
    ((layoutOf oneFace d geom).pages.flatMap (·.lines)).map (·.setWidth)
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
    fr.body == #[.frame #[] false .center #[.center #[.para #[.text "Questions?"]]]])
  -- Inside inline content there is no block to centre; the warning stays.
  t "centering in an argument still warns"
    (warnCodes "\\textbf{\\centering x}" == ["W0108"])

/-- `\vspace{\fill}` and `\vfill`: TeX's first-order infinite glue, whose
share of the page's leftover is what places the content. Asserted over
`Layout.Out` — the claim is about where lines land, never about an IR
dump. -/
def filChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let linesOf (src : String) : Array Layout.LineOut :=
    let (d, _) := Elab.run "t" src
    (layoutOf oneFace d geom).pages.flatMap (·.lines)
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
      #[.columns #[(some 500, #[.para #[.text "x"]])]])
  t "a bare textwidth minipage takes the whole measure"
    ((elabStr (doc "\\begin{minipage}{\\textwidth}x\\end{minipage}")).1.body ==
      #[.columns #[(some 1000, #[.para #[.text "x"]])]])
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
  let cpdf := Pdf.write geom oneFace (layoutOf oneFace cdoc geom).pages cdoc.info
  t "the pdf paints a cmyk colour in DeviceCMYK, components as declared"
    (bytesContain cpdf "0 0.83 0.76 0.07 k")
  t "the html backend converts, explicitly, to the preview"
    (((HtmlDoc.emit {} cdoc).1.splitOn
        (HtmlDoc.cssColor (Ir.Color.ofCmyk 0 830 760 70))).length ≥ 2 &&
      HtmlDoc.cssColor (Ir.Color.ofCmyk 0 830 760 70) == "#ed2839")
  -- The print boxes follow from the declared bleed: pageBoxes_nest proves
  -- TrimBox ⊆ BleedBox ⊆ MediaBox with the trim at the declared size;
  -- this pins that the written page dictionary carries all three.
  let (bdoc, bds) := elabStr
    "\\documentclass{card}\\page{ bleed = 3mm }\\begin{document}x\\end{document}"
  let bgeom := Layout.Geom.ofPage bdoc.page
  let bpdf := Pdf.write bgeom oneFace (layoutOf oneFace bdoc bgeom).pages bdoc.info
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
     let zpdf := Pdf.write zgeom oneFace (layoutOf oneFace zdoc zgeom).pages zdoc.info
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
    | .run _ _ (some _) _ _ _ ul _ => some ul
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
  let abLines := ((outOf oneFace "\\underline{ab}").pages.flatMap (·.lines))
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
          [((slot, false, false), 0), ((slot, true, false), 0),
           ((slot, false, true), 0), ((slot, true, true), 0)]).toArray
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
              [((slot, false, false), 0), ((slot, true, false), 0),
               ((slot, false, true), 1), ((slot, true, true), 1)]).toArray
          }
          let firstRunAndRule (src : String) : Dim.Sp × Dim.Sp := Id.run do
            let lines := ((outOf mixedSet src).pages.flatMap (·.lines))
            let runW := ((lines[0]?.map (·.segs)).getD #[]).filterMap fun s =>
              match s with
              | .run _ _ _ w _ _ _ _ => some w
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
  -- (above the baseline, or below half the em) or thickness (nonpositive,
  -- or over a quarter em) falls back to the convention, each independently.
  t "band: declared plausible values pass" (Font.underlineBand 2048 (-154) 102 == (-154, 102))
  t "band: zero position falls back" ((Font.underlineBand 1000 0 50).1 == -100)
  t "band: positive position falls back" ((Font.underlineBand 1000 200 50).1 == -100)
  t "band: absurdly deep position falls back" ((Font.underlineBand 1000 (-30000) 50).1 == -100)
  t "band: zero thickness falls back" ((Font.underlineBand 1000 (-50) 0).2 == 50)
  t "band: negative thickness falls back" ((Font.underlineBand 1000 (-50) (-80)).2 == 50)
  t "band: absurdly thick falls back" ((Font.underlineBand 1000 (-50) 900).2 == 50)
  t "band: one bad value keeps the other" (Font.underlineBand 1000 (-50) (-80) == (-50, 50))
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
          [((slot, false, false), 0), ((slot, true, false), 0),
           ((slot, false, true), 0), ((slot, true, true), 0)]).toArray
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
      if l.segs.any (fun s => match s with | .run .. => true | _ => false) then some l.y else none
  let pagesOf (g : Layout.Geom) (src : String) : Nat :=
    (layoutOf oneFace (Elab.run "t" src).1 g).pages.size
  let body := geom.fontSize
  let leading := Ir.leadingFor body geom.leading
  let scaled (sz : Dim.Sp) (units : Int) : Dim.Sp := units * sz / font.unitsPerEm
  -- Interline: body lines sit one leading apart, and a body line after a
  -- Huge one is one body leading below it plus what the Huge line hangs
  -- under its baseline — not a Huge leading.
  let plain := ysOf geom "a\n\nb"
  t "peers sit a leading plus parskip apart"
    (plain.size == 2 && plain[1]! - plain[0]! == leading + (geom.parskip.resolve body 0).width)
  let huge := ysOf geom "{\\Huge Title \\par}\n\nbody"
  let hugeSize := body * 2488 / 1000
  let hugeDepth := scaled hugeSize (-font.descent)
  let bodyHeight := scaled body font.capHeight
  t "a Huge title ends one paragraph, not two lines" (huge.size == 2)
  t "the line after a Huge title is spaced by TeX's rule"
    (huge.size == 2 && huge[1]! - huge[0]! ==
      max leading (hugeDepth + bodyHeight + Dim.pt 1) + (geom.parskip.resolve body 0).width)
  t "the line after a Huge title is not a Huge leading away"
    (huge.size == 2 && huge[1]! - huge[0]! < Ir.leadingFor hugeSize geom.leading)
  t "the first line hangs the title's own height below the margin"
    (huge.size == 2 && huge[0]! == geom.vmargin + max (scaled body font.ascent) (scaled hugeSize font.capHeight))
  -- Gaps: `\vspace` is the gap in place of parskip and adds to other declared
  -- glue; an element's own space (a list's topsep, a heading's before) takes
  -- the larger against what is owed, as LaTeX's `\addvspace` does.
  let vs := ysOf geom "a\n\n\\vspace{20pt}\nb"
  t "a bare vspace replaces parskip" (vs.size == 2 && vs[1]! - vs[0]! == leading + Dim.pt 20)
  let blk := ysOf geom "a\n\n\\block[before = 20pt]{b}"
  t "block before is the gap" (blk.size == 2 && blk[1]! - blk[0]! == leading + Dim.pt 20)
  let listSrc (mid : String) := "\\documentclass{article}\\style{itemize}{ before = 10pt }" ++
    "\\begin{document}a\\begin{itemize}\\item b\\end{itemize}" ++ mid ++ "c\\end{document}"
  let ls := ysOf geom (listSrc "")
  t "list topsep stands above the list" (ls.size == 3 && ls[1]! - ls[0]! == leading + Dim.pt 10)
  t "list topsep stands below the list too" (ls.size == 3 && ls[2]! - ls[1]! == leading + Dim.pt 10)
  let lv := ysOf geom (listSrc "\\vspace{7pt}")
  t "a vspace after a list adds to its topsep"
    (lv.size == 3 && lv[2]! - lv[1]! == leading + Dim.pt 17)
  let secSrc := "\\documentclass{article}\\style{itemize}{ before = 10pt }" ++
    "\\style{section}{ before = 15pt, after = 4pt }" ++
    "\\begin{document}\\begin{itemize}\\item b\\end{itemize}\\section{S}c\\end{document}"
  let sec := ysOf geom secSrc
  t "a heading after a list takes the larger space, not the sum"
    (sec.size == 3 && sec[1]! - sec[0]! ==
      max (Ir.leadingFor (Layout.sectionSize geom 1) geom.leading)
        (scaled body (-font.descent) + scaled (Layout.sectionSize geom 1) font.capHeight + Dim.pt 1)
      + Dim.pt 15)
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
  let natural := firstY + 2 * (leading + Dim.pt 20) + scaled body (-font.descent)
  let tight : Layout.Geom := { geom with pageH := natural - Dim.pt 10 + geom.vmargin }
  t "within its shrink the page holds" (pagesOf tight three == 1)
  let ys := ysOf tight three
  t "the shrunk page moves later lines up, in proportion"
    (ys.size == 3 && ys[0]! == firstY && ys[2]! < firstY + 2 * (leading + Dim.pt 20) &&
      ys[1]! - ys[0]! == leading + Dim.pt 20 - Dim.pt 5 && ys[2]! - ys[1]! == leading + Dim.pt 20 - Dim.pt 5)
  t "a shrunk page says so"
    ((layoutOf oneFace (Elab.run "t" three).1 tight).diags.any (·.code == "N0200"))
  let tooTight : Layout.Geom := { geom with pageH := natural - Dim.pt 20 + geom.vmargin }
  t "beyond its shrink the page breaks" (pagesOf tooTight three == 2)
  t "an unshrunk page says nothing"
    (!(layoutOf oneFace (Elab.run "t" three).1 geom).diags.any (·.code == "N0200"))

/-- Recovery emits the author's content, never the source's syntax. An
unknown command's leading `[...]` run is how the author addressed the
command — a parameter, not content — so no character of it reaches the
shipped page, while every `{...}` group survives, and no space the author
never wrote is fabricated after the kept text. Judged over `Layout.Out`'s
glyphs, never the IR dump: a bracketed number once shipped in front of a
URL while the suite was green. `elabInlines` terminates provably now, so
the elaborator half ("no character of an option run reaches the
elaborated inlines", over the W0341 arm) is statable as a theorem at
last; until that proof lands, this stays its shipped-page witness. -/
def recoveryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let pageText (src : String) : String :=
    let (d, _) := elabStr src
    let lines := (layoutOf oneFace d geom).pages.flatMap (·.lines)
    String.join (lines.toList.map fun l =>
      String.ofList (l.segs.toList.flatMap fun s =>
        match s with
        | .run _ _ _ _ glyphs _ _ _ => (glyphs.map (·.2)).toList
        | .gap _ => [' ']
        | _ => []))
  let has (page part : String) : Bool := (page.splitOn part).length > 1
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
  -- Consecutive runs are one parameter train; both groups are content.
  let par := pageText "\\parbox[c][2cm]{alpha}{beta}"
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

/-- Vertical distribution: beamer's frame options select the split, the
default centres (beamer user guide §8.1), and a titled frame's page-top
chrome never moves with the body. -/
def vdistChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let linesOf (src : String) : Array Layout.LineOut :=
    (layoutOf oneFace (elabStr src).1 geom).pages.flatMap (·.lines)
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
  t "[t] parses to top"
    ((elabStr (deck169Body "\\begin{frame}[t]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] false .top #[.para #[.text "x"]]])
  t "[b] parses to bottom"
    ((elabStr (deck169Body "\\begin{frame}[b]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] false .bottom #[.para #[.text "x"]]])
  t "[t,standout] keeps both"
    ((elabStr (deck169Body "\\begin{frame}[t,standout]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] true .top #[.para #[.text "x"]]])
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
     | #[.frame _ _ .golden _] => true
     | _ => false)
  t "an undeclared title page centres"
    (match (elabStr titled).1.body with
     | #[.frame _ _ _ #[.center _]] => true
     | _ => false)
  let styledSrc := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{sep = #445566}\n" ++
    "\\style{titlepage}{align = left, separator = sep}\n" ++
    "\\begin{document}\n\\title{A Deck}\\author{Pat Placeholder}\n\\maketitle\n" ++
    "\\end{document}"
  t "a left title page is ragged and carries the separator"
    (match (elabStr styledSrc).1.body with
     | #[.frame _ _ .golden inner] =>
       inner.size ≥ 2 && inner.any (fun b => match b with
         | .rule _ (some "sep") _ => true
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

/-- The running head's reserved band (`headBandFor`/`Geom.bodyTop`): with a
top margin too small to hold the head line, body ink still starts at least
`lineskip` below the head's ink bottom — `bodyTop_clears_head` is the
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
  t "body ink clears the head's ink by lineskip under a tight margin"
    (!bodyInkTops.isEmpty &&
      bodyInkTops.all fun top => headBottom + Layout.lineskip ≤ top)
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
    let (doc, _) := elabStr (deck169 "\\theme{moloch}\\title{T}\\author{A}"
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
      (l.segs.foldl (fun s seg => match seg with
        | .run _ _ _ _ glyphs _ _ _ => glyphs.foldl (fun s (_, c) => s.push c) s
        | .gap _ => s.push ' '
        | _ => s) "",
       (l.segs.findSome? fun seg => match seg with
        | .run _ color _ _ _ _ _ _ => some color
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
  let codesOf (src : String) : Array Diag := (elabStr src).2
  -- A use whose epoch declares a dark page is judged on that page.
  let dsDark := codesOf (doc
    "\\palette{ bg = #202020, dim = #333333 }\n\n\\textcolor{dim}{dim words} here.")
  t "a use inside a dark-page epoch is judged on that page"
    (dsDark.any fun d => d.code == "W0315" && hasStr d.message "#202020")
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
    (dsRedecl.any fun d => d.code == "W0315" && hasStr d.message "'q'")
  -- The resolved-design judge (W0345) is per epoch: a bad frame-title
  -- pair declared before a frame is judged for it; declared after the
  -- last frame, it styles nothing and stays silent.
  let deckDoc (mid tail : String) : String :=
    "\\documentclass{slides}\\theme{moloch}\\begin{document}\n\
\\begin{frame}{A}\none\n\\end{frame}\n\n" ++ mid ++
    "\\begin{frame}{B}\ntwo\n\\end{frame}\n\n" ++ tail ++ "\\end{document}"
  t "a bad frame-title pair declared before a frame is judged for it"
    ((codesOf (deckDoc "\\palette{ frametitlebg = #F2F2F0 }\n\n" "")).any
      (·.code == "W0345"))
  t "a bad frame-title pair declared after the last frame styles nothing"
    ((codesOf (deckDoc "" "\\palette{ frametitlebg = #F2F2F0 }\n\n")).all
      (·.code != "W0345"))

/-- Tables and floats: the too-wide diagnostic, the caption's source side,
and the rule extents on the shipped page — a rule claim is judged from
`Layout.Out`, never the IR dump. Its own function: `main`'s do block has no
elaboration budget left. -/
def tableChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrap (tab : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ tab ++ "\n\\end{document}"
  let layoutDiags (src : String) : Array Diag :=
    let doc := (elabStr src).1
    (layoutOf oneFace doc).diags
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
    (Ir.captionPrefix .figure (some 2) == some "Figure 2: " &&
     Ir.captionPrefix .table (some 1) == some "Table 1: " &&
     Ir.captionPrefix .sub (some 1) == some "(a) " &&
     Ir.captionPrefix .sub (some 2) == some "(b) " &&
     Ir.captionPrefix .figure none == none)
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
        | #[.columns #[(some w1, #[.float .sub (some 1) false _ c1]),
                       (some w2, #[.float .sub (some 2) false _ c2])]] =>
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
  -- The caption seam: nothing keeps a float and its caption on one page
  -- yet, so the break is reported (W0339, pending), never silent. The
  -- `\vspace` sweep parks the object at every position around the page
  -- bottom in 3pt steps: the seam-break window is about one leading tall,
  -- so some step lands the object on the page with the caption past it,
  -- whatever the face's metrics — and a small vspace leaves room for both.
  let tieDoc (pts : Nat) : String :=
    "\\documentclass{article}\n\\page{ size = a5 }\n\\begin{document}\n" ++
    s!"top\n\n\\vspace\{{pts}pt}\n\n\\begin\{table}\n" ++
    "\\begin{tabular}{l}\nalpha \\\\\n\\end{tabular}\n" ++
    "\\caption{Below the table}\n\\end{table}\n\\end{document}"
  t "a page break through the caption seam is named"
    ((List.range 50).any fun k =>
      (layoutDiags (tieDoc (350 + 3 * k))).any (·.code == "W0339"))
  t "a float that fits keeps its caption silently"
    (!(layoutDiags (tieDoc 12)).any (·.code == "W0339"))
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
          | .gap g => x := x + g
          | .run _ _ _ w _ _ _ _ => x := x + w
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

def hyphenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Hyphenation. Expectations are real TeX \showhyphens output with the SAME
  -- pattern set the engine embeds (luatex + hyph-en-us.tex, hyphenmins 2/3);
  -- plain lualatex is a different oracle because TeX Live maps `english` to
  -- hyphen.tex, Knuth's frozen subset. \showhyphens lists every admissible
  -- break, not one chosen rendering. Full 552-word check: scripts/hyphen-diff.lean
  let pats := Hyphen.load
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
        | .run _ _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '-')
        | .gap _ | .rule .. | .image .. => false
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
  let bPdf := Pdf.write bGeom oneFace bOut.pages
  t "bleed writes a TrimBox 3mm in from the medium corner"
    (bytesContain bPdf "/TrimBox [8.504 8.504 251.15 161.518]")
  t "bleed grows the MediaBox by twice itself"
    (bytesContain bPdf "/MediaBox [0 0 259.654 170.022]")
  -- The ink shifts with the trim box: the first glyph sits at the margin
  -- measured from the trim corner (8.504 + 14.173 pt), not the medium corner.
  t "bleed shifts the content with the trim box"
    (bytesContain bPdf "1 0 0 1 22.677 ")
  let plainGeom := Layout.Geom.ofPage cDoc.page
  let plainPdf := Pdf.write plainGeom oneFace
    (layoutOf oneFace cDoc plainGeom).pages
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
  t "an illegible card pairing earns the colour contract's W0315"
    ((warnCodes (card "" "\\textcolor{washed}{faint}"
      "\\palette{ washed = #DDDDDD }\n")).contains "W0315")
  t "declared decorative intent silences it on a card too"
    (!(warnCodes (card "" "\\textcolor{washed}{faint}"
      "\\palette[decorative]{ washed = #DDDDDD }\n")).contains "W0315")

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
    .label (Dim.pt 10) (Dim.pt 5) "7" Ir.Color.black 800] }
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
      match p.lines.toList with
      | [l] =>
        (match l.segs.toList with
         | [Layout.Seg.run _ _ _ _ glyphs _ _ _] =>
           String.ofList (glyphs.toList.map (·.2)) == "7"
         | _ => false)
        && l.x + l.setWidth / 2 == geom.hmargin + Dim.pt 10
      | _ => false).getD false)
  -- A fills-only picture is page content: the page ships.
  let bare := run #[.picture { shapes := #[.rect 0 0 (Dim.pt 5) (Dim.pt 5) red] }]
  t "a picture of fills alone still ships its page"
    ((bare.pages[0]?.map fun p => p.fills.size == 1).getD false)
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
        | .run _ _ _ _ glyphs _ _ _ => glyphs.foldl (fun s (_, c) => s.push c) s
        | .gap _ => s.push ' '
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
    String.intercalate " " (p.lines.toList.map fun l =>
      l.segs.foldl (fun s seg => match seg with
        | .run _ _ _ _ glyphs _ _ _ => glyphs.foldl (fun s (_, c) => s.push c) s
        | _ => s.push ' ') ""))
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
  let pdf := Pdf.write geom oneFace out.pages {} {} out.outline
  t "the PDF carries the outline"
    (bytesContain pdf "/Outlines" && bytesContain pdf "/Title (One)" &&
     bytesContain pdf "/Title (Two)" && bytesContain pdf "/Dest [" &&
     bytesContain pdf "/S /URI /URI (https://example.org)")
  let (plainDoc, _) := elabStr "\\documentclass{article}\\begin{document}\nx\n\\end{document}"
  let plainOut := layoutOf oneFace plainDoc geom
  t "no nav, no outline, nothing emitted"
    (plainOut.outline.isEmpty &&
      !bytesContain (Pdf.write geom oneFace plainOut.pages {} {} plainOut.outline)
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

