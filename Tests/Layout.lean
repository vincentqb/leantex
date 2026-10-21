module

public import LeanTex.Cli.FontDiscovery
public import Tests.Support

public section

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
    | .W w => items := items.push (.box (Dim.pt w) 0 Ir.Color.black none #[] (Dim.pt 10) {} {} 0 none (.leaf 0))
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

/-- Total demerits of a break sequence ending at the final forced penalty, or none when it spans a
forced break. -/
def seqCost (items : Array Layout.Item) (target : Dim.Length) (breaks : List Nat) :
    Option Int := Id.run do
  let mut prev : Nat := 0
  let mut first := true
  let mut prevFlagged := false
  let mut total : Int := 0
  for b in breaks do
    let a := if first then Layout.lineStart items 0 else Layout.lineStart items (prev + 1)
    -- `kp`'s own `a ≤ j` gate: a line whose start passes its break ships nothing.
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
def bruteBest (items : Array Layout.Item) (target : Dim.Length) : Option Int := Id.run do
  let n := items.size
  let legal := (List.range n).filter (Layout.canBreakAt items)
  let mut best : Option Int := none
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

/-- List markers reach the positioned page: enumerate order and nesting, itemize depth,
overlay-stepped items, declared markers, and depth past four. -/
def listChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (font : Font) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let runOn (src : String) : Array Layout.LineOut × Array Diag :=
    let (d, _) := Elab.run "t" src
    let out := layoutOf oneFace d geom
    (bodyLines out, out.diags)
  let markerOf (l : Layout.LineOut) : String :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ _ _ _ glyphs _ _ _ _ _ _) => String.ofList (glyphs.toList.map (·.2.1))
    | _ => ""
  t "enum labels match the class defaults"
    (ListMark.enumLabel 1 1 == "1." && ListMark.enumLabel 2 1 == "(a)" &&
     ListMark.enumLabel 3 4 == "iv." && ListMark.enumLabel 4 2 == "B." &&
     ListMark.enumLabel 1 12 == "12." && ListMark.enumLabel 2 26 == "(z)")
  t "alph past its range degrades to arabic, distinctly"
    (ListMark.enumLabel 2 27 == "(27)")
  -- Roman injectivity is left to this round trip over LaTeX's counter range.
  t "roman round-trips over the counter range"
    ((List.range 32767).all fun k =>
      ListMark.romanVal (ListMark.romanN (k + 1)).toList == k + 1)
  let (enumLines, _) := runOn
    "\\begin{enumerate}\\item alpha\\item beta\\item gamma\\end{enumerate}"
  t "enumerate numbers its items in order"
    (enumLines.map markerOf == #["1.", "2.", "3."])
  let (nestLines, _) := runOn ("\\begin{enumerate}\\item one\\item two" ++
    "\\begin{enumerate}\\item inner\\item inner too\\end{enumerate}" ++
    "\\item three\\end{enumerate}")
  t "nested enumerate resets and the outer resumes"
    (nestLines.map markerOf == #["1.", "2.", "(a)", "(b)", "3."])
  -- Level 3's glyph follows the face, so only distinctness is asserted.
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
  let (stepLines, _) := runOn ("\\documentclass{beamer}\n\\usetheme{default}\n" ++
    "\\setbeamercovered{transparent=38}\n\\begin{document}\n" ++
    "\\begin{frame}\\begin{itemize}\\item<1-> alpha\\item<2-> beta" ++
    "\\end{itemize}\\end{frame}\n\\end{document}")
  t "stepped items keep their markers on every page"
    (stepLines.size == 4 && (stepLines.map markerOf).all (· == "•"))
  let markerColor (l : Layout.LineOut) : Option Ir.Color :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ c _ _ _ _ _ _ _ _ _) => some c
    | _ => none
  t "a covered item's marker dims with it"
    (markerColor stepLines[1]! == some (Ir.Design.ofDoc { palette := { coveredFraction := some 38 } }).inkCover &&
     markerColor stepLines[0]! == some Ir.Color.black)
  let (hiddenLines, _) := runOn ("\\documentclass{beamer}\n\\usetheme{default}\n" ++
    "\\begin{document}\n" ++
    "\\begin{frame}\\begin{itemize}\\item<1-> alpha\\item<2-> beta" ++
    "\\end{itemize}\\end{frame}\n\\end{document}")
  t "a hidden item keeps its line's place and ships neither its marker nor its words"
    (hiddenLines.size == 4 && (hiddenLines.map markerOf) == #["•", "", "•", "•"] &&
     hiddenLines[1]!.segs.all (fun s => match s with | .run .. => false | _ => true))
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
  let (deepLines, deepDiags) := runOn ("\\begin{itemize}\\item a" ++
    "\\begin{itemize}\\item b\\begin{itemize}\\item c\\begin{itemize}\\item d" ++
    "\\begin{itemize}\\item e\\end{itemize}\\end{itemize}\\end{itemize}" ++
    "\\end{itemize}\\end{itemize}")
  t "a fifth level warns W0010" (deepDiags.any (·.code == "W0010"))
  t "a fifth level still renders the fourth's marker"
    (deepLines.size == 5 && markerOf deepLines[4]! == "·")
  let (_, glyphDiags) := runOn ("\\documentclass{article}\n" ++
    "\\style{itemize}{ marker = {✦} }\n\\begin{document}\n" ++
    "\\begin{itemize}\\item a\\end{itemize}\n\\end{document}")
  t "an uncoverable marker glyph warns" (glyphDiags.any (·.code == "E0405"))
  let scalars := Layout.docScalars (Elab.run "t"
    ("\\begin{itemize}\\item a\\begin{itemize}\\item b\\end{itemize}" ++
     "\\end{itemize}")).1
  t "docScalars carries the reached default markers"
    (scalars.contains '•' && scalars.contains '–' &&
     scalars.contains '*' && scalars.contains '-' && !scalars.contains '∗')

/-- A numbered algorithm's line numbers stand inside the text area. -/
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
  let leftmost (ls : Array Layout.LineOut) : Dim.Length :=
    ls.foldl (fun m l => min m l.x) geom.pageW
  let short := linesOf (alg true 13)
  t s!"a numbered algorithm's numbers stand inside the measure \
({(leftmost short).toBpString} vs {geom.hmargin.toBpString})"
    (0 < short.size && geom.hmargin ≤ leftmost short)
  let long := linesOf (alg true 120)
  t s!"a hundred-line algorithm's three-digit numbers stay inside \
({(leftmost long).toBpString} vs {geom.hmargin.toBpString})"
    (0 < long.size && geom.hmargin ≤ leftmost long)
  let plain := linesOf (alg false 13)
  t s!"an unnumbered algorithm reserves no number column \
({(leftmost plain).toBpString})"
    (0 < plain.size && leftmost plain == geom.hmargin)
  -- All three set the same first line, so right-edge differences are reserve differences.
  let rightOf (ls : Array Layout.LineOut) : Dim.Length :=
    (ls[0]?.map fun l => l.x + l.setWidth).getD 0
  t s!"the default column is two ems, algorithm2e's inset and the HTML's padding \
({(rightOf short - rightOf plain).toBpString})"
    (rightOf short - rightOf plain == 2 * geom.fontSize)
  t s!"a wider number widens the column \
({(rightOf long - rightOf short).toBpString})"
    (rightOf plain < rightOf short && rightOf short < rightOf long)

/-- Line-level typesetting checks against a one-face set. -/
def lineChecks (ref : IO.Ref (List String)) (geom : Layout.Geom) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let widthOf (src : String) : Dim.Length :=
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
  t "tilde is a no-break space"
    ((Elab.run "t" "a~b").1.body == #[.para #[.text "a\u00a0b"]])
  t "tilde does not break the line" (widthOf "a~b" == widthOf "a\u00a0b")
  t "escaped tilde is a literal tilde"
    ((Elab.run "t" "a\\~b").1.body == #[.para #[.text "a~b"]])
  let firstX (src : String) : Option Dim.Length :=
    ((bodyLines (layoutOf oneFace (Elab.run "t" src).1 geom))[0]?).map (·.x)
  t "noindent's first line stands at the margin, as every first line does"
    (firstX "\\noindent alpha beta" == some geom.hmargin &&
     firstX "alpha beta" == some geom.hmargin)

  let scOut := layoutOf oneFace (Elab.run "t" "\\scshape aB").1 geom
  let scRuns := (bodyLines scOut).flatMap (·.segs.filterMap fun s =>
    match s with
    | .run _ _ _ _ glyphs size _ _ _ _ _ => some (glyphs.map (·.2.1), size)
    | _ => none)
  t "synthesised small caps carry no lowercase form"
    (!scRuns.isEmpty && scRuns.all fun (cs, _) => cs.all fun c => !c.isLower)
  t "synthesised small caps are uniform: mixed case sets at one reduced size"
    (scRuns.all (·.2 == geom.fontSize * Layout.smallCapScale / 1000))

  -- A departure from LaTeX: a last line's `\hfill` takes the whole leftover.
  let measureOf (src : String) : Array Dim.Length :=
    let (d, _) := Elab.run "t" src
    (bodyLines (layoutOf oneFace d geom)).map (·.setWidth)
  t "paragraph ending in a break keeps its content"
    ((measureOf "first line\\\\\n\nsecond").size == 2)
  let lastLine := measureOf "Left \\hfill Right"
  t "hfill reaches the margin on a final line"
    (lastLine.size == 1 && lastLine[0]! == geom.textWidth)
  let brokenLine := measureOf "Left \\hfill Right\\\\Second"
  t "hfill reaches the margin before a break"
    (brokenLine.size == 2 && brokenLine[0]! == geom.textWidth)
  t "no hfill leaves the last line short"
    (brokenLine.size == 2 && brokenLine[1]! < geom.textWidth)
  t "verbatim sets one line per code line, blanks included"
    ((measureOf "\\begin{verbatim}\na\n\nb\n\\end{verbatim}").size == 3)

  -- Every word starts 'A' and ends '.', so each full line's boundary glyphs are known.
  let font := oneFace.get 0
  let scaledAdv (c : Char) : Dim.Length :=
    font.advance c * max 0 geom.fontSize / font.unitsPerEm
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

/-- A `\label` binds to the nearest preceding numbered thing, a forward reference resolves, a
missing key is `??` named by W0349, and a duplicate keeps its first binding. -/
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
  let (fwd, fwdDs) := art
    "\\section{A}\\label{s:a}\nSee \\ref{s:b}.\n\\section{B}\\label{s:b}\nBack to \\ref{s:a}."
  t "a forward reference resolves without a second pass"
    (fwdDs.isEmpty && refShows fwd "s:b" == some ("2", some "s:b") &&
     refShows fwd "s:a" == some ("1", some "s:a"))
  let (eq, _) := art "\\section{A}\\label{s:a}\nAs \\eqref{s:a}."
  t "eqref parenthesises the number" (refShows eq "s:a" == some ("(1)", some "s:a"))
  let (missing, missDs) := art "\\section{A}\nSee \\ref{gone} and \\ref{gone}."
  t "an unresolved reference is ?? and W0349 names the key once"
    (refShows missing "gone" == some ("??", none) &&
     (missDs.filter (·.code == "W0349")).size == 1)
  let (bare, bareDs) := art "\\label{early}\nSee \\ref{early}."
  t "a label where nothing numbers resolves to ??"
    (refShows bare "early" == some ("??", none) &&
     bareDs.any (·.code == "W0349"))
  let (dup, dupDs) := art
    "\\section{A}\\label{k}\n\\section{B}\\label{k}\nSee \\ref{k}."
  t "a duplicate label warns and the first wins"
    (dupDs.any (·.code == "W0350") && refShows dup "k" == some ("1", some "k"))
  let (flt, _) := art ("\\section{A}\\label{s:a}\n" ++
    "\\begin{figure}\\caption{Invented}\\label{fig:x}\\end{figure}\n" ++
    "\\label{after}\nSee \\ref{fig:x} and \\ref{after}.")
  t "a float's label takes the float's number; one after it, the section's"
    ((refShows flt "fig:x").map (·.1) == some "1" &&
     (refShows flt "after").map (·.1) == some "1" &&
     (refShows flt "fig:x").bind (·.2) == some "fig:x")
  let (eqn, eqnDs) := art ("\\section{A}\n" ++
    "\\begin{equation}\\label{eq:one} a = b \\end{equation}\n" ++
    "\\begin{equation} c = d \\nonumber\\end{equation}\n" ++
    "\\begin{equation}\\label{eq:two} e = f \\end{equation}\n" ++
    "See \\eqref{eq:one} and \\eqref{eq:two}.")
  t "equation labels bind to the equation's number; nonumber opts out"
    (eqnDs.isEmpty &&
     (refShows eqn "eq:one").map (·.1) == some "(1)" &&
     (refShows eqn "eq:two").map (·.1) == some "(2)")
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
  let (sub, _) := art ("\\begin{figure}\n" ++
    "\\begin{subfigure}{0.4\\textwidth}left\\caption{L}\\label{sf:l}\\end{subfigure}\n" ++
    "\\begin{subfigure}{0.4\\textwidth}right\\caption{R}\\label{sf:r}\\end{subfigure}\n" ++
    "\\caption{Parent}\\label{fig:p}\\end{figure}\n" ++
    "See \\ref{sf:l}, \\ref{sf:r}, \\ref{fig:p}.")
  t "a subfigure label resolves to the parent number and its letter"
    ((refShows sub "sf:l").map (·.1) == some "1a" &&
     (refShows sub "sf:r").map (·.1) == some "1b" &&
     (refShows sub "fig:p").map (·.1) == some "1")
  let (dupf, dupfDs) := art ("\\section{A}\n\\section{B}\\label{k}\n" ++
    "\\begin{figure}\\caption{C}\\label{k}\\end{figure}\nSee \\ref{k}.")
  t "a float duplicate of an outside key warns and the first wins"
    (dupfDs.any (·.code == "W0350") && refShows dupf "k" == some ("2", some "k"))
  let (eqf, _) := art ("\\begin{figure}\\caption{C}\n" ++
    "\\begin{equation}\\label{eq:f} x = y \\end{equation}\\end{figure}\n" ++
    "As \\eqref{eq:f}.")
  t "an equation label inside a float keeps the equation's number"
    ((refShows eqf "eq:f").map (·.1) == some "(1)")
  t "an anchor keeps no whitespace and stays nonempty"
    (Ir.labelAnchor "a b\"c" == "a-b-c" && Ir.labelAnchor "" == "label")
  let (htmlDoc, _) := art "\\section{A}\\label{s:a}\nSee \\ref{s:a}."
  let page := (HtmlDoc.emit {} htmlDoc).1
  t "HTML links a resolved reference to its label's anchor"
    ((page.splitOn "<span id=\"s:a\">").length == 2 &&
     (page.splitOn "href=\"#s:a\"").length == 2)
  let run (body : String) : Nat :=
    let (doc, _) := art body
    let out := layoutOf oneFace doc
    out.pages.foldl (fun n p => n + p.lines.size) 0
  t "a lone label line ships no blank line"
    (run "\\section{A}\\label{s:a}\nText after." == run "\\section{A}\nText after.")

/-- `quote` and `quotation` elaborate to one `Block.quote` of their kinds, set inside both margins in
the PDF, as `<blockquote>` in HTML and as one `> ` block in markdown. -/
def quoteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Before.\\begin{quote}One invented line.\\end{quote}" ++
    "\\begin{quotation}First paragraph.\n\nSecond paragraph.\\end{quotation}" ++
    "After.\\end{document}")
  t "quote source is clean" ds.isEmpty
  -- The first quote follows text, so it rides in the in-paragraph role.
  let unrole : Option Ir.Block → Option Ir.Block
    | some (.role n #[b]) => if n == Ir.inParagraphRole then some b else some (.role n #[b])
    | b => b
  t "quote and quotation elaborate to the one quote node, each of its kind"
    (doc.body.size == 4 &&
      (match unrole doc.body[1]?, doc.body[2]? with
       | some (Ir.Block.quote s1 q1), some (Ir.Block.quote s2 q2) =>
         q1.size == 1 && q2.size == 2 && s1.kind == .quote && s2.kind == .quotation
       | _, _ => false))
  let md := (MarkdownDoc.emit doc)
  t "markdown sets the quotation as > lines"
    ((md.splitOn "> One invented line.").length == 2)
  t "markdown keeps a two-paragraph quotation one block"
    ((md.splitOn "> First paragraph.\n>\n> Second paragraph.").length == 2)
  let page := (HtmlDoc.emit {} doc).1
  t "html sets the quotation as a blockquote"
    (match (page.splitOn "<blockquote")[1]? with
     | some rest =>
       ((rest.splitOn "</blockquote>")[0]?.map fun inner =>
         (inner.splitOn "<p>One invented line.</p>").length == 2).getD false
     | none => false)
  let (esc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{quote}2 < 3\\end{quote}\\end{document}")
  t "html escapes quoted content like any other"
    ((((HtmlDoc.emit {} esc).1.splitOn "2 &lt; 3").length == 2))
  -- `\leftmargini` is 2.5em (classes.dtx), and both margins move in.
  let geom : Layout.Geom := {}
  let lm := geom.fontSize * 5 / 2
  let out := layoutOf oneFace doc geom
  let lines := out.pages.flatMap (·.lines)
  let quoted := lines.filter fun l => l.x == geom.hmargin + lm
  t "pdf quotation indents from the left margin" (quoted.size ≥ 1)
  t "pdf quotation keeps inside the narrowed right margin"
    (quoted.all fun l =>
      decide (l.x + l.setWidth ≤ geom.hmargin + geom.textWidth - lm))
  t "pdf prose around the quotation keeps the full measure"
    (lines.any fun l => l.x == geom.hmargin)

/-- A declared box width reaches the page as declared: a fraction of the measure as that fraction,
an absolute length as that length. -/
def boxWidthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let filler := "Panel prose long enough to need more than one line inside its box."
  let boxDoc (pre : String) (w : String) : String :=
    "\\documentclass{article}" ++ pre ++ "\\begin{document}\\begin{minipage}{" ++ w ++
    "}" ++ filler ++ "\\end{minipage}\\end{document}"
  let widest (src : String) : Dim.Length :=
    ((allLines (layoutOf oneFace (elabStr src).1 geom)).filter
      fun l => !l.furniture && !l.segs.isEmpty).foldl
        (fun m l => max m (l.x + l.setWidth - geom.hmargin)) 0
  let half := widest (boxDoc "" ".5\\textwidth")
  t "a fractional box width still sets at its fraction"
    (decide (half ≤ geom.textWidth / 2) && decide (half > geom.textWidth / 4))
  let abs90 := widest (boxDoc "" "90pt")
  t "an absolute box width sets at that length"
    (decide (abs90 ≤ Dim.pt 90) && decide (abs90 > Dim.pt 30))
  t "an absolute box width is not a named loss"
    (!(warnCodes (boxDoc "" "90pt")).contains "W0314")
  let affineSrc := "0.315\\dimexpr \\textwidth +36mm\\relax"
  let affine := widest (boxDoc "" affineSrc)
  let affineBound := ((geom.textWidth + Dim.mm 36) * 315).tdiv 1000
  t "an affine box width resolves against its enclosing measure"
    (decide (affine ≤ affineBound) && decide (affine > geom.textWidth / 3))
  t "an affine box width has one successful reading"
    (!(warnCodes (boxDoc "" affineSrc)).contains "W0314")
  let viaMacro := widest (boxDoc "\\newcommand{\\panelw}{.5\\textwidth}" "\\panelw")
  t "a box width spelled through a document command resolves"
    (viaMacro == half)
  t "a box width spelled through a document command is not a named loss"
    (!(warnCodes (boxDoc "\\newcommand{\\panelw}{.5\\textwidth}" "\\panelw")).contains
      "W0314")
  let parbox := widest ("\\documentclass{article}\\begin{document}\\parbox{90pt}{" ++
    filler ++ "}\\end{document}")
  t "a parbox sets at its declared width"
    (decide (parbox ≤ Dim.pt 90) && decide (parbox > Dim.pt 30))
  t "a parbox width is kept"
    (!(warnCodes ("\\documentclass{article}\\begin{document}\\parbox{90pt}{x}" ++
      "\\end{document}")).contains "W0104")
  t "an absolute width past the measure is clamped to it"
    (decide (widest (boxDoc "" "900pt") ≤ geom.textWidth))
  t "each declared width has its own HTML track"
    (Ir.Track.css (Ir.BoxWidth.trackOf (.frac 500)) == "50%" &&
      Ir.Track.css (Ir.BoxWidth.trackOf (.abs (Dim.pt 90))) == s!"{(Dim.pt 90).toBpString}pt" &&
      Ir.Track.css (Ir.BoxWidth.trackOf .share) == "1fr")

/-- A declared ragged setting hangs its lines from the side it declares. -/
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
  -- The lines are short, so none fills the measure.
  t "the ragged probe set three unfilled lines on each side"
    (leftSet.size == 3 && rightSet.size == 3 &&
      rightSet.all fun l => decide (l.setWidth < geom.textWidth))
  t "a left-set ragged scope hangs its lines from the margin"
    (leftSet.all fun l => l.x + l.hang == geom.hmargin)
  t "a right-set ragged scope hangs its lines from the measure's right edge"
    (rightSet.all fun l => l.x + l.setWidth == right)
  let envLeft := linesOf "\\begin{flushleft}"
  t "the flushleft environment sets from the margin"
    (envLeft.size ≥ 1 && envLeft.all fun l => l.x + l.hang == geom.hmargin)
  let envRight := (allLines (layoutOf oneFace (elabStr
    ("\\documentclass{article}\\begin{document}\\begin{flushright}" ++
      "One short line.\\\\ Another short line.\\end{flushright}" ++
      "\\end{document}")).1 geom)).filter fun l => !l.furniture && !l.segs.isEmpty
  t "the flushright environment sets from the measure's right edge"
    (envRight.size == 2 && envRight.all fun l => l.x + l.setWidth == right)
  let centred := (allLines (layoutOf oneFace (elabStr (doc "\\centering ")).1 geom)).filter
    fun l => !l.furniture && !l.segs.isEmpty
  t "a right-set line is not a centred line"
    (centred.size == 3 && centred.all fun l => decide (l.x + l.setWidth < right))
  t "the right-set spellings are not a named loss"
    (!(warnCodes (doc "\\raggedleft ")).contains "W0104" &&
      !(warnCodes ("\\documentclass{article}\\begin{document}" ++
        "\\begin{flushright}x\\end{flushright}\\end{document}")).contains "W0104")
  let treeOf (decl : String) : Html.Node :=
    HtmlDoc.blockNode {} (elabStr (doc decl)).1.body[0]!
  let classOf : Html.Node → Option String
    | .elem _ attrs _ => (attrs.find? fun a => a.1 == "class").map (·.2)
    | _ => none
  t "the typed tree carries the declared side's class"
    (classOf (treeOf "\\raggedright ") == some (HtmlDoc.raggedClass .left) &&
      classOf (treeOf "\\raggedleft ") == some (HtmlDoc.raggedClass .right))
  t "the sheet declares each side's own edge"
    (HtmlDoc.raggedRule .left == ".ragged { text-align: left; --ltx-box-left: 0; " ++
        "--ltx-box-right: auto; --ltx-box-justify: start; }\n" &&
      HtmlDoc.raggedRule .right == ".ragged-right { text-align: right; --ltx-box-left: auto; " ++
        "--ltx-box-right: 0; --ltx-box-justify: end; }\n")

/-- A box set in an alignment scope takes the scope's side: none, half or all of its slack under
`flushleft`, `center` and `flushright`. -/
def boxSideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let marker := "Boxed Marker"
  let boxes : List (String × String) :=
    [("tabular", "\\begin{tabular}{l}" ++ marker ++ "\\end{tabular}"),
     ("picture", "\\begin{tikzpicture}\\draw (0,0) rectangle (2,1);" ++
        "\\node at (1,0.5) {" ++ marker ++ "};\\end{tikzpicture}"),
     ("minipage", "\\begin{minipage}{0.4\\textwidth}" ++ marker ++ "\\end{minipage}"),
     ("parbox", "\\parbox{0.4\\textwidth}{" ++ marker ++ "}")]
  for (kind, box) in boxes do
    let xOf (env : String) : Option Dim.Length :=
      let src := "\\documentclass{article}\\begin{document}\\begin{" ++ env ++ "}" ++ box ++
        "\\end{" ++ env ++ "}\\end{document}"
      ((bodyLines (layoutOf oneFace (elabStr src).1)).find? (lineText · == marker)).map (·.x)
    match xOf "flushleft", xOf "center", xOf "flushright" with
    | some l, some c, some r =>
      t s!"a {kind} centres midway between its two flush placements"
        (l < c && c < r && (c - l - (r - c)).abs ≤ Dim.Length.quantum)
    | _, _, _ => t s!"a {kind} sets its marker line under each side" false

/-- The HTML twin of `boxSideChecks`: each alignment scope's rule places a box on its side. -/
def boxSideHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabStr ("\\documentclass{article}\\begin{document}\\begin{center}" ++
    "\\begin{tabular}{c}Title\\end{tabular}\\end{center}\\begin{center}" ++
    "\\begin{minipage}{0.4\\textwidth}Box\\end{minipage}\\end{center}\\end{document}")
  let (page, _) := HtmlDoc.emit {} doc
  for (cls, h) in [("centered", Ir.HAlign.center), ("ragged", .left), ("ragged-right", .right),
      ("column", .left)] do
    let decls := (screenRuleOf page ("." ++ cls)).getD ""
    t s!"the .{cls} scope declares its side's box placement"
      (hasStr decls s!"text-align: {h.align};" &&
        hasStr decls s!"--ltx-box-left: {(HtmlDoc.boxMargins h).1};" &&
        hasStr decls s!"--ltx-box-right: {(HtmlDoc.boxMargins h).2};" &&
        hasStr decls s!"--ltx-box-justify: {HtmlDoc.boxJustify h};")
  t "a table reads its scope's box margins"
    (((screenRuleOf page "table").getD "").trimAscii.toString ==
      "margin-left: var(--ltx-box-left, 0); margin-right: var(--ltx-box-right, auto);")
  let styles := (elemAttrsList (· == "div") #[] (HtmlDoc.emitTree {} doc).2.1.toList).filterMap
    fun (_, attrs) => if HtmlDoc.classTokens attrs == ["columns"]
      then (attrs.find? (·.1 == "style")).map (·.2) else none
  t "a lone box's row reads its scope's track placement"
    (styles.size == 1 && styles.all (hasStr · "justify-content: var(--ltx-box-justify, start)"))

/-- The title heading takes what the title page reads, and a heading key it cannot read is named
with the page unchanged. -/
def titleHeadingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (decl : String) : String :=
    "\\documentclass{article}\\palette{ quiet = #6B7280 }" ++ decl ++
    "\\title{An Invented Title}\\author{Pat Placeholder}\\begin{document}\\maketitle " ++
    "Body text.\\end{document}"
  let (plain, _) := elabStr (src "")
  let linesOf (d : Ir.Doc) : Array (Dim.Length × Dim.Length × String) :=
    (bodyLines (layoutOf oneFace d)).map fun l => (l.x, l.y, lineText l)
  let values : List (String × String) :=
    [("rule", "quiet"), ("rule-position", "baseline"), ("rule-thickness", "1pt"),
     ("marker", "{x}"), ("indent", "2em"), ("gap", "1em"), ("body-size", "small"),
     ("color", "quiet"), ("tilde", "low"), ("label", "{x}"), ("leftmargin", "2em")]
  t "every unread title key is exercised" (values.map (·.1) == Ir.styleKeys.filter fun k =>
    !(Ir.styleKeysRead "titlepage").contains k && !Ir.listSetKeys.contains k)
  for (key, v) in values do
    let (d, ds) := elabStr (src ("\\style{titlepage}{ " ++ key ++ " = " ++ v ++ " }"))
    t s!"a title page's '{key}' is named by its own key"
      (ds.any fun g => g.code == DiagCode.W0104.code && g.subject == some ("style:titlepage:" ++ key))
    t s!"a title page's '{key}' ships the page of the document without it"
      (linesOf d == linesOf plain && (HtmlDoc.emit {} d).1 == (HtmlDoc.emit {} plain).1)

/-- A centred headline stands on its band's centre whatever logo stands beside it, and a declared
side keeps the matter beside the logos. -/
def headlineSideChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let poster (pre : String) : Ir.Doc := (elabStr ("\\documentclass{poster}" ++ pre ++
    "\\title{An Invented Band}\\begin{document}\\begin{frame}Body.\\end{frame}" ++
    "\\end{document}")).1
  let css (d : Ir.Doc) : String := (HtmlDoc.emit {} d).1
  let right := poster "\\logoright{Right Mark}"
  let page := css right
  t "a centred band lays its matter between two equal flexible tracks"
    (hasStr ((screenRuleOf page "body > header.headline").getD "")
      "grid-template-columns: 1fr auto 1fr;" &&
     hasStr ((screenRuleOf page "body > header.headline > .headline-matter").getD "")
      "grid-area: 1 / 2;" &&
     hasStr ((screenRuleOf page "body > header.headline > .headline-logo:first-child").getD "")
      "grid-area: 1 / 1;" &&
     hasStr ((screenRuleOf page "body > header.headline > .headline-matter ~ .headline-logo").getD "")
      "grid-area: 1 / 3;")
  let order (d : Ir.Doc) : List String :=
    match (HtmlDoc.emitTree {} d).2.1.toList.find? fun n => match n with
      | .elem "header" a _ => HtmlDoc.classTokens a == ["headline"]
      | _ => false with
    | some (.elem _ _ kids) => kids.toList.filterMap fun k => match k with
      | .elem _ a _ => (HtmlDoc.classTokens a).head?
      | _ => none
    | _ => []
  t "the band ships its left logo first and its right logo after the matter"
    (order right == ["headline-matter", "headline-logo"] &&
      order (poster "\\logoleft{Left Mark}") == ["headline-logo", "headline-matter"])
  for (side, align) in [("left", "left"), ("right", "right")] do
    let d := poster ("\\style{titlepage}{ align = " ++ side ++ " }\\logoright{Right Mark}")
    t s!"a band declared {side} sets its matter {align} beside the logos"
      (hasStr ((screenRuleOf (css d) "body > header.headline .headline-matter").getD "")
        s!"flex: 1; text-align: {align};")

/-- `\centering` centres the rest of its scope, as a declaration. -/
def centeringChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (c1, ds1) := elabStr "{\\centering x\\par} y"
  t "centering centres the rest of its group" (ds1.isEmpty &&
    c1.body == #[.center #[.para #[.text "x"]], .para #[.text "y"]])
  t "centering carries across par like other declarations"
    ((elabStr "{\\centering a\\par b}").1.body ==
      #[.center #[.para #[.text "a"]], .center #[.para #[.text "b"]]])
  let (fr, frDs) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}\\centering Questions?\\end{frame}\\end{document}")
  t "centering inside a frame centres its content" (frDs.isEmpty &&
    fr.body == #[.frame #[] false .center false #[.center #[.para #[.text "Questions?"]]]])
  t "centering in an argument still warns"
    (warnCodes "\\textbf{\\centering x}" == ["W0108"])
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
  -- A center's close after the caption is its float's marker (`Ir.captionCloseRole`), else nothing.
  let unmark (d : Ir.Doc) : Ir.Doc := { d with body := d.body.map fun b => match b with
    | .float k n ca body cap =>
      .float k n ca (body.filter fun x => match x with
        | .role r _ => r != Ir.captionCloseRole
        | _ => true) cap
    | b => b }
  let (gDoc, gDs) := elabStr (grouped "center")
  let (fDoc, fDs) := elabStr flat
  t "a float's center group is transparent: the Ir of \\centering, its close after the caption marked"
    (unmark gDoc == fDoc && gDoc != fDoc)
  t "a float's center group is transparent: same diagnostics"
    (sig gDs == sig fDs)
  t "the caption inside the group is the float's, never unknown"
    (gDs.all (·.code != "W0301"))
  let (cDoc, cDs) := elabStr (grouped "centering")
  t "the centering environment name is the same transparent group"
    (unmark cDoc == fDoc && sig cDs == sig fDs)
  let tblBody := "\\begin{tabular}{ll}\na & b \\\\\n\\end{tabular}\n" ++
    "\\caption{An invented strip.}\n\\label{tab:s}\n"
  let (tg, tgDs) := elabStr (floatDoc
    ("\\begin{table}[h]\n\\begin{center}\n" ++ tblBody ++ "\\end{center}\n\\end{table}"))
  let (tf, tfDs) := elabStr (floatDoc
    ("\\begin{table}[h]\n\\centering\n" ++ tblBody ++ "\\end{table}"))
  t "a table's center group is transparent: same Ir and diagnostics"
    (unmark tg == tf && tg != tf && sig tgDs == sig tfDs && tgDs.all (·.code != "W0301"))

theorem backend_rgb_exact (c : Ir.Color) (hm : c.pdfModel = none) (hc : c.cmyk = none) :
    HtmlDoc.cssColor c =
        "#" ++ Hex.byte false c.r ++ Hex.byte false c.g ++ Hex.byte false c.b ∧
      c.pdfFill = Ir.Color.pdfMilli (Ir.Color.milli c.r) ++ " " ++
        Ir.Color.pdfMilli (Ir.Color.milli c.g) ++ " " ++
        Ir.Color.pdfMilli (Ir.Color.milli c.b) ++ " rg" :=
  ⟨rfl, by rw [Ir.Color.pdfFill_srgb c hm hc]; rfl⟩

/-- Every supported xcolor model reaches one concrete colour in every surface context, and both
artifacts project that value. -/
def colorModelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let cases : List (String × String × Ir.Color × String) :=
    [("HTML", "010203", { r := 0x01, g := 0x02, b := 0x03 },
        "0.00392 0.00784 0.01176 rg"),
     ("RGB", "+51.5,+102,+153", { r := 0x34, g := 0x66, b := 0x99 },
        "0.20195 0.4 0.59999 rg"),
     ("rgb", "0.1234,0.2345,0.3456", { r := 0x1F, g := 0x3C, b := 0x58 },
        "0.1234 0.2345 0.3456 rg"),
     ("gray", "0.2345", { r := 0x3C, g := 0x3C, b := 0x3C }, "0.2345 g"),
     ("cmyk", "0.1234,0.2345,0.3456,0.4567",
        { r := 0x6B, g := 0x4F, b := 0x32, cmyk := some (123, 235, 346, 457) },
        "0.1234 0.2345 0.3456 0.4567 k")]
  let colorsOf (d : Ir.Doc) : Array Ir.Color :=
    Ir.foldDoc (fun acc i => match i with
      | .colored c _ _ => acc.push c
      | _ => acc) #[] d
  let samePreview (a b : Ir.Color) : Bool :=
    a.r == b.r && a.g == b.g && a.b == b.b && a.cmyk == b.cmyk
  let article (pre body : String) : String :=
    "\\documentclass{article}" ++ pre ++ "\\begin{document}" ++ body ++ "\\end{document}"
  let deck (body : String) : String :=
    "\\documentclass{slides}\\theme{default}\\begin{document}" ++ body ++ "\\end{document}"
  let artifactHas (d : Ir.Doc) (text : String) (want : Ir.Color) (pdfOp : String) : Bool :=
    let geom := Layout.Geom.ofPage d.page
    let pdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace d geom).pages d.info)
    let (_, body, _) := emitIn {} d .print
    bytesContain pdf pdfOp &&
      (elemLightStyles body.toList).any fun (shown, style) =>
        hasStr shown text && hasStr style ("color: " ++ HtmlDoc.cssColor want)
  for (model, spec, want, pdfOp) in cases do
    let direct := "\\textcolor[" ++ model ++ "]{" ++ spec ++ "}{Model Ink}"
    let (paragraph, pds) := elabStr (article "" direct)
    t s!"xcolor {model}: direct text colour resolves in a paragraph"
      (pds.all (·.severity != .error) && (colorsOf paragraph).any (samePreview want))
    t s!"xcolor {model}: paragraph colour reaches exact PDF and typed HTML"
      (artifactHas paragraph "Model Ink" want pdfOp)
    let (frame, fds) := elabStr (deck
      ("\\begin{frame}{" ++ direct ++ "}Frame body.\\end{frame}"))
    t s!"xcolor {model}: direct text colour resolves in a frame title"
      (fds.all (·.severity != .error) && (colorsOf frame).any (samePreview want))
    t s!"xcolor {model}: frame-title colour reaches exact PDF and typed HTML"
      (artifactHas frame "Model Ink" want pdfOp)
    let decl := "\\definecolor{modelink}{" ++ model ++ "}{" ++ spec ++ "}"
    let (defined, dds) := elabStr (article decl "\\textcolor{modelink}{Defined Ink}")
    t s!"xcolor {model}: definecolor and a named use share the resolved value"
      (dds.all (·.severity != .error) &&
        (defined.palette.find? "modelink").any (samePreview want) &&
        (colorsOf defined).any (samePreview want))
    let (flow, cds) := elabStr (article ""
      ("Before {\\color[" ++ model ++ "]{" ++ spec ++ "}Flow Ink} after."))
    t s!"xcolor {model}: the declaration form resolves through the same value"
      (cds.all (·.severity != .error) && (colorsOf flow).any (samePreview want) &&
        artifactHas flow "Flow Ink" want pdfOp)
    let (pageDoc, pageDs) := elabStr (article ""
      ("\\pagecolor[" ++ model ++ "]{" ++ spec ++ "}Model Ground"))
    let pageGeom := Layout.Geom.ofPage pageDoc.page
    let pageOut := layoutOf oneFace pageDoc pageGeom
    let pagePdf := pdfText (Pdf.write pageGeom oneFace pageOut.pages pageDoc.info)
    let (_, pageBody, _) := HtmlDoc.emitTree {} pageDoc
    t s!"xcolor {model}: page colour shares the exact model projection"
      (pageDs.all (·.severity != .error) && bytesContain pagePdf pdfOp &&
        (pageOut.pages[0]?).any fun p => p.fills.any fun f => samePreview want f.color)
    t s!"xcolor {model}: typed HTML paints the same page-colour preview"
      ((elemStylesList #[] pageBody.toList).any fun (shown, style) =>
        hasStr shown "Model Ground" && hasStr style ("--ltx-bg: " ++ HtmlDoc.cssColor want) &&
          hasStr style "background: var(--ltx-bg")
  let boundaryPdf (pre body : String) : ByteArray :=
    let (d, _) := elabStr (article pre body)
    let geom := Layout.Geom.ofPage d.page
    pdfText (Pdf.write geom oneFace (layoutOf oneFace d geom).pages d.info)
  let directBoundary := boundaryPdf ""
    "\\textcolor[rgb]{.000009,.123456,.999999}{Direct Boundary}"
  t "xcolor direct rgb keeps the source's numeric value"
    (bytesContain directBoundary "0.000009 0.123456 0.999999 rg")
  let definitions :=
    "\\definecolor{boundrgb}{rgb}{.000009,.123456,.999999}" ++
      "\\definecolor{boundgray}{gray}{.500009}" ++
      "\\definecolor{boundcmyk}{cmyk}{.000009,.00001,.123456,.999999}"
  let definedRgb := boundaryPdf definitions "\\pagecolor{boundrgb}Defined RGB"
  let definedGray := boundaryPdf definitions "\\pagecolor{boundgray}Defined Gray"
  let definedCmyk := boundaryPdf definitions "\\pagecolor{boundcmyk}Defined CMYK"
  t "xcolor definitions use the five-decimal device values LuaLaTeX writes"
    (bytesContain definedRgb "0 0.12345 0.99999 rg" &&
      bytesContain definedGray "0.5 g" &&
      bytesContain definedCmyk "0 0.00001 0.12345 0.99999 k")
  let (mixedDoc, mixedDs) := elabStr (article ""
    "\\textcolor[rgb]{0.1, 0.2 0.3}{Mixed Separators}")
  t "xcolor component separators may mix commas and ASCII whitespace"
    (mixedDs.all (·.severity != .error) &&
      (colorsOf mixedDoc).any (samePreview { r := 26, g := 51, b := 77 }))
  let half : Decl.ColorComponent := { num := 1, scale := 2 }
  let rgbHalf := Ir.Color.ofRgbUnit half half half
  let grayHalf := Ir.Color.ofGray half
  let rgbSpan : Span := ⟨"rgb.tex", { line := 1, col := 1 }⟩
  let graySpan : Span := ⟨"gray.tex", { line := 2, col := 1 }⟩
  let sites : Array (Ir.Palette × String × Ir.Color × Bool × Span) :=
    #[({}, "rgb(.5,.5,.5)", rgbHalf, false, rgbSpan),
      ({}, "gray(.5)", grayHalf, false, graySpan)]
  t "anonymous colour-site selection keeps PDF model provenance"
    (rgbHalf == grayHalf && rgbHalf.pdfModel != grayHalf.pdfModel &&
      Elab.colorSiteOf sites none grayHalf == some ("gray(.5)", graySpan))
  let named := article "\\definecolor{namedink}{HTML}{336699}"
    "\\textcolor{namedink}{Named Ink}"
  let (namedDoc, namedDs) := elabStr named
  t "xcolor no-model syntax resolves a declared name"
    (namedDs.all (·.severity != .error) &&
      (colorsOf namedDoc).contains ({ r := 0x33, g := 0x66, b := 0x99 } : Ir.Color))
  let (contrastDoc, contrastDs) := elabStr (article
    "\\palette{ muted = #8A8A99 }" "\\color{black}\\textcolor{muted}{Muted Ink}")
  let contrastEpoch := contrastDoc.body.foldl (fun p b => match b with
    | .setPalette q => some q
    | _ => p) none
  let declaredMuted := contrastDoc.palette.find? "muted"
  t "a role failing in one epoch is reported, both palettes keeping its declared value"
    (contrastDs.any (·.code == "W0315") &&
      declaredMuted == some { r := 0x8A, g := 0x8A, b := 0x99 } &&
      contrastEpoch.bind (·.find? "muted") == declaredMuted)
  t "the accessibility colour judge reads the declared root pair"
    (!(HtmlDoc.schemeFailures true contrastDoc).isEmpty)
  let malformed : List (String × String × String) :=
    [("short HTML", "\\textcolor[HTML]{369}{Kept Ink}", "E0321"),
     ("bad HTML digit", "\\textcolor[HTML]{GG6699}{Kept Ink}", "E0321"),
     ("short rgb", "\\textcolor[rgb]{.2,.4}{Kept Ink}", "E0321"),
     ("empty rgb field", "\\textcolor[rgb]{.2,,.4,.6}{Kept Ink}", "E0321"),
     ("large RGB", "\\textcolor[RGB]{256,0,0}{Kept Ink}", "E0321"),
     ("wide gray", "\\textcolor[gray]{.2,.4}{Kept Ink}", "E0321"),
     ("large cmyk", "\\textcolor[cmyk]{0,0,0,2}{Kept Ink}", "E0321"),
     ("unsupported hsb", "\\textcolor[hsb]{.2,.4,.6}{Kept Ink}", "W0102")]
  for (label, cmd, code) in malformed do
    let (d, ds) := elabStr (article "" cmd)
    let shipped := censusOf (coveredColorsOf d) (layoutOf oneFace d)
    t s!"xcolor {label}: content is retained and the model failure is named"
      ((ds.filter (·.code == code)).size == 1 && ds.all (·.code != "E0304") &&
        pageHas shipped 0 "Kept Ink" && (colorsOf d).isEmpty)
  let unsupported : List (String × String × String) :=
    [("text colour", "", "\\textcolor[hsb]{.2,.4,.6}{Kept Unsupported}"),
     ("declaration colour", "", "{\\color[hsb]{.2,.4,.6}Kept Unsupported}"),
     ("named definition", "\\definecolor{badmodel}{hsb}{.2,.4,.6}",
        "Kept Unsupported"),
     ("page colour", "", "\\pagecolor[hsb]{.2,.4,.6}Kept Unsupported")]
  for (label, pre, body) in unsupported do
    let (d, ds) := elabStr (article pre body)
    let shipped := censusOf (coveredColorsOf d) (layoutOf oneFace d)
    t s!"xcolor unsupported model: {label} reports once and retains content"
      ((ds.filter (·.code == "W0102")).size == 1 &&
        ds.all (fun x => x.severity != .error && x.code != "W0301" && x.code != "E0304") &&
        pageHas shipped 0 "Kept Unsupported" && d.palette.find? "badmodel" == none)
  let (badDecl, badDeclDs) := elabStr (article
    "\\definecolor{bad}{rgb}{1,0}" "\\textcolor{bad}{Kept Definition Body}")
  t "a malformed colour definition is refused without installing a partial value"
    (badDecl.palette.find? "bad" == none && badDeclDs.any (·.code == "E0321") &&
      badDeclDs.all (·.code != "E0304"))
  let (snapDoc, snapDs) := elabStr (article
    ("\\definecolor{snap}{HTML}{111111}\\pagecolor{snap}" ++
      "\\definecolor{snap}{HTML}{222222}") "Snapshot page.")
  t "a preamble page colour snapshots the name where the command stands"
    (snapDs.all (·.severity != .error) &&
      snapDoc.palette.find? "bg" == some ({ r := 0x11, g := 0x11, b := 0x11 } : Ir.Color) &&
      snapDoc.palette.find? "snap" == some ({ r := 0x22, g := 0x22, b := 0x22 } : Ir.Color))
  let (forwardDoc, forwardDs) := elabStr (article
    "\\pagecolor{latercolor}\\definecolor{latercolor}{HTML}{222222}" "Unpainted page.")
  t "a preamble page colour cannot resolve a definition written after it"
    (forwardDoc.palette.find? "bg" == none && forwardDs.any (·.code == "W0304"))
  let base : Ir.Color := { r := 0xF7, g := 0xF7, b := 0xF7 }
  let painted : Ir.Color := { r := 0x11, g := 0x22, b := 0x33 }
  let groundDiff := HtmlDoc.epochPaletteDiff [.page, .progressTrack, .paper, .standoutInk]
    ({} : Ir.Palette) (({} : Ir.Palette).declare (.role .page) painted)
  t "HTML palette epochs carry the ground change before CSS serialization"
    (groundDiff.groundChanged && groundDiff.entries.any (·.1 == .role .page) &&
      hasStr groundDiff.style s!"{HtmlDoc.roleVar .page}: #112233")
  t "HTML palette epochs re-state the roles inheriting the changed ground"
    (hasStr groundDiff.style s!"{HtmlDoc.roleVar .progressTrack}: var({HtmlDoc.roleVar .page})" &&
      hasStr groundDiff.style s!"{HtmlDoc.roleVar .paper}: var({HtmlDoc.roleVar .page})" &&
      hasStr groundDiff.style s!"{HtmlDoc.roleVar .standoutInk}: var({HtmlDoc.roleVar .paper})")
  let projectionDiff := HtmlDoc.epochPaletteDiff [.page]
    (({} : Ir.Palette).declare (.role .page) rgbHalf)
    (({} : Ir.Palette).declare (.role .page) grayHalf)
  t "HTML palette diffs compare the screen projection, not PDF provenance"
    (projectionDiff.entries.isEmpty && projectionDiff.defaults.isEmpty)
  let accent : Ir.Color := { r := 0xAA, g := 0xBB, b := 0xCC }
  let later : Ir.Color := { r := 0x22, g := 0x33, b := 0x44 }
  let resetSrc := article
    "\\palette{ bg = #F7F7F7, accent = #445566 }\\pagecolor[HTML]{112233}"
    "\\palette{ accent = #AABBCC, later = #223344 }Painted page.\\pagebreak\\nopagecolor Reset page."
  let (resetDoc, resetDs) := elabStr resetSrc
  let resetGeom := Layout.Geom.ofPage resetDoc.page
  let resetOut := layoutOf oneFace resetDoc resetGeom
  let fullGround (page : Layout.PageOut) (c : Ir.Color) : Bool :=
    page.fills.any fun f => f.x == 0 && f.y == 0 && f.w == resetGeom.pageW &&
      f.h == resetGeom.pageH && f.color == c
  t "page colour reset is a palette epoch restoring the document ground"
    (resetDs.all (fun d => d.severity != .error && d.code != "W0301") &&
      (resetOut.pages[0]?).any (fullGround · painted) &&
      (resetOut.pages[1]?).any (fullGround · base))
  let resetPal := resetDoc.body.foldl (fun p b => match b with
    | .setPalette q => some q
    | _ => p) none
  t "page colour reset changes only the ground and keeps later palette reads"
    (resetPal.bind (·.find? "bg") == some base &&
      resetPal.bind (·.find? "accent") == some accent &&
      resetPal.bind (·.find? "later") == some later)
  let (resetHead, resetBody, _) := HtmlDoc.emitTree {} resetDoc
  let resetRootCss := resetHead.foldl (fun css n => match n with
    | .style s => css ++ s
    | _ => css) ""
  let resetStyles := elemStylesList #[] resetBody.toList
  t "the typed HTML root paints the preamble ground and the reset epoch restores it"
    (hasStr resetRootCss "--ltx-bg: #112233" &&
      resetStyles.any (fun (text, style) => hasStr text "Reset page" &&
        !hasStr text "Painted page" && hasStr style "--ltx-bg: #f7f7f7" &&
        hasStr style "background: var(--ltx-bg"))
  let (clearDoc, clearDs) := elabStr (article ""
    "\\pagecolor[HTML]{112233}Painted clear page.\\pagebreak\\nopagecolor Default clear page.")
  let clearGeom := Layout.Geom.ofPage clearDoc.page
  let clearOut := layoutOf oneFace clearDoc clearGeom
  let (_, clearBody, _) := HtmlDoc.emitTree {} clearDoc
  let clearStyles := elemStylesList #[] clearBody.toList
  t "page colour reset restores an undeclared class ground without inventing white"
    (clearDs.all (fun d => d.severity != .error && d.code != "W0301") &&
      (clearOut.pages[0]?).any (fun p => p.fills.any (·.color == painted)) &&
      (clearOut.pages[1]?).any (·.fills.isEmpty))
  t "typed HTML restores the registry ground in an epoch with no declared document ground"
    (clearStyles.any fun (text, style) => hasStr text "Default clear page" &&
      !hasStr text "Painted clear page" &&
      hasStr style ("--ltx-bg: " ++ HtmlDoc.cssColor (screenColor .light .page)) &&
      hasStr style "background: var(--ltx-bg")
  let (samePageDoc, samePageDs) := elabStr (article ""
    "\\pagecolor[HTML]{112233}Earlier text. \\nopagecolor same paragraph.\\pagebreak Later text.")
  let samePageOut := layoutOf oneFace samePageDoc (Layout.Geom.ofPage samePageDoc.page)
  let samePageParas := samePageDoc.body.filter (· matches .para _)
  t "the last page-ground epoch before shipout controls the whole current page"
    (samePageDs.all (·.code != "W0301") && samePageParas.size == 2 &&
      (samePageOut.pages[0]?).any (·.fills.isEmpty) &&
      (samePageOut.pages[1]?).any (·.fills.isEmpty))

/-- `\vspace{\fill}` and `\vfill` share the page's leftover as TeX's first-order infinite glue. -/
def filChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let linesOf (src : String) : Array Layout.LineOut :=
    allLines (layoutOf oneFace (elabStr src).1 geom)
  let doc (body : String) : String :=
    s!"\\documentclass\{article}\\begin\{document}{body}\\end\{document}"
  let top := linesOf (doc "hello")
  -- `\nointerlineskip` before the anchor, as the centring idiom writes it.
  let mid := linesOf (doc "\\nointerlineskip\\vspace*{\\fill}\nhello\n\\vspace*{\\fill}")
  let low := linesOf (doc "\\nointerlineskip\\vspace*{\\fill}\nhello")
  t "the fill sandwich centres its page"
    (match mid[0]? with
     | some b =>
       let (h, d) := Layout.segsInk oneFace b.segs
       ((b.y - h - geom.bodyTop - Dim.pt 10) - (geom.bodyBottom - (b.y + d))).abs ≤ Dim.Length.quantum
     | none => false)
  t "a leading fill alone pushes content to the bottom"
    (match low[0]?, mid[0]? with
     | some c, some b => c.y > b.y
     | _, _ => false)
  t "a line closing a bottom-flushed page stands on the floor, its depth below it"
    ((low[0]?.map (·.y == geom.bodyBottom)).getD false)
  t "a trailing fill alone moves nothing"
    ((linesOf (doc "hello\n\\vspace*{\\fill}")).map (·.y) == top.map (·.y))
  let spaced (body : String) : String :=
    "\\documentclass{article}\\setlength{\\topsep}{7pt}\\setlength{\\partopsep}{0pt}" ++
      s!"\\begin\{document}{body}\\end\{document}"
  let viaTrivlist := linesOf (spaced
    "\\vspace*{\\fill}\n\\begin{center}hello\\end{center}\n\\vspace*{\\fill}")
  let viaSkips := linesOf (spaced
    "\\vspace*{\\fill}\\vspace{7pt}\n\nhello\n\n\\vspace{7pt}\\vspace*{\\fill}")
  t "a fill before a trivlist's space keeps its share of the page"
    (!viaTrivlist.isEmpty && viaTrivlist.map (·.y) == viaSkips.map (·.y))
  t "minipage is one column of its declared width"
    (match (elabStr (doc "\\begin{minipage}{0.5\\textwidth}x\\end{minipage}")).1.body with
     | #[.columns #[(w, #[.para #[.text "x"]])]] =>
       w.resolve geom.textWidth == some (geom.textWidth / 2)
     | _ => false)
  t "a bare textwidth minipage takes the whole measure"
    (match (elabStr (doc "\\begin{minipage}{\\textwidth}x\\end{minipage}")).1.body with
     | #[.columns #[(w, #[.para #[.text "x"]])]] =>
       w.resolve geom.textWidth == some geom.textWidth
     | _ => false)
  t "minipage alignment options are a note, never an error"
    (let ds := (elabStr (doc "\\begin{minipage}[c][2cm][t]{\\textwidth}x\\end{minipage}")).2
     ds.all (·.severity != .error) && ds.any (·.code == "N0102"))
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
      == some { width := .ofLength (Dim.pt 4) })
  t "a preamble-only declaration in the body is W0340, not unknown"
    (let ds := (elabStr (doc "x\n\n\\page{ size = a5 }\n\ny")).2
     ds.any (·.code == "W0340") && ds.all (·.code != "W0301") &&
       ds.all (·.severity != .error))
  let (cdoc, cds) := elabStr
    "\\documentclass{article}\\definecolor{ink}{cmyk}{0,.6,.4,.2}\
\\begin{document}\\textcolor{ink}{x}\\end{document}"
  t "a cmyk definecolor lands in the palette with its components"
    (cds.all (·.severity != .error) && cds.all (·.code != "W0102") &&
      cdoc.palette.find? "ink" == some (Ir.Color.ofCmyk 0 600 400 200))
  t "the cmyk screen preview follows xcolor's cmyk-to-rgb conversion"
    (Ir.Color.ofCmyk 0 600 400 200 ==
      { r := 204, g := 51, b := 102, cmyk := some (0, 600, 400, 200) })
  let cpdf := pdfText (Pdf.write geom oneFace (layoutOf oneFace cdoc geom).pages cdoc.info)
  t "the pdf paints a cmyk colour in DeviceCMYK, components as declared"
    (bytesContain cpdf "0 0.6 0.4 0.2 k")
  t "the html backend converts, explicitly, to the preview"
    (((HtmlDoc.emit {} cdoc).1.splitOn
        (HtmlDoc.cssColor (Ir.Color.ofCmyk 0 600 400 200))).length ≥ 2 &&
      HtmlDoc.cssColor (Ir.Color.ofCmyk 0 600 400 200) == "#cc3366")
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

/-- The band projection reports every ink interval inside the band, whatever the outline's shape. -/
def inkGeometryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let iv (cmds : Array Ink.Cmd) (minY : Int) : Array (Int × Int) :=
    Ink.bandIntervals ⟨cmds, minY⟩ (-100) (-50)
  let floatRectCmds : Array Ink.Cmd := #[.move 100 (-60), .line 200 (-60),
    .line 200 (-70), .line 100 (-70)]
  let floatRect := iv floatRectCmds (-70)
  t "ink: contour wholly inside the band is covered"
    (floatRect.size == 1 && floatRect.all fun (lo, hi) => lo ≤ 100 && hi ≥ 200)
  let tallRectCmds : Array Ink.Cmd := #[.move 300 0, .line 400 0,
    .line 400 (-200), .line 300 (-200)]
  let tallRect := iv tallRectCmds (-200)
  t "ink: contour spanning the band covers its full width"
    (tallRect.size == 1 && tallRect.all fun (lo, hi) => lo ≤ 300 && hi ≥ 400)
  -- The control point puts an unforced flattener's k=4 chord vertex on the band's midline scanline.
  let curvedSpanCmds : Array Ink.Cmd := #[.move 300 0, .line 400 0,
    .quad 405 (-49) 400 (-200), .line 300 (-200)]
  let curvedSpan := iv curvedSpanCmds (-200)
  t "ink: curve-sided contour spanning the band covers its full width"
    (curvedSpan.size == 1 && curvedSpan.all fun (lo, hi) => lo ≤ 300 && hi ≥ 400)
  let dipCmds : Array Ink.Cmd := #[.move 500 (-60), .quad 550 (-90) 600 (-60)]
  let dip := iv dipCmds (-75)
  t "ink: curve extremum reports the whole lens extent"
    (dip.size == 1 && dip.all fun (lo, hi) => lo ≤ 502 && hi ≥ 598)
  let slantCmds : Array Ink.Cmd := #[.move 700 (-40), .line 750 (-110),
    .line 770 (-110), .line 720 (-40)]
  let slant := iv slantCmds (-110)
  t "ink: slanted stroke is one gap-free interval"
    (slant.size == 1 && slant.all fun (lo, hi) => lo ≤ 709 && hi ≥ 761)
  t "ink: contour above the band is empty"
    ((iv #[.move 0 0, .line 50 0, .line 50 (-40), .line 0 (-40)] (-40)).isEmpty)
  t "ink: contour below the band is empty"
    ((iv #[.move 0 (-120), .line 50 (-120), .line 50 (-160), .line 0 (-160)]
      (-160)).isEmpty)
  -- Independent oracle: Float flattening at 32 chords, half-open crossings, 2 units of slack.
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
  -- Each glyph's yMin dips below the band, so the header shortcut cannot mask the decode.
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
  -- A composite whose header bbox (yMin 0) hides a component reaching y −200.
  let g0 : Array UInt8 :=
    -- one contour, bbox (0,−200)–(100,0), 4 on-curve points
    #[0, 1,  0, 0,  0xFF, 0x38,  0, 100,  0, 0,
      0, 3,  0, 0,
      0x31, 0x33, 0x15, 0x23,
      100, 100, 200,
      0]  -- pad to even length for short loca
  let g1 : Array UInt8 :=
    -- numberOfContours −1, bbox yMin 0, one component: glyph 0, xy args (0,0), no MORE_COMPONENTS.
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

/-- Links carry an underline in both backends, and a native underline is interrupted wherever glyph
ink crosses its band. -/
def linkSignalChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let out := layoutOf oneFace
    (Elab.run "t" "see \\href{https://example.org/}{the example} here").1 geom
  let segs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  let linkRuns := segs.filterMap fun s => match s with
    | .run _ _ (some _) _ _ _ _ decorations _ _ _ => some decorations.underline
    | _ => none
  t "pdf link runs exist" (!linkRuns.isEmpty)
  t "pdf link runs are underlined" (linkRuns.all (· == true))
  t "pdf link draws its underline rule" (segs.any fun s => match s with
    | .decoration .underline .. => true
    | _ => false)

def underlineChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font) : IO Unit := do
  let t := check ref
  t "underline ir shape" ((elabStr "\\underline{a}").1.body ==
    #[.para #[.decorated .underline #[.text "a"]]])
  t "uline is underline" ((elabStr "\\uline{b}").1.body ==
    #[.para #[.decorated .underline #[.text "b"]]])
  let gidOf (c : Char) : Nat := (font.gid c).getD 0
  let hasInk (c : Char) : Bool := !(font.inkAt (gidOf c)).isEmpty
  t "g has ink in the band" (hasInk 'g')
  t "y has ink in the band" (hasInk 'y')
  -- Per-face, not a theorem: `underline_in_descent` covers only the position.
  let shipped ← FontDiscovery.scanRoots [testFonts]
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
  let qAdv : Int := font.widths[gidOf 'q']?.getD 0
  let qInk := font.inkAt (gidOf 'q')
  t "q ink is a narrow interval, not the advance"
    (qInk.size == 1 && qInk.all fun (lo, hi) =>
      lo > qAdv / 2 && hi - lo < qAdv / 3)
  t "g ink is two intervals" ((font.inkAt (gidOf 'g')).size == 2)
  let cedAdv : Int := font.widths[gidOf 'ç']?.getD 0
  let cedInk := font.inkAt (gidOf 'ç')
  t "composite ç ink is the cedilla, not the advance"
    (cedInk.size == 1 && cedInk.all fun (lo, hi) => lo > 0 && hi < cedAdv)
  let t0 ← IO.monoMsNow
  let mut inkReads := 0
  for _ in [0:100000] do
    inkReads := inkReads + (font.inkAt (gidOf 'q')).size
  let inkMs := (← IO.monoMsNow) - t0
  t "100000 repeated glyph ink reads each read the glyph's one interval" (inkReads == 100000)
  t s!"hang guard: 100000 repeated glyph ink reads within {hangGuardMs 5} ms ({inkMs} ms)"
    (inkMs < hangGuardMs 5)
  let outOf (fs : Font.FontSet) (src : String) : Layout.Out :=
    layoutOf fs (Elab.run "t" src).1 geom
  let rulesOf (fs : Font.FontSet) (src : String) : Array (Dim.Length × Dim.Length) :=
    ((outOf fs src).pages.flatMap (·.lines)).flatMap (·.segs.filterMap fun s =>
      match s with
      | .decoration .underline w th _ _ _ => some (w, th)
      | _ => none)
  let widthOf (fs : Font.FontSet) (src : String) : Dim.Length :=
    (((outOf fs src).pages.flatMap (·.lines))[0]?.map (·.setWidth)).getD 0
  let coverage (fs : Font.FontSet) (src : String) : Dim.Length × Dim.Length :=
    ((rulesOf fs src).foldl (fun acc (w, _) => acc + w) (0 : Dim.Length),
     widthOf fs src)
  t "underline emits a rule" ((rulesOf oneFace "\\underline{ab}").size ≥ 1)
  t "plain text emits no rule" ((rulesOf oneFace "ab").isEmpty)
  t "underline splits around a descender" ((rulesOf oneFace "\\underline{aqa}").size ≥ 2)
  let (aqaRules, aqaWidth) := coverage oneFace "\\underline{aqa}"
  t "underline leaves a gap at the descender" (0 < aqaRules && aqaRules < aqaWidth)
  let (qRules, qWidth) := coverage oneFace "\\underline{q}"
  t "underlined q keeps rule under its bowl" (qRules > qWidth * 2 / 5)
  t "underlined q still clears its stem" (qRules < qWidth)
  let (gyRules, gyWidth) := coverage oneFace "\\underline{gy}"
  t "underline under gy keeps some rule" (0 < gyRules && gyRules < gyWidth)
  t "underline splits at a comma" ((rulesOf oneFace "\\underline{a,a}").size ≥ 2)
  let (genRules, genWidth) := coverage oneFace "\\underline{genuinely}"
  t "genuinely keeps most of its rule"
    ((rulesOf oneFace "\\underline{genuinely}").size ≥ 3 &&
     genRules > genWidth / 2 && genRules < genWidth)
  let abLines := bodyLines (outOf oneFace "\\underline{ab}")
  t "underline rules ride a second line at the same y"
    (abLines.size == 2 && abLines[0]!.y == abLines[1]!.y &&
     abLines[1]!.segs.all fun s => match s with
      | .run .. => false
      | _ => true)
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
          let firstRunAndRule (src : String) : Dim.Length × Dim.Length := Id.run do
            let lines := ((outOf mixedSet src).pages.flatMap (·.lines))
            let runW := ((lines[0]?.map (·.segs)).getD #[]).filterMap fun s =>
              match s with
              | .run _ _ _ w _ _ _ _ _ _ _ => some w
              | _ => none
            let ruleW := ((lines[1]?.map (·.segs)).getD #[]).filterMap fun s =>
              match s with
              | .decoration .underline w _ _ _ _ => some w
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
  match ← findFont with
  | some fontData =>
    let patched := Id.run do
      let mut d := fontData
      match Ink.findTable d "post" with
      | some post =>
        -- post offsets 8 and 10: underlinePosition +200, underlineThickness -80 (FWords).
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
          | .decoration .underline w th raise _ _ => some (w, th, raise)
          | _ => none)
      t "band: absurd post metrics still rule below the baseline"
        (badRules.size ≥ 1 && badRules.all fun (w, th, raise) =>
          w > 0 && th > 0 && raise < 0)
  | none => pure ()
  let (uPage, _) := HtmlDoc.emit {} (elabStr "\\underline{x}").1
  t "html underline is u" ((uPage.splitOn "<u>x</u>").length == 2)
  t "html u skips ink"
    ((uPage.splitOn "u { text-decoration: underline; text-decoration-skip-ink: auto;").length == 2)
  t "html links skip ink" ((uPage.splitOn "text-decoration-skip-ink").length ≥ 3)
  t "compat ul" ((elabStr "\\ul{x}").1.body == #[.para #[.decorated .underline #[.text "x"]]])
  t "compat varul drops its options"
    ((elabStr "\\varul<5>[0.2ex][0.1ex]{x}").1.body ==
      #[.para #[.decorated .underline #[.text "x"]]])
  t "compat varul without options"
    ((elabStr "\\varul{x}").1.body == #[.para #[.decorated .underline #[.text "x"]]])
  t "compat soul is a note"
    ((elabStr ("\\documentclass{article}\\usepackage{soul}" ++
      "\\begin{document}x\\end{document}")).2.all (·.severity == .note))
  let redef := elabStr ("\\documentclass{article}" ++
    "\\NewDocumentCommand{\\varul}{ O{} m }{#2}" ++
    "\\begin{document}\\varul{y}\\end{document}")
  t "document varul definition is ignored"
    ((redef.2.filter (·.severity == .warning)).any (·.code == "W0303") &&
     redef.1.body == #[.para #[.decorated .underline #[.text "y"]]])

/-- Display math stands where TeX sets it: the display skips, their short forms and the interline
glue, measured from the baselines. -/
def displayTexChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fs ← mathSetOf oneFace
  let linesOf (body : String) : Array Layout.LineOut :=
    ((layoutOf fs (elabStr (dvDoc "" body)).1).pages.flatMap (·.lines)).filter fun l =>
      !l.furniture && l.segs.any (· matches .run ..)
  let geom := Layout.Geom.ofPage (elabStr (dvDoc "" "Alpha.")).1.page
  let size := geom.fontSize
  let bs := Ir.leadingFor size geom.leading
  let sk := Ir.displaySkipsAt size
  let w (g : Dim.SymGlue) : Dim.Length := (g.resolve size 0).width
  let texPar := (geom.texParskip.resolve size 0).width
  let depth (l : Layout.LineOut) : Dim.Length := (Layout.segsInk fs l.segs).2
  let height (l : Layout.LineOut) : Dim.Length := (Layout.segsInk fs l.segs).1
  let step (xs : Array Layout.LineOut) (i : Nat) : Dim.Length := xs[i + 1]!.y - xs[i]!.y
  let long := "Alpha words run on long enough to pass the display."
  let three (ls : Array Layout.LineOut) : Bool := ls.size == 3
  let l1 := linesOf (long ++ "\n\\[ x = 1 \\]\nBravo words.")
  t "a display after a long line stands the long skip and the leading below it"
    (three l1 && step l1 0 == w sk.above + bs)
  t "the line after a display stands the skip below and the leading under it"
    (three l1 && step l1 1 == w sk.below + bs)
  let s1 := linesOf "Alpha.\n\\[ x = 1 \\]\nBravo."
  t "a display after a line ending left of it takes the short skips"
    (three s1 && step s1 0 == w sk.aboveShort + bs && step s1 1 == w sk.belowShort + bs)
  let sub := linesOf (long ++ "\n\\[ x_{i} = 1 \\]\nBravo words.")
  t "a subscript under the leading moves no baseline: the baselines stand the leading apart"
    (three sub && step sub 0 == w sk.above + bs && step sub 1 == w sk.below + bs)
  let deep := linesOf (long ++ "\n\\[ \\sum_{i=1}^{n} x_{i} \\]\nBravo words.")
  t "a display taller than the leading leaves allows stands its box a lineskip below the line"
    (three deep && depth deep[0]! + height deep[1]! > bs &&
      step deep 0 == w sk.above + depth deep[0]! + Ir.inkClearance + height deep[1]!)
  t "the line under a deep display stands a lineskip below the display's box"
    (three deep && depth deep[1]! + height deep[2]! > bs &&
      step deep 1 == w sk.below + depth deep[1]! + Ir.inkClearance + height deep[2]!)
  t "the baseline distance across a display is TeX's interline rule on both sides"
    (three deep && step deep 0 == w sk.above + Layout.texBaselineGap bs (depth deep[0]!)
        (height deep[1]!) &&
      step deep 1 == w sk.below + Layout.texBaselineGap bs (depth deep[1]!) (height deep[2]!))
  let opens := linesOf "Alpha words.\n\n\\[ x = 1 \\]\nBravo words."
  t "a display opening a paragraph stands below the empty line amsmath sets, on the short skip"
    (three opens && step opens 0 == texPar + bs + w sk.aboveShort + bs &&
      step opens 1 == w sk.belowShort + bs)
  let ends := linesOf (long ++ "\n\\[ x = 1 \\]\n\nBravo words.")
  t "a paragraph break after a display stacks TeX's parskip on its skip"
    (three ends && step ends 1 == w sk.below + texPar + bs)
  let eq := linesOf (long ++ "\n\\begin{equation} x = 1 \\end{equation}\nBravo words.")
  t "a numbered equation stands as a display does"
    (three eq && step eq 0 == w sk.above + bs && step eq 1 == w sk.below + bs)
  let eqs := linesOf "Alpha.\n\\begin{equation} x = 1 \\end{equation}\nBravo."
  t "a numbered equation reads the short skips off its formula's edge, not its number's"
    (three eqs && step eqs 0 == w sk.aboveShort + bs)
  let al := linesOf "Alpha.\n\\begin{align*} x &= 1 \\end{align*}\nBravo."
  t "an alignment after a short line takes the long skips"
    (three al && step al 0 == w sk.above + bs && step al 1 == w sk.below + bs)
  let tok := linesOf ("\\tokens{ abovedisplayshortskip = 5pt, belowdisplayshortskip = 7pt }" ++
    "Alpha.\n\\[ x = 1 \\]\nBravo.")
  t "declared short skips are the ones a short display pays"
    (three tok && step tok 0 == Dim.pt 5 + bs && step tok 1 == Dim.pt 7 + bs)
  let pOf (body : String) : Array Layout.LineOut :=
    ((layoutOf fs (elabStr (dvDoc "\\setlength{\\parskip}{5pt}\n" body)).1).pages.flatMap
      (·.lines)).filter fun l => !l.furniture && l.segs.any (· matches .run ..)
  let pOpens := pOf "Alpha words.\n\n\\[ x = 1 \\]\nBravo words."
  t "a display opening a paragraph pays the declared parskip before its empty line"
    (three pOpens && step pOpens 0 == Dim.pt 5 + bs + w sk.aboveShort + bs &&
      step pOpens 1 == w sk.belowShort + bs)
  let pEnds := pOf (long ++ "\n\\[ x = 1 \\]\n\nBravo words.")
  t "a paragraph break after a display pays the declared parskip on its skip"
    (three pEnds && step pEnds 0 == w sk.above + bs && step pEnds 1 == w sk.below + Dim.pt 5 + bs)
  let pRuns := pOf (long ++ "\n\\[ x = 1 \\]\nBravo words.")
  t "the text a display runs on into pays no parskip"
    (three pRuns && step pRuns 1 == w sk.below + bs)
  let vsp := linesOf (long ++ "\n\n\\vspace{10pt}\n\\[ x = 1 \\]\nBravo words.")
  t "a display opening a paragraph after a vspace sets the empty line, the vspace glue above it"
    (three vsp && step vsp 0 == Dim.pt 10 + bs + w sk.aboveShort + bs)
  let dd := linesOf "Alpha.\n\\[ a = 0 \\]\n\n\\[ x = 1 \\]\nBravo."
  t "a display opening a paragraph after a display sets its empty line over the first's skip below"
    (dd.size == 4 && step dd 1 == w sk.belowShort + bs + w sk.aboveShort + bs)
  let listend := linesOf "\\begin{itemize}\\item A\\end{itemize}\n\\[ x = 1 \\]\nBravo."
  let listpar := linesOf "\\begin{itemize}\\item A\\end{itemize}\n\n\\[ x = 1 \\]\nBravo."
  let vsp2 := linesOf "Alpha words.\n\n\\vspace{10pt}\n\\[ x = 1 \\]\nBravo words."
  t "a display right after a list end sets no empty line, one amsmath sets after an equal vspace"
    (listend.size == 3 && vsp2.size == 3 && step vsp2 0 == step listend 0 + bs)
  t "a display after a list end and a blank line sets the empty line"
    (listpar.size == 3 && step listpar 0 == step listend 0 + bs)
  let listParCtrl := linesOf "\\begin{itemize}\\item A\\end{itemize}\n\\par\n\\[ x = 1 \\]\nBravo."
  t "a display after a list end and an explicit \\par sets the empty line"
    (listParCtrl.size == 3 && step listParCtrl 0 == step listpar 0)
  let amsLines (body : String) : Array Layout.LineOut :=
    ((layoutOf fs (elabStr (dvDoc "\\usepackage{amsthm}\n\\newtheorem{theorem}{Theorem}\n" body)).1).pages.flatMap
      (·.lines)).filter fun l => !l.furniture && l.segs.any (· matches .run ..)
  let thmEnd := amsLines "\\begin{theorem}A\\end{theorem}\n\\[ x = 1 \\]\nBravo."
  let thmPar := amsLines "\\begin{theorem}A\\end{theorem}\n\n\\[ x = 1 \\]\nBravo."
  t "a display right after an amsthm theorem sets the empty line, as after a blank line"
    (thmEnd.size == thmPar.size && thmEnd.size ≥ 3 &&
      (thmEnd.zip thmPar).all fun (a, b) => a.y == b.y)
  let ctrlNo := linesOf "Alpha words.\n\\vspace{3pt}\n\\[ x = 1 \\]\nBravo."
  let ctrlBlank := linesOf "Alpha words.\n\n\\vspace{3pt}\n\n\\[ x = 1 \\]\nBravo."
  t "a vspace with no blank line after it opens the display's empty line, as a blank line would"
    (ctrlNo.size == 3 && ctrlBlank.size == 3 && step ctrlNo 0 == step ctrlBlank 0 &&
      step ctrlNo 0 == Dim.pt 3 + bs + w sk.aboveShort + bs)
  let pVsp := pOf (long ++ "\n\n\\vspace{10pt}\n\\[ x = 1 \\]\nBravo words.")
  t "a display opening after a vspace pays the declared parskip before its empty line"
    (three pVsp && step pVsp 0 == Dim.pt 10 + Dim.pt 5 + bs + w sk.aboveShort + bs)

/-- Vertical spacing is TeX's, checked on the placed lines. -/
def spacingChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font) : IO Unit := do
  let t := check ref
  let ysOf (g : Layout.Geom) (src : String) : Array Dim.Length :=
    -- Text lines only: an underline rule rides a sibling line at the same y.
    ((layoutOf oneFace (Elab.run "t" src).1 g).pages.flatMap (·.lines)).filterMap fun l =>
      if !l.furniture &&
          l.segs.any (fun s => match s with | .run .. => true | _ => false) then some l.y else none
  let pagesOf (g : Layout.Geom) (src : String) : Nat :=
    (layoutOf oneFace (Elab.run "t" src).1 g).pages.size
  let body := geom.fontSize
  let leading := Ir.leadingFor body geom.leading
  let scaled (sz : Dim.Length) (units : Int) : Dim.Length := units * sz / font.unitsPerEm
  let leadedAt (sz : Dim.Length) (step : Option String := none) : Dim.Length × Dim.Length :=
    Layout.leadedBox (scaled sz font.ascent) (scaled sz (-font.descent))
      (Ir.stepSkip (step.bind (Ir.stepLead Ir.sizeSkipScale · body)) sz geom.leading)
  let plain := ysOf geom "a\n\nb"
  t "peers sit a leading plus parskip apart"
    (plain.size == 2 && plain[1]! - plain[0]! == leading + (geom.parskip.resolve body 0).width)
  let commented := ysOf geom "a\n  % an aside\n\n  b"
  t "peers stay peers across a comment line before the blank line"
    (commented.size == 2 && commented[1]! - commented[0]! == plain[1]! - plain[0]!)
  let dispSkip := (Ir.displaySkipDefault body).resolve body 0
  t "the display skip is not the peer gap"
    (dispSkip.width != (geom.parskip.resolve body 0).width)
  let inlineDisp := ysOf geom "a $x$ b\n\nc"
  t "an inline formula opens no display skip"
    (inlineDisp.size == 2 &&
      inlineDisp[1]! - inlineDisp[0]! == leading + (geom.parskip.resolve body 0).width)
  let huge := ysOf geom "{\\Huge Title \\par}\n\nbody"
  let hugeSize := body * 2488 / 1000
  t "a Huge title ends one paragraph, not two lines" (huge.size == 2)
  t "the line after a Huge title is spaced by the metric rule"
    (huge.size == 2 && (huge[1]! - huge[0]! -
      ((leadedAt hugeSize (some "Huge")).2 + (leadedAt body).1 +
        (geom.parskip.resolve body 0).width)).abs ≤ Dim.Length.quantum)
  t "the line after a Huge title is not a Huge leading away"
    (huge.size == 2 && huge[1]! - huge[0]! < Ir.leadingFor hugeSize geom.leading)
  let hugeBox := ((layoutOf oneFace (Elab.run "t" "{\\Huge Title \\par}\n\nbody").1 geom).pages[0]?.bind
    fun p => p.lines.find? fun l => !l.furniture).map fun l => (Layout.segsInk oneFace l.segs).1
  t "the first line stands on its own glyph box below the margin, taller than \\topskip"
    (huge.size == 2 && hugeBox.any fun h =>
      body < h && huge[0]! == geom.vmargin + h)
  let uni := ysOf geom (String.intercalate " " (List.replicate 60 "grid"))
  t "uniform baselines sit on the grid"
    (uni.size ≥ 3 && (uni.zip (uni.extract 1 uni.size)).all
      (fun (a, b) => b - a == leading))
  let mixed := ysOf geom ("{\\Huge M} " ++
    String.intercalate " " (List.replicate 60 "grid"))
  t "a size change displaces by the metric rule and leaves the grid"
    (mixed.size ≥ 3 && mixed[1]! - mixed[0]! == (leadedAt hugeSize).2 + (leadedAt body).1 &&
     mixed[1]! - mixed[0]! != leading && mixed[2]! - mixed[1]! == leading)
  let rdoc := (Elab.run "t" ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink }\\begin{document}\\section{S}x\\end{document}")).1
  let ruleRaises := ((layoutOf oneFace rdoc geom).pages.flatMap (·.lines)).filterMap
    fun l => if l.furniture then none else
      l.segs.findSome? fun s => match s with
        | .rule _ _ raise _ _ => if raise > 0 then some raise else none
        | _ => none
  t "the heading rule sits at half the heading's own x-height"
    (ruleRaises ==
      #[(font.xHeightOptical : Int) * Layout.sectionSize geom 1 / font.unitsPerEm / 2])
  let firstRule (d : Ir.Doc) : Array (Dim.Length × Dim.Length) :=
    ((layoutOf oneFace d geom).pages.flatMap (·.lines)).filterMap
      fun l => if l.furniture then none else
        l.segs.findSome? fun s => match s with
          | .rule _ th raise _ _ => some (th, raise)
          | _ => none
  let komaRule := (Elab.run "t" ("\\documentclass{scrartcl}\\definecolor{ink}{HTML}{112233}" ++
    "\\makeatletter\\renewcommand\\sectionlinesformat[4]{#3#4 \\textcolor{ink}{\\leaders\\hrule height 2pt\\hfill}}\\makeatother" ++
    "\\begin{document}\\section{S}x\\end{document}")).1
  t "a TeX hrule heading rule sits on the baseline at its declared height"
    (firstRule komaRule == #[(Dim.pt 2, (0 : Dim.Length))])
  let nativeBaseline := (Elab.run "t" ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink, rule-position = baseline, rule-thickness = 2pt }" ++
    "\\begin{document}\\section{S}x\\end{document}")).1
  t "a native baseline rule is the same Layout.Out fact"
    (firstRule nativeBaseline == firstRule komaRule)
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
        | .rule _ th raise _ _ => some (th, raise)
        | _ => none) == some (Dim.pt 1, 0))
  t "the synthetic hero page sets title, two contact lines, section, entry"
    (heroLines.size == 5 && (heroLines.zip (heroLines.extract 1 heroLines.size)).all
      fun (a, b) => a.y < b.y)
  let pq := Ir.rhythmQuantum geom.fontSize
  let vs := ysOf geom "a\n\n\\vspace{20pt}\nb"
  t "a bare vspace adds to parskip"
    (vs.size == 2 && vs[1]! - vs[0]! == leading + pq + Dim.pt 20)
  let plain := ysOf geom "a\n\nb"
  let gapOf (mid : String) : Option Dim.Length :=
    let ys := ysOf geom ("a\n\n" ++ mid ++ "\nb")
    if ys.size == 2 then some (ys[1]! - ys[0]!) else none
  let plainGap : Option Dim.Length :=
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
    (sec.size == 3 && ((sec[1]! - sec[0]!) -
      ((leadedAt body).2 + (leadedAt (Layout.sectionSize geom 1)).1 + Dim.pt 15)).abs ≤
        Dim.Length.ofSp 1)
  let g0 := ysOf { geom with parskip := { width := Dim.SymLength.ofLength 0 } } "a\n\nb"
  t "parskip zero sets peers one leading apart" (g0.size == 2 && g0[1]! - g0[0]! == leading)
  let (pDoc, pDs) := elabStr ("\\documentclass{article}\\page{ parskip = 3pt plus 1pt minus 1pt }" ++
    "\\begin{document}x\\end{document}")
  t "page parskip declared" (pDs.isEmpty && pDoc.page.parskip ==
    some { width := Dim.SymLength.ofLength (Dim.pt 3), stretch := Dim.SymLength.ofLength (Dim.pt 1),
           shrink := Dim.SymLength.ofLength (Dim.pt 1) })
  let firstY := geom.vmargin + body
  let three := "a\n\n\\vspace{20pt minus 8pt}\nb\n\n\\vspace{20pt minus 8pt}\nc"
  let natural := firstY + 2 * (leading + pq + Dim.pt 20) + scaled body (-font.descent)
  let tight : Layout.Geom := { geom with pageH := natural - Dim.pt 10 + geom.bottomMargin }
  t "within its shrink the page holds" (pagesOf tight three == 1)
  let ys := ysOf tight three
  t "the shrunk page moves later lines up, in proportion"
    (ys.size == 3 && ys[0]! == firstY && ys[2]! < firstY + 2 * (leading + pq + Dim.pt 20) &&
      ys[1]! - ys[0]! == leading + pq + Dim.pt 20 - Dim.pt 5 &&
      ys[2]! - ys[1]! == leading + pq + Dim.pt 20 - Dim.pt 5)
  t "a shrunk page says so"
    ((layoutOf oneFace (Elab.run "t" three).1 tight).diags.any (·.code == "N0200"))
  let tooTight : Layout.Geom := { geom with pageH := natural - Dim.pt 20 + geom.bottomMargin }
  t "beyond its shrink the page breaks" (pagesOf tooTight three == 2)
  t "an unshrunk page says nothing"
    (!(layoutOf oneFace (Elab.run "t" three).1 geom).diags.any (·.code == "N0200"))
  let alignSrc (al : String) := "\\documentclass{article}" ++
    (if al.isEmpty then "" else "\\style{abstract}{ align = " ++ al ++ " }") ++
    "\\begin{document}\\begin{abstract}Placeholder abstract body.\\end{abstract}" ++
    "Body text.\\end{document}"
  let alignX (al : String) : Option Dim.Length :=
    let (d, _) := elabStr (alignSrc al)
    lineXOf (censusOf (coveredColorsOf d) (layoutOf oneFace d geom)) 0 "Abstract"
  match alignX "left", alignX "", alignX "right" with
  | some l, some c, some rgt =>
    t "a declared alignment moves the heading's origin: left, centre, right"
      (decide (l < c) && decide (c < rgt))
    t "an undeclared abstract heading keeps the class's centred origin"
      (decide (l < c))
  | _, _, _ => t "the alignment probe produced its heading" false

/-- Title bars stand their declared gap from the type's body: the cap line above the text, the
baseline below it. -/
def titleBarChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font) : IO Unit := do
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
  let cap : Dim.Length := (font.capHeight : Int) * titleSize / font.unitsPerEm
  let probe (last : String) : Option (Dim.Length × Dim.Length × Nat) := do
    let lines := bodyLines (layoutOf oneFace (Elab.run "t" (src last)).1 tg)
    let bars := lines.filter (fun l => Layout.ruleOnly l.segs)
    let titles := lines.filter (fun l => !Layout.ruleOnly l.segs && l.size == titleSize)
    let bar1 ← bars[0]?
    let bar2 ← bars[1]?
    let firstT ← titles[0]?
    let lastT ← titles.back?
    let th2 ← bar2.segs.findSome? fun s => match s with
      | .rule _ th _ _ _ => some th | _ => none
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

/-- Recovery ships the author's content, never the source's syntax: an unknown command's leading
`[...]` run never reaches the page, and every `{...}` group survives. -/
def recoveryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let pageText (src : String) : String := pageTextOf oneFace src (some geom)
  let has := hasStr
  let url := pageText "\\textls[16]{placeholder}.example.org"
  t "an unknown command's option run ships no character"
    (!has url "[" && !has url "]" && !has url "16")
  t "the kept group stays fused to what follows it"
    (has url "placeholder.example.org")
  let mail := pageText "\\textls[16]{someone}@example.org"
  t "an option run before an email address ships nothing"
    (!has mail "[" && has mail "someone@example.org")
  let lsDiags := dvE "\\textls[16]{placeholder}.example.org"
  let lsCodes := lsDiags.foldl
    (fun acc d => if acc.contains d.code then acc else acc.push d.code) (#[] : Array String)
  t "the command's span carries exactly one code"
    (lsCodes == #["W0301"] && lsDiags.size == 1)
  t "and that code is counted, so a reader can size the loss"
    (lsDiags.all fun d => d.subject == some "ctrl:textls")
  let par := pageText "\\zzz[c][2cm]{alpha}{beta}"
  t "consecutive option runs all go with the command"
    (!has par "[" && !has par "2cm" && has par "alpha beta")
  let open_ := pageText "\\foo[16 oops"
  t "an unclosed bracket run stays on the page"
    (has open_ "[16 oops" &&
     (warnCodes "\\foo[16 oops").contains "W0310")
  let later := pageText "\\foo\n[note] stays"
  t "a bracket run on the next line is content"
    (has later "[note] stays")
  t "no space is fabricated after a kept group"
    (pageText "\\foo{a}.b" == "a.b")
  t "a written space after a kept group survives"
    (pageText "\\foo{a} b" == "a b")
  t "a starred unknown command drops its options too"
    (let s := pageText "\\foo*[1]{x}"; s == "x")
  let deg := pageText "$\\overset{?}{=}$"
  t "a degraded formula ships no control sequence"
    (!has deg "\\" && !has deg "{" && !has deg "}" && !has deg "overset")
  t "a degraded formula keeps its text content"
    (has deg "?" && has deg "=")
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
  t "no space survives a dropped command"
    (pageText "$\\overset{k\\phantom{hidden}}{y}$" == "ky")
  t "a formula with no content characters ships the declared placeholder"
    (pageText "$\\overset{\\alpha}{\\beta}$" == "[…]")
  let col := pageText "$\\overset{\\textcolor{indigo}{q}}{=}$"
  t "a degraded formula ships no colour name"
    (!has col "indigo" && !has col "textcolor" && has col "q")
  let tab := pageText "\\begin{align*} \\overset{a}{b} &= c_d \\end{align*}"
  t "a degraded alignment ships no tab or script mark"
    (!has tab "&" && !has tab "_" && !has tab "\\" && has tab "c")
  t "the no-math-face floor ships no control sequence"
    (let s := pageText "$\\alpha^2$"
     !has s "\\" && !has s "alpha" && has s "2")

/-- The recovery floor is a function of the declared `Loss`, judged page by page against
`Ir.FloorHonest`. -/
def floorPolicyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pageText (src : String) : String := pageTextOf oneFace src (some ({} : Layout.Geom))
  let has := hasStr
  t "exactly the degraded codes owe the reader ink"
    (DiagCode.all.all fun c => c.floor.inks == (c.loss == .degraded))
  t "a floor that owes ink is a floor that ships"
    (DiagCode.all.all fun c => !c.floor.inks || c.floor.ships)
  t "the codes with no content operand owe no ink and ship none"
    (DiagCode.all.all fun c =>
      (c.loss != .config && c.loss != .info) || (!c.floor.ships && !c.floor.inks))
  t "every all-markup formula ships the declared placeholder"
    ([ "$\\overset{\\alpha}{\\beta}$", "$\\overset{\\gamma}{\\delta}$",
       "$\\overset{\\phantom{x}}{\\alpha}$", "$\\overset{\\label{k}}{\\beta}$" ].all
      fun src => pageText src == "[…]")
  t "no degraded formula ships LaTeX punctuation"
    ([ "$\\overset{a+b}{c}$", "$\\overset{\\textcolor{teal}{p}}{q}$",
       "$\\overset{\\alpha}{\\beta}$", "$\\overset{x_1}{y^2}$" ].all
      fun src =>
        let s := pageText src
        !has s "\\" && !has s "{" && !has s "}" && !has s "$" &&
        !has s "&" && !has s "^" && !has s "_" && !has s "~")
  t "a markup-only source carried no content"
    (!Ir.floorCarries "\\overset{\\alpha}{\\beta}" &&
     !Ir.floorCarries "\\," && !Ir.floorCarries "{}")
  t "a source with a content character carried content"
    (Ir.floorCarries "\\overset{abc}{d}" && Ir.floorCarries "x")
  t "a space-only formula inks nothing, and carried nothing to ink"
    (pageText "$\\,$" == "" && !Ir.floorCarries "\\,")
  t "a formula with one digit inks it without a math face"
    (pageText "$\\,2$" == "2")
  t "the parsed floor ships the brace glyph its author spelled"
    (let s := pageText "$\\{x\\}$"; has s "{" && has s "}" && !has s "\\")
  t "a known command's index option never reaches the page"
    (pageText "$\\overset{a}{b}\\sqrt[3]{8}$" == "ab8")
  t "an unknown command's option run never reaches the page"
    (pageText "$\\overset{a}{b}\\zzz[opt]{x}$" == "abx")
  t "an option run after a command with no group goes too"
    (pageText "$\\overset{\\alpha[1]z}{y}$" == "zy")
  t "a bracket run following no command stays on the page"
    (pageText "$\\overset{[0,1]}{y}$" == "[0,1]y")
  t "a bracket run opening a formula stays on the page"
    (pageText "$\\overset{a}{b}[2,3]$" == "ab[2,3]")

/-- An unrenderable construct costs itself, not the formula around it. -/
def mathContainChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf oneFace
  let mathText (src : String) : String := pageTextOf mathSet src (some ({} : Layout.Geom))
  let has := hasStr
  let disp := "\\begin{align*} P_u = Q_u \
+ \\raisebox{1pt}{\\sum_{k} R_{uk}} + \\sum_{km} G_{ukm} \\end{align*}"
  let d := mathText disp
  t "a big operator beside an unmodelled construct still sets as mathematics"
    (has d "\u2211")
  t "both of the display's big operators survive one unmodelled addend"
    ((d.splitOn "\u2211").length == 3)
  t "the display's variables set as math italic, not as body letters"
    (has d "𝑃" && has d "𝑄" && !has d "P" && !has d "Q")
  t "a contained construct leaks no markup onto the page"
    (!has d "\\" && !has d "{" && !has d "}" && !has d "&")
  t "containment names the construct by its own code"
    ((warnCodes disp).contains "W0389" && !(warnCodes disp).contains "W0012")
  let one := mathText "$\\raisebox{1pt}{x}$"
  t "a contained construct ships its content operand as mathematics"
    (has one "𝑥")
  t "a contained construct does not ship its naming argument"
    (!has one "1" && !has one "pt")
  t "a construct with two content operands degrades the formula whole"
    (mathText "$\\overset{a}{b}$" == "ab" &&
     (warnCodes "$\\overset{a}{b}$").contains "W0012")
  t "a single operand is not enough where nothing ruled on it"
    ((warnCodes "$\\zzz{q}$").contains "W0012" &&
     !(warnCodes "$\\zzz{q}$").contains "W0389")
  t "a misplaced alignment tab still degrades the formula whole"
    ((warnCodes "$a & b$").contains "W0012")
  let sup := mathText "$\\raisebox{1pt}{y} + z^2$"
  t "a script beside a contained construct is still a script"
    (has sup "2" && has sup "𝑧")
  -- `structuralCtrl` is a list beside a `match`: each name on it must still reach a parse arm.
  let structuralParses (n : String) : Bool :=
    let src := match n with
      | "over" => "$a \\over b$"
      | "genfrac" => "$\\genfrac{(}{)}{0pt}{}{a}{b}$"
      | "left" | "right" => "$\\left( a \\right)$"
      | "limits" => "$\\sum\\limits_k a$"
      | "nolimits" => "$\\sum\\nolimits_k a$"
      | "textcolor" => "$\\textcolor{teal}{a}$"
      | "color" => "$\\color{teal}a$"
      | "cancelto" => "$\\cancelto{0}{a}$"
      | "ensuremath" => "$\\ensuremath{a}$"
      | _ => s!"$\\{n}\{a}$"
    let cs := warnCodes src
    !cs.contains "W0012" && !cs.contains "W0389"
  t "every structurally read control word still reaches its parse arm"
    (MathParse.structuralCtrl.all structuralParses)

/-- Beamer's frame options select the vertical split, the default centres, and a titled frame's
page-top chrome never moves with the body. -/
def vdistChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let linesOf (src : String) : Array Layout.LineOut :=
    allLines (layoutOf oneFace (elabStr src).1 geom)
  let firstY (body : String) : Dim.Length :=
    ((linesOf (deck169Body body))[0]?.map (·.y)).getD 0
  let yT := firstY "\\begin{frame}[t]\nhello\n\\end{frame}"
  let yC := firstY "\\begin{frame}\nhello\n\\end{frame}"
  let yB := firstY "\\begin{frame}[b]\nhello\n\\end{frame}"
  t "a frame centres by default, [t] sits above it" (yT < yC)
  t "[b] sits below the centre" (yC < yB)
  -- beamer centres with fills of 1 above and 1.5 below; `Dim.mm 2` is its `.2cm` top skip.
  t "centre is two fifths of the way between [t] less its top skip and [b]"
    (yC - (yT - Dim.mm 2) == (yB - (yT - Dim.mm 2)) * 1000 / 2500)
  t "[t] opens beamer's top skip and one baselineskip below the paper's top"
    (yT == Dim.mm 2 + Ir.leadingFor geom.fontSize geom.leading && yT < firstY "hello")
  let textYs (body : String) : Array Dim.Length :=
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
  t "[t,standout] is a standout frame, centred as moloch's key centres it"
    ((elabStr (deck169Body "\\begin{frame}[t,standout]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] true .center false #[.para #[.text "x"]]])
  let titled (opt : String) : String :=
    deck169Body ("\\begin{frame}" ++ opt ++ "{Head}\nbody text\n\\end{frame}")
  let tLines := linesOf (titled "[t]")
  let cLines := linesOf (titled "")
  t "a titled frame has title and body lines" (tLines.size ≥ 2 && cLines.size ≥ 2)
  t "the title never moves with the distribution"
    (((tLines[0]?).map (·.y)) == ((cLines[0]?).map (·.y)))
  t "the body distributes below the title"
    ((((tLines[1]?).map (·.y)).getD 0) < (((cLines[1]?).map (·.y)).getD 0))
  let barH (opt : String) : Dim.Length :=
    let src := "\\documentclass[aspectratio=169]{slides}\n" ++
      "\\palette{frametitlebg = #23373B}\n\\begin{document}\n" ++
      "\\begin{frame}" ++ opt ++ "{Head}\nbody text\n\\end{frame}\n\\end{document}"
    (((layoutOf oneFace (elabStr src).1 geom).pages.flatMap
      (·.fills))[0]?.map (·.h)).getD 0
  t "the title bar keeps its height under centring" (barH "" == barH "[t]")
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
       inner.size ≥ 2 && inner.any (fun b => match b with
         | .rule _ (some (.color "sep")) _ => true
         | .spaced _ #[.rule _ (some (.color "sep")) _] => true
         | _ => false) && !inner.any (fun b => match b with
         | .center _ => true
         | _ => false)
     | _ => false)
  t "the separator sets as a full-measure rule"
    ((linesOf styledSrc).any fun l => l.segs.any fun sg =>
      match sg with
      | .rule w _ _ _ _ => w == geom.textWidth
      | _ => false)
  let deckTitleSrc := "\\documentclass[aspectratio=169]{slides}\n\\theme{moloch}\n" ++
    "\\begin{document}\n\\title{Alpha Beta}\\author{Pat Placeholder}\n" ++
    "\\maketitle\n\\end{document}"
  let deckTitleSize := Ir.scaleStepIn Ir.sizeScale geom.fontSize "Large"
  t "a deck title sets at the bundle's declared step, not the flow fallback"
    ((linesOf deckTitleSrc).any (·.size == deckTitleSize) &&
      !(linesOf deckTitleSrc).any (·.size == Ir.scaleStepIn Ir.sizeScale geom.fontSize "LARGE"))
  -- The share is scale-free, so it is read from how fast the block moves as its height grows.
  let titleBlock (extra : String) : Option (Dim.Length × Dim.Length) := do
    let ls := (linesOf ("\\documentclass[aspectratio=169]{slides}\n\\theme{moloch}\n" ++
      "\\begin{document}\n\\title{Alpha" ++ extra ++ "}\\author{Pat Placeholder}\n" ++
      "\\maketitle\n\\end{document}")).filter (!·.furniture)
    let first ← ls[0]?
    let last ← ls.back?
    return (first.y, last.y - first.y)
  match titleBlock "", titleBlock "\\\\ Beta\\\\ Gamma\\\\ Delta" with
  | some (y1, span1), some (y2, span2) =>
    let (above, below) := Ir.VAlign.golden.shares .moloch
    let predicted := y1 - (span2 - span1) * above / (above + below)
    t "the title page's block grew" (span1 < span2)
    t "the title page splits its leftover by the composed golden share"
      ((y2 - predicted).abs ≤ 2 * Dim.Length.quantum)
  | _, _ => t "the title page's split probe produced its blocks" false
  let slotted (title yshift : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\style{titlepage}{ slot = { set = title, anchor = west, at = west, xshift = 20pt }, " ++
    "slot = { set = author, anchor = south west, at = south west, xshift = 20pt, " ++
    "yshift = " ++ yshift ++ ", inner-sep = 0pt } }\n" ++
    "\\begin{document}\n\\title{" ++ title ++ "}\\author{Pat Placeholder}\n" ++
    "\\maketitle\n\\end{document}"
  let slotLines (src : String) := (linesOf src).filter (!·.furniture)
  let one := slotLines (slotted "Alpha" "30pt")
  let three := slotLines (slotted "Alpha\\\\ Beta\\\\ Gamma" "30pt")
  let lifted := slotLines (slotted "Alpha" "40pt")
  t "a pinned title starts inside both inner and outer sep"
    (one[0]?.any (·.x == Dim.pt 20 + Ir.pgfInnerSep geom.fontSize + Ir.pgfOuterSep))
  t "zero inner sep keeps pgf's outer anchor clearance"
    (one.back?.any (·.x == Dim.pt 20 + Ir.pgfOuterSep))
  t "a larger yshift lifts a bottom-pinned slot by exactly the difference"
    (match one.back?, lifted.back? with
     | some a, some b => a.y - b.y == Dim.pt 10
     | _, _ => false)
  t "a west-anchored title keeps its shipped-ink vertical middle as it grows"
    (match one[0]?, three[0]?, three[2]? with
     | some a, some f, some l =>
       let (ah, ad) := Layout.segsInk oneFace a.segs
       let (fh, _) := Layout.segsInk oneFace f.segs
       let (_, ld) := Layout.segsInk oneFace l.segs
       (2 * (a.y - ah) + ah + ad - ((f.y - fh) + (l.y + ld))).abs ≤ 2 * Dim.Length.quantum
     | _, _, _ => false)
  t "a slotted title page ships no separator and no golden flow"
    (one.size == 2 && one.all fun l => l.segs.all fun sg => !(sg matches .rule ..))
  let brokenSrc := "\\documentclass[aspectratio=169]{slides}\n\\theme{moloch}\n" ++
    "\\begin{document}\n\\title{Alpha beta gamma\\\\ \\quad delta epsilon zeta}" ++
    "\\author{Pat Placeholder}\n\\maketitle\n\\end{document}"
  let titleLines := (linesOf brokenSrc).filter fun l =>
    !l.furniture && l.size == deckTitleSize
  t "a declared two-line title stays two lines"
    (titleLines.size == 2)
  let firstRunWidth (l : Layout.LineOut) : Option Dim.Length :=
    l.segs.findSome? fun sg => match sg with
      | .run _ _ _ w _ _ _ _ _ _ _ => some w
      | _ => none
  t "the declared second line keeps its indent"
    ((do
      let a ← titleLines[0]?
      let b ← titleLines[1]?
      let wa ← firstRunWidth a
      let wb ← firstRunWidth b
      return wb == deckTitleSize && wa != deckTitleSize : Option Bool).getD false)
  let ownGeomYs (src : String) : Array Dim.Length :=
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

/-- With a top margin too small for the head line, body ink still starts `inkClearance` below the
head's ink, and at the default margins the band is zero. -/
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
  let scale (u : Int) : Dim.Length := u * geom.fontSize / (font.unitsPerEm : Int)
  let headY := geom.vmargin / 2 + scale font.ascent
  t "the tight-margin page ships its head line" (lines.any fun l => l.y == headY)
  let headBottom := headY + scale (-font.descent)
  let bodyInkTops := lines.filterMap fun l =>
    if l.y == headY then none else some (l.y - scale font.capHeight)
  t "body ink clears the head's ink by the clearance floor under a tight margin"
    (!bodyInkTops.isEmpty &&
      bodyInkTops.all fun top => headBottom + Ir.inkClearance ≤ top)
  let dflt (head : Bool) : Option Dim.Length := Id.run do
    let src := "\\documentclass{article}" ++
      (if head then "\\runninghead{Invented Notes}" else "") ++
      "\\begin{document}Body text at the default margin.\\end{document}"
    let (doc, _) := elabStr src
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom
    let lines := (out.pages[0]?.map (·.lines)).getD #[]
    return (lines.filter (!·.furniture))
      |>.foldl (fun acc l => match acc with
        | none => some l.y
        | some y => some (min y l.y)) none
  t "the default margin reserves no band: the body does not move"
    (dflt true == dflt false && (dflt false).isSome)
  -- The shipped faces sit inside the two-em bound `slides_lines_survive_bands` assumes.
  for name in ["OpenSans-Regular.ttf", "SourceSerifPro-Regular.otf",
               "SourceCodePro-Regular.otf"] do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f =>
      t s!"{name} line ink stays under two em"
        (f.ascent + (-f.descent) ≤ 2 * (f.unitsPerEm : Int))
    | .error e => failures ref s!"headBand font parse {name}: {e}"

/-- Every page ships its declared head and foot at the geometry's own baselines, the short last page
included. -/
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
  let scale (u : Int) : Dim.Length := u * geom.fontSize / (font.unitsPerEm : Int)
  let a := scale font.ascent
  let d := scale (-font.descent)
  let band := Layout.furnitureBand geom.vmargin (a + d) none
  -- article.cls's `\headsep` and `\footskip`.
  let headY := (furnYs font geom (some (Layout.furnGapOfSep (Dim.pt 25) d))).1
  let footY := geom.pageH - geom.bottomMargin + Dim.pt 30
  t "every page ships its head and foot at the class's own baselines"
    (out.pages.all fun p =>
      p.lines.any (fun l => l.furniture && l.y == headY) &&
      p.lines.any (fun l => l.furniture && l.y == footY))
  let bodyBottom := geom.pageH - geom.bottomMargin - band.band
  t "the first page fills its body area"
    ((out.pages[0]?.map fun p => p.lines.any fun l =>
      !l.furniture && l.y + d + Ir.leadingFor geom.fontSize > bodyBottom).getD false)
  t "the short last page keeps its foot in place"
    ((out.pages.back?.map fun p =>
      p.lines.any (fun l => l.furniture && l.y == footY) &&
      p.lines.all (fun l => l.furniture || l.y + d + Ir.leadingFor geom.fontSize ≤ bodyBottom))
      |>.getD false)
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
  let dHeadY := (furnYs font dGeom (some dGap)).1
  let dFootY := dGeom.pageH - dGeom.bottomMargin + Dim.pt 20
  t "declared seps place the head and the foot as LaTeX reads them"
    (dOut.pages.all fun p =>
      p.lines.any (fun l => l.furniture && l.y == dHeadY) &&
      p.lines.any (fun l => l.furniture && l.y == dFootY))
  let dFurn := ((dOut.pages[0]?.map fun p => (p.lines.filter (·.furniture)).map (·.y)).getD #[])
  t "the declared seps are honoured exactly on the page, baseline to text area"
    (match dFurn[0]? with
     | some y0 =>
       (dGeom.vmargin + dBand.band) - dFurn.foldl min y0 == Dim.pt 20 &&
         dFurn.foldl max y0 - (dGeom.pageH - dGeom.bottomMargin) == Dim.pt 20
     | none => false)
  t "equal declared seps carry no note" (!dOut.diags.any (·.code == "N0021"))
  let (nDoc, _) := elabStr (declPre "\\page{ headsep = 20pt, footskip = 30pt }")
  let nOut := layoutOf oneFace nDoc
  t "differing declared seps are named as declared, once"
    ((nOut.diags.filter (·.code == "N0021")).size == 1 &&
      nOut.diags.all fun dg => dg.code != "N0021" || dg.severity == .note)
  let (fDoc, _) := elabStr (declPre "\\page{ furnituregap = 12pt }")
  let fGeom := Layout.Geom.ofPage fDoc.page
  let fOut := layoutOf oneFace fDoc fGeom
  let (fHeadY, fFootY) := furnYs font fGeom (some (Dim.pt 12))
  t "the native furnituregap places both sides"
    (fOut.pages.all fun p =>
      p.lines.any (fun l => l.furniture && l.y == fHeadY) &&
      p.lines.any (fun l => l.furniture && l.y == fFootY))
  t "the native gap carries no note" (!fOut.diags.any (·.code == "N0021"))

/-- The default `plain` page style numbers every page once in its footer band, and the documented
exceptions carry no number. -/
def pageNumberChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let build (src : String) : Layout.Out × Layout.Geom :=
    let (doc, _) := elabStr src
    let geom := Layout.Geom.ofPage doc.page
    (layoutOf oneFace doc geom, geom)
  let footTexts (out : Layout.Out) (geom : Layout.Geom) (i : Nat) : Array String :=
    ((out.pages[i]?.map (·.lines)).getD #[]).filterMap fun l =>
      if l.furniture && l.y > geom.pageH - geom.bottomMargin then
        some (lineText l (gapAsSpace := false))
      else none
  let threeBody := "One.\\pagebreak Two.\\pagebreak Three."
  let (out, geom) := build (dvDoc "" threeBody)
  t "plain numbers every page: three pages ship" (out.pages.size == 3)
  for i in [0:3] do
    t s!"plain numbers every page: page {i + 1} ships exactly its own number"
      (footTexts out geom i == #[toString (i + 1)])
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
  let (emptyOut, emptyGeom) := build (dvDoc "\\thispagestyle{empty}" threeBody)
  t "thispagestyle empty on page 1 ships no number there"
    (footTexts emptyOut emptyGeom 0 == #[])
  t "and every page after the first keeps exactly its own number"
    (footTexts emptyOut emptyGeom 1 == #["2"] && footTexts emptyOut emptyGeom 2 == #["3"])

/-- A declared `\footskip` runs baseline to baseline, from the text area's floor to the foot's
baseline. -/
def footskipChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (pre : String) : String :=
    "\\documentclass{article}\\usepackage{geometry}" ++ pre ++
    "\\begin{document}Alpha words.\n\nBravo words.\n\\end{document}"
  let drop (s : String) : Option Dim.Length := do
    let (doc, _) := elabStr s
    let g := Layout.Geom.ofPage doc.page
    let foot ← ((layoutOf oneFace doc).pages[0]?).bind (·.lines.find? (·.furniture))
    pure (foot.y - (g.pageH - g.bottomMargin))
  for fs in [12, 30, 60] do
    t s!"a declared footskip of {fs}pt sets the foot's baseline that far below the text area"
      (drop (src s!"\\geometry\{letterpaper, textheight=9in, footskip={fs}pt}") ==
        some (Dim.pt fs))
  t "the native \\page key reads footskip as the geometry key does"
    (drop (src "\\page{ footskip = 20pt }") == some (Dim.pt 20))
  t "\\setlength{\\footskip} is read, not only noted"
    (drop (src "\\geometry{letterpaper, textheight=9in}\\setlength{\\footskip}{45pt}") ==
      some (Dim.pt 45))
  let headAt (s : String) : Option Dim.Length := do
    let (doc, _) := elabStr s
    let g := Layout.Geom.ofPage doc.page
    let p ← (layoutOf oneFace doc).pages[0]?
    let ys := (p.lines.filter (·.furniture)).map (·.y)
    let top ← ys[0]?
    pure (g.vmargin - ys.foldl min top)
  t "\\setlength{\\headsep} is read, not only noted"
    (headAt ("\\documentclass{article}\\runninghead{Invented Notes}\\setlength{\\headsep}{30pt}" ++
      "\\begin{document}Alpha words.\n\\end{document}") == some (Dim.pt 30))
  t "a page geometry places hangs its foot the standard class's 30pt footskip below the text"
    (drop (src "\\geometry{letterpaper, textheight=9in}") == some (Dim.pt 30))
  let native := "\\documentclass{article}\\page{ size = letter, textheight = 9in }" ++
    "\\begin{document}Alpha words.\n\nBravo words.\n\\end{document}"
  let (bare, _) := elabStr native
  let bg := Layout.Geom.ofPage bare.page
  t "kept: an undeclared footskip hangs the foot from half the margin"
    (drop native == some ((furnYs oneFace.body bg).2 - (bg.pageH - bg.bottomMargin)))

/-- A LaTeX class's body lines stand its size file's `\normalsize` baselineskip apart, within the
leading factor's thousandth, and a native class's at the 6⁄5 rule. -/
def classLeadingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let words := String.intercalate " " (List.replicate 120 "invented")
  let pitch (cls : String) (pre : String := "") (size : String := "") : Option Dim.Length := do
    let (doc, _) := elabStr (s!"\\documentclass{cls}\n{pre}\\begin\{document}\n{size}" ++ words ++
      "\n\\end{document}\n")
    let body := ((((layoutOf oneFace doc).pages[0]?).map (·.lines)).getD #[]).filter (!·.furniture)
    let a ← body[0]?
    let b ← body[1]?
    pure (b.y - a.y)
  let near (p : Option Dim.Length) (want : Dim.Length) : Bool :=
    p.any fun p => (p - want).abs ≤ want / 1000
  -- lualatex: `\the\baselineskip` 12pt, 13.6pt and 14.5pt under size10, size11 and size12.clo.
  for (cls, size) in [("[10pt]{article}", 10), ("[11pt]{article}", 11), ("[12pt]{report}", 12),
      ("{scrartcl}", 11), ("[12pt]{scrreprt}", 12)] do
    t s!"class leading: {cls}'s lines stand its size file's baselineskip apart ({reprStr (pitch cls)})"
      (near (pitch cls) (Ir.sizeFileLeading (Dim.pt size) 1000 "normalsize"))
  -- lualatex: `\huge` sets its baselineskip at 25pt under size11.clo, not 2.5 of the body's 11pt.
  t s!"class leading: an 11pt class's \\huge lines stand 25pt apart ({reprStr (pitch "[11pt]{article}" "" "\\huge ")})"
    (near (pitch "[11pt]{article}" "" "\\huge ") (Dim.pt 25))
  -- lualatex: setspace's one-and-a-half and double spacing are 1.5 and 2 of the size at 11pt and 12pt.
  t "class leading: setspace's spacings stand 1.5 and 2 of an 11pt or 12pt size apart"
    (near (pitch "[11pt]{article}" "\\usepackage{setspace}\n\\onehalfspacing\n") (Dim.pt 33 / 2) &&
      near (pitch "{scrartcl}" "\\usepackage[onehalfspacing]{setspace}\n") (Dim.pt 33 / 2) &&
      near (pitch "[12pt]{article}" "\\usepackage{setspace}\n\\doublespacing\n") (Dim.pt 24))
  -- lualatex: a redefined \small leaves the class's other sizes as its size file sets them.
  t "class leading: one redefined size leaves the size file's other rows"
    (near (pitch "[11pt]{article}" "\\makeatletter\n\\renewcommand\\small{\\@setfontsize\\small{10}{12}}\n")
      (Dim.pt 136 / 10))
  t "class leading: the resume class keeps the 6/5 rule"
    (pitch "[fontsize=11pt]{resume}" == some (Ir.leadingFor (Dim.pt 11)))

/-- The strut box a preamble length reads stands as the class set it, `.7` and `.3` of its
`\baselineskip` in TeX's arithmetic, and where the preamble may have set it again the length is
named and dropped. -/
def strutLengthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (cls pre : String) : String :=
    s!"\\documentclass{cls}\\usepackage\{geometry}" ++ pre ++
    "\\begin{document}Alpha words.\n\nBravo words.\n\\end{document}"
  let drop (s : String) : Option Dim.Length := do
    let (doc, _) := elabStr s
    let g := Layout.Geom.ofPage doc.page
    let foot ← ((layoutOf oneFace doc).pages[0]?).bind (·.lines.find? (·.furniture))
    pure (foot.y - (g.pageH - g.bottomMargin))
  let lost (s : String) : Bool :=
    (elabStr s).2.any fun d => d.code == "W0101" || d.code == "W0107"
  let quarter := Dim.inch 1 / 4
  let geo := "\\geometry{letterpaper, textheight=9in, footskip=\\dimexpr 0.25in + \\ht\\strutbox\\relax}"
  -- lualatex: `\the\ht\strutbox` 8.39996pt, 9.51996pt and 10.14995pt, `\dp` 3.60004pt at 10pt.
  for (cls, htSp) in [("[10pt]{article}", (550500 : Int)), ("[11pt]{article}", 623900),
      ("[12pt]{report}", 665187), ("[11pt]{scrartcl}", 623900),
      ("[fontsize=12pt]{scrartcl}", 665187), ("{article}", 550500), ("{scrartcl}", 623900)] do
    let ht := Dim.Length.ofSp htSp
    t s!"strut: {cls}'s geometry footskip reads the class's strut height"
      ((drop (src cls geo)).map (·.toSp) == some (quarter + ht).toSp && !lost (src cls geo))
    t s!"strut: {cls}'s preamble \\setlength reads it too"
      (let s := src cls ("\\geometry{letterpaper, textheight=9in}\\setlength{\\footskip}" ++
        "{\\dimexpr 0.25in + \\ht\\strutbox\\relax}")
       (drop s).map (·.toSp) == some (quarter + ht).toSp && !lost s)
  let depth := src "[10pt]{article}"
    "\\geometry{letterpaper, textheight=9in, footskip=\\dimexpr 2\\dp\\strutbox\\relax}"
  t "strut: the depth reads as the class sets it" (drop depth == some (2 * Dim.Length.ofSp 235932) && !lost depth)
  let sum := src "[10pt]{article}"
    "\\geometry{letterpaper, textheight=9in, footskip=\\dimexpr 20pt + 10pt\\relax}"
  t "strut: geometry reads any dimexpr the length door reads" (drop sum == some (Dim.pt 30))
  let base := drop (src "[10pt]{article}" "\\geometry{letterpaper, textheight=9in}")
  for (cls, pre) in [("[10pt]{article}", "\\linespread{1.5}"),
      ("[10pt]{article}", "\\onehalfspacing"), ("[10pt]{article}", "\\fontsize{11}{14}\\selectfont"),
      ("[10pt]{article}", "\\small"), ("[10pt]{article}", "\\usepackage[onehalfspacing]{setspace}"),
      ("[10pt]{scrartcl}", "\\KOMAoptions{fontsize=12pt}"),
      ("[10pt]{article}", "\\renewcommand{\\baselinestretch}{1.5}"),
      ("[10pt]{article}", "\\setbox\\strutbox\\hbox{\\vrule height 20pt depth 4pt width 0pt}"),
      ("[10pt]{article}", "\\sbox\\strutbox{\\rule{0pt}{20pt}}"),
      ("[10pt]{article}", "\\savebox\\strutbox{\\rule{0pt}{20pt}}"),
      ("[9pt]{memoir}", ""), ("[14pt]{memoir}", "")] do
    let s := src cls (pre ++ geo)
    t s!"strut: after '{pre}' in {cls} the strut is not read, and the footskip is named and dropped"
      (lost s && (cls != "[10pt]{article}" || drop s == base))
  -- A length the page cannot resolve leaves its value named and the page shipped, as before any read.
  for value in ["footskip=\\dimexpr\\headheight+1pt\\relax", "footskip=\\dimexpr\\topskip\\relax",
      "footskip=\\dimexpr 0.5\\paperheight\\relax", "footskip=\\dimexpr 1in/2\\relax",
      "left=\\dimexpr 0.1\\paperwidth\\relax", "top=\\dimexpr\\headheight+1in\\relax",
      "footskip=\\dimexpr\\marginparwidth+\\oddsidemargin\\relax", "footskip=\\dimexpr 2em\\relax",
      "footskip=\\dimexpr 30pt+1ex\\relax", "footskip=\\dimexpr 20px\\relax"] do
    let s := src "[10pt]{article}" s!"\\geometry\{letterpaper, textheight=9in, {value}}"
    let (doc, ds) := elabStr s
    t s!"strut: geometry's '{value}' is named with its spelling and the page ships"
      (ds.all (·.severity != .error) && (layoutOf oneFace doc).pages.size == 1 &&
        ds.any fun d => d.code == "W0101" && hasStr (saidText d) "\\dimexpr")

/-- A chrome slot's box depends only on the declared layout and the geometry, priorities decide who
yields, and a yield stays in place and is named. -/
def bandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let longTok := String.ofList (List.replicate 20 "0123456789".toList).flatten
  let frame := "\\begin{frame}{F}\nx\n\\end{frame}"
  let run (left : String) : Layout.Out × Array CensusPage :=
    let (doc, _) := elabStr (deck169
      "\\theme{moloch}\\chrome{ footer = { left = \\sectiontitle } }\\title{T}\\author{A}"
      (s!"\\maketitle\n{left}{frame}"))
    let out := layoutOf oneFace doc
    (out, censusOf (coveredColorsOf doc) out)
  let numBox (c : Array CensusPage) (page : Nat) : Option (Dim.Length × Dim.Length) :=
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
      hasStr d.message "slot framenumber" && hasStr d.message "framefoot note")
  t "band: the yielding number is painted first, under the note"
    ((noteC[1]?.map fun p =>
      match p.lines.findIdx? (·.text == "1"),
            p.lines.findIdx? (fun l => hasStr l.text longTok) with
      | some ni, some ti => ni < ti
      | _, _ => false).getD false)
  let (secCollideOut, secCollideC) := run s!"\\section\{{longTok}}\n"
  t "band: the number yields to the section title by declared priority"
    (secCollideOut.diags.any fun d => d.code == "W0333" &&
      hasStr d.message "slot framenumber for sectiontitle")
  t "band: and holds the right margin while yielding"
    (numBox secCollideC 2 == numBox emptyC 1)

/-- A setting's effect is confined to its declared extent, and a misplaced native declaration is
named as misplaced, its arguments never shipped as ink. -/
def scopeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let doc (body : String) : String :=
    s!"\\documentclass\{article}\\begin\{document}\n{body}\n\\end\{document}"
  let censusOfSrc (src : String) : Array CensusPage :=
    let (d, _) := elabStr src
    censusOf (coveredColorsOf d) (layoutOf oneFace d geom)
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
  let runsOf (src : String) : Array (String × Ir.Color) :=
    let (d, _) := elabStr src
    let out := layoutOf oneFace d geom
    out.pages.flatMap fun p => p.lines.map fun l =>
      (lineText l,
       (l.segs.findSome? fun seg => match seg with
        | .run _ color _ _ _ _ _ _ _ _ _ => some color
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
  let (d2, _) := elabStr t2src
  let (head2, body2, _) := HtmlDoc.emitTree {} d2
  let headCss := head2.foldl (fun s n => match n with
    | .style css => s ++ css
    | _ => s) ""
  t "the html :root carries the epoch-0 palette value"
    (hasStr headCss "--ltx-accent: #1155cc" && !hasStr headCss "--ltx-accent: #cc1100")
  let styleAttrs (nodes : Array Html.Node) : Array (String × String) :=
    -- (own text, style attribute) of each top-level element, in order
    nodes.filterMap fun n => match n with
      | .elem _ attrs _ =>
        some (nodeTextOne "" n, ((attrs.find? (·.1 == "style")).map (·.2)).getD "")
      | _ => none
  let tops := body2.foldl (fun acc n => match n with
    | .elem "main" _ kids => acc ++ kids
    | _ => acc) #[]
  let roots2 := screenRootVars headCss
  let entries := (styleAttrs tops).map fun (x, st) => (x, lightStyleAll roots2 st)
  t "the html sibling before the declaration carries no epoch redefinition"
    ((entries.find? fun (txt, _) => hasStr txt "Early ink").map
      (fun (_, st) => !hasStr st "--ltx-accent") == some true)
  t "the html sibling after the declaration redefines the property on itself"
    ((entries.find? fun (txt, _) => hasStr txt "Late ink").map
      (fun (_, st) => hasStr st "--ltx-accent: #cc1100") == some true)
  let nestedSrc := doc
    "\\block{First inside.\n\n\\palette{ accent = #CC1100 }\n\nSecond inside.}\n\n\
\\textcolor{accent}{Outside after.}"
  let (d5, _) := elabStr nestedSrc
  let (head5, body5, _) := HtmlDoc.emitTree {} d5
  let roots5 := screenRootVars (treeCssList "" head5.toList)
  let els5 := (elemStylesList #[] body5.toList).map fun (x, st) => (x, lightStyleAll roots5 st)
  t "a nested epoch redefines the property on its later siblings"
    (els5.any fun (txt, st) => hasStr txt "Second inside" &&
      !hasStr txt "First inside" && hasStr st "--ltx-accent: #cc1100")
  t "a nested epoch never reaches the content before it"
    (els5.all fun (txt, st) => !(hasStr txt "First inside" &&
      !hasStr txt "Second inside" && hasStr st "--ltx-accent"))
  t "a nested epoch reaches the enclosing element's later siblings in html"
    (els5.any fun (txt, st) => hasStr txt "Outside after" &&
      !hasStr txt "First inside" && hasStr st "--ltx-accent: #cc1100")
  t "a nested epoch reaches the same later text in pdf"
    (colorOf (runsOf nestedSrc) "Outside after" == some post)
  let (dd, _) := elabStr ("\\documentclass{slides}\\palette{ accent = #1155CC }\
\\begin{document}\n\\framefoot{note}\n\\begin{frame}{A}\none\n\\end{frame}\n\n\
\\palette{ accent = #CC1100 }\n\n\\begin{frame}{B}\ntwo\n\\end{frame}\n\\end{document}")
  let (_, bodyd, _) := HtmlDoc.emitTree {} dd
  let elsd := elemStylesList #[] bodyd.toList
  t "a deck epoch redefines the property on the frames after it"
    (elsd.any fun (txt, st) => hasStr txt "two" && !hasStr txt "one" &&
      hasStr st "--ltx-accent: #cc1100")
  t "a deck epoch never reaches the frames before it"
    (elsd.all fun (txt, st) => !(hasStr txt "one" && !hasStr txt "two" &&
      hasStr st "--ltx-accent"))
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
  let codesOf := dvE
  let dsDark := codesOf (doc
    "\\palette{ bg = #202020, dim = #787878 }\n\n\\textcolor{dim}{dim words} here.")
  t "a use inside a dark-page epoch is judged on that page, and warns there"
    (dsDark.any fun d => d.code == "W0315" && hasStr (diagWords d) "#202020")
  t "a body epoch's defaulted ink on its declared page is W0330"
    ((codesOf (doc "x\n\n\\palette{ bg = #111111 }\n\ny")).any (·.code == "W0330"))
  let dsRedecl := codesOf ("\\documentclass{article}\
\\palette[decorative]{ q = #888888 }\\begin{document}\n\
\\textcolor{q}{quiet before} stays exempt.\n\n\\palette{ q = #888888 }\n\n\
\\textcolor{q}{loud after} is judged.\n\\end{document}")
  t "a plain body redeclaration removes the decorative exemption from here on"
    (dsRedecl.any fun d => d.code == "W0315" && hasStr d.message "colour q")
  let deckDoc (mid tail : String) : String :=
    "\\documentclass{slides}\\theme{moloch}\\begin{document}\n\
\\begin{frame}{A}\none\n\\end{frame}\n\n" ++ mid ++
    "\\begin{frame}{B}\ntwo\n\\end{frame}\n\n" ++ tail ++ "\\end{document}"
  t "a bad frame-title pair declared before a frame is judged for it"
    ((codesOf (deckDoc "\\palette{ frametitlebg = #555555, frametitlefg = #888888 }\n\n"
      "")).any
      fun d => d.code == "W0345" && hasStr (diagWords d) "the frame-title bar")
  t "a bad frame-title pair declared after the last frame styles nothing"
    ((codesOf (deckDoc "" "\\palette{ frametitlebg = #555555, frametitlefg = #888888 }\n\n")).all
      fun d => d.code != "W0345")
  let deckAlert (title body : String) : String :=
    "\\documentclass{slides}\\theme{moloch}\\palette{ alert = #AF5C00 }\\begin{document}\n\
\\begin{frame}{" ++ title ++ "}\n" ++ body ++ "\n\\end{frame}\n\\end{document}"
  t "an accent inside the frame title is judged on the bar, and warns there"
    ((codesOf (deckAlert "An \\alert{urgent} word" "plain body")).any
      fun d => d.code == "W0315" && hasStr (diagWords d) "the frame-title bar")
  t "the same accent in the body is judged on the page, and passes there"
    ((codesOf (deckAlert "A title" "an \\alert{urgent} word")).all
      fun d => d.code != "W0315")
  t "an accent inside a standout frame is judged on the inversion, and warns there"
    ((codesOf ("\\documentclass{slides}\\theme{moloch}\\palette{ alert = #AF5C00 }\
\\begin{document}\n\
\\begin{frame}[standout]\nan \\alert{urgent} word\n\\end{frame}\n\\end{document}")).any
      fun d => d.code == "W0315" && hasStr (diagWords d) "the standout frame")

/-- Tables and floats: the too-wide diagnostic, the caption's source side, and the rule extents on
the shipped page. -/
def tableChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrap (tab : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ tab ++ "\n\\end{document}"
  let layoutOut (src : String) : Layout.Out :=
    let doc := (elabStr src).1
    layoutOf oneFace doc
  let layoutDiags (src : String) : Array Diag := (layoutOut src).diags
  let pageTexts (out : Layout.Out) : Array String :=
    out.pages.map fun p => String.join (p.lines.toList.map fun l =>
      String.join (l.segs.toList.map fun s => match s with
        | .run _ _ _ _ glyphs _ _ _ _ _ _ => String.ofList (glyphs.toList.map (·.2.1))
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
  let affineTable := wrap
    "\\begin{tabular}{p{0.315\\dimexpr \\linewidth +36mm\\relax}}word word word word word word word word \\\\\\end{tabular}"
  t "an affine table column width parses once without a fallback"
    ((elabStr affineTable).2.all fun d =>
      d.severity != .error && d.code != "W0104" && d.code != "W0314")
  t "an affine table column ships wrapped lines on the page"
    (((bodyLines (layoutOut affineTable)).filter (!·.segs.isEmpty)).size >= 2)
  t "a caption written above its table stands above"
    (match (elabStr (wrap "\\begin{table}\\caption{Above}\\begin{tabular}{l}a\\\\\\end{tabular}\\end{table}")).1.body with
     | #[.float .table _ true _ cap] => Ir.plainText cap == "Above"
     | _ => false)
  t "a caption written below its table stands below"
    (match (elabStr (wrap "\\begin{table}\\begin{tabular}{l}a\\\\\\end{tabular}\\caption{Below}\\end{table}")).1.body with
     | #[.float .table _ false _ cap] => Ir.plainText cap == "Below"
     | _ => false)
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
  t "caption prefixes spell from the node"
    (Ir.captionPrefix Locale.en .figure (some 2) == some "Figure 2: " &&
     Ir.captionPrefix Locale.en .table (some 1) == some "Table 1: " &&
     Ir.captionPrefix Locale.en .sub (some 1) == some "(a) " &&
     Ir.captionPrefix Locale.en .sub (some 2) == some "(b) " &&
     Ir.captionPrefix Locale.de .figure (some 2) == some "Abbildung 2: " &&
     Ir.captionPrefix Locale.en .figure none == none)
  let subSrc := wrap ("\\begin{figure}\\centering\n" ++
    "\\begin{subfigure}[t]{0.4\\textwidth}\\centering\nleft panel\n" ++
    "\\caption{First sub}\\end{subfigure}\n\\hfill\n" ++
    "\\begin{subfigure}[t]{0.4\\textwidth}\\centering\nright panel\n" ++
    "\\caption{Second sub}\\end{subfigure}\n" ++
    "\\caption{The parent}\\end{figure}")
  t "subfigures elaborate to lettered sub floats in one columns row"
    (match (elabStr subSrc).1.body with
     | #[.float .figure (some ⟨"", 1, 0⟩) false inner cap] =>
       Ir.plainText cap == "The parent" &&
       (match inner with
        | #[.columns #[(w1, #[.float .sub (some ⟨"", 1, 0⟩) false _ c1]),
                       (w2, #[.float .sub (some ⟨"", 2, 0⟩) false _ c2])]] =>
          w1.pos == .first && w2.pos == .first &&
          w1.resolve (1000 * Dim.Length.quantum) == some (400 * Dim.Length.quantum) &&
          w2.resolve (1000 * Dim.Length.quantum) == some (400 * Dim.Length.quantum) &&
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
     | #[.float .figure (some ⟨"", 1, 0⟩) false i1 _, .float .figure (some ⟨"", 2, 0⟩) false i2 _] =>
       (match i1, i2 with
        | #[.columns #[(_, #[.float .sub (some ⟨_, n1, _⟩) _ _ _])]],
          #[.columns #[(_, #[.float .sub (some ⟨_, n2, _⟩) _ _ _])]] =>
          n1 == 1 && n2 == 1
        | _, _ => false)
     | _ => false)
  let subHtml := (HtmlDoc.emit {} (elabStr subSrc).1).1
  t "subfigures are nested figures with lettered figcaptions in HTML"
    ((subHtml.splitOn "<figure class=\"float subfloat\">").length == 3 &&
     (subHtml.splitOn "<figcaption>(a) First sub</figcaption>").length == 2 &&
     (subHtml.splitOn "<figcaption>(b) Second sub</figcaption>").length == 2 &&
     (subHtml.splitOn "<figcaption>Figure 1: The parent</figcaption>").length == 2)
  -- A 3pt sweep of the leading `\vspace` puts the seam at every position near the page bottom.
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
  let altFiller (tag : String) (rows reps : Nat) : String :=
    String.join ((List.range rows).map fun i =>
      tag ++ " " ++ toString i ++ " " ++
        String.join (List.replicate reps "band of body text ") ++ "\n\n")
  let altFrame (body : String) : String :=
    deck169 "\\theme{moloch}\\palette{ covered = 31\\% }"
      ("\\begin{frame}{Alternating}\n" ++ body ++ "\n\\end{frame}")
  let altSrc (a b : String) : String :=
    altFrame ("\\alt<2>{" ++ a ++ "}{" ++ b ++ "}")
  -- The stacked shape: the active group in range, the other before it.
  let stackSrc (a b : String) : String :=
    altFrame ("\\onslide<2>{" ++ a ++ "}\\onslide<1>{" ++ b ++ "}")
  let shipsMark (src mark : String) : Array Bool :=
    (pageTexts (layoutOut src)).map fun txt => (txt.splitOn mark).length > 1
  let spillTexts (src : String) : Array String :=
    ((layoutDiags src).filter (·.code == "W0384")).map fun d => d.message ++ " " ++ d.detail.getD ""
  let one := "Alphafill"
  let two := "Bravofill"
  let shortA := altFiller one 1 1
  let shortB := altFiller two 1 1
  t "alternation: each step page inks one group, where the stacked shape inks both"
    (shipsMark (altSrc shortA shortB) one == #[false, true] &&
     shipsMark (altSrc shortA shortB) two == #[true, false] &&
     shipsMark (stackSrc shortA shortB) one == #[true, true] &&
     shipsMark (stackSrc shortA shortB) two == #[true, true])
  t "alternation: a fitting frame ships one page per step, as the stack does"
    ((layoutOut (altSrc shortA shortB)).pages.size ==
       (layoutOut (stackSrc shortA shortB)).pages.size &&
     (layoutOut (altSrc shortA shortB)).pages.size == 2 &&
     (layoutOut (altFrame ("\\alt<3-4>{" ++ shortA ++ "}{" ++ shortB ++ "}" ++
       "\n\\pause\\pause\\pause"))).pages.size == 4)
  t "alternation: never more pages and never more spill accounts than the stack"
    ((List.range 9).all fun k =>
      let a := altFiller one (5 + 2 * k) 3
      let b := altFiller two (5 + 2 * k) 3
      (layoutOut (altSrc a b)).pages.size ≤ (layoutOut (stackSrc a b)).pages.size &&
        (spillTexts (altSrc a b)).size ≤ (spillTexts (stackSrc a b)).size)
  -- The groups spill by different amounts, so a wrong attribution cannot pass.
  let overA := altFiller one 20 3
  let overB := "{\\Large " ++ altFiller two 9 3 ++ "}"
  t "alternation: a step page's spill is the selected group's own, not the stack's"
    (spillTexts (altSrc overA overB) ==
       (spillTexts (altFrame overB)) ++ (spillTexts (altFrame overA)) &&
     (spillTexts (altFrame overA)).size == 1 &&
     (spillTexts (altFrame overB)).size == 1 &&
     spillTexts (altFrame overA) != spillTexts (altFrame overB) &&
     spillTexts (stackSrc overA overB) == spillTexts (altFrame overA))
  let figDoc (above : Bool) (decl : String := "") : String :=
    "\\documentclass{article}\n" ++ decl ++ "\\begin{document}\nbefore words\n\n" ++
    (if above then
      "\\begin{figure}\n\\caption{Caption words}\nBody line\n\\end{figure}"
     else
      "\\begin{figure}\nBody line\n\\caption{Caption words}\n\\end{figure}") ++
    "\n\nafter words\n\\end{document}"
  let deltas (src : String) : Option (Dim.Length × Dim.Length × Dim.Length) :=
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
  let doc := (elabStr (wrap ("\\begin{tabular}{ll}\\toprule\na & b \\\\ \\cmidrule(lr){2-2}\nc & d \\\\ \\bottomrule\\end{tabular}"))).1
  let out := layoutOf oneFace doc
  let ruleSegs : Array (Dim.Length × Dim.Length) := Id.run do
    let mut acc : Array (Dim.Length × Dim.Length) := #[]
    for p in out.pages do
      for l in p.lines do
        let mut x := l.x
        for s in l.segs do
          match s with
          | .rule w _ _ _ _ =>
            acc := acc.push (x, w)
            x := x + w
          | .gap g _ | .decoratedGap g _ _ => x := x + g
          | .decoration _ w _ _ _ _ => x := x + w
          | .run _ _ _ w _ _ _ _ _ _ _ => x := x + w
          | .image _ w _ _ _ _ => x := x + w
          | .poly _ _ => pure ()
    return acc
  t "the three rules ship" (ruleSegs.size == 3)
  t "toprule and bottomrule span the same extent"
    ((ruleSegs[0]?).isSome && ruleSegs[0]? == ruleSegs[2]?)
  t "the trimmed cmidrule lies strictly inside the full rules"
    (match ruleSegs[0]?, ruleSegs[1]? with
     | some (fx, fw), some (cx, cw) => decide (fx < cx && cx + cw < fx + fw)
     | _, _ => false)

/-- `\multicolumn` follows TeX's rule for a spanned entry: it enters no single column's maximum,
widens the last covered column by its excess, and sets across its columns by its own spec. -/
def multicolumnSpanChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let out (tab : String) : Layout.Out :=
    layoutOf oneFace (elabStr ("\\documentclass{article}\n\\begin{document}\n" ++ tab ++
      "\n\\end{document}")).1
  let topRule (o : Layout.Out) : Dim.Length := Id.run do
    for p in o.pages do
      for l in p.lines do
        if l.size == 0 then
          for sg in l.segs do
            if let .rule w _ _ _ _ := sg then
              return w
    return 0
  -- (measure edge, right ink edge) of page 0's first line holding `needle`.
  let extent (o : Layout.Out) (needle : String) : Option (Dim.Length × Dim.Length) := Id.run do
    for p in o.pages.extract 0 1 do
      for l in p.lines do
        if hasStr (lineText l) needle then
          let w := l.segs.foldl (fun a s => match s with
            | .run _ _ _ w .. => a + w
            | .gap w _ => a + w
            | .decoratedGap w _ _ => a + w
            | .decoration _ w .. => a + w
            | .rule w .. => a + w
            | .image _ w _ _ _ _ => a + w
            | .poly .. => a) (0 : Dim.Length)
          return some (l.x + l.hang, l.x + w)
    return none
  let tab (spec body : String) : String :=
    s!"\\begin\{tabular}\{{spec}}\\toprule {body} \\\\\\bottomrule\\end\{tabular}"
  let plain := topRule (out (tab "lrr" "alpha & 12345 & 67890"))
  t "a spanning head that fits its columns leaves the table at its column maxima"
    (topRule (out (tab "lrr" "& \\multicolumn{2}{c}{1234567890} \\\\ alpha & 12345 & 67890")) ==
      plain && plain > 0)
  let wide := "12345678901234567890123456789012345"
  let twoCol := topRule (out (tab "lr" s!"alpha & {wide}"))
  t "a spanning head wider than its columns widens the table by exactly its excess"
    (topRule (out (tab "lrr" s!"& \\multicolumn\{2}\{c}\{{wide}} \\\\ alpha & 12345 & 67890")) ==
      twoCol && twoCol > plain)
  let co := out (tab "lrr" "& \\multicolumn{2}{c}{ZZZ} \\\\ alpha & 12345 & 67890")
  t "a spanned head is centred over the columns it covers"
    (match extent co "ZZZ", extent co "12345", extent co "67890" with
     | some (hx, hr), some (ax, _), some (_, br) => ((hx + hr) - (ax + br)).abs ≤ 2 * Dim.Length.quantum
     | _, _, _ => false)
  let ro := out (tab "ll" "\\multicolumn{1}{r}{QQ} & b \\\\ widewidewide & b")
  t "a one-column multicolumn sets its own alignment"
    (match extent ro "QQ", extent ro "widewidewide" with
     | some (_, qr), some (_, wr) => (qr - wr).abs ≤ 2 * Dim.Length.quantum
     | _, _ => false)
  let po := out (tab "ll" ("\\multicolumn{2}{p{2cm}}{word word word word word word} \\\\ " ++
    "widewidewidewide & widewidewidewide"))
  t "a p-column span wraps at its declared width"
    (match extent po "word", extent po "widewidewidewide" with
     | some (px, pr), some (wx, _) => px == wx && pr - px ≤ Dim.pt 57
     | _, _ => false)

def kpChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let cases : List (String × Array Layout.Item × Dim.Length) := [
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
  let ragged := Layout.raggedItems
    (mkItems (List.intersperse G (List.replicate 10 (W 50))))
  let rNats : Array Dim.Length := Id.run do
    let mut prev := 0
    let mut first := true
    let mut nats : Array Dim.Length := #[]
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
  -- Expectations: luatex `\showhyphens` over the embedded hyph-en-us.tex, hyphenmins 2/3.
  let pats := Hyphen.english.get
  let hyph := Hyphen.marked pats
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
  -- These three tell hyph-en-us.tex from Knuth's hyphen.tex.
  t "hyphen set is ushyphmax (definition)" (hyph "definition" == "de-f-i-n-i-tion")
  t "hyphen set is ushyphmax (monotone)" (hyph "monotone" == "mo-not-one")
  t "hyphen set is ushyphmax (toolchain)" (hyph "toolchain" == "tool-chain")
  -- Expectations are lualatex `\showhyphens` output under [french]{babel}.
  let frp := Hyphen.french.get
  let hyphFr := Hyphen.marked frp
  t "hyphen french patterns loaded" (frp.map.size > 1000)
  t "hyphen fr considérablement" (hyphFr "considérablement" == "consi-dé-ra-ble-ment")
  t "hyphen fr constitution" (hyphFr "constitution" == "consti-tu-tion")
  t "hyphen fr déclaration" (hyphFr "déclaration" == "dé-cla-ra-tion")
  t "hyphen fr accented capital folds" (hyphFr "Électricité" == "Élec-tri-cité")
  -- German: hyph-de-1996.tex, hyphenmins 2/2 from the locale record.
  let dep := Hyphen.german.get
  let hyphDe := Hyphen.marked dep
  t "hyphen german patterns loaded" (dep.map.size > 30000)
  t "hyphen de wissenschaft" (hyphDe "Wissenschaft" == "Wis-sen-schaft")
  t "hyphen de compound" (hyphDe "Donaudampfschifffahrt" == "Do-nau-dampf-schiff-fahrt")
  t "hyphen de rightmin 2" (hyphDe "Zusammenfassung" == "Zu-sam-men-fas-sung")
  t "hyphen en mis-breaks french" (hyph "considérablement" != "consi-dé-ra-ble-ment")
  t "patsOf main for untagged" (Layout.patsOf (some pats) none |>.isSome)
  t "patsOf tagged run takes its own language"
    ((Layout.patsOf (some pats) (some "fr")).map (·.map.size) == some frp.map.size)
  t "patsOf off is off for every tag" ((Layout.patsOf none (some "fr")).isNone)
  t "hyphen respects hyphenmins" ((Hyphen.hyphenate pats "typesetting").all
    fun p => p ≥ 2 && p + 3 ≤ 11)

/-- The measure band (W0201) fires on continuous text set too wide or too narrow, applies to pages
rather than slides, and is silenced by `\page{ measure = free }`. -/
def measureChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Long enough to set at least four full lines at any measure under test.
  let prose := String.intercalate " " (List.replicate 40 "typesetting is the arrangement of type")
  let diagsOf (pre : String) (body : String) (geom : Layout.Geom := {}) : Array Diag :=
    let src := pre ++ "\\begin{document}" ++ body ++ "\\end{document}"
    (layoutOf oneFace (Elab.run "t" src).1 geom).diags
  let w0201 (ds : Array Diag) : Array Diag := ds.filter (·.code == "W0201")
  let wide := diagsOf "\\documentclass{article}\\page{ hmargin = 1in }" prose
  t "wide measure warns" ((w0201 wide).size == 1)
  t "wide measure says narrow"
    ((w0201 wide).all fun d => (d.help.getD "").startsWith "narrow")
  t "measure = free silences the band"
    ((w0201 (diagsOf "\\documentclass{article}\\page{ hmargin = 1in, measure = free }" prose)).isEmpty)
  t "slides are outside the rule's scope"
    ((w0201 (diagsOf "\\documentclass{slides}" prose)).isEmpty)
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
  let (dfltDoc, _) := Elab.run "t" ("\\documentclass{article}\\begin{document}" ++
    prose ++ "\\end{document}")
  t "default article text block is size10.clo's 345pt"
    (dfltDoc.page.width - 2 * dfltDoc.page.hmargin == Dim.pt 345)
  t "default article measure is in band"
    ((w0201 (layoutOf oneFace dfltDoc).diags).isEmpty)
  let (declDoc, _) := Elab.run "t"
    "\\documentclass{article}\\page{ vmargin = 0.5in }\\begin{document}x\\end{document}"
  t "a declared \\page keeps the margins it names, the class's standing across"
    (declDoc.page.vmargin == Dim.inch 1 / 2 &&
      declDoc.page.width - 2 * declDoc.page.hmargin == Dim.pt 345)
  t "measure key rejects a stray value"
    ((elabStr "\\documentclass{article}\\page{ measure = loose }\\begin{document}x\\end{document}").2.any
      (·.code == "E0323"))
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
  t "a sub-point \\page fontsize is rejected and keeps the base"
    (((elabStr ("\\documentclass{article}\\page{ fontsize = 0.4pt }" ++
        "\\begin{document}x\\end{document}")).2.any (·.code == "E0323")) &&
     (pageOf "\\documentclass{article}\\page{ fontsize = 0.4pt }").fontSize
       == Ir.baseFontSize)

/-- A heading binds to the text it introduces, so declared space below it must not exceed the
declared space above. -/
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

/-- The `card` class: trade-standard trim sizes, print safe-zone margins, no hyphenation, no running
furniture, and bleed on request. -/
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
    ((elabStr (card "[us]" "x")).1.page.width == Dim.bp 252 &&
     (elabStr (card "[us]" "x")).1.page.height == Dim.bp 144)
  t "jis option is the 91 × 55 mm meishi"
    ((elabStr (card "[jis]" "x")).1.page.width == Dim.mm 91 &&
     (elabStr (card "[jis]" "x")).1.page.height == Dim.mm 55)
  t "card margins default to the safe zone"
    (cDoc.page.hmargin == Dim.mm 5 && cDoc.page.vmargin == Dim.mm 5)
  t "a declared page beats the card defaults"
    ((elabStr (card "" "x" "\\page{ width = 100pt, height = 60pt, margin = 4pt }\n")).1.page.width
      == Dim.pt 100)
  t "card turns hyphenation off by default"
    (cDoc.page.hyphenate == some false)
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
  let widestGap (pre : String) : Dim.Length :=
    (bodyLines (layoutOf oneFace (elabStr (card "" prose pre)).1)).foldl (fun m l =>
      l.segs.foldl (fun m s => match s with
        | .gap w _ => max m w
        | _ => m) m) 0
  t s!"the same prose justified at card width sets loose lines, never overfull ones \
({reprStr (widestGap "\\page{ justify = on }\n")} against {reprStr (widestGap "")} ragged)"
    (!judgeOverfull "\\page{ justify = on }\n"
      && widestGap "\\page{ justify = on }\n" > 2 * widestGap "")
  t "article leaves hyphenation to the class default"
    ((elabStr "x").1.page.hyphenate == none)
  t "hyphenate is a page key any class may declare"
    ((elabStr "\\page{ hyphenate = off }\\begin{document}x\\end{document}").1.page.hyphenate
      == some false)
  t "hyphenate rejects a value that is not on or off"
    (errCodes "\\page{ hyphenate = 5pt }\\begin{document}x\\end{document}" == ["E0323"])
  let hyphenRendered (doc : Ir.Doc) : Bool :=
    let out := layoutOf oneFace doc (pats := some pats)
    out.pages.any fun p => p.lines.any fun l =>
      l.segs.any fun s => match s with
        | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '-')
        | .gap _ _ | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => false
  let narrowPage := "\\page{ width = 90pt, height = 400pt, margin = 10pt }\n"
  let word := "incomprehensibility incomprehensibility"
  t "an article at this measure does hyphenate"
    (hyphenRendered (elabStr (s!"{narrowPage}\\begin\{document}\n{word}\n\\end\{document}")).1)
  t "a card never hyphenates"
    (!hyphenRendered (elabStr (card "" word narrowPage)).1)
  let (rDoc, rDs) := elabStr (card "" "x" "\\runninghead{name \\pagenumber}\n")
  t "card drops running content with W0317"
    (rDs.any (·.code == "W0317") && rDoc.head.isNone)
  let two := card "" "\\begin{frame}front\\end{frame}\n\\begin{frame}back\\end{frame}"
  let (twoDoc, twoDs) := elabStr two
  t "card faces source clean" (!twoDs.any (·.severity == .error))
  t "two faces are two pages"
    ((layoutOf oneFace twoDoc).pages.size == 2)
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
  -- 22.677 pt is the 8.504 pt trim offset plus the 14.173 pt margin.
  t "bleed shifts the content with the trim box"
    (bytesContain bPdf "1 0 0 1 22.677 ")
  let plainGeom := Layout.Geom.ofPage cDoc.page
  let plainPdf := pdfText (Pdf.write plainGeom oneFace
    (layoutOf oneFace cDoc plainGeom).pages)
  t "no bleed, no TrimBox" (!bytesContain plainPdf "/TrimBox")
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
      ((saidText d).splitOn "right margin").length == 2)
  t "tiny type fails the legibility floor"
    ((judge (card "" "{\\tiny Pat Placeholder}")).any fun d =>
      (d.message.splitOn "text.xheight").length == 2)
  t "a reasonable card passes its whole contract"
    ((judge (card "" "Pat Placeholder\\\\ {\\small pat@example.org}")).isEmpty)
  let areaGeom : Layout.Geom := {}
  let areaEdges (box : Dim.Length → Dim.Length → Layout.Seg) : List String :=
    let edge (x y w h : Dim.Length) : String :=
      let line : Layout.LineOut :=
        { x := x, y := y, size := Dim.pt 10, segs := #[box w h], setWidth := Dim.pt 100 }
      let out : Layout.Out := { diags := #[], pages := #[{ lines := #[line] }] }
      let s := Check.Shipped.ofOut areaGeom oneFace out true
      if s.inArea then "inside" else s.areaActual
    [edge (Dim.pt 40) (Dim.pt 300) (Dim.pt 10) (Dim.pt 10),
     edge (Dim.pt 72) (Dim.pt 300) (Dim.pt 600) (Dim.pt 10),
     edge (Dim.pt 72) (Dim.pt 72) (Dim.pt 10) (Dim.pt 20),
     edge (Dim.pt 72) (Dim.pt 760) (Dim.pt 10) (Dim.pt 10)]
  let namesEveryEdge (es : List String) : Bool :=
    es.length == 4 &&
    (["left", "right", "top", "bottom"].zip es).all fun (e, s) =>
      (s.splitOn s!"{e} margin").length == 2
  t "the area judge holds a rule to all four edges"
    (namesEveryEdge (areaEdges fun w h => .rule w h 0 Ir.Color.black false))
  t "the area judge holds an image box to all four edges"
    (namesEveryEdge (areaEdges fun w h => .image none w h true 0 false))
  t "a running head does not fail text.in_area"
    ((judge ("\\runninghead{Pat Placeholder \\hfill \\pagenumber}\n" ++
      "\\assert{ text.in_area }\n" ++
      "\\begin{document}\nbody text\n\\end{document}")).isEmpty)
  t "furniture glyphs still feed the legibility floor"
    ((judge ("\\runninghead{{\\tiny Pat}}\n\\assert{ text.xheight >= 1.5mm }\n" ++
      "\\begin{document}\nbody\n\\end{document}")).any fun d =>
      (d.message.splitOn "text.xheight").length == 2)
  t "card takes the shared base size" (cDoc.page.fontSize == Ir.baseFontSize)
  t "a card class option sets the base size through the shared path"
    ((elabStr (card "[12pt]" "x")).1.page.fontSize == Dim.pt 12)
  t "an illegible card pairing warns through the colour contract"
    ((warnCodes (card "" "\\textcolor{washed}{faint}"
      "\\palette{ washed = #888888 }\n")).contains "W0315")
  t "declared decorative intent silences it on a card too"
    (let src := card "" "\\textcolor{washed}{faint}"
      "\\palette[decorative]{ washed = #DDDDDD }\n"
     !(warnCodes src).contains "W0315")

/-- Printer's cut marks: the `\page` keys parse into the spec, the declared faces ship exactly the
eight derived fills, off means none, and the ink follows the registration reading. -/
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
     p.markGap == (Dim.inch 1).ofRatioRound 1 10 && p.markThickness == Dim.pt 1)
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
  t "registration ink follows the document's colour model: the All colorant in print"
    (Ir.Color.registration true == Ir.Color.ofInk Ir.Ink.all 1 &&
     Ir.Color.registration false == Ir.Color.black)
  t "an RGB document's marks paint plain black"
    ((outOf "bleed = 3mm, marks = cut").pages.all fun p =>
      p.fills.all fun f => f.color == Ir.Color.black)
  t "a print document's marks paint every plate, in the All separation"
    ((outOf "bleed = 3mm, marks = cut" "\\palette{ spot = cmyk(1, 0, 0, 0) }").pages.all
      fun p => p.fills.all fun f => (f.color.ink?.map (·.1.name)) == some "All")
  let grounded := src "bleed = 3mm" "\\palette{ bg = #F4EDE0 }"
  let g := Layout.Geom.ofPage (elabStr grounded).1.page
  t "a page ground covers the bleed strip, not only the trim"
    (let out := layoutOf oneFace (elabStr grounded).1 g
     out.pages.size ≥ 1 && out.pages.all fun p => p.fills.any fun f =>
      f.x == -Dim.mm 3 && f.y == -Dim.mm 3 && f.w == g.pageW + 2 * Dim.mm 3 &&
        f.h == g.pageH + 2 * Dim.mm 3)

/-- A card spelled in LaTeX draws its own printer's marks, and marks that are exactly a trim's cut
marks declare that trim. -/
def drawnMarkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre (draw : String) : String :=
    "\\documentclass{article}\\usepackage{geometry}\\usepackage[cmyk]{xcolor}" ++
    "\\usepackage{calc}" ++
    "\\newlength{\\trimw}\\newlength{\\trimh}\\newlength{\\bl}\\newlength{\\paperw}" ++
    "\\newlength{\\paperh}\\newlength{\\hair}\\newlength{\\stub}" ++
    "\\setlength{\\trimw}{3.5in}\\setlength{\\trimh}{2in}\\setlength{\\bl}{3mm}" ++
    "\\setlength{\\paperw}{\\trimw+2\\bl}\\setlength{\\paperh}{\\trimh+2\\bl}" ++
    "\\setlength{\\hair}{0.25pt}\\setlength{\\stub}{1mm}" ++
    "\\geometry{paperwidth=\\paperw, paperheight=\\paperh, margin=8mm}" ++
    "\\definecolor{allplates}{cmyk}{1,1,1,1}\\pagestyle{empty}" ++ draw ++
    "\\begin{document}\\noindent Placeholder Name\\end{document}"
  let vmark (x y : String) : String :=
    s!"\\put({x},{y})\{\\rule\{\\hair}\{\\stub}}"
  let hmark (x y : String) : String :=
    s!"\\put({x},{y})\{\\rule\{\\stub}\{\\hair}}"
  let marks :=
    "\\newcommand{\\drawmarks}{\\begin{picture}(0,0)" ++
    vmark "\\dimexpr\\bl-0.5\\hair\\relax" "0pt" ++
    vmark "\\dimexpr\\bl-0.5\\hair\\relax" "\\dimexpr\\paperh-\\stub\\relax" ++
    vmark "\\dimexpr\\paperw-\\bl-0.5\\hair\\relax" "0pt" ++
    vmark "\\dimexpr\\paperw-\\bl-0.5\\hair\\relax" "\\dimexpr\\paperh-\\stub\\relax" ++
    hmark "0pt" "\\dimexpr\\bl-0.5\\hair\\relax" ++
    hmark "\\dimexpr\\paperw-\\stub\\relax" "\\dimexpr\\bl-0.5\\hair\\relax" ++
    hmark "0pt" "\\dimexpr\\paperh-\\bl-0.5\\hair\\relax" ++
    hmark "\\dimexpr\\paperw-\\stub\\relax" "\\dimexpr\\paperh-\\bl-0.5\\hair\\relax" ++
    "\\end{picture}}" ++
    "\\AddToHook{shipout/background}{\\put(0pt,-\\paperh){\\color{allplates}\\drawmarks}}"
  let boxes := "\\AddToHook{shipout/before}{\\pdfvariable pageattr{/TrimBox [8.5 8.5 260.5 152.5]}}"
  let (doc, ds) := elabStr (pre (marks ++ boxes))
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  let bl := Dim.mm 3
  let hair := Dim.pt 1 / 4
  let want := Layout.cutMarks (Dim.inch 7 / 2) (Dim.inch 2) bl (bl - Dim.mm 1) hair
    (Ir.Color.ofCmyk 1000 1000 1000 1000)
  t "a drawn picture's rules and the page attribute's box are read, no hook skipped"
    (doc.page.drawn.size == 8 && doc.page.boxes.size == 1 &&
      !(ds.any fun d => d.code == DiagCode.W0104.code && d.subject == some "ctrl:AddToHook"))
  t "the medium is the declared paper, with no bleed of its own"
    (geom.bleed == 0 && geom.pageW == Dim.inch 7 / 2 + 2 * bl && geom.pageH == Dim.inch 2 + 2 * bl)
  t "the drawn marks ship on every page where they were drawn, in their ink"
    (out.pages.size ≥ 1 && out.pages.all fun p =>
      want.all fun f => p.fills.any fun g =>
        -- The source's \dimexpr reads each mark to TeX's scaled point.
        let near (a b : Dim.Length) : Bool := (a - b).abs ≤ Dim.Length.ofSp 1
        near g.x (f.x + bl) && near g.y (f.y + bl) && near g.w f.w && near g.h f.h &&
          g.color == f.color)
  t "the text keeps the margin the geometry measured from the medium"
    (lineXOf (censusOf #[] out) 0 "Placeholder" == some (Dim.mm 8))
  let pdf := pdfText (Pdf.write geom oneFace out.pages doc.info)
  let (media, _, _) := Pdf.pageBoxes (Dim.inch 7 / 2) (Dim.inch 2) bl
  t "the file writes the declared TrimBox and no box it did not declare, as lualatex's does"
    (bytesContain pdf "/TrimBox [8.5 8.5 260.5 152.5]" && !bytesContain pdf "/BleedBox" &&
     !bytesContain pdf "/ArtBox" && bytesContain pdf s!"/MediaBox {media.render}")
  let (bare, bareDs) := elabStr (pre marks)
  let bareGeom := Layout.Geom.ofPage bare.page
  let barePdf := pdfText (Pdf.write bareGeom oneFace (layoutOf oneFace bare bareGeom).pages bare.info)
  t "marks drawn with no declared page box declare no trim, as lualatex's file has none"
    (bare.page.drawn.size == 8 && bare.page.boxes.isEmpty && !bytesContain barePdf "/TrimBox" &&
     !(bareDs.any fun d => d.code == DiagCode.W0104.code && d.subject == some "ctrl:AddToHook"))
  let (lone, _) := elabStr (pre ("\\AddToHook{shipout/background}" ++
    "{\\put(0pt,-\\paperh){\\color{allplates}\\put(\\bl,\\bl){\\rule{\\stub}{\\hair}}}}"))
  let loneGeom := Layout.Geom.ofPage lone.page
  t "a lone drawn rule ships as drawn, from the medium's corner"
    ((layoutOf oneFace lone loneGeom).pages.all fun p => p.fills.any fun f =>
      f.x == bl && f.w == Dim.mm 1 && f.h == hair && f.y == lone.page.height - bl - hair)
  let stub (ink : String) : String := pre ("\\AddToHook{shipout/background}" ++
    s!"\{\\put(0pt,-\\paperh)\{\\color\{{ink}}\\put(\\bl,\\bl)\{\\rule\{\\stub}\{\\hair}}}}")
  let (redDoc, _) := elabStr (stub "red")
  t "a drawn rule in xcolor's red paints xcolor's red"
    ((layoutOf oneFace redDoc).pages.all fun p => p.fills.any fun f =>
      f.w == Dim.mm 1 && f.h == hair && f.color == ({ r := 255, g := 0, b := 0 } : Ir.Color))
  let (missDoc, missDs) := elabStr (stub "nosuchink")
  let missOut := layoutOf oneFace missDoc
  t "a drawn rule in a name that is no colour paints black and says so, once, by name"
    ((missOut.pages.all fun p => p.fills.any fun f =>
      f.w == Dim.mm 1 && f.color == Ir.Color.black) &&
     ((missDs ++ missOut.diags).filter fun d =>
       d.code == "W0304" && d.subject == some "palette:nosuchink").size == 1)

/-- A declared `pdfversion = 1.7` ships a PDF 1.7 file with a 1.7 structure namespace and no loss;
undeclared, the file stays PDF 2.0. -/
def pdfVersionChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (keys : String) : String :=
    s!"\\DocumentMetadata\{{keys}}\\documentclass\{article}\\begin\{document}" ++
      "Placeholder text.\\footnote{A placeholder note.}\\end{document}"
  let build (s : String) : ByteArray × Array Diag :=
    let (doc, ds) := elabStr s
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom
    let tree := Struct.ofDoc (Layout.pdfView doc)
    (Pdf.write geom oneFace out.pages doc.info (outline := out.outline) (tree := tree), ds)
  let (p17, d17) := build (src "lang=en, pdfversion=1.7")
  let (p20, _) := build (src "lang=en")
  let head (p : ByteArray) : String := String.fromUTF8! (p.extract 0 8)
  t "a declared pdfversion 1.7 writes a PDF 1.7 header"
    (head p17 == "%PDF-1.7" && head p20 == "%PDF-2.0")
  t "a declared pdfversion names no loss"
    (!(d17.any fun d => d.code == DiagCode.W0101.code))
  t "a 1.7 file carries no 2.0 namespace, and role-maps the 2.0 note type"
    (let x := pdfText p17
     !bytesContain x "/Namespace" && bytesContain x "/RoleMap" &&
       bytesContain x "/FENote /Note")
  t "an undeclared version keeps the 2.0 namespace"
    (bytesContain (pdfText p20) "/Namespaces")
  t "a version the writer does not write stays named"
    ((warnCodes (src "pdfversion=1.4")).contains "W0101")

/-- A driver option asks for nothing the page shows: geometry's and crop's driver names and
`verbose` ship the same bytes, no loss named. -/
def driverOptionChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (pre : String) : String :=
    s!"\\documentclass\{article}{pre}\\begin\{document}Placeholder text.\\end\{document}"
  let pdfOf (s : String) : ByteArray :=
    let doc := (elabStr s).1
    let geom := Layout.Geom.ofPage doc.page
    Pdf.write geom oneFace (layoutOf oneFace doc geom).pages doc.info
  let sheet := "\\geometry{paperwidth=3in, paperheight=2in, margin=0.25in}"
  let bare := src ("\\usepackage{geometry}" ++ sheet)
  let driven := src ("\\usepackage[dvips=false,pdftex=false,vtex=false,luatex,verbose]" ++
    "{geometry}" ++ sheet)
  t "geometry's driver options and verbose name no loss"
    (!(warnCodes driven).contains "W0101")
  t "geometry's driver options ship the page without them"
    (pdfOf driven == pdfOf bare)
  let cropBare := src ("\\usepackage[cam]{crop}\\page{ bleed = 3mm }")
  let cropDriven := src ("\\usepackage[cam,pdftex,dvips]{crop}\\page{ bleed = 3mm }")
  t "crop's driver options name no loss"
    (!(warnCodes cropDriven).contains "W0101")
  t "crop's driver options ship the page without them"
    (pdfOf cropDriven == pdfOf cropBare)
  t "an option with meaning is still named"
    ((warnCodes (src "\\usepackage[showframe]{geometry}")).contains "W0104")

/-- The poster's legibility floor, judged over the shipped pages, passes the class's own default
body and fails an unscaled article body. -/
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
    -- 11pt, not 10: a declared 10pt equals the PageSpec default, and the class record wins it back.
    ((judge (poster "\\page{ fontsize = 11pt }\n" "An unscaled article body.")).any
      fun d => (d.message.splitOn "text.xheight").length == 2)
  t "an enumerate at poster size keeps its marker inside the print margin"
    ((judge (poster "" "\\begin{enumerate}\n\\item one\n\\item two\n\\end{enumerate}")).all
      fun d => (d.message.splitOn "text.in_area").length == 1)
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

/-- Pictures through layout: shapes land as fills and label runs through one `Pic.Place` transform,
and W0335 fires when the box cannot fit the text area. -/
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
  t "picture rect ships as one fill mark of its own size and colour, and no page fill"
    ((out.pages[0]?.map fun p => p.fills.isEmpty && match (pageDraws p).toList with
      | [(.rect x y w h, some f, none)] =>
        x == geom.hmargin && y == geom.vmargin && w == Dim.pt 20 && h == Dim.pt 10 &&
          f == Ir.Pic.solidFill red
      | _ => false).getD false)
  t "picture label ships its glyphs centred on the anchor"
    ((out.pages[0]?.map fun p =>
      match (p.lines.filter (!·.furniture)).toList with
      | [l] =>
        (match l.segs.toList with
         | [Layout.Seg.run _ _ _ _ glyphs _ _ _ _ _ _] =>
           String.ofList (glyphs.toList.map (·.2.1)) == "7"
         | _ => false)
        && l.x + l.setWidth / 2 == geom.hmargin + Dim.pt 10
      | _ => false).getD false)
  let bare := run #[.picture { shapes := #[.rect 0 0 (Dim.pt 5) (Dim.pt 5) red] }]
  t "a picture of fills alone still ships its page"
    ((bare.pages[0]?.map fun p => (pageDraws p).size == 1).getD false)
  let circled : Ir.Pic.Picture := { shapes := #[
    .circle (Dim.pt 10) (Dim.pt 5) (Dim.pt 5) (some ({} : Ir.Pic.Stroke)) (some red)] }
  let outC := run #[.picture circled]
  t "an outlined circle ships as one page path with its paint"
    ((outC.pages[0]?.bind fun p => (pageDraws p)[0]?.map fun (g, fl, st) =>
      (match g with
       | .ellipse cx cy rx ry =>
         cx == geom.hmargin + Dim.pt 5 && cy == geom.vmargin + Dim.pt 5 && rx == Dim.pt 5 &&
           ry == Dim.pt 5
       | .rect _ _ _ _ => false
       | .path _ => false) &&
      st == some (Ir.Pic.strokeOf {}) && fl == some (Ir.Pic.solidFill red)).getD false)
  let centered := run #[.center #[.picture pic]]
  t "a centred picture centres its box"
    ((centered.pages[0]?.bind fun p => (pageDraws p)[0]?.map fun (g, _, _) =>
      (markExtent g).1 == geom.hmargin + (geom.textWidth - Dim.pt 20) / 2).getD false)
  let wide := run #[.picture { shapes :=
    #[.rect 0 0 (geom.textWidth + Dim.pt 50) (Dim.pt 10) red] }]
  t "a picture wider than the text area warns W0335"
    (wide.diags.any (·.code == "W0335"))
  t "a fitting picture does not warn W0335"
    (!out.diags.any (·.code == "W0335"))

mutual

/-- A tree with every `class` attribute dropped: the element tree a consumer stylesheet's
combinators walk. -/
def unclassOne : Html.Node → Html.Node
  | .elem t attrs kids => .elem t (attrs.filter (·.1 != "class")) (unclassList #[] kids.toList)
  | .text s => .text s
  | .style css => .style css
  | .script attrs js => .script attrs js

def unclassList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | k :: rest => unclassList (acc.push (unclassOne k)) rest

end

mutual

/-- The parent tag of every element carrying the class token `c`, in tree order. -/
def classParentsOne (c parent : String) (acc : Array String) : Html.Node → Array String
  | .elem t attrs kids =>
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    let acc := if (cls.splitOn " ").contains c then acc.push parent else acc
    classParentsList c t acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def classParentsList (c parent : String) (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => classParentsList c parent (classParentsOne c parent acc k) rest

end

/-- A trivlist spends `\@trivlist`'s space as lualatex sets each probe: the `\topsep` in force, its
`\partopsep` where it opens in vertical mode and the `\parskip` in force on top, above and below, and
none in an item's label. -/
def trivlistChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (cls pre body : String) : String :=
    s!"\\documentclass{cls}" ++ pre ++ "\\begin{document}" ++ body ++ "\n\\end{document}"
  let steps (src : String) (words : List String) : List Dim.Length :=
    let c := censusOfSrc oneFace src
    let v := words.filterMap (lineYOf c 0 ·)
    (v.zip v.tail).map fun (a, b) => b - a
  let geomOf (src : String) : Layout.Geom := Layout.Geom.ofPage (elabStr src).1.page
  let leadOf (src : String) : Dim.Length := Ir.leadingFor (geomOf src).fontSize (geomOf src).leading
  let lead := leadOf (doc "{article}" "" "x")
  let gaps (xs : List Int) : List Dim.Length := xs.map fun x => lead + Dim.pt x
  let abc := ["Alpha.", "Bravo.", "Charlie."]
  let abcd := ["Alpha.", "Bravo.", "Charlie.", "Delta."]
  let ul (body : String) : String := "\\begin{itemize}\n" ++ body ++ "\n\\end{itemize}"
  -- size10.clo: `\topsep` 8pt and `\partopsep` 2pt; level one's `\parsep` and `\itemsep` 4pt, level
  -- two's `\topsep` 4pt and `\parsep` 2pt, level three's `\topsep` 2pt and `\partopsep` 1pt.
  for e in ["center", "flushleft", "flushright", "verbatim"] do
    let b := s!"\\begin\{{e}}\nBravo.\n\\end\{{e}}"
    let art := doc "{article}" ""
    let cases : List (String × String × List String × List Int) :=
      [("after a blank line", s!"Alpha.\n\n{b}\n\nCharlie.", abc, [10, 10]),
       ("inside a paragraph", s!"Alpha.\n{b}\nCharlie.", abc, [8, 8]),
       ("below, as it opened", s!"Alpha.\n\n{b}\nCharlie.", abc, [10, 10]),
       ("in an item", ul s!"\\item Alpha.\n{b}\nCharlie.", abc, [12, 12]),
       ("in an item after a blank line", ul s!"\\item Alpha.\n\n{b}\n\nCharlie.", abc, [14, 14]),
       ("opening an item", ul s!"\\item Alpha.\n\\item {b}\nCharlie.\n\\item Delta.", abcd, [8, 4, 8]),
       ("last in an item", ul s!"\\item Alpha.\n{b}\n\\item Charlie.", abc, [12, 12]),
       ("last in a list", "Zulu.\n" ++ ul s!"\\item Alpha.\n{b}" ++ "\nCharlie.", abc, [12, 12]),
       ("in a level-two item", ul ("\\item Zulu.\n" ++ ul s!"\\item Alpha.\n{b}\nCharlie."), abc, [6, 6]),
       ("in a level-three item after a blank line",
         ul ("\\item Zulu.\n" ++ ul ("\\item Yankee.\n" ++ ul s!"\\item Alpha.\n\n{b}\n\nCharlie.")),
         abc, [3, 3]),
       ("in a quote", s!"\\begin\{quote}\nAlpha.\n{b}\nCharlie.\n\\end\{quote}", abc, [12, 12]),
       ("opening a quote", s!"Alpha.\n\\begin\{quote}\n{b}\nCharlie.\n\\end\{quote}\nDelta.", abcd,
         [8, 4, 8]),
       ("closing a quote", s!"Alpha.\n\\begin\{quote}\nZulu.\n{b}\n\\end\{quote}\nCharlie.",
         ["Zulu.", "Bravo.", "Charlie."], [12, 12]),
       ("in a quotation", s!"\\begin\{quotation}\nAlpha.\n{b}\nCharlie.\n\\end\{quotation}", abc,
         [8, 8]),
       ("in a verse", s!"\\begin\{verse}\nAlpha.\n{b}\nCharlie.\n\\end\{verse}", abc, [12, 12]),
       ("after another", s!"Alpha.\n\n{b}\n\\begin\{{e}}\nCharlie.\n\\end\{{e}}\nDelta.", abcd,
         [10, 10, 10])]
    for (name, body, words, want) in cases do
      t s!"{e} {name}: lualatex's distances" (steps (art body) words == gaps want)
    t s!"{e} after a heading opens no space above it"
      (steps (art s!"\\section\{Head}\n{b}\nCharlie.") ["Head", "Bravo."] ==
        steps (art "\\section{Head}\nBravo.\n\nCharlie.") ["Head", "Bravo."])
  let center := "\\begin{center}\nBravo.\n\\end{center}"
  for (cls, top) in [("[11pt]{article}", 12), ("[12pt]{article}", 13), ("{report}", 10), ("{book}", 10),
      ("{scrartcl}", 12)] do
    let src := doc cls "" s!"Alpha.\n\n{center}\n\nCharlie."
    t s!"a center in {cls} after a blank line spends its size file's topsep and partopsep"
      (steps src abc == [leadOf src + Dim.pt top, leadOf src + Dim.pt top])
  -- scrsize11pt.clo's level one, and level two under `\@list@extra` from level one's `\parsep`.
  let koma := doc "{scrartcl}" ""
    (ul ("\\item Alpha.\n" ++ center ++ "\nCharlie.\n\\item Zulu.\n" ++
      ul ("\\item Delta.\n\\begin{center}\nEcho.\n\\end{center}\nFoxtrot.")))
  let kl := leadOf koma
  t "a KOMA-Script center reads level one's topsep and level two's \\@list@extra"
    (steps koma ["Alpha.", "Bravo.", "Charlie.", "Zulu.", "Delta.", "Echo.", "Foxtrot."] ==
      [kl + Dim.pt 27 / 2, kl + Dim.pt 27 / 2, kl + Dim.pt 9, kl + Dim.pt 9 / 2, kl + Dim.pt 9 / 2,
       kl + Dim.pt 9 / 2])
  let half := doc "[parskip=half]{scrartcl}" "" (ul ("\\item Alpha.\n" ++ center ++ "\nCharlie.\n\\item Delta."))
  t "a KOMA-Script center under parskip=half takes the item's parsep alone, as its items do"
    (match steps half abcd with
     | [x, y, z] => x == y && y == z && z > leadOf half
     | _ => false)
  for (name, pre, body, want) in [
      ("a declared topsep sets the top level's", "\\setlength{\\topsep}{3pt}",
        s!"Alpha.\n{center}\nCharlie.", [3, 3]),
      ("a declared topsep does not reach a list, which resets it", "\\setlength{\\topsep}{3pt}",
        ul s!"\\item Alpha.\n{center}\nCharlie.", [12, 12]),
      ("a declared partopsep stacks in vertical mode", "\\setlength{\\partopsep}{5pt}",
        s!"Alpha.\n\n{center}\n\nCharlie.", [13, 13]),
      ("a declared partopsep reaches a level-one item", "\\setlength{\\partopsep}{5pt}",
        ul s!"\\item Alpha.\n\n{center}\n\nCharlie.", [17, 17]),
      ("a declared parskip stands on top", "\\setlength{\\parskip}{6pt}",
        s!"Alpha.\n{center}\nCharlie.", [14, 14]),
      ("a \\setlist parsep and partopsep reach it, its topsep does not",
        "\\usepackage{enumitem}\\setlist{topsep=3pt,partopsep=7pt,parsep=9pt}",
        ul s!"\\item Alpha.\n\n{center}\n\nCharlie.", [24, 24]),
      ("a list's own parsep reaches it", "\\usepackage{enumitem}",
        s!"\\begin\{itemize}[topsep=2pt,parsep=1pt]\n\\item Alpha.\n{center}\nCharlie.\n\\end\{itemize}",
        [9, 9])] do
    t s!"{name}: lualatex's distances" (steps (doc "{article}" pre body) abc == gaps want)
  t "a center opening a flushleft stands in its label"
    (steps (doc "{article}" "" ("Alpha.\n\\begin{flushleft}\n" ++ center ++ "\nCharlie.\n\\end{flushleft}\nDelta."))
      ["Alpha.", "Bravo."] == gaps [8])
  let peer := match steps (doc "{article}" "" "Alpha.\n\nBravo.") ["Alpha.", "Bravo."] with
    | [d] => d
    | _ => 0
  t "a list opening a center stands in its label, leaving the peer gap below it"
    (steps (doc "{article}" "" ("Alpha.\n\\begin{center}\n" ++ ul "\\item Bravo." ++
      "\nCharlie.\n\\end{center}")) abc == [lead + Dim.pt 8, peer])
  t "a quote opening an item stands in its label: lualatex's distances"
    (steps (doc "{article}" "" (ul ("\\item Alpha.\n\\item \\begin{quote}\nBravo.\n\\end{quote}\n" ++
      "Charlie.\n\\item Delta."))) abcd == gaps [8, 4, 8])
  t "a heading after a center stands where it stands after a paragraph or a list, as lualatex sets it"
    (let after (blk : String) : List Dim.Length :=
      steps (doc "{article}" "" ("Alpha.\n\n" ++ blk ++ "\n\n\\section{Bravo}\nCharlie.")) ["Delta.", "Bravo"]
     after "\\begin{center}\nDelta.\n\\end{center}" == after "Delta." &&
       after "\\begin{center}\nDelta.\n\\end{center}" ==
         after "\\begin{itemize}\n\\item Delta.\n\\end{itemize}" &&
       (after "Delta.").length == 1)
  t "a list opening right after a trivlist in an item spends the larger of the two: lualatex's"
    (steps (doc "{article}" "" (ul ("\\item Alpha.\n" ++ center ++ "\n" ++ ul "\\item Charlie."))) abc ==
      gaps [12, 10])
  t "a quote opening right after a trivlist in an item spends the larger of the two: lualatex's"
    (steps (doc "{article}" "" (ul ("\\item Alpha.\n" ++ center ++
      "\n\\begin{quote}\nCharlie.\n\\end{quote}"))) abc == gaps [12, 10])
  t "a trivlist right after a display opens inside its paragraph, closing without partopsep"
    (steps (doc "{article}" "" ("Alpha.\n\\[ x = y \\]\n" ++ center ++ "\nCharlie.")) ["Bravo.", "Charlie."]
      == gaps [8])
  t "a trivlist after a description label alone stands in its label, the label on its line"
    (steps (doc "{article}" "" ("\\begin{description}\n\\item[Alpha] Text.\n\\item[Term] " ++ center ++
      "\nCharlie.\n\\end{description}")) ["Term", "Bravo.", "Charlie."] == [0, lead + Dim.pt 4])
  -- enumitem's `\trivlist` runs `\@list@extra` again from the list's `\parsep`.
  let kkey := doc "{scrartcl}" "\\usepackage{enumitem}"
    ("\\begin{itemize}[topsep=20pt]\n\\item Alpha.\n" ++ center ++ "\nCharlie.\n\\end{itemize}")
  t "a KOMA-Script list's declared topsep does not reach a trivlist in it: lualatex's distances"
    (steps kkey abc == [leadOf kkey + Dim.pt 9 / 2, leadOf kkey + Dim.pt 9 / 2])
  -- beamer's 11pt `\topsep` 9pt and level one's 3pt, no `\parsep`.
  let deck := "\\documentclass{beamer}\\begin{document}\\begin{frame}[t]\n" ++
    ul ("\\item Alpha.\n\\item " ++ center ++ "\nCharlie.\n\\item Delta.") ++ "\n\\end{frame}\\end{document}"
  let dl := leadOf deck
  t "a deck's center opening an item spends nothing of its own"
    (steps deck abcd == [dl + Dim.pt 3, dl, dl + Dim.pt 3])
  let flat := "\\documentclass{beamer}\\begin{document}\\begin{frame}[t]\nAlpha.\n" ++ center ++
    "\nCharlie.\n\\end{frame}\\end{document}"
  t "a deck's center spends beamer's top-level topsep" (steps flat abc == [leadOf flat + Dim.pt 9, leadOf flat + Dim.pt 9])
  -- The web page reads the same values off its gap rules.
  let rules := HtmlDoc.blockGapRules .sizeFile Ir.baseFontSize (HtmlDoc.exAt none Ir.baseFontSize) {}
  let triv := "." ++ HtmlDoc.roleClass Ir.trivlistRole
  t "html: a trivlist opens the top level's topsep and partopsep under the parskip in force"
    (rules.any fun r => match r with
      | .boundary sel v => sel == s!"* + {triv}" && hasStr v "var(--topsep, " &&
          hasStr v "var(--partopsep, " && hasStr v "var(--parskip, 0rem)"
      | _ => false)
  t "html: one opened inside a paragraph spends no partopsep"
    (rules.any fun r => match r with
      | .boundary sel v => sel == s!"* + {triv}.{HtmlDoc.roleClass Ir.inParagraphRole}" &&
          !hasStr v "partopsep"
      | _ => false)
  t "html: a list level states its topsep and partopsep for a trivlist inside"
    (rules.any fun r => match r with
      | .trivIn sel _ _ => hasStr sel "li:not(" && !hasStr sel ":is(li, dd"
      | _ => false)
  t "html: a trivlist opening an item leaves the peer gap alone below it"
    (rules.any fun r => match r with
      | .boundary sel v => hasStr sel s!"{triv}, " && hasStr sel ":first-child + *" &&
          hasStr v "var(--parskip, "
      | _ => false)
  let order := rules.zipIdx.filterMap fun (r, i) => match r with
    | .boundary sel _ => some (sel, i)
    | _ => none
  let at? (p : String → Bool) : Option Nat := (order.find? (p ·.1)).map (·.2)
  t "html: a trivlist's own space above outranks the close of an in-paragraph one before it"
    (match at? (· == s!"{triv}.{HtmlDoc.roleClass Ir.inParagraphRole} + *"), at? (· == s!"* + {triv}") with
     | some c, some o => c < o
     | _, _ => false)
  t "html: a list after a trivlist takes the larger of the two, past the trivlist's own close"
    (match at? (· == s!"{triv} + *"), at? (fun s => hasStr s s!"{triv}:not(" && hasStr s "+ :is(ul") with
     | some c, some o => c < o
     | _, _ => false)
  t "html: a block after a description label alone stands in its label"
    (rules.any fun r => match r with
      | .boundary sel v => hasStr sel "p:empty):first-child + " && v == "0"
      | _ => false)
  let kdoc := (elabStr (doc "[parskip=half]{scrartcl}" "" (ul ("\\item Alpha.\n\\begin{center}\nBravo.\n" ++
    ul "\\item Charlie." ++ "\n\\end{center}\nDelta.")))).1
  let ksize := kdoc.page.fontSize
  let kcloses := HtmlDoc.nestedClosesOf kdoc.docClass.record.lists ksize (HtmlDoc.exAt none ksize)
    kdoc.tokens false kdoc.body kdoc.docClass.record.listExtra
  t "html: a KOMA-Script trivlist closing on a list keeps the zero topsep \\@list@extra leaves"
    (kcloses.any fun c => c.parent == .triv && c.own == 0)
  let csrc := doc "{article}" "" "Alpha.\n\n\\begin{center}\nBravo.\n\\end{center}\n\nCharlie."
  let body (src : String) : Array Html.Node := (HtmlDoc.emitTree {} (elabStr src).1).2.1
  let cbody := body csrc
  t "html: a center environment's element is main's own child, carrying the trivlist role"
    (classParentsList "centered" "body" #[] cbody.toList == #["main"] &&
      classParentsList (HtmlDoc.roleClass Ir.trivlistRole) "body" #[] cbody.toList == #["main"])
  let shape (src : String) : String := Html.document "en" #[] (unclassList #[] (body src).toList)
  for (env, decl) in [("center", "\\centering"), ("flushleft", "\\raggedright"),
      ("flushright", "\\raggedleft")] do
    t s!"html: the {env} environment and its declaration ship one element tree"
      (shape (doc "{article}" "" s!"Alpha.\n\n\\begin\{{env}}\nBravo.\n\\end\{{env}}\n\nCharlie.") ==
        shape (doc "{article}" "" s!"Alpha.\n\n\{{decl} Bravo.\\par}\n\nCharlie."))
  t "the centering declaration opens no space"
    (steps (doc "{article}" "" "Alpha.\n\n{\\centering Bravo.\\par}\n\nCharlie.") abc ==
      steps (doc "{article}" "" "Alpha.\n\nBravo.\n\nCharlie.") abc)

/-- A list spends LaTeX's own list spacing: `\topsep` around it with `\parskip` on top, `\itemsep +
\parsep` between items, `\parsep` between an item's paragraphs, and a nested list its own level's. -/
def listRhythmChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (cls body : String) : String :=
    s!"\\documentclass{cls}\\begin\{document}" ++ body ++ "\n\\end{document}"
  let ys (src : String) (words : List String) : List Dim.Length :=
    let c := censusOfSrc oneFace src
    words.filterMap (lineYOf c 0 ·)
  let steps (src : String) (words : List String) : List Dim.Length :=
    let v := ys src words
    (v.zip v.tail).map fun (a, b) => b - a
  let geomOf (src : String) : Layout.Geom := Layout.Geom.ofPage (elabStr src).1.page
  let peerOf (cls : String) : Dim.Length :=
    match steps (doc cls "Alpha.\n\nBravo.") ["Alpha.", "Bravo."] with
    | [d] => d
    | _ => 0
  let three := "Alpha.\n\n\\begin{itemize}\n\\item Bravo.\n\\item Charlie.\n\\end{itemize}\n\nDelta."
  let words := ["Alpha.", "Bravo.", "Charlie.", "Delta."]
  -- size10.clo and size12.clo 215-219; a blank line before the list adds `\partopsep`.
  for (cls, size, top, item) in [("{article}", 10, 8 + 2, 4 + 4), ("[12pt]{article}", 12, 10 + 3, 5 + 5)] do
    let src := doc cls three
    let g := geomOf src
    let lead := Ir.leadingFor g.fontSize g.leading
    t s!"a list at {size}pt: topsep and partopsep under TeX's parskip, items itemsep plus parsep apart"
      (steps src words == [lead + Dim.pt top, lead + Dim.pt item, lead + Dim.pt top])
  let lead10 := Ir.leadingFor (Dim.pt 10) 1000
  t "a declared parskip stacks on a list's topsep, as TeX's does"
    (steps ("\\documentclass{article}\\setlength{\\parskip}{5pt}\\begin{document}" ++ three ++
      "\n\\end{document}") words == [lead10 + Dim.pt 5 + Dim.pt 10,
        lead10 + Dim.pt 8, lead10 + Dim.pt 5 + Dim.pt 10])
  t "two paragraphs of one item stand parsep apart"
    (steps (doc "{article}" "\\begin{itemize}\n\\item Bravo.\n\nCharlie.\n\\end{itemize}")
      ["Bravo.", "Charlie."] == [lead10 + Dim.pt 4])
  t "a nested list opens its own level's topsep and items"
    (steps (doc "{article}" ("\\begin{itemize}\n\\item Bravo.\n\\begin{itemize}\n\\item Charlie.\n" ++
      "\\item Delta.\n\\end{itemize}\n\\end{itemize}")) ["Bravo.", "Charlie.", "Delta."]
      == [lead10 + Dim.pt 4 + Dim.pt 4, lead10 + Dim.pt 2 + Dim.pt 2])
  t "article list fixtures lay out their peer boundary" (peerOf "{article}" > 0)
  let web := doc "{webpage}" three
  let wg := geomOf web
  let wlead := Ir.leadingFor wg.fontSize wg.leading
  let wpeer := peerOf "{webpage}"
  t "a webpage's list opens the peer gap a paragraph would, and its items stand a leading apart"
    (0 < wpeer && steps web words == [wpeer, wlead, wpeer])
  -- beamer's own family: 3 pt items and topsep, no parsep, in a frame.
  let deck := "\\documentclass{beamer}\\begin{document}\\begin{frame}[t]\nAlpha.\n" ++
    "\\begin{itemize}\n\\item Bravo.\n\\item Charlie.\n\\end{itemize}\nDelta.\n\\end{frame}\\end{document}"
  let dg := geomOf deck
  let dlead := Ir.leadingFor dg.fontSize dg.leading
  t "a deck's items stand beamer's itemsep apart, its list beamer's topsep from the text"
    (steps deck words == [dlead + Dim.pt 3, dlead + Dim.pt 3, dlead + Dim.pt 3])

/-- An explicit `\vspace` is never absorbed by an element's space: the element's first line moves by
the skip's whole width. -/
def vspaceKeptChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (body : String) : String :=
    "\\documentclass{article}\\begin{document}Alpha.\n\n" ++ body ++ "\n\nCharlie.\n\\end{document}"
  let at2 (src : String) : Option (Dim.Length × Dim.Length) := do
    let c := censusOfSrc oneFace src
    pure (← lineYOf c 0 "Alpha.", ← lineYOf c 0 "Bravo")
  let elements : List (String × String) :=
    [("itemize", "\\begin{itemize}\n\\item Bravo.\n\\end{itemize}"),
     ("enumerate", "\\begin{enumerate}\n\\item Bravo.\n\\end{enumerate}"),
     ("quote", "\\begin{quote}\nBravo.\n\\end{quote}"),
     ("center", "\\begin{center}\nBravo.\n\\end{center}"),
     ("flushleft", "\\begin{flushleft}\nBravo.\n\\end{flushleft}"),
     ("section", "\\section*{Bravo}")]
  for (name, el) in elements do
    for skip in ["\\vspace{12pt}", "\\bigskip"] do
      match at2 (doc el), at2 (doc (skip ++ "\n" ++ el)) with
      | some (a0, b0), some (a1, b1) =>
        t s!"{skip} before {name} moves it by the skip's whole width"
          (a1 == a0 && b1 - b0 == Dim.pt 12)
      | _, _ => t s!"{skip} before {name}: the fixture lays out" false

/-- A fill-centred block stands where its content stands alone, and a face closed by `\pagebreak`
stands as on a page of its own. -/
def fillCentreChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}" ++ pre ++ "\\begin{document}" ++ body ++ "\n\\end{document}"
  let y (src : String) (page : Nat) (word : String) : Option Dim.Length :=
    lineYOf (censusOfSrc oneFace src) page word
  let sandwich (inner : String) : String :=
    "\\vspace*{\\fill}\n" ++ inner ++ "\n\n\\vspace*{\\fill}"
  let bare := y (doc "" (sandwich "Alpha words.")) 0 "Alpha"
  for (name, inner) in [("center", "\\begin{center}\nAlpha words.\n\\end{center}"),
      ("flushleft", "\\begin{flushleft}\nAlpha words.\n\\end{flushleft}"),
      ("itemize", "\\begin{itemize}\n\\item Alpha words.\n\\end{itemize}"),
      ("quote", "\\begin{quote}\nAlpha words.\n\\end{quote}")] do
    t s!"a fill-centred {name} stands where its bare line stands"
      (bare.isSome && y (doc "" (sandwich inner)) 0 "Alpha" == bare)
  let face (size w1 w2 : String) : String :=
    "\\vspace*{\\fill}\n\\begin{center}\n\\begin{minipage}{\\textwidth}\n\\" ++ size ++ "\n" ++
      w1 ++ "\\\\\n" ++ w2 ++ "\n\\end{minipage}\n\\end{center}\n\\vspace*{\\fill}\n\\pagebreak\n"
  let card := "\\usepackage{geometry}\\geometry{paperwidth=4in, paperheight=2.5in, margin=0.3in}"
  let alone := y (doc card (face "normalsize" "Delta words" "Echo words")) 0 "Delta"
  let second := y (doc card (face "Huge" "Alpha words" "Bravo words" ++
    face "normalsize" "Delta words" "Echo words")) 1 "Delta"
  t "a second face stands where the same face stands on a page of its own"
    (alone.isSome && second == alone)
  let pic := "\\begin{center}\n\\begin{tikzpicture}\\draw (0,0) rectangle (2,1);" ++
    "\\node at (1,0.5) {Alpha};\\end{tikzpicture}\n\\end{center}"
  let skew (pre body : String) : Option (Dim.Length × Bool) := do
    let (d, _) := elabStr (doc (card ++ "\\usepackage{tikz}\\pagestyle{empty}" ++ pre) body)
    let g := Layout.Geom.ofPage d.page
    let p ← (layoutOf oneFace d).pages[0]?
    let (top, h) ← (pageDraws p).findSome? fun (g, _, _) => match g with
      | .rect _ y _ h => some (y, h)
      | _ => none
    let label ← p.lines.find? fun l => hasStr (lineText l) "Alpha"
    pure ((top - g.bodyTop) - (g.bodyBottom - (top + h)), top < label.y && label.y < top + h)
  let within (v : Option (Dim.Length × Bool)) (want : Dim.Length) : Bool :=
    (v.map fun (s, inside) => inside && want - Dim.Length.quantum ≤ s && s ≤ want + Dim.Length.quantum).getD false
  t "a fill-framed picture stands centred, its label inside it"
    (within (skew "\\setlength{\\topskip}{0pt}"
      ("\\nointerlineskip\n" ++ sandwich pic)) 0)
  t "a fill-framed picture stands the class's \\topskip and \\lineskip low, as in lualatex"
    (within (skew "" (sandwich pic)) (Dim.pt 10 + Ir.inkClearance))

/-- A block framed by two fills stands centred on its TeX box under the class's and a declared
`\topskip`, and an untitled frame does too. -/
def faceCentreChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let face (size w1 w2 : String) : String :=
    "\\nointerlineskip\n\\vspace*{\\fill}\n\\begin{center}\n\\begin{minipage}{\\textwidth}\n" ++
      "\\flushleft\n\\" ++ size ++ "\n" ++ w1 ++ "\\\\\n" ++ w2 ++
      "\n\\end{minipage}\n\\end{center}\n\\vspace*{\\fill}\n\\pagebreak\n"
  let src (pre : String) : String :=
    "\\documentclass{article}\\usepackage{geometry}" ++
    "\\geometry{paperwidth=4in, paperheight=2.5in, margin=0.3in, noheadfoot}" ++
    "\\pagestyle{empty}\\setlength{\\parindent}{0pt}\\setlength{\\parskip}{0pt}" ++ pre ++
    "\\begin{document}" ++ face "Large" "Alpha Bravo" "Charlie Delta, Echo" ++
    face "normalsize" "golf.example.org" "hotel@example.org" ++ "\\end{document}"
  -- The gap above the block's box on page `i` less the gap below it.
  let skew (s : String) (i : Nat) : Option Dim.Length := do
    let (doc, _) := elabStr s
    let g := Layout.Geom.ofPage doc.page
    let p ← (layoutOf oneFace doc).pages[i]?
    let first ← p.lines[0]?
    let last ← p.lines.back?
    let top := first.y - (Layout.segsInk oneFace first.segs).1
    let bottom := last.y + (Layout.segsInk oneFace last.segs).2
    pure ((top - g.bodyTop) - (g.bodyBottom - bottom))
  let within (v : Option Dim.Length) (want : Dim.Length) : Bool :=
    (v.map fun d => want - Dim.Length.quantum ≤ d && d ≤ want + Dim.Length.quantum).getD false
  for i in [0, 1] do
    t s!"face {i + 1}: a block framed by two fills stands centred on its box"
      (within (skew (src "\\setlength{\\topskip}{0pt}") i) 0)
    t s!"face {i + 1}: the class's \\topskip stands above the fill, as in lualatex"
      (within (skew (src "") i) (Dim.pt 10))
    t s!"face {i + 1}: a declared \\topskip stands above the fill whole"
      (within (skew (src "\\setlength{\\topskip}{14pt}") i) (Dim.pt 14))
  let deck (head last : String) : String :=
    "\\documentclass{beamer}\\usetheme{moloch}\\begin{document}\\begin{frame}[c]" ++ head ++
      "\nAlpha words here.\n\n" ++ last ++ "\n\\end{frame}\\end{document}"
  let lastDepth (s : String) : Option (Dim.Length × Dim.Length) := do
    let p ← (layoutOf oneFace (elabStr s).1).pages[0]?
    let l ← p.lines.find? fun l => hasStr (lineText l) "Bravo"
    pure (l.y, (Layout.segsInk oneFace l.segs).2)
  match lastDepth (deck "" "Bravo words ooo"), lastDepth (deck "" "Bravo words ppp") with
  | some (yo, dO), some (yp, dp) =>
    t "an untitled centred frame lifts by half its last line's glyph depth, as lualatex does"
      (dO < dp && (yo - yp) - (dp - dO) / 2 ≤ Dim.Length.quantum &&
        (dp - dO) / 2 - (yo - yp) ≤ Dim.Length.quantum)
  | _, _ => t "the frame depth fixtures lay out" false
  match lastDepth (deck "{Kilo}" "Bravo words ooo"), lastDepth (deck "{Kilo}" "Bravo words ppp") with
  | some (yo, dO), some (yp, dp) =>
    t "owed: a titled centred frame still ends on its last line's face descent"
      (dO < dp && yo == yp)
  | _, _ => t "the titled frame depth fixtures lay out" false

/-- Under `\flushbottom` a page the builder broke stands its last baseline on the text area's floor,
while `\raggedbottom` keeps the glue natural. -/
def flushBottomChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let para := String.intercalate " " (List.replicate 30 "kilo lima mike november")
  let src (decl : String) : String :=
    "\\documentclass{article}\\usepackage{geometry}" ++
    "\\geometry{paperwidth=5in, paperheight=4in, margin=0.5in}\\pagestyle{empty}" ++
    "\\setlength{\\parskip}{0pt plus 1pt}" ++ decl ++ "\\begin{document}" ++
    String.intercalate "\n\n" (List.replicate 7 para) ++ "\n\\end{document}"
  let pages (s : String) : Array (Array Dim.Length) × Dim.Length :=
    let (doc, _) := elabStr s
    let g := Layout.Geom.ofPage doc.page
    ((layoutOf oneFace doc).pages.map fun p => (p.lines.filter (!·.furniture)).map (·.y),
     g.bodyBottom)
  let (flush, floor) := pages (src "\\flushbottom")
  let (ragged, _) := pages (src "\\raggedbottom")
  let (bare, _) := pages (src "")
  t "the flush fixture breaks across pages" (flush.size ≥ 2)
  t "a flushbottom page the builder broke stands its last baseline on the floor"
    ((flush[0]?.bind (·.back?)).map (· == floor) |>.getD false)
  t "its first line keeps its place, the stretch spent below it, in order"
    (match flush[0]?, ragged[0]? with
     | some f, some r =>
       let sh : List Dim.Length := ((f.zip r).map fun (a, b) => a - b).toList
       f.size == r.size && f[0]? == r[0]? &&
         (sh.zip sh.tail).all (fun (a, b) => decide (a ≤ b)) &&
         (sh.getLast?.map fun v => decide ((0 : Dim.Length) < v)).getD false
     | _, _ => false)
  t "kept: raggedbottom is the undeclared page's natural glue" (ragged == bare)
  t "kept: the document's last page stays ragged under flushbottom"
    ((flush.back?.bind (·.back?)).map (fun v => decide (v < floor)) |>.getD false)
  let unread (s : String) : Array String :=
    ((elabStr s).2.filter (·.code == "W0104")).map (·.message)
  t "flushbottom is read, not named as a setting ignored"
    (unread (src "\\flushbottom") == unread (src ""))

/-- `\vspace*`'s space stays at a page's top, and the line below it takes TeX's interline glue. -/
def vspaceStarChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (pre body : String) : String :=
    "\\documentclass{article}\\usepackage{geometry}" ++
    "\\geometry{paperwidth=4in, paperheight=2.5in, margin=0.3in}\\pagestyle{empty}" ++ pre ++
    "\\begin{document}" ++ body ++ "\n\\end{document}"
  -- The first line holding `word` on page `pg`: its baseline below the text top, and its glyph box.
  let at? (s : String) (pg : Nat) (word : String) : Option (Dim.Length × Dim.Length × Dim.Length) := do
    let (doc, _) := elabStr s
    let g := Layout.Geom.ofPage doc.page
    let p ← (layoutOf oneFace doc).pages[pg]?
    let l ← p.lines.find? fun l => hasStr (lineText l) word
    let (h, d) := Layout.segsInk oneFace l.segs
    pure (l.y - g.bodyTop, h, d)
  let lead := Ir.leadingFor Ir.baseFontSize 1000
  for ts in [0, 10, 30] do
    t s!"\\vspace* keeps its space at a page's top, below a {ts}pt \\topskip"
      ((at? (src s!"\\setlength\{\\topskip}\{{ts}pt}" "\\vspace*{20pt}\nAlpha words") 0 "Alpha").map
        (·.1 == Dim.pt (ts + 20) + lead) |>.getD false)
  t "a first line taller than the leading takes \\lineskip below the kept space"
    ((at? (src "" "\\vspace*{20pt}\n{\\Huge Alpha words}") 0 "Alpha").map
      (fun (y, h, _) => y == Dim.pt 30 + h + Ir.inkClearance) |>.getD false)
  t "a rule taller than the leading takes \\lineskip below the kept space"
    ((at? (src "" "\\vspace*{20pt}\n\\rule{1pt}{24pt} Alpha words") 0 "Alpha").map
      (fun (y, h, _) => y == Dim.pt 30 + h + Ir.inkClearance) |>.getD false)
  t "a Huge first line stands Huge's leading below the kept space"
    ((at? (src "" "\\vspace*{20pt}\n{\\Huge Alpha words\\par}") 0 "Alpha").map
      (fun (y, _, _) => y == Dim.pt 60) |>.getD false)
  let p2 (pre : String) := src "" ("Alpha words\n\\newpage\n" ++ pre ++ "\\vspace*{20pt}\nBravo words")
  t "after \\newpage the line takes \\baselineskip less the last line's depth"
    (match at? (p2 "") 0 "Alpha", at? (p2 "") 1 "Bravo" with
     | some (_, _, dPrev), some (y, _, _) => y == Dim.pt 30 + lead - dPrev
     | _, _ => false)
  t "after \\nointerlineskip the line stands on its own box below the kept space"
    ((at? (p2 "\\nointerlineskip") 1 "Bravo").map
      (fun (y, h, _) => y == Dim.pt 30 + h) |>.getD false)
  let mid (v : String) := src "" ("Alpha words\n\n" ++ v ++ "\nBravo words\n\nCharlie words")
  t "mid-page, \\vspace* and \\vspace place alike"
    (pageLines oneFace (mid "\\vspace*{20pt}") == pageLines oneFace (mid "\\vspace{20pt}") &&
     (at? (mid "\\vspace{20pt}") 0 "Bravo").isSome)
  let sandwich (pre : String) :=
    src "" (pre ++ "\\vspace*{\\fill}\n\\begin{center}\nAlpha words\n\\end{center}\n\\vspace*{\\fill}")
  t "a fill-framed line takes the interline glue under the anchor, halved by the fils"
    (match at? (sandwich "") 0 "Alpha", at? (sandwich "\\nointerlineskip\n") 0 "Alpha" with
     | some (y, h, _), some (y0, _, _) => ((y - y0) - (lead - h) / 2).abs ≤ Dim.Length.quantum
     | _, _ => false)
  let html (s : String) : String :=
    Html.document "en" #[] (HtmlDoc.emitTree {} (elabStr s).1).2.1
  t "kept: html ships \\vspace* as \\vspace"
    (html (mid "\\vspace*{20pt}") == html (mid "\\vspace{20pt}"))

/-- A list or quote that opens a paragraph spends `\partopsep`, and one inside an open paragraph
does not. -/
def partopsepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (cls pre body : String) : String :=
    s!"\\documentclass{cls}" ++ pre ++ "\\begin{document}" ++ body ++ "\n\\end{document}"
  let steps (src : String) (words : List String) : List Dim.Length :=
    let c := censusOfSrc oneFace src
    let v := words.filterMap (lineYOf c 0 ·)
    (v.zip v.tail).map fun (a, b) => b - a
  let leadOf (src : String) : Dim.Length :=
    let g := Layout.Geom.ofPage (elabStr src).1.page
    Ir.leadingFor g.fontSize g.leading
  let art := doc "{article}" ""
  let lead := leadOf (art "x")
  let abc := ["Alpha.", "Bravo.", "Charlie."]
  for (name, el) in [("itemize", "\\begin{itemize}\n\\item Bravo.\n\\end{itemize}"),
      ("enumerate", "\\begin{enumerate}\n\\item Bravo.\n\\end{enumerate}"),
      ("quote", "\\begin{quote}\nBravo.\n\\end{quote}")] do
    t s!"{name} after a blank line opens topsep and partopsep above and below it"
      (steps (art ("Alpha.\n\n" ++ el ++ "\n\nCharlie.")) abc == [lead + Dim.pt 10, lead + Dim.pt 10])
    t s!"{name} inside an open paragraph opens topsep alone"
      (steps (art ("Alpha.\n" ++ el ++ "\nCharlie.")) abc == [lead + Dim.pt 8, lead + Dim.pt 8])
  let item := "\\begin{itemize}\n\\item Bravo.\n\\end{itemize}"
  t "the space below a list follows the mode the list opened in"
    (steps (art ("Alpha.\n\n" ++ item ++ "\nCharlie.")) abc == [lead + Dim.pt 10, lead + Dim.pt 10] &&
     steps (art ("Alpha.\n" ++ item ++ "\n\nCharlie.")) abc == [lead + Dim.pt 8, lead + Dim.pt 8])
  t "a list right after a list's end opens in vertical mode"
    (steps (art ("Alpha.\n\n" ++ item ++ "\n\\begin{itemize}\n\\item Charlie.\n\\end{itemize}\nDelta."))
      ["Alpha.", "Bravo.", "Charlie.", "Delta."] == [lead + Dim.pt 10, lead + Dim.pt 10, lead + Dim.pt 10])
  -- size10.clo: level two's topsep 4 and parsep 2, level three's topsep 2 and own partopsep 1pt.
  let nest (pre inner : String) : String := doc "{article}" pre
    ("\\begin{itemize}\n\\item Alpha.\n\\begin{itemize}\n\\item Bravo.\n\n" ++ inner ++
      "\n\n\\item Charlie.\n\\end{itemize}\n\\end{itemize}")
  let three := "\\begin{itemize}\n\\item Kilo.\n\\end{itemize}"
  let kilo := ["Bravo.", "Kilo.", "Charlie."]
  t "a level-two list after a blank line spends its level's topsep and partopsep"
    (steps (doc "{article}" "" ("\\begin{itemize}\n\\item Alpha.\n\n" ++
       "\\begin{itemize}\n\\item Bravo.\n\\end{itemize}\n\\end{itemize}")) ["Alpha.", "Bravo."]
      == [lead + Dim.pt 4 + Dim.pt 4 + Dim.pt 2] &&
     steps (doc "{article}" "" ("\\begin{itemize}\n\\item Alpha.\n" ++
       "\\begin{itemize}\n\\item Bravo.\n\\end{itemize}\n\\end{itemize}")) ["Alpha.", "Bravo."]
      == [lead + Dim.pt 4 + Dim.pt 4])
  t "a level-three list after a blank line spends its own partopsep"
    (steps (nest "" three) kilo == [lead + Dim.pt 5, lead + Dim.pt 5])
  t "a declared partopsep reaches the top level"
    (steps (doc "{article}" "\\setlength{\\partopsep}{5pt}" ("Alpha.\n\n" ++ item ++ "\n\nCharlie.")) abc
      == [lead + Dim.pt 13, lead + Dim.pt 13])
  t "a declared partopsep does not reach level three, whose list resets it"
    (steps (nest "\\setlength{\\partopsep}{5pt}" three) kilo == [lead + Dim.pt 5, lead + Dim.pt 5])
  let a12 := doc "[12pt]{article}" "" ("Alpha.\n\n" ++ item ++ "\n\nCharlie.")
  t "a 12pt list after a blank line spends size12's topsep and partopsep"
    (steps a12 abc == [leadOf a12 + Dim.pt 13, leadOf a12 + Dim.pt 13])
  let deck := "\\documentclass{beamer}\\begin{document}\\begin{frame}[t]\nAlpha.\n\n" ++ item ++
    "\n\nCharlie.\n\\end{frame}\\end{document}"
  t "a deck's list after a blank line spends beamer's zero partopsep"
    (steps deck abc == [leadOf deck + Dim.pt 3, leadOf deck + Dim.pt 3])
  let body (src : String) : Array Html.Node := (HtmlDoc.emitTree {} (elabStr src).1).2.1
  let shape (src : String) : String := Html.document "en" #[] (unclassList #[] (body src).toList)
  let inPar := art ("Alpha.\n" ++ item ++ "\nCharlie.")
  t "html: a list inside an open paragraph ships the element tree a blank-line list ships"
    (shape inPar == shape (art ("Alpha.\n\n" ++ item ++ "\n\nCharlie.")))
  t "html: a list inside an open paragraph carries the role's class on its own element"
    (hasStr (Html.document "en" #[] (body inPar))
      s!"<ul class=\"{HtmlDoc.roleClass Ir.inParagraphRole}\">")

/-- A list, quotation or abstract stands its class's `\leftmargin⟨n⟩` for its `\@listdepth` in,
fixed in the preamble font, a declared one reaching every list that deep, and the HTML hangs and
measures the same. -/
def listIndentChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let place (src : String) (w : String) : Option (Dim.Length × Dim.Length) := do
    let (d, _) := elabStr src
    let g := Layout.Geom.ofPage d.page
    let l ← (bodyLines (layoutOf oneFace d { g with protrude := false })).find? fun l =>
      hasStr (lineText l) w
    let r ← (lineRuns l).find? fun r => r.2.1.startsWith w
    pure (r.2.2.1 - g.hmargin, l.y)
  let xs (src : String) (ws : List String) : List (Option Dim.Length) :=
    ws.map fun w => (place src w).map (·.1)
  let doc (cls pre body : String) : String :=
    "\\documentclass" ++ cls ++ pre ++ "\\begin{document}" ++ body ++ "\n\\end{document}"
  let nest := "Alpha words.\n\\begin{itemize}\n\\item Bravo words.\n\\begin{itemize}\n" ++
    "\\item Charlie words.\n\\begin{itemize}\n\\item Delta words.\n\\begin{itemize}\n" ++
    "\\item Echo words.\n\\end{itemize}\n\\end{itemize}\n\\end{itemize}\n\\end{itemize}\nFoxtrot."
  let levels := ["Bravo", "Charlie", "Delta", "Echo"]
  let l3 := Dim.pt 47 + Dim.pt 187 / 10
  t "each list level stands its leftmargin in, at 10pt"
    (xs (doc "{article}" "" nest) levels ==
      [some (Dim.pt 25), some (Dim.pt 47), some l3, some (l3 + Dim.pt 17)])
  t "the first list level follows the type, at 12pt"
    (xs (doc "[12pt]{article}" "" nest) ["Bravo"] == [some (Dim.pt 30)])
  -- lualatex: 27.37498pt and 24.08995pt, 2.5em and 2.2em of size11.clo's 10.95pt; beamer's
  -- 21.9pt, 2em of the same 10.95pt.
  let s11 := Dim.pt 1095 / 100
  t "a deck's list levels stand beamer's 2em of its 10.95pt in"
    (xs (doc "{beamer}" "" ("\\begin{frame}[t]\n" ++ "Alpha words.\n\\begin{itemize}\n" ++
      "\\item Bravo words.\n\\begin{itemize}\n\\item Charlie words.\n\\end{itemize}\n" ++
      "\\end{itemize}\n\\end{frame}")) ["Bravo", "Charlie"] ==
      [some (2000 * s11 / 1000), some (2 * (2000 * s11 / 1000))])
  t "a quotation's text stands its level's leftmargin in"
    (xs (doc "{article}" "" "Alpha words.\n\\begin{quote}\nBravo words.\n\\end{quote}\nCharlie.")
      ["Bravo"] == [some (Dim.pt 25)])
  let qlist := doc "{article}" "" ("Alpha words.\n\\begin{quote}\nBravo words.\n" ++
    "\\begin{itemize}\n\\item Charlie words.\n\\end{itemize}\n\\end{quote}\nFoxtrot.")
  t "a list inside a quotation reads the next level's margin and topsep"
    (match place qlist "Bravo", place qlist "Charlie" with
     | some (bx, by_), some (cx, cy) =>
       bx == Dim.pt 25 && cx == Dim.pt 47 &&
         cy - by_ == Ir.leadingFor (Dim.pt 10) 1000 + Dim.pt 4 + Dim.pt 4
     | _, _ => false)
  t "a declared leftmargini keeps its value"
    (xs (doc "{article}" "\\setlength{\\leftmargini}{15pt}\n" nest) ["Bravo"] ==
      [some (Dim.pt 15)])
  let declQuote := doc "{article}" "\\setlength{\\leftmargini}{30pt}\n"
    "Alpha words.\n\\begin{quote}\nBravo words.\n\\end{quote}\nCharlie."
  t "a declared leftmargini reaches a quotation, as every level-one list reads it"
    (xs declQuote ["Bravo"] == [some (Dim.pt 30)])
  let tabled (body : String) := doc "{article}" "\\setlength{\\leftmargini}{30pt}\n"
    ("Alpha words.\n" ++ body)
  let table := "\n\\begin{tabular}{ll}\na & b \\\\\n\\end{tabular}\n"
  let listed := tabled ("\\begin{itemize}\n\\item Bravo words.\n" ++ table ++ "\\end{itemize}\n")
  let quoted := tabled ("\\begin{quote}\nBravo words.\n" ++ table ++ "\\end{quote}\n")
  let measured (src : String) (inset : Dim.Length) : Bool :=
    let d := (elabStr src).1
    let w := (Layout.Geom.ofPage d.page).textWidth - inset
    hasStr (HtmlDoc.emit { tableFit := fun avail _ _ _ _ _ => (none, avail == w) } d).1 "bt-overhang"
  t "the HTML measures a table in a list or a quotation off the margin its page stands them at"
    (match xs listed ["Bravo"], xs quoted ["Bravo"] with
     | [some l], [some q] => l == Dim.pt 30 && measured listed l && measured quoted (2 * q)
     | _, _ => false)
  -- Measured under lualatex: `\@listdepth` counts every list and quotation, whatever its kind.
  let mixed := "\\begin{enumerate}\n\\item Alpha words.\n\\begin{itemize}\n\\item Bravo words.\n" ++
    "\\begin{enumerate}\n\\item Charlie words.\n\\end{enumerate}\n\\end{itemize}\n" ++
    "\\end{enumerate}\n\\begin{quote}\nDelta words.\n\\begin{itemize}\n\\item Echo words.\n" ++
    "\\end{itemize}\n\\begin{quote}\nFoxtrot words.\n\\end{quote}\n\\end{quote}"
  let declared := "\\setlength{\\leftmargini}{20pt}\n\\setlength{\\leftmarginii}{40pt}\n" ++
    "\\setlength{\\leftmarginiii}{15pt}\n"
  t "a declared leftmargin reaches every list at its depth, whatever its kind"
    (xs (doc "{article}" declared mixed) ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot"] ==
      [20, 60, 75, 20, 60, 60].map fun p => some (Dim.pt p))
  let ex := Dim.pt 10 * 431 / 1000
  let listii := "\\makeatletter\n\\def\\@listii{\\leftmargin 30pt \\labelwidth\\leftmarginii " ++
    "\\advance\\labelwidth-\\labelsep \\topsep 4\\p@ \\@plus 1\\p@ \\parsep 1.5\\p@ " ++
    "\\itemsep \\parsep}\n\\setlength{\\leftmarginiii}{4ex}\n\\makeatother\n"
  t "a redefined \\@listii's leftmargin reaches every list two deep, and an ex is the class's"
    (xs (doc "{article}" listii mixed) ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot"] ==
      [some (Dim.pt 25), some (Dim.pt 55), some (Dim.pt 55 + 4 * ex), some (Dim.pt 25),
        some (Dim.pt 55), some (Dim.pt 55)])
  let abstract := "\\begin{abstract}\nAlpha words.\n\\begin{itemize}\n\\item Bravo words.\n" ++
    "\\begin{enumerate}\n\\item Charlie words.\n\\end{enumerate}\n\\end{itemize}\n" ++
    "Delta words.\n\\end{abstract}\nEcho words."
  t "a list in the abstract stands the class's lengths in, which its \\small leaves be"
    (xs (doc "{article}" "" abstract) ["Bravo", "Charlie", "Delta", "Echo"] ==
      [some (Dim.pt 47), some l3, some (Dim.pt 25), some 0])
  t "the list margins are the class's, fixed at the 10.95pt its 11pt option sets"
    (xs (doc "[11pt]{article}" "" nest) ["Bravo", "Charlie"] ==
      [some (2500 * s11 / 1000), some (2500 * s11 / 1000 + 2200 * s11 / 1000)])
  let fits (src : String) (avail : Dim.Length) : Bool :=
    hasStr (HtmlDoc.emit { tableFit := fun a _ _ _ _ _ => (none, a == avail) }
      (elabStr src).1).1 "bt-overhang"
  let width := (Layout.Geom.ofPage (elabStr (doc "{article}" "" "x")).1.page).textWidth
  let boxed := doc "{article}" "" ("\\begin{itemize}\n\\item Alpha words.\n\n" ++
    "\\noindent\\begin{minipage}{200pt}\n\\begin{itemize}\n\\item Bravo words.\n" ++ table ++
    "\\end{itemize}\n\\end{minipage}\n\\end{itemize}")
  t "the HTML measures a list in a box at the depth its page counts there"
    (match xs boxed ["Bravo"] with
     | [some b] => fits boxed (Dim.pt 200 - (b - Dim.pt 25))
     | _ => false)
  let inAbstract := doc "{article}" "" ("\\begin{abstract}\nAlpha words.\n\\begin{itemize}\n" ++
    "\\item Bravo words.\n" ++ table ++ "\\end{itemize}\n\\end{abstract}")
  t "the HTML measures a list in the abstract off the margins its page stands them at"
    (fits inAbstract (width - 2 * Dim.pt 25 - Dim.pt 22))
  let exList := doc "{article}" "\\setlength{\\leftmargini}{4ex}\n"
    ("\\begin{itemize}\n\\item Bravo words.\n" ++ table ++ "\\end{itemize}")
  t "the HTML measures an ex in a list margin as the page does, in the class's font"
    (xs exList ["Bravo"] == [some (4 * ex)] && fits exList (width - 4 * ex))
  let sheet (cls : String) : String :=
    (HtmlDoc.emit {} (elabStr (doc cls "" "x")).1).1
  let lv := ":is(li, dd, blockquote, :where(.abstract.quoted)) "
  let art := sheet "{article}"
  t "html each list level's padding is its leftmargin in the class's rem, under the length's property"
    (hasStr art (":where(ul, ol, dd) { padding-left: var(--leftmargini, 2.5rem); }\n" ++
        ":where(:is(blockquote, .abstract.quoted)) { padding: 0 var(--leftmargini, 2.5rem); }") &&
     hasStr art s!":where({lv}ul, {lv}ol, {lv}dd) \{ padding-left: var(--leftmarginii, 2.2rem); }" &&
     hasStr art (s!":where({lv}{lv}{lv}ul, {lv}{lv}{lv}ol, {lv}{lv}{lv}dd) " ++
       "{ padding-left: var(--leftmarginiv, 1.7rem); }"))
  t "html a declared leftmargini reaches the sheet as its property, in the class's rem"
    (hasStr (HtmlDoc.emit {} (elabStr declQuote).1).1 "--leftmargini: 3rem;")
  let sections := elemNodesList (· == "section") #[]
    (docNodesOf (elabStr (doc "{article}" "" abstract)).1).toList
  t "html the abstract hangs its quotation's margins on both sides, as its page does"
    (sections.any (fun n => ((nodeAttr "class" n).splitOn " ").contains "abstract") &&
      hasStr art ":where(:is(blockquote, .abstract.quoted)) { padding: 0 var(--leftmargini, 2.5rem); }")
  let pad (css : String) (k : Nat) : Option String :=
    (css.splitOn s!"padding-left: var(--{Ir.leftMarginName (k + 1)}, ")[1]?.bind fun rest =>
      (rest.splitOn ")")[0]?
  t "html a deck's lists stand one stage length in at its first two levels"
    (match pad (sheet "{beamer}") 0, pad (sheet "{beamer}") 1 with
     | some a, some b => a == b && a.endsWith "vh"
     | _, _ => false)
  t "html a webpage's lists keep the engine's one indent"
    ((List.range 4).all fun k => (pad (sheet "{webpage}") k).isSome &&
      pad (sheet "{webpage}") k == pad (sheet "{webpage}") 0)
  let cssSp (page : Ir.PageSpec) (v : String) : Option Dim.Length :=
    match remMilliOf v with
    | some m => some (m * page.fontSize / 1000)
    | none => do
      guard (v.endsWith "vh")
      let (m, sc) ← Decl.parseDecimal (v.dropEnd 2).toString
      return m * page.height / (100 * (sc : Int))
  let deck := "\\begin{frame}[t]\n" ++ nest ++ "\n\\end{frame}"
  t "each lineage's sheet hangs every list level where its page stands it"
    ([("{article}", nest), ("{webpage}", nest), ("{beamer}", deck)].all fun (cls, body) =>
      let src := doc cls "" body
      let page := (elabStr src).1.page
      let sheet := (HtmlDoc.emit {} (elabStr src).1).1
      let pads := (List.range 4).map fun k => (pad sheet k).bind (cssSp page)
      let depths := (List.range 4).map fun k =>
        (pads.take (k + 1)).foldl (fun d m => d.bind fun d => m.map (d + ·)) (some 0)
      let placed := xs src (if cls == "{beamer}" then levels.take 2 else levels)
      !placed.isEmpty && (placed.zip depths).all fun
        | (some p, some d) => withinSp (Dim.pt 1 / 200) p d
        | _ => false)

/-- A list's margin where a body length, a level macro naming another level's or none, a declared
indent or the class's abstract decides it, and a deep level's spacing named. -/
def listMarginChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let place (src : String) (w : String) : Option Dim.Length := do
    let (d, _) := elabStr src
    let g := Layout.Geom.ofPage d.page
    let l ← (bodyLines (layoutOf oneFace d { g with protrude := false })).find? fun l =>
      hasStr (lineText l) w
    let r ← (lineRuns l).find? fun r => r.2.1.startsWith w
    pure (r.2.2.1 - g.hmargin)
  let doc (pre body : String) : String :=
    "\\documentclass{article}" ++ pre ++ "\\begin{document}" ++ body ++ "\n\\end{document}"
  let html (src : String) : String := (HtmlDoc.emit {} (elabStr src).1).1
  let inAbstract := "\\begin{abstract}\nAlpha words.\n\\begin{itemize}\n\\item Bravo words.\n" ++
    "\\end{itemize}\n\\end{abstract}\nCharlie words."
  let bodySet := doc "" ("\\setlength{\\leftmargini}{3em}\n\\setlength{\\leftmarginii}{40pt}\n" ++
    inAbstract)
  t "a body em margin is fixed as the page fixes it, and the stylesheet ships that value"
    (place bodySet "Alpha" == some (Dim.pt 30) && place bodySet "Bravo" == some (Dim.pt 70) &&
      hasStr (html bodySet) "--leftmargini: 3rem" && !hasStr (html bodySet) "--leftmargini: 3em")
  t "a body leftmargin both artifacts honour is not named as a loss"
    ((elabStr bodySet).2.all fun d => !(d.code == "W0104" && hasStr (saidText d) "leftmargin"))
  let native := doc "" ("\\tokens{ leftmargini = 3em, leftmarginii = 4ex }\n" ++
    "\\begin{itemize}\n\\item Alpha words.\n\\begin{itemize}\n\\item Bravo words.\n" ++
    "\\end{itemize}\n\\end{itemize}")
  let ex4 := 4 * (Dim.pt 10 * 431 / 1000)
  t "a native body em and ex margin ship as the page sets them"
    (place native "Alpha" == some (Dim.pt 30) && place native "Bravo" == some (Dim.pt 30 + ex4) &&
      hasStr (html native) "--leftmargini: 3rem" && hasStr (html native) "--leftmarginii: 1.724rem")
  let three := "\\begin{itemize}\n\\item Alpha words.\n\\begin{itemize}\n\\item Bravo words.\n" ++
    "\\begin{itemize}\n\\item Charlie words.\n\\end{itemize}\n\\end{itemize}\n\\end{itemize}"
  let refd := doc "\\makeatletter\n\\def\\@listii{\\leftmargin\\leftmargini \\topsep 2pt}\n\\makeatother\n" three
  t "a level macro's margin may name another level's"
    (place refd "Bravo" == some (Dim.pt 50))
  let carried := doc "\\makeatletter\n\\def\\@listii{\\topsep 2pt}\n\\makeatother\n" three
  t "a level macro that sets no margin keeps the enclosing list's, as LaTeX's list does"
    (place carried "Bravo" == some (Dim.pt 50) &&
      place carried "Charlie" == some (Dim.pt 50 + Dim.pt 187 / 10))
  let declared := doc "\\usepackage{enumitem}\n\\setlist[itemize]{leftmargin=40pt}\n" inAbstract
  let sheet := html declared
  t "a declared indent is its type's at its level, in the page's unit, over the depth's default"
    (place declared "Bravo" == some (Dim.pt 65) &&
      hasStr sheet "\nul { padding-left: 4rem; }" &&
      hasStr sheet ":where(ul, ol, dd) { padding-left: var(--leftmargini, 2.5rem); }")
  let typed := html (doc "\\style{itemize}{ indent = 30pt }\n\\style{itemize2}{ indent = 15pt }\n"
    "\\begin{itemize}\n\\item Alpha.\n\\end{itemize}")
  t "a first level's declared indent reaches every level no deeper declaration takes, as the page's"
    (hasStr typed "\nul { padding-left: 3rem; }" &&
      hasStr typed "\nul ul:not(ul ul ul) { padding-left: 1.5rem; }" &&
      !hasStr typed "ul:not(ul ul) {")
  let tabular := doc "" ("{\\small\\setlength{\\tabcolsep}{2em}\n" ++
    "\\begin{tabular}{ll}Alpha & Bravo\\\\\\end{tabular}}")
  t "a body table length keeps its em for the font in force, as LaTeX evaluates it there"
    (hasStr (html tabular) "--tabcolsep: 2em" && !hasStr (html tabular) "--tabcolsep: 2rem")
  let deep := (elabStr (doc "\\makeatletter\n\\def\\@listv{\\leftmargin 10pt \\topsep 3pt}\n\\makeatother\n"
    "Words.")).2
  t "a fifth level macro's spacing is named as no list five deep reads it"
    (deep.any fun d => d.code == "W0104" && hasStr (saidText d) "topsep")

/-- The abstract sets in its class's form (`Ir.AbstractForm`): article's quotation, a title page's
full measure, beamer's inset beside its own paragraphs alone, and a redefinition's quote. -/
def abstractFormChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let lineOf (src : String) (w : String) : Option (Layout.Geom × Layout.LineOut) := do
    let (d, _) := elabStr src
    let g := Layout.Geom.ofPage d.page
    let l ← (bodyLines (layoutOf oneFace d { g with protrude := false })).find? fun l =>
      hasStr (lineText l) w
    pure (g, l)
  let place (src : String) (w : String) : Option Dim.Length := do
    let (g, l) ← lineOf src w
    let r ← (lineRuns l).find? fun r => r.2.1.startsWith w
    pure (r.2.2.1 - g.hmargin)
  -- How far short of the measure's right edge a line's last glyph ends.
  let short (src : String) (w : String) : Option Dim.Length := do
    let (g, l) ← lineOf src w
    let r ← (lineRuns l).back?
    pure (g.hmargin + g.textWidth - (r.2.2.1 + r.2.2.2))
  let html (src : String) : String := (HtmlDoc.emit {} (elabStr src).1).1
  let inAbstract := "\\begin{abstract}\nAlpha words.\n\\begin{itemize}\n\\item Bravo words.\n" ++
    "\\end{itemize}\n\\end{abstract}\nCharlie words."
  let report := "\\documentclass{report}\\begin{document}" ++ inAbstract ++ "\n\\end{document}"
  t "a report's abstract stands on its title page as no quotation, its lists one level deep"
    (place report "Alpha" == some 0 && place report "Bravo" == some (Dim.pt 25) &&
      !hasStr (html report) "quoted\"" && hasStr (html report) "class=\"abstract")
  let article := "\\documentclass{article}\\begin{document}" ++ inAbstract ++ "\n\\end{document}"
  let passed := "\\PassOptionsToClass{notitlepage}{report}\n" ++ report
  t "a notitlepage passed to report sets its abstract as the article's quotation"
    (place article "Alpha" == some (Dim.pt 25) && place passed "Alpha" == some (Dim.pt 25) &&
      place passed "Bravo" == place article "Bravo")
  -- beamer's template, `\leftskip2em\rightskip2em plus 1fill` at the class's 10.95pt.
  let em2 := 2 * (Dim.pt 1095 / 100)
  let deck := "\\documentclass{beamer}\\begin{document}\\begin{frame}[t]\nZulu reference line " ++
    "with enough words to run across the whole frame and wrap onto the next line.\n" ++
    "\\begin{abstract}\nAlpha words in the abstract paragraph which runs long enough to wrap " ++
    "across several lines of the frame.\n\\begin{itemize}\n\\item Bravo words in a list item " ++
    "which also runs long enough to wrap across the frame here.\n\\begin{itemize}\n" ++
    "\\item Charlie words.\n\\end{itemize}\n\\end{itemize}\nDelta words after the list in the " ++
    "abstract which runs long enough to wrap across the frame.\n\\end{abstract}\n\\end{frame}\n" ++
    "\\end{document}"
  t "a deck's abstract text stands 2em in from both sides as beamer's, its lists at their own margins"
    (place deck "Zulu" == some 0 && place deck "Alpha" == some em2 &&
      place deck "Bravo" == some em2 && place deck "Charlie" == some (2 * em2) &&
      place deck "Delta" == some em2 && ((short deck "Alpha").map (decide <| em2 ≤ ·)).getD false)
  let deckDoc := (elabStr deck).1
  let insetCss := HtmlDoc.tableLengthCss (HtmlDoc.lengthBasisOf deckDoc) (.ofLength em2)
  t "a deck page insets its abstract's paragraphs as the deck does, and not its lists"
    (hasStr (html deck) "class=\"abstract size-small inset" &&
      hasStr (html deck) s!".abstract.inset > p \{ padding: 0 {insetCss}; }" &&
      !hasStr (html deck) "quoted\"")
  let poster := "\\documentclass{poster}\\begin{document}\\begin{frame}{An Invented Poster Probe}\n" ++
    "Zulu reference line with enough words to run across the whole face and wrap onto the next " ++
    "line of the poster board here and further.\n\\begin{abstract}\nAlpha words in the abstract " ++
    "paragraph which runs long enough to wrap across several lines of the board.\n" ++
    "\\begin{itemize}\n\\item Bravo words.\n\\end{itemize}\n\\end{abstract}\n\\end{frame}\n" ++
    "\\end{document}"
  let posterEm2 := 2 * (Dim.pt 2488 / 100)
  let off (src w : String) : Option Dim.Length := do pure ((← place src w) - (← place src "Zulu"))
  t "a poster's abstract text stands 2em of its class size in, as beamer's template sets it"
    (off poster "Alpha" == some posterEm2 && off poster "Bravo" == some posterEm2)
  let redefined := "\\documentclass{report}\n\\renewenvironment{abstract}{\\vskip 0.1in" ++
    "\\centerline{\\large\\bf Abstract}\\vspace{1ex}\\begin{quote}}{\\par\\end{quote}" ++
    "\\vskip 2ex}\n\\begin{document}\n\\noindent Zulu reference words in the body.\n" ++
    "\\begin{abstract}\nAlpha words in the abstract paragraph which runs long enough to wrap " ++
    "across several lines of the page, so the measure shows on both sides of it here.\n" ++
    "\\end{abstract}\n\\end{document}"
  t "a report's abstract redefined on a quote keeps the quote's margins, as its refusal names"
    (place redefined "Alpha" == some (Dim.pt 25) &&
      ((short redefined "Alpha").map (decide <| Dim.pt 25 ≤ ·)).getD false &&
      (elabStr redefined).2.any fun d => d.code == "W0303" && hasStr (saidText d) "quotation margins")

/-- A list right after a heading opens no `\topsep`: its first item stands where a paragraph after
the heading stands. -/
def afterHeadingListChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (body : String) : String :=
    "\\documentclass{article}\\begin{document}Alpha.\n\n\\section*{Bravo}\n\n" ++ body ++
      "\n\nDelta.\n\\end{document}"
  let steps (src : String) (words : List String) : List Dim.Length :=
    let c := censusOfSrc oneFace src
    let v := words.filterMap (lineYOf c 0 ·)
    (v.zip v.tail).map fun (a, b) => b - a
  let lead := Ir.leadingFor (Dim.pt 10) 1000
  let para := steps (doc "Charlie.") ["Bravo", "Charlie."]
  for (name, el) in [("itemize", "\\begin{itemize}\n\\item Charlie.\n\\end{itemize}"),
      ("quote", "\\begin{quote}\nCharlie.\n\\end{quote}")] do
    t s!"{name} right after a heading stands where a paragraph after it stands"
      (!para.isEmpty && steps (doc el) ["Bravo", "Charlie."] == para)
    t s!"{name} right after a heading still closes with its topsep and partopsep"
      (steps (doc el) ["Charlie.", "Delta."] == [lead + Dim.pt 10])

/-- A heading keeps with the next block's first box, so it never ends a page. -/
def headingKeepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf oneFace
  let src (n : Nat) (after : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\begin{document}" ++
    String.join ((List.range n).map fun i => s!"Filler line {i}.\n\n") ++
    "\\section{Heading}\n" ++ after ++ "\n\\end{document}"
  let pageOf (c : Array CensusPage) (needle : String) : Option Nat :=
    (List.range c.size).find? fun i => (lineYOf c i needle).isSome
  -- An image carries no text: its page is the one its box ships on.
  let imagePage (c : Array CensusPage) : Option Nat :=
    (List.range c.size).find? fun i => 0 < (c[i]?.map (·.images)).getD 0
  let shapes : List (String × Font.FontSet × String × (Array CensusPage → Option Nat)) :=
    [("its text", oneFace, "Body text after the heading, long enough to run onto a second " ++
        "line of the page so that the club rule has two lines to keep together.",
        (pageOf · "Body text")),
     ("a tall picture", oneFace, "\\begin{tikzpicture}\\draw (0,0) -- (0,5);" ++
        "\\node at (0.5,4.5) {Kilo};\\end{tikzpicture}\n\nMore text after the picture.",
        (pageOf · "Kilo")),
     ("a second heading", oneFace, "\\subsection{Second}\nBody text after both headings, " ++
        "long enough to run onto a second line of the page so that the club rule has two lines.",
        (pageOf · "Second")),
     ("a tall image", oneFace, "\\noindent\\includegraphics[width=20pt,height=150pt]{tall.png}" ++
        "\n\nMore text after the image.", imagePage),
     ("a tall display", mathSet, "\\[\\begin{array}{c}\\text{Kilo}\\\\" ++
        "\\\\".intercalate (List.replicate 8 "x") ++ "\\end{array}\\]\n\nMore text after it.",
        (pageOf · "Kilo"))]
  for (what, fonts, after, follower) in shapes do
    let placements := (List.range 40).map fun k =>
      let c := censusOfSrc fonts (src (20 + k) after)
      (20 + k, pageOf c "Heading", follower c)
    let strands := placements.filterMap fun (n, h, b) =>
      match h, b with
      | some h, some b => if h == b then none else some n
      | _, _ => some n
    t s!"a heading shares a page with {what} wherever it falls (strands: {strands})"
      strands.isEmpty
    t s!"the heading fixtures with {what} reach a page boundary"
      (placements.any fun (_, h, _) => h == some 1)

/-- A frame's content opens on a baseline below the title box, and a picture's bottom is a baseline. -/
def frameBodyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (opt : String) : String :=
    "\\documentclass{beamer}\\usetheme{moloch}\\begin{document}\\begin{frame}" ++ opt ++
    "{Heading}\nWords on one line.\n\\end{frame}\\end{document}"
  let run (src : String) : Option (Layout.Geom × Dim.Length × Dim.Length) := do
    let (d, _) := elabStr src
    let g := Layout.Geom.ofPage d.page
    let p ← (layoutOf oneFace d g).pages[0]?
    -- The bar: the page-top fill, not the page's own ground.
    let bar := p.fills.foldl (fun m f =>
      if f.x == 0 && f.y == 0 && f.h < g.pageH then max m (f.y + f.h) else m) 0
    let l ← p.lines.find? fun l => !l.furniture && hasStr (lineText l) "Words"
    pure (g, bar, l.y)
  match run (deck "[t]"), run (deck ""), run (deck "[b]") with
  | some (g, barT, yT), some (_, barC, yC), some (_, _, yB) =>
    let lead := Ir.leadingFor g.fontSize g.leading
    t "a top frame's first line stands the title box's skip, the top skip and a leading below the bar"
      (yT == barT + g.fontSize / 4 + Dim.mm 2 + lead)
    let top := yC - lead - (barC + g.fontSize / 4)
    let bottom := yB - yC
    t "a centred frame's leftover splits evenly above and below its content"
      (0 < top && top ≤ bottom && bottom ≤ top + Dim.Length.quantum)
  | _, _, _ => t "frame body fixtures lay out" false
  let art (inner : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\begin{document}Alpha.\n\n" ++
    "\\begin{center}\n" ++ inner ++ "\n\\end{center}\n\nCharlie.\n\\end{document}"
  let picSrc := art "\\begin{tikzpicture}\\fill (0,0) rectangle (2,1);\\end{tikzpicture}"
  let (pd, _) := elabStr picSrc
  let below : Option Dim.Length := do
    let p ← (layoutOf oneFace pd).pages[0]?
    let (_, fy, _, fh) ← (pageDraws p)[0]?.map fun (g, _, _) => markExtent g
    let l ← p.lines.find? fun l => hasStr (lineText l) "Charlie."
    pure (l.y - (fy + fh))
  let c := censusOfSrc oneFace (art "Bravo.")
  let pitch : Option Dim.Length := do
    let b ← lineYOf c 0 "Bravo."
    let d ← lineYOf c 0 "Charlie."
    pure (d - b)
  t "the line under a centred picture stands as far below it as under a centred line"
    (below.isSome && below == pitch)

/-- A centred frame centres its content box whole. -/
def frameContentEndChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let deck (frames : List String) : String :=
    "\\documentclass{beamer}\\usetheme{moloch}\\pictures{ tool = none }" ++
    "\\begin{document}" ++
    String.join (frames.map fun f => "\\begin{frame}{Heading}\n" ++ f ++ "\n\\end{frame}") ++
    "\\end{document}"
  let y (src : String) (page : Nat) (word : String) : Option Dim.Length :=
    lineYOf (censusOfSrc oneFace src) page word
  let lone := y (deck ["\\begin{center}\nWords on one line.\n\\end{center}"]) 0 "Words"
  t "a centred frame's lone center line stands where its plain line stands"
    (lone.isSome && lone == y (deck ["Words on one line."]) 0 "Words")
  let pic (below extra : String) : String :=
    "\\begin{center}\n\\begin{tikzpicture}\n" ++
    s!"\\useasboundingbox (-1,{below}) rectangle (4,1);\n" ++ extra ++
    "\\node (a) at (0,0) {Kilo};\n\\node (b) at (3,0) {Lima};\n\\draw[->] (a) -- (b);\n" ++
    "\\end{tikzpicture}\n\\end{center}"
  match y (deck [pic "-1" ""]) 0 "Kilo", y (deck [pic "-2" ""]) 0 "Kilo" with
  | some y1, some y2 =>
    let lift := y1 - y2
    t "a declared box grown one cm below lifts a centred frame's ink half a cm"
      (Dim.mm 5 - Dim.Length.quantum ≤ lift && lift ≤ Dim.mm 5 + Dim.Length.quantum)
  | _, _ => t "declared-box frame fixtures lay out" false
  let two := deck [pic "-2" "", pic "-2" "\\node at (1.5,-1.5) {November};\n"]
  match y two 0 "Kilo", y two 1 "Kilo" with
  | some k1, some k2 =>
    -- lualatex moves them 0.03 pt: the frame numbers 1 and 2 differ in height.
    t "two centred frames sharing one declared box keep their shared nodes still"
      (k1 - k2 ≤ Dim.pt 1 / 20 && k2 - k1 ≤ Dim.pt 1 / 20)
  | _, _ => t "shared-box frame fixtures lay out" false

/-- A frame's text area ends 4 pt above its footline, and the footline is moloch's. -/
def footlineChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "footline: the shipped Fira Sans parses" false
  let tol : Dim.Length := Dim.pt 3 / 2
  let near (a b slack : Dim.Length) : Bool := a - b ≤ slack && b - a ≤ slack
  let bp (milli : Int) : Dim.Length := Dim.pt 1 * milli / 1000
  let build (pre : String) (frames : String) : Layout.Geom × Layout.Out :=
    let (doc, _) := elabStr ("\\documentclass[10pt]{beamer}\\usetheme{moloch}" ++ pre ++
      "\\begin{document}" ++ frames ++ "\\end{document}")
    let geom := Layout.Geom.ofPage doc.page
    (geom, layoutOf fira doc geom)
  let baseline (out : Layout.Out) (page : Nat) (word : String) : Option Dim.Length :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      !l.furniture && hasStr (lineText l) word).map (·.y)
  let number (out : Layout.Out) (page : Nat) : Option Layout.LineOut :=
    out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.furniture && lineText l == toString (page + 1)
  let (geom, out) := build ""
    ("\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
     "\\begin{frame}[t]{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
     "\\begin{frame}\nBravo words.\n\\end{frame}\n")
  t "footline: the frame number is set at the tiny step, as moloch's footline font"
    ([0, 1, 2].all fun i => ((number out i).map (·.size == Ir.scaleStepIn Ir.sizeScale geom.fontSize "tiny")).getD false)
  t "footline: the number's baseline stands where lualatex's does, a round digit's higher"
    ([(0, 3985), (1, 3985), (2, 4045)].all fun (i, up) =>
      ((number out i).map fun l => near (geom.pageH - l.y) (bp up) (Dim.pt 1 / 20)).getD false)
  t "footline: the number's right edge is 5 pt in from the paper's, as moloch insets it"
    ([0, 1, 2].all fun i =>
      ((number out i).map fun l => near (geom.pageW - (l.x + l.setWidth)) (bp 4981)
        (Dim.pt 1 / 20)).getD false)
  t "footline: a titled centred frame centres above its footline, as lualatex does"
    (((baseline out 0 "Alpha").map fun y => near y (bp 151219) tol).getD false)
  t "footline: an untitled centred frame opens at the paper's top, as lualatex does"
    (((baseline out 2 "Bravo").map fun y => near y (bp 136275) tol).getD false)
  t "footline: a top-aligned frame is untouched by the floor (control)"
    (((baseline out 1 "Alpha").map fun y => near y (bp 49405) tol).getD false)
  let (_, noted) := build "" "\\framefoot{Kilo gauge}\n\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n"
  let noteLine := noted.pages[0]?.bind fun p => p.lines.find? fun l =>
    l.furniture && hasStr (lineText l) "Kilo"
  t "footline: a footer's descender raises the band's one baseline, as in lualatex"
    ((noteLine.map fun l => near (geom.pageH - l.y) (bp 5046) (Dim.pt 1 / 20) &&
      ((number noted 0).map (·.y == l.y)).getD false).getD false)
  t "footline: and the centred line rises with the floor, as in lualatex"
    (((baseline noted 0 "Alpha").map fun y => near y (bp 150412) tol).getD false)

/-- The first line of a page stands `\topskip` below the text area's top, or on its own box where
that is taller. -/
def topskipChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (opts body : String) : String :=
    s!"\\documentclass[{opts}]\{article}" ++
    "\\usepackage[paperwidth=5in,paperheight=4in,top=1in,bottom=1in,left=1in,right=1in]{geometry}" ++
    "\\pagestyle{empty}\\begin{document}" ++ body ++ "\\end{document}"
  let first (src : String) (pg : Nat) (word : String) : Option Dim.Length :=
    lineYOf (censusOfSrc oneFace src) pg word
  let near (y : Option Dim.Length) (milli : Int) : Bool :=
    (y.map fun v => let want := Dim.Length.ofBpMilli milli
      v - want ≤ Dim.pt 1 / 10 && want - v ≤ Dim.pt 1 / 10).getD false
  t "topskip: a body line stands \\topskip below the text area, as in lualatex"
    (near (first (page "10pt" "Alpha Hotel words.") 0 "Alpha") 81963)
  t "topskip: at 11pt and 12pt it is the class's own \\topskip"
    (near (first (page "11pt" "Alpha Hotel words.") 0 "Alpha") 82959 &&
     near (first (page "12pt" "Alpha Hotel words.") 0 "Alpha") 83955)
  t "topskip: a line of x-height letters stands on the same grid line"
    (near (first (page "10pt" "acme.") 0 "acme") 81963)
  t "topskip: a first line taller than \\topskip stands on its own glyph box"
    (near (first (page "10pt" "{\\LARGE Alpha Hotel}") 0 "Alpha") 85080)
  t "topskip: the next page's first line keeps the rule, and a top parskip is dropped"
    (near (first (page "10pt" "Alpha words.\\newpage Hotel words.") 1 "Hotel") 81963 &&
     near (first (page "10pt" "\\setlength{\\parskip}{6pt}Alpha words.") 0 "Alpha") 81963)

/-- A picture occupies TikZ's box: a declared box moves ink and text by its growth, and a node's
`inner sep` reserves room whether or not a path draws it. -/
def pictureBoxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src (box node : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\begin{document}Above.\n\n" ++
    "\\begin{center}\n\\begin{tikzpicture}\n" ++ box ++ node ++
    "\n\\end{tikzpicture}\n\\end{center}\n\nBelow.\n\\end{document}"
  -- Elaborated as the driver does, with layout's label measurement.
  let elabM (s : String) : Ir.Doc × Array Diag :=
    let (toks, lds) := Lex.lex "t" s
    let (raws, pds) := Parse.parse "t" toks
    Elab.runRaws "t" raws (lds ++ pds)
      (Layout.labelMetric (Layout.Geom.ofPage (Elab.run "t" s).1.page) oneFace)
  let probe (s : String) : Option (Dim.Length × Dim.Length × Dim.Length × Dim.Length) := do
    let (doc, _) := elabM s
    let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
    let ay ← lineYOf c 0 "Above."
    let lx ← lineXOf c 0 "Label"
    let ly ← lineYOf c 0 "Label"
    let bl ← lineYOf c 0 "Below."
    pure (ay, lx, ly, bl)
  let node := "\\node at (0,0) {Label};"
  let cm : Dim.Length := Dim.mm 10
  let boxed := src "\\useasboundingbox (-2,-1) rectangle (2,1);\n" node
  let declared := probe boxed
  let taller := probe (src "\\useasboundingbox (-2,-1) rectangle (2,2);\n" node)
  let deeper := probe (src "\\useasboundingbox (-2,-2) rectangle (2,1);\n" node)
  let wider := probe (src "\\useasboundingbox (-4,-1) rectangle (2,1);\n" node)
  t "a declared box grown one cm above moves its ink and the text below one cm down"
    (match declared, taller with
     | some (a0, x0, l0, b0), some (a1, x1, l1, b1) =>
       a1 == a0 && x1 == x0 && l1 - l0 == cm && b1 - b0 == cm
     | _, _ => false)
  t "a declared box grown one cm below moves only the text below it"
    (match declared, deeper with
     | some (a0, x0, l0, b0), some (a1, x1, l1, b1) =>
       a1 == a0 && x1 == x0 && l1 == l0 && b1 - b0 == cm
     | _, _ => false)
  t "a declared box grown two cm left centres the box, so its ink moves one cm right"
    (match declared, wider with
     | some (a0, x0, l0, b0), some (a1, x1, l1, b1) =>
       a1 == a0 && x1 - x0 == cm && l1 == l0 && b1 == b0
     | _, _ => false)
  t "the declaration is a size, not a drawing: no loss is named for it"
    (!((elabM boxed).2.any (·.code == "W0334")))
  let (dd, _) := elabM boxed
  let page := (HtmlDoc.emit
    { labelMetric := Layout.labelMetric (Layout.Geom.ofPage dd.page) oneFace } dd).1
  t "the SVG's viewBox is the declared box"
    (hasStr page s!"viewBox=\"0 0 {(4 * cm).toBpString} {(2 * cm).toBpString}\"")
  let (od, _) := elabM (src "\\useasboundingbox (0,0) rectangle (2,1);\n\\fill (0,0) rectangle (1,1);\n"
    "\\node at (3.5,0.5) {Outside};")
  let svgs := elemAttrsList (· == "svg") #[] (HtmlDoc.emitTree
    { labelMetric := Layout.labelMetric (Layout.Geom.ofPage od.page) oneFace } od).2.1.toList
  t "html: a picture's SVG paints ink outside its declared box"
    (!svgs.isEmpty && svgs.all fun (_, a) => HtmlDoc.attrOf? a "overflow" == some "visible")
  let padded := probe (src "" "\\node at (0,0) {Label};")
  let tight := probe (src "" "\\node[inner sep=0pt] at (0,0) {Label};")
  let sep := Picture.innerSep (Layout.Geom.ofPage dd.page).fontSize
  t "an undrawn node's inner sep reserves room above and below its label"
    (match padded, tight with
     | some (a0, _, l0, b0), some (a1, _, l1, b1) =>
       a1 == a0 && l0 - l1 == sep && 2 * sep ≤ b0 - b1 && b0 - b1 ≤ 2 * sep + Dim.Length.quantum
     | _, _ => false)

/-- Sibling picture labels share a baseline whatever their descenders, a hand-written correction
stays inert, and the measured extent covers glyphs above the band. -/
def labelBaselineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  -- `\topskip` 0 pt, so a picture opening the page stands at the text area's top.
  let run (body : Array Ir.Block) : Layout.Out :=
    layoutOf oneFace { body := body, tokens := ({} : Ir.Tokens).declare "topskip" {} } geom
  let pair (a b : String) : Ir.Pic.Picture := { shapes := #[
    .label (Dim.pt 10) (Dim.pt 20) #[.text a] Ir.Color.black 1000 .center,
    .label (Dim.pt 60) (Dim.pt 20) #[.text b] Ir.Color.black 1000 .center] }
  let baselines (p : Ir.Pic.Picture) : List Dim.Length :=
    ((run #[.picture p]).pages[0]?.map fun pg =>
      (pg.lines.filter (!·.furniture)).toList.map (·.y)).getD []
  t "two sibling labels ship two lines"
    ((baselines (pair "candle" "misty")).length == 2)
  t "a descender does not lift a label off its neighbour's baseline"
    (match baselines (pair "candle" "misty") with
     | [p, q] => p == q
     | _ => false)
  t "nor does a word of nothing but descenders"
    (match baselines (pair "WAX" "gjpqy") with
     | [p, q] => p == q
     | _ => false)
  -- Absolute: a uniform shift of every label passes the equalities above and fails here.
  let m := Layout.labelMetric geom oneFace
  let solo : Ir.Pic.Picture := { shapes := #[
    .label (Dim.pt 10) (Dim.pt 5) #[.text "candle"] Ir.Color.black 1000 .center] }
  let hull := solo.inkBbox m
  let inkS := m #[.text "candle"] 1000
  t "the shipped baseline is the one the IR predicts"
    (((run #[.picture solo]).pages[0]?.bind fun pg =>
      (pg.lines.filter (!·.furniture))[0]?.map fun l =>
        l.y == geom.vmargin
          + (hull.2.2 - Ir.Pic.labelBaseline (Dim.pt 5) .center inkS)).getD false)
  let inkV := m #[.text "candle"] 1000
  let inkI := m #[.text "misty"] 1000
  t "the declared band is one number per face, whatever the word"
    (inkV.height == inkI.height && inkV.depth == inkI.depth)
  t "the set width still follows the glyphs"
    (inkV.w != inkI.w && inkV.w > 0)
  t "so does the baseline the placement reads"
    (Ir.Pic.labelBaseline (Dim.pt 20) .center inkV
      == Ir.Pic.labelBaseline (Dim.pt 20) .center inkI)
  let seat := Ir.Pic.labelBaseline (Dim.pt 20) .center inkV - Dim.pt 20
  let font := oneFace.body
  let units (u : Int) : Dim.Length := u * geom.fontSize / (font.unitsPerEm : Int)
  t "the band is the face's capitals-to-descent box, as a border measures it"
    (let span := units (font.capHeight - font.descent)
     span - Dim.Length.quantum <= inkV.height + inkV.depth &&
       inkV.height + inkV.depth <= span + Dim.Length.quantum)
  let xh := units (font.xHeightOptical : Int)
  t "the seat is half the face's measured x-height below the anchor, to within two scaled points"
    (-xh / 2 - 2 * Dim.Length.quantum <= seat && seat <= -xh / 2 + 2 * Dim.Length.quantum)
  let xInk := m #[.text "xz"] 1000
  let rule : Ir.Color := { r := 200, g := 40, b := 40 }
  let ruled : Ir.Pic.Picture := { shapes := #[
    .rect 0 (Dim.pt 5 - Dim.pt 1 / 10) (Dim.pt 4) (Dim.pt 1 / 5) rule,
    .label (Dim.pt 20) (Dim.pt 5) #[.text "xz"] Ir.Color.black 1000 .center] }
  t "x-height letters measure the face's x-height box: its ex, no depth"
    (xInk.boxDepth == 0 && xInk.boxHeight - Dim.Length.quantum <= xInk.ex &&
      xInk.ex <= xInk.boxHeight + Dim.Length.quantum)
  t "on the page, x-height letters stand half an ex below the rule at their anchor"
    (match (run #[.picture ruled]).pages[0]? with
     | some pg =>
       match (pageDraws pg)[0]?, (pg.lines.filter (!·.furniture))[0]? with
       | some (g, _, _), some l =>
         let (_, fy, _, fh) := markExtent g
         let below := l.y - (fy + fh / 2)
         xh / 2 - 2 * Dim.Length.quantum <= below && below <= xh / 2 + 2 * Dim.Length.quantum
       | _, _ => false
     | none => false)
  let milli (s : Option String) : Option Int := s.bind fun v =>
    (Decl.parseDecimal v).map fun (mant, scale) => mant * 1000 / scale
  let ruledSvg := HtmlDoc.pictureSvg { labelMetric := m } ruled
  t "html: and in the SVG, against the same rule"
    (match (elemAttrsOne (· == "rect") #[] ruledSvg)[0]?,
        (elemAttrsOne (· == "text") #[] ruledSvg)[0]? with
     | some (_, ra), some (_, ta) =>
       match milli (HtmlDoc.attrOf? ra "y"), milli (HtmlDoc.attrOf? ra "height"),
           milli (HtmlDoc.attrOf? ta "y") with
       | some ry, some rh, some ty =>
         let below := ty - (ry + rh / 2)
         let want := Dim.Length.toBpMilli (xh / 2)
         want - 2 <= below && below <= want + 2
       | _, _, _ => false
     | _, _ => false)
  let reach (c : Char) : Option (Int × Int) := (font.gid c).bind font.yExtent
  let bound : Dim.Length := match reach 'l', reach 'p' with
    | some (_, asc), some (desc, _) => max (units asc - xh) (units (-desc)) / 2 + 2 * Dim.Length.quantum
    | _, _ => 0
  for w in ["xz", "HIE", "Hg", "gap", "query", "label", "Fly", "42"] do
    let ink := m #[.text w] 1000
    let tex := -((ink.boxHeight - ink.boxDepth) / 2)
    t s!"the seat departs from TeX's by no more than the declared bound: {w}"
      (bound > 2 * Dim.Length.quantum && ((Ir.Pic.labelBaseline 0 .center ink) - tex).abs <= bound)
  let dominated : Ir.Pic.LabelInk :=
    { w := 0, height := inkV.height - Dim.pt 1, depth := inkV.depth - Dim.pt 1 }
  t "a phantom box the label already covers moves neither letters nor box"
    (Ir.Pic.labelInkBox 0 (Dim.pt 20) .center (inkV.join dominated)
        == Ir.Pic.labelInkBox 0 (Dim.pt 20) .center inkV
      && Ir.Pic.labelBaseline (Dim.pt 20) .center (inkV.join dominated)
        == Ir.Pic.labelBaseline (Dim.pt 20) .center inkV)
  let deeper : Ir.Pic.LabelInk := { w := 0, height := 0, depth := inkV.depth + Dim.pt 2 }
  let boxV := Ir.Pic.labelInkBox 0 (Dim.pt 20) .center inkV
  let boxJ := Ir.Pic.labelInkBox 0 (Dim.pt 20) .center (inkV.join deeper)
  t "a phantom deeper than the band grows it, and only to the join"
    (boxJ.1.2 <= boxV.1.2 && boxV.2.2 <= boxJ.2.2
      && (inkV.join deeper).depth == inkV.depth + Dim.pt 2
      && (inkV.join deeper).height == inkV.height)
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
  t "while the face's declared descent covers its descenders"
    (match (do
      let g ← font.gid 'y'
      let (lo, _) ← font.yExtent g
      return lo) with
     | some lo => font.descent <= lo
     | none => false)
  let accent : Ir.Pic.Picture := { shapes := #[
    .label 0 0 #[.text "É"] Ir.Color.black 1000 .center] }
  let accentInk := m #[.text "É"] 1000
  let accentBase := Ir.Pic.labelBaseline 0 .center accentInk
  let accentBox := Ir.Pic.labelGlyphBox 0 0 .center accentInk
  t "the reserved box covers a diacritic above the alignment band"
    (accentInk.boxHeight > accentInk.height
      && accentBase + accentInk.boxHeight <= accentBox.2.2)
  t "the shipped diacritic stays inside the picture's measured top"
    (match (run #[.picture accent]).pages[0]? with
     | some pg =>
       (pg.lines.filter (!·.furniture)).any fun l =>
         l.segs.any fun s => match s with
         | .run idx _ _ _ glyphs sz _ _ raise _ _ =>
           glyphs.any fun (g, ch, _) =>
             ch == 'É' && l.y -
               (Layout.glyphVExtent (oneFace.get idx)
                 (if sz == 0 then l.size else sz) raise g).1 >= geom.vmargin
         | _ => false
     | none => false)

/-- An unstyled role ships exactly the pages its content ships unwrapped. -/
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
  let linesOf (src : String) : Array (String × Dim.Length) :=
    let (d, _) := elabStr src
    (layoutOf oneFace d geom).pages.flatMap fun p =>
      p.lines.map fun l => (l.segs.foldl (fun s seg => match seg with
        | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.foldl (fun s (_, c, _) => s.push c) s
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

/-- A nav renders as the PDF outline when unpinned, as nothing when pinned, and drops whole from the
markdown twin. -/
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
  t "the outline holds one entry per menu link that lands, in order"
    (out.outline.map (·.title) == #["One", "Two", "Out"])
  t "in-document targets resolve to the pages their headings land on"
    ((out.outline.find? (·.title == "One")).map (·.page) == some (some 0) &&
     (out.outline.find? (·.title == "Two")).map (·.page) == some (some 1))
  t "an external target rides as its URL"
    ((out.outline.find? (·.title == "Out")).map (·.url) ==
      some (some "https://example.org"))
  t "a target landing nowhere is left out of the outline, named once for the PDF"
    ((out.outline.find? (·.title == "Lost")).isNone &&
      (out.diags.filter fun d => d.code == "W0326" && d.output == some .pdf).size == 1)
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
  let md := MarkdownDoc.emit doc
  t "the twin drops both navs and keeps the sections"
    (!hasStr md "](#one-head)" && !hasStr md "](#top)" &&
      hasStr md "One Head" && hasStr md "second body")

/-- Under a class-declared zero `\parskip`, headings keep more space above than below, neither zero. -/
def headingRhythmChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let (d, _) := elabStr ("\\documentclass{scrartcl}\n\\begin{document}\n" ++
    "Opening line.\n\n\\section*{Alpha}\n\nClosing line.\n\\end{document}")
  t "premise: the class declared a zero parskip"
    ((d.page.parskip.map (·.width.fixed)) == some 0)
  let out := layoutOf oneFace d
  let c := censusOf #[] out
  let yOf (s : String) : Option Dim.Length := lineYOf c 0 s
  match yOf "Opening", yOf "Alpha", yOf "Closing" with
  | some yo, some yh, some yc =>
    let leading := Ir.leadingFor (Layout.Geom.ofPage d.page).fontSize
    t "the heading's own rhythm stands: a full unit above plus a half below"
      (yc - yo ≥ 2 * leading
        + (Ir.headingBeforeDefault (Layout.Geom.ofPage d.page).fontSize).width.fixed
        + (Ir.headingAfterDefault (Layout.Geom.ofPage d.page).fontSize).width.fixed
        - Dim.pt 1)
    t "more space above the heading than below it"
      (yh - yo > yc - yh)
  | _, _, _ => failures ref "heading rhythm: probe lines missing from the page"

/-- A title's ragged lines balance and never strand one word, and a declared break that does not fit
is named. -/
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
  t "the re-flow is not an overfull line, so W0005 stays silent and no record carries one"
    (!lostOut.diags.any (·.code == "W0005") && !lostOut.diags.any (·.carries.contains .W0005))
  t "the loss is named once for the paragraph that lost it"
    ((lostOut.diags.filter (·.code == "W0386")).size == 1)
  let keptOut := layoutOf oneFace (declared "Short Title\\\\Second Line")
  t "a declared break that holds is silent"
    (!keptOut.diags.any (·.code == "W0386"))
  t "a title declaring no break never reports one"
    (!(layoutOf oneFace
      (declared "Coordinating Placeholder Schedules Across Several Regions")).diags.any
        (·.code == "W0386"))
  let prose := "Placeholder words run on past the measure here and wrap " ++
    "onto a further line as prose does"
  let bodyOut (body : String) : Layout.Out :=
    layoutOf oneFace (elabStr (narrow ++ "\\begin{document}\n" ++ body ++
      "\n\\end{document}")).1
  let heldOut := bodyOut s!"Short Label\\\\ {prose}."
  let heldC := censusOf #[] heldOut
  t "a held break before wrapping prose ships the declared line whole"
    ((heldC[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Label").map
      (fun l => !hasStr l.text "Placeholder") |>.getD false)
  t "a held break before wrapping prose sets the prose on more than one line"
    (((heldC[0]?.map fun p =>
      (p.lines.filter fun l => hasStr l.text "Placeholder" || hasStr l.text "prose").size).getD
        0) > 1)
  t "a held break before wrapping prose is silent"
    (!heldOut.diags.any (·.code == "W0386"))
  t "an item's held break before wrapping prose is silent"
    (!(bodyOut s!"\\begin\{itemize}\\item Short Label\\\\ {prose}.\\end\{itemize}").diags.any
      (·.code == "W0386"))
  t "a declared line that re-flows before a last line of prose is still named"
    (((bodyOut s!"Coordinating Placeholder Schedules Across Regions\\\\ {prose}.").diags.filter
      (·.code == "W0386")).size == 1)

/-- xcolor's top-level `\color{n}` is the document's ink and reaches every uncoloured shipped run. -/
def bodyColorChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let (d, _) := elabStr ("\\palette{ graphite = #2A2C30 }\n\\begin{document}\n" ++
    "\\color{graphite}\nBody words here.\n\\end{document}")
  let out := layoutOf oneFace d
  let graphite : Ir.Color := { r := 0x2A, g := 0x2C, b := 0x30 }
  t "the declared body colour reaches the shipped runs"
    ((out.pages.flatMap (·.lines)).any fun l => l.segs.any fun s => match s with
      | .run _ c _ _ glyphs _ _ _ _ _ _ => c == graphite && !glyphs.isEmpty
      | _ => false)
  t "no body run stayed silently pure black"
    ((bodyLines out).all fun l => l.segs.all fun s => match s with
      | .run _ c _ _ glyphs _ _ _ _ _ _ => glyphs.isEmpty || c != Ir.Color.black
      | _ => true)

/-- A footnote mark is a raised run in its line, and its note lands at the foot of the mark's page,
spilling with its line and named (W0372) when taller than the text block. -/
def footnoteLayoutChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let hasMarkRun (geom : Layout.Geom) (l : Layout.LineOut) : Bool :=
    l.segs.any fun s => match s with
      | .run _ _ _ _ _ sz _ _ raise _ _ => raise > 0 && sz > 0 && sz < geom.fontSize
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
    ((notesOf out).any fun l => l.segs.any fun s => s matches .rule _ _ _ _ _)
  t "footnote: notes are body ink, never furniture"
    ((notesOf out).all fun l => !l.furniture)
  let filler := String.intercalate " " (List.replicate 40 "wandering syllables")
  let src2 := dvDoc "" ("Opening claim\\footnote{the note under discussion} here.\n\n" ++
    String.intercalate "\n\n" (List.replicate 24 filler))
  let (doc2, _) := elabStr src2
  let out2 := layoutOf oneFace doc2
  t "footnote: the article spans pages" (out2.pages.size ≥ 2)
  t "footnote: the note ships on page 1, its mark's page"
    (((out2.pages[0]?.map fun p => p.lines.any (·.note)).getD false) &&
      (out2.pages.toList.drop 1).all fun p => p.lines.all (!·.note))
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
  let dsrc := deck169Frame "Frame words\\footnote{a frame-foot note} here."
  let (ddoc, _) := elabStr dsrc
  let dgeom := Layout.Geom.ofPage ddoc.page
  let dout := layoutOf oneFace ddoc
  t "footnote: a frame's note lands at the frame foot"
    (!(notesOf dout).isEmpty && dout.pages.all fun p =>
      p.lines.all fun n => !n.note ||
        (n.y ≤ Layout.frameFloor dgeom.pageH Ir.footline.sep p.footBox &&
          dgeom.bodyBottom < n.y && (flowOf dout).all fun b => b.y < n.y))
  let (bigDoc, _) := elabStr (dvDoc
    "\\page{ width = 120pt, height = 150pt, margin = 20pt }\n"
    ("x\\footnote{" ++ String.intercalate " " (List.replicate 60 "wow") ++ "}"))
  t "footnote: a note taller than the text block fires W0372"
    ((layoutOf oneFace bigDoc).diags.any (·.code == "W0372"))
  t "footnote: an ordinary note stays silent on W0372"
    (out.diags.all (·.code != "W0372") && (dvE src).all (·.code != "W0372"))
  let gapOf (pre : String) : Option Dim.Length := Id.run do
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

/-- A leaf of the projected tree with its ancestors' kinds, root first, and whether it stands in the
first paragraph of a list item. -/
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
    leafRowsList (k :: path) (k == .body || k == .tocItem) (inMarked || (first && k == .paragraph))
      acc kids.toList

end

def leafRows (t : Struct.Tree) : Array LeafRow :=
  leafRowsList [] false false #[] t.children.toList

/-- The ink the comparison reads: `Layout.inkCensus`'s exclusions plus the fixed spaces and the
hyphen dropped, case-folded. -/
def attrInk (s : String) : Array Char :=
  (s.toList.toArray.filter fun c =>
    !(c.isWhitespace || c == '\u00a0' || c == '\u00ad' || c == '-'
      || (Layout.fixedSpace c).isSome)).map Char.toLower

/-- The glyph text of one line for the attribution census, raised runs no leaf owns skipped. -/
def attrLineText (l : Layout.LineOut) : String :=
  l.segs.foldl (fun s seg => match seg with
    | .run _ _ _ _ glyphs _ _ _ raise _ attr =>
      if raise != 0 && !(attr matches .leaf _) then s
      else glyphs.foldl (fun s (_, c, _) => s.push c) s
    | .gap _ _ => s.push ' '
    | _ => s) ""

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
  | .quote | .aside | .nav | .toc | .tocItem | .link _ | .span _ | .line _ _ | .reference _ => false

def ownerOf (r : LeafRow) : Option Struct.Kind := (r.path.filter ownerKind).getLast?

/-- A leaf the PDF path deliberately ships no text for, by kind. -/
def unshippedKind (r : LeafRow) : Bool :=
  r.path.any (fun k => k matches .aside | .nav | .artifact | .formula)
    || (r.leaf matches .picture _ | .image _ _ | .linebreak)

def leafAttributionChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  for n in goldenNames do
    let (doc0, _) ← goldenDoc n
    let doc := Layout.pdfView doc0
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    -- Attribution reads the laid pages, before hidden overlay content drops its ink.
    let out := layoutOf fs doc (Layout.Geom.ofPage doc.page) (some pats) (ship := false)
    let tree := Struct.ofDoc doc
    let rows := leafRows tree
    let size := rows.size
    let generated : Array String := #[doc.info.locale.abstract] ++
      (match doc.headline with
        | some hl => #[Ir.plainText hl.title, Ir.plainText hl.author, Ir.plainText hl.institute]
        | none => #[])
    let iconAlts := Ir.foldBlocks (fun out _ => out) (fun out x => match x with
      | .icon _ label => out.push label
      | _ => out) (#[] : Array String) doc.body
    let numberedCode := Ir.foldBlocks (fun out b => match b with
      | .verbatim _ s spec => if spec.numbers then out.push s else out
      | _ => out) (fun out _ => out) (#[] : Array String) doc.body
    let standoutTitles := Ir.foldBlocks (fun out b => match b with
      | .frame title true _ _ _ => out.push (Ir.plainText title)
      | _ => out) (fun out _ => out) (#[] : Array String) doc.body
    let navLeaves := navSectionLeaves doc
    let excluded (r : LeafRow) : Bool :=
      unshippedKind r || navLeaves.contains r.id || (match r.leaf with
        | .text s => iconAlts.contains s || numberedCode.contains s || standoutTitles.contains s
        | _ => false)
    -- A glyph no face covers is dropped and named (E0405), so only covered characters are compared.
    let covered (c : Char) : Bool := fs.fonts.any fun f => (f.gid c).isSome
    let lines := allLines out
    let body := lines.filter fun l => !l.furniture && hasGlyphRun l
    let mut noneLines : Array String := #[]
    for l in body do
      match l.leaf with
      | some k => t s!"leaf {n}: index {k} is below {size}" (k < size)
      | none =>
        let txt := attrInk (lineText l)
        unless generated.any (fun g => attrInk g == txt) do
          noneLines := noneLines.push (lineText l)
    t s!"leaf {n}: every body line names a leaf ({noneLines.toList.take 3})" noneLines.isEmpty
    t s!"leaf {n}: furniture lines carry none" (lines.all fun l => !l.furniture || l.leaf.isNone)
    t s!"leaf {n}: note lines name a note leaf" (body.all fun l => !l.note ||
      (match l.leaf with
        | some k => (rows[k]?.map fun r => r.path.contains .note).getD false
        | none => false))
    let named := (body.filterMap (·.leaf)).qsort (· < ·) |>.foldl
      (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
    let underNote (k : Nat) : Bool := (rows[k]?.map fun r => r.path.contains .note).getD false
    let ownerGroup (r : LeafRow) : Option Nat :=
      (named.filter fun k => k ≤ r.id && underNote k == r.path.contains .note).back?
    let mut mismatch : Option String := none
    let mut exactFail : Option String := none
    let mut uncovered : Array String := #[]
    for k in named do
      -- A stepped frame sets its blocks once per step page; a flow paragraph may span pages.
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
      -- Exact only where the block carries no generated ink.
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
    for r in rows do
      unless excluded r || (attrInk r.leaf.census).isEmpty || (ownerGroup r).isSome do
        uncovered := uncovered.push s!"{r.id}:{r.leaf.census.quote}"
    t s!"leaf {n}: every inked leaf is attributed ({uncovered.toList.take 3})" uncovered.isEmpty
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

/-- A run's attribution, `none` for any other segment. -/
def segAttr : Layout.Seg → Option Layout.Attribution
  | .run _ _ _ _ _ _ _ _ _ _ a => some a
  | _ => none

def segGlyphText : Layout.Seg → String
  | .run _ _ _ _ glyphs _ _ _ _ _ _ => String.ofList (glyphs.toList.map (·.2.1))
  | _ => ""

def isGlyphRun : Layout.Seg → Bool
  | .run _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
  | _ => false

def isInkSeg : Layout.Seg → Bool
  | .run _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
  | .image _ _ _ _ _ _ => true
  | _ => false

def isWordGap : Layout.Seg → Bool
  | .gap _ word => word
  | _ => false

/-- The longest run of spaces in a text: how many word gaps in a row a line setting it may carry. -/
def longestSpaceRun (s : String) : Nat :=
  (s.toList.foldl (fun (best, cur) c => if c == ' ' then (max best (cur + 1), cur + 1)
    else (best, 0)) (0, 0)).1

/-- Ink for the exact census: whitespace, the no-break and fixed spaces and the soft hyphen dropped,
case folded; the hyphen stays. -/
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
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut labelFixtures : Array String := #[]
  for n in goldenNames do
    let (doc0, _) ← goldenDoc n
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
    let leafRunIds := body.flatMap fun l => l.segs.filterMap fun seg =>
      match segAttr seg with
      | some (.leaf k) => if isGlyphRun seg then some k else none
      | _ => none
    t s!"attr {n}: a leaf run names a text leaf"
      (leafRunIds.all fun k => (rows[k]?.map fun r => r.leaf matches .text _).getD false)
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
    let navLeaves := navSectionLeaves doc
    let excluded (r : LeafRow) : Bool :=
      unshippedKind r || navLeaves.contains r.id || r.path.contains .bibEntry || (match r.leaf with
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
        -- A stepped frame repeats its blocks per step page; a flow paragraph's parts join.
        let actual := leafInk (" ".intercalate painted.toList)
        let repeated := !painted.isEmpty && painted.all fun p => leafInk p == expected
        if !expected.isEmpty then exactLeaves := exactLeaves + 1
        if actual != expected && !repeated && exactFail.isNone then
          exactFail := some s!"leaf {r.id}: expected {(String.ofList expected.toList).quote} \
got {(String.ofList actual.toList).quote}"
      | _ => pure ()
    t s!"attr {n}: every counted leaf's runs are exactly its census \
({exactLeaves} leaves; {exactFail.getD ""})" exactFail.isNone
    let spaceRun : Nat := rows.foldl (fun m r => match r.leaf with
      | .text s => max m (longestSpaceRun s)
      | _ => m) 0
    let mut badGap : Option String := none
    for l in lines do
      let mut run := 0
      for i in [0:l.segs.size] do
        if isWordGap l.segs[i]! then
          run := run + 1
          let before := (l.segs.extract 0 i).any isInkSeg
          let after := (l.segs.extract (i + 1) l.segs.size).any isInkSeg
          unless before && after && run ≤ max 1 spaceRun do
            if badGap.isNone then badGap := some (lineText l)
        else run := 0
    t s!"attr {n}: a word gap stands inside its line's ink, no more of them in a row than \
the text sets ({badGap.getD ""})"
      badGap.isNone
    let marks := (body.flatMap fun l => l.segs.filterMap fun seg =>
      match segAttr seg with
      | some (.noteMark num) => some num
      | _ => none).qsort (· < ·) |>.foldl
        (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
    let notes := ((Ir.footnotesOf doc.body).map fun (num, _) => num.getD 0).qsort (· < ·)
      |>.foldl (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
    t s!"attr {n}: note marks are the footnotes {notes} (got {marks})" (marks == notes)
    let mut labelOff : Option String := none
    let mut labelLines := 0
    for l in body do
      let attrs := l.segs.filterMap fun seg => if isGlyphRun seg then segAttr seg else none
      let labels := attrs.filter (· matches .label)
      unless labels.isEmpty do
        labelLines := labelLines + 1
        let firstOther := attrs.findIdx? (fun a => !(a matches .label))
        let lastLabel := attrs.size - 1 - ((attrs.reverse.findIdx? (· matches .label)).getD 0)
        match firstOther with
        | some j => if j < lastLabel && labelOff.isNone then labelOff := some (lineText l)
        | none => pure ()
    let expectedMarkers := Ir.foldBlocks (fun acc b => match b with
      | .list _ _ items => acc + (items.filter fun item =>
          match (item.toList.dropWhile fun blk =>
              blk matches .setPalette _ | .setTokens _).head? with
          | some (.para _) => true
          | _ => false).size
      | .algorithm numbered _ ls =>
        if numbered then acc + (ls.filter fun l => !(l.kind matches .io _)).size else acc
      | .bibliography _ _ items => acc + (items.filter (·.marker.isSome)).size
      | .contents _ entries => acc + (entries.filter (·.number.isSome)).size
      | _ => acc) (fun acc _ => acc) 0 doc.body
    -- Compared only where every page is the one flow and every marker is the class's text.
    let declaredMarker := doc.styles.entries.any fun (_, st) => st.marker.isSome
    if (out.pages.size == 1 || !(doc.body.any fun b => b matches .frame ..)) && !declaredMarker then
      t s!"attr {n}: one marker line per item and numbered line ({labelLines} vs \
{expectedMarkers})" (labelLines == expectedMarkers)
    t s!"attr {n}: label runs lead their line ({labelOff.getD ""})" labelOff.isNone
    if labelLines > 0 then labelFixtures := labelFixtures.push n
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
            -- The block's next line in page order; an underline sibling between carries no run.
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
      let mut arith : Option String := none
      let groups := (body.filterMap (·.leaf)).qsort (· < ·) |>.foldl
        (fun (acc : Array Nat) k => if acc.back? == some k then acc else acc.push k) #[]
      for k in groups do
        let ls := body.filter (·.leaf == some k)
        let owned := rows.filter fun r => (match r.path.getLast? with
          | some .paragraph => true | _ => false) && k ≤ r.id &&
          (groups.filter fun g => g ≤ r.id).back? == some k
        if owned.isEmpty || ls.isEmpty then continue
        -- Each space of the paragraph's text atoms is one glue; a formula's source spaces are math.
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

/-- A declaration between blocks scopes every following block of its group and never sets an empty
styled paragraph in its place. -/
def declBlockChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := "\\footnotesize\n\\begin{tabular}{ll}\nalpha & beta \\\\\n" ++
    "gamma & delta\n\\end{tabular}\n\\normalsize\nBody text after the table."
  let (doc, diags) := Elab.run "t" src
  let c := censusOf #[] (layoutOf oneFace doc geom)
  let small := Ir.scaleStepIn Ir.sizeScale geom.fontSize "footnotesize"
  t "decl between blocks: the fixture elaborates clean" (diags.all (·.code.startsWith "N"))
  t "decl between blocks: the table's cells set at the footnotesize step"
    (lineSizeOf c 0 "alpha" == some small && lineSizeOf c 0 "gamma" == some small)
  t "decl between blocks: the paragraph after \\normalsize sets at the body size"
    (lineSizeOf c 0 "Body text" == some geom.fontSize)
  t "decl between blocks: no empty styled paragraph stands before the table"
    ((c[0]?.map fun p => p.lines.all fun l => !l.text.trimAscii.toString.isEmpty).getD false)
  let grouped := "{\\footnotesize\n\\begin{tabular}{ll}\nalpha & beta \\\\\n" ++
    "gamma & delta\n\\end{tabular}}\nBody text after the table."
  let cg := censusOf #[] (layoutOf oneFace (Elab.run "t" grouped).1 geom)
  t "decl between blocks: the grouped spelling sizes the cells the same way"
    (lineSizeOf cg 0 "alpha" == some small && lineSizeOf cg 0 "Body text" == some geom.fontSize)
  let colored := "\\palette{ accent = #336699 }\n\\accent\n\\begin{itemize}\\item one\\end{itemize}"
  let cout := layoutOf oneFace (Elab.run "t" colored).1 geom
  -- A body `\palette` ships as a `setPalette` block, so the value is spelled here.
  let accent : Ir.Color := { r := 51, g := 102, b := 153 }
  let itemRuns := (bodyLines cout).flatMap (·.segs.filterMap fun s =>
    match s with
    | .run _ color _ _ glyphs _ _ _ _ _ _ =>
      if glyphs.any (·.2.1 == 'o') then some color else none
    | _ => none)
  t "decl between blocks: a bare palette name colours the list after it"
    (!itemRuns.isEmpty && itemRuns.all (· == accent))
