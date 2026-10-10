module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.BlockSkips

/-!
# An explicit vertical skip adds to the boundary it stands at

TeX puts `\smallskip`, `\medskip`, `\bigskip` and `\vspace` on the vertical
list where they stand (latex.ltx `\@vspace`: `\vskip #1\vskip\z@skip`), so
the glue adds to the space the element above leaves below it and to the space
the element below spends above it, and an `\addvspace` after it adds rather
than taking the larger. Nothing absorbs it: not a beamer block's own
`\medskipamount` above its title box and `\smallskipamount` below its body
box (beamerinnerthemedefault.sty), not a list's `\topsep`, not a display's
skips, not a listing's. At a frame's top the skip stands between beamer's
`\vskip-\parskip\vbox{}` (beamerbaseframe.sty) and the first element, whose
own `\parskip` still cancels the frame's.

lualatex (TeX Live 2026) on the invented probes below — beamer with moloch at
10 pt, every frame `[t]` with room to spare so each glue keeps its natural
width — moves the element below a skip by these distances, in thousandths of
a TeX point, against the same frame without the skip, at `\parskip` 0 and
4 pt alike. The engine owes them exactly: a skip at its natural width, plus
whatever smaller own space of a neighbour the skip keeps from being merged
(two trivlist-like spaces meeting take the larger, as `\addvspace` does,
until a skip stands between them).

Not owed here, and measured on the same probes: a beamer list, centred block,
display or listing meeting another element without a skip spaces itself
differently from TeX in places (beamer's list colour stands between a block
and its list, so TeX adds the list's `\topsep` where the engine takes the
larger; a verbatim block is no trivlist here), so pairs whose skip-free
boundary already differs are left out of the table.

The HTML twin: a document skip is a box of its own, as tall as the skip's
natural width in the gap sheet's screen unit (`HtmlDoc.screenMilli`), with
no margin of its own and a block formatting context, so no margin collapses
through it; the element above owns its own space below before it (a rule
for every element that owns a boundary below), the element below its own
space above. The boundary is the three addends the page sums.
-/

private def preamble (pre : String) : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
  "\\usepackage{listings}\n" ++
  "\\definecolor{probeInk}{HTML}{202830}\n\\definecolor{probeTitle}{HTML}{D0D8E0}\n" ++
  "\\definecolor{probeSurface}{HTML}{ECF0F4}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{block title}{fg=probeInk,bg=probeTitle}\n" ++
  "\\setbeamercolor{block body}{fg=probeInk,bg=probeSurface}\n" ++ pre

private def titleColor : Ir.Color := { r := 0xD0, g := 0xD8, b := 0xE0 }
private def bodyColor : Ir.Color := { r := 0xEC, g := 0xF0, b := 0xF4 }

private def frame (body : String) : String :=
  "\\begin{frame}[fragile,t]{Probe}\n" ++ body ++ "\n\\end{frame}\n"

private def document (pre : String) (frames : List String) : String :=
  preamble pre ++ "\\begin{document}\n" ++ String.join frames ++ "\\end{document}\n"

/-- The element above a skip, marked by its first word. -/
private def above : String → String
  | "paragraph" => "Alpha lead words."
  | "block" => "\\begin{block}{Alpha title}Alpha body words.\\end{block}"
  | "list" => "\\begin{itemize}\n\\item Alpha item words.\n\\end{itemize}"
  | "centred" => "\\begin{center}\nAlpha centred words.\n\\end{center}"
  | "display" => "Alpha lead words.\n\\[ x = y \\]"
  | "verbatim" => "\\begin{verbatim}\nalpha code\n\\end{verbatim}"
  | _ => "\\begin{lstlisting}\nalpha code\n\\end{lstlisting}"

/-- The element below a skip, marked by its first word. -/
private def below : String → String
  | "paragraph" => "Omega tail words."
  | "block" => "\\begin{block}{Omega title}Omega body words.\\end{block}"
  | "list" => "\\begin{itemize}\n\\item Omega item words.\n\\end{itemize}"
  | "centred" => "\\begin{center}\nOmega centred words.\n\\end{center}"
  | "display" => "\\[ \\text{Omega} = z \\]"
  | "verbatim" => "\\begin{verbatim}\nomega code\n\\end{verbatim}"
  | _ => "\\begin{lstlisting}\nomega code\n\\end{lstlisting}"

/-- `\bigskip` between two elements: lualatex's move of the lower one. Every
pair whose skip-free boundary the engine sets as TeX does; the 15 and 18 pt
rows are the unmerged neighbour spaces (a block's `\smallskipamount`, a
display's skip below, against a centred block's `\topsep`). -/
private def bigskipMoves : List (String × String × Int) :=
  (["paragraph", "block", "list", "centred", "display", "verbatim", "listing"].map
    fun y => ("paragraph", y, 12000)) ++
  [("block", "paragraph", 12000), ("block", "block", 11999), ("block", "centred", 15000),
   ("block", "display", 12000), ("block", "listing", 11999),
   ("list", "paragraph", 11999), ("list", "block", 12000), ("list", "centred", 15000),
   ("list", "listing", 12000),
   ("centred", "paragraph", 12001), ("centred", "block", 11999), ("centred", "display", 12000),
   ("centred", "listing", 12000),
   ("display", "paragraph", 12000), ("display", "block", 11999), ("display", "centred", 18000),
   ("display", "listing", 12001),
   ("verbatim", "paragraph", 12001), ("verbatim", "block", 12000), ("verbatim", "list", 12000),
   ("verbatim", "display", 12000), ("verbatim", "listing", 12000)] ++
  (["paragraph", "block", "list", "centred", "display", "verbatim", "listing"].map
    fun y => ("listing", y, 12000))

/-- Each skip spelling between blocks and paragraphs: lualatex's move in
TeX points. A length in points is the engine's point numerically; the
centimetre (28.453 TeX points) is compared as a length. -/
private def skipMoves : List (String × String × Int × Bool) :=
  [("\\smallskip", "small", 3000, false), ("\\medskip", "medium", 6000, false),
   ("\\bigskip", "big", 12000, false), ("\\vspace{1cm}", "centimetre", 28453, true),
   ("\\vspace{-4pt}", "negative", -4000, false), ("\\bigskip\n\\medskip", "two", 18000, false)]

/-- lualatex's distance from a painted block's body box to the next block's
title box, the skip between them: medskip, smallskip and `\lineskip` with
nothing between, then each skip on top. -/
private def blockGaps : List (String × Int) :=
  [("", 10000), ("\\smallskip", 13001), ("\\medskip", 16001), ("\\bigskip", 22000),
   ("\\vspace{1cm}", 38454)]

/-- 2 thousandths of a point: lualatex's three-decimal big points and their
conversion to TeX points. -/
private def tolerance : Int := 2

/-- TeX points in thousandths, in the engine's point (PostScript's): a
centimetre is 28.453 TeX points and 28.346 of the engine's. -/
private def bpMilli (texMilli : Int) : Int := (texMilli * 7200 + 3613) / 7227

private def pagesOf (fonts : Font.FontSet) (src : String) : Array Layout.PageOut × Ir.Doc :=
  let (doc, _) := Elab.run "block-skips.tex" src
  ((Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).pages, doc)

/-- The baseline of a page's first body line whose text opens with `word`,
any case, past a list's marker. -/
private def lineY (page : Layout.PageOut) (word : String) : Option Dim.Sp :=
  (page.lines.find? fun l =>
    !l.furniture &&
      (String.ofList ((lineText l).toLower.toList.dropWhile (!·.isAlpha))).startsWith
        word.toLower).map (·.y)

private def span (page : Layout.PageOut) : Option Dim.Sp := do
  pure ((← lineY page "omega") - (← lineY page "alpha"))

/-- The empty skips of a document, in document order: the IR values both
backends read. -/
private def skipsOf (doc : Ir.Doc) : Array (Ir.Sourced Dim.SymGlue) :=
  Ir.foldBlocks (fun acc b => match b with
    | .spaced g body => if body.isEmpty then acc.push g else acc
    | _ => acc) (fun acc _ => acc) #[] doc.body

private def pdfChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for (pre, label) in [("", "parskip 0"), ("\\setlength{\\parskip}{4pt}\n", "parskip 4pt")] do
    -- `\bigskip` between every pair TeX sets additively.
    let frames := bigskipMoves.flatMap fun (x, y, _) =>
      [frame (above x ++ "\n\n" ++ below y), frame (above x ++ "\n\n\\bigskip\n\n" ++ below y)]
    let (pages, _) := pagesOf fonts (document pre frames)
    check ref s!"block skips ({label}): one page per probe frame"
      (pages.size == 2 * bigskipMoves.length)
    for ((x, y, lua), i) in bigskipMoves.zipIdx do
      match (pages[2 * i]?.bind span), (pages[2 * i + 1]?.bind span) with
      | some d0, some d1 =>
        let want := (lua + 500) / 1000
        check ref s!"block skips ({label}): \\bigskip between {x} and {y} moves it {lua} (lualatex), got {spMilli (d1 - d0)}"
          (d1 - d0 == Dim.pt want && (lua - 1000 * want).natAbs ≤ tolerance.toNat)
      | _, _ => check ref s!"block skips ({label}): the {x}/{y} probe's marks ship" false
    -- Every skip spelling, between blocks and paragraphs.
    let pairs := [("block", "block"), ("paragraph", "paragraph"), ("block", "paragraph"),
      ("paragraph", "block")]
    for (skip, name, lua, physical) in skipMoves do
      let frames := pairs.flatMap fun (x, y) =>
        [frame (above x ++ "\n\n" ++ below y), frame (above x ++ "\n\n" ++ skip ++ "\n\n" ++ below y)]
      let (pages, doc) := pagesOf fonts (document pre frames)
      let size := doc.page.fontSize
      -- The engine pays the IR's value whole: the glue the skip elaborated to,
      -- at its natural width, which is TeX's within the measurement.
      let width := (skipsOf doc).foldl (fun s g => s + (g.value.resolve size (size / 2)).width) (0 : Dim.Sp)
      let width := width / pairs.length
      check ref s!"block skips ({label}): {name} resolves to lualatex's {lua} TeX points"
        ((spMilli width - (if physical then bpMilli lua else lua)).natAbs ≤ tolerance.toNat)
      for ((x, y), i) in pairs.zipIdx do
        match (pages[2 * i]?.bind span), (pages[2 * i + 1]?.bind span) with
        | some d0, some d1 =>
          check ref s!"block skips ({label}): {name} between {x} and {y} moves it by its width, got {spMilli (d1 - d0)}"
            (d1 - d0 == width)
        | _, _ => check ref s!"block skips ({label}): the {name} {x}/{y} probe's marks ship" false
    -- At a frame's top the skip stands under the opening; the first
    -- paragraph's or list's `\parskip` still cancels the frame's.
    let tops := ["paragraph", "block", "list"]
    let frames := tops.flatMap fun y => [frame (below y), frame ("\\bigskip\n\n" ++ below y)]
    let (pages, _) := pagesOf fonts (document pre frames)
    for (y, i) in tops.zipIdx do
      match (pages[2 * i]?.bind (lineY · "omega")), (pages[2 * i + 1]?.bind (lineY · "omega")) with
      | some y0, some y1 =>
        check ref s!"block skips ({label}): \\bigskip at a frame's top moves its first {y} 12000 (lualatex), got {spMilli (y1 - y0)}"
          (y1 - y0 == Dim.pt 12)
      | _, _ => check ref s!"block skips ({label}): the frame-top {y} probe's marks ship" false
    -- Inside a block's body, before its end, and before `\pause`.
    let inner := [
      ("at a block body's top", "\\begin{block}{Alpha title}\n", "Omega body words.\\end{block}", false),
      ("before a block's end", "\\begin{block}{Alpha title}Alpha body words.\n", "\\end{block}\n" ++ below "block", false),
      ("before \\pause", above "block" ++ "\n", "\\pause\n" ++ below "block", true)]
    for (name, head, tail, stepped) in inner do
      let (pages, _) := pagesOf fonts (document pre [frame (head ++ "\n" ++ tail),
        frame (head ++ "\n\\bigskip\n\n" ++ tail)])
      let step := if stepped then 1 else 0
      match (pages[step]?.bind span), (pages[2 * step + 1]?.bind span) with
      | some d0, some d1 =>
        check ref s!"block skips ({label}): \\bigskip {name} moves what follows 12000 (lualatex), got {spMilli (d1 - d0)}"
          (d1 - d0 == Dim.pt 12)
      | _, _ => check ref s!"block skips ({label}): the probe {name} ships its marks" false
  -- The distance between two painted blocks, body box to title box.
  let frames := blockGaps.map fun (skip, _) =>
    frame (above "block" ++ "\n" ++ skip ++ "\n" ++ below "block")
  let (pages, _) := pagesOf fonts (document "" frames)
  for ((skip, lua), i) in blockGaps.zipIdx do
    let fills := ((pages[i]?.map (·.fills)).getD #[]).qsort (·.y < ·.y)
    let bodyBottom := (fills.find? (·.color == bodyColor)).map fun f => f.y + f.h
    let nextTop := ((fills.filter (·.color == titleColor))[1]?).map (·.y)
    match bodyBottom, nextTop with
    | some b, some t =>
      let want := if skip.startsWith "\\vspace" then 10000 + bpMilli (lua - 10000) else lua
      check ref s!"block skips: '{skip}' sets two blocks {lua} apart (lualatex), got {spMilli (t - b)}"
        ((spMilli (t - b) - want).natAbs ≤ tolerance.toNat)
    | _, _ => check ref s!"block skips: the '{skip}' blocks ship their boxes" false

/-- TeX's primitive `\vskip` reads its glue unbraced, its keywords run into
their dimensions or not (`plus2pt`). lualatex moves what follows it by its
glue — 7 pt between paragraphs, and mid-paragraph too, where the vertical
command ends the paragraph (a `\vspace` there is a `\vadjust` and keeps it),
-3 pt for a negative skip, and `3pt plus2pt` or `3pt minus1pt` by 3 pt — and
`\vskip 0pt plus 1fill` is `\vfill`, spelled `\vskip0pt plus1fill` too. One
difference stays owed: an `\addvspace` after `\vskip` takes the larger, so
lualatex moves a centred block after `\vskip 12pt` by 4 pt (its `\topsep`
is 8 pt) where the engine adds the skip whole. -/
private def vskipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let para := above "paragraph"
  let cases := [("between paragraphs", "\n\n\\vskip 7pt\n\n", 7),
    ("mid-paragraph", "\n\\vskip 7pt\n", 7), ("negative", "\n\n\\vskip -3pt\n\n", -3),
    ("with a run-in stretch", "\n\n\\vskip 3pt plus2pt\n\n", 3),
    ("with a run-in shrink", "\n\n\\vskip 3pt minus1pt\n\n", 3),
    ("with both run in", "\n\n\\vskip3pt plus2pt minus1pt\n\n", 3)]
  for (name, skip, pts) in cases do
    let src := document "" [frame (para ++ "\n\n" ++ below "paragraph"),
      frame (para ++ skip ++ below "paragraph")]
    let (doc, diags) := Elab.run "block-skips-vskip.tex" src
    let pages := (Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).pages
    match (pages[0]?.bind span), (pages[1]?.bind span) with
    | some d0, some d1 =>
      check ref s!"block skips: \\vskip {name} moves what follows {pts} pt (lualatex), got {spMilli (d1 - d0)}"
        (d1 - d0 == Dim.pt pts)
    | _, _ => check ref s!"block skips: the \\vskip {name} probe ships its marks" false
    check ref s!"block skips: \\vskip {name} is a skip, never text"
      (diags.all (·.code != "W0301") &&
        pages.all fun p => p.lines.all fun l =>
          !hasStr (lineText l) "pt" && !hasStr (lineText l) "plus" && !hasStr (lineText l) "minus")
  let fillOf (skip : String) : Option Dim.Sp :=
    let (doc, _) := Elab.run "block-skips-fill.tex"
      (document "" [frame (para ++ "\n\n" ++ skip ++ "\n\n" ++ below "paragraph")])
    ((Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).pages[0]?).bind (lineY · "omega")
  check ref "block skips: \\vskip 0pt plus 1fill stands where \\vfill stands"
    ((fillOf "\\vskip 0pt plus 1fill").isSome && fillOf "\\vskip 0pt plus 1fill" == fillOf "\\vfill")
  check ref "block skips: \\vskip0pt plus1fill stands where \\vfill stands"
    ((fillOf "\\vskip0pt plus1fill").isSome && fillOf "\\vskip0pt plus1fill" == fillOf "\\vfill")
  let centred := document "" [frame (para ++ "\n\n" ++ below "centred"),
    frame (para ++ "\n\n\\vskip 12pt\n\n" ++ below "centred")]
  let (pages, _) := pagesOf fonts centred
  check ref "owed: \\vskip before a centred block adds 12 pt where TeX takes the larger, 4 pt"
    (((pages[0]?.bind span).bind fun d0 => (pages[1]?.bind span).map (· - d0)) == some (Dim.pt 12))

/-- A declaration's value in an inline style. -/
private def styleDecl (style name : String) : Option String :=
  (style.splitOn ";").findSome? fun decl => do
    let [n, value] := decl.splitOn ":" | none
    if n.trimAscii.toString == name then some value.trimAscii.toString else none

/-- A skip box's natural width in milli-rem, read off its style: the
`--skip` the sheet turns into its height or, negative, its bottom margin;
nothing declared is zero. -/
private def boxMilli (style : String) : Option Int :=
  match styleDecl style "--skip" with
  | some value => remMilliOf value
  | none => if style.trimAscii.isEmpty then some 0 else none

/-- The box's extent where no sheet reaches it: a positive skip's height, a
negative one's bottom margin, the same length as its `--skip`, and no other
margin. -/
private def boxExtentInline (style : String) : Bool :=
  match styleDecl style "--skip" with
  | none => style.trimAscii.isEmpty
  | some len =>
    if len.startsWith "-" then
      styleDecl style "margin-bottom" == some len && (styleDecl style "height").isNone
    else styleDecl style "height" == some len && !hasStr style "margin"

private def hasClassTok (attrs : Array (String × String)) (c : String) : Bool :=
  ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " " |>.contains c

private def htmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let skips := ["\\smallskip", "\\medskip", "\\bigskip", "\\vspace{1cm}", "\\vspace{-4pt}"]
  let src := document "\\setlength{\\parskip}{4pt}\n"
    ((skips.map fun s => frame (above "block" ++ "\n" ++ s ++ "\n" ++ below "block")) ++
      [frame ("\\bigskip\n\n" ++ below "paragraph")])
  let (doc, _) := Elab.run "block-skips.tex" src
  let size := doc.page.fontSize
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let boxes := (elemNodesList (· == "div") #[] body.toList).filterMap fun
    | .elem _ attrs _ => if hasClassTok attrs "vskip" then some attrs else none
    | _ => none
  let values := skipsOf doc
  check ref "block skips HTML: every document skip ships as a box of its own"
    (boxes.size == values.size && values.size == skips.length + 1)
  for (attrs, g) in boxes.zip values do
    let v := (g.value.resolve size (size / 2)).width
    let style := (HtmlDoc.attrOf? attrs "style").getD ""
    let want : Int := if v < 0 then -(HtmlDoc.screenMilli size (-v) : Int)
      else (HtmlDoc.screenMilli size v : Int)
    check ref s!"block skips HTML: a {spMilli v} thousandths skip is a box of {want} milli-rem, its extent on the box ('{style}')"
      (boxMilli style == some want && boxExtentInline style && !hasStr style "margin-top")
  -- A page that ships none of the engine's sheet still moves the follower
  -- by the skip: the box carries its extent itself, as it does with the sheet.
  for (cfg, mode) in [(({ css := .none } : HtmlDoc.Config), "css = none"), ({ css := .bulma }, "bulma")] do
    let (_, bare, _) := HtmlDoc.emitTree cfg doc
    let styles := (elemNodesList (· == "div") #[] bare.toList).filterMap fun
      | .elem _ attrs _ =>
        if hasClassTok attrs "vskip" then some ((HtmlDoc.attrOf? attrs "style").getD "") else none
      | _ => none
    check ref s!"block skips HTML ({mode}): every skip box carries its extent inline"
      (styles == boxes.map (fun attrs => (HtmlDoc.attrOf? attrs "style").getD "") &&
        styles.all boxExtentInline && styles.any (hasStr · "height: ") &&
        styles.any (hasStr · "margin-bottom: -"))
  -- The frame-top box takes the frame's opening and pays beamer's
  -- `\vskip-\parskip`, which the paragraph after it cancels by its own.
  check ref "block skips HTML: a skip opening a frame owns its opening"
    ((boxes.back?.map (hasClassTok · "frame-body-start")).getD false)
  let (head, _, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" (head.toList ++ body.toList)
  check ref "block skips HTML: a skip box is as tall as its skip and pays the frame's \\vskip-\\parskip"
    ((cssRuleOf css ".vskip").any fun d =>
      hasStr d "display: flow-root" && hasStr d "height: max(0rem, var(--skip, 0rem))" &&
        hasStr d "--frame-body-before: calc(0rem - var(--parskip, 0rem))")
  check ref "block skips HTML: a negative skip is the box's bottom margin, its only own margin"
    (HtmlDoc.blockGapRules doc.docClass.record.lists size doc.tokens |>.contains
      (.reset ".vskip" "0 0 min(0rem, var(--skip, 0rem))"))
  -- Every element that owns a space below it in the sheet owns it before a
  -- skip too, without the peer gap of the paragraph the generic boundary
  -- assumes after it: the follower past the skip pays its own. A boundary
  -- that sets its follower flush (a heading's, a caption's) sets a skip
  -- flush through the same rule.
  for (lineage, lname) in [(Ir.ListLineage.sizeFile, "size file"), (.beamer, "beamer"), (.web, "web")] do
    for sz in [Dim.pt 10, Dim.pt 12] do
      let rules := HtmlDoc.blockGapRules lineage sz {}
      let bounds := rules.filterMap fun
        | .boundary sel v => some (sel, v)
        | _ => none
      for ((sel, v), i) in bounds.zipIdx do
        let parts := cssSelParts sel
        if parts.all (·.endsWith " + *") && v != "0" then
          let want := ", ".intercalate (parts.map fun p =>
            (p.dropEnd 1).toString ++ s!":is(.vskip, {HtmlDoc.skipCarrier})")
          let companion := (bounds.drop (i + 1)).find? (·.1 == want)
          check ref s!"block skips HTML ({lname}, {spMilli sz}): '{sel}' owns its space before a skip, without the follower's gap"
            ((companion.map fun (_, own) =>
              !hasStr own "+ var(--parskip" && (own == v || hasStr v own || hasStr own v)).getD false)
  -- The boundary the three addends make, block to block across
  -- `\bigskip`, in screen milli-rem: the block's `\smallskipamount`, the
  -- skip, the next block's `\medskipamount` and `\lineskip` — the page's
  -- 22 pt, each addend converted once.
  let rules := HtmlDoc.blockGapRules doc.docClass.record.lists size doc.tokens
  let valueOf (p : String → Bool) : Option Int := rules.findSome? fun
    | .boundary sel v => if p sel then remMilliOf v else none
    | _ => none
  let below := valueOf fun s => s.startsWith "section.block" && s.endsWith s!"+ :is(.vskip, {HtmlDoc.skipCarrier})"
  let aboveNext := valueOf fun s => s == "* + section.block"
  let skip := (boxes[2]?.bind fun attrs => boxMilli ((HtmlDoc.attrOf? attrs "style").getD ""))
  match below, aboveNext, skip with
  | some b, some a, some s =>
    let page := Dim.pt 3 + Dim.pt 12 + Dim.pt 6 + Layout.inkClearance
    let want := (HtmlDoc.screenMilli size page : Int)
    check ref s!"block skips HTML: two blocks across \\bigskip stand the page's 22 pt, {b} + {s} + {a} milli-rem against {want}"
      ((b + s + a - want).natAbs ≤ 3)
  | _, _, _ => check ref "block skips HTML: the block boundary's three addends are in the sheet" false

/-- A skip met inside inline content — a table cell, a bold run, a
footnote, a frame or block title — has no vertical glue to stand in: it is
skipped with one W0329, the document builds, and none of its native
spelling reaches the page as text. lualatex accepts every one. -/
private def inlineChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let sites := [("a table cell", "\\begin{tabular}{p{3cm}}cell words \\vskip 3pt more\\end{tabular}"),
    ("a bold run", "\\textbf{bold \\vskip 3pt words}"),
    ("a footnote", "Words\\footnote{note \\vspace{3pt} words}."),
    ("a block title", "\\begin{block}{Title \\vskip 3pt words}Body words.\\end{block}")]
  for (name, body) in sites do
    let src := document "" [frame body]
    let (doc, diags) := Elab.run "block-skips-inline.tex" src
    let pages := (Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).pages
    check ref s!"block skips: a skip inside {name} builds, got {(diags.filter (·.severity == .error)).map (·.code)}"
      (diags.all (·.severity != .error))
    check ref s!"block skips: a skip inside {name} is named once, W0329"
      ((diags.filter (·.code == "W0329")).size == 1)
    check ref s!"block skips: a skip inside {name} sets none of its spelling as text"
      (pages.all fun p => p.lines.all fun l => !hasStr (lineText l) "before")
  let titled := document "" ["\\begin{frame}[t]{Frame \\vskip 3pt title}Words.\\end{frame}\n"]
  let (_, diags) := Elab.run "block-skips-inline-title.tex" titled
  check ref "block skips: a skip inside a frame title builds" (diags.all (·.severity != .error))

/-- An infinite stretch other than `\\vfill`'s ranks against the page's other
infinite glues, which the engine does not tell apart: lualatex leaves what
follows `\\vskip 0pt plus 1fil` in place on a `[t]` frame, whose own bottom
glue outranks it. The engine sets the skip at its natural width and names
it once (W0104); `\\vskip 0pt plus 1fill` stays `\\vfill`. -/
private def filOrderChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let para := above "paragraph"
  let pageOf (skip : String) : Option Dim.Sp × Array Diag :=
    let (doc, diags) := Elab.run "block-skips-fil.tex"
      (document "" [frame (para ++ "\n\n" ++ skip ++ "\n\n" ++ below "paragraph")])
    (((Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).pages[0]?).bind (lineY · "omega"), diags)
  let (natural, _) := pageOf "\\vskip 0pt"
  for skip in ["\\vskip 0pt plus 1fil", "\\vskip 0pt plus 2fill", "\\vskip 0pt plus 1filll"] do
    let (y, diags) := pageOf skip
    check ref s!"block skips: '{skip}' sets at its natural width" (y.isSome && y == natural)
    check ref s!"block skips: '{skip}' is named once, W0104"
      ((diags.filter (·.code == "W0104")).size == 1)
  let (fill, diags) := pageOf "\\vskip 0pt plus 1fill"
  check ref "block skips: \\vskip 0pt plus 1fill is \\vfill, unnamed"
    (fill.isSome && fill != natural && diags.all (·.code != "W0104"))

/-- The sheet's rules for a skip box where its follower's term is not the
one the generic boundary assumes: a skip opening an untitled frame pays the
frame's `\\vskip-\\parskip`, a step carrier opening on a skip box owns the
box's boundaries and opening, the paragraph past a box after a list pays
TeX's `\\parskip` (the list's own term) rather than the sheet's peer gap, and
a rule's `<hr>` carries no margin of its own, as TeX's `\\hrule` has none. -/
private def sheetChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (lineage, lname) in [(Ir.ListLineage.sizeFile, "size file"), (.beamer, "beamer")] do
    let rules := HtmlDoc.blockGapRules lineage (Dim.pt 10) {}
    let has (p : String → String → Bool) : Bool := rules.any fun
      | .boundary sel v => p sel v
      | _ => false
    check ref s!"block skips HTML ({lname}): a skip opening an untitled frame pays the frame's \\vskip-\\parskip"
      (has fun sel v => hasStr sel "section.slide > :is(.vskip" && hasStr sel ":first-child" &&
        v == "calc(0rem - var(--parskip, 0rem))")
    check ref s!"block skips HTML ({lname}): a list owns its space before a carrier opening on a skip"
      (has fun sel v => hasStr sel "ul:not(.bibliography) + :is(.vskip, " && hasStr sel HtmlDoc.skipCarrier &&
        !hasStr v "var(--parskip")
    check ref s!"block skips HTML ({lname}): the paragraph past a skip after a list pays TeX's \\parskip"
      (has fun sel v => hasStr sel "ul:not(.bibliography) + .vskip + p" && v == "var(--parskip, 0rem)")
    -- The follower past a skip box after a heading, or opening a container
    -- other than a frame or a step carrier, pays what its place pays
    -- without the box — nothing — in the second-last rule, after every rule
    -- a follower takes its gap from: the rules stand at zero specificity,
    -- so the later one wins.
    let follower := (rules.reverse[1]?).bind fun
      | .boundary sel v => if v == "0" then some (cssSelParts sel) else none
      | _ => none
    let carrier := HtmlDoc.skipCarrier
    for (place, edge) in [(":is(h1, h2, h3, h4, h5, h6) + ", ""),
        (":not(section.slide, .step, .step-set) > ", ":first-child")] do
      for want in [s!"{place}.vskip{edge} + *", s!"{place}.vskip{edge} + .vskip + *",
          s!"{place}{carrier}{edge} > .vskip:first-child + *"] do
        check ref s!"block skips HTML ({lname}): the follower past '{want}' pays nothing, second-last"
          ((follower.map (·.contains want)).getD false)
    check ref s!"block skips HTML ({lname}): a title under a title bar stands on the bar's skip alone"
      (has fun sel v => sel == "hr.separator + .vskip + h1:not(.body-heading)" && v == "0")
    check ref s!"block skips HTML ({lname}): a title over a title bar's skip has no band below"
      (rules.any fun
        | .reset sel m => sel == "h1:not(.body-heading):has(+ .vskip + hr.separator)" && m == "0"
        | _ => false)
    check ref s!"block skips HTML ({lname}): a rule's <hr> carries no margin"
      (rules.any fun
        | .reset sel m => (cssSelParts sel).contains "hr" && m == "0"
        | _ => false)
    check ref s!"block skips HTML ({lname}): the paragraph past two skips after a list pays TeX's \\parskip"
      (has fun sel v => (cssSelParts sel).contains "ul:not(.bibliography) + .vskip + .vskip + p" &&
        v == "var(--parskip, 0rem)")

def blockSkipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  pdfChecks ref fonts
  vskipChecks ref fonts
  inlineChecks ref fonts
  filOrderChecks ref fonts
  sheetChecks ref
  htmlChecks ref

end Tests.BlockSkips
