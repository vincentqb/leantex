module

public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FrameGeometry

/-- The slide stages of a document's web deck. -/
private def stagesOf (doc : Ir.Doc) : Array Html.Node :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  slideStages body

/-- **A moloch frame title starts the bar's inset from the paper's edge**
(`Ir.frameTitleInset`): moloch's bar is a colour box as wide as the paper
whose title is inset 0.85 of the title's strut from either edge
(beamerouterthememoloch.sty:134-135), never at the text margin. Against
lualatex on the moloch spelling (10 pt, 4:3, the shipped Fira Sans for
every face): the title's first glyph at 8.30 bp under moloch's `\large`
title and at 10.67 bp under a theme's `\Large`, held to half a point — what
remains is the strut's leading, the rhythm's 1.2 against size10.clo's 14 pt
and 18 pt. The web deck pads its bar by the same inset, in em of the title.
At `f319b96c` both titles stood at the text margin, 28.35 bp, and the bar
padded by the stage's safe area. Invented words. -/
def titleInsetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "title inset: the shipped Fira Sans parses" false
  for (font, step, lua) in [("", "large", 8299),
      ("\\setbeamerfont{frametitle}{size=\\Large}\n", "Large", 10670)] do
    let (doc, ds) := elabStr (s!"\\documentclass[10pt]\{beamer}\n\\usetheme\{moloch}\n{font}" ++
      "\\begin{document}\n\\begin{frame}{Alpha words}\nKilo words.\n\\end{frame}\n\\end{document}\n")
    let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
    let title := ((out.pages[0]?.map (·.lines)).getD #[]).find? fun l => hasStr (lineText l) "Alpha"
    let inset := Ir.frameTitleInset (Ir.scaleStep doc.page.fontSize step)
    t s!"title inset {step}: the deck elaborates clean" (ds.all (·.severity != .error))
    t s!"title inset {step}: the title starts the bar's inset from the paper's left edge"
      (title.map (·.x) == some inset)
    t s!"title inset {step}: the title starts within half a point of lualatex's"
      (title.any fun l => withinSp (ptMilli 500) l.x (ptMilli lua))
    let (head, _, _) := HtmlDoc.emitTree {} doc
    let css := treeCssList "" head.toList
    t s!"title inset {step}: the web bar pads its title by the inset, in em of the title"
      ((cssBlocksFor css "section.slide > header").any fun decls =>
        match cssDeclOf decls "padding" with
        | some v => match v.splitOn " " with
          | [top, side] => top == "0" && cssEmMilli side == some (Ir.frameTitleInset 1000)
          | _ => false
        | none => false)

/-- **A standout frame bears no number and advances no count**
(`Ir.Block.countable`): moloch's `standout` key sets `noframenumbering`
unless `standoutnumbering` asks otherwise (beamerinnerthememoloch.sty:
462-467), so the frames after it, the footline's numbers and the section
page's progress bar read the frames lualatex counts. Over `Layout.Out` and
the typed HTML tree: frames numbered 1, 2, 3 around an unnumbered standout,
and a section page after the first frame filling a third of its bar, the
PDF's measure (`Ir.sectionPageMeasure`). lualatex on the same spelling
fills 2 of 7 of a bar on a deck whose standout stands second, where the
engine filled 3 of 8. At `f319b96c` the standout bore 2 and the bar filled
half. Invented words. -/
def standoutNumberChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "standout numbering: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr ("\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n" ++
    "\\begin{document}\n\\begin{frame}{Alpha}\nKilo words.\n\\end{frame}\n" ++
    "\\begin{frame}[standout]\nLima words.\n\\end{frame}\n\\section{Hotel words}\n" ++
    "\\begin{frame}{Bravo}\nMike words.\n\\end{frame}\n" ++
    "\\begin{frame}{Charlie}\nOscar words.\n\\end{frame}\n\\end{document}\n")
  t "standout numbering: the deck elaborates clean" (ds.all (·.severity != .error))
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fira doc geom
  t "standout numbering: the pages number the frames around the standout 1, 2 and 3"
    (pdfFoots out == #[("", "1"), ("", "2"), ("", "3")] &&
      out.pages.map (·.frame) == #[some 1, none, none, some 2, some 3])
  let (_, body, _) := HtmlDoc.emitTree {} doc
  t "standout numbering: the web deck numbers the same frames"
    (slideFootsList #[] body.toList == #[("", "1"), ("", "2"), ("", "3")])
  let design := Ir.Design.ofDoc doc
  let measure := Ir.sectionPageMeasure geom.textWidth
  t "standout numbering: the section page's bar fills the frames done of the frames counted"
    (match design.sectionProgress, out.pages[2]? with
     | some bar, some p => p.fills.any fun f => f.color == bar.fg && f.w == measure * 1 / 3
     | _, _ => false)
  t "standout numbering: the web section page's bar fills the same third"
    ((elemAttrsList (fun _ => true) #[] body.toList).any fun (_, attrs) =>
      (HtmlDoc.attrOf? attrs "style") == some "width: 33%")

/-- **A moloch section page sets its title and bar in moloch's measure on
both artifacts** (`Ir.sectionPageMeasure`): the `progressbar` section
page's `0.7875\linewidth` minipage (beamerinnerthememoloch.sty:345),
centred. Over `Layout.Out`, the bar's track is the measure wide and starts
half the rest of the line in from the text margin; over the stylesheet, the
web section page's title and bar are the same share of the stage, to its
one printed milli-percent. At `f319b96c` the web deck set both in 60% of
the stage's width, its title 20 bp right of the page's on a 16:9 deck.
Invented words. -/
def sectionMeasureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "section measure: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr ("\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\begin{document}\n\\begin{frame}{Alpha}\nKilo words.\n\\end{frame}\n" ++
    "\\section{Hotel words}\n\\begin{frame}{Bravo}\nMike words.\n\\end{frame}\n\\end{document}\n")
  t "section measure: the deck elaborates clean" (ds.all (·.severity != .error))
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fira doc geom
  let measure := Ir.sectionPageMeasure geom.textWidth
  t "section measure: the page's bar track is moloch's measure, centred in the line"
    (match (Ir.Design.ofDoc doc).sectionProgress, out.pages[1]? with
     | some bar, some p => p.fills.any fun f =>
        f.color == bar.bg && f.w == measure &&
          f.x == geom.hmargin + (geom.textWidth - measure) / 2
     | _, _ => false)
  let (head, _, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  -- `min(<share>vh, 100%)`: the stage's share, never past its width.
  let shares (sel : String) : Bool :=
    (cssBlocksFor css sel).any fun decls => match cssDeclOf decls "width" with
      | some v => match (v.dropPrefix "min(").toString.splitOn ", " with
        | [share, "100%)"] => cssStageLength s!"width: {share}" "width" measure doc.page.height
        | _ => false
      | none => false
  t "section measure: the web section page's title and bar take the same share of the stage"
    (shares "section.section-page h2" && shares ".progress")

/-- **A bar-less frame title stands in beamer's default title box**
(`Ir.defaultFrameTitleBelow`): beamer's default `frametitle` template closes
its box `1ex` above the title strut's depth (beamerouterthemedefault.sty:
169-180), and the body opens below that box, its `\vskip0.25em`, a `[t]`
frame's `.2cm` and one `\baselineskip`. Against lualatex on the unthemed
spelling (10 pt, the shipped Fira Sans for every face): the first body
line 17.93 bp below the title's baseline, held to half a point — the
title's leading remains, the rhythm's 17.28 pt against size10.clo's 18 pt.
The web deck trims the title to its baseline and adds the same box to the
body's opening. At `f319b96c` the line stood 24.39 bp below, and the web
deck held no such box. Invented words. -/
def titleOpeningChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "title opening: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr ("\\documentclass[10pt]{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}[t]{Alpha words}\nKilo words.\n\\end{frame}\n\\end{document}\n")
  t "title opening: the deck elaborates clean" (ds.all (·.severity != .error))
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let titleY := (out.pages[0]?.bind fun p => p.lines.find? fun l =>
    hasStr (lineText l) "Alpha").map (·.y)
  t "title opening: the first line stands beamer's box and skips below the title, as lualatex sets it"
    (match titleY, bodyLineY out 0 "Kilo" with
     | some ty, some bodyY => withinSp (ptMilli 500) (bodyY - ty) (ptMilli 17935)
     | _, _ => false)
  let (head, _, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  -- The box below the title's baseline, in the title's em and ex at its step:
  -- `calc(<step> * (<below>em - 1ex))`, each number the IR's own.
  let below := Ir.defaultFrameTitleBelow 1000 doc.page.leading 0
  let step := Ir.scaleStep 1000 Ir.plainFrameTitleStep
  let boxDecl := (cssBlocksFor css "section.slide:not(.title-page):not(.titlebar):has(> header)").findSome?
    (cssDeclOf · "--frame-title-below")
  t "title opening: the web title trims to its baseline and the body opens below beamer's box"
    ((cssBlocksFor css "section.slide:not(.title-page):not(.titlebar) > header h2").any
        (hasStr · "text-box: trim-end text alphabetic") &&
      (match boxDecl with
       | some v => match ((v.dropPrefix "calc(").toString.splitOn " * (") with
         | [k, rest] =>
           (Decl.parseDecimal k).any (fun (m, sc) => m * 1000 / (sc : Int) == step) &&
             cssEmMilli ((rest.splitOn " - ").headD "") == some below &&
             rest.endsWith " - 1ex))"
         | _ => false
       | none => false) &&
      (artCssBlocks css).any fun (sel, decls) =>
        hasStr sel "section.slide > .frame-body-start" && hasStr decls "var(--frame-title-below")

/-- **A centred frame splits its leftover as its theme's `[c]` key does**
(`Ir.VAlign.glue`): beamer's own a fill above against a fill and a half
below (beamerbaseframe.sty:257-258), moloch's one fil on either side
(beamerinnerthememoloch.sty:455-456). Against lualatex on `deck` (10 pt,
the shipped Fira Sans for every face), two and four lines centred: under
beamer's keys at 109.60 and 100.04 bp, under moloch's at 130.32 and
118.37, held to a fifth of a point. The web deck's spacers grow by the same
shares. At `f319b96c` beamer's keys centred evenly, the two lines at
134.00 bp. Invented words. -/
def centreSplitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "centre split: the shipped Fira Sans parses" false
  let two := "Kilo words.\n\nLima words."
  let four := two ++ "\n\nMike words.\n\nNovember words."
  for (theme, name, luaTwo, luaFour, grows) in [
      ("\\usetheme{default}\n", "beamer", 109600, 100035, #["1000", "1500"]),
      ("\\usetheme{moloch}\n", "moloch", 130322, 118372, #["1000", "1000"])] do
    let (doc, ds) := elabStr (beamerDeck theme [("c", two), ("c", four)])
    t s!"centre split {name}: the deck elaborates clean" (ds.all (·.severity != .error))
    let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
    t s!"centre split {name}: two and four centred lines stand where lualatex centres them"
      ((bodyLineY out 0 "Kilo").any (withinSp (ptMilli 200) · (ptMilli luaTwo)) &&
        (bodyLineY out 1 "Kilo").any (withinSp (ptMilli 200) · (ptMilli luaFour)))
    t s!"centre split {name}: the web stage's spacers grow by the key's shares"
      ((stagesOf doc).all (stageGrows · == grows) && (stagesOf doc).size == 2)
  -- A standout frame is moloch's key, which sets moloch's own `[c]` under
  -- any deck's keys (`Ir.frameKeysOf`): the block's top rises by half of
  -- its growth, the rate that cancels the lines' own boxes.
  let (sdoc, sds) := elabStr (beamerDeck "" [("standout", two), ("standout", four)])
  t "centre split: the standout deck elaborates clean" (sds.all (·.severity != .error))
  let sout := layoutOf fira sdoc (Layout.Geom.ofPage sdoc.page)
  t "centre split: a standout frame centres evenly under beamer's keys, on the page"
    (match bodyLineY sout 0 "Kilo", bodyLineY sout 0 "Lima", bodyLineY sout 1 "Kilo", bodyLineY sout 1 "November" with
     | some k2, some l2, some k4, some n4 =>
       let growth := (n4 - k4) - (l2 - k2)
       (k2 - k4 - growth / 2).natAbs ≤ 2
     | _, _, _, _ => false)
  t "centre split: a standout frame centres evenly under beamer's keys, in the web deck"
    ((stagesOf sdoc).size == 2 && (stagesOf sdoc).all (stageGrows · == #["1000", "1000"]))

/-- **A body's `\vfill` shares a frame's leftover with the frame's own glue
of its order** (`Layout.VDist.filAbove`, `HtmlDoc.deckSpacerShares`): TeX
stretches only the highest order of infinity present, in proportion to the
stretch each glue states (TeXbook ch. 12) — beamer's keys are of
`\vfill`'s order, so a `\vfill` takes its share beside them, and moloch's
`[c]` is an order below, so a `\vfill` takes it all. Against lualatex on the
spelling (10 pt, the shipped Fira Sans for every face), the line after a
`\vfill` under `[t]`, `[c]` and `[b]`: beamer's keys at 148.80, 163.40 and
268.02 bp (the line before at 17.62, 81.70 and 134.01), moloch's at 145.14,
260.65 and 260.59 (before: 17.62, 11.96, 130.30), held to a fifth of a
point. The web deck stands a spacer of one fill for the `\vfill` beside the
frame's, which a moloch `[c]` frame holding one drops. At `f319b96c` the
`\vfill` took the whole leftover on the page and the web deck rendered
nothing for it. Invented words. -/
def vfillChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "vfill: the shipped Fira Sans parses" false
  let body := "Kilo words.\n\n\\vfill\n\nLima words."
  for (theme, name, lua, grows) in [
      ("\\usetheme{default}\n", "beamer",
        #[(17624, 148800), (81701, 163402), (134011, 268021)],
        #[#["1000", "1000"], #["1000", "1000", "1500"], #["1000", "1000"]]),
      ("\\usetheme{moloch}\n", "moloch",
        #[(17624, 145142), (11955, 260654), (130297, 260594)],
        #[#["1000", "1000"], #["1000"], #["1000", "1000"]])] do
    let (doc, ds) := elabStr (beamerDeck theme [("t", body), ("c", body), ("b", body)])
    t s!"vfill {name}: the deck elaborates clean" (ds.all (·.severity != .error))
    let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
    t s!"vfill {name}: the lines around a vfill stand where lualatex shares the leftover"
      ((List.range 3).all fun i => match lua[i]? with
        | some (before, after) =>
          (bodyLineY out i "Kilo").any (withinSp (ptMilli 200) · (ptMilli before)) &&
            (bodyLineY out i "Lima").any (withinSp (ptMilli 200) · (ptMilli after))
        | none => false)
    t s!"vfill {name}: the web stage grows a fill's spacer beside the frame's"
      ((stagesOf doc).size == 3 && ((stagesOf doc).zip grows).all fun (s, g) => stageGrows s == g)

/-- The fill cases, in invented words: a name, the theme, the frame's
options, its body, the page held, where lualatex sets Kilo and Lima on it
(10 pt, the shipped Fira Sans for every face; `none` where only their
distance is held — the lines a box's fill leaves one baseline apart, a
list's own place aside — or where nothing is), and the grows of the web
stage's direct children. -/
private def fillCases : List (String × String × String × String × Nat × Option (Int × Int) × Int ×
    Array String) :=
  let beamer := "\\usetheme{default}\n"
  let moloch := "\\usetheme{moloch}\n"
  let fill := "Kilo words.\n\n\\vfill\n\nLima words."
  let paused := "Kilo words.\n\n\\pause\n\\vfill\n\nLima words."
  let items := "\\begin{itemize}\n\\item Kilo words.\n\\vfill\n\\item Lima words.\n\\end{itemize}"
  let block := "\\begin{block}{}\n" ++ fill ++ "\n\\end{block}"
  let column := "\\begin{columns}[T]\n\\column{.5\\textwidth}\n" ++ fill ++ "\n\\end{columns}"
  let plain := "Kilo words.\n\nLima words."
  let spacer := "\\newcommand\\spacer[1]{\\vspace{#1}}\nKilo words.\n\n\\spacer{\\fill}\n\nLima words."
  let desc := "\\begin{description}\n\\item[Kilo] words.\n\\vfill\n\\item[Lima] words.\n\\end{description}"
  let nested := "\\begin{itemize}\n\\item Kilo words.\n\\begin{itemize}\n\\item Mike words.\n" ++
    "\\vfill\n\\item Oscar words.\n\\end{itemize}\n\\item Lima words.\n\\end{itemize}"
  let midItem := "\\begin{itemize}\n\\item Kilo words.\n\\vfill\nLima words.\n\\end{itemize}"
  let figure := "\\begin{figure}\n" ++ fill ++ "\n\\end{figure}"
  let table := "\\begin{table}\n" ++ fill ++ "\n\\end{table}"
  let alt := "\\alt<2>{" ++ fill ++ "}{" ++ plain ++ "}"
  let stepped := "\\begin{itemize}\n\\item<2-> Kilo words.\n\\vfill\n\\item Lima words.\n\\end{itemize}"
  let template := moloch ++ "\\makeatletter\n\\setbeamertemplate{block begin}{%\n" ++
    "  \\par\\vskip\\medskipamount\n  \\ifx\\insertblocktitle\\@empty\\else\n" ++
    "    {\\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}" ++
    "\\strut\\insertblocktitle\\strut\\par}%\n  \\fi\n" ++
    "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n\\makeatother\n" ++
    "\\setbeamertemplate{block end}{\\par\\vskip\\smallskipamount}\n"
  let titled := "\\begin{block}{Alpha}\n" ++ fill ++ "\n\\end{block}"
  [("pause beamer", beamer, "c", paused, 1, some (81701, 163402), 81701, #["1000", "1000", "1500"]),
   ("pause moloch", moloch, "c", paused, 1, some (11955, 260704), 248749, #["1000"]),
   ("items beamer", beamer, "c", items, 0, none, 82128, #["1000", "1000", "1500"]),
   ("items moloch", moloch, "c", items, 0, some (14944, 257665), 242721, #["1000"]),
   ("block beamer", beamer, "c", block, 0, none, 11955, #["1000", "1500"]),
   ("block moloch", moloch, "c", block, 0, none, 11955, #["1000", "1000"]),
   ("column beamer", beamer, "c", column, 0, none, 11955, #["1000", "1500"]),
   ("column moloch", moloch, "c", column, 0, none, 11955, #["1000", "1000"]),
   ("breakable fill beamer", beamer, "c,allowframebreaks", fill, 0, some (11955, 268021),
     256066, #["1000"]),
   ("breakable fill moloch", moloch, "c,allowframebreaks", fill, 0, some (11955, 260644),
     248689, #["1000"]),
   ("breakable beamer", beamer, "c,allowframebreaks", plain, 0, some (109598, 121553),
     11955, #["1000", "1500"]),
   ("breakable moloch", moloch, "c,allowframebreaks", plain, 0, some (106627, 118582),
     11955, #["1000", "1500"]),
   ("group beamer", beamer, "c", spacer, 0, some (81701, 163402), 81701, #["1000", "1000", "1500"]),
   ("group moloch", moloch, "c", spacer, 0, some (11955, 260704), 248749, #["1000"]),
   ("description beamer", beamer, "c", desc, 0, some (82128, 164256), 82128,
     #["1000", "1000", "1500"]),
   ("description moloch", moloch, "c", desc, 0, some (14944, 257665), 242721, #["1000"]),
   ("figure beamer", beamer, "c", figure, 0, some (85117, 162264), 77147, #["1000", "1000", "1500"]),
   ("figure moloch", moloch, "c", figure, 0, some (19925, 252674), 232749, #["1000"]),
   ("table beamer", beamer, "c", table, 0, some (85117, 162264), 77147, #["1000", "1000", "1500"]),
   ("table moloch", moloch, "c", table, 0, some (19925, 252624), 232699, #["1000"]),
   ("item step moloch", moloch, "c", stepped, 1, some (14944, 257705), 242761, #["1000"]),
   ("templated block moloch", template, "c", titled, 0, some (29888, 257715), 227827, #["1000"]),
   ("nested items moloch", moloch, "c", nested, 0, some (242661, 257605), 14944, #["1000", "1000"]),
   ("mid-item moloch", moloch, "c", midItem, 0, some (14944, 257665), 242721, #["1000", "1000"]),
   ("alternation beamer, step 1", beamer, "c", alt, 0, some (109600, 121555), 11955,
     #["1000", "1500"]),
   ("alternation beamer, step 2", beamer, "c", alt, 1, some (81701, 163402), 81701,
     #["1000", "1500"]),
   ("alternation moloch, step 1", moloch, "c", alt, 0, some (130327, 142282), 11955,
     #["1000", "1000"]),
   ("alternation moloch, step 2", moloch, "c", alt, 1, some (11955, 260654), 248699,
     #["1000", "1000"])]

/-- **A fill shares the leftover wherever it stands on the frame's own list,
and stretches nothing inside a box** (`Ir.Block.listScope`, the one
classification the page's reader, the web deck and the fill census read):
TeX sets a fill an overlay step, a list item, a group, a description or one
side of an alternation holds on the frame's vertical list, and beamer's
`{figure}` and `{table}` are a `{center}` there (beamerbaselocalstructure.sty:
550-560); a fill in a beamer block or a column sets in a box at its natural
height, and a breakable centred frame's own glue is finite
(`Ir.autobreakCentre`), so a fill takes all of its leftover and without one
it splits two to three. Against lualatex on the spelling (10 pt, the shipped
Fira Sans for every face), held to a fifth of a point: after `\pause`
(beamer's keys 81.70 and 163.40 bp, moloch's 11.96 and 260.70), between two
items (moloch's 14.94 and 257.67; beamer's 82.13 apart), in a group a macro
opens (81.70 and 163.40; 11.96 and 260.70), between two descriptions (82.13
and 164.26; 14.94 and 257.67), in a figure (85.12 and 162.26; 19.93 and
252.67) and a table (19.93 and 252.62 under moloch), a fill in a block or a
column leaving its lines one baseline apart, a breakable frame's lines
around its fill (beamer's 11.96 and 268.02, moloch's 11.96 and 260.64) and
without one (beamer's 109.60, moloch's 106.63), an alternation's two steps
(beamer's 109.60 and 121.56, then 81.70 and 163.40; moloch's 130.33 and
142.28, then 11.96 and 260.65), under moloch a fill an item's step ends on
(14.94 and 257.71) and one in a block standing in its kind's declared
template, which sets no box (29.89 and 257.72), and under moloch a fill before more of its item (14.94
and 257.67) or between nested items (Oscar 242.66, Lima 257.61). The web stage's direct children grow by the frame's spacers
and by the fills the deck reads (`Ir.FillView.deck`). At `f319b96c` a
block's and a column's fill took the leftover on the page, a breakable frame
centred evenly or shared its leftover with a fill, and the web deck grew none
of them; on the branch's first reviewed tree a figure's and a table's fill
stretched nothing. Invented words. -/
def nestedFillChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "nested fill: the shipped Fira Sans parses" false
  for (name, theme, opt, body, page, at?, apart, grows) in fillCases do
    let (doc, ds) := elabStr (beamerDeck theme [(opt, body)])
    t s!"nested fill {name}: the deck elaborates clean" (ds.all (·.severity != .error))
    let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
    let near := withinSp (ptMilli 200)
    let lower := if hasStr name "nested" then "Oscar" else "Kilo"
    t s!"nested fill {name}: the lines stand where lualatex shares the frame's leftover"
      (match bodyLineY out page lower, bodyLineY out page "Lima", at? with
       | some k, some l, some (lk, ll) => near k (ptMilli lk) && near l (ptMilli ll)
       | some k, some l, none => near (l - k) (ptMilli apart)
       | _, _, _ => false)
    t s!"nested fill {name}: the web stage grows by its spacers and the fills the deck reads"
      ((stagesOf doc).size == 1 && (stagesOf doc).all (stageGrows · == grows))

/-- The last declaration of `key` on an element's style attribute: the one
CSS applies. -/
private def styleLast (attrs : Array (String × String)) (key : String) : Option String :=
  (((HtmlDoc.attrOf? attrs "style").getD "").splitOn ";").foldl (fun acc d =>
    match d.splitOn ":" with
    | k :: rest => if k.trimAscii.toString == key then some (":".intercalate rest).trimAscii.toString
      else acc
    | [] => acc) none

/-- An element's `flex-grow`, zero where it declares none. -/
private def growOf : Html.Node → Nat
  | .elem _ attrs _ => ((styleLast attrs "flex-grow").bind (·.toNat?)).getD 0
  | .text _ | .style _ | .script .. => 0

private def classesOf (attrs : Array (String × String)) : List String :=
  ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " "

mutual

/-- The fills a list item ends on, as its last children: document skips with
no extent of their own, read through an overlay step or a backend's share
the item ends on, as the census reads them (`Ir.trailingFillsOne`). `n` is
the run so far. -/
private def tailSkipsOne (n : Nat) : Html.Node → Nat
  | .elem "div" attrs kids =>
    if (classesOf attrs).contains HtmlDoc.skipClass && styleLast attrs "--skip" == none then n + 1
    else if (classesOf attrs).contains "step" || (HtmlDoc.attrOf? attrs "data-backend").isSome then
      tailSkipsList 0 kids.toList
    else 0
  | .text s => if s.isEmpty then n else 0
  | .elem .. | .style _ | .script .. => 0

private def tailSkipsList (n : Nat) : List Html.Node → Nat
  | [] => n
  | k :: rest => tailSkipsList (tailSkipsOne n k) rest

end

private def trailingSkips (kids : Array Html.Node) : Nat := tailSkipsList 0 kids.toList

mutual

/-- The faults of a stage's fill growth at `n`, whose ancestors up to the
stage are all growing flex columns where `carried` holds: an element that
grows where an ancestor does not grows nothing, a growing flex column grows by
exactly its children's grows (a `fill-before` box its own fill's too), and a
growing list item, which is no flex column, by the fills it ends on. -/
private def growFaultsOne (carried : Bool) (acc : Array String) : Html.Node → Array String
  | .elem tag attrs kids =>
    let g := growOf (.elem tag attrs kids)
    let cls := classesOf attrs
    let acc := if g > 0 && !carried then acc.push s!"{tag} {cls} grows {g} under a box that does not"
      else acc
    let column := styleLast attrs "display" == some "flex" &&
      styleLast attrs "flex-direction" == some "column"
    if g > 0 && column then
      let own := if cls.contains "fill-before" then Ir.fillUnit else 0
      let sum := kids.foldl (fun n k => n + growOf k) own
      let acc := if sum == g then acc else acc.push s!"{tag} {cls} grows {g}, its contents {sum}"
      growFaultsList true acc kids.toList
    else if g > 0 && tag == "li" then
      let acc := if g == Ir.fillUnit * trailingSkips kids then acc
        else acc.push s!"li grows {g}, ending on {trailingSkips kids} fills"
      growFaultsList false acc kids.toList
    else growFaultsList false acc kids.toList
  | .text _ | .style _ | .script .. => acc

private def growFaultsList (carried : Bool) (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | n :: rest => growFaultsList carried (growFaultsOne carried acc n) rest

end

/-- **Every fill the web stage grows grows something, and the stage grows by
the fills the deck reads** (`HtmlDoc.fillCarrier`, `Ir.FillView.deck`):
over the typed tree of every fill case's stage, an element with a grow
stands in an unbroken chain of growing flex columns up to the stage, a
carrier grows by exactly what it holds, a list item by the fills it ends on,
and the stage's children other than its spacers by the deck's census of the
frame's fills. A frame whose census on the page exceeds the deck's — a fill
before more of its item, a fill in an alternation — and only such a frame
is named once in the web build (W0399). On the branch's first reviewed tree a
fill in a group, a link, a description, a backend's share or a nested item
grew inside a box that did not, so it moved nothing, and nothing named
it. Invented words. -/
def fillCarrierChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let engineOnly : List (String × String × String) :=
    [("link", "\\usetheme{moloch}\n",
        "\\link{https://example.org}{Kilo words.\n\n\\vfill\n\nLima words.}"),
     ("backend share", "\\usetheme{moloch}\n",
        "\\begin{ifbackend}{html,pdf}\nKilo words.\n\n\\vfill\n\nLima words.\n\\end{ifbackend}"),
     ("fill before", "\\usetheme{default}\n", "Kilo words.\n\n\\block[before = fill]{Lima words.}"),
     ("centre", "\\usetheme{default}\n",
        "\\begin{center}\nKilo words.\n\n\\vfill\n\nLima words.\n\\end{center}")]
  let cases := fillCases.map (fun (n, th, opt, body, _) => (n, th, opt, body)) ++
    engineOnly.map fun (n, th, body) => (n, th, "c", body)
  for (name, theme, opt, body) in cases do
    let (doc, _) := elabStr (beamerDeck theme [(opt, body)])
    let fbody := match doc.body.toList.find? (· matches .frame ..) with
      | some (.frame _ _ _ _ b) => b
      | _ => #[]
    let lists := doc.docClass.record.lists
    for stage in stagesOf doc do
      let kids := match stage with
        | .elem _ _ ks => ks
        | .text _ | .style _ | .script .. => #[]
      t s!"fill carrier {name}: every grow stands in a chain of growing flex columns, and conserves"
        (growFaultsList true #[] kids.toList).isEmpty
      let held := kids.foldl (fun n k => match k with
        | .elem _ attrs _ => if (classesOf attrs).contains "fill" then n else n + growOf k
        | .text _ | .style _ | .script .. => n) 0
      t s!"fill carrier {name}: the stage grows by the deck's census of the frame's fills"
        (held == Ir.fillUnit * Ir.frameFills lists doc.styles .deck fbody)
    let (_, hds) := HtmlDoc.emit {} doc
    let named := hds.any (·.code == "W0399")
    t s!"fill carrier {name}: the web build names a fill it cannot grow, and only then"
      (named == (Ir.frameFills lists doc.styles .deck fbody < Ir.frameFills lists doc.styles .every fbody))
    t s!"fill carrier {name}: a named fill's frame is the subject"
      (hds.all fun d => d.code != "W0399" || d.subject == some "1")

/-- **The page shares its leftover among the fills the census counts on it**
(`Ir.FillView.page`, `Layout.PageOut.fils`): over every fill case, each page
of the frame closes on exactly the fill units the census reads on the frame
at the page's step — an alternation's shown side, a box's fills none. -/
def fillCensusChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "fill census: the shipped Fira Sans parses" false
  for (name, theme, opt, body, page, _) in fillCases do
    let (doc, _) := elabStr (beamerDeck theme [(opt, body)])
    let fbody := match doc.body.toList.find? (· matches .frame ..) with
      | some (.frame _ _ _ _ b) => b
      | _ => #[]
    let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
    t s!"fill census {name}: the page closes on the fills the census reads at its step"
      ((out.pages[page]?.map (·.fils)) ==
        some (Ir.frameFills doc.docClass.record.lists doc.styles (.page (page + 1)) fbody))

/-- **Outside a deck a quotation and an abstract stand on the page's own
list** (`Ir.Block.listScope`): article sets both as a quotation list, so a
fill inside either takes the page's leftover, where beamer's colour box sets
it at its natural height. Over `Layout.Out` on an article (the shipped Fira
Sans for every face): the line after the fill stands one paragraph above the
line after the environment, the page's last, as lualatex's 17.93 bp (the
abstract) and 21.92 bp (the quotation), held to half a point. On the
branch's first reviewed tree the abstract's fill stretched nothing.
Invented words. -/
def articleFillChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "article fill: the shipped Fira Sans parses" false
  let fill := "Kilo words.\n\n\\vfill\n\nLima words."
  let (doc, ds) := elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
    s!"\\begin\{abstract}\n{fill}\n\\end\{abstract}\nMike words.\n\\newpage\n" ++
    s!"\\begin\{quote}\n{fill}\n\\end\{quote}\nMike words.\n\\end\{document}\n")
  t "article fill: the article elaborates clean" (ds.all (·.severity != .error))
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  for (page, env, lua) in [(0, "abstract", 17930), (1, "quotation", 21920)] do
    let lines := ((out.pages[page]?.map (·.lines)).getD #[]).filter (!·.furniture)
    t s!"article fill {env}: the line after the environment is the page's last"
      ((lines.back?.map fun l => hasStr (lineText l) "Mike") == some true)
    t s!"article fill {env}: the fill puts one paragraph's gap between it and the page's last line"
      (match bodyLineY out page "Lima", bodyLineY out page "Mike" with
       | some l, some m => withinSp (ptMilli 500) (m - l) (ptMilli lua)
       | _, _ => false)

/-- **An alerted word takes its theme's alert colour and the body's face**
(`Compat.alertStyled`): beamer's `\alert` selects the `alerted text` colour
and font, and beamer's default font theme leaves that font empty
(beamerfontthemedefault.sty:15), as moloch does. Over `Layout.Out`, with the
regular and the bold weight set apart: under moloch and in a deck naming no
theme — its class's default bundle — the word sets in the regular face in
the bundle's alert colour, and the typed HTML tree carries that colour and no
strong emphasis. A deck that names bareness has no alert colour to read,
and only that its word still stands apart from its neighbours is held here:
beamer's default colour theme sets it red in the regular face, which the bare
deck does not install (`Compat.alertStyled`), and the bold standing in is a
departure this check leaves open rather than asserts. lualatex sets the
moloch word in the regular face. At `f319b96c` the themed word was bold, and
a deck naming no theme set it bold in its ink. Invented words. -/
def alertChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some font ← shippedFiraFont | t "alert: the shipped Fira Sans parses" false
  let weighted : Font.FontSet := {
    fonts := #[font, font]
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 1),
       ((slot, 400, true), 0), ((slot, 700, true), 1)]).toArray }
  for (theme, name, bare) in [("\\usetheme{moloch}\n", "moloch", false),
      ("", "a deck naming no theme", false), ("\\usetheme{default}\n", "a bare deck", true)] do
    let (doc, ds) := elabStr (beamerDeck theme [("t", "Kilo \\alert{lima} words.")])
    t s!"alert {name}: the deck elaborates clean" (ds.all (·.severity != .error))
    let out := layoutOf weighted doc (Layout.Geom.ofPage doc.page)
    let runOf (word : String) := (allLines out).findSome? fun l => l.segs.findSome? fun s =>
      match s with
      | .run idx color _ _ glyphs _ _ _ _ _ _ =>
        if glyphs.foldl (fun acc (_, c, _) => acc.push c) "" == word then some (idx, color)
        else none
      | _ => none
    let run := runOf "lima"
    let alert := doc.palette.find? "alert"
    let (_, body, _) := HtmlDoc.emitTree {} doc
    let strong := (elemNodesList (· == "strong") #[] body.toList).any fun n =>
      hasStr (nodeTextOne "" n) "lima"
    let coloured := (elemNodesList (fun _ => true) #[] body.toList).any fun n => match n with
      | .elem _ attrs _ => nodeTextOne "" n == "lima" &&
          hasStr ((HtmlDoc.attrOf? attrs "style").getD "")
            ("var(" ++ (Ir.ColorRef.role .alert).property)
      | .text _ | .style _ | .script .. => false
    if bare then
      t s!"alert {name}: the alerted word stands apart from its neighbours on the page"
        (run.isSome && run != runOf "Kilo")
      t s!"alert {name}: the web word stands apart from its neighbours" (strong || coloured)
    else
      t s!"alert {name}: the alerted word sets in the regular face" (run.map (·.1) == some 0)
      t s!"alert {name}: the alerted word takes the bundle's alert colour"
        (alert.isSome && run.map (·.2) == alert)
      t s!"alert {name}: the web word is not strong emphasis" (!strong)
      t s!"alert {name}: the web word takes the alert colour" coloured

end Tests.FrameGeometry
