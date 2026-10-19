module

public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FrameGeometry

/-- The slide stages of a document's web deck. -/
private def stagesOf (doc : Ir.Doc) : Array Html.Node :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  slideStages body

/-- A moloch frame title starts the bar's inset, 0.85 of the title's strut, from the paper's edge,
on both artifacts. -/
def titleInsetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "title inset: the shipped Fira Sans parses" false
  for (font, step, lua) in [("", "large", 8299),
      ("\\setbeamerfont{frametitle}{size=\\Large}\n", "Large", 10670)] do
    let (doc, ds) := elabStr (s!"\\documentclass[10pt]\{beamer}\n\\usetheme\{moloch}\n{font}" ++
      "\\begin{document}\n\\begin{frame}{Alpha words}\nKilo words.\n\\end{frame}\n\\end{document}\n")
    let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
    let title := ((out.pages[0]?.map (·.lines)).getD #[]).find? fun l => hasStr (lineText l) "Alpha"
    let inset := Ir.frameTitleInset (Ir.scaleStepIn Ir.sizeScale doc.page.fontSize step)
    t s!"title inset {step}: the deck elaborates clean" (ds.all (·.severity != .error))
    t s!"title inset {step}: the title starts the bar's inset from the paper's left edge"
      (title.map (·.x) == some inset)
    t s!"title inset {step}: the title starts within half a point of lualatex's"
      (title.any fun l => withinSp (ptMilli 500) l.x (ptMilli lua))
    let (head, _, _) := HtmlDoc.emitTree {} doc
    let css := treeCssList "" head.toList
    t s!"title inset {step}: the web bar pads its title by the inset, in em of the title"
      ((cssBlocksFor css "section.slide > header").any fun decls =>
        match cssProperty decls "padding" with
        | some v => match v.splitOn " " with
          | [top, side] => top == "0" && cssEmMilli side == some (Ir.frameTitleInset (1000 * Dim.Length.quantum)).units
          | _ => false
        | none => false)

/-- A standout frame bears no number and advances no count, so the footline's numbers and the
section page's bar read the frames lualatex counts. -/
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

/-- A moloch section page sets its title and bar in moloch's `0.7875\linewidth` measure, centred, on
both artifacts. -/
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
    ((artCssBlocks css).toList.filter fun (s, _) => (cssSelectorParts s).contains sel).any
      fun (_, decls) => match cssProperty decls "width" with
      | some v => match (v.dropPrefix "min(").toString.splitOn ", " with
        | [share, "100%)"] => cssStageLength s!"width: {share}" "width" measure doc.page.height
        | _ => false
      | none => false
  t "section measure: the web section page's title and bar take the same share of the stage"
    (shares "section.section-page h2" && shares ".progress")

/-- A bar-less frame title stands in beamer's default title box, the body opening below it, on both
artifacts. -/
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
  -- The box below the title's baseline in the title's em and ex at its step, each number the IR's.
  let below := (Ir.defaultFrameTitleBelow (1000 * Dim.Length.quantum) doc.page.leading 0).units
  let step := (Ir.scaleStepIn Ir.sizeScale (1000 * Dim.Length.quantum) Ir.plainFrameTitleStep).units
  let boxDecl := (cssBlocksFor css "section.slide:not(.title-page):not(.titlebar):has(> header)").findSome?
    (cssProperty · "--frame-title-below")
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

/-- A centred frame splits its leftover as its theme's `[c]` key does, on both artifacts. -/
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
  -- A standout frame is moloch's key, which sets moloch's own `[c]` under any deck's keys.
  let (sdoc, sds) := elabStr (beamerDeck "" [("standout", two), ("standout", four)])
  t "centre split: the standout deck elaborates clean" (sds.all (·.severity != .error))
  let sout := layoutOf fira sdoc (Layout.Geom.ofPage sdoc.page)
  t "centre split: a standout frame centres evenly under beamer's keys, on the page"
    (match bodyLineY sout 0 "Kilo", bodyLineY sout 0 "Lima", bodyLineY sout 1 "Kilo", bodyLineY sout 1 "November" with
     | some k2, some l2, some k4, some n4 =>
       let growth := (n4 - k4) - (l2 - k2)
       (k2 - k4 - growth / 2).abs ≤ 2 * Dim.Length.quantum
     | _, _, _, _ => false)
  t "centre split: a standout frame centres evenly under beamer's keys, in the web deck"
    ((stagesOf sdoc).size == 2 && (stagesOf sdoc).all (stageGrows · == #["1000", "1000"]))

/-- A body's `\vfill` shares a frame's leftover with the frame's own glue of its order, as TeX
stretches only the highest order present. -/
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

/-- The fill cases: a name, the theme, the frame's options, its body, the page held, lualatex's Kilo
and Lima baselines (`none` where only their distance is held), and the web stage's grows. -/
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

/-- A fill shares the leftover wherever it stands on the frame's own list and stretches nothing
inside a box, on both artifacts. -/
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

/-- The last declaration of `key` on an element's style attribute. -/
private def styleLast (attrs : Array (String × String)) (key : String) : Option String :=
  cssProperty ((HtmlDoc.attrOf? attrs "style").getD "") key

/-- An element's `flex-grow`, zero where it declares none. -/
private def growOf : Html.Node → Nat
  | .elem _ attrs _ => ((styleLast attrs "flex-grow").bind (·.toNat?)).getD 0
  | .text _ | .style _ | .script .. => 0

private def classesOf (attrs : Array (String × String)) : List String :=
  ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " "

mutual

/-- The fills a list item ends on, read through an overlay step or a backend's share as the census
reads them; `n` is the run so far. -/
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

/-- The faults of a stage's fill growth: a grow under a non-growing ancestor, a flex column not
growing by its children's grows, a list item not growing by the fills it ends on. -/
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

/-- Every fill the web stage grows grows something, and the stage grows by the fills the deck reads;
a frame whose page census exceeds the deck's is named once (W0399). -/
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

/-- The page shares its leftover among the fills the census counts on it. -/
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

/-- Outside a deck a quotation and an abstract stand on the page's own list, so a fill inside either
takes the page's leftover. -/
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

/-- An alerted word takes its theme's alert colour and the body's face. -/
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
