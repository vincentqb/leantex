module

public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FrameArea

/-- The invented moloch deck the checks lay out: standout frames (one whose note the footline hook
restores, one naming `b`), a titled control, a section page and a bottom-aligned frame. -/
private def deck : String :=
  "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n" ++
  "\\newenvironment{framefooter}[1]{%\n" ++
  "  \\setbeamertemplate{frame footer}{{\\scriptsize #1}}%\n" ++
  "}{\\setbeamertemplate{frame footer}{}}\n" ++
  "\\makeatletter\n" ++
  "\\apptocmd{\\KV@beamerframe@standout}{%\n" ++
  "  \\ifbeamertemplateempty{frame footer}{}{%\n" ++
  "    \\setbeamercolor{footline}{use={standout,background canvas},\n" ++
  "      fg=standout.fg,bg=background canvas.bg}%\n" ++
  "    \\setbeamertemplate{footline}[plain]%\n" ++
  "    \\ifbeamer@noframenumbering\n" ++
  "      \\setbeamertemplate{page number in head/foot}{}%\n" ++
  "    \\fi\n" ++
  "  }%\n" ++
  "}{}{\\PackageError{probe}{hook}{}}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[standout]\nKilo words.\n\\end{frame}\n" ++
  "\\begin{framefooter}{Lima mike}\n" ++
  "\\begin{frame}[standout]\nKilo words.\n\\end{frame}\n" ++
  "\\end{framefooter}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\begin{frame}[b,standout]\nKilo words.\n\\end{frame}\n" ++
  "\\section{Hotel words}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\begin{frame}[b]\nKilo words.\n\\end{frame}\n" ++
  "\\end{document}\n"

/-- A templated title page with a section page on its heels, a frame, and a second section page of
the same title. -/
private def slottedDeck : String :=
  "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n" ++
  "\\setbeamertemplate{title page}{%\n" ++
  "  \\begin{tikzpicture}[remember picture,overlay]\n" ++
  "    \\node[anchor=west, align=left, text width=0.86\\paperwidth]\n" ++
  "      at ([xshift=1.05cm,yshift=0.15cm]current page.west) {%\n" ++
  "      {\\raggedright\\usebeamerfont{title}\\inserttitle\\par}};\n" ++
  "    \\node[anchor=south west, align=left, text width=0.86\\paperwidth]\n" ++
  "      at ([xshift=1.05cm,yshift=0.8cm]current page.south west) {%\n" ++
  "      {\\raggedright\\insertauthor\\par}};\n" ++
  "  \\end{tikzpicture}%\n" ++
  "  \\null\n}\n" ++
  "\\title{Kilo lima}\n\\author{Mike November}\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[plain,noframenumbering]\n\\titlepage\n\\end{frame}\n" ++
  "\\section{Hotel words}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\section{Hotel words}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\end{document}\n"

/-- Every frame stands its content box in beamer's text area, held to lualatex's baselines on `deck`
within 0.5 bp. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "frame area: the shipped Fira Sans parses" false
  let (doc, _) := elabStr deck
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let near := withinSp (Dim.Length.ofBpMilli 500)
  let line (out : Layout.Out) (page : Nat) (word : String) (furniture : Bool := false) :
      Option Layout.LineOut :=
    out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.furniture == furniture && hasStr (lineText l) word
  let at? (page : Nat) (word : String) (milli : Int) (furniture : Bool := false) : Bool :=
    ((line out page word furniture).map fun l => near l.y (Dim.Length.ofBpMilli milli)).getD false
  t "frame area: a standout frame centres in beamer's text area, as lualatex does"
    (at? 0 "Kilo" 142951)
  t "frame area: a restored standout note lifts its frame by half its footheight, as lualatex does"
    (at? 1 "Kilo" 138197 && at? 1 "Lima" 268057 true)
  t "frame area: a standout frame centres whatever alignment it names, as moloch's key does"
    (at? 3 "Kilo" 142951)
  t "frame area: a section page centres on the whole paper, as lualatex does"
    (at? 4 "Hotel" 127894)
  t "frame area: a bottom-aligned frame stands its last line on its text area's floor, as lualatex does"
    (at? 6 "Kilo" 260590)
  -- A title page's slots each set from its page's top; lualatex sets both section pages at 127.894.
  let (sdoc, _) := elabStr slottedDeck
  let sout := layoutOf fira sdoc (Layout.Geom.ofPage sdoc.page)
  let sectionY (page : Nat) : Option Dim.Length :=
    sout.pages[page]?.bind fun p =>
      (p.lines.find? fun l => hasStr (lineText l) "Hotel").map (·.y)
  t "frame area: a section page on a title page's heels opens as every section page does"
    (match sectionY 1, sectionY 3 with
     | some a, some b => a == b && near a (Dim.Length.ofBpMilli 127894)
     | _, _ => false)
  let geom := Layout.Geom.ofPage doc.page
  let band := ((out.pages[6]?.map (·.lines)).getD #[]).filter (·.furniture)
  let box := band.foldl (fun (acc : Dim.Length × Dim.Length) l =>
    let (h, d) := Layout.segsInk fira l.segs
    (max acc.1 h, max acc.2 d)) (0, 0)
  t "frame area: a bottom-aligned frame's content ends on its text area's floor"
    (!band.isEmpty && ((line out 6 "Kilo").map fun l =>
      l.y + (Layout.segsInk fira l.segs).2 ==
        Layout.frameFloor geom.pageH Ir.footline.sep (some box)).getD false)

/-- The deck the class option `t` declares, with a frame naming `c` and a standout frame; `opt` is
the class options' tail, `frame` every unaligned frame's options. -/
private def classDeck (opt frame : String) : String :=
  s!"\\documentclass[10pt{opt}]\{beamer}\n\\usetheme\{moloch}\n\\begin\{document}\n" ++
  s!"\\begin\{frame}{frame}\{Foxtrot}\nAlpha words.\n\\end\{frame}\n" ++
  s!"\\begin\{frame}{frame}\nKilo words.\n\\end\{frame}\n" ++
  "\\begin{frame}[c]{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\begin{frame}[standout]\nKilo words.\n\\end{frame}\n\\end{document}\n"

/-- The class option `t` aligns every frame naming no alignment as `[t]` does, two builds apart,
while a frame naming `c` and a standout still centre. -/
def classAlignChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "class t: the shipped Fira Sans parses" false
  let (tdoc, tds) := elabStr (classDeck ",t" "")
  let (edoc, eds) := elabStr (classDeck "" "[t]")
  let ys (doc : Ir.Doc) : Array (Array Dim.Length) :=
    (layoutOf fira doc (Layout.Geom.ofPage doc.page)).pages.map (·.lines.map (·.y))
  t "class t: the deck sets every bare frame as an explicit [t] sets it"
    (ys tdoc == ys edoc && (HtmlDoc.emit {} tdoc).1 == (HtmlDoc.emit {} edoc).1 &&
      tds.size == eds.size)
  let near := withinSp (Dim.Length.ofBpMilli 500)
  let out := layoutOf fira tdoc (Layout.Geom.ofPage tdoc.page)
  let at? (page : Nat) (word : String) (milli : Int) : Bool :=
    ((out.pages[page]?.bind fun p => p.lines.find? fun l =>
      !l.furniture && hasStr (lineText l) word).map fun l => near l.y (Dim.Length.ofBpMilli milli)).getD false
  t "class t: an untitled frame opens at the text area's top and a standout frame centres, as lualatex does"
    (at? 1 "Kilo" 17620 && at? 3 "Kilo" 142950)
  let centred (doc : Ir.Doc) : Option Ir.VAlign := doc.body.findSome? fun b => match b with
    | .frame _ false v _ _ => if v matches .center then some v else none
    | _ => none
  t "class t: a frame naming c keeps its centring"
    (centred tdoc).isSome

/-- An invented deck whose frames open on a paragraph, on lists and on
images: `[t]` untitled, a paragraph, an itemize, an enumerate, an image
taller than the body's `\baselineskip` and one shorter. -/
private def openDeck : String :=
  "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n\\begin{document}\n" ++
  "\\begin{frame}[t]\nKilo words.\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{itemize}\n\\item Kilo words.\n\\item Lima words.\n" ++
  "\\end{itemize}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{enumerate}\n\\item Kilo words.\n\\end{enumerate}\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\includegraphics[width=20pt,height=40pt]{tall.png}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\includegraphics[width=20pt,height=8pt]{tall.png}\n\\end{frame}\n" ++
  "\\end{document}\n"

/-- A frame's content opens as TeX opens it below its `\vbox{}`, on both artifacts. -/
def openingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "frame opening: the shipped Fira Sans parses" false
  let (doc, _) := elabStr openDeck
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let first (page : Nat) : Option Dim.Length :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      !l.furniture && hasStr (lineText l) "Kilo").map (·.y)
  let near := withinSp (Dim.Length.ofBpMilli 500)
  let size := doc.page.fontSize
  let lead := Ir.leadingFor size doc.page.leading
  let skip := (Ir.frameBodySkip false .top).resolve size 0
  t "frame opening: a paragraph's first baseline stands one baselineskip below the opening, as lualatex's"
    ((first 0).any fun y => y == skip + lead && near y (Dim.Length.ofBpMilli 17620))
  let listOpen : Option Dim.Length := (Ir.listSkips doc.docClass.record.lists size 1).map fun sk =>
    sk.topsep.width.sp + (Ir.partopsepFor doc.docClass.record.lists size 1 doc.tokens).width.sp
  t "frame opening: a list's first item stands its topsepadd lower, as lualatex's"
    (match first 1, first 2, listOpen with
     | some a, some b, some o => a == skip + o + lead && b == a && near a (Dim.Length.ofBpMilli 20610)
     | _, _, _ => false)
  -- An image's box takes TeX's interline glue at its paragraph's `\baselineskip`.
  let imageY (page : Nat) : Option Dim.Length :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.segs.any (· matches .image ..)).map (·.y)
  t "frame opening: an image stands TeX's interline glue below the opening, as lualatex's"
    ((imageY 3).any (fun y => y == skip + Ir.inkClearance + Dim.pt 40 && near y (Dim.Length.ofBpMilli 46517)) &&
     (imageY 4).any (fun y => y == skip + lead && near y (Dim.Length.ofBpMilli 17624)))
  let (head, _, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let blocks := artCssBlocks css
  let strut := blocks.filter fun (sel, _) => hasStr sel "p.frame-body-start::before"
  t "frame opening html: the first line's strut is the page's baselineskip at an em of the line"
    (strut.size == 1 && strut.all fun (sel, d) =>
      hasStr sel "li:first-child" &&
      ((cssProperty d "height").bind cssEmMilli).any (· * size / 1000 == lead))
  -- Every frame's last element is marked, and its last line trims to its baseline.
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let classes := attrValuesOf (fun _ => true) "class" (Html.elem "body" body #[])
  let trims := blocks.filter fun (sel, d) =>
    hasStr sel ".frame-body-end" && cssProperty d "text-box" == some "trim-end text alphabetic"
  t "frame opening html: a frame's content ends on its last line's baseline"
    (trims.size == 1 && trims.all (fun (sel, _) =>
      hasStr sel "p, ul, ol" && !hasStr sel "pre" && !hasStr sel ".block" && !hasStr sel "figure") &&
     (classes.filter (·.splitOn " " |>.contains "frame-body-end")).size ==
       (classes.filter (·.splitOn " " |>.contains "slide")).size)
  t "frame opening html: an opening list rides its topsepadd on the opening, the stage's share"
    ((listOpen.any fun o => (blocks.filter fun (sel, _) =>
        hasStr sel "ul:not(.bibliography)" && hasStr sel ").frame-body-start").any
      fun (_, d) => cssStageLength d "--frame-body-open" o doc.page.height) &&
     (cssBlocksFor css ":where(section.slide > .frame-body-start)").any
      (hasStr · "var(--frame-body-open, 0pt)"))

/-- An invented deck whose frames open on beamer's trivlists, figures, a description, and trivlists
inside list items. -/
private def trivDeck : String :=
  "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n\\begin{document}\n" ++
  "\\begin{frame}[t]\n\\begin{center}\nKilo words.\n\\end{center}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{flushleft}\nKilo words.\n\\end{flushleft}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{flushright}\nKilo words.\n\\end{flushright}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{figure}\n\\includegraphics[width=60pt,height=40pt]{tall.png}\n" ++
  "\\end{figure}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{center}\n\\includegraphics[width=60pt,height=40pt]{tall.png}\n" ++
  "\\end{center}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{description}\n\\item[Kilo] words.\n\\end{description}\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]\nKilo words.\n\\begin{center}\nLima words.\n\\end{center}\n" ++
  "Mike words.\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{itemize}\n\\item Kilo words.\n\\begin{center}\nLima words.\n" ++
  "\\end{center}\nMike words.\n\\item November words.\n\\end{itemize}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{figure}\n\\includegraphics[width=60pt,height=40pt]{tall.png}\n" ++
  "\\caption{Lima words.}\n\\end{figure}\nMike words.\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{itemize}\n\\item Kilo words.\n\\begin{figure}\n" ++
  "\\includegraphics[width=60pt,height=40pt]{tall.png}\n\\end{figure}\nMike words.\n" ++
  "\\end{itemize}\n\\end{frame}\n\\end{document}\n"

/-- A frame's trivlists open and stand apart as TeX sets them, on both artifacts, at the `\topsep`
in force where they stand. -/
def trivlistOpeningChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "trivlist opening: the shipped Fira Sans parses" false
  let (doc, _) := elabStr trivDeck
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let near := withinSp (Dim.Length.ofBpMilli 500)
  let size := doc.page.fontSize
  let lists := doc.docClass.record.lists
  let lead := Ir.leadingFor size doc.page.leading
  let skip := (Ir.frameBodySkip false .top).resolve size 0
  let topsep := (Ir.trivlistSkipFor lists doc.tokens size 0).width.sp
  let lineY (page : Nat) (word : String) : Option Dim.Length :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      !l.furniture && hasStr (lineText l) word).map (·.y)
  let imageY (page : Nat) : Option Dim.Length :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.segs.any (· matches .image ..)).map (·.y)
  t "trivlist opening: a frame's trivlist spends LaTeX's top-level topsep, size10's 8pt"
    (topsep == Dim.pt 8 && (Ir.floatSpaceFor lists doc.tokens size 0).1.width.sp == topsep)
  t "trivlist opening: a center, flushleft or flushright line stands its topsep and a baselineskip below the opening, as lualatex's"
    ([0, 1, 2].all fun pg => (lineY pg "Kilo").any fun y =>
      y == skip + topsep + lead && near y (Dim.Length.ofBpMilli 25594))
  t "trivlist opening: a figure's and a center's image stand their topsep and lineskip below the opening, as lualatex's"
    ([3, 4].all fun pg => (imageY pg).any fun y =>
      y == skip + topsep + Ir.inkClearance + Dim.pt 40 && near (y - Dim.pt 40) (Dim.Length.ofBpMilli 14635))
  t "trivlist opening: a description's item stands its topsep below the opening, as lualatex's"
    ((lineY 5 "Kilo").any fun y => near y (Dim.Length.ofBpMilli 20613))
  t "trivlist opening: a center between paragraphs stands its topsep above and below, as lualatex's"
    ((lineY 6 "Kilo").any (near · (Dim.Length.ofBpMilli 17624)) && (lineY 6 "Lima").any (near · (Dim.Length.ofBpMilli 37550)) &&
     (lineY 6 "Mike").any (near · (Dim.Length.ofBpMilli 57475)))
  -- Inside a list beamer's `\@listi` has set `\topsep` again, to 3 pt.
  t "trivlist opening: a center inside a list item spends its level's topsep, as lualatex's"
    ((Ir.trivlistSkipFor lists doc.tokens size 1).width.sp == Dim.pt 3 &&
     (lineY 7 "Lima").any (near · (Dim.Length.ofBpMilli 35557)) && (lineY 7 "Mike").any (near · (Dim.Length.ofBpMilli 50501)) &&
     (lineY 7 "November").any (near · (Dim.Length.ofBpMilli 65445)))
  -- A caption sets 7 pt below its line (`\belowcaptionskip`), then the figure's topsep.
  t "trivlist opening: a captioned figure spends beamer's caption skips, as lualatex's"
    ((imageY 8).any (fun y => near (y - Dim.pt 40) (Dim.Length.ofBpMilli 14635)) &&
     (match lineY 8 "Figure", lineY 8 "Mike" with
      | some c, some m => near (m - c) (Dim.Length.ofBpMilli 26899)
      | _, _ => false))
  -- The top-level topsep is the size file's: extsizes' 6 pt under `9pt`, beamer's 11pt's 9 pt.
  t "trivlist opening: the top-level topsep is the class option's size file's"
    ((Ir.trivlistSkipFor lists {} (Dim.pt 9) 0).width.sp == Dim.pt 6 &&
     (Ir.trivlistSkipFor lists {} Ir.posterFontSize 0).width.sp == Dim.pt 9 &&
     (Ir.trivlistSkipFor lists {} (Dim.pt 10) 2).width.sp == Dim.pt 2 &&
     (Ir.trivlistSkipFor lists { entries := #[(Ir.trivlistSkipName, { width := { sp := Dim.pt 20 } })] } (Dim.pt 10) 1).width.sp
       == Dim.pt 3 &&
     (Ir.floatSpaceFor lists doc.tokens size 1).1.width.sp == Dim.pt 3 &&
     Ir.captionPosFor lists #[] .figure == .bottom)
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let blocks := artCssBlocks css
  let opens (sel : String) : Bool := (blocks.filter (·.1 == sel)).any fun (_, d) =>
    cssStageLength d "--frame-body-open" topsep doc.page.height
  t "trivlist opening html: a trivlist and a figure ride their topsep on the opening, the stage's share"
    (opens s!"section.slide > .{HtmlDoc.roleClass Ir.trivlistRole}.frame-body-start" &&
     opens "section.slide > figure.float.frame-body-start")
  let strut := blocks.filter fun (sel, _) => hasStr sel "p.frame-body-start::before"
  t "trivlist opening html: a trivlist's, a figure's and a description's first line take the strut"
    (strut.size == 1 && strut.all fun (sel, _) =>
      hasStr sel s!".{HtmlDoc.roleClass Ir.trivlistRole}.frame-body-start > p:first-child::before" &&
      hasStr sel "figure.float.frame-body-start > :is(p, figcaption):first-child::before" &&
      hasStr sel "dl.frame-body-start > dt:first-child::before" && !hasStr sel "+ dd")
  let root := (cssBlocksFor css ":root").foldl (· ++ ";" ++ ·) ""
  t "trivlist opening html: the deck declares beamer's trivlist and float spaces, the stage's share"
    (cssStageLength root "--topsep" topsep doc.page.height &&
     cssProperty root "--floatsep" == some "calc(var(--topsep) + var(--parskip, 0rem))")
  t "trivlist opening html: each list level declares its own topsep, the stage's share"
    ((cssBlocksFor css "li, dd, blockquote").any (cssStageLength · "--topsep"
        (Ir.trivlistSkipFor lists doc.tokens size 1).width.sp doc.page.height) &&
     (cssBlocksFor css ("li li, li dd, li blockquote, dd li, dd dd, dd blockquote, " ++
        "blockquote li, blockquote dd, blockquote blockquote")).any
       (cssStageLength · "--topsep" (Ir.trivlistSkipFor lists doc.tokens size 2).width.sp
         doc.page.height))
  -- The caption skips' undeclared value is the chain's innermost fallback.
  let innermost (v : String) : String :=
    ((v.splitOn ", ").getLast!.splitOn ")").head!
  t "trivlist opening html: a figure's caption skips are beamer's 7pt, the stage's share"
    ((cssBlocksFor css "figure.float").any fun d =>
      (cssProperty d "--ltx-capsep").any (fun v =>
        cssStageLength ("--c: " ++ innermost v) "--c" (Dim.pt 7) doc.page.height) &&
      (cssProperty d "--ltx-capfar").any (fun v =>
        cssStageLength ("--c: " ++ innermost v) "--c" (Dim.pt 7) doc.page.height))
  let classes := attrValuesOf (fun _ => true) "class" (Html.elem "body" body #[])
  t "trivlist opening html: every trivlist frame opens on its trivlist or its figure"
    ((classes.filter fun c => (c.splitOn " ").contains "frame-body-start" &&
      ((c.splitOn " ").contains (HtmlDoc.roleClass Ir.trivlistRole) ||
       (c.splitOn " ").contains "float")).size == 6)

/-- An alignment a standout frame discards is named once; `[standout]` and `[c,standout]` raise
none. -/
def standoutAlignNoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deckOf (opts : String) : String :=
    "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n\\begin{document}\n" ++
    s!"\\begin\{frame}[{opts}]\nKilo words.\n\\end\{frame}\n\\end\{document}\n"
  let notes (opts : String) : Array Diag := (elabStr (deckOf opts)).2.filter fun d =>
    d.kind == .N0102 && hasStr d.message "standout"
  let centred (opts : String) : Bool := (elabStr (deckOf opts)).1.body.any fun b =>
    match b with
    | .frame _ true v _ _ => (v matches .center)
    | _ => false
  t "standout alignment: an alignment before or after standout is named once, by its letter"
    ((notes "b,standout").size == 1 && (notes "b,standout").all (hasStr ·.message "'b'") &&
     (notes "standout,t").size == 1 && (notes "standout,t").all (hasStr ·.message "'t'"))
  t "standout alignment: a standout frame that loses no alignment raises no note"
    ((notes "standout").isEmpty && (notes "c,standout").isEmpty)
  t "standout alignment: every standout frame centres"
    (["b,standout", "standout,t", "standout", "c,standout"].all centred)

/-- The deck stands every frame in beamer's text area too: its text area, footline, title bar and
openings are the PDF's lengths as stage shares. -/
def htmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabStr deck
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let height := doc.page.height
  t "frame area html: the stage opens at its top edge, its text area ending on the frame's end spacer"
    ((cssBlocksFor css "section.slide:not(.title-page)").any (fun d =>
      cssProperty d "padding-top" == some "0" && cssProperty d "padding-bottom" == some "0") &&
     (cssBlocksFor css "section.slide:not(.title-page)::after").any fun d =>
      cssProperty d "flex" == some s!"{HtmlDoc.printEndGrow} 0 0" &&
      cssStageLength d "max-height" Ir.footline.sep height)
  let foot := cssBlocksFor css "section.slide > footer.slide-foot"
  t "frame area html: the footline stands after the end spacer, on the stage's edge, through no padding"
    (foot.any fun d => cssProperty d "order" == some "1" &&
      cssProperty d "margin" == some "0 calc(-1 * var(--safearea, 6vmin))" &&
      cssProperty d "line-height" == some "0")
  t "frame area html: on paper a frame's end never opens a sheet, its footline kept with its content"
    ((cssBlocksFor css "section.slide > :is(.fill, footer.slide-foot), section.slide::after").any
      (cssProperty · "break-before" == some "avoid"))
  t "frame area html: on screen the footline stays on the stage's edge when content overruns it"
    (hasStr css "@media screen { section.slide > footer.slide-foot { position: sticky; bottom: 0; } }")
  -- A value holding the stage's share of the closing skip (`Ir.footline.raise`).
  let raised (v : String) : Bool :=
    (v.splitOn " ").any fun tok =>
      cssStageLength s!"x: {(tok.replace ")" "").replace "(" ""}" "x" Ir.footline.raise height
  t "frame area html: the footline's box is the band's glyph height and depth and its closing skip"
    ((cssBlocksFor css "footer.slide-foot::before").any fun d =>
      (cssProperty d "height").any fun h => raised h &&
        hasStr h "var(--foot-h, var(--foot-cap, 1) * 1cap)" && hasStr h "var(--foot-d, 0px)")
  t "frame area html: each slot's baseline stands the band's depth and the closing skip above the edge"
    ((cssBlocksFor css "footer.slide-foot > :is(.band-left, .band-right)::before").any fun d =>
      (cssProperty d "vertical-align").any fun v => raised v && hasStr v "var(--foot-d, 0px)")
  t "frame area html: the slots stand inset from the paper's sides, as moloch's footline"
    ((cssBlocksFor css "footer.slide-foot > .band-left").any (cssStageLength · "left" Ir.footline.left height) &&
     (cssBlocksFor css "footer.slide-foot > .band-right").any (cssStageLength · "right" Ir.footline.right height))
  t "frame area html: the frame-title bar is moloch's strut box"
    ((cssBlocksFor css "section.slide > header h2::before").any (hasStr · "height: calc(var(--frametitlepadding") &&
     (cssBlocksFor css "section.slide > header h2::after").any (hasStr · "vertical-align: calc(-1 * var(--frametitlepadding"))
  -- The standout type is the frame's (`\usebeamerfont{standout}`); the footline undoes that step.
  let standoutSize := (cssBlocksFor css "section.slide.standout").findSome? (cssProperty · "font-size")
  let footStep := (cssBlocksFor css s!".size-{Ir.footline.step}").findSome? (cssProperty · "font-size")
  t "frame area html: a standout frame's type is the whole frame's, its footline keeping its own"
    ((cssBlocksFor css "section.slide.standout").any (cssProperty · "font-weight" == some "600") &&
     (cssBlocksFor css "section.slide.standout > p").isEmpty &&
     match standoutSize, footStep with
     | some s, some f =>
       (cssBlocksFor css "section.slide.standout > footer.slide-foot").any
         (cssProperty · "font-size" == some s!"calc({f} / {s.dropEnd 2})")
     | _, _ => false)
  let sections := elemAttrsList (· == "section") #[] body.toList
  let slides := sections.filter fun (_, attrs) =>
    ((attrs.find? (·.1 == "class")).map (·.2.splitOn " " |>.contains "slide")).getD false
  t "frame area html: every frame opens its body as beamer's content box"
    (slides.size == 6 && slides.all fun (_, attrs) =>
      ((attrs.find? (·.1 == "style")).map (hasStr ·.2 "--frame-body-skip")).getD false)
  -- The strut's em is the page's own at the section page's body, less the bar above it.
  let size := doc.page.fontSize
  let pdfStrut := Ir.sectionPageStrut doc.page.scale size doc.page.leading
  t "frame area html: a section page closes on its subsection strut below its bar"
    ((cssBlocksFor css "section.section-page::after").any fun d =>
      ((cssProperty d "height").bind fun h =>
        if hasStr h "em - var(--progressheight" then
          cssEmMilli (((h.drop 5).takeWhile (· != ' ')).toString) else none).any fun m =>
        size * m / (1000 : Int) - 4 * Dim.Length.quantum ≤ pdfStrut &&
          pdfStrut ≤ size * m / (1000 : Int))
  let feet := elemAttrsList (· == "footer") #[] body.toList
  t "frame area html: a restored scriptsize note sizes its footline's box"
    (feet.any fun (_, attrs) =>
      ((attrs.find? (·.1 == "style")).map (hasStr ·.2 "--foot-cap: 1.400;")).getD false)
  let (bdoc, _) := elabStr barlessDeck
  let (bhead, _, _) := HtmlDoc.emitTree {} bdoc
  let bcss := treeCssList "" bhead.toList
  t "frame area html: with no title bar the title opens at the slides' top margin, as the PDF sets it"
    ((cssBlocksFor bcss "section.slide:not(.title-page) > header").any fun d =>
      cssStageLength d "padding-top" bdoc.page.vmargin bdoc.page.height)
where
  /-- A deck with no title bar: one titled frame. -/
  barlessDeck : String :=
    "\\documentclass[10pt]{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n\\end{document}\n"

mutual

/-- Every `want` element's ancestor path, root first, as the selector judge
reads elements (`ArtElem`: tag and classes). -/
private def tagPathsOne (want : String) (path : Array ArtElem) (acc : Array (Array ArtElem)) :
    Html.Node → Array (Array ArtElem)
  | .elem tag attrs kids =>
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    let here := path.push (tag, ((cls.splitOn " ").filter (!·.isEmpty)).toArray)
    tagPathsList want here (if tag == want then acc.push here else acc) kids.toList
  | .text _ | .style _ | .script .. => acc

private def tagPathsList (want : String) (path : Array ArtElem) (acc : Array (Array ArtElem)) :
    List Html.Node → Array (Array ArtElem)
  | [] => acc
  | k :: rest => tagPathsList want path (tagPathsOne want path acc k) rest

end

/-- The winning declaration of `key` on the last element of `path` among
the rules whose selector this judge reads (`artSelChain`), the later of two
at one specificity; a pseudo-element's rule styles no element. -/
private def declaredOn (css key : String) (path : Array ArtElem) : Option String := Id.run do
  let mut best : Option ((Nat × Nat) × String) := none
  for (sel, decls) in artCssBlocks css do
    if let some v := cssProperty decls key then
      for part in cssSelectorParts sel do
        if !hasStr part "::" then
          if let some chain := artSelChain part then
            if artChainMatchesPath chain path then
              let s := (chain.foldl (fun n st => n + st.1.2.size) 0,
                chain.foldl (fun n st => n + (if st.1.1.isEmpty then 0 else 1)) 0)
              let wins := match best with
                | some (b, _) => b.1 < s.1 || (b.1 == s.1 && b.2 ≤ s.2)
                | none => true
              if wins then best := some (s, v)
  return best.map (·.2)

/-- What an inherited property computes to on the first element of `up`
(the path read leaf first): its own winning declaration, else its
parent's. -/
private def inheritedOn (css key : String) : List ArtElem → Option String
  | [] => none
  | e :: up => (declaredOn css key (e :: up).reverse.toArray).orElse fun _ => inheritedOn css key up

/-- An inherited property's value with a `var(--x, fallback)` resolved on the
same path, the custom property inheriting too. -/
private def computedOn (css key : String) (path : Array ArtElem) : Option String :=
  let up := path.toList.reverse
  (inheritedOn css key up).map fun v =>
    if v.startsWith "var(--" && v.endsWith ")" then
      match ((v.drop 4).dropEnd 1).toString.splitOn "," with
      | name :: rest =>
        (inheritedOn css name.trimAscii.toString up).getD (",".intercalate rest).trimAscii.toString
      | [] => v
    else v

/-- A figure inside a list item reads its own level's float space in the web deck, as each level
declares `--floatsep` beside its `--topsep`. -/
def floatLevelChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabStr trivDeck
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let level := (Ir.trivlistSkipFor doc.docClass.record.lists doc.tokens doc.page.fontSize 1).width.sp
  let figs := (tagPathsList "figure" artBodyPath #[] body.toList).filter (·.any (·.1 == "li"))
  let owner (path : Array ArtElem) : Option (Array ArtElem) :=
    ((List.range path.size).reverse.map (fun k => path.extract 0 (k + 1))).find? fun pre =>
      (declaredOn css "--floatsep" pre).isSome
  t "float level: a figure in a list item reads the float space its item declares beside its own topsep"
    (!figs.isEmpty && figs.all fun p => match owner p with
      | some o =>
        o.back?.any (·.1 == "li") &&
        declaredOn css "--floatsep" o == some "calc(var(--topsep) + var(--parskip, 0rem))" &&
        (declaredOn css "--topsep" o).any fun v =>
          cssStageLength ("--c: " ++ v) "--c" level doc.page.height
      | none => false)
  let (ddoc, dds) := elabStr ("\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n" ++
    "\\setlength{\\topsep}{20pt}\n\\begin{document}\n\\begin{frame}[t]\n" ++
    "\\begin{center}\nKilo words.\n\\end{center}\n\\end{frame}\n\\end{document}\n")
  let (dhead, _, _) := HtmlDoc.emitTree {} ddoc
  let roots := cssBlocksFor (treeCssList "" dhead.toList) ":root"
  t "float level: a declared topsep reaches the deck as the stage's share and is noted as the top level's"
    ((roots.any fun d => cssStageLength d "--topsep" (Dim.pt 20) ddoc.page.height) &&
     !(roots.any fun d => (cssProperty d "--topsep").any (·.endsWith "pt")) &&
     dds.any fun d => hasStr (saidText d) "which a trivlist outside a list reads")

/-- A Light family's set: the shipped Fira Sans's outlines as a 300 in the
regular slot and as a 400 in the bold one, the shape of a deck that sets a
Light family with its Regular for bold. -/
private def lightSet (f : Font) : Font.FontSet :=
  { fonts := #[{ f with weight := 300 }, f]
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 1),
       ((slot, 400, true), 0), ((slot, 700, true), 1)]).toArray }

/-- Every footline sets at the body's weight, standout frames included. -/
def footWeightChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some f ← shippedFiraFont | t "footline weight: the shipped Fira Sans parses" false
  let (doc, _) := elabStr deck
  let (head, body, _) := HtmlDoc.emitTree { fonts := some (lightSet f) } doc
  let css := treeCssList "" head.toList
  let feet := tagPathsList "footer" artBodyPath #[] body.toList
  let weights (css : String) := feet.map (computedOn css "font-weight")
  t "footline weight: the body resolves the regular face's 300"
    (computedOn css "font-weight" artBodyPath == some "300")
  t "footline weight: every footline computes to the body's weight, standout frames' too"
    (2 ≤ feet.size && (weights css).all (· == some "300") &&
      feet.any fun p => p.any (·.2.contains "standout"))
  t "footline weight: a standout frame's own type keeps its weight"
    (feet.any fun p => p.any (·.2.contains "standout") &&
      computedOn css "font-weight" (p.pop) == some "600")
  t "footline weight: the judge sees a footer rule naming the keyword"
    ((weights (css ++ "section.slide > footer.slide-foot { font-weight: normal; }\n")).all
      (· == some "normal"))

/-- A moloch deck whose footer note has glyphs that descend: one frame,
invented words. -/
private def noteDeck : String :=
  "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n" ++
  "\\newenvironment{framefooter}[1]{%\n" ++
  "  \\setbeamertemplate{frame footer}{{\\scriptsize #1}}%\n" ++
  "}{\\setbeamertemplate{frame footer}{}}\n" ++
  "\\begin{document}\n\\begin{framefooter}{Quay jog}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\end{framefooter}\n\\end{document}\n"

/-- The web footline is the page's band box: a frame's footer declares its band's glyph height and
depth as stage shares. -/
def footBoxChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "footline box: the shipped Fira Sans parses" false
  let (doc, _) := elabStr noteDeck
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fira doc geom
  let feet := ((out.pages[0]?.map (·.lines)).getD #[]).filter (·.furniture)
  let (h, d) := feet.foldl (fun (acc : Dim.Length × Dim.Length) l =>
    let (lh, ld) := Layout.segsInk fira l.segs
    (max acc.1 lh, max acc.2 ld)) (0, 0)
  let (_, body, _) := HtmlDoc.emitTree
    { footBox := fun n band => some (Layout.footBandBox geom fira {} n band) } doc
  let styles := (elemAttrsList (· == "footer") #[] body.toList).filterMap fun (_, attrs) =>
    (attrs.find? (·.1 == "style")).map (·.2)
  t "footline box: the shipped page's footline descends"
    (feet.size == 2 && 0 < d)
  t "footline box: the web footline declares the shipped page's band box"
    (styles.size == 1 && styles.all fun st =>
      cssStageLength st "--foot-h" h doc.page.height &&
      cssStageLength st "--foot-d" d doc.page.height)

/-- An invented moloch deck whose frames carry footnotes — a titled centred
frame, an untitled one, a top-aligned one with two notes — and the titled
frame again with no note, to read the note's own lift against. -/
private def noteFrames : String :=
  "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n\\begin{document}\n" ++
  "\\begin{frame}{Alpha words}\nKilo lima mike\\footnote{Oscar papa quebec.} november.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}\nKilo lima mike\\footnote{Romeo sierra tango.} november.\n\\end{frame}\n" ++
  "\\begin{frame}[t]{Bravo words}\nKilo lima mike\\footnote{Uniform victor.}" ++
  "\\footnote{Whiskey yankee.} november.\n\\end{frame}\n" ++
  "\\begin{frame}{Charlie words}\nKilo lima mike november.\n\\end{frame}\n\\end{document}\n"

/-- A frame's footnotes stand in its text area as beamer sets them, held to lualatex within 0.5 bp. -/
def frameNoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "frame notes: the shipped Fira Sans parses" false
  let (doc, _) := elabStr noteFrames
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let near := withinSp (Dim.Length.ofBpMilli 500)
  let ys (page : Nat) (note : Bool) : List Dim.Length :=
    ((out.pages[page]?.map fun p => (p.lines.filter fun l =>
      l.note == note && !l.furniture &&
        (if note then !(lineText l).isEmpty else hasStr (lineText l) "Kilo")).map (·.y)).getD #[]).toList
  let at? (got : List Dim.Length) (milli : List Int) : Bool :=
    got.length == milli.length && (got.zip milli).all fun (a, m) => near a (Dim.Length.ofBpMilli m)
  t "frame notes: a frame's notes stand their last baseline on the text area's floor, as lualatex does"
    (at? (ys 0 true) [260820] && at? (ys 1 true) [260770] && at? (ys 2 true) [251000, 260710])
  t "frame notes: an untitled frame centres above its note, as lualatex does"
    (at? (ys 1 false) [132870])
  t "frame notes: a note lifts its titled frame's body by half its box, as lualatex does"
    (match ys 0 false, ys 3 false with
     | [a], [b] => near (a - b) (Dim.Length.ofBpMilli (-3390))
     | _, _ => false)

end Tests.FrameArea
