module

public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FrameArea

/-- A CSS length in `em` as thousandths of the em, where the value is one. -/
private def emMilli (v : String) : Option Int := do
  guard (v.endsWith "em")
  let (m, sc) ← Decl.parseDecimal (v.dropEnd 2).toString
  return m * 1000 / (sc : Int)

/-- The invented moloch deck the checks lay out, the one source each value
below was first measured on under lualatex (beamer 10 pt, 4:3, the shipped
Fira Sans for every face): a standout frame, a standout frame whose note the
deck's footline hook restores, a titled control, a standout frame that also
names `b`, a section page, and a bottom-aligned frame. The footline hook is
the one a moloch deck spells to restore an explicit note on a standout
frame. -/
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

/-- A templated title page — its title and author set as nodes, which the
engine places as title slots — with a section page on its heels, a frame,
and a second section page of the same title: invented words. -/
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

/-- **Every frame stands its content box in beamer's text area**
(`Layout.FrameArea`, `Layout.frameFloor_exact`). beamer's `\textheight` is
the paper less `\footheight` — the footline's box plus 4 pt, the 4 pt alone
where the footline is empty — and a frame's content opens at its top on
`\vskip-\parskip\vbox{}`; a plain frame, as moloch's section page is,
centres on the whole paper with its first box flush on that `\vbox{}`.
Asserted over `Layout.Out` against lualatex's measurements of `deck` (TeX
Live 2026; bp from the page top to the baseline): a standout frame's line
at 142.951 — whatever alignment its options name besides, as moloch's key
centres it — the same frame with its note restored at 138.197 (the note's
own baseline at 268.057), the section page's title at 127.894, on a
templated title page's heels (`slottedDeck`) as after a frame, and a
bottom-aligned frame's line at 260.59, its content ending exactly on the
text area's floor, the footline's box and 4 pt above the paper's edge. The
lines are held to
0.5 bp: what remains is the standout size's leading, 17.28 pt on the
engine's ladder against size10.clo's 18 pt, half of it after centring
(0.36 bp). At `fa516a82` the standout frame stood 2.06 bp high, the
restored note sent its line 9.12 bp low — the page took the note's band off
a floor still at the slides margin, the paper's top still 26.4 bp above its
content — and the section page stood 9.99 bp low; with the area alone, the
section page after the title page stood 14.3 bp low, the title page's slots
leaving the page fresh for the next page's opening. At `5e6eedf5` a standout
frame naming `b` stood on the floor, 125 bp below where lualatex centres it.
Invented words. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "frame area: the shipped Fira Sans parses" false
  let (doc, _) := elabStr deck
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let near := withinSp (ptMilli 500)
  let line (out : Layout.Out) (page : Nat) (word : String) (furniture : Bool := false) :
      Option Layout.LineOut :=
    out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.furniture == furniture && hasStr (lineText l) word
  let at? (page : Nat) (word : String) (milli : Int) (furniture : Bool := false) : Bool :=
    ((line out page word furniture).map fun l => near l.y (ptMilli milli)).getD false
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
  -- A title page's slots each set as from its page's top; the next page,
  -- a section page here, still opens as every section page does (lualatex
  -- sets both of `slottedDeck`'s at 127.894).
  let (sdoc, _) := elabStr slottedDeck
  let sout := layoutOf fira sdoc (Layout.Geom.ofPage sdoc.page)
  let sectionY (page : Nat) : Option Dim.Sp :=
    sout.pages[page]?.bind fun p =>
      (p.lines.find? fun l => hasStr (lineText l) "Hotel").map (·.y)
  t "frame area: a section page on a title page's heels opens as every section page does"
    (match sectionY 1, sectionY 3 with
     | some a, some b => a == b && near a (ptMilli 127894)
     | _, _ => false)
  -- The floor itself, exactly: a bottom-aligned frame's content ends on
  -- it, the glyphs' depth below its last baseline (`B.contentEnd`), the
  -- footline's box and 4 pt above the paper's edge (`Layout.frameFloor`).
  let geom := Layout.Geom.ofPage doc.page
  let band := ((out.pages[6]?.map (·.lines)).getD #[]).filter (·.furniture)
  let box := band.foldl (fun (acc : Dim.Sp × Dim.Sp) l =>
    let (h, d) := Layout.segsInk fira l.segs
    (max acc.1 h, max acc.2 d)) (0, 0)
  t "frame area: a bottom-aligned frame's content ends on its text area's floor"
    (!band.isEmpty && ((line out 6 "Kilo").map fun l =>
      l.y + (Layout.segsInk fira l.segs).2 ==
        Layout.frameFloor geom.pageH Ir.footline.sep (some box)).getD false)

/-- The deck the class option `t` declares — `opt` the class options'
tail, `frame` every unaligned frame's option list — with a frame that names
`c` and a standout frame. Invented words. -/
private def classDeck (opt frame : String) : String :=
  s!"\\documentclass[10pt{opt}]\{beamer}\n\\usetheme\{moloch}\n\\begin\{document}\n" ++
  s!"\\begin\{frame}{frame}\{Foxtrot}\nAlpha words.\n\\end\{frame}\n" ++
  s!"\\begin\{frame}{frame}\nKilo words.\n\\end\{frame}\n" ++
  "\\begin{frame}[c]{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\begin{frame}[standout]\nKilo words.\n\\end{frame}\n\\end{document}\n"

/-- **The class options' `t` aligns every frame that names no alignment as
`[t]` does** (`Elab.Ctx.frameAlign`; beamer.cls's `\ExecuteOptionsBeamer{c}`,
then the document's options, the last winning): two builds apart — the
deck under `t` with bare frames, and the deck with no class option whose
frames each name `[t]` — the page and the web page are the same, a frame
naming `c` still centres and a standout frame still centres. Against
lualatex on the `t` deck (4:3, the shipped Fira Sans for every face): the
untitled frame's line at 17.62 bp, the standout's at 142.95. At
`5e6eedf5` the option was dropped unnamed and every bare frame centred, the
untitled one's line 118.7 bp low. Invented words. -/
def classAlignChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "class t: the shipped Fira Sans parses" false
  let (tdoc, tds) := elabStr (classDeck ",t" "")
  let (edoc, eds) := elabStr (classDeck "" "[t]")
  let ys (doc : Ir.Doc) : Array (Array Dim.Sp) :=
    (layoutOf fira doc (Layout.Geom.ofPage doc.page)).pages.map (·.lines.map (·.y))
  t "class t: the deck sets every bare frame as an explicit [t] sets it"
    (ys tdoc == ys edoc && (HtmlDoc.emit {} tdoc).1 == (HtmlDoc.emit {} edoc).1 &&
      tds.size == eds.size)
  let near := withinSp (ptMilli 500)
  let out := layoutOf fira tdoc (Layout.Geom.ofPage tdoc.page)
  let at? (page : Nat) (word : String) (milli : Int) : Bool :=
    ((out.pages[page]?.bind fun p => p.lines.find? fun l =>
      !l.furniture && hasStr (lineText l) word).map fun l => near l.y (ptMilli milli)).getD false
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

/-- **A frame's content opens as TeX opens it below its `\vbox{}`, on both
artifacts** (`HtmlDoc.frameOpeningCss`): the first line's baseline one
`\baselineskip` of its paragraph below the opening — `Ir.leadingFor`, which
the page's opening rule spends and the web's first-line strut is, at an em
of the line — and a list opening the content first its `\@topsepadd`
lower, the length the web's list rides on the opening (`--frame-body-open`,
the stage's share). Asserted over `Layout.Out` against lualatex on
`openDeck` (4:3, the shipped Fira Sans for every face): the paragraph's
line at 17.62 bp, the itemize's and the enumerate's first items at 20.61,
the tall image's bottom at 46.52 and the short one's at 17.62;
and over the stylesheet the deck ships, each web length the PDF's own. At
`5e6eedf5` the web set a frame's first line on its screen line box, the
half-leading and the face's ascent below the opening (1.37 bp above
lualatex's), and dropped an opening list's `\topsep`: an opening list's
first item stood 4.36 bp above lualatex's; and the page stood an opening image flush on the opening, a
short one 4 pt above lualatex's, a tall one the 1 pt of `\lineskip`. The
trim reaches a paragraph's, a list's and an alignment scope's last line,
never a box that paints or scrolls: a trimmed listing hid the last of its
lines (the browser oracle's `code-height`). Invented words. -/
def openingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "frame opening: the shipped Fira Sans parses" false
  let (doc, _) := elabStr openDeck
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let first (page : Nat) : Option Dim.Sp :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      !l.furniture && hasStr (lineText l) "Kilo").map (·.y)
  let near := withinSp (ptMilli 500)
  let size := doc.page.fontSize
  let lead := Ir.leadingFor size doc.page.leading
  let skip := (Ir.frameBodySkip false .top).resolve size 0
  t "frame opening: a paragraph's first baseline stands one baselineskip below the opening, as lualatex's"
    ((first 0).any fun y => y == skip + lead && near y (ptMilli 17620))
  let listOpen : Option Dim.Sp := (Ir.listSkips doc.docClass.record.lists size 1).map fun sk =>
    sk.topsep.width.sp + (Ir.partopsepFor doc.docClass.record.lists size 1 doc.tokens).width.sp
  t "frame opening: a list's first item stands its topsepadd lower, as lualatex's"
    (match first 1, first 2, listOpen with
     | some a, some b, some o => a == skip + o + lead && b == a && near a (ptMilli 20610)
     | _, _, _ => false)
  -- An image's box takes TeX's interline glue at its paragraph's
  -- `\baselineskip`: a short one stands its bottom one skip below the
  -- opening, a tall one `\lineskip` below its own height.
  let imageY (page : Nat) : Option Dim.Sp :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.segs.any (· matches .image ..)).map (·.y)
  t "frame opening: an image stands TeX's interline glue below the opening, as lualatex's"
    ((imageY 3).any (fun y => y == skip + Layout.inkClearance + Dim.pt 40 && near y (ptMilli 46517)) &&
     (imageY 4).any (fun y => y == skip + lead && near y (ptMilli 17624)))
  let (head, _, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let blocks := artCssBlocks css
  let strut := blocks.filter fun (sel, _) => hasStr sel "p.frame-body-start::before"
  t "frame opening html: the first line's strut is the page's baselineskip at an em of the line"
    (strut.size == 1 && strut.all fun (sel, d) =>
      hasStr sel "li:first-child" &&
      ((cssDeclOf d "height").bind emMilli).any (· * size / 1000 == lead))
  -- The content ends where its last line's glyphs end: every frame's last
  -- element is marked, and its last line trims to its baseline.
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let classes := attrValuesOf (fun _ => true) "class" (Html.elem "body" body #[])
  let trims := blocks.filter fun (sel, d) =>
    hasStr sel ".frame-body-end" && cssDeclOf d "text-box" == some "trim-end text alphabetic"
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

/-- An invented deck whose frames open on beamer's trivlists: `[t]`
untitled, a `{center}`, a `{flushleft}` and a `{flushright}` on a line, a
`{figure}` and a `{center}` on an image taller than the body's
`\baselineskip`, a `{description}`, a `{center}` between two paragraphs,
a `{center}` inside a list item, a captioned `{figure}`, and a `{figure}`
inside a list item. -/
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

/-- **A frame's trivlists open and stand apart as TeX sets them, on both
artifacts**: a `{center}`, `{flushleft}` or `{flushright}` — and beamer's
`{figure}`, which is a `{center}` (beamerbaselocalstructure.sty:550-553) —
spends the `\topsep` in force where it stands (`Ir.trivlistSkipFor`):
outside a list the class option's size file's (size10.clo's `8pt plus 2pt
minus 4pt`, which beamer leaves in force there; extsizes' 6 pt under `9pt`;
beamer's own 11pt's 9 pt under a poster's scaled body), inside one the
`\topsep` beamer's `\@listi` sets again (3 pt, then 2 pt), which a preamble
declaration does not survive; its first line stands one `\baselineskip`
below the opening, an image `\lineskip` below its own height; a caption
spends beamer's 7 pt `\abovecaptionskip` and `\belowcaptionskip`. Over
`Layout.Out` against lualatex on `trivDeck` (4:3, the shipped Fira Sans for
every face): the three lines at 25.59 bp, both images' tops at 14.64, the
description's item at 20.61, the paragraphs around the `{center}` at 17.62,
37.55 and 57.48, the `{center}` in an item at 35.56 with its item's next
line at 50.50 and the next item at 65.45, and the captioned figure's next
line 26.90 below its caption; over the stylesheet the deck ships, the
opening space of a trivlist and of a figure, the root's and each list
level's `--topsep` and the caption skips are the stage's shares of the
page's, and their first lines and a description's label take the
first-line strut. Before the first fix the page spent the rhythm's 6 pt
quantum for the `\topsep` and a float's text gap for a figure — the lines
1.93 bp high and the figure's image 4.03 bp low — and the web deck dropped
the trivlist's opening space and its strut: the lines 9.35 bp high, both
images 8.97. Before the second, a `{center}` in an item spent the top
level's 8 pt (its line 5.11 bp low, its item's next line 10.17), and the
captioned figure's next line stood 6.90 bp short of its caption. Invented
words. -/
def trivlistOpeningChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "trivlist opening: the shipped Fira Sans parses" false
  let (doc, _) := elabStr trivDeck
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let near := withinSp (ptMilli 500)
  let size := doc.page.fontSize
  let lists := doc.docClass.record.lists
  let lead := Ir.leadingFor size doc.page.leading
  let skip := (Ir.frameBodySkip false .top).resolve size 0
  let topsep := (Ir.trivlistSkipFor lists doc.tokens size 0).width.sp
  let lineY (page : Nat) (word : String) : Option Dim.Sp :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      !l.furniture && hasStr (lineText l) word).map (·.y)
  let imageY (page : Nat) : Option Dim.Sp :=
    (out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.segs.any (· matches .image ..)).map (·.y)
  t "trivlist opening: a frame's trivlist spends LaTeX's top-level topsep, size10's 8pt"
    (topsep == Dim.pt 8 && (Ir.floatSpaceFor lists doc.tokens size 0).1.width.sp == topsep)
  t "trivlist opening: a center, flushleft or flushright line stands its topsep and a baselineskip below the opening, as lualatex's"
    ([0, 1, 2].all fun pg => (lineY pg "Kilo").any fun y =>
      y == skip + topsep + lead && near y (ptMilli 25594))
  t "trivlist opening: a figure's and a center's image stand their topsep and lineskip below the opening, as lualatex's"
    ([3, 4].all fun pg => (imageY pg).any fun y =>
      y == skip + topsep + Layout.inkClearance + Dim.pt 40 && near (y - Dim.pt 40) (ptMilli 14635))
  t "trivlist opening: a description's item stands its topsep below the opening, as lualatex's"
    ((lineY 5 "Kilo").any fun y => near y (ptMilli 20613))
  t "trivlist opening: a center between paragraphs stands its topsep above and below, as lualatex's"
    ((lineY 6 "Kilo").any (near · (ptMilli 17624)) && (lineY 6 "Lima").any (near · (ptMilli 37550)) &&
     (lineY 6 "Mike").any (near · (ptMilli 57475)))
  -- Inside a list beamer's `\@listi` has set `\topsep` again, to 3 pt.
  t "trivlist opening: a center inside a list item spends its level's topsep, as lualatex's"
    ((Ir.trivlistSkipFor lists doc.tokens size 1).width.sp == Dim.pt 3 &&
     (lineY 7 "Lima").any (near · (ptMilli 35557)) && (lineY 7 "Mike").any (near · (ptMilli 50501)) &&
     (lineY 7 "November").any (near · (ptMilli 65445)))
  -- A caption sets 7 pt below its own line (`\belowcaptionskip`), the
  -- figure's topsep after that, as beamer's caption does.
  t "trivlist opening: a captioned figure spends beamer's caption skips, as lualatex's"
    ((imageY 8).any (fun y => near (y - Dim.pt 40) (ptMilli 14635)) &&
     (match lineY 8 "Figure", lineY 8 "Mike" with
      | some c, some m => near (m - c) (ptMilli 26899)
      | _, _ => false))
  -- The top-level topsep is the class option's size file's: extsizes'
  -- 6 pt under `9pt`, and beamer's own 11pt's 9 pt under a poster's body.
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
     cssDeclOf root "--floatsep" == some "calc(var(--topsep) + var(--parskip, 0rem))")
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
      (cssDeclOf d "--ltx-capsep").any (fun v =>
        cssStageLength ("--c: " ++ innermost v) "--c" (Dim.pt 7) doc.page.height) &&
      (cssDeclOf d "--ltx-capfar").any (fun v =>
        cssStageLength ("--c: " ++ innermost v) "--c" (Dim.pt 7) doc.page.height))
  let classes := attrValuesOf (fun _ => true) "class" (Html.elem "body" body #[])
  t "trivlist opening html: every trivlist frame opens on its trivlist or its figure"
    ((classes.filter fun c => (c.splitOn " ").contains "frame-body-start" &&
      ((c.splitOn " ").contains (HtmlDoc.roleClass Ir.trivlistRole) ||
       (c.splitOn " ").contains "float")).size == 6)

/-- **An alignment a standout frame discards is named** (`Elab.frameOpts`):
moloch's `standout` key opens with `\setkeys{beamerframe}{c}`, so `b` before
it is overridden and `t` after it is an undefined key lualatex steps over;
either way the frame centres, and here one note names the alignment it
lost. `[standout]` and `[c,standout]`, which lose nothing, raise none. At
`7600baa5` the alignment was dropped unnamed. Invented words. -/
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

/-- **The deck stands every frame in beamer's text area too**, the PDF's
(`checks`): the stage opens at its top edge and its text area ends
`\footheight` above its bottom edge — the 4 pt gap the frame's end spacer,
the grow-only spacer a printed frame ends on (`HtmlDoc.printEndGrow`), and
the footline after it, on the stage's bottom edge, reaching into no padding
(`HtmlDoc.footlineCss`), and on paper kept with the frame's last content;
its slots' baseline its closing skip above that
edge, inset as moloch insets them, its box as tall as its tallest slot's cap
height; the frame-title bar is moloch's strut box, and with no bar the title
opens at the slides' top margin, where the PDF sets it; an untitled or
standout frame opens its body as the PDF does; a section page closes on its
subsection strut; and a standout frame's type is the whole frame's while its
footline keeps its own step. Asserted over the typed tree and the
stylesheet it ships, on `deck` and `barlessDeck`: lengths are the stage's
shares of the PDF's own (`cssStageLength`, one printed milli-percent). At
`fa516a82` the stage kept the 6vmin safe area above and below every frame,
the footline stood that safe area and a 1.45 rem margin up with its slots at
the safe area's edge, the bar was padded below its line box, untitled and
standout frames paid a paragraph gap at their top, and a standout note set
at 1.44 times its size in bold. At `0232749b` the footline reached the edge
by a negative margin through the stage's padding, which sent it to a sheet
of its own on paper, a bar-less title stood on the stage's top edge, and a
standout frame's lists set at the body's size. Invented words. -/
def htmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabStr deck
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let height := doc.page.height
  t "frame area html: the stage opens at its top edge, its text area ending on the frame's end spacer"
    ((cssBlocksFor css "section.slide:not(.title-page)").any (fun d =>
      cssDeclOf d "padding-top" == some "0" && cssDeclOf d "padding-bottom" == some "0") &&
     (cssBlocksFor css "section.slide:not(.title-page)::after").any fun d =>
      cssDeclOf d "flex" == some s!"{HtmlDoc.printEndGrow} 0 0" &&
      cssStageLength d "max-height" Ir.footline.sep height)
  let foot := cssBlocksFor css "section.slide > footer.slide-foot"
  t "frame area html: the footline stands after the end spacer, on the stage's edge, through no padding"
    (foot.any fun d => cssDeclOf d "order" == some "1" &&
      cssDeclOf d "margin" == some "0 calc(-1 * var(--safearea, 6vmin))" &&
      cssDeclOf d "line-height" == some "0")
  t "frame area html: on paper a frame's end never opens a sheet, its footline kept with its content"
    ((cssBlocksFor css "section.slide > :is(.fill, footer.slide-foot), section.slide::after").any
      (cssDeclOf · "break-before" == some "avoid"))
  t "frame area html: on screen the footline stays on the stage's edge when content overruns it"
    (hasStr css "@media screen { section.slide > footer.slide-foot { position: sticky; bottom: 0; } }")
  -- A value holding the stage's share of the closing skip (`Ir.footline.raise`).
  let raised (v : String) : Bool :=
    (v.splitOn " ").any fun tok =>
      cssStageLength s!"x: {(tok.replace ")" "").replace "(" ""}" "x" Ir.footline.raise height
  t "frame area html: the footline's box is the band's glyph height and depth and its closing skip"
    ((cssBlocksFor css "footer.slide-foot::before").any fun d =>
      (cssDeclOf d "height").any fun h => raised h &&
        hasStr h "var(--foot-h, var(--foot-cap, 1) * 1cap)" && hasStr h "var(--foot-d, 0px)")
  t "frame area html: each slot's baseline stands the band's depth and the closing skip above the edge"
    ((cssBlocksFor css "footer.slide-foot > :is(.band-left, .band-right)::before").any fun d =>
      (cssDeclOf d "vertical-align").any fun v => raised v && hasStr v "var(--foot-d, 0px)")
  t "frame area html: the slots stand inset from the paper's sides, as moloch's footline"
    ((cssBlocksFor css "footer.slide-foot > .band-left").any (cssStageLength · "left" Ir.footline.left height) &&
     (cssBlocksFor css "footer.slide-foot > .band-right").any (cssStageLength · "right" Ir.footline.right height))
  t "frame area html: the frame-title bar is moloch's strut box"
    ((cssBlocksFor css "section.slide > header h2::before").any (hasStr · "height: calc(var(--frametitlepadding") &&
     (cssBlocksFor css "section.slide > header h2::after").any (hasStr · "vertical-align: calc(-1 * var(--frametitlepadding"))
  -- The standout type is the frame's, moloch's `\usebeamerfont{standout}`;
  -- the footline undoes that step for its own (its weight: `footWeightChecks`).
  let standoutSize := (cssBlocksFor css "section.slide.standout").findSome? (cssDeclOf · "font-size")
  let footStep := (cssBlocksFor css s!".size-{Ir.footline.step}").findSome? (cssDeclOf · "font-size")
  t "frame area html: a standout frame's type is the whole frame's, its footline keeping its own"
    ((cssBlocksFor css "section.slide.standout").any (cssDeclOf · "font-weight" == some "600") &&
     (cssBlocksFor css "section.slide.standout > p").isEmpty &&
     match standoutSize, footStep with
     | some s, some f =>
       (cssBlocksFor css "section.slide.standout > footer.slide-foot").any
         (cssDeclOf · "font-size" == some s!"calc({f} / {s.dropEnd 2})")
     | _, _ => false)
  -- The frames' own attributes: every frame of the deck opens its body
  -- (`frame-body-start`), the untitled ones with no fixed skip of their own.
  let sections := elemAttrsList (· == "section") #[] body.toList
  let slides := sections.filter fun (_, attrs) =>
    ((attrs.find? (·.1 == "class")).map (·.2.splitOn " " |>.contains "slide")).getD false
  t "frame area html: every frame opens its body as beamer's content box"
    (slides.size == 6 && slides.all fun (_, attrs) =>
      ((attrs.find? (·.1 == "style")).map (hasStr ·.2 "--frame-body-skip")).getD false)
  -- The strut's em is the page's own strut at the section page's body
  -- (`Ir.sectionPageStrut_between`), less the bar it stands under.
  let size := doc.page.fontSize
  let pdfStrut := Ir.sectionPageStrut size doc.page.leading
  t "frame area html: a section page closes on its subsection strut below its bar"
    ((cssBlocksFor css "section.section-page::after").any fun d =>
      ((cssDeclOf d "height").bind fun h =>
        if hasStr h "em - var(--progressheight" then
          emMilli (((h.drop 5).takeWhile (· != ' ')).toString) else none).any fun m =>
        size * m / 1000 - 4 ≤ pdfStrut && pdfStrut ≤ size * m / 1000)
  let feet := elemAttrsList (· == "footer") #[] body.toList
  t "frame area html: a restored scriptsize note sizes its footline's box"
    (feet.any fun (_, attrs) =>
      ((attrs.find? (·.1 == "style")).map (hasStr ·.2 "--foot-cap: 1.400;")).getD false)
  -- With no bar the title is the page's first line at the slides' top
  -- margin (`Layout.collectFrameTitle`), the stage's top edge its area's.
  let (bdoc, _) := elabStr barlessDeck
  let (bhead, _, _) := HtmlDoc.emitTree {} bdoc
  let bcss := treeCssList "" bhead.toList
  t "frame area html: with no title bar the title opens at the slides' top margin, as the PDF sets it"
    ((cssBlocksFor bcss "section.slide:not(.title-page) > header").any fun d =>
      cssStageLength d "padding-top" bdoc.page.vmargin bdoc.page.height)
where
  /-- A deck with no title bar (the bundle a deck without `\usetheme` gets):
  one titled frame. Invented words. -/
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
    if let some v := cssDeclOf decls key then
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

/-- **A figure inside a list item reads its own level's float space in the
web deck** (`HtmlDoc.lineageLevelRules`): `--floatsep`'s `var(--topsep)`
resolves where the property is declared, so each list level declares it
beside its own `--topsep` — the nearest ancestor of a figure in an item that
declares the one is the item, and declares the other at the level's 3 pt,
the stage's share, the space the page spends there (`Ir.floatSpaceFor` at
depth one). Declared on the root alone, a figure in an item spent the top
level's 8 pt in the web deck, 5 bp low above and below at 10 pt. Read by a
cascade over the shipped stylesheet and the typed tree's paths
(`declaredOn`). Invented words. -/
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
  -- A preamble `\topsep` is the top level's alone: the deck states it as
  -- the stage's share, and a note says the lists set their own.
  let (ddoc, dds) := elabStr ("\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n" ++
    "\\setlength{\\topsep}{20pt}\n\\begin{document}\n\\begin{frame}[t]\n" ++
    "\\begin{center}\nKilo words.\n\\end{center}\n\\end{frame}\n\\end{document}\n")
  let (dhead, _, _) := HtmlDoc.emitTree {} ddoc
  let roots := cssBlocksFor (treeCssList "" dhead.toList) ":root"
  t "float level: a declared topsep reaches the deck as the stage's share and is noted as the top level's"
    ((roots.any fun d => cssStageLength d "--topsep" (Dim.pt 20) ddoc.page.height) &&
     !(roots.any fun d => (cssDeclOf d "--topsep").any (·.endsWith "pt")) &&
     dds.any fun d => hasStr d.message "which a trivlist outside a list reads")

/-- A Light family's set: the shipped Fira Sans's outlines as a 300 in the
regular slot and as a 400 in the bold one, the shape of a deck that sets a
Light family with its Regular for bold. -/
private def lightSet (f : Font.Font) : Font.FontSet :=
  { fonts := #[{ f with weight := 300 }, f]
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 1),
       ((slot, 400, true), 0), ((slot, 700, true), 1)]).toArray }

/-- **Every footline sets at the body's weight, standout frames included**
(`HtmlDoc.footlineCss`, `fontCss`'s `--ltx-body-weight`): on `deck` with a
Light family whose regular face is a 300, every footer element computes to
the 300 the body resolves, while a standout frame's own type stays at its
600. Read by a cascade over the shipped stylesheet and the typed tree's
paths (`computedOn`), which a footer rule naming `normal` again breaks. At
`5e6eedf5` every footer computed to `normal`, a 400: the family's Regular,
the deck's bold, where the PDF and lualatex set the Light. Invented words. -/
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

/-- **The web footline is the page's band box** (`Layout.footBandBox`,
`HtmlDoc.Config.footBox`): where the driver measures it, a frame's footer
declares its band's glyph height and depth as the stage's shares of the box
the shipped page's footline lines carry, so its slots' baseline stands their
depth above the closing skip, as TeX's box of the line puts it. Asserted
over `Layout.Out` and the typed tree on `noteDeck`, whose note descends. At
`913469fb` the footer declared no box: the slots stood their baseline the
closing skip above the stage's edge whatever they held, and a note that
descends stood its depth (1.42 bp at seven points) below the page's.
Invented words. -/
def footBoxChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "footline box: the shipped Fira Sans parses" false
  let (doc, _) := elabStr noteDeck
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fira doc geom
  let feet := ((out.pages[0]?.map (·.lines)).getD #[]).filter (·.furniture)
  let (h, d) := feet.foldl (fun (acc : Dim.Sp × Dim.Sp) l =>
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

/-- **A frame's footnotes stand in its text area as beamer sets them**
(`Spacing.Page.noteGap`, `Spacing.Page.noteHang`): one box directly under the
frame's content, no `\skip\footins` above it, its last baseline on the text
area's floor and its depth below, the content centred in what the box
leaves. Asserted over `Layout.Out` against lualatex's measurements of
`noteFrames` (TeX Live 2026, beamer 10 pt, 4:3, the shipped Fira Sans for
every face; bp from the page top to the baseline): the notes at 260.82,
260.77, and 251.00 and 260.71; the untitled frame's body at 132.87; and the
titled frame's body 3.39 bp above the same frame's with no note — the note's
own lift, apart from the titled frames' size-ladder residual. Held to 0.5
bp, as `checks` holds its lines. At `fac230ee` the notes stood a
`\skip\footins` and their ink above the floor: about 2 bp high, and the
body above them about 8 bp high. Invented words. -/
def frameNoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "frame notes: the shipped Fira Sans parses" false
  let (doc, _) := elabStr noteFrames
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let near := withinSp (ptMilli 500)
  let ys (page : Nat) (note : Bool) : List Dim.Sp :=
    ((out.pages[page]?.map fun p => (p.lines.filter fun l =>
      l.note == note && !l.furniture &&
        (if note then !(lineText l).isEmpty else hasStr (lineText l) "Kilo")).map (·.y)).getD #[]).toList
  let at? (got : List Dim.Sp) (milli : List Int) : Bool :=
    got.length == milli.length && (got.zip milli).all fun (a, m) => near a (ptMilli m)
  t "frame notes: a frame's notes stand their last baseline on the text area's floor, as lualatex does"
    (at? (ys 0 true) [260820] && at? (ys 1 true) [260770] && at? (ys 2 true) [251000, 260710])
  t "frame notes: an untitled frame centres above its note, as lualatex does"
    (at? (ys 1 false) [132870])
  t "frame notes: a note lifts its titled frame's body by half its box, as lualatex does"
    (match ys 0 false, ys 3 false with
     | [a], [b] => near (a - b) (ptMilli (-3390))
     | _, _ => false)

end Tests.FrameArea
