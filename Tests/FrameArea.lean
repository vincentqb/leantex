import Tests.Support

open LeanTex.Core

namespace Tests.FrameArea

/-- The invented moloch deck the checks lay out, the one source each value
below was first measured on under lualatex (beamer 10 pt, 4:3, the shipped
Fira Sans for every face): a standout frame, a standout frame whose note the
deck's footline hook restores, a titled control, a bottom-aligned standout,
and a section page. The footline hook is the one a moloch deck spells to
restore an explicit note on a standout frame. -/
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
  "\\begin{frame}[standout,b]\nKilo words.\n\\end{frame}\n" ++
  "\\section{Hotel words}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
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
at 142.951, the same frame with its note restored at 138.197 (the note's
own baseline at 268.057), and the section page's title at 127.894, on a
templated title page's heels (`slottedDeck`) as after a frame. The lines are
held to 0.5 bp: what remains is the standout size's leading,
17.28 pt on the engine's ladder against size10.clo's 18 pt, half of it
after centring (0.36 bp). At `fa516a82` the standout frame stood 2.06 bp
high, the restored note sent its line 9.12 bp low — the page took the
note's band off a floor still at the slides margin, the paper's top still
26.4 bp above its content — and the section page stood 9.99 bp low; with
the area alone, the section page after the title page stood 14.3 bp low,
the title page's slots leaving the page fresh for the next page's opening.
Invented words. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← (do
      match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraSans-Regular.otf")) with
      | .ok f => pure (some (oneFaceOf f))
      | .error _ => pure none : IO (Option Font.FontSet))
    | t "frame area: the shipped Fira Sans parses" false
  let (doc, _) := elabStr deck
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fira doc geom
  let bp (milli : Int) : Dim.Sp := Dim.pt 1 * milli / 1000
  let near (a b : Dim.Sp) : Bool := a - b ≤ bp 500 && b - a ≤ bp 500
  let line (page : Nat) (word : String) (furniture : Bool := false) :
      Option Layout.LineOut :=
    out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.furniture == furniture && hasStr (lineText l) word
  let at? (page : Nat) (word : String) (milli : Int) (furniture : Bool := false) : Bool :=
    ((line page word furniture).map fun l => near l.y (bp milli)).getD false
  t "frame area: a standout frame centres in beamer's text area, as lualatex does"
    (at? 0 "Kilo" 142951)
  t "frame area: a restored standout note lifts its frame by half its footheight, as lualatex does"
    (at? 1 "Kilo" 138197 && at? 1 "Lima" 268057 true)
  t "frame area: a section page centres on the whole paper, as lualatex does"
    (at? 4 "Hotel" 127894)
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
     | some a, some b => a == b && near a (bp 127894)
     | _, _ => false)
  -- The floor itself, exactly: a bottom-aligned standout frame's content
  -- ends on it, the glyphs' depth below its last baseline (`B.contentEnd`),
  -- 4 pt above the paper's edge where no footline stands.
  t "frame area: an empty footline's text area ends its gap above the paper's edge"
    (((line 3 "Kilo").map fun l =>
      l.y + (Layout.segsInk fira l.segs).2 ==
        Layout.frameFloor geom.pageH Ir.footline.sep none).getD false)

/-- A deck with no title bar (the bundle a deck without `\usetheme` gets):
one titled frame. Invented words. -/
private def barlessDeck : String :=
  "\\documentclass[10pt]{beamer}\n\\begin{document}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n\\end{document}\n"

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
footline keeps its own step and weight. Asserted over the typed tree and the
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
  -- the footline undoes that step for its own and sets at the body weight.
  let standoutSize := (cssBlocksFor css "section.slide.standout").findSome? (cssDeclOf · "font-size")
  let footStep := (cssBlocksFor css s!".size-{Ir.footline.step}").findSome? (cssDeclOf · "font-size")
  t "frame area html: a standout frame's type is the whole frame's, its footline keeping its own"
    ((cssBlocksFor css "section.slide.standout").any (cssDeclOf · "font-weight" == some "600") &&
     (cssBlocksFor css "section.slide.standout > p").isEmpty &&
     foot.any (cssDeclOf · "font-weight" == some "normal") &&
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
    (slides.size == 5 && slides.all fun (_, attrs) =>
      ((attrs.find? (·.1 == "style")).map (hasStr ·.2 "--frame-body-skip")).getD false)
  t "frame area html: a section page closes on its subsection strut below its bar"
    ((cssBlocksFor css "section.section-page::after").any fun d =>
      ((cssDeclOf d "height").map (hasStr · "em - var(--progressheight")).getD false)
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
  let some fira ← (do
      match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraSans-Regular.otf")) with
      | .ok f => pure (some (oneFaceOf f))
      | .error _ => pure none : IO (Option Font.FontSet))
    | t "footline box: the shipped Fira Sans parses" false
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

end Tests.FrameArea
